use std::marker::PhantomData;

use halo2_proofs::arithmetic::FieldExt;
use halo2_proofs::circuit::{AssignedCell, Chip, Layouter, SimpleFloorPlanner, Value};
use halo2_proofs::halo2curves::pasta::Fp;
use halo2_proofs::plonk::{Advice, Circuit, Column, Constraints, ConstraintSystem, Error, Expression, Instance, Selector};
use halo2_proofs::poly::Rotation;

const ELEMENT_LEN: usize = 3;
const MAX_VAL: u64 = 100;

#[derive(Clone, Debug)]
struct SortConfig {
    advices: [Column<Advice>; ELEMENT_LEN],
    instance: Column<Instance>,
    s_is_less_than: Selector,
    s_diff: Selector,
}

#[derive(Clone, Debug)]
struct Number<F: FieldExt>(AssignedCell<F, F>);

// [0, range]
pub fn range_check<F: FieldExt>(expr: Expression<F>, range: u64) -> Expression<F> {
    (1..((range + 1) as usize)).fold(expr.clone(), |acc, i| acc * (Expression::Constant(F::from(i as u64)) - expr.clone()))
}

struct SortChip<F> {
    config: SortConfig,
    _maker: PhantomData<F>,
}

impl<F: FieldExt> SortChip<F> {

    fn construct(config: SortConfig) -> Self {
        Self {
            config,
            _maker: PhantomData,
        }
    }

    fn configure(
        meta: &mut ConstraintSystem<F>,
        advices: [Column<Advice>; ELEMENT_LEN],
        instance: Column<Instance>,
    ) -> SortConfig {
        meta.enable_equality(instance);
        for col in advices {
            meta.enable_equality(col);
        }
        let s_is_less_than = meta.selector();
        let s_diff = meta.selector();

        meta.create_gate("bool check", |meta| {
            let selector = meta.query_selector(s_is_less_than);
            let advice = meta.query_advice(advices[0], Rotation::cur());
            Constraints::with_selector(selector, Some(range_check(advice, MAX_VAL)))
        });

        meta.create_gate("diff constraint", |meta| {
            let s_diff = meta.query_selector(s_diff);
            let a = meta.query_advice(advices[0], Rotation::cur());
            let b = meta.query_advice(advices[1], Rotation::cur());
            let diff = meta.query_advice(advices[2], Rotation::cur());
            let max_range = Expression::Constant(F::from(MAX_VAL));
            vec![s_diff * (a + max_range - b - diff)]
        });

        SortConfig {advices, instance, s_is_less_than, s_diff}
    }

    fn assign_all(&self, mut layouter: impl Layouter<F>, val: [Value<F>; ELEMENT_LEN]) -> Result<[Number<F>; ELEMENT_LEN], Error> {
        let config = self.config();
        layouter.assign_region(|| "copy", |mut region| {
            let a = region.assign_advice(|| "a", config.advices[0], 0, || val[0]).map(Number).unwrap();
            let b = region.assign_advice(|| "b", config.advices[1], 0, || val[1]).map(Number).unwrap();
            let c = region.assign_advice(|| "c", config.advices[2], 0, || val[2]).map(Number).unwrap();
            Ok([a,b,c])
        })
    }

    pub fn assign_diff(
        &self,
        mut layouter: impl Layouter<F>,
        a: Number<F>,
        b: Number<F>,
        max: Value<F>,
    ) -> Result<Number<F>, Error> {
        let config = self.config();
        layouter.assign_region(
            || "assign diff",
            |mut region| {
                config.s_diff.enable(&mut region, 0)?;
                a.0.copy_advice(|| "lhs a", &mut region, config.advices[0], 0).map(Number).unwrap();
                b.0.copy_advice(|| "rhs b", &mut region, config.advices[1], 0).map(Number).unwrap();
                let diff = a.0.value().copied() + max - b.0.value() ;
                let diff = region.assign_advice(|| "diff", config.advices[2], 0, || diff).map(Number).unwrap();
                Ok(diff)
            })
    }

    pub fn check_less_than(
        &self,
        mut layouter: impl Layouter<F>,
        diff: Number<F>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "check less than",
            |mut region| {
                self.config.s_is_less_than.enable(&mut region, 0)?;
                diff.0.copy_advice(|| "diff", &mut region, self.config.advices[0], 0)?;
                Ok(())
            },
        )
    }

}

impl<F: FieldExt> Chip<F> for SortChip<F> {
    type Config = SortConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

#[derive(Default)]
struct SortCircuit<F: FieldExt> {
    list: [F; ELEMENT_LEN],
    max: Value<F>,
}

impl<F: FieldExt> Circuit<F> for SortCircuit<F> {
    type Config = SortConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let advices = [meta.advice_column(), meta.advice_column(), meta.advice_column()];
        let instance = meta.instance_column();
        // TODO use instance later
        SortChip::configure(meta, advices, instance)
    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        let sort_chip = SortChip::<F>::construct(config);

        // sort value
        let mut raw = self.list;
        for i in 1..ELEMENT_LEN {
            for j in 1..(ELEMENT_LEN - i + 1) {
                if raw[j] < raw[j-1] {
                    raw.swap(j - 1, j);
                }
            }
        }

        for i in 0..ELEMENT_LEN {
            println!("element on idx({:?}) is {:?}", i, raw[i]);
        }

        // load sorted values
        let new_arr = sort_chip.assign_all(layouter.namespace(|| "one"),
                                           [Value::known(raw[0]), Value::known(raw[1]), Value::known(raw[2])])?;

        let diff = sort_chip.assign_diff(layouter.namespace(|| "load diff a,b"),
                                         new_arr[0].clone(), new_arr[1].clone(), self.max)?;

        sort_chip.check_less_than(layouter.namespace(|| "check diff in range"), diff)?;

        let diff = sort_chip.assign_diff(layouter.namespace(|| "load diff b c"),
                                         new_arr[1].clone(), new_arr[2].clone(), self.max)?;
        sort_chip.check_less_than(layouter.namespace(|| "check diff in range"), diff)?;

        Ok(())
    }
}

fn main() {
    use halo2_proofs::{dev::MockProver};
    let k = 4;
    let a = Fp::from(3);
    let b = Fp::from(2);
    let c = Fp::from(1);
    let max = Fp::from(MAX_VAL);

    let circuit = SortCircuit {
        list: [a,b,c],
        max: Value::known(max),
    };

    // while instance may not used, init still need it. Or err "invalidInstances will be returned."
    let prover = MockProver::run(k, &circuit, vec![vec![]]).unwrap();
    assert_eq!(prover.verify(), Ok(()));

    // optional, draw layout picture
    use plotters::prelude::*;
    let root = BitMapBackend::new("sort-circuit-layout.png", (1024, 768)).into_drawing_area();
    root.fill(&WHITE).unwrap();
    let root = root
        .titled("Sort Circuit Layout", ("sans-serif", 60))
        .unwrap();
    halo2_proofs::dev::CircuitLayout::default()
        .show_labels(true)
        .render(5, &circuit, &root)
        .unwrap();
}