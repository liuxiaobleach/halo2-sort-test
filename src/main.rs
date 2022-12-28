use std::marker::PhantomData;

use halo2_proofs::arithmetic::FieldExt;
use halo2_proofs::circuit::{AssignedCell, Chip, Layouter, SimpleFloorPlanner, Value};
use halo2_proofs::halo2curves::pasta::Fp;
use halo2_proofs::plonk::{Advice, Circuit, Column, Constraints, ConstraintSystem, Error, Expression, Instance, Selector, TableColumn};
use halo2_proofs::poly::Rotation;

const ELEMENT_LEN: usize = 3;
const MAX_VAL: u64 = 100;

#[derive(Clone, Debug)]
struct SortConfig {
    advices: [Column<Advice>; ELEMENT_LEN],
    instances: [Column<Instance>; ELEMENT_LEN],
    s_is_less_than: Selector,
    s_diff: Selector,
    s_one_eq: Selector,
    s_sum_eq: Selector,

    test_table: [TableColumn; 3],
    s_test_table: Selector,
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
        instances: [Column<Instance>; ELEMENT_LEN],
    ) -> SortConfig {
        for col in advices {
            meta.enable_equality(col);
        }
        for col in instances {
            meta.enable_equality(col);
        }
        let s_is_less_than = meta.selector();
        let s_diff = meta.selector();
        let s_one_eq = meta.selector();
        let s_sum_eq = meta.selector();
        let s_test_table = meta.complex_selector();

        let test_table = [meta.lookup_table_column(), meta.lookup_table_column(), meta.lookup_table_column()];

        meta.create_gate("bool check for less than", |meta| {
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

        meta.create_gate("one eq", |meta| {
            let s_one_eq = meta.query_selector(s_one_eq);
            let max_range = Expression::Constant(F::from(MAX_VAL));
            let a = meta.query_advice(advices[0], Rotation::cur());

            let diff_a_1 = meta.query_advice(advices[0], Rotation::next());
            let diff_a_2 = meta.query_advice(advices[1], Rotation::next());
            let diff_a_3 = meta.query_advice(advices[2], Rotation::next());

            let i_a = meta.query_advice(advices[0], Rotation(2));
            let i_b = meta.query_advice(advices[1], Rotation(2));
            let i_c = meta.query_advice(advices[2], Rotation(2));

            vec![s_one_eq.clone() * (a.clone() + max_range.clone() - i_a.clone() - diff_a_1.clone()),
                 s_one_eq.clone() * (a.clone() + max_range.clone() - i_b.clone() - diff_a_2.clone()),
                 s_one_eq.clone() * (a.clone() + max_range.clone() - i_c.clone() - diff_a_3.clone()),
                 s_one_eq.clone() * (diff_a_1.clone() - max_range.clone()) * (diff_a_2.clone() - max_range.clone()) * (diff_a_3.clone() - max_range.clone())
            ]
        });

        meta.create_gate("eq pub input", |meta| {
            let sum_eq = meta.query_selector(s_sum_eq);
            let a = meta.query_advice(advices[0], Rotation::cur());
            let b = meta.query_advice(advices[1], Rotation::cur());
            let c = meta.query_advice(advices[2], Rotation::cur());

            let i_a = meta.query_advice(advices[0], Rotation::next());
            let i_b = meta.query_advice(advices[1], Rotation::next());
            let i_c = meta.query_advice(advices[2], Rotation::next());

            vec![sum_eq * (a + b + c - i_a - i_b - i_c)]
        });

        meta.lookup("test table", |meta| {
            let s = meta.query_selector(s_test_table);
            let one = meta.query_advice(advices[0], Rotation::cur());
            let two = meta.query_advice(advices[1], Rotation::cur());
            let three = meta.query_advice(advices[2], Rotation::cur());
            vec![
                (s.clone() * one, test_table[0]),
                (s.clone() * two, test_table[1]),
                (s * three, test_table[2]),
            ]
        });

        SortConfig {advices, instances, s_is_less_than, s_diff, s_one_eq, s_sum_eq, test_table, s_test_table}
    }

    fn assign_all(&self, mut layouter: impl Layouter<F>, val: [Value<F>; ELEMENT_LEN]) -> Result<[Number<F>; ELEMENT_LEN], Error> {
        let config = self.config();

        layouter.assign_region(|| "load private", |mut region| {
            config.s_sum_eq.enable(&mut region, 0)?;
            let a = region.assign_advice(|| "a", config.advices[0], 0, || val[0]).map(Number).unwrap();
            let b = region.assign_advice(|| "b", config.advices[1], 0, || val[1]).map(Number).unwrap();
            let c = region.assign_advice(|| "c", config.advices[2], 0, || val[2]).map(Number).unwrap();

            region.assign_advice_from_instance(|| "a", config.instances[0], 0, config.advices[0], 1)?;
            region.assign_advice_from_instance(|| "a", config.instances[1], 0, config.advices[1], 1)?;
            region.assign_advice_from_instance(|| "a", config.instances[2], 0, config.advices[2], 1)?;
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

    pub fn assign_instance_diff(
        &self,
        mut layouter: impl Layouter<F>,
        a: Number<F>,
        instance: [Value<F>; ELEMENT_LEN],
        max: Value<F>,
    ) -> Result<(), Error> {
        let config = self.config();
        layouter.assign_region(
            || "assign eq diff",
            |mut region| {
                config.s_one_eq.enable(&mut region, 0)?;
                a.0.copy_advice(|| "one val", &mut region, config.advices[0], 0).map(Number).unwrap();

                let diff_1 = a.0.value().copied() + max - instance[0];
                let diff_2 = a.0.value().copied() + max - instance[1];
                let diff_3 = a.0.value().copied() + max - instance[2];
                region.assign_advice(|| "one instance diff", config.advices[0], 1, || diff_1).map(Number).unwrap();
                region.assign_advice(|| "one instance diff", config.advices[1], 1, || diff_2).map(Number).unwrap();
                region.assign_advice(|| "one instance diff", config.advices[2], 1, || diff_3).map(Number).unwrap();

                region.assign_advice_from_instance(|| "a", config.instances[0], 0, config.advices[0], 2)?;
                region.assign_advice_from_instance(|| "a", config.instances[1], 0, config.advices[1], 2)?;
                region.assign_advice_from_instance(|| "a", config.instances[2], 0, config.advices[2], 2)?;

                Ok(())
            })
    }
    fn load_test_table(&self, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_table(|| "test table", |mut table| {
            table.assign_cell(|| "one", self.config.test_table[0], 0, || Value::known(F::from(1)))?;
            table.assign_cell(|| "two", self.config.test_table[1], 0, || Value::known(F::from(2)))?;
            table.assign_cell(|| "three", self.config.test_table[2], 0, || Value::known(F::from(3)))?;

            Ok(())
        })
    }

    pub fn assign_test_table(
        &self,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let config = self.config();
        layouter.assign_region(
            || "assign eq diff",
            |mut region| {
                config.s_test_table.enable(&mut region, 0)?;
                region.assign_advice(|| "lookup a", config.advices[0], 0, || Value::known(F::from(1)))?;
                region.assign_advice(|| "lookup b", config.advices[1], 0, || Value::known(F::from(2)))?;
                region.assign_advice(|| "lookup c", config.advices[2], 0, || Value::known(F::from(3)))?;
                Ok(())
            })
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
    instances: [Value<F>; ELEMENT_LEN],
}

impl<F: FieldExt> Circuit<F> for SortCircuit<F> {
    type Config = SortConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let advices = [meta.advice_column(), meta.advice_column(), meta.advice_column()];
        let instances = [meta.instance_column(), meta.instance_column(), meta.instance_column()];
        SortChip::configure(meta, advices, instances)
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

        sort_chip.load_test_table(layouter.namespace(|| "load test table"))?;

        // load sorted values
        let new_arr = sort_chip.assign_all(layouter.namespace(|| "one"),
                                           [Value::known(raw[0]), Value::known(raw[1]), Value::known(raw[2])])?;

        //let diff1inv = diff1.0.value().map(|v| v.invert().unwrap_or(F::zero()));
        // private input is a sorted array
        let diff1 = sort_chip.assign_diff(layouter.namespace(|| "load diff a,b"), new_arr[0].clone(), new_arr[1].clone(), self.max)?;
        sort_chip.check_less_than(layouter.namespace(|| "check diff in range"), diff1)?;
        let diff2 = sort_chip.assign_diff(layouter.namespace(|| "load diff b c"), new_arr[1].clone(), new_arr[2].clone(), self.max)?;
        sort_chip.check_less_than(layouter.namespace(|| "check diff in range"), diff2)?;

        // private input is equal to public input
        sort_chip.assign_instance_diff(layouter.namespace(|| "diff of a with instances"), new_arr[0].clone(), self.instances, self.max)?;

        //sort_chip.assign_test_table(layouter.namespace(|| "assign_test_table"))?;

        Ok(())
    }
}

fn main() {
    use halo2_proofs::{dev::MockProver};
    let k = 4;
    // use a,b,c as public input
    let a = Fp::from(3);
    let b = Fp::from(2);
    let c = Fp::from(1);
    let max = Fp::from(MAX_VAL);

    let circuit = SortCircuit {
        list: [a,b,c],
        max: Value::known(max),
        instances: [Value::known(a), Value::known(b), Value::known(c)],
    };

    // while instance may not used, init still need it. Or err "invalidInstances will be returned."
    let prover = MockProver::run(k, &circuit, vec![vec![a], vec![b], vec![c]]).unwrap();
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