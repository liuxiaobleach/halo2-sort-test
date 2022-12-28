use std::marker::PhantomData;

use halo2_proofs::arithmetic::FieldExt;
use halo2_proofs::circuit::{AssignedCell, Chip, Layouter, SimpleFloorPlanner, Value};
use halo2_proofs::dev::MockProver;
use halo2_proofs::halo2curves::pasta::Fp;
use halo2_proofs::plonk::{Advice, Circuit, Column, Constraints, ConstraintSystem, Error, Expression, Instance, Selector, TableColumn};
use halo2_proofs::poly::Rotation;

#[derive(Clone, Debug)]
struct RangeCheckConfig {
    advice: Column<Advice>,
    instance: Column<Instance>,

    range_table: TableColumn,
    s_range_table: Selector,
}

struct RangeCheckChip<F> {
    config: RangeCheckConfig,
    _maker: PhantomData<F>,
}

impl<F: FieldExt> RangeCheckChip<F> {
    fn construct(config: RangeCheckConfig) -> Self {
        Self {
            config,
            _maker: PhantomData,
        }
    }

    fn configure(
        meta: &mut ConstraintSystem<F>,
        advice: Column<Advice>,
        instance: Column<Instance>,
        range_table: TableColumn,
    ) -> RangeCheckConfig {
        meta.enable_equality(advice);
        meta.enable_equality(instance);
        let s_range_table = meta.complex_selector();

        meta.lookup("range table", |meta| {
            let s = meta.query_selector(s_range_table);
            let a = meta.query_advice(advice, Rotation::cur());
            vec![(s * a, range_table)]
        });

        RangeCheckConfig {advice, instance, range_table, s_range_table}
    }

    fn load_range_check_table(&self, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        let config = self.config();
        layouter.assign_table(|| "range check table", |mut table| {
            table.assign_cell(|| "a", config.range_table, 0, || Value::known(F::from(0)))?;
            table.assign_cell(|| "a", config.range_table, 1, || Value::known(F::from(1)))?;
            // why
            //  table.assign_cell(|| "a", config.range_table, 0, || Value::known(F::from(0)))?;
            //  table.assign_cell(|| "a", config.range_table, 1, || Value::known(F::from(1)))?;
            // not work ?
            Ok(())
        })
    }

    fn assign_all(&self, mut layouter: impl Layouter<F>, val: Value<F>) -> Result<AssignedCell<F, F>, Error> {
        let config = self.config();

        layouter.assign_region(|| "load private", |mut region| {
            config.s_range_table.enable(&mut region, 0)?;
            let a = region.assign_advice(|| "a", config.advice, 0, || val.clone()).unwrap();
            Ok(a)
        })
    }
}

impl<F: FieldExt> Chip<F> for RangeCheckChip<F> {
    type Config = RangeCheckConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

#[derive(Default)]
struct RangeCheckCircuit<F: FieldExt> {
    val: F,
}

impl<F: FieldExt> Circuit<F> for RangeCheckCircuit<F> {
    type Config = RangeCheckConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let advice = meta.advice_column();
        let instance = meta.instance_column();
        let range_table = meta.lookup_table_column();
        RangeCheckChip::configure(meta, advice, instance, range_table)
    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        let range_check_chip = RangeCheckChip::<F>::construct(config);

        // load sorted values
        range_check_chip.load_range_check_table(layouter.namespace(|| "load table"))?;
        let assigned_cell = range_check_chip.assign_all(layouter.namespace(|| "assign all"), Value::known(self.val))?;

        println!("{:?}", assigned_cell);

        Ok(())
    }
}

fn main() {
    println!("Hello, world!");

    let k = 4;

    let a = Fp::from(1);
    let ins = Fp::from(9);

    let circuit = RangeCheckCircuit {
        val: a,
    };

    let prover = MockProver::run(k, &circuit, vec![vec![ins]]).unwrap();
    assert_eq!(prover.verify(), Ok(()));
}
