use std::marker::PhantomData;

use halo2_proofs::arithmetic::FieldExt;
use halo2_proofs::circuit::{AssignedCell, Chip, Layouter, SimpleFloorPlanner, Value};
use halo2_proofs::dev::MockProver;
use halo2_proofs::halo2curves::pasta::Fp;
use halo2_proofs::plonk::{Advice, Circuit, Column, Constraints, ConstraintSystem, Error, Expression, Instance, Selector, TableColumn};
use halo2_proofs::poly::Rotation;

#[derive(Clone, Debug)]
struct RangeCheckConfig {
    advice: [Column<Advice>; 2],
    instance: Column<Instance>,

    range_table: [TableColumn; 2],
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
        advice: [Column<Advice>; 2],
        instance: Column<Instance>,
        range_table: [TableColumn; 2],
    ) -> RangeCheckConfig {
        meta.enable_equality(advice[0]);
        meta.enable_equality(advice[1]);
        meta.enable_equality(instance);
        let s_range_table = meta.complex_selector();

        meta.lookup("range table", |meta| {
            let s = meta.query_selector(s_range_table);
            let a = meta.query_advice(advice[0], Rotation::cur());
            let b = meta.query_advice(advice[1], Rotation::cur());
            vec![(s.clone() * a, range_table[0]), (s * b, range_table[1])]
        });

        RangeCheckConfig {advice, instance, range_table, s_range_table}
    }

    fn load_range_check_table(&self, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        let config = self.config();
        layouter.assign_table(|| "range check table", |mut table| {
            table.assign_cell(|| "a0", config.range_table[0], 0, || Value::known(F::from(0)))?;
            table.assign_cell(|| "a1", config.range_table[0], 1, || Value::known(F::from(1)))?;
            table.assign_cell(|| "a2", config.range_table[0], 2, || Value::known(F::from(2)))?;
            table.assign_cell(|| "a3", config.range_table[0], 3, || Value::known(F::from(3)))?;

            table.assign_cell(|| "b0", config.range_table[1], 0, || Value::known(F::from(0)))?;
            table.assign_cell(|| "b1", config.range_table[1], 1, || Value::known(F::from(5)))?;
            table.assign_cell(|| "b2", config.range_table[1], 2, || Value::known(F::from(6)))?;
            table.assign_cell(|| "b3", config.range_table[1], 3, || Value::known(F::from(7)))?;
            // why
            //  table.assign_cell(|| "a", config.range_table, 0, || Value::known(F::from(1)))?;
            //  table.assign_cell(|| "a", config.range_table, 1, || Value::known(F::from(0)))?;
            // not work ?
            Ok(())
        })
    }

    fn assign_all(&self, mut layouter: impl Layouter<F>) -> Result<AssignedCell<F, F>, Error> {
        let config = self.config();

        layouter.assign_region(|| "load private", |mut region| {
            config.s_range_table.enable(&mut region, 0)?;
            let a = region.assign_advice(|| "a", config.advice[0], 0, || Value::known(F::from(2))).unwrap();
            let b = region.assign_advice(|| "b", config.advice[1], 0, || Value::known(F::from(6))).unwrap();
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
        let advice = [meta.advice_column(), meta.advice_column()];
        let instance = meta.instance_column();
        let range_table = [meta.lookup_table_column(), meta.lookup_table_column()];
        RangeCheckChip::configure(meta, advice, instance, range_table)
    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        let range_check_chip = RangeCheckChip::<F>::construct(config);

        // load sorted values
        range_check_chip.load_range_check_table(layouter.namespace(|| "load table"))?;
        let assigned_cell = range_check_chip.assign_all(layouter.namespace(|| "assign all"))?;

        println!("{:?}", assigned_cell);

        Ok(())
    }
}

fn main() {
    println!("Hello, world!");

    let k = 4;

    let a = Fp::from(20);
    let ins = Fp::from(9);

    let circuit = RangeCheckCircuit {
        val: a,
    };

    let prover = MockProver::run(k, &circuit, vec![vec![ins]]).unwrap();
    assert_eq!(prover.verify(), Ok(()));
}
