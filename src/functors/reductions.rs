use std::marker::PhantomData;
use crate::proof_manipulation::deductions::FormalDeduction;
use crate::proof_manipulation::proofs::{Proof, ProofStep};

pub trait Reduction<D1: FormalDeduction, D2: FormalDeduction<Formula = D1::Formula>> {
    fn reduce(d: D1) -> Proof<D2>;
    fn check_reduce(d: D1) -> bool where D1: Clone, D2::Formula :Eq, D2: Eq{
        let pf = Self::reduce(d.clone());
        d.output() == pf.output() && d.inputs() == pf.inputs()
    }

    fn reduce_proof(p: Proof<D1>) -> Proof<D2> where D1::Formula: Clone + Eq, D1: Clone, D2: Clone{
        match p.un_step() {
            ProofStep::CopyInput(step) => {
                ProofStep::<D2>::make_copy_input_step(
                    step.inputs().clone(),
                    step.index()
                ).unwrap().step()
            }
            ProofStep::Deduce(step) => {
                Proof::<D2>::compose(
                    step.inputs().clone(),
                    step.sub_proofs().iter()
                        .map(
                            |p| Self::reduce_proof(p.clone())
                        )
                        .collect(),
                    Self::reduce(step.deduction().clone())
                ).unwrap()
            }
        }
    }
}

pub struct Reflexive<D: FormalDeduction> {_marker: PhantomData<D>}
impl<D: FormalDeduction> Reduction<D, D> for Reflexive<D> where D::Formula: Clone + Eq{
    fn reduce(d: D) -> Proof<D> {
        let inputs = d.inputs().clone();
        let input_proofs =
            (0.. inputs.len())
                .map(|i|
                    Proof::copy_input(
                        inputs.clone(),
                        i,
                    ).unwrap()
                )
                .collect();
        Proof::deduce(inputs, input_proofs, d).unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::proof_manipulation::proofs::tests::{Decrement};
    use crate::proof_manipulation::deductions::*;
    #[test]
    fn check_decrement_reduce() {
        let d = Decrement::make_deduction("d".to_string(), vec![10usize]).unwrap();
        assert!(Reflexive::check_reduce(d));
    }

    #[test]
    fn check_proof_reduce() {
        let pf = crate::proof_manipulation::proofs::tests::make_prod_150();
        let id = Reflexive::reduce_proof(pf.clone());
        assert_eq!(pf.inputs(), id.inputs());
        assert_eq!(pf.output(), id.output());
    }
}