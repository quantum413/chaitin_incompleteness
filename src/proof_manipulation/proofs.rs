use std::fmt::Debug;
use std::rc::Rc;
use std::vec::Vec;
use derivative::Derivative;
use crate::abstract_parser::AbstractParser;
use crate::proof_manipulation::deductions::{Deduction, DeductionRule};
use crate::proof_manipulation::serial_proofs::{CheckedSerialProofStep, SerialProof};

pub type Index = usize;

#[derive(Derivative)]
#[derivative(Debug(bound = "D::Formula: Debug, D::Parameter: Debug"))]
#[derivative(Clone(bound = "D::Formula: Clone, D::Parameter: Clone"))]
#[derivative(PartialEq(bound = "D::Formula: PartialEq, D::Parameter: PartialEq"))]
#[derivative(Eq(bound = "D::Formula: Eq, D::Parameter: Eq"))]
enum InternalProofStep<D: DeductionRule>{
    Input(Index),
    Deduce(Deduction<D>, Vec<Rc<InternalProofStep<D>>>),
}

#[derive(Derivative)]
#[derivative(Debug(bound = "D::Formula: Debug, D::Parameter: Debug"))]
#[derivative(Clone(bound = "D::Formula: Clone, D::Parameter: Clone"))]
#[derivative(PartialEq(bound = "D::Formula: PartialEq, D::Parameter: PartialEq"))]
#[derivative(Eq(bound = "D::Formula: Eq, D::Parameter: Eq"))]
struct Proof<D: DeductionRule>{
    inputs: Vec<D::Formula>,
    output: D::Formula,
    derivation: InternalProofStep<D>,
}

impl<D: DeductionRule> InternalProofStep<D> {
    fn add_to_proof(
        proof: &mut Vec<CheckedSerialProofStep<D>>,
        derivation: Rc<InternalProofStep<D>>,
        inputs: &Vec<D::Formula>,
    ) where D::Formula: Clone, D::Parameter: Clone {
        match &*derivation {
            InternalProofStep::Input(i) => {
                proof.push(CheckedSerialProofStep::Input(inputs[*i].clone(), *i))
            }
            InternalProofStep::Deduce(d, sub) => {
                let mut indices = Vec::<Index>::new();
                for s in sub{
                    InternalProofStep::add_to_proof(proof, s.clone(), inputs);
                    indices.push(proof.len() - 1);
                }
                proof.push(
                    CheckedSerialProofStep::Deduce(d.clone(), indices)
                )
            }
        }
    }
}
impl<D: DeductionRule> AbstractParser<SerialProof<D>> for Proof<D> where D::Formula: Clone + Eq, D::Parameter: Clone + Eq {
    fn parse(input: SerialProof<D>) -> Option<Self> {
        let SerialProof { inputs, output, deductions } = input;
        let mut steps = Vec::<Rc<InternalProofStep<D>>>::new();
        for deduction in deductions {
            let new_step =
                match deduction {
                    CheckedSerialProofStep::Input(_, i) => { InternalProofStep::Input(i)}
                    CheckedSerialProofStep::Deduce(d, ded_indices) => {
                        InternalProofStep::Deduce(
                            d,
                            ded_indices
                                .into_iter()
                                .map(|i| steps[i].clone())
                                .collect()
                        )
                    }
                };
            steps.push(Rc::new(new_step));
        }
        Some(Proof {inputs, output, derivation: Rc::into_inner(steps.pop()?)?})
    }

    fn un_parse(self) -> SerialProof<D> {
        let Proof {inputs, output, derivation} = self;
        let mut proof = Vec::<CheckedSerialProofStep<D>>::new();
        InternalProofStep::add_to_proof(&mut proof, Rc::new(derivation), &inputs);
        SerialProof { inputs, output, deductions: proof, }
    }
}

#[cfg(test)]
pub(in crate::proof_manipulation) mod tests {
    use crate::abstract_parser::AbstractParser;
    use crate::proof_manipulation::serial_proofs::{UncheckedSerialProof, UncheckedSerialProofStep};
    use super::super::deductions::DeductionRule;
    use super::*;

    #[derive(Debug)]
    pub(in crate::proof_manipulation) struct Decrement;

    impl DeductionRule for Decrement{
        type Formula = usize;
        type Parameter = String;

        fn deduce(params: String, inputs: Vec<usize>) -> Option<usize> {
            if &params != "d" || inputs.len() != 1 {return None;}
            if inputs[0] > 0 {
                Some(inputs[0] - 1)
            }
            else {
                None
            }
        }
    }
    #[derive(Debug)]
    struct Product;

    impl DeductionRule for Product{
        type Formula = usize;
        type Parameter = ();

        fn deduce(_: Self::Parameter, inputs: Vec<Self::Formula>) -> Option<Self::Formula> {
            if inputs.len() != 2 {return None;}
            Some(inputs[0] * inputs[1])
        }
    }


    fn example_proof() -> SerialProof<Decrement> {
        let pf= UncheckedSerialProof::<Decrement>::new(
            19usize,
            vec![15usize, 20usize],
            vec![
                (UncheckedSerialProofStep::Input(1usize), 20usize),
                (UncheckedSerialProofStep::Deduce("d".to_string(), vec![0usize]), 19usize)
            ]
        );
        SerialProof::parse(pf).unwrap()
    }
    #[test]
    fn decrement_abstract_proof_creation(){
        let pf = example_proof();
        let abstract_pf = Proof::parse(pf).unwrap();
        assert!(Proof::check_un_parse(abstract_pf.clone()));
        assert!(SerialProof::check_un_parse(Proof::un_parse(abstract_pf.clone())));
    }
}