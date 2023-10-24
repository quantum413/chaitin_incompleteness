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
enum ProofStep<D: DeductionRule>{
    Input(Index),
    Deduce(Deduction<D>, Vec<Rc<ProofStep<D>>>),
}

#[derive(Derivative)]
#[derivative(Debug(bound = "D::Formula: Debug, D::Parameter: Debug"))]
#[derivative(Clone(bound = "D::Formula: Clone, D::Parameter: Clone"))]
#[derivative(PartialEq(bound = "D::Formula: PartialEq, D::Parameter: PartialEq"))]
#[derivative(Eq(bound = "D::Formula: Eq, D::Parameter: Eq"))]
struct Proof<D: DeductionRule>{
    inputs: Vec<D::Formula>,
    output: D::Formula,
    derivation: ProofStep<D>,
}

impl<D: DeductionRule> ProofStep<D> {
    fn add_to_proof(
        proof: &mut Vec<CheckedSerialProofStep<D>>,
        derivation: Rc<ProofStep<D>>,
        inputs: &Vec<D::Formula>,
    ) where D::Formula: Clone, D::Parameter: Clone{
        match &*derivation {
            ProofStep::Input(i) => {
                proof.push(CheckedSerialProofStep::Input(inputs[*i].clone(), *i))
            }
            ProofStep::Deduce(d, sub) => {
                let mut indices = Vec::<Index>::new();
                for s in sub{
                    ProofStep::add_to_proof(proof, s.clone(), inputs);
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
        let mut steps = Vec::<Rc<ProofStep<D>>>::new();
        for deduction in deductions {
            let new_step =
                match deduction {
                    CheckedSerialProofStep::Input(_, i) => { ProofStep::Input(i)}
                    CheckedSerialProofStep::Deduce(d, ded_indices) => {
                        ProofStep::Deduce(
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
        ProofStep::add_to_proof(&mut proof, Rc::new(derivation), &inputs);
        SerialProof { inputs, output, deductions: proof, }
    }
}

#[cfg(test)]
mod tests {
    use crate::abstract_parser::{AbstractParser, StrictAbstractParser};
    use crate::proof_manipulation::serial_proofs::{UncheckedSerialProof, UncheckedSerialProofStep};
    use super::super::deductions::DeductionRule;
    use super::*;

    #[derive(Debug)]
    struct Decrement;

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

    #[test]
    fn decrement_rules(){
        let d_str = "d".to_string();
        let e_str = "e".to_string();
        assert_eq!(Decrement::deduce(d_str.clone(), vec![30usize]), Some(29));
        assert_eq!(Decrement::deduce(e_str.clone(), vec![30usize]), None);
        assert_eq!(Decrement::deduce(d_str.clone(), vec![0usize]), None);
        assert_eq!(Decrement::deduce(d_str.clone(), vec![30usize, 2usize]), None);
    }

    #[test]
    fn decrement_deduction(){
        let d_str = "d".to_string();
        assert!(Decrement::make_deduction(d_str.clone(), vec![0usize]).is_none());
        let d_1 = Decrement::make_deduction(d_str.clone(), vec![30usize]).unwrap();
        let d_2 = Decrement::make_deduction(d_str.clone(), vec![20usize]).unwrap();
        assert_eq!(d_1, d_1);
        assert_ne!(d_1, d_2);
        assert_eq!(d_1.output, 29usize);
        assert_eq!(d_1.params, d_str);
        assert_eq!(d_1.inputs, vec![30usize]);
    }
    #[test]
    fn decrement_make_proof() {
        let pf = make_single_step_decrement_proof(
            19usize,
            20usize,
            0usize,
            20usize,
            0usize,
            19usize
        );
        assert!(SerialProof::parse(pf.clone()).is_some());
        assert!(SerialProof::check_parse(pf));
    }
    #[test]
    fn decrement_proof_check_final_output() {
        let pf = make_single_step_decrement_proof(
            18usize,
            20usize,
            0usize,
            20usize,
            0usize,
            19usize
        );
        assert!(SerialProof::parse(pf).is_none());
    }

    fn make_single_step_decrement_proof(
        output: usize,
        input: usize,
        step_input_index: usize,
        step_input_output: usize,
        step_deduce_index: usize,
        step_deduce_output: usize
    ) -> UncheckedSerialProof<Decrement> {
        UncheckedSerialProof::new(
            output,
            vec![input],
            vec![
                (UncheckedSerialProofStep::Input(step_input_index), step_input_output),
                (UncheckedSerialProofStep::Deduce("d".to_string(), vec![step_deduce_index]), step_deduce_output),
            ]
        )
    }

    #[test]
    fn decrement_proof_check_deduction_output() {
        let pf = make_single_step_decrement_proof(
            19usize,
            20usize,
            0usize,
            20usize,
            0usize,
            18usize,
        );
        assert!(SerialProof::parse(pf).is_none());
    }
    #[test]
    fn decrement_proof_zero_length() {
        let pf: UncheckedSerialProof<Decrement> = UncheckedSerialProof::new(
            20usize,
            vec![20usize],
            vec![]
        );
        assert!(SerialProof::parse(pf).is_none());
    }
    #[test]
    fn decrement_proof_identity(){
        let pf: UncheckedSerialProof<Decrement> = UncheckedSerialProof::new(
            20usize,
            vec![10usize, 20usize],
            vec![(UncheckedSerialProofStep::Input(1usize), 20usize)],
        );
        assert!(SerialProof::parse(pf.clone()).is_some());
        assert!(SerialProof::check_parse(pf));
    }
    #[test]
    fn decrement_proof_out_of_bounds_input(){
        let pf: UncheckedSerialProof<Decrement> = UncheckedSerialProof::new(
            20usize,
            vec![10usize, 20usize],
            vec![(UncheckedSerialProofStep::Input(2usize), 20usize)],
        );
        assert!(SerialProof::parse(pf.clone()).is_none());
    }

    #[test]
    fn decrement_proof_out_of_bounds_deduction(){
        let pf = make_single_step_decrement_proof(
            19usize,
            20usize,
            0usize,
            20usize,
            1usize,
            19usize,
        );
        assert!(SerialProof::parse(pf).is_none());
    }
    #[test]
    fn decrement_proof_check_input_output(){
        let pf = make_single_step_decrement_proof(
            19usize,
            20usize,
            0usize,
            19usize,
            0usize,
            19usize,
        );
        assert!(SerialProof::parse(pf).is_none());
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