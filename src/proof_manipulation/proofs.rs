use std::fmt::Debug;
use std::vec::Vec;
use derivative::Derivative;
use crate::abstract_parser::{AbstractParser, StrictAbstractParser};
use crate::proof_manipulation::deductions::{Deduction, DeductionRule};

type Index = usize;

#[derive(Debug, Clone, PartialEq, Eq)]
enum ProofStep<P> {
    Input(Index),
    Deduce(P, Vec<Index>),
}

#[derive(Derivative)]
#[derivative(Debug(bound = "D::Formula: Debug, D::Parameter: Debug"))]
#[derivative(Clone(bound = "D::Formula: Clone, D::Parameter: Clone"))]
#[derivative(PartialEq(bound = "D::Formula: PartialEq, D::Parameter: PartialEq"))]
#[derivative(Eq(bound = "D::Formula: Eq, D::Parameter: Eq"))]
struct UncheckedProof<D: DeductionRule> {
    inputs: Vec<D::Formula>,
    output: D::Formula,
    proof: Vec<(ProofStep<D::Parameter>, D::Formula)>,
}

impl<D: DeductionRule> UncheckedProof<D> {
    fn new(output: D::Formula, inputs: Vec<D::Formula>, proof: Vec<(ProofStep<D::Parameter>, D::Formula)>) -> Self {
        UncheckedProof { output, inputs, proof}
    }
}

#[derive(Derivative)]
#[derivative(Debug(bound = "D::Formula: Debug, D::Parameter: Debug"))]
#[derivative(Clone(bound = "D::Formula: Clone, D::Parameter: Clone"))]
#[derivative(PartialEq(bound = "D::Formula: PartialEq, D::Parameter: PartialEq"))]
#[derivative(Eq(bound = "D::Formula: Eq, D::Parameter: Eq"))]
enum CheckedProofStep<D: DeductionRule>{
    Input(D::Formula, Index),
    Deduce(Deduction<D>, Vec<Index>)
}

impl<D: DeductionRule> CheckedProofStep<D> {
    fn get_output(&self) -> &D::Formula{
        match self {
            CheckedProofStep::Input(f, _) => {&f}
            CheckedProofStep::Deduce(d, _) => {&d.output}
        }
    }
    fn check_step(inputs: &Vec<D::Formula>, step: ProofStep<D::Parameter>) -> Option<CheckedProofStep<D>>
        where D::Formula: Clone + Eq, D::Parameter: Clone + Eq {
        Some(match step {
            ProofStep::Input(i) => {
                CheckedProofStep::Input(inputs.get(i)?.clone(), i)
            }
            ProofStep::Deduce(params, indices) => {
                let mut input_formulae: Vec<D::Formula> = vec![];
                for &i in &indices {
                    input_formulae.push(inputs.get(i)?.clone())
                }
                let deduction = D::make_deduction(params, input_formulae)?;
                CheckedProofStep::Deduce(
                    deduction,
                    indices
                )
            }
        })
    }
}

#[derive(Derivative)]
#[derivative(Debug(bound = "D::Formula: Debug, D::Parameter: Debug"))]
#[derivative(Clone(bound = "D::Formula: Clone, D::Parameter: Clone"))]
#[derivative(PartialEq(bound = "D::Formula: PartialEq, D::Parameter: PartialEq"))]
#[derivative(Eq(bound = "D::Formula: Eq, D::Parameter: Eq"))]
struct Proof<D: DeductionRule>{
    inputs: Vec<D::Formula>,
    output: D::Formula,
    deductions: Vec<CheckedProofStep<D>>,
}

impl<D: DeductionRule> AbstractParser<UncheckedProof<D>> for Proof<D> where D::Formula: Clone + Eq, D::Parameter: Clone + Eq {
    fn parse(pf: UncheckedProof<D>) -> Option<Self> {
        let UncheckedProof{inputs, output, proof} = pf;
        if proof.len() == 0 {return None;}
        let mut deductions: Vec<CheckedProofStep<D>> = vec![];
        for (step, output) in proof.into_iter(){
            let checked_step = CheckedProofStep::check_step(&inputs, step)?;
            if *checked_step.get_output() != output {return None;}
            deductions.push(checked_step);
        }
        if output != *deductions[deductions.len() - 1].get_output() {return None;}
        Some(Proof{
            inputs,
            output,
            deductions,
        })
    }

    fn un_parse(self) -> UncheckedProof<D> {
        UncheckedProof{
            output: self.output,
            inputs: self.inputs,
            proof: self.deductions.into_iter().map(
                |s| {
                    match s {
                        CheckedProofStep::Input(f, i) =>
                            (ProofStep::Input(i), f),
                        CheckedProofStep::Deduce(d, indices) =>
                            (ProofStep::Deduce(d.params, indices), d.output),
                    }
                }
            ).collect(),
        }
    }
}

impl<D: DeductionRule> StrictAbstractParser<UncheckedProof<D>> for Proof<D> where D::Formula: Clone + Eq, D::Parameter: Clone + Eq {}

#[cfg(test)]
mod tests {
    use crate::abstract_parser::{AbstractParser, StrictAbstractParser};
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
        assert!(Proof::parse(pf.clone()).is_some());
        assert!(Proof::check_parse(pf));
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
        assert!(Proof::parse(pf).is_none());
    }

    fn make_single_step_decrement_proof(output: usize, input: usize, step_input_index: usize, step_input_output: usize, step_deduce_index: usize, step_deduce_output: usize) -> UncheckedProof<Decrement> {
        UncheckedProof::new(
            output,
            vec![input],
            vec![
                (ProofStep::Input(step_input_index), step_input_output),
                (ProofStep::Deduce("d".to_string(), vec![step_deduce_index]), step_deduce_output),
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
        assert!(Proof::parse(pf).is_none());
    }
    #[test]
    fn decrement_proof_zero_length() {
        let pf: UncheckedProof<Decrement> = UncheckedProof::new(
            20usize,
            vec![20usize],
            vec![]
        );
        assert!(Proof::parse(pf).is_none());
    }
    #[test]
    fn decrement_proof_identity(){
        let pf: UncheckedProof<Decrement> = UncheckedProof::new(
            20usize,
            vec![10usize, 20usize],
            vec![(ProofStep::Input(1usize), 20usize)],
        );
        assert!(Proof::parse(pf.clone()).is_some());
        assert!(Proof::check_parse(pf));
    }
    #[test]
    fn decrement_proof_out_of_bounds_input(){
        let pf: UncheckedProof<Decrement> = UncheckedProof::new(
            20usize,
            vec![10usize, 20usize],
            vec![(ProofStep::Input(2usize), 20usize)],
        );
        assert!(Proof::parse(pf.clone()).is_none());
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
        assert!(Proof::parse(pf).is_none());
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
        assert!(Proof::parse(pf).is_none());
    }
}