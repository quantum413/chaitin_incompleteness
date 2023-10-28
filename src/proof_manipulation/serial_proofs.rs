use std::fmt::Debug;
use derivative::Derivative;
use crate::functors::abstract_parser::{AbstractParser, StrictAbstractParser};
use crate::proof_manipulation::deductions::{Deduction, DeductionRule};
use crate::proof_manipulation::proofs::Index;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UncheckedSerialProofStep<P> {
    Input(Index),
    Deduce(P, Vec<Index>),
}

#[derive(Derivative)]
#[derivative(Debug(bound = "D::Formula: Debug, D::Parameter: Debug"))]
#[derivative(Clone(bound = "D::Formula: Clone, D::Parameter: Clone"))]
#[derivative(PartialEq(bound = "D::Formula: PartialEq, D::Parameter: PartialEq"))]
#[derivative(Eq(bound = "D::Formula: Eq, D::Parameter: Eq"))]
pub struct UncheckedSerialProof<D: DeductionRule> {
    pub(in crate::proof_manipulation) inputs: Vec<D::Formula>,
    pub(in crate::proof_manipulation) output: D::Formula,
    pub(in crate::proof_manipulation) proof: Vec<(UncheckedSerialProofStep<D::Parameter>, D::Formula)>,
}

impl<D: DeductionRule> UncheckedSerialProof<D> {
    pub fn new(output: D::Formula, inputs: Vec<D::Formula>, proof: Vec<(UncheckedSerialProofStep<D::Parameter>, D::Formula)>) -> Self {
        UncheckedSerialProof { output, inputs, proof}
    }
}

#[derive(Derivative)]
#[derivative(Debug(bound = "D::Formula: Debug, D::Parameter: Debug"))]
#[derivative(Clone(bound = "D::Formula: Clone, D::Parameter: Clone"))]
#[derivative(PartialEq(bound = "D::Formula: PartialEq, D::Parameter: PartialEq"))]
#[derivative(Eq(bound = "D::Formula: Eq, D::Parameter: Eq"))]
pub enum CheckedSerialProofStep<D: DeductionRule>{
    Input(D::Formula, Index),
    Deduce(Deduction<D>, Vec<Index>)
}

impl<D: DeductionRule> CheckedSerialProofStep<D> {
    fn get_output(&self) -> &D::Formula{
        match self {
            CheckedSerialProofStep::Input(f, _) => {&f}
            CheckedSerialProofStep::Deduce(d, _) => {&d.output}
        }
    }
    fn check_step(inputs: &Vec<D::Formula>,
                  deductions: &Vec<CheckedSerialProofStep<D>>,
                  step: UncheckedSerialProofStep<D::Parameter>) -> Option<CheckedSerialProofStep<D>>
        where D::Formula: Clone + Eq, D::Parameter: Clone + Eq {
        Some(match step {
            UncheckedSerialProofStep::Input(i) => {
                CheckedSerialProofStep::Input(inputs.get(i)?.clone(), i)
            }
            UncheckedSerialProofStep::Deduce(params, indices) => {
                let mut input_formulae: Vec<D::Formula> = vec![];
                for &i in &indices {
                    input_formulae.push(deductions.get(i)?.get_output().clone())
                }
                let deduction = D::make_deduction(params, input_formulae)?;
                CheckedSerialProofStep::Deduce(
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
pub struct SerialProof<D: DeductionRule>{
    pub(in crate::proof_manipulation) inputs: Vec<D::Formula>,
    pub(in crate::proof_manipulation) output: D::Formula,
    pub(in crate::proof_manipulation) deductions: Vec<CheckedSerialProofStep<D>>,
}

impl<D: DeductionRule> AbstractParser<UncheckedSerialProof<D>> for SerialProof<D> where D::Formula: Clone + Eq, D::Parameter: Clone + Eq {
    fn parse(pf: UncheckedSerialProof<D>) -> Option<Self> {
        let UncheckedSerialProof {inputs, output, proof} = pf;
        if proof.len() == 0 {return None;}
        let mut deductions: Vec<CheckedSerialProofStep<D>> = vec![];
        for (step, output) in proof.into_iter(){
            let checked_step = CheckedSerialProofStep::check_step(&inputs, &deductions, step)?;
            if *checked_step.get_output() != output {return None;}
            deductions.push(checked_step);
        }
        if output != *deductions[deductions.len() - 1].get_output() {return None;}
        Some(SerialProof {
            inputs,
            output,
            deductions,
        })
    }

    fn un_parse(self) -> UncheckedSerialProof<D> {
        UncheckedSerialProof {
            output: self.output,
            inputs: self.inputs,
            proof: self.deductions.into_iter().map(
                |s| {
                    match s {
                        CheckedSerialProofStep::Input(f, i) =>
                            (UncheckedSerialProofStep::Input(i), f),
                        CheckedSerialProofStep::Deduce(d, indices) =>
                            (UncheckedSerialProofStep::Deduce(d.params, indices), d.output),
                    }
                }
            ).collect(),
        }
    }
}

impl<D: DeductionRule> StrictAbstractParser<UncheckedSerialProof<D>> for SerialProof<D> where D::Formula: Clone + Eq, D::Parameter: Clone + Eq {}

#[cfg(test)]
mod tests {
    use crate::functors::abstract_parser::*;
    use crate::proof_manipulation::deductions::*;
    use crate::proof_manipulation::serial_proofs::*;
    use crate::proof_manipulation::proofs::tests::Decrement;

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
}