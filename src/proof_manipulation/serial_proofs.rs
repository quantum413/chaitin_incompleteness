use std::fmt::Debug;
use derivative::Derivative;
use crate::abstract_parser::{AbstractParser, StrictAbstractParser};
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
