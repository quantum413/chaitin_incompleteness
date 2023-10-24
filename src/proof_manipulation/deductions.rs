use std::fmt::Debug;
use derivative::Derivative;

pub trait DeductionRule {
    type Formula;
    type Parameter;
    fn deduce(params: Self::Parameter, inputs: Vec<Self::Formula>) -> Option<Self::Formula>;
    fn make_deduction(params: Self::Parameter, inputs: Vec<Self::Formula>)
        -> Option<Deduction<Self>>
        where Self: Sized, Self::Formula : Eq + Clone, Self::Parameter: Eq + Clone
    {
        Deduction::<Self>::new(params, inputs)
    }
}

#[derive(Derivative)]
#[derivative(Debug(bound = "D::Formula: Debug, D::Parameter: Debug"))]
#[derivative(Clone(bound = "D::Formula: Clone, D::Parameter: Clone"))]
#[derivative(PartialEq(bound = "D::Formula: PartialEq, D::Parameter: PartialEq"))]
#[derivative(Eq(bound = "D::Formula: Eq, D::Parameter: Eq"))]
pub struct Deduction<D: DeductionRule>{
    pub(in crate::proof_manipulation) params: D::Parameter,
    pub(in crate::proof_manipulation) inputs: Vec<D::Formula>,
    pub(in crate::proof_manipulation) output: D::Formula,
}

impl<D: DeductionRule> Deduction<D> {
    pub fn new(params: D::Parameter, inputs: Vec<D::Formula>) -> Option<Self>
        where D::Parameter: Clone, D::Formula: Clone{
        D::deduce(params.clone(), inputs.clone()).map(
            |output| Deduction {params, inputs, output}
        )
    }
    pub fn params(&self) -> &D::Parameter {&self.params}
    pub fn inputs(&self) -> &Vec<D::Formula> {&self.inputs}
    pub fn output(&self) -> &D::Formula {&self.output}
}

pub trait FormalDeduction {
    type Formula;
    fn inputs(&self) -> &Vec<Self::Formula>;
    fn output(&self) -> &Self::Formula;
}

impl<D: DeductionRule> FormalDeduction for Deduction<D> {
    type Formula = D::Formula;

    fn inputs(&self) -> &Vec<Self::Formula> {self.inputs()}

    fn output(&self) -> &Self::Formula {self.output()}
}