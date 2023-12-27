use std::cell::{RefCell};
use std::fmt::Debug;
use std::rc::Rc;
use std::vec::Vec;
use derivative::Derivative;
use crate::functors::abstract_parser::AbstractParser;
use crate::functors::recursive::{UnpackRc, UnpackRcWrapper};
use crate::functors::unpack::Unpack;
use crate::proof_manipulation::deductions::{Deduction, DeductionRule, FormalDeduction};
use crate::proof_manipulation::serial_proofs::{CheckedSerialProofStep, SerialProof};

pub type Index = usize;

#[derive(Debug, Clone, PartialEq, Eq)]
enum InternalProofStep<FD> {
    Input(Index),
    Deduce(FD, Vec<InternalProof<FD>>),
}
#[derive(Debug, Clone, PartialEq, Eq)]
enum InternalProofStepData<FD> {
    Input(Index),
    Deduce(FD),
}
#[derive(Debug, Clone, PartialEq, Eq)]
struct InternalProof<FD>{
    internal: Rc<InternalProofStep<FD>>,
}

#[derive(Derivative)]
#[derivative(Debug(bound = "FD::Formula: Debug, FD: Debug"))]
#[derivative(Clone(bound = "FD::Formula: Clone"))]
#[derivative(PartialEq(bound = "FD::Formula: PartialEq, FD: PartialEq"))]
#[derivative(Eq(bound = "FD::Formula: Eq, FD: Eq"))]
pub struct Proof<FD: FormalDeduction> where FD::Formula: Clone, FD: Clone {
    inputs: Vec<FD::Formula>,
    output: FD::Formula,
    derivation: UnpackRcWrapper<InternalProof<FD>>,
}

pub struct CopyInputStep<FD: FormalDeduction> {
    inputs: Vec<FD::Formula>,
    index: Index,
}
impl<FD: FormalDeduction> CopyInputStep<FD> {
    pub fn inputs(&self) -> &Vec<FD::Formula> {&self.inputs}
    pub fn index(&self) -> Index {self.index}
}
pub struct DeduceStep<FD: FormalDeduction> where FD::Formula: Clone, FD: Clone {
    inputs: Vec<FD::Formula>,
    sub_proofs: Vec<Proof<FD>>,
    deduction: FD,
}

impl<FD: FormalDeduction> DeduceStep<FD> where FD::Formula: Clone, FD: Clone {
    pub fn inputs(&self) -> &Vec<FD::Formula> {&self.inputs}
    pub fn sub_proofs(&self) -> &Vec<Proof<FD>> {&self.sub_proofs}
    pub fn deduction(&self) -> &FD {&self.deduction}
}
pub enum ProofStep<FD: FormalDeduction> where FD::Formula: Clone, FD: Clone {
    CopyInput(CopyInputStep<FD>),
    Deduce(DeduceStep<FD>),
}
impl<D: DeductionRule> InternalProof<Deduction<D>> where D::Formula: Clone, D::Parameter: Clone {
    fn parse_step(
        proof_step_data: InternalProofStepData<Deduction<D>>,
        sub_indices: Vec<Index>,
        serial_proof_steps: &RefCell<Vec<CheckedSerialProofStep<D>>>,
        inputs: &Vec<D::Formula>,
    ) -> Index {
        let out_index = serial_proof_steps.borrow().len();
        match proof_step_data {
            InternalProofStepData::Input(i) => {
                serial_proof_steps.borrow_mut().push(CheckedSerialProofStep::Input(inputs[i].clone(), i));
            }
            InternalProofStepData::Deduce(d) => {
                serial_proof_steps.borrow_mut().push(CheckedSerialProofStep::Deduce(d.clone(), sub_indices));
            }
        }
        out_index
    }
}
impl<FD: FormalDeduction> InternalProof<FD> {
    fn get_output<'a, 'b: 'a, 'c: 'a>(&'b self,inputs: &'c Vec<FD::Formula>) -> &'a FD::Formula{
        match &*self.internal {
            InternalProofStep::Input(i) => {&inputs[*i]}
            InternalProofStep::Deduce(d, _) => {&d.output()}
        }
    }
}
impl<D: DeductionRule> AbstractParser<SerialProof<D>> for Proof<Deduction<D>> where D::Formula: Clone + Eq, D::Parameter: Clone + Eq {
    fn parse(input: SerialProof<D>) -> Option<Self> {
        let SerialProof { inputs, output, deductions } = input;
        let mut steps = Vec::<UnpackRcWrapper<InternalProof<Deduction<D>>>>::new();
        for deduction in deductions {
            let new_step =
                match deduction {
                    CheckedSerialProofStep::Input(_, i) => { InternalProofStep::Input(i)}
                    CheckedSerialProofStep::Deduce(d, ded_indices) => {
                        InternalProofStep::Deduce(
                            d,
                            ded_indices
                                .into_iter()
                                .map(|i| steps[i].internal().clone())
                                .collect()
                        )
                    }
                };
            steps.push(UnpackRcWrapper::new(InternalProof { internal: Rc::new(new_step) }));
        }
        Some(Proof {inputs, output, derivation: steps.pop()?})
    }

    fn un_parse(self) -> SerialProof<D> {
        let Proof {inputs, output, derivation} = self;
        let proof = RefCell::new(Vec::<CheckedSerialProofStep<D>>::new());
        derivation.build(|step: InternalProofStepData<Deduction<D>>, sub_indices: Vec<Index>| InternalProof::parse_step(step, sub_indices, &proof, &inputs));
        SerialProof { inputs, output, deductions: proof.take(), }
    }
}

impl<FD: FormalDeduction> Proof<FD> where FD::Formula: Clone, FD: Clone {
    pub fn deduce(inputs: Vec<FD::Formula>, sub_proofs: Vec<Proof<FD>>, deduction: FD) -> Option<Proof<FD>> where FD::Formula: Clone + Eq{
        Some(ProofStep::make_deduce_step(inputs, sub_proofs, deduction)?.step())
    }
    pub fn copy_input(inputs: Vec<FD::Formula>, index: Index) -> Option<Proof<FD>> where FD::Formula: Clone{
        Some(ProofStep::make_copy_input_step(inputs, index)?.step())
    }
    fn step_deduce(inputs: Vec<FD::Formula>, sub_proofs: Vec<Proof<FD>>, deduction: FD) -> Proof<FD> where FD::Formula: Clone{
        Proof {
            inputs,
            output: deduction.output().clone(),
            derivation: UnpackRcWrapper::new(InternalProof { internal: Rc::new( InternalProofStep::Deduce(
                deduction,
                sub_proofs.into_iter().map(|p| p.derivation.internal().clone()).collect(),
            )) }),
        }
    }

    fn step_copy_input(inputs: Vec<FD::Formula>, index: Index) -> Proof<FD> where FD::Formula: Clone {
        let output = inputs[index].clone();
        Proof {
            inputs,
            output,
            derivation: UnpackRcWrapper::new(InternalProof { internal:  Rc::new(InternalProofStep::Input(index))}),
        }
    }

    pub fn inputs(&self) -> &Vec<FD::Formula> {&self.inputs}
    pub fn output(&self) -> &FD::Formula {&self.output}

    pub fn un_step(self) -> ProofStep<FD> where FD::Formula: Clone, FD: Clone{
        let Proof{inputs, output: _, derivation} = self;
        match derivation.un_step_data() {
            InternalProofStepData::Input(i) => {
                ProofStep::CopyInput(CopyInputStep{inputs, index: i})
            }
            InternalProofStepData::Deduce(d) => {
                let sub_proofs =
                    derivation
                        .un_step_subs()
                        .into_iter()
                        .map(
                            |s|
                                Proof{
                                    inputs: inputs.clone(),
                                    output: s.internal().get_output(&inputs).clone(),
                                    derivation: s,
                                }
                        )
                        .collect();
                ProofStep::Deduce(DeduceStep{inputs, sub_proofs, deduction: d})
            }
        }
    }
    fn compose_step(
        step: InternalProofStepData<FD>,
        built_proofs: Vec<Option<Proof<FD>>>,
        inputs: &Vec<FD::Formula>,
        sub_proofs: &Vec<Proof<FD>>,
    ) -> Option<Proof<FD>>
        where FD::Formula: Clone + Eq, FD: Clone  {
        match step {
            InternalProofStepData::Input(i) => {
                Some(sub_proofs[i].clone())
            }
            InternalProofStepData::Deduce(d) => {
                let checked_built_proofs = built_proofs.into_iter().collect::<Option<Vec<_>>>()?;
                Proof::deduce(
                    inputs.clone(),
                    checked_built_proofs,
                    d
                )
            }
        }
    }
    pub fn compose(inputs: Vec<FD::Formula>, sub_proofs: Vec<Proof<FD>>, top_proof: Proof<FD>)
        -> Option<Proof<FD>> where FD::Formula: Clone + Eq, FD: Clone {
        if sub_proofs.iter().any(|p| p.inputs() != &inputs) {return None;}
        if sub_proofs.iter().map(|p| p.output())
            .ne(top_proof.inputs().iter()) {return None;}
        top_proof.derivation.build::<Option<Proof<FD>>, _>(
            |step, built|
                Proof::compose_step(step, built, &inputs, &sub_proofs)
        )
    }
}

pub enum ProofStepData<FD> {
    CopyInputStep(Index),
    DeduceStep(FD),
}

impl<FD: FormalDeduction> UnpackRc for InternalProof<FD> where FD::Formula: Clone, FD: Clone {
    type StepData = InternalProofStepData<FD>;
    type StepRef = InternalProofStep<FD>;
    fn rc(&self) -> &Rc<Self::StepRef> {
        &self.internal
    }
    fn un_step_data(&self) -> Self::StepData {
        match &*self.internal {
            InternalProofStep::Input(i) => { InternalProofStepData::Input(*i)},
            InternalProofStep::Deduce(d, _) => { InternalProofStepData::Deduce(d.clone())}
        }
    }
    fn un_step_subs(&self) -> Vec<Self> {
        match &*self.internal {
            InternalProofStep::Input(_) => { vec![] },
            InternalProofStep::Deduce(_, v) => { v.clone() },
        }
    }
}

impl<FD: FormalDeduction> ProofStep<FD> where FD::Formula: Clone, FD: Clone {
    pub fn make_copy_input_step(inputs: Vec<FD::Formula>, index: Index) -> Option<ProofStep<FD>> {
        if index >= inputs.len() {return None;}
        Some(ProofStep::CopyInput(CopyInputStep {inputs, index}))
    }
    pub fn make_deduce_step(inputs: Vec<FD::Formula>, sub_proofs: Vec<Proof<FD>>, deduction: FD) -> Option<ProofStep<FD>> where FD::Formula: Eq{
        if sub_proofs.iter().any(|e| *e.inputs != inputs) ||
            sub_proofs.iter().map(|e|-> &FD::Formula {&e.output})
            .ne(deduction.inputs().iter()) {return None;}
        Some(ProofStep::Deduce(DeduceStep {inputs, sub_proofs, deduction}))
    }
    pub fn step(self) -> Proof<FD> where FD::Formula: Clone {
        match self {
            ProofStep::CopyInput(CopyInputStep{inputs, index}) => {
                Proof::step_copy_input(inputs, index)
            }
            ProofStep::Deduce(DeduceStep{inputs, sub_proofs, deduction}) => {
                Proof::step_deduce(inputs, sub_proofs, deduction)
            }
        }
    }
}

#[cfg(test)]
pub(in crate) mod tests {
    use crate::functors::abstract_parser::AbstractParser;
    use crate::proof_manipulation::serial_proofs::{UncheckedSerialProof, UncheckedSerialProofStep};
    use super::super::deductions::DeductionRule;
    use super::*;

    #[derive(Debug)]
    pub(in crate) struct Decrement;

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
    pub(in crate) struct Product;

    impl DeductionRule for Product{
        type Formula = usize;
        type Parameter = ();

        fn deduce(_: Self::Parameter, inputs: Vec<Self::Formula>) -> Option<Self::Formula> {
            if inputs.len() != 2 {return None;}
            Some(inputs[0] * inputs[1])
        }
    }
    type DProduct = Deduction<Product>;

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

    #[test]
    fn proof_copy_input(){
        let input = vec![10usize, 20usize, 30usize];
        assert!(Proof::<DProduct>::copy_input(input.clone(), 3).is_none());
        let pf = Proof::<DProduct>::copy_input(input.clone(), 1).unwrap();
        assert_eq!(*pf.inputs(), input);
        assert_eq!(*pf.output(), 20usize);
    }

    #[test]
    fn proof_deduce(){
        let input_1 = vec![2usize, 3usize, 5usize];
        let input_2 = vec![2usize, 3usize, 4usize];
        let pf_1_1 = Proof::<DProduct>::copy_input(input_1.clone(), 0).unwrap();
        let pf_1_2 = Proof::<DProduct>::copy_input(input_1.clone(), 1).unwrap();
        let pf_2_2 = Proof::<DProduct>::copy_input(input_2.clone(), 1).unwrap();
        let ded = Product::make_deduction((), vec![2usize, 3usize]).unwrap();
        let pf = Proof::deduce(input_1.clone(), vec![pf_1_1.clone(), pf_1_2.clone()], ded.clone()).unwrap();
        assert!(Proof::check_un_parse(pf.clone()));
        assert!(SerialProof::check_un_parse(Proof::un_parse(pf.clone())));
        assert!(Proof::deduce(input_1.clone(), vec![pf_1_1.clone(), pf_2_2.clone()], ded.clone()).is_none());
        assert!(Proof::deduce(input_1.clone(), vec![pf_1_1.clone()], ded.clone()).is_none());
        assert!(Proof::deduce(input_1.clone(), vec![pf_1_1.clone(), pf_1_1.clone()], ded.clone()).is_none());
        assert_eq!(pf.clone().un_step().step(), pf.clone());
        assert_eq!(pf_1_1.clone().un_step().step(), pf_1_1.clone());
    }
    pub(in crate) fn make_prod_150() -> Proof<Deduction<Product>> {
        let input_1 = vec![2usize, 3usize, 5usize];
        Proof::deduce(
            input_1.clone(),
            vec![
                Proof::deduce(
                    input_1.clone(),
                    vec![
                        Proof::deduce(
                            input_1.clone(),
                            vec![
                                Proof::copy_input(input_1.clone(), 0).unwrap(),
                                Proof::copy_input(input_1.clone(), 1).unwrap(),
                            ],
                            Product::make_deduction((), vec![2usize, 3usize]).unwrap()
                        ).unwrap(),
                        Proof::copy_input(input_1.clone(), 2).unwrap(),
                    ],
                    Product::make_deduction((), vec![6usize, 5usize]).unwrap(),
                ).unwrap(),
                Proof::copy_input(input_1.clone(), 2).unwrap(),
            ],
            Product::make_deduction((), vec![30usize, 5usize]).unwrap(),
        ).unwrap()
    }
    #[test]
    pub fn proof_chaining(){
        let input_1 = vec![2usize, 3usize, 5usize];
        let pf_2: Proof<Deduction<Product>> = Proof::copy_input(input_1.clone(), 0usize).unwrap();
        let pf_3: Proof<Deduction<Product>> = Proof::copy_input(input_1.clone(), 1usize).unwrap();
        let pf_5: Proof<Deduction<Product>> = Proof::copy_input(input_1.clone(), 2usize).unwrap();
        let pf_6 = Proof::deduce(
            input_1.clone(),
            vec![pf_2.clone(), pf_3.clone()],
            Product::make_deduction((), vec![2usize, 3usize]).unwrap()
        ).unwrap();
        assert_eq!(*pf_6.output(), 6usize);
        assert_eq!(*pf_6.inputs(), input_1.clone());

        let input_sub = vec![6usize, 5usize];
        let pf_sub_30 = Proof::deduce(
            input_sub.clone(),
            vec![
                Proof::copy_input(input_sub.clone(), 0).unwrap(),
                Proof::copy_input(input_sub.clone(), 1).unwrap(),
            ],
            Product::make_deduction((), vec![6usize, 5usize]).unwrap(),
        ).unwrap();
        assert_eq!(*pf_sub_30.output(), 30usize);
        assert_eq!(*pf_sub_30.inputs(), input_sub.clone());

        let pf_30 = Proof::compose(
            input_1.clone(),
            vec![
                pf_6.clone(),
                pf_5.clone(),
            ],
            pf_sub_30.clone(),
        ).unwrap();
        assert_eq!(pf_30.inputs(), &input_1);
        assert_eq!(*pf_30.output(), 30);

        let pf_sub_150 = Proof::deduce(
            input_sub.clone(),
            vec![pf_sub_30, Proof::copy_input(input_sub.clone(), 1).unwrap()],
            Product::make_deduction((), vec![30usize, 5usize]).unwrap(),
        ).unwrap();
        let pf_150 = Proof::compose(
            input_1.clone(),
            vec![
                pf_6.clone(),
                pf_5.clone(),
            ],
            pf_sub_150.clone()
        ).unwrap();
        assert_eq!(pf_150.inputs(), &input_1);
        assert_eq!(*pf_150.output(), 150);
    }

    #[test]
    fn proof_chaining_counterexamples(){
        let input_1 = vec![2usize, 3usize, 5usize];
        let pf_2: Proof<Deduction<Product>> = Proof::copy_input(input_1.clone(), 0usize).unwrap();
        let pf_3: Proof<Deduction<Product>> = Proof::copy_input(input_1.clone(), 1usize).unwrap();
        let pf_6_wrong = Proof::deduce(
            vec![2usize, 3usize],
            vec![
                Proof::copy_input(vec![2usize, 3usize], 0usize).unwrap(),
                Proof::copy_input(vec![2usize, 3usize], 1usize).unwrap(),
            ],
            Product::make_deduction((), vec![2usize, 3usize]).unwrap()
        ).unwrap();
        assert!(Proof::compose(input_1.clone(), vec![pf_2.clone(), pf_3.clone()], pf_2.clone()).is_none());
        assert!(Proof::compose(
            input_1.clone(),
            vec![pf_2.clone(), pf_6_wrong.clone()],
            Proof::copy_input(vec![2usize, 6usize], 0usize).unwrap()
        ).is_none());
    }
}