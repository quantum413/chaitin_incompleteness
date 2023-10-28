use std::fmt::Debug;
use std::rc::Rc;
use std::vec::Vec;
use derivative::Derivative;
use crate::functors::abstract_parser::AbstractParser;
use crate::proof_manipulation::deductions::{Deduction, DeductionRule, FormalDeduction};
// use crate::proof_manipulation::proofs::ProofStep::CopyInput;
use crate::proof_manipulation::serial_proofs::{CheckedSerialProofStep, SerialProof};

pub type Index = usize;

#[derive(Derivative)]
#[derivative(Debug(bound = "FD::Formula: Debug, FD: Debug"))]
#[derivative(Clone(bound = "FD::Formula: Clone, FD: Clone"))]
#[derivative(PartialEq(bound = "FD::Formula: PartialEq, FD: PartialEq"))]
#[derivative(Eq(bound = "FD::Formula: Eq, FD: Eq"))]
enum InternalProofStep<FD: FormalDeduction>{
    Input(Index),
    Deduce(FD, Vec<Rc<InternalProofStep<FD>>>),
}

#[derive(Derivative)]
#[derivative(Debug(bound = "FD::Formula: Debug, FD: Debug"))]
#[derivative(Clone(bound = "FD::Formula: Clone"))]
#[derivative(PartialEq(bound = "FD::Formula: PartialEq, FD: PartialEq"))]
#[derivative(Eq(bound = "FD::Formula: Eq, FD: Eq"))]
pub struct Proof<FD: FormalDeduction>{
    inputs: Vec<FD::Formula>,
    output: FD::Formula,
    derivation: Rc<InternalProofStep<FD>>,
}

pub struct CopyInputStep<FD: FormalDeduction> {
    inputs: Vec<FD::Formula>,
    index: Index,
}
impl<FD: FormalDeduction> CopyInputStep<FD> {
    pub fn inputs(&self) -> &Vec<FD::Formula> {&self.inputs}
    pub fn index(&self) -> Index {self.index}
}
pub struct DeduceStep<FD: FormalDeduction>{
    inputs: Vec<FD::Formula>,
    sub_proofs: Vec<Proof<FD>>,
    deduction: FD,
}

impl<FD: FormalDeduction> DeduceStep<FD> {
    pub fn inputs(&self) -> &Vec<FD::Formula> {&self.inputs}
    pub fn sub_proofs(&self) -> &Vec<Proof<FD>> {&self.sub_proofs}
    pub fn deduction(&self) -> &FD {&self.deduction}
}
pub enum ProofStep<FD: FormalDeduction>{
    CopyInput(CopyInputStep<FD>),
    Deduce(DeduceStep<FD>),
}
impl<D: DeductionRule> InternalProofStep<Deduction<D>> where D::Formula: Clone, D::Parameter: Clone {
    fn add_to_proof(
        proof: &mut Vec<CheckedSerialProofStep<D>>,
        derivation: Rc<InternalProofStep<Deduction<D>>>,
        inputs: &Vec<D::Formula>
    ) {
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
impl<FD: FormalDeduction> InternalProofStep<FD> {
    fn get_output<'a, 'b: 'a, 'c: 'a>(&'b self,inputs: &'c Vec<FD::Formula>) -> &'a FD::Formula{
        match self {
            InternalProofStep::Input(i) => {&inputs[*i]}
            InternalProofStep::Deduce(d, _) => {&d.output()}
        }
    }
}
impl<D: DeductionRule> AbstractParser<SerialProof<D>> for Proof<Deduction<D>> where D::Formula: Clone + Eq, D::Parameter: Clone + Eq {
    fn parse(input: SerialProof<D>) -> Option<Self> {
        let SerialProof { inputs, output, deductions } = input;
        let mut steps = Vec::<Rc<InternalProofStep<Deduction<D>>>>::new();
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
        Some(Proof {inputs, output, derivation: steps.pop()?})
    }

    fn un_parse(self) -> SerialProof<D> {
        let Proof {inputs, output, derivation} = self;
        let mut proof = Vec::<CheckedSerialProofStep<D>>::new();
        InternalProofStep::add_to_proof(&mut proof, derivation, &inputs);
        SerialProof { inputs, output, deductions: proof, }
    }
}

impl<FD: FormalDeduction> Proof<FD> {
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
            derivation: Rc::new(InternalProofStep::Deduce(
                deduction,
                sub_proofs.into_iter().map(|p| p.derivation).collect(),
            )),
        }
    }

    fn step_copy_input(inputs: Vec<FD::Formula>, index: Index) -> Proof<FD> where FD::Formula: Clone {
        let output = inputs[index].clone();
        Proof {
            inputs,
            output,
            derivation: Rc::new(InternalProofStep::Input(index)),
        }
    }

    pub fn inputs(&self) -> &Vec<FD::Formula> {&self.inputs}
    pub fn output(&self) -> &FD::Formula {&self.output}

    pub fn un_step(self) -> ProofStep<FD> where FD::Formula: Clone, FD: Clone{
        let Proof{inputs, output: _, derivation} = self;
        match &*derivation {
            InternalProofStep::Input(index) => {
                ProofStep::CopyInput(
                    CopyInputStep{
                        inputs,
                        index: *index
                    }
                )
            }
            InternalProofStep::Deduce(d, v) => {
                let sub_proofs = v
                    .iter()
                    .map(|e|
                        Proof{
                            inputs: inputs.clone(),
                            output: e.get_output(&inputs).clone(),
                            derivation: e.clone()
                        }
                    )
                    .collect();
                ProofStep::Deduce(
                    DeduceStep {
                        inputs,
                        sub_proofs,
                        deduction: d.clone()
                    }
                )
            }
        }
    }

    pub fn compose(inputs: Vec<FD::Formula>, sub_proofs: Vec<Proof<FD>>, top_proof: Proof<FD>)
        -> Option<Proof<FD>> where FD::Formula: Clone + Eq, FD: Clone {
        let top_inputs = top_proof.inputs().clone();
        match top_proof.un_step() {
            ProofStep::CopyInput(step) => {
                if sub_proofs.iter().any(|p| p.inputs() != &inputs) {return None;}
                if sub_proofs.iter().map(|p| p.output())
                    .ne(top_inputs.iter()) {return None;}
                Some(sub_proofs[step.index()].clone())
            }
            ProofStep::Deduce(step) => {
                let mut semi_sub_proofs = Vec::<Proof<FD>>::new();
                for p in step.sub_proofs.iter() {
                    semi_sub_proofs.push(
                        Proof::compose(
                            inputs.clone(),
                            sub_proofs.clone(),
                            p.clone(),
                        )?
                    )
                }
                Proof::deduce(
                    inputs.clone(),
                    semi_sub_proofs,
                    step.deduction().clone(),
                )
            }
        }
    }
}

impl<FD: FormalDeduction> ProofStep<FD> {
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
}