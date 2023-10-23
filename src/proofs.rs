use std::fmt::Debug;
use std::vec::Vec;
use impl_tools::autoimpl;

type Index = usize;

trait DeductionRule {
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

#[autoimpl(Debug where D::Formula: Debug, D::Parameter: Debug)]
#[autoimpl(Clone where D::Formula: Clone, D::Parameter: Clone)]
#[autoimpl(PartialEq where D::Formula: PartialEq, D::Parameter: PartialEq)]
#[autoimpl(Eq where D::Formula: Eq, D::Parameter: Eq)]
struct Deduction<D: DeductionRule>{
    params: D::Parameter,
    inputs: Vec<D::Formula>,
    output: D::Formula,
}

impl<D: DeductionRule> Deduction<D> {
    fn new(params: D::Parameter, inputs: Vec<D::Formula>) -> Option<Self>
        where D::Parameter: Clone, D::Formula: Clone{
        D::deduce(params.clone(), inputs.clone()).map(
            |output| Deduction {params, inputs, output}
        )
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
enum ProofStep<P> {
    Input(Index),
    Deduce(P, Vec<Index>),
}

#[autoimpl(Debug where D::Formula: Debug, D::Parameter: Debug)]
#[autoimpl(Clone where D::Formula: Clone, D::Parameter: Clone)]
#[autoimpl(PartialEq where D::Formula: PartialEq, D::Parameter: PartialEq)]
#[autoimpl(Eq where D::Formula: Eq, D::Parameter: Eq)]
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

trait AbstractParser<S> : Sized{
    fn parse(input: S) -> Option<Self>;
    fn un_parse(self) -> S;
    fn check_un_parse(self) -> bool where Self: Clone + Eq{
        if let Some(parse_un_parse) =
            <Self as AbstractParser<S>>::parse(
                <Self as AbstractParser<S>>::un_parse(
                    self.clone()
                )
            ){
            parse_un_parse == self
        }
        else {false}
    }
}

trait StrictAbstractParser<S: Eq + Clone> : AbstractParser<S> + Clone{
    fn check_parse(input: S) -> bool{
        if let Some(parsed) = Self::parse(input.clone()) {
            input == parsed.un_parse()
        }
        else { true }
    }
}

#[autoimpl(PartialEq where D::Formula: PartialEq, D::Parameter: PartialEq)]
#[autoimpl(Debug     where D::Formula: Debug    , D::Parameter: Debug    )]
#[autoimpl(Eq        where D::Formula: Eq       , D::Parameter: Eq       )]
#[autoimpl(Clone     where D::Formula: Clone    , D::Parameter: Clone    )]
enum CheckedProofStep<D: DeductionRule>{
    Input(D::Formula, Index),
    Deduce(Deduction<D>, Vec<Index>)
}
#[autoimpl(Debug where D::Formula: Debug, D::Parameter: Debug)]
#[autoimpl(Clone where D::Formula: Clone, D::Parameter: Clone)]
#[autoimpl(PartialEq where D::Formula: PartialEq, D::Parameter: PartialEq)]
#[autoimpl(Eq where D::Formula: Eq, D::Parameter: Eq)]
struct Proof<D: DeductionRule>{
    inputs: Vec<D::Formula>,
    output: D::Formula,
    deductions: Vec<CheckedProofStep<D>>,
}

impl<D: DeductionRule> AbstractParser<UncheckedProof<D>> for Proof<D> where D::Formula: Clone + Eq, D::Parameter: Clone + Eq {
    fn parse(pf: UncheckedProof<D>) -> Option<Self> {
        let UncheckedProof{inputs, output: result, proof} = pf;
        let mut deductions: Vec<CheckedProofStep<D>> = vec![];
        for (step, output) in proof.into_iter(){
            match step {
                ProofStep::Input(i) => {
                    // TODO: check matches step output
                    deductions.push(CheckedProofStep::Input(inputs[i].clone(), i)); // TODO: check out of bounds
                }
                ProofStep::Deduce(params, indices ) => {
                    let mut input_formulae: Vec<D::Formula> = vec![];
                    for &i in &indices {
                        input_formulae.push(inputs[i].clone()) // TODO: Check out of bounds
                    }
                    // TODO: Check outputs match
                    deductions.push(CheckedProofStep::Deduce(
                        D::make_deduction(params, input_formulae)?,
                        indices
                    ));
                }
            }
            // let mut input_formulae = vec![];
            // for &i in &indices{
            //     input_formulae.push(if i < inputs.len() {
            //         Some(inputs[i].clone()) }
            //     else if i < inputs.len() + deductions.len() {
            //         todo!()
            //         // Some((deductions[i].0).output.clone())
            //     }
            //     else { todo!() }?);
            // }
            // let deduction = D::make_deduction(params, input_formulae)?;
            // if deduction.output != output {return None;}
            // deductions.push((deduction, indices));
        }
        Some(Proof{
            inputs,
            output: result,
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
                        CheckedProofStep::Input(f, i) => (ProofStep::Input(i), f),
                        CheckedProofStep::Deduce(d, indices) => (ProofStep::Deduce(d.params, indices), d.output),
                    }
                }
            ).collect(),
        }
    }
}

impl<D: DeductionRule> StrictAbstractParser<UncheckedProof<D>> for Proof<D> where D::Formula: Clone + Eq, D::Parameter: Clone + Eq {}

#[cfg(test)]
mod tests {
    use crate::proofs::*;

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
            19usize,
        );
        assert!(Proof::parse(pf).is_none());
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
}