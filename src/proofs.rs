use std::fmt::{Debug, Formatter};
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

// impl<D: DeductionRule> Debug for Deduction<D> where D::Formula: Debug, D::Parameter: Debug {
//     fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
//         let Deduction {params, inputs, output} = self;
//         f
//             .debug_struct("Deduction")
//             .field("params", &params)
//             .field("inputs", &inputs)
//             .field("output", &output)
//             .finish()
//     }
// }

impl<D: DeductionRule> Deduction<D> {
    fn new(params: D::Parameter, inputs: Vec<D::Formula>) -> Option<Self>
        where D::Parameter: Clone, D::Formula: Clone{
        D::deduce(params.clone(), inputs.clone()).map(
            |output| Deduction {params, inputs, output}
        )
    }

    // fn output(&self) -> &D::Formula { &self.output }
    // fn params(&self) -> &D::Parameter { &self.params }
    // fn inputs(&self) -> &Vec<D::Formula> { &self.inputs }
}

// impl<D: DeductionRule>
//         PartialEq for Deduction<D> where D::Formula: PartialEq, D::Parameter: PartialEq, {
//     fn eq(&self, other: &Self) -> bool {
//         (&self.params, &self.inputs, &self.output) ==
//             (&other.params, &other.inputs, &other.output)
//     }
// }
//
// impl<D: DeductionRule> Eq for Deduction<D> where D::Formula: Eq, D::Parameter: Eq,  {}

// #[derive(Debug)]
#[autoimpl(Debug where D::Formula: Debug, D::Parameter: Debug)]
#[autoimpl(Clone where D::Formula: Clone, D::Parameter: Clone)]
#[autoimpl(PartialEq where D::Formula: PartialEq, D::Parameter: PartialEq)]
#[autoimpl(Eq where D::Formula: Eq, D::Parameter: Eq)]
struct UncheckedProof<D: DeductionRule> {
    result: D::Formula,
    inputs: Vec<D::Formula>,
    proof: Vec<((D::Parameter, Vec<Index>), D::Formula)>,
}

impl<D: DeductionRule> UncheckedProof<D> {
    fn new(result: D::Formula, inputs: Vec<D::Formula>, proof: Vec<((D::Parameter, Vec<Index>), D::Formula)>) -> Self {
        UncheckedProof {result, inputs, proof}
    }
}

// impl<D: DeductionRule> PartialEq for UncheckedProof<D> where D::Formula: PartialEq, D::Parameter: PartialEq{
//     fn eq(&self, other: &Self) -> bool {
//         self.result == other.result && self.inputs == other.inputs && self.proof == other.proof
//     }
// }
//
// impl<D: DeductionRule> Eq for UncheckedProof<D> where D::Formula: Eq, D::Parameter: Eq {}
//
// impl<D: DeductionRule> Clone for UncheckedProof<D> where D::Formula: Clone, D::Parameter: Clone{
//     fn clone(&self) -> Self {
//         UncheckedProof {
//             result: self.result.clone(),
//             inputs: self.inputs.clone(),
//             proof: self.proof.clone(),
//         }
//     }
// }
// trait AbstractParser<S> : Eq + Sized{
//     fn parse(input: &S) -> Option<Self>;
//     fn un_parse(&self) -> S;
//     fn check_un_parse(&self) -> bool{
//         let parse_un_parse_op =
//             <Self as AbstractParser<S>>::parse(
//                 &<Self as AbstractParser<S>>::un_parse(
//                     &self
//                 )
//             );
//         if let Some(parse_un_parse) = parse_un_parse_op {
//             self == &parse_un_parse
//         }
//         else {
//             false
//         }
//     }
// }
//
// trait StrictAbstractParser<S: Eq> : AbstractParser<S>{
//     fn check_parse(input: &S) -> bool{
//         if let Some(parsed) = Self::parse(input) {
//             input == &parsed.un_parse()
//         }
//         else { true }
//     }
// }
#[autoimpl(Debug where D::Formula: Debug, D::Parameter: Debug)]
#[autoimpl(Clone where D::Formula: Clone, D::Parameter: Clone)]
#[autoimpl(PartialEq where D::Formula: PartialEq, D::Parameter: PartialEq)]
#[autoimpl(Eq where D::Formula: Eq, D::Parameter: Eq)]
struct Proof<D: DeductionRule>{
    inputs: Vec<D::Formula>,
    output: D::Formula,
    deductions: Vec<(Deduction<D>, Vec<Index>)>,
}

// impl<D: DeductionRule> Debug for Proof<D> where D::Formula: Debug, D::Parameter: Debug{
//     fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
//         let Proof {inputs, output, deductions} = self;
//         f
//             .debug_struct("Proof")
//             .field("inputs", &inputs)
//             .field("output", &output)
//             .field("deductions", &deductions)
//             .finish()
//     }
// }
// impl <D: DeductionRule> PartialEq for Proof<D> where D::Formula: PartialEq, D::Parameter: PartialEq{
//     fn eq(&self, other: &Self) -> bool {
//         self.inputs == other.inputs && self.output == other.output && self.deductions == other.deductions
//     }
// }
//
// impl <D: DeductionRule> Eq for Proof<D> where D::Formula: Eq, D::Parameter: Eq {}

impl <D: DeductionRule> Proof<D> {
    fn check(pf: UncheckedProof<D>) -> Option<Self> where D::Formula: Eq, D::Parameter: Eq{
        // let inputs : Vec<&'a D::Formula> = (&pf.inputs).into_iter().collect();
        // let output = &pf.result; // TODO: remove unchecked usage of result
        // let mut deductions: Vec<(Deduction<D>, Vec<Index>)> = vec![];
        // for ((param, indices), output) in (&pf.proof).into_iter(){
        //     let mut input_formulae = vec![];
        //     for &i in indices{
        //         input_formulae.push(if i < (&inputs).len() { Some(inputs[i]) }
        //         else if i < (&inputs).len() + (&deductions).len() { Some((&deductions[i].0).get_output()) }
        //         else { None }?);
        //     }
        //     let deduction = D::make_deduction(
        //         &param,
        //         &input_formulae,
        //     ) ?;
        //     deductions.push((deduction, indices.clone())); // TODO: check output
        // }
        // Some(Proof {
        //     inputs,
        //     output,
        //     deductions,
        // })
        todo!()
    }

    fn un_check(&self) -> UncheckedProof<D> where D::Formula : Clone, D::Parameter : Clone {
        UncheckedProof{
            result: self.output.clone(),
            inputs: (&self.inputs).into_iter().map(|e| e.clone()).collect(), // TODO
            proof: vec![], // TODO
        }
    }
}
// impl<'a, D: DeductionRule> AbstractParser<UncheckedProof<D>> for Proof<'a, D> where D::Formula: Eq, D::Parameter: Eq, {
//     fn parse(input: &UncheckedProof<D>) -> Option<Self> {
//         // let inputs: Vec<& D::Formula> = input.inputs.into_iter().collect();
//         // let deductions: Vec<Deduction<D>> = vec![];
//         // let get_formula : fn(Index) -> Option<&D::Formula> = |i: Index| {
//         //     if i < inputs.len() { Some(inputs[i]) }
//         //     else if i < inputs.len() + deductions.len() { Some(deductions[i].get_output()) }
//         //     else { None }
//         // };
//         //
//         // todo!()
//         return Some(Proof{inputs: vec![], output: &input.result.clone() , deductions: vec![]})
//     }
//
//     fn un_parse(&self) -> UncheckedProof<D> {
//         todo!()
//     }
// }

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
    fn decrement_proofs(){
        let pf: UncheckedProof<Decrement> = UncheckedProof::new(
            19usize,
            vec![20usize],
            vec![(
                ("d".to_string(), vec![20usize]),
                19usize
            )]
        );
        let checked = Proof::check(pf.clone()).unwrap();
        assert_eq!(pf, checked.un_check());
    }
}