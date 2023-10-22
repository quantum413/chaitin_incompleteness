use std::fmt::{Debug, Formatter};
use std::vec::Vec;

type Index = usize;

trait DeductionRule {
    type Formula;
    type Parameter;
    fn deduce(params: &Self::Parameter, inputs: &Vec<&Self::Formula>) -> Option<Self::Formula>;
    fn make_deduction<'a>(params: &'a Self::Parameter, inputs: &Vec<&'a Self::Formula>)
        -> Option<Deduction<'a, Self>>
        where Self: Sized, Self::Formula : Eq, Self::Parameter: Eq
    {
        Deduction::<'a, Self>::new(params, inputs.clone())
    }
}

struct Deduction<'a, D: DeductionRule>{
    params: &'a D::Parameter,
    inputs: Vec<&'a D::Formula>,
    output: D::Formula,
}

impl<'a, D: DeductionRule> Debug for Deduction<'a, D> where D::Formula: Debug, D::Parameter: Debug {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let Deduction {params, inputs, output} = self;
        f
            .debug_struct("Deduction")
            .field("params", &params)
            .field("inputs", &inputs)
            .field("output", &output)
            .finish()
    }
}

impl<'a, D: DeductionRule> Deduction<'a, D> {
    fn new(params: &'a D::Parameter, inputs: Vec<&'a D::Formula>) -> Option<Self>{
        D::deduce(params, &inputs).map(
            |output| Deduction {params, inputs, output}
        )
    }

    fn get_output(&self) -> &D::Formula { &self.output }
    fn get_params(&self) -> &'a D::Parameter { self.params }
    fn get_inputs(&self) -> &Vec<&'a D::Formula> { &self.inputs }
}

impl<'a, D: DeductionRule>
        PartialEq for Deduction<'a, D> where D::Formula: PartialEq, D::Parameter: PartialEq, {
    fn eq(&self, other: &Self) -> bool {
        (&self.params, &self.inputs, &self.output) ==
            (&other.params, &other.inputs, &other.output)
    }
}

impl<'a, D: DeductionRule> Eq for Deduction<'a, D> where D::Formula: Eq + PartialEq, D::Parameter: Eq + PartialEq,  {}

#[derive(Debug)]
struct UncheckedProof<D: DeductionRule> {
    result: D::Formula,
    inputs: Vec<D::Formula>,
    proof: Vec<((D::Parameter, Vec<Index>), D::Formula)>,
}

impl<D: DeductionRule> UncheckedProof<D> {
    fn new(result: D::Formula, inputs: Vec<D::Formula>, proof: Vec<((D::Parameter, Vec<Index>), D::Formula)>) -> Self {
        UncheckedProof {result, inputs, proof} // TODO
    }
}

impl<D: DeductionRule> PartialEq for UncheckedProof<D> where D::Formula: PartialEq, D::Parameter: PartialEq{
    fn eq(&self, other: &Self) -> bool {
        self.result == other.result && self.inputs == other.inputs && self.proof == other.proof
    }
}

impl<D: DeductionRule> Eq for UncheckedProof<D> where D::Formula: Eq, D::Parameter: Eq {}

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

struct Proof<'a, D: DeductionRule>{
    inputs: Vec<&'a D::Formula>,
    output: &'a D::Formula,
    deductions: Vec<(Deduction<'a, D>, Vec<Index>)>,
}

impl<'a, D: DeductionRule> Debug for Proof<'a, D> where D::Formula: Debug, D::Parameter: Debug{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let Proof {inputs, output, deductions} = self;
        f
            .debug_struct("Proof")
            .field("inputs", &inputs)
            .field("output", &output)
            .field("deductions", &deductions)
            .finish()
    }
}
impl <'a, D: DeductionRule> PartialEq for Proof<'a, D> where D::Formula: PartialEq, D::Parameter: PartialEq{
    fn eq(&self, other: &Self) -> bool {
        &self.inputs == &other.inputs && &self.output == &other.output && &self.deductions == &other.deductions
    }
}

impl <'a, D: DeductionRule> Eq for Proof<'a, D> where D::Formula: Eq, D::Parameter: Eq {}

impl <'a, D: DeductionRule> Proof<'a, D> {
    fn check<'b: 'a>(pf: &'b UncheckedProof<D>) -> Option<Self> where D::Formula: Eq, D::Parameter: Eq{
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
            inputs: (&self.inputs).into_iter().map(|&e| e.clone()).collect(), // TODO
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
        type Parameter = Box<str>;

        fn deduce(params: &Box<str>, inputs: &Vec<&usize>) -> Option<usize> {
            if &**params != "d" || inputs.len() != 1 {return None;}
            if *inputs[0] > 0 {
                Some(*inputs[0] - 1)
            }
            else {
                None
            }
        }
    }
    #[test]
    fn decrement_rules(){
        assert_eq!(Decrement::deduce(&"d".to_string().into_boxed_str(), &vec![&30usize]), Some(29));
        assert_eq!(Decrement::deduce(&"e".to_string().into_boxed_str(), &vec![&30usize]), None);
        assert_eq!(Decrement::deduce(&"d".to_string().into_boxed_str(), &vec![&0usize]), None);
        assert_eq!(Decrement::deduce(&"d".to_string().into_boxed_str(), &vec![&30usize, &2usize]), None);
    }

    #[test]
    fn decrement_deduction(){
        let d_str = "d".to_string().into_boxed_str();
        assert!(Decrement::make_deduction(&d_str, &vec![&0usize]).is_none());
        let d_1 = Decrement::make_deduction(&d_str, &vec![&30usize]).unwrap();
        let d_2 = Decrement::make_deduction(&d_str, &vec![&20usize]).unwrap();
        assert_eq!(d_1, d_1);
        assert_ne!(d_1, d_2);
        assert_eq!(d_1.get_output(), &29usize);
        assert_eq!(d_1.get_params(), &d_str);
        assert_eq!(d_1.get_inputs(), &vec![&30usize]);
    }

    #[test]
    fn decrement_proofs(){
        let pf: UncheckedProof<Decrement> = UncheckedProof::new(
            19usize,
            vec![20usize],
            vec![(
                ("d".to_string().into_boxed_str(), vec![20usize]),
                19usize
            )]
        );
        let checked = Proof::check(&pf).unwrap();
        assert_eq!(&pf, &checked.un_check());
    }
}