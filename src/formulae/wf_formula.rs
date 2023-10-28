use std::rc::Rc;
use derivative::Derivative;
use std::fmt::Debug;

pub type Arity = usize;
pub trait WFFNames {
    type Variable;
    type Function;
    type Predicate;
    type Connective;
    type Quantifier;
    type Type;

    fn get_variable_type(name: &Self::Variable) -> &Self::Type;
    fn get_function_type(name: &Self::Function) -> (&Self::Type, Vec<&Self::Type>);
    fn get_predicate_type(name: &Self::Predicate) -> Vec<&Self::Type>;
    fn get_connective_type(name: &Self::Connective) -> Arity;
    fn get_quantifier_type(name: &Self::Quantifier) -> &Self::Type;
}

pub trait WFTNames {
    type Variable;
    type Function;
    type Type;
    fn get_variable_type(name: &Self::Variable) -> &Self::Type;
    fn get_function_type(name: &Self::Function) -> (&Self::Type, Vec<&Self::Type>);
}

impl<N: WFFNames> WFTNames for N {
    type Variable = N::Variable;
    type Function = N::Function;
    type Type = N::Type;

    fn get_variable_type(name: &Self::Variable) -> &Self::Type {
        Self::get_variable_type(name)
    }

    fn get_function_type(name: &Self::Function) -> (&Self::Type, Vec<&Self::Type>) {
        Self::get_function_type(name)
    }
}
// macro_rules! lumped_trait {
//     ($new_wft_trait_name: ident, $new_wff_trait_name: ident, $trait_name: ident) => {
//         pub trait $new_wft_trait_name: WFTNames where
//             Self::Variable: $trait_name,
//             Self::Function: $trait_name,
//         {}
//         impl<N: WFTNames> $new_wft_trait_name for N where
//             Self::Variable: $trait_name,
//             Self::Function: $trait_name,
//         {}
//         pub trait $new_wff_trait_name: WFFNames where
//             Self::Variable: $trait_name,
//             Self::Function: $trait_name,
//             Self::Predicate: $trait_name,
//             Self::Connective: $trait_name,
//             Self::Quantifier: $trait_name,
//         {}
//         impl<N: WFFNames> $new_wff_trait_name for N where
//             Self::Variable: $trait_name,
//             Self::Function: $trait_name,
//             Self::Predicate: $trait_name,
//             Self::Connective: $trait_name,
//             Self::Quantifier: $trait_name,
//         {}
//     };
// }
//
// macro_rules! wft_bounds {
//     ($N: ty, $trait_name: ident) => {
//         $N::Variable: $trait_name,
//         $N::Function: $trait_name
//     };
// }
//
// macro_rules! wft_bounds_derivative {
//     ($N: ty, $trait_name: ident) => {
//         #[derivative($trait_name(bound = stringify!(wft_bounds!($N, $trait_name))))]
//     };
// }
//
// macro_rules! wff_bounds {
//     ($N: ty, $trait_name: ident) => {
//         $N::Variable: $trait_name,
//         $N::Function: $trait_name,
//         $N::Predicate: $trait_name,
//         $N::Connective: $trait_name,
//         $N::Quantifier: $trait_name
//     };
// }
//
// lumped_trait!(WFTClone, WFFClone, Clone);
// lumped_trait!(WFTDebug, WFFDebug, Debug);
// lumped_trait!(WFTPartialEq, WFFPartialEq, PartialEq);
// lumped_trait!(WFTEq, WFFEq, Eq);
//
// #[derive(Derivative)]
// wft_bounds_derivative !{N, Debug}
// #[derivative(Debug(bound = wft_bounds_string!(N, Debug)))]
// #[derivative(Clone(bound = "wft_bounds!(N, Clone)"))]
// macro_rules! pile_of_derives {
//     () => {
//         #[derive(Derivative)]
//         #[derivative(Debug(bound =
//             "N::Variable: Debug, \
//             N::Function: Debug,"))]
//         #[derivative(Clone(bound =
//             "N::Variable: Clone, \
//             N::Function: Clone,"))]
//         #[derivative(PartialEq(bound =
//             "N::Variable: PartialEq, \
//             N::Function: PartialEq,"))]
//         #[derivative(Eq(bound =
//             "N::Variable: Eq, \
//             N::Function: Eq,"))]
//     };
// }

#[derive(Derivative)]
#[derivative(Debug(bound =
    "N::Variable: Debug, \
    N::Function: Debug,"))]
#[derivative(Clone(bound =
    "N::Variable: Clone, \
    N::Function: Clone,"))]
#[derivative(PartialEq(bound =
    "N::Variable: PartialEq, \
    N::Function: PartialEq,"))]
#[derivative(Eq(bound =
    "N::Variable: Eq, \
    N::Function: Eq,"))]
// pile_of_derives!{}
pub enum WFTStep < N: WFTNames > {
Variable(N::Variable),
Function(N::Function, Vec < WFTerm < N > >),
}
impl<N: WFTNames> WFTStep<N> {
    pub fn step(self) -> Option<WFTerm<N>> where N::Type: Clone + Eq, WFTStep<N>: Clone {
        match &self {
            WFTStep::Variable(_) => {}
            WFTStep::Function(name, inputs) => {
                if !Self::check_input_types(N::get_function_type(name).1, inputs) {
                    return None;
                }
            }
        };
        Some(WFTerm{step: Rc::new(self)})
    }

    fn check_input_types(expected: Vec<&N::Type>, inputs: &Vec<WFTerm<N>>) -> bool
        where WFTStep<N>: Clone, N::Type: Clone + Eq {
        inputs.iter().map(
            |t| -> N::Type { t.un_step_rc().get_type().clone() }
        )
            .eq(expected.into_iter().cloned())
    }
    pub fn get_type(&self) -> &N::Type {
        match &self {
            WFTStep::Variable(name) => {N::get_variable_type(name)}
            WFTStep::Function(name, _) => {N::get_function_type(name).0}
        }
    }
}
#[derive(Derivative)]
#[derivative(Debug(bound =
    "N::Variable: Debug, \
    N::Function: Debug,"))]
#[derivative(Clone(bound = ""))]
#[derivative(PartialEq(bound =
    "N::Variable: PartialEq, \
    N::Function: PartialEq,"))]
#[derivative(Eq(bound =
    "N::Variable: Eq, \
    N::Function: Eq,"))]
pub struct WFTerm<N: WFTNames> {
    step: Rc<WFTStep<N>>
}

impl<N: WFTNames> WFTerm<N> {
    pub fn un_step(self) -> WFTStep<N> where WFTStep<N>: Clone{
        (&*self.step).clone()
    }
    pub fn un_step_rc(&self) -> Rc<WFTStep<N>> {
        self.step.clone()
    }
}
#[derive(Derivative)]
#[derivative(Debug(bound =
    "N::Variable: Debug, \
    N::Function: Debug, \
    N::Predicate: Debug, \
    N::Connective: Debug, \
    N::Quantifier: Debug,"))]
#[derivative(Clone(bound =
    "N::Variable: Clone, \
    N::Function: Clone, \
    N::Predicate: Clone, \
    N::Connective: Clone, \
    N::Quantifier: Clone,"))]
#[derivative(PartialEq(bound =
    "N::Variable: PartialEq, \
    N::Function: PartialEq, \
    N::Predicate: PartialEq, \
    N::Connective: PartialEq, \
    N::Quantifier: PartialEq,"))]
#[derivative(Eq(bound =
    "N::Variable: Eq, \
    N::Function: Eq, \
    N::Predicate: Eq, \
    N::Connective: Eq, \
    N::Quantifier: Eq,"))]
enum WFFStep<N: WFFNames> {
    Predicate(N::Predicate, Vec<WFTerm<N>>),
    Connective(N::Connective, Vec<WFFormula<N>>),
    Quantifer(N::Quantifier, N::Variable, WFFormula<N>),
}
impl<N: WFFNames> WFFStep<N> {
    pub fn step(self) -> Option<WFFormula<N>> where WFTStep<N>: Clone, N::Type: Clone + Eq {
        match &self {
            WFFStep::Predicate(name, inputs) =>  {
                if !WFTStep::check_input_types(N::get_predicate_type(name), inputs) {
                    return None;
                }
            }
            WFFStep::Connective(name, inputs) => {
                if N::get_connective_type(name) != inputs.len() {
                    return None;
                }
            }
            WFFStep::Quantifer(name, var_name, _) => {
                if N::get_quantifier_type(name) != N::get_variable_type(var_name) {
                    return None;
                }
            }
        }
        Some(WFFormula {step: Rc::new(self)})
    }
}
#[derive(Derivative)]
#[derivative(Debug(bound =
"N::Variable: Debug, \
    N::Function: Debug, \
    N::Predicate: Debug, \
    N::Connective: Debug, \
    N::Quantifier: Debug,"))]
#[derivative(Clone(bound =
"N::Variable: Clone, \
    N::Function: Clone, \
    N::Predicate: Clone, \
    N::Connective: Clone, \
    N::Quantifier: Clone,"))]
#[derivative(PartialEq(bound =
"N::Variable: PartialEq, \
    N::Function: PartialEq, \
    N::Predicate: PartialEq, \
    N::Connective: PartialEq, \
    N::Quantifier: PartialEq,"))]
#[derivative(Eq(bound =
"N::Variable: Eq, \
    N::Function: Eq, \
    N::Predicate: Eq, \
    N::Connective: Eq, \
    N::Quantifier: Eq,"))]
struct WFFormula<N: WFFNames> {
    step: Rc<WFFStep<N>>
}

impl<N: WFFNames> WFFormula<N> {
    pub fn un_step(self) -> WFFStep<N> where WFFStep<N>: Clone {
        (&*self.step).clone()
    }

    pub fn un_step_rc(&self) -> Rc<WFFStep<N>> {
        self.step.clone()
    }
}
#[cfg(test)]
mod tests{
    use crate::formulae::wf_formula::{Arity, WFFNames, WFFormula, WFFStep, WFTerm, WFTStep};

    struct BoolTypes;

    impl WFFNames for BoolTypes {
        type Variable = (bool, String);
        type Function = (bool, Vec<bool>, String);
        type Predicate = (Vec<bool>, String);
        type Connective = (Arity, String);
        type Quantifier = (bool, String);
        type Type = bool;

        fn get_variable_type(name: &Self::Variable) -> &Self::Type { &name.0 }
        fn get_function_type(name: &Self::Function) -> (&Self::Type, Vec<&Self::Type>) { (&name.0, name.1.iter().collect()) }
        fn get_predicate_type(name: &Self::Predicate) -> Vec<&Self::Type> { name.0.iter().collect() }
        fn get_connective_type(name: &Self::Connective) -> Arity { name.0 }
        fn get_quantifier_type(name: &Self::Quantifier) -> &Self::Type { &name.0 }
    }
    #[test]
    fn check_make_variable() {
        let step = WFTStep::<BoolTypes>::Variable((true, "v".to_string()));
        assert_eq!(step.clone(), step.step().unwrap().un_step());
    }
    #[test]
    fn check_make_function() {
        let true_var = make_var(true);
        let false_var = make_var(false);
        let step = WFTStep::<BoolTypes>::Function(
            (true, vec![true, false], "f".to_string()),
            vec![true_var.clone(), false_var.clone()]);
        assert_eq!(step.clone(), step.clone().step().unwrap().un_step());
        let bad_typed_step = WFTStep::<BoolTypes>::Function(
            (true, vec![true, true], "f".to_string()),
            vec![true_var.clone(), false_var.clone()]);
        assert!(bad_typed_step.step().is_none());
        assert_eq!(step.get_type(), &true);
        let arg_mismatch = WFTStep::<BoolTypes>::Function(
            (true, vec![true, false, true], "f".to_string()),
            vec![true_var.clone(), false_var.clone()]);
        assert!(arg_mismatch.step().is_none());
    }

    #[test]
    fn check_make_predicate() {
        let true_var = make_var(true);
        let false_func = make_func(false, vec![make_var(true), make_func(false, vec![])]);
        let step = WFFStep::<BoolTypes>::Predicate(
            (vec![true, false], "p".to_string()),
            vec![true_var.clone(), false_func.clone()],
        );
        assert_eq!(step.clone(), step.clone().step().unwrap().un_step());
        let bad_step = WFFStep::<BoolTypes>::Predicate(
            (vec![true, false], "p".to_string()),
            vec![true_var.clone(), true_var.clone()],
        );
        assert!(bad_step.step().is_none());
        let arg_mismatch = WFFStep::<BoolTypes>::Predicate(
            (vec![true], "p".to_string()),
            vec![true_var.clone(), true_var.clone()],
        );
        assert!(arg_mismatch.step().is_none());
    }
    #[test]
    fn check_make_quantifier() {
        let pred = make_pred(vec![]);
        let step = WFFStep::<BoolTypes>::Quantifer((true, "q".to_string()), (true, "".to_string()), pred.clone());
        assert_eq!(step.clone(), step.step().unwrap().un_step());
        let bad_step = WFFStep::<BoolTypes>::Quantifer((false, "q".to_string()), (true, "".to_string()), pred);
        assert!(bad_step.step().is_none());
    }

    #[test]
    fn check_make_connective() {
        let pred_1 = make_pred(vec![make_var(true), make_func(false, vec![])]);
        let pred_2 = make_connective(vec![make_pred(vec![])]);
        let step = WFFStep::Connective((2, "c".to_string()), vec![pred_1.clone(), pred_2.clone()]);
        assert_eq!(step.clone(), step.clone().step().unwrap().un_step());
        let bad_step = WFFStep::Connective((1, "c".to_string()), vec![pred_1.clone(), pred_2.clone()]);
        assert!(bad_step.step().is_none());
    }
    fn make_connective(inputs: Vec<WFFormula<BoolTypes>>) -> WFFormula<BoolTypes> {
        WFFStep::<BoolTypes>::Connective(
            (inputs.len(), "c".to_string()),
            inputs,
        ).step().unwrap()
    }
    fn make_pred(inputs: Vec<WFTerm<BoolTypes>>) -> WFFormula<BoolTypes> {
        WFFStep::<BoolTypes>::Predicate(
            (
                inputs.iter().map(|e| e.un_step_rc().get_type().clone()).collect(),
                "p".to_string(),
            ),
            inputs,
        ).step().unwrap()
    }
    fn make_func(ty: bool, inputs: Vec<WFTerm<BoolTypes>>) -> WFTerm<BoolTypes> {
        WFTStep::<BoolTypes>::Function(
            (
                ty,
                inputs
                    .iter()
                    .map(|e| e.un_step_rc().get_type().clone())
                    .collect(),
                "f".to_string(),
            ),
            inputs,
        ).step().unwrap()
    }
    fn make_var(ty: bool) -> WFTerm<BoolTypes> {
        WFTStep::<BoolTypes>::Variable((ty, "v".to_string())).step().unwrap()
    }
}