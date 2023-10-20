use std::fmt::{Display, Formatter};
use crate::wff::WFFParser;
use crate::wff::Rule;
use pest::Parser;

#[derive(Debug)]
pub enum Term<'a>{
    Variable(&'a str),
    Function(&'a str, Vec<Term<'a>>),
}

impl<'a> Term<'a>{
    fn new_from_string(s: &'a str) -> Option<Self>{
        WFFParser::parse(Rule::term, s).ok().map(
            |mut e| {
                Self::new(e.next().unwrap())
            }
        )
    }
    fn new(pair: pest::iterators::Pair<'a, Rule>) -> Self {
        match pair.as_rule() {
            Rule::variable => Term::Variable(pair.into_inner().next().unwrap().as_str()),
            Rule::function => {
                let mut iter = pair.into_inner();
                Term::Function(
                    iter.next().unwrap().as_str(),
                    iter.map(
                        |e: pest::iterators::Pair<'a, Rule>| Self::new(e)).collect()
                )
            }
            _ => unreachable!(),
        }
    }
    fn replace_var(&self, name: &str, rep: &'a str) -> Self{
        match self {
            Term::Variable(n) => Term::Variable(if *n == name {rep} else {n}),
            Term::Function(s, v) =>
                Term::Function(s,
                         v.into_iter().map(|e| e.replace_var(name, rep)).collect()
                ),
        }
    }
    fn contains_var(&self, name: &str) -> bool{
        match self {
            Term::Variable(n) => n == &name,
            Term::Function(_, v) => v.into_iter().any(|e| e.contains_var(name)),
        }
    }
}

impl PartialEq for Term<'_> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Term::Variable(s), Term::Variable(o)) => s == o,
            (Term::Function(s, t), Term::Function(o, r)) => s == o && t == r,
            _ => false,
        }
    }
}

impl Display for Term<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Term::Variable(s) => write!(f, "v{}", s),
            Term::Function(s, terms) => {
                write!(f, "(f{}{}", (0..terms.len()).map(|_| "_").collect::<String>(), s)?;
                for term in terms{
                    write!(f, " {}", term)?;
                }
                write!(f, ")")
            },
        }
    }
}

impl Clone for Term<'_> {
    fn clone(&self) -> Self {
        match self {
            Term::Variable(n) => Term::Variable(*n),
            Term::Function(n, s) => Term::Function(*n, s.clone()),
        }
    }
}

#[derive(Debug)]
pub enum Formula<'a> {
    Predicate(&'a str, Vec<Term<'a>>),
    Equals(Term<'a>, Term<'a>),
    Implies(Box<Formula<'a>>, Box<Formula<'a>>),
    And(Box<Formula<'a>>, Box<Formula<'a>>),
    Or(Box<Formula<'a>>, Box<Formula<'a>>),
    Not(Box<Formula<'a>>),
    ForAll(&'a str, Box<Formula<'a>>),
    Exists(&'a str, Box<Formula<'a>>),
}

impl<'a> Formula<'a> {
    fn new_from_string(s: &'a str) -> Option<Self>{
        WFFParser::parse(Rule::just_formula, s).ok().map(
            |mut e| {
                Self::new(e.next().unwrap())
            }
        )
    }
    fn new(pair: pest::iterators::Pair<'a, Rule>) -> Self{
        let rule = pair.as_rule();
        let mut iter = pair.into_inner();
        match rule {
            Rule::predicate => Formula::Predicate(
                iter.next().unwrap().as_str(),
                iter.map(|t| Term::new(t)).collect()),
            Rule::equals => Formula::Equals(
                Term::new(iter.next().unwrap()),
                Term::new(iter.next().unwrap()),
            ),
            Rule::implies => Formula::Implies(
                Box::new(Formula::new(iter.next().unwrap())),
                Box::new(Formula::new(iter.next().unwrap())),
            ),
            Rule::and => Formula::And(
                Box::new(Formula::new(iter.next().unwrap())),
                Box::new(Formula::new(iter.next().unwrap())),
            ),
            Rule::or => Formula::Or(
                Box::new(Formula::new(iter.next().unwrap())),
                Box::new(Formula::new(iter.next().unwrap())),
            ),
            Rule::not => Formula::Not(
                Box::new(Formula::new(iter.next().unwrap())),
            ),
            Rule::forall =>
                Formula::ForAll(
                iter.next().unwrap().into_inner().next().unwrap().as_str(),
                Box::new(Formula::new(iter.next().unwrap())),
            ),
            Rule::exists =>
                Formula::Exists(
                    iter.next().unwrap().into_inner().next().unwrap().as_str(),
                    Box::new(Formula::new(iter.next().unwrap())),
                ),
            _ => unreachable!()
        }
    }
}

impl PartialEq for Formula<'_>{
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (
                Formula::Predicate(s, v),
                Formula::Predicate(o, w),
            ) => s == o && v == w,
            (
                Formula::Equals(a1, b1),
                Formula::Equals(a2, b2),
            ) => a1 == a2 && b1 == b2,
            (
                Formula::Implies(a1, b1),
                Formula::Implies(a2, b2),
            ) => a1 == a2 && b1 == b2,
            (
                Formula::And(a1, b1),
                Formula::And(a2, b2),
            ) => a1 == a2 && b1 == b2,
            (
                Formula::Or(a1, b1),
                Formula::Or(a2, b2),
            ) => a1 == a2 && b1 == b2,
            (
                Formula::Not(a1),
                Formula::Not(a2),
            ) => a1 == a2,
            (
                Formula::ForAll(n1, a1),
                Formula::ForAll(n2, a2),
            ) => n1 == n2 && a1 == a2,
            (
                Formula::Exists(n1, a1),
                Formula::Exists(n2, a2),
            ) => n1 == n2 && a1 == a2,
            _ => false,
        }
    }
}

impl Clone for Formula<'_> {
    fn clone(&self) -> Self {
        match self {
            Formula::Predicate(s, v) => Formula::Predicate(s.clone(), v.clone()),
            Formula::Equals(a, b) => Formula::Equals(a.clone(), b.clone()),
            Formula::Implies(a, b) => Formula::Implies(a.clone(), b.clone()),
            Formula::And(a, b) => Formula::And(a.clone(), b.clone()),
            Formula::Or(a, b) => Formula::Or(a.clone(), b.clone()),
            Formula::Not(a) => Formula::Not(a.clone()),
            Formula::ForAll(n, a) => Formula::ForAll(n.clone(), a.clone()),
            Formula::Exists(n, a) => Formula::Exists(n.clone(), a.clone()),
        }
    }
}

impl Display for Formula<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Formula::Predicate(s, terms) => {
                write!(f, "(P{}{}", (0..terms.len()).map(|_| "_").collect::<String>(), s)?;
                for term in terms{
                    write!(f, " {}", term)?;
                }
                write!(f, ")")
            },
            Formula::Equals(a, b) => {
                write!(f, "(= {} {})", a, b)
            },
            Formula::Implies(a, b) => {
                write!(f, "(> {} {})", *a, *b)
            },
            Formula::And(a, b) => {
                write!(f, "(& {} {})", *a, *b)
            },
            Formula::Or(a, b) => {
                write!(f, "(| {} {})", *a, *b)
            },
            Formula::Not(a) => {
                write!(f, "(! {})", *a)
            }
            Formula::ForAll(n, s) => {
                write!(f, "(@ v{} {})", *n, *s)
            },
            Formula::Exists(n, s) => {
                write!(f, "(# v{} {})", *n, *s)
            }
        }
    }
}

#[cfg(test)]
mod formula_test {
    use super::Term;
    use super::Formula;

    #[test]
    fn formula_conversion(){
        let str_1 = "(Paa)";
        let str_2 = "(P)";
        let fa_1 = Formula::new_from_string(str_1).unwrap();
        let fa_2 = Formula::new_from_string(str_2).unwrap();
        assert_eq!(fa_1, Formula::Predicate("aa", vec![]));
        assert_ne!(fa_1, fa_2);

        let str_3 = "(P___abc vx (f__ab vy vz) vw)";
        let fa_3 = Formula::new_from_string(str_3).unwrap();
        assert_eq!(fa_3, Formula::Predicate("abc", vec![
            Term::Variable("x"),
            Term::new_from_string("(f__ab vy vz)").unwrap(),
            Term::Variable("w")]));
        assert_ne!(fa_3, Formula::Predicate("abc", vec![]));

        assert!(Formula::new_from_string("(P)a").is_none());

        let fa_4 = Formula::Equals(
            Term::new_from_string("vx").unwrap(),
            Term::new_from_string("(f_a vy)").unwrap()
        );
        let str_4 = "(= vx (f_a vy))";
        assert_eq!(fa_4, Formula::new_from_string(str_4).unwrap());
        assert_eq!(fa_4.to_string(), str_4);

        let str_5_1 = "(P__ab vx vy)";
        let str_5_2 = "(= (f) vz)";
        let fa_5_1 = Formula::new_from_string(str_5_1).unwrap();
        let fa_5_2 = Formula::new_from_string(str_5_2).unwrap();

        let str_5_3 = &format!("(> {} {})", str_5_1, str_5_2);
        let fa_5_3 = Formula::Implies(
            Box::new(fa_5_1.clone()),
            Box::new(fa_5_2.clone())
        );
        assert_eq!(fa_5_3, Formula::new_from_string(str_5_3).unwrap());
        assert_eq!(fa_5_3.to_string(), *str_5_3);

        let str_5_3 = &format!("(& {} {})", str_5_1, str_5_2);
        let fa_5_3 = Formula::And(
            Box::new(fa_5_1.clone()),
            Box::new(fa_5_2.clone())
        );
        assert_eq!(fa_5_3, Formula::new_from_string(str_5_3).unwrap());
        assert_eq!(fa_5_3.to_string(), *str_5_3);

        let str_5_3 = &format!("(| {} {})", str_5_1, str_5_2);
        let fa_5_3 = Formula::Or(
            Box::new(fa_5_1.clone()),
            Box::new(fa_5_2.clone())
        );
        assert_eq!(fa_5_3, Formula::new_from_string(str_5_3).unwrap());
        assert_eq!(fa_5_3.to_string(), *str_5_3);

        let str_5_3 = &format!("(! {})", str_5_1);
        let fa_5_3 = Formula::Not(
            Box::new(fa_5_1.clone())
        );
        assert_eq!(fa_5_3, Formula::new_from_string(str_5_3).unwrap());
        assert_eq!(fa_5_3.to_string(), *str_5_3);

        let str_5_4 = "(@ vxy (P__ab vyy vzz))";
        let fa_5_4 = Formula::new_from_string("(P__ab vyy vzz)").unwrap();
        assert_eq!(
            Formula::ForAll("xy", Box::new(fa_5_4.clone())),
            Formula::new_from_string(str_5_4).unwrap(),
        );
        assert_eq!(
            Formula::ForAll("xy", Box::new(fa_5_4.clone())).to_string(),
            str_5_4
        );


        let str_5_4 = "(# vxy (P__ab vyy vzz))";
        let fa_5_4 = Formula::new_from_string("(P__ab vyy vzz)").unwrap();
        assert_eq!(
            Formula::Exists("xy", Box::new(fa_5_4.clone())),
            Formula::new_from_string(str_5_4).unwrap(),
        );
        assert_eq!(
            Formula::Exists("xy", Box::new(fa_5_4.clone())).to_string(),
            str_5_4
        );

        let str_5_5 = "(# v (@ vx (& (! (P)) (| (> (P__ v v) (P)) (= vx (f_a vy))))))";
        let fa_5_5 = Formula::new_from_string(str_5_5).unwrap();
        assert_eq!(fa_5_5.clone(), fa_5_5);
    }
}

#[cfg(test)]
mod term_tests {
    use super::Term;

    #[test]
    fn term_conversion() {
        let str_1 = "vxy";
        let str_1_name = "xy";
        assert_eq!(Term::new_from_string(str_1), Some(Term::Variable(str_1_name)));
        assert_eq!(str_1, Term::Variable(str_1_name).to_string());

        let str_2 = "(fa)";
        assert_eq!(str_2, Term::new_from_string(str_2).unwrap().to_string());
        let str_3 = "(f___abc vx vy (f__ab vx (f_c vz)))";
        assert_eq!(str_3, Term::new_from_string(str_3).unwrap().to_string());
        assert_eq!(Term::new_from_string(str_2), Term::new_from_string(str_2));
        assert_ne!(Term::new_from_string(str_2), Term::new_from_string(str_3));
        let str_4 = "(f___abc vx vy (f__ab vx (f_c vy)))";
        let term_4 = Term::new_from_string(str_4).unwrap();
        assert_ne!(term_4, Term::new_from_string(str_3).unwrap());
        let str_5 = "(f___abc vz vy (f__ab vz (f_c vy)))";
        let term_5 = Term::new_from_string(str_5).unwrap();
        assert_eq!(term_4.replace_var("x", "z").to_string(), str_5);
        assert_eq!(term_4.replace_var("x", "z"), term_5);

        assert!(term_4.contains_var("x"));
        assert!(!term_4.contains_var(""));
    }
}