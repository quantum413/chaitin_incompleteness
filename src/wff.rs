use pest_derive::Parser;

#[derive(Parser)]
#[grammar = "first_order_logic.pest"]
pub struct WFFParser;


#[cfg(test)]
mod tests {
    use std::error::Error;
    use std::iter::zip;
    use pest::iterators::{Pair, Pairs};
    use pest::Parser;
    use super::Rule;
    use super::WFFParser;

    fn parse_and_extract(rule: Rule, str: &str) -> Pair<Rule>{
        WFFParser::parse(rule, str).unwrap().next().unwrap()
    }
    fn check_full(str: &str, parse_rule: Rule, expected_rule: Rule, args: &[(Rule, &str)]){
        let mut iter = parse_and_check_top(str, parse_rule, expected_rule);
        for (expected, sub_str) in args {
            check_pair_eq(iter.next().unwrap(), parse_and_extract(*expected, sub_str));
        }
        assert_last(iter);
    }
    #[test]
    fn pure_formulae(){
        let str = "(@ vx0 (@ vx1 (= (f__plus vx0 vx1) (f__plus vx1 vx0))))";
        check_parse_eq(WFFParser::parse(Rule::just_formula, str),
                       WFFParser::parse(Rule::formula, str));
    }
    #[test]
    fn symbols_parsing() {
        let str_1 = "(= v0 (f_a v1))";
        check_full(str_1,
                   Rule::formula,
                   Rule::equals,
                   &[
                       (Rule::term, "v0"),
                       (Rule::term, "(f_a v1)")
                   ]);

        let str_2 = "(! (P0))";
        check_full(str_2,
                   Rule::formula,
                   Rule::not,
                   &[(Rule::formula, "(P0)")]);


        let str_3_1 = "(P0)";
        let str_3_2 = "(! (P1))";
        let str_3 = ["(> ", str_3_1, " ", str_3_2, ")"].concat();
        check_full(&str_3,
                   Rule::formula,
                   Rule::implies,
                   &[
                       (Rule::formula, str_3_1),
                       (Rule::formula, str_3_2),
                   ]);


        let str_4 = ["(& ", str_3_1, " ", str_3_2, ")"].concat();
        check_full(&str_4,
                   Rule::formula,
                   Rule::and,
                   &[
                       (Rule::formula, str_3_1),
                       (Rule::formula, str_3_2),
                   ]);

        let str_5 = ["(| ", str_3_1, " ", str_3_2, ")"].concat();
        check_full(&str_5,
                   Rule::formula,
                   Rule::or,
                   &[
                       (Rule::formula, str_3_1),
                       (Rule::formula, str_3_2),
                   ]);

        let var_str = "vx";
        let non_var_term = "(fa)";
        check_full(&["(@ ", var_str, " ", str_3_2, ")"].concat(),
                   Rule::formula,
                   Rule::forall,
                   &[
                       (Rule::term, var_str),
                       (Rule::formula, str_3_2),
                   ]);
        assert!(WFFParser::parse(Rule::formula, &["(@ ", non_var_term, " ", str_3_2, ")"].concat()).is_err());

        check_full(&["(# ", var_str, " ", str_3_2, ")"].concat(),
                   Rule::formula,
                   Rule::exists,
                   &[
                       (Rule::term, var_str),
                       (Rule::formula, str_3_2),
                   ]);
        assert!(WFFParser::parse(Rule::formula, &["(# ", non_var_term, " ", str_3_2, ")"].concat()).is_err());
    }
    #[test]
    fn variable_parsing() {
        let parse_1 = WFFParser::parse(Rule::just_variable, "vxyz");
        assert!(parse_1.is_ok());
        let mut pairs = parse_1.unwrap();
        assert_eq!(pairs.as_str(), "vxyz");
        let pair_1 = pairs.next().unwrap();
        let _ = pairs.next().unwrap(); // EOI
        assert_last(pairs);

        let expected_name = "xyz";
        check_variable(pair_1, expected_name);

        assert!(WFFParser::parse(Rule::just_variable, "zzz").is_err());
        assert!(WFFParser::parse(Rule::just_variable, "v*").is_err());
    }

    fn check_variable(pair: Pair<Rule>, expected_name: &str){
        assert_eq!(pair.as_rule(), Rule::variable);
        assert_eq!(pair.as_str(), ["v", expected_name].concat());
        let mut sub_pairs = pair.into_inner();
        check_name(sub_pairs.next().unwrap(), expected_name);
        assert_last(sub_pairs);
    }

    fn assert_last(mut i: impl Iterator){
        assert!(i.next().is_none());
    }
    #[test]
    fn pred_parsing(){
        let str_1 = "(Pa)";
        let mut iter_1 = parse_and_check_top(str_1, Rule::predicate, Rule::predicate);
        check_name(iter_1.next().unwrap(), "a");
        assert_last(iter_1);

        let str_2 = "(P__ab v0 (f__A v1 v2))";
        let mut iter_2 = parse_and_check_top(str_2, Rule::predicate, Rule::predicate);
        check_name(iter_2.next().unwrap(), "ab");
        check_pair_eq(iter_2.next().unwrap(), WFFParser::parse(Rule::term, "v0").unwrap().next().unwrap());
        check_pair_eq(iter_2.next().unwrap(), WFFParser::parse(Rule::term, "(f__A v1 v2)").unwrap().next().unwrap());
        assert_last(iter_2);

        check_parse_eq(WFFParser::parse(Rule::formula, str_1), WFFParser::parse(Rule::predicate, str_1));
        check_parse_eq(WFFParser::parse(Rule::formula, str_2), WFFParser::parse(Rule::predicate, str_2));
    }

    fn parse_and_check_top(str: &str, parse_rule: Rule, expected: Rule) -> Pairs<Rule> {
        check_top(str, WFFParser::parse(parse_rule, str).unwrap(), expected)
    }

    fn check_top<'a>(str_1: &'a str, mut parse_1: Pairs<'a, Rule>, expected: Rule) -> Pairs<'a, Rule> {
        let pair_1 = parse_1.next().unwrap();
        assert_last(parse_1);
        assert_eq!(pair_1.as_str(), str_1);
        assert_eq!(pair_1.as_rule(), expected);
        pair_1.into_inner()
    }

    #[test]
    fn term_parsing() {
        assert!(WFFParser::parse(Rule::function, "(fa vx)").is_err());
        let str_1 = "(fab)";
        let var_str = "vxy";
        let str_2 = "(f_ab vxy)";
        let mut parse_2_n = parse_and_check_top(str_2, Rule::function, Rule::function);
        check_name(parse_2_n.next().unwrap(), "ab");
        let pair_2_2 = parse_2_n.next().unwrap();
        check_variable(pair_2_2, "xy");
        assert_last(parse_2_n);

        let str_3 = "(f__abc vxy vzw)";
        let mut sub_parse_3 = parse_and_check_top(str_3, Rule::function, Rule::function);
        check_name(sub_parse_3.next().unwrap(), "abc");
        check_variable(sub_parse_3.next().unwrap(), "xy");
        check_variable(sub_parse_3.next().unwrap(), "zw");
        assert_last(sub_parse_3);

        assert!(WFFParser::parse(Rule::function, "(f__abc vxy)").is_err());
        assert!(WFFParser::parse(Rule::function, "(f_abc vxy vzw)").is_err());

        check_parse_eq(WFFParser::parse(Rule::variable, var_str), WFFParser::parse(Rule::term, var_str));
        check_parse_eq(WFFParser::parse(Rule::function, str_1), WFFParser::parse(Rule::term, str_1));
        check_parse_eq(WFFParser::parse(Rule::function, str_2), WFFParser::parse(Rule::term, str_2));
        check_parse_eq(WFFParser::parse(Rule::function, str_3), WFFParser::parse(Rule::term, str_3));

        let str_4 = "(f___abcd v0 (f_a v1) (f__ab v2 (f)))";
        let mut iter_4 = parse_and_check_top(str_4, Rule::term, Rule::function);
        check_name(iter_4.next().unwrap(), "abcd");
        check_variable(iter_4.next().unwrap(), "0");
        check_pair_eq(iter_4.next().unwrap(), WFFParser::parse(Rule::term, "(f_a v1)").unwrap().next().unwrap());
        check_pair_eq(iter_4.next().unwrap(), WFFParser::parse(Rule::term, "(f__ab v2 (f))").unwrap().next().unwrap());
        assert_last(iter_4);
    }
    fn check_parse_eq<E: Error>(lhs: Result<Pairs<Rule>, E>, rhs: Result<Pairs<Rule>, E>){
        assert_eq!(lhs.is_err(), rhs.is_err());
        if lhs.is_err() {return;}
        let unwrapped_lhs = lhs.unwrap();
        let unwrapped_rhs = rhs.unwrap();
        assert_eq!(unwrapped_lhs.len(), unwrapped_rhs.len());
        assert_eq!(unwrapped_lhs.as_str(), unwrapped_rhs.as_str());
        for (l, r) in zip(unwrapped_lhs, unwrapped_rhs){
            check_pair_eq(l, r);
        }
    }
    fn check_pair_eq(lhs: Pair<Rule>, rhs: Pair<Rule>){
        assert_eq!(lhs.as_str(), rhs.as_str());
        assert_eq!(lhs.as_rule(), rhs.as_rule());
        let (iter_l, iter_r) = (lhs.into_inner(), rhs.into_inner());
        assert_eq!(iter_l.len(), iter_r.len());
        for (l,r) in zip(iter_l, iter_r){
            check_pair_eq(l, r);
        }
    }
    #[test]
    fn zero_ary_functions() {
        let parse_0 = WFFParser::parse(Rule::function, "fa");
        assert!(parse_0.is_err());
        let parse_1_wrapped = WFFParser::parse(Rule::function, "(fa)");
        assert!(parse_1_wrapped.is_ok());
        let mut parse_1 = parse_1_wrapped.unwrap();
        assert_eq!(parse_1.as_str(), "(fa)");
        let pair_1_1 = parse_1.next().unwrap();
        assert_eq!(pair_1_1.as_str(), "(fa)");
        assert_eq!(pair_1_1.as_rule(), Rule::function);
        assert!(parse_1.next().is_none());
        let mut parse_1_1 = pair_1_1.into_inner();
        let pair_1_2 = parse_1_1.next().unwrap();
        assert!(parse_1_1.next().is_none());
        check_name(pair_1_2, "a");
    }

    fn check_name(pair: Pair<Rule>, expected_name: &str) {
        assert_eq!(pair.as_str(), expected_name);
        assert_eq!(pair.as_rule(), Rule::name);
        assert!(pair.into_inner().next().is_none());
    }
}
