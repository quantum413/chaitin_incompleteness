mod wff;
mod formula;

// use pest::Parser;

// #[derive(Parser)]
// #[grammar = "parens.pest"]
// struct Ps;

fn main() {
    println!("Hello, world!");
    // let test_parse = Ps::parse(Rule::file, "(()(()))");
    // println!("{:?}", test_parse);
}

// struct PsParser{
//
// }
//
// impl PsParser {
//     fn parse(s: &str) -> Option<PsParser>{
//         None
//     }
// }
//
// struct FOLParser{
//
// }
// impl FOLParser{
//     fn parse_term(s: &str) -> Option<FOLParser>{
//         if s.as_bytes()[0] != b'v' {
//             return None
//         }
//         if !s.as_bytes()[1..].iter().all(|&x| x.is_ascii_alphanumeric()){
//             return None
//         }
//         Some(FOLParser {})
//     }
// }
