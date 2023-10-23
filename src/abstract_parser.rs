pub trait AbstractParser<S> : Sized{
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

pub trait StrictAbstractParser<S: Eq + Clone> : AbstractParser<S> + Clone{
    fn check_parse(input: S) -> bool{
        if let Some(parsed) = Self::parse(input.clone()) {
            input == parsed.un_parse()
        }
        else { true }
    }
}
