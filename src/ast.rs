use crate::lexer::Lexer;
use crate::lexer::Loc;
use crate::lexer::Token;

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Literal<'a> {
    Float(&'a str),
    Hexcode(&'a str),
}

impl<'a> Literal<'a> {
    fn try_parse(lexer: &mut Lexer<'a>) -> Result<Result<Loc<Self>, Loc<Token<'a>>>, String> {
        let token = lexer.next().unwrap()?;
        match token.inner {
            Token::Decimal(s) => Ok(Ok(token.map(|_| Literal::Float(s)))),
            Token::Hexcode(s) => Ok(Ok(token.map(|_| Literal::Hexcode(s)))),
            _ => Ok(Err(token)),
        }
    }

    fn parse(lexer: &mut Lexer<'a>) -> Result<Loc<Self>, String> {
        Self::try_parse(lexer)?
            .map_err(|token| token.error(format!("expected literal got {:?}", token.inner)))
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Value<'a> {
    Literal(Literal<'a>),
    Ident(&'a str),
}

impl<'a> Value<'a> {
    fn try_parse(lexer: &mut Lexer<'a>) -> Result<Result<Loc<Self>, Loc<Token<'a>>>, String> {
        match Literal::try_parse(lexer)? {
            Ok(literal) => Ok(Ok(literal.map(|inner| Value::Literal(inner)))),
            Err(token) => match token.inner {
                Token::Ident(s) => Ok(Ok(token.map(|_| Value::Ident(s)))),
                _ => Ok(Err(token)),
            },
        }
    }

    fn parse(lexer: &mut Lexer<'a>) -> Result<Loc<Self>, String> {
        Self::try_parse(lexer)?
            .map_err(|token| token.error(format!("expected value got {:?}", token.inner)))
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Let<'a> {
    pub ident: Loc<&'a str>,
    pub literal: Loc<Literal<'a>>,
}

impl<'a> Let<'a> {
    fn parse_body(lexer: &mut Lexer<'a>) -> Result<Self, String> {
        let token = lexer.next().unwrap()?;
        let ident = match token.inner {
            Token::Ident(s) => token.map(|_| s),
            inner => Err(token.error(format!("expected identifier got {inner:?}")))?,
        };

        let token = lexer.next().unwrap()?;
        match &token.inner {
            Token::EqualSign => {}
            inner => Err(token.error(&format!("expected equal-sign got {inner:?}")))?,
        };

        let literal = Literal::parse(lexer)?;

        Ok(Let { ident, literal })
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Variable {
    Elevation,
    Temperature,
    Humidity,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Comparator {
    LessThan,
    GreaterThan,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Case<'a> {
    pub variable: Loc<Variable>,
    pub comparator: Loc<Comparator>,
    pub value: Loc<Value<'a>>,
    pub yes: Box<Loc<Expr<'a>>>,
    pub no: Box<Loc<Expr<'a>>>,
}

impl<'a> Case<'a> {
    fn parse_body(lexer: &mut Lexer<'a>) -> Result<Self, String> {
        let token = lexer.next().unwrap()?;
        let variable = match &token.inner {
            Token::Elevation => token.map(|_| Variable::Elevation),
            Token::Temperature => token.map(|_| Variable::Temperature),
            Token::Humidity => token.map(|_| Variable::Humidity),
            inner => Err(token.error(format!("expected variable got {inner:?}")))?,
        };

        let token = lexer.next().unwrap()?;
        let comparator = match &token.inner {
            Token::LessThan => token.map(|_| Comparator::LessThan),
            Token::GreaterThan => token.map(|_| Comparator::GreaterThan),
            inner => Err(token.error(&format!("expected comparator got {inner:?}")))?,
        };

        let value = Value::parse(lexer)?;

        let yes = Box::new(Expr::parse(lexer)?);

        let token = lexer.next().unwrap()?;
        let no = match &token.inner {
            Token::Else => Box::new(Expr::parse(lexer)?),
            Token::Case => {
                let case = Case::parse_body(lexer)?;
                Box::new(token.map(|_| Expr::Case(case)))
            }
            inner => Err(token.error(&format!("expected 'else' got {inner:?}")))?,
        };

        Ok(Case {
            variable,
            comparator,
            value,
            yes,
            no,
        })
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Expr<'a> {
    Value(Value<'a>),
    Case(Case<'a>),
}

impl<'a> Expr<'a> {
    fn try_parse(lexer: &mut Lexer<'a>) -> Result<Result<Loc<Self>, Loc<Token<'a>>>, String> {
        match Value::try_parse(lexer)? {
            Ok(value) => Ok(Ok(value.map(Expr::Value))),
            Err(token) => match token.inner {
                Token::Case => {
                    let case = Case::parse_body(lexer)?;
                    Ok(Ok(token.map(|_| Expr::Case(case))))
                }
                _ => Ok(Err(token)),
            },
        }
    }

    fn parse(lexer: &mut Lexer<'a>) -> Result<Loc<Self>, String> {
        Self::try_parse(lexer)?
            .map_err(|token| token.error(format!("expected 'case' or value got {:?}", token.inner)))
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Top<'a> {
    Let(Let<'a>),
    Expr(Expr<'a>),
}

impl<'a> Top<'a> {
    fn try_parse(lexer: &mut Lexer<'a>) -> Result<Result<Loc<Self>, Loc<Token<'a>>>, String> {
        match Expr::try_parse(lexer)? {
            Ok(value) => Ok(Ok(value.map(Top::Expr))),
            Err(token) => match token.inner {
                Token::Let => {
                    let l = Let::parse_body(lexer)?;
                    Ok(Ok(token.map(|_| Top::Let(l))))
                }
                _ => Ok(Err(token)),
            },
        }
    }
}

pub fn parse<'a>(lexer: &mut Lexer<'a>) -> Result<Vec<Loc<Top<'a>>>, String> {
    let mut tops = Vec::new();
    loop {
        match Top::try_parse(lexer)? {
            Ok(top) => tops.push(top),
            Err(token) => {
                if token.inner == Token::EOF {
                    return Ok(tops);
                } else {
                    Err(token.error(format!(
                        "expected 'let', 'case', literal or EOF got {:?}",
                        token.inner
                    )))?
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::lexer::LocExt;

    #[test]
    fn literal() {
        struct Test {
            input: &'static [u8],
            expected: Result<Loc<Literal<'static>>, String>,
        }
        let tests = vec![
            Test {
                input: b"",
                expected: Err("expected literal got EOF at 1:1".into()),
            },
            Test {
                input: b"3.14",
                expected: Ok(Literal::Float("3.14").loc(1, 1)),
            },
            Test {
                input: b"#fc9630",
                expected: Ok(Literal::Hexcode("fc9630").loc(1, 1)),
            },
        ];
        for test in tests {
            assert_eq!(Literal::parse(&mut Lexer::new(test.input)), test.expected);
        }
    }

    #[test]
    fn value() {
        struct Test {
            input: &'static [u8],
            expected: Result<Loc<Value<'static>>, String>,
        }
        let tests = vec![
            Test {
                input: b"",
                expected: Err("expected value got EOF at 1:1".into()),
            },
            Test {
                input: b"3.14",
                expected: Ok(Value::Literal(Literal::Float("3.14")).loc(1, 1)),
            },
            Test {
                input: b"#fc9630",
                expected: Ok(Value::Literal(Literal::Hexcode("fc9630")).loc(1, 1)),
            },
            Test {
                input: b"i-denti-fier",
                expected: Ok(Value::Ident("i-denti-fier").loc(1, 1)),
            },
        ];
        for test in tests {
            assert_eq!(Value::parse(&mut Lexer::new(test.input)), test.expected);
        }
    }

    #[test]
    fn let_() {
        struct Test {
            input: &'static [u8],
            expected: Result<Let<'static>, String>,
        }
        let tests = vec![
            Test {
                input: b"",
                expected: Err("expected identifier got EOF at 1:1".into()),
            },
            Test {
                input: b"pi = 3.14",
                expected: Ok(Let {
                    ident: "pi".loc(1, 1),
                    literal: Literal::Float("3.14").loc(1, 6),
                }),
            },
        ];
        for test in tests {
            assert_eq!(Let::parse_body(&mut Lexer::new(test.input)), test.expected);
        }
    }

    #[test]
    fn parser() {
        struct Test {
            input: &'static [u8],
            expected: Result<Vec<Loc<Top<'static>>>, String>,
        }
        let tests = vec![
            Test {
                input: b"",
                expected: Ok(vec![]),
            },
            Test {
                input: b"foo",
                expected: Ok(vec![Top::Expr(Expr::Value(Value::Ident("foo"))).loc(1, 1)]),
            },
            Test {
                input: b"case elevation > 0.5 foo else bar",
                expected: Ok(vec![Top::Expr(Expr::Case(Case {
                    variable: Variable::Elevation.loc(1, 6),
                    comparator: Comparator::GreaterThan.loc(1, 16),
                    value: Value::Literal(Literal::Float("0.5")).loc(1, 18),
                    yes: Box::new(Expr::Value(Value::Ident("foo")).loc(1, 22)),
                    no: Box::new(Expr::Value(Value::Ident("bar")).loc(1, 31)),
                }))
                .loc(1, 1)]),
            },
            Test {
                input: b"let pi = 3.14\nlet tau = 6.28",
                expected: Ok(vec![
                    Top::Let(Let {
                        ident: "pi".loc(1, 5),
                        literal: Literal::Float("3.14").loc(1, 10),
                    })
                    .loc(1, 1),
                    Top::Let(Let {
                        ident: "tau".loc(2, 5),
                        literal: Literal::Float("6.28").loc(2, 11),
                    })
                    .loc(2, 1),
                ]),
            },
        ];
        for test in tests {
            assert_eq!(parse(&mut Lexer::new(test.input)), test.expected);
        }
    }
}
