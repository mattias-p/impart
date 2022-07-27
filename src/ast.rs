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
pub enum Comparator {
    LessThan,
    GreaterThan,
}

impl Comparator {
    fn try_parse<'a>(lexer: &mut Lexer<'a>) -> Result<Result<Loc<Self>, Loc<Token<'a>>>, String> {
        let token = lexer.next().unwrap()?;
        match token.inner {
            Token::LessThan => Ok(Ok(token.map(|_| Comparator::LessThan))),
            Token::GreaterThan => Ok(Ok(token.map(|_| Comparator::GreaterThan))),
            _ => Ok(Err(token)),
        }
    }

    fn parse<'a>(lexer: &mut Lexer<'a>) -> Result<Loc<Self>, String> {
        Self::try_parse(lexer)?
            .map_err(|token| token.error(format!("expected comparator got {:?}", token.inner)))
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct If<'a> {
    pub left: Loc<Value<'a>>,
    pub comparator: Loc<Comparator>,
    pub right: Loc<Value<'a>>,
    pub yes: Box<Loc<Expr<'a>>>,
    pub no: Box<Loc<Expr<'a>>>,
}

impl<'a> If<'a> {
    fn parse_body(lexer: &mut Lexer<'a>) -> Result<Self, String> {
        let left = Value::parse(lexer)?;
        let comparator = Comparator::parse(lexer)?;
        let right = Value::parse(lexer)?;
        let yes = Box::new(Expr::parse(lexer)?);
        let no = Box::new(If::parse_else(lexer)?);

        Ok(If {
            left,
            comparator,
            right,
            yes,
            no,
        })
    }

    fn parse_else(lexer: &mut Lexer<'a>) -> Result<Loc<Expr<'a>>, String> {
        let token = lexer.next().unwrap()?;
        match &token.inner {
            Token::Else => Expr::parse(lexer),
            Token::If => {
                let body = If::parse_body(lexer)?;
                Ok(token.map(|_| Expr::If(body)))
            }
            inner => Err(token.error(&format!("expected 'if' or 'else' got {inner:?}")))?,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Expr<'a> {
    Value(Value<'a>),
    If(If<'a>),
}

impl<'a> Expr<'a> {
    fn try_parse(lexer: &mut Lexer<'a>) -> Result<Result<Loc<Self>, Loc<Token<'a>>>, String> {
        match Value::try_parse(lexer)? {
            Ok(value) => Ok(Ok(value.map(Expr::Value))),
            Err(token) => match token.inner {
                Token::If => {
                    let body = If::parse_body(lexer)?;
                    Ok(Ok(token.map(|_| Expr::If(body))))
                }
                _ => Ok(Err(token)),
            },
        }
    }

    fn parse(lexer: &mut Lexer<'a>) -> Result<Loc<Self>, String> {
        Self::try_parse(lexer)?
            .map_err(|token| token.error(format!("expected 'if' or value got {:?}", token.inner)))
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
                        "expected 'let', 'if', literal or EOF got {:?}",
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
                input: b"if elevation > 0.5 foo else bar",
                expected: Ok(vec![Top::Expr(Expr::If(If {
                    left: Value::Ident("elevation").loc(1, 4),
                    comparator: Comparator::GreaterThan.loc(1, 14),
                    right: Value::Literal(Literal::Float("0.5")).loc(1, 16),
                    yes: Box::new(Expr::Value(Value::Ident("foo")).loc(1, 20)),
                    no: Box::new(Expr::Value(Value::Ident("bar")).loc(1, 29)),
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
