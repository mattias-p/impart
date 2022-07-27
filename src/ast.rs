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

        let token = lexer.next().unwrap()?;
        let no = match &token.inner {
            Token::Else => Box::new(Expr::parse(lexer)?),
            inner => Err(token.error(&format!("expected 'else' got {inner:?}")))?,
        };

        Ok(If {
            left,
            comparator,
            right,
            yes,
            no,
        })
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
        assert_eq!(
            Literal::parse(&mut Lexer::new(
                //1234567
                b"3.14",
            )),
            Ok(Literal::Float("3.14").loc(1, 1)),
        );
    }

    #[test]
    fn hexcode() {
        assert_eq!(
            parse(&mut Lexer::new(
                //1234567
                b"#123456",
            )),
            Ok(vec![Top::Expr(Expr::Value(Value::Literal(
                Literal::Hexcode("123456")
            )))
            .loc(1, 1)]),
        );
    }

    #[test]
    fn ident() {
        assert_eq!(
            parse(&mut Lexer::new(
                //123
                b"foo",
            )),
            Ok(vec![Top::Expr(Expr::Value(Value::Ident("foo"))).loc(1, 1)]),
        );
    }

    #[test]
    fn let_x() {
        assert_eq!(
            parse(&mut Lexer::new(
                //         1
                //1234567890123
                b"let pi = 3.14",
            )),
            Ok(vec![Top::Let(Let {
                ident: "pi".loc(1, 5),
                literal: Literal::Float("3.14").loc(1, 10),
            })
            .loc(1, 1),]),
        );
    }

    #[test]
    fn let_x_let_y() {
        assert_eq!(
            parse(&mut Lexer::new(
                //         1         2
                //1234567890123456789012345678
                b"let pi = 3.14 let tau = 6.28",
            )),
            Ok(vec![
                Top::Let(Let {
                    ident: "pi".loc(1, 5),
                    literal: Literal::Float("3.14").loc(1, 10),
                })
                .loc(1, 1),
                Top::Let(Let {
                    ident: "tau".loc(1, 19),
                    literal: Literal::Float("6.28").loc(1, 25),
                })
                .loc(1, 15),
            ]),
        );
    }

    #[test]
    fn if_a_x_else_y() {
        assert_eq!(
            parse(&mut Lexer::new(
                //         1         2         3         4         5         6         7
                //1234567890123456789012345678901234567890123456789012345678901234567890123
                b"if elevation > 0.5 brown else cyan",
            )),
            Ok(vec![Top::Expr(Expr::If(If {
                left: Value::Ident("elevation").loc(1, 4),
                comparator: Comparator::GreaterThan.loc(1, 14),
                right: Value::Literal(Literal::Float("0.5")).loc(1, 16),
                yes: Box::new(Expr::Value(Value::Ident("brown")).loc(1, 20)),
                no: Box::new(Expr::Value(Value::Ident("cyan")).loc(1, 31)),
            }))
            .loc(1, 1)]),
        );
    }

    #[test]
    fn if_a_x_else_if_b_y_else_z() {
        assert_eq!(
            parse(&mut Lexer::new(
                //         1         2         3         4         5         6         7
                //1234567890123456789012345678901234567890123456789012345678901234567890123
                b"if elevation > 0.5 cyan else if humidity < 0.31 sandybrown else rosybrown"
            )),
            Ok(vec![Top::Expr(Expr::If(If {
                left: Value::Ident("elevation").loc(1, 4),
                comparator: Comparator::GreaterThan.loc(1, 14),
                right: Value::Literal(Literal::Float("0.5")).loc(1, 16),
                yes: Box::new(Expr::Value(Value::Ident("cyan")).loc(1, 20)),
                no: Box::new(
                    Expr::If(If {
                        left: Value::Ident("humidity").loc(1, 33),
                        comparator: Comparator::LessThan.loc(1, 42),
                        right: Value::Literal(Literal::Float("0.31")).loc(1, 44),
                        yes: Box::new(Expr::Value(Value::Ident("sandybrown")).loc(1, 49)),
                        no: Box::new(Expr::Value(Value::Ident("rosybrown")).loc(1, 65)),
                    })
                    .loc(1, 30),
                ),
            }))
            .loc(1, 1)]),
        );
    }

    #[test]
    fn if_a_if_b_x_else_y_else_z() {
        assert_eq!(
            parse(&mut Lexer::new(
                //         1         2         3         4         5         6         7
                //123456789012345678901234567890123456789012345678901234567890123456789012345678
                b"if elevation > 0.5 if humidity < 0.31 sandybrown else rosybrown else cyan",
            )),
            Ok(vec![Top::Expr(Expr::If(If {
                left: Value::Ident("elevation").loc(1, 4),
                comparator: Comparator::GreaterThan.loc(1, 14),
                right: Value::Literal(Literal::Float("0.5")).loc(1, 16),
                yes: Box::new(
                    Expr::If(If {
                        left: Value::Ident("humidity").loc(1, 23),
                        comparator: Comparator::LessThan.loc(1, 32),
                        right: Value::Literal(Literal::Float("0.31")).loc(1, 34),
                        yes: Box::new(Expr::Value(Value::Ident("sandybrown")).loc(1, 39)),
                        no: Box::new(Expr::Value(Value::Ident("rosybrown")).loc(1, 55)),
                    })
                    .loc(1, 20),
                ),
                no: Box::new(Expr::Value(Value::Ident("cyan")).loc(1, 70)),
            }))
            .loc(1, 1)]),
        );
    }
}
