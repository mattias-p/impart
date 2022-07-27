use crate::lexer::Lexer;
use crate::lexer::Loc;
use crate::lexer::Token;

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Literal<'a> {
    Float(&'a str),
    Hexcode(&'a str),
}

impl<'a> Literal<'a> {
    pub fn try_parse(lexer: &mut Lexer<'a>) -> Result<Result<Loc<Self>, Loc<Token<'a>>>, String> {
        let token = lexer.next().unwrap()?;
        match token.inner {
            Token::Decimal(s) => Ok(Ok(token.map(|_| Literal::Float(s)))),
            Token::Hexcode(s) => Ok(Ok(token.map(|_| Literal::Hexcode(s)))),
            _ => Ok(Err(token)),
        }
    }

    pub fn parse(lexer: &mut Lexer<'a>) -> Result<Loc<Self>, String> {
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
    pub fn try_parse(lexer: &mut Lexer<'a>) -> Result<Result<Loc<Self>, Loc<Token<'a>>>, String> {
        match Literal::try_parse(lexer)? {
            Ok(literal) => Ok(Ok(literal.map(|inner| Value::Literal(inner)))),
            Err(token) => match token.inner {
                Token::Ident(s) => Ok(Ok(token.map(|_| Value::Ident(s)))),
                _ => Ok(Err(token)),
            },
        }
    }

    pub fn parse(lexer: &mut Lexer<'a>) -> Result<Loc<Self>, String> {
        Self::try_parse(lexer)?
            .map_err(|token| token.error(format!("expected value got {:?}", token.inner)))
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Let<'a> {
    pub term: Loc<&'a str>,
    pub definition: Loc<Value<'a>>,
    pub expr: Loc<Expr<'a>>,
}

impl<'a> Let<'a> {
    pub fn parse_body(lexer: &mut Lexer<'a>) -> Result<Self, String> {
        let token = lexer.next().unwrap()?;
        let term = match token.inner {
            Token::Ident(s) => token.map(|_| s),
            inner => Err(token.error(format!("expected identifier got {inner:?}")))?,
        };

        let token = lexer.next().unwrap()?;
        match &token.inner {
            Token::EqualSign => {}
            inner => Err(token.error(&format!("expected '=' got {inner:?}")))?,
        };

        let definition = Value::parse(lexer)?;

        let token = lexer.next().unwrap()?;
        match &token.inner {
            Token::In => {}
            inner => Err(token.error(&format!("expected 'in' got {inner:?}")))?,
        };

        let expr = Expr::parse(lexer)?;

        Ok(Let {
            term,
            definition,
            expr,
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Comparator {
    LessThan,
    GreaterThan,
}

impl Comparator {
    pub fn try_parse<'a>(
        lexer: &mut Lexer<'a>,
    ) -> Result<Result<Loc<Self>, Loc<Token<'a>>>, String> {
        let token = lexer.next().unwrap()?;
        match token.inner {
            Token::LessThan => Ok(Ok(token.map(|_| Comparator::LessThan))),
            Token::GreaterThan => Ok(Ok(token.map(|_| Comparator::GreaterThan))),
            _ => Ok(Err(token)),
        }
    }

    pub fn parse<'a>(lexer: &mut Lexer<'a>) -> Result<Loc<Self>, String> {
        Self::try_parse(lexer)?
            .map_err(|token| token.error(format!("expected comparator got {:?}", token.inner)))
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct If<'a> {
    pub left: Loc<Value<'a>>,
    pub comparator: Loc<Comparator>,
    pub right: Loc<Value<'a>>,
    pub branch_true: Loc<Expr<'a>>,
    pub branch_false: Loc<Expr<'a>>,
}

impl<'a> If<'a> {
    pub fn parse_body(lexer: &mut Lexer<'a>) -> Result<Self, String> {
        let left = Value::parse(lexer)?;
        let comparator = Comparator::parse(lexer)?;
        let right = Value::parse(lexer)?;

        let token = lexer.next().unwrap()?;
        match &token.inner {
            Token::Then => {}
            inner => Err(token.error(&format!("expected 'then' got {inner:?}")))?,
        };

        let branch_true = Expr::parse(lexer)?;

        let token = lexer.next().unwrap()?;
        let branch_false = match &token.inner {
            Token::Else => Expr::parse(lexer)?,
            inner => Err(token.error(&format!("expected 'else' got {inner:?}")))?,
        };

        Ok(If {
            left,
            comparator,
            right,
            branch_true,
            branch_false,
        })
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Expr<'a> {
    Value(Value<'a>),
    If(Box<If<'a>>),
    Let(Box<Let<'a>>),
}

impl<'a> Expr<'a> {
    pub fn try_parse(lexer: &mut Lexer<'a>) -> Result<Result<Loc<Self>, Loc<Token<'a>>>, String> {
        match Value::try_parse(lexer)? {
            Ok(value) => Ok(Ok(value.map(Expr::Value))),
            Err(token) => match token.inner {
                Token::If => {
                    let body = If::parse_body(lexer)?;
                    Ok(Ok(token.map(|_| Expr::If(Box::new(body)))))
                }
                Token::Let => {
                    let body = Let::parse_body(lexer)?;
                    Ok(Ok(token.map(|_| Expr::Let(Box::new(body)))))
                }
                _ => Ok(Err(token)),
            },
        }
    }

    pub fn parse(lexer: &mut Lexer<'a>) -> Result<Loc<Self>, String> {
        Self::try_parse(lexer)?
            .map_err(|token| token.error(format!("expected 'if' or value got {:?}", token.inner)))
    }
}

pub fn parse<'a>(lexer: &mut Lexer<'a>) -> Result<Loc<Expr<'a>>, String> {
    let expr = Expr::parse(lexer)?;
    let token = lexer.next().unwrap()?;
    if token.inner == Token::EOF {
        return Ok(expr);
    } else {
        Err(token.error(format!(
            "expected 'let', 'if', literal or EOF got {:?}",
            token.inner
        )))?
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
            Ok(Expr::Value(Value::Literal(Literal::Hexcode("123456"))).loc(1, 1)),
        );
    }

    #[test]
    fn ident() {
        assert_eq!(
            parse(&mut Lexer::new(
                //123
                b"foo",
            )),
            Ok(Expr::Value(Value::Ident("foo")).loc(1, 1)),
        );
    }

    #[test]
    fn let_x() {
        assert_eq!(
            parse(&mut Lexer::new(
                //         1         2
                //123456789012345678901234
                b"let pi = 3.14 in foo",
            )),
            Ok(Expr::Let(Box::new(Let {
                term: "pi".loc(1, 5),
                definition: Value::Literal(Literal::Float("3.14")).loc(1, 10),
                expr: Expr::Value(Value::Ident("foo")).loc(1, 18),
            }))
            .loc(1, 1)),
        );
    }

    #[test]
    fn let_x_let_y() {
        assert_eq!(
            parse(&mut Lexer::new(
                //         1         2         3
                //12345678901234567890123456789012345678
                b"let pi = 3.14 in let tau = 6.28 in foo",
            )),
            Ok(Expr::Let(Box::new(Let {
                term: "pi".loc(1, 5),
                definition: Value::Literal(Literal::Float("3.14")).loc(1, 10),
                expr: Expr::Let(Box::new(Let {
                    term: "tau".loc(1, 22),
                    definition: Value::Literal(Literal::Float("6.28")).loc(1, 28),
                    expr: Expr::Value(Value::Ident("foo")).loc(1, 36),
                }))
                .loc(1, 18),
            }))
            .loc(1, 1)),
        );
    }

    #[test]
    fn if_a_x_else_y() {
        assert_eq!(
            parse(&mut Lexer::new(
                //         1         2         3
                //123456789012345678901234567890123456789
                b"if elevation > 0.5 then brown else cyan",
            )),
            Ok(Expr::If(Box::new(If {
                left: Value::Ident("elevation").loc(1, 4),
                comparator: Comparator::GreaterThan.loc(1, 14),
                right: Value::Literal(Literal::Float("0.5")).loc(1, 16),
                branch_true: Expr::Value(Value::Ident("brown")).loc(1, 25),
                branch_false: Expr::Value(Value::Ident("cyan")).loc(1, 36),
            }))
            .loc(1, 1)),
        );
    }

    #[test]
    fn if_a_x_else_if_b_y_else_z() {
        assert_eq!(
            parse(&mut Lexer::new(
                //         1         2         3         4         5         6         7         8
                //12345678901234567890123456789012345678901234567890123456789012345678901234567890123
                b"if elevation > 0.5 then cyan else if humidity < 0.31 then sandybrown else rosybrown"
            )),
            Ok(Expr::If(Box::new(If {
                left: Value::Ident("elevation").loc(1, 4),
                comparator: Comparator::GreaterThan.loc(1, 14),
                right: Value::Literal(Literal::Float("0.5")).loc(1, 16),
                branch_true: Expr::Value(Value::Ident("cyan")).loc(1, 25),
                branch_false: Expr::If(Box::new(If {
                        left: Value::Ident("humidity").loc(1, 38),
                        comparator: Comparator::LessThan.loc(1, 47),
                        right: Value::Literal(Literal::Float("0.31")).loc(1, 49),
                        branch_true: Expr::Value(Value::Ident("sandybrown")).loc(1, 59),
                        branch_false: Expr::Value(Value::Ident("rosybrown")).loc(1, 75),
                    }))
                    .loc(1, 35),
            }))
            .loc(1, 1)),
        );
    }

    #[test]
    fn if_a_if_b_x_else_y_else_z() {
        assert_eq!(
            parse(&mut Lexer::new(
                //         1         2         3         4         5         6         7         8
                //12345678901234567890123456789012345678901234567890123456789012345678901234567890123
                b"if elevation > 0.5 then if humidity < 0.31 then sandybrown else rosybrown else cyan",
            )),
            Ok(Expr::If(Box::new(If {
                left: Value::Ident("elevation").loc(1, 4),
                comparator: Comparator::GreaterThan.loc(1, 14),
                right: Value::Literal(Literal::Float("0.5")).loc(1, 16),
                branch_true: Expr::If(Box::new(If {
                        left: Value::Ident("humidity").loc(1, 28),
                        comparator: Comparator::LessThan.loc(1, 37),
                        right: Value::Literal(Literal::Float("0.31")).loc(1, 39),
                        branch_true: Expr::Value(Value::Ident("sandybrown")).loc(1, 49),
                        branch_false: Expr::Value(Value::Ident("rosybrown")).loc(1, 65),
                    }))
                    .loc(1, 25),
                branch_false: Expr::Value(Value::Ident("cyan")).loc(1, 80),
            }))
            .loc(1, 1)),
        );
    }

    #[test]
    fn wip() {
        assert_eq!(
            parse(&mut Lexer::new(
                //         1         2         3           1         2         3
                //123456789012345678901234567890  1234567890123456789012345678901234  1234567
                b"let peak = #A38983 in // brown\nlet mountain = #805C54 in // brown\n#123456"
            )),
            Ok(Expr::Let(Box::new(Let {
                term: "peak".loc(1, 5),
                definition: Value::Literal(Literal::Hexcode("A38983")).loc(1, 12),
                expr: Expr::Let(Box::new(Let {
                    term: "mountain".loc(2, 5),
                    definition: Value::Literal(Literal::Hexcode("805C54")).loc(2, 16),
                    expr: Expr::Value(Value::Literal(Literal::Hexcode("123456"))).loc(3, 1),
                }))
                .loc(2, 1),
            }))
            .loc(1, 1)),
        );
    }
}
