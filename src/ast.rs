use crate::lexer::Lexer;
use crate::lexer::Loc;
use crate::lexer::Token;

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Value<'a> {
    True,
    False,
    Float(&'a str),
    Hexcode(&'a str),
    Ident(&'a str),
}

impl<'a> Value<'a> {
    pub fn try_parse(lexer: &mut Lexer<'a>) -> Result<Result<Loc<Self>, Loc<Token<'a>>>, String> {
        let token = lexer.next().unwrap()?;
        match token.inner {
            Token::Decimal(s) => Ok(Ok(token.map(|_| Value::Float(s)))),
            Token::Hexcode(s) => Ok(Ok(token.map(|_| Value::Hexcode(s)))),
            Token::Ident(s) => Ok(Ok(token.map(|_| Value::Ident(s)))),
            _ => Ok(Err(token)),
        }
    }

    pub fn parse(lexer: &mut Lexer<'a>) -> Result<Loc<Self>, String> {
        Self::try_parse(lexer)?
            .map_err(|token| token.error(format!("expected value got {:?}", token.inner)))
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct LetIn<'a> {
    pub term: Loc<&'a str>,
    pub definition: Loc<Value<'a>>,
    pub expr: Loc<Expr<'a>>,
}

impl<'a> LetIn<'a> {
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

        Ok(LetIn {
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
pub struct Cond<'a> {
    pub left: Loc<Value<'a>>,
    pub comparator: Loc<Comparator>,
    pub right: Loc<Value<'a>>,
}

impl<'a> Cond<'a> {
    pub fn parse(lexer: &mut Lexer<'a>) -> Result<Self, String> {
        let left = Value::parse(lexer)?;

        let token = lexer.next().unwrap()?;
        let comparator = match &token.inner {
            Token::GreaterThan => token.map(|_| Comparator::GreaterThan),
            Token::LessThan => token.map(|_| Comparator::LessThan),
            inner => Err(token.error(&format!("expected 'then' got {inner:?}")))?,
        };

        let right = Value::parse(lexer)?;

        Ok(Cond {
            left,
            comparator,
            right,
        })
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct IfElse<'a> {
    pub cond: Cond<'a>,
    pub if_true: Loc<Expr<'a>>,
    pub if_false: Loc<Expr<'a>>,
}

impl<'a> IfElse<'a> {
    pub fn parse_body(lexer: &mut Lexer<'a>) -> Result<Self, String> {
        let cond = Cond::parse(lexer)?;

        let token = lexer.next().unwrap()?;
        match &token.inner {
            Token::Then => {}
            inner => Err(token.error(&format!("expected 'then' got {inner:?}")))?,
        };

        let if_true = Expr::parse(lexer)?;

        let token = lexer.next().unwrap()?;
        let if_false = match &token.inner {
            Token::Else => Expr::parse(lexer)?,
            inner => Err(token.error(&format!("expected 'else' got {inner:?}")))?,
        };

        Ok(IfElse {
            cond,
            if_true,
            if_false,
        })
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Expr<'a> {
    Value(Value<'a>),
    IfElse(Box<IfElse<'a>>),
    LetIn(Box<LetIn<'a>>),
}

impl<'a> Expr<'a> {
    pub fn try_parse(lexer: &mut Lexer<'a>) -> Result<Result<Loc<Self>, Loc<Token<'a>>>, String> {
        match Value::try_parse(lexer)? {
            Ok(value) => Ok(Ok(value.map(Expr::Value))),
            Err(token) => match token.inner {
                Token::If => {
                    let body = IfElse::parse_body(lexer)?;
                    Ok(Ok(token.map(|_| Expr::IfElse(Box::new(body)))))
                }
                Token::Let => {
                    let body = LetIn::parse_body(lexer)?;
                    Ok(Ok(token.map(|_| Expr::LetIn(Box::new(body)))))
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
    fn float() {
        assert_eq!(
            Value::parse(&mut Lexer::new(
                //1234567
                b"3.14",
            )),
            Ok(Value::Float("3.14").loc(1, 1)),
        );
    }

    #[test]
    fn hexcode() {
        assert_eq!(
            parse(&mut Lexer::new(
                //1234567
                b"#123456",
            )),
            Ok(Expr::Value(Value::Hexcode("123456")).loc(1, 1)),
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
            Ok(Expr::LetIn(Box::new(LetIn {
                term: "pi".loc(1, 5),
                definition: Value::Float("3.14").loc(1, 10),
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
            Ok(Expr::LetIn(Box::new(LetIn {
                term: "pi".loc(1, 5),
                definition: Value::Float("3.14").loc(1, 10),
                expr: Expr::LetIn(Box::new(LetIn {
                    term: "tau".loc(1, 22),
                    definition: Value::Float("6.28").loc(1, 28),
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
            Ok(Expr::IfElse(Box::new(IfElse {
                cond: Cond {
                    left: Value::Ident("elevation").loc(1, 4),
                    comparator: Comparator::GreaterThan.loc(1, 14),
                    right: Value::Float("0.5").loc(1, 16),
                },
                if_true: Expr::Value(Value::Ident("brown")).loc(1, 25),
                if_false: Expr::Value(Value::Ident("cyan")).loc(1, 36),
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
            Ok(Expr::IfElse(Box::new(IfElse {
                cond: Cond {
                left: Value::Ident("elevation").loc(1, 4),
                comparator: Comparator::GreaterThan.loc(1, 14),
                right: Value::Float("0.5").loc(1, 16),
                },
                if_true: Expr::Value(Value::Ident("cyan")).loc(1, 25),
                if_false: Expr::IfElse(Box::new(IfElse {
                        cond: Cond {
                        left: Value::Ident("humidity").loc(1, 38),
                        comparator: Comparator::LessThan.loc(1, 47),
                        right: Value::Float("0.31").loc(1, 49),
                        },
                        if_true: Expr::Value(Value::Ident("sandybrown")).loc(1, 59),
                        if_false: Expr::Value(Value::Ident("rosybrown")).loc(1, 75),
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
            Ok(Expr::IfElse(Box::new(IfElse {
                cond: Cond {
                left: Value::Ident("elevation").loc(1, 4),
                comparator: Comparator::GreaterThan.loc(1, 14),
                right: Value::Float("0.5").loc(1, 16),
                },
                if_true: Expr::IfElse(Box::new(IfElse {
                        cond: Cond {
                        left: Value::Ident("humidity").loc(1, 28),
                        comparator: Comparator::LessThan.loc(1, 37),
                        right: Value::Float("0.31").loc(1, 39),
                        },
                        if_true: Expr::Value(Value::Ident("sandybrown")).loc(1, 49),
                        if_false: Expr::Value(Value::Ident("rosybrown")).loc(1, 65),
                    }))
                    .loc(1, 25),
                if_false: Expr::Value(Value::Ident("cyan")).loc(1, 80),
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
            Ok(Expr::LetIn(Box::new(LetIn {
                term: "peak".loc(1, 5),
                definition: Value::Hexcode("A38983").loc(1, 12),
                expr: Expr::LetIn(Box::new(LetIn {
                    term: "mountain".loc(2, 5),
                    definition: Value::Hexcode("805C54").loc(2, 16),
                    expr: Expr::Value(Value::Hexcode("123456")).loc(3, 1),
                }))
                .loc(2, 1),
            }))
            .loc(1, 1)),
        );
    }
}
