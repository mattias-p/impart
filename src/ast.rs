use crate::lexer::Lexer;
use crate::lexer::Loc;
use crate::lexer::Op;
use crate::lexer::Token;

fn expr_bp<'a>(lexer: &mut Lexer<'a>, min_bp: u8) -> Result<Loc<Expr<'a>>, String> {
    let token = lexer.next().unwrap()?;
    let mut lhs = match token.inner {
        Token::True => token.map(|_| Expr::Atom(Atom::True)),
        Token::False => token.map(|_| Expr::Atom(Atom::False)),
        Token::Decimal(s) => token.map(|_| Expr::Atom(Atom::Float(s))),
        Token::Hexcode(s) => token.map(|_| Expr::Atom(Atom::Hexcode(s))),
        Token::Ident(s) => token.map(|_| Expr::Atom(Atom::Ident(s))),
        Token::ParenLeft => {
            let lhs = expr_bp(lexer, 0);

            let delim = lexer.next().unwrap()?;
            match delim.inner {
                Token::ParenRight => {}
                inner => Err(delim.error(format!("expected ')' got {inner:?}")))?,
            }

            lhs?
        }
        Token::Op(op) => {
            let ((), r_bp) = prefix_binding_power(op);
            let rhs = expr_bp(lexer, r_bp)?;
            token.map(|_| Expr::UnOp(Box::new(UnOp { op, rhs })))
        }
        inner => Err(token.error(format!("expected atom, operator or '(' got {inner:?}")))?,
    };

    loop {
        let token = lexer.peek().unwrap()?;
        let op = match token.inner {
            Token::Op(op) => op,
            _ => break,
        };

        if let Some((l_bp, r_bp)) = infix_binding_power(op) {
            if l_bp < min_bp {
                break;
            }
            lexer.next();

            let rhs = expr_bp(lexer, r_bp)?;
            lhs = token.map(|_| Expr::BinOp(Box::new(BinOp { op, lhs, rhs })));
            continue;
        }

        break;
    }

    Ok(lhs)
}

fn prefix_binding_power(op: Op) -> ((), u8) {
    match op {
        Op::Not => ((), 7),
        Op::Minus => ((), 15),
        _ => panic!("bad op: {:?}", op),
    }
}

fn infix_binding_power(op: Op) -> Option<(u8, u8)> {
    let res = match op {
        Op::Or => (2, 1),
        Op::Xor => (4, 3),
        Op::And => (6, 5),
        Op::Less | Op::Greater => (8, 9),
        Op::Plus | Op::Minus => (12, 11),
        Op::Asterisk | Op::Slash => (14, 13),
        _ => return None,
    };
    Some(res)
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Atom<'a> {
    True,
    False,
    Float(&'a str),
    Hexcode(&'a str),
    Ident(&'a str),
}

impl<'a> Atom<'a> {
    pub fn try_parse(lexer: &mut Lexer<'a>) -> Result<Result<Loc<Self>, Loc<Token<'a>>>, String> {
        let token = lexer.next().unwrap()?;
        match token.inner {
            Token::True => Ok(Ok(token.map(|_| Atom::True))),
            Token::False => Ok(Ok(token.map(|_| Atom::False))),
            Token::Decimal(s) => Ok(Ok(token.map(|_| Atom::Float(s)))),
            Token::Hexcode(s) => Ok(Ok(token.map(|_| Atom::Hexcode(s)))),
            Token::Ident(s) => Ok(Ok(token.map(|_| Atom::Ident(s)))),
            _ => Ok(Err(token)),
        }
    }

    pub fn parse(lexer: &mut Lexer<'a>) -> Result<Loc<Self>, String> {
        Self::try_parse(lexer)?
            .map_err(|token| token.error(format!("expected atom got {:?}", token.inner)))
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct LetIn<'a> {
    pub term: Loc<&'a str>,
    pub definition: Loc<Atom<'a>>,
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

        let definition = Atom::parse(lexer)?;

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

#[derive(Clone, Debug, PartialEq)]
pub struct Cond<'a> {
    pub left: Loc<Atom<'a>>,
    pub comparator: Loc<Comparator>,
    pub right: Loc<Atom<'a>>,
}

impl<'a> Cond<'a> {
    pub fn parse(lexer: &mut Lexer<'a>) -> Result<Loc<Expr<'a>>, String> {
        let lhs = Atom::parse(lexer)?.map(Expr::Atom);

        let token = lexer.next().unwrap()?;
        let op = match &token.inner {
            Token::Op(op @ Op::Greater) | Token::Op(op @ Op::Less) => *op,
            inner => Err(token.error(&format!("expected comparator got {inner:?}")))?,
        };

        let rhs = Atom::parse(lexer)?.map(Expr::Atom);

        Ok(token.map(|_| Expr::BinOp(Box::new(BinOp { op, lhs, rhs }))))
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct IfElse<'a> {
    pub cond: Loc<Expr<'a>>,
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
pub struct UnOp<'a> {
    pub op: Op,
    pub rhs: Loc<Expr<'a>>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct BinOp<'a> {
    pub op: Op,
    pub lhs: Loc<Expr<'a>>,
    pub rhs: Loc<Expr<'a>>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Expr<'a> {
    Atom(Atom<'a>),
    UnOp(Box<UnOp<'a>>),
    BinOp(Box<BinOp<'a>>),
    //Cond(Cond<'a>),
    IfElse(Box<IfElse<'a>>),
    LetIn(Box<LetIn<'a>>),
}

impl<'a> Expr<'a> {
    pub fn try_parse(lexer: &mut Lexer<'a>) -> Result<Result<Loc<Self>, Loc<Token<'a>>>, String> {
        match Atom::try_parse(lexer)? {
            Ok(atom) => Ok(Ok(atom.map(Expr::Atom))),
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
            .map_err(|token| token.error(format!("expected 'if' or atom got {:?}", token.inner)))
    }
}

pub fn parse<'a>(lexer: &mut Lexer<'a>) -> Result<Loc<Expr<'a>>, String> {
    let expr = Expr::parse(lexer)?;
    let token = lexer.next().unwrap()?;
    if token.inner == Token::Eof {
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
            Atom::parse(&mut Lexer::new(
                //1234567
                b"3.14",
            )),
            Ok(Atom::Float("3.14").loc(1, 1)),
        );
    }

    #[test]
    fn hexcode() {
        assert_eq!(
            parse(&mut Lexer::new(
                //1234567
                b"#123456",
            )),
            Ok(Expr::Atom(Atom::Hexcode("123456")).loc(1, 1)),
        );
    }

    #[test]
    fn ident() {
        assert_eq!(
            parse(&mut Lexer::new(
                //123
                b"foo",
            )),
            Ok(Expr::Atom(Atom::Ident("foo")).loc(1, 1)),
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
                definition: Atom::Float("3.14").loc(1, 10),
                expr: Expr::Atom(Atom::Ident("foo")).loc(1, 18),
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
                definition: Atom::Float("3.14").loc(1, 10),
                expr: Expr::LetIn(Box::new(LetIn {
                    term: "tau".loc(1, 22),
                    definition: Atom::Float("6.28").loc(1, 28),
                    expr: Expr::Atom(Atom::Ident("foo")).loc(1, 36),
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
                    left: Atom::Ident("elevation").loc(1, 4),
                    comparator: Comparator::GreaterThan.loc(1, 14),
                    right: Atom::Float("0.5").loc(1, 16),
                },
                if_true: Expr::Atom(Atom::Ident("brown")).loc(1, 25),
                if_false: Expr::Atom(Atom::Ident("cyan")).loc(1, 36),
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
                left: Atom::Ident("elevation").loc(1, 4),
                comparator: Comparator::GreaterThan.loc(1, 14),
                right: Atom::Float("0.5").loc(1, 16),
                },
                if_true: Expr::Atom(Atom::Ident("cyan")).loc(1, 25),
                if_false: Expr::IfElse(Box::new(IfElse {
                        cond: Cond {
                        left: Atom::Ident("humidity").loc(1, 38),
                        comparator: Comparator::LessThan.loc(1, 47),
                        right: Atom::Float("0.31").loc(1, 49),
                        },
                        if_true: Expr::Atom(Atom::Ident("sandybrown")).loc(1, 59),
                        if_false: Expr::Atom(Atom::Ident("rosybrown")).loc(1, 75),
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
                left: Atom::Ident("elevation").loc(1, 4),
                comparator: Comparator::GreaterThan.loc(1, 14),
                right: Atom::Float("0.5").loc(1, 16),
                },
                if_true: Expr::IfElse(Box::new(IfElse {
                        cond: Cond {
                        left: Atom::Ident("humidity").loc(1, 28),
                        comparator: Comparator::LessThan.loc(1, 37),
                        right: Atom::Float("0.31").loc(1, 39),
                        },
                        if_true: Expr::Atom(Atom::Ident("sandybrown")).loc(1, 49),
                        if_false: Expr::Atom(Atom::Ident("rosybrown")).loc(1, 65),
                    }))
                    .loc(1, 25),
                if_false: Expr::Atom(Atom::Ident("cyan")).loc(1, 80),
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
                definition: Atom::Hexcode("A38983").loc(1, 12),
                expr: Expr::LetIn(Box::new(LetIn {
                    term: "mountain".loc(2, 5),
                    definition: Atom::Hexcode("805C54").loc(2, 16),
                    expr: Expr::Atom(Atom::Hexcode("123456")).loc(3, 1),
                }))
                .loc(2, 1),
            }))
            .loc(1, 1)),
        );
    }
}
