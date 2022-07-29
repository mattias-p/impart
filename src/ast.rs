use crate::lexer::Lexer;
use crate::lexer::Loc;
use crate::lexer::Op;
use crate::lexer::Token;

fn expr_bp<'a>(
    lexer: &mut Lexer<'a>,
    min_bp: u8,
) -> Result<Result<Loc<Expr<'a>>, Loc<Token<'a>>>, String> {
    let token = lexer.next().unwrap()?;
    let mut lhs = match token.inner {
        Token::True => token.map(|_| Expr::Atom(Atom::True)),
        Token::False => token.map(|_| Expr::Atom(Atom::False)),
        Token::Decimal(s) => token.map(|_| Expr::Atom(Atom::Float(s))),
        Token::Hexcode(s) => token.map(|_| Expr::Atom(Atom::Hexcode(s))),
        Token::Ident(s) => token.map(|_| Expr::Atom(Atom::Ident(s))),
        Token::ParenLeft => {
            let lhs = match expr_bp(lexer, 0)? {
                Ok(lhs) => lhs,
                Err(token) => {
                    Err(token.error(format!("unclosed parenthesis got {:?}", token.inner)))?
                }
            };

            let delim = lexer.next().unwrap()?;
            match delim.inner {
                Token::ParenRight => {}
                inner => Err(delim.error(format!("expected ')' got {inner:?}")))?,
            }

            lhs
        }
        Token::Op(op) => {
            let ((), r_bp) = prefix_binding_power(op);
            let rhs = match expr_bp(lexer, r_bp)? {
                Ok(rhs) => rhs,
                Err(token) => Err(token.error(format!(
                    "expected operand for unary operator got {:?}",
                    token.inner
                )))?,
            };
            token.map(|_| Expr::UnOp(Box::new(UnOp { op, rhs })))
        }
        _ => return Ok(Err(token)),
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

            let rhs = match expr_bp(lexer, r_bp)? {
                Ok(rhs) => rhs,
                Err(token) => Err(token.error(format!(
                    "expected right operand for binary operator got {:?}",
                    token.inner
                )))?,
            };
            lhs = token.map(|_| Expr::BinOp(Box::new(BinOp { op, lhs, rhs })));
            continue;
        }

        break;
    }

    Ok(Ok(lhs))
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
        Op::Asterisk | Op::Solidus => (14, 13),
        _ => return None,
    };
    Some(res)
}

#[derive(Clone, Debug, PartialEq)]
pub struct LetIn<'a> {
    pub term: Loc<&'a str>,
    pub definition: Loc<Expr<'a>>,
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
            Token::Equal => {}
            inner => Err(token.error(&format!("expected '=' got {inner:?}")))?,
        };

        let definition = Expr::parse(lexer)?;

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

#[derive(Clone, Debug, PartialEq)]
pub struct IfElse<'a> {
    pub cond: Loc<Expr<'a>>,
    pub if_true: Loc<Expr<'a>>,
    pub if_false: Loc<Expr<'a>>,
}

impl<'a> IfElse<'a> {
    pub fn parse_body(lexer: &mut Lexer<'a>) -> Result<Self, String> {
        let cond = Expr::parse(lexer)?;

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

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Atom<'a> {
    True,
    False,
    Float(&'a str),
    Hexcode(&'a str),
    Ident(&'a str),
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
    IfElse(Box<IfElse<'a>>),
    LetIn(Box<LetIn<'a>>),
}

impl<'a> Expr<'a> {
    pub fn try_parse(lexer: &mut Lexer<'a>) -> Result<Result<Loc<Self>, Loc<Token<'a>>>, String> {
        let token = lexer.peek().unwrap()?;
        match token.inner {
            Token::If => {
                lexer.next();
                let body = IfElse::parse_body(lexer)?;
                Ok(Ok(token.map(|_| Expr::IfElse(Box::new(body)))))
            }
            Token::Let => {
                lexer.next();
                let body = LetIn::parse_body(lexer)?;
                Ok(Ok(token.map(|_| Expr::LetIn(Box::new(body)))))
            }
            _ => Ok(expr_bp(lexer, 0)?),
        }
    }

    pub fn parse(lexer: &mut Lexer<'a>) -> Result<Loc<Self>, String> {
        match Self::try_parse(lexer)? {
            Ok(expr) => Ok(expr),
            Err(token) => Err(token.error(format!("expected 'if' or atom got {:?}", token.inner))),
        }
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
            Expr::parse(&mut Lexer::new(
                //1234567
                b"3.14",
            )),
            Ok(Expr::Atom(Atom::Float("3.14")).loc(1, 1)),
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
                definition: Expr::Atom(Atom::Float("3.14")).loc(1, 10),
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
                definition: Expr::Atom(Atom::Float("3.14")).loc(1, 10),
                expr: Expr::LetIn(Box::new(LetIn {
                    term: "tau".loc(1, 22),
                    definition: Expr::Atom(Atom::Float("6.28")).loc(1, 28),
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
                cond: Expr::BinOp(Box::new(BinOp {
                    op: Op::Greater,
                    lhs: Expr::Atom(Atom::Ident("elevation")).loc(1, 4),
                    rhs: Expr::Atom(Atom::Float("0.5")).loc(1, 16),
                }))
                .loc(1, 14),
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
                cond: Expr::BinOp(Box::new(BinOp {
                    op: Op::Greater,
                    lhs: Expr::Atom(Atom::Ident("elevation")).loc(1, 4),
                    rhs: Expr::Atom(Atom::Float("0.5")).loc(1, 16),
                })).loc(1, 14),
                if_true: Expr::Atom(Atom::Ident("cyan")).loc(1, 25),
                if_false: Expr::IfElse(Box::new(IfElse {
                    cond: Expr::BinOp(Box::new(BinOp {
                        op: Op::Less,
                        lhs: Expr::Atom(Atom::Ident("humidity")).loc(1, 38),
                        rhs: Expr::Atom(Atom::Float("0.31")).loc(1, 49),
                    })).loc(1,47),
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
                cond: Expr::BinOp(Box::new(BinOp {
                    op: Op::Greater,
                    lhs: Expr::Atom(Atom::Ident("elevation")).loc(1, 4),
                    rhs: Expr::Atom(Atom::Float("0.5")).loc(1, 16),
                })).loc(1, 14),
                if_true: Expr::IfElse(Box::new(IfElse {
                        cond: Expr::BinOp(Box::new(BinOp {
                            op: Op::Less,
                            lhs: Expr::Atom(Atom::Ident("humidity")).loc(1, 28),
                            rhs: Expr::Atom(Atom::Float("0.31")).loc(1, 39),
                        })).loc(1, 37),
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
                definition: Expr::Atom(Atom::Hexcode("A38983")).loc(1, 12),
                expr: Expr::LetIn(Box::new(LetIn {
                    term: "mountain".loc(2, 5),
                    definition: Expr::Atom(Atom::Hexcode("805C54")).loc(2, 16),
                    expr: Expr::Atom(Atom::Hexcode("123456")).loc(3, 1),
                }))
                .loc(2, 1),
            }))
            .loc(1, 1)),
        );
    }
}
