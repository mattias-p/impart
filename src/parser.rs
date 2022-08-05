use crate::lexer::Lexer;
use crate::lexer::Loc;
use crate::lexer::Op;
use crate::lexer::Token;
use crate::lexer::Var;

fn expr_bp<'a>(
    lexer: &mut Lexer<'a>,
    min_bp: u8,
) -> Result<Result<Loc<Expr<'a>>, Loc<Token<'a>>>, String> {
    let token = lexer.next().unwrap()?;
    let mut lhs = match token.inner {
        Token::True => token.map(|_| Expr::True),
        Token::False => token.map(|_| Expr::False),
        Token::Decimal(s) => token.map(|_| Expr::Float(s)),
        Token::Hexcode(s) => token.map(|_| Expr::Hexcode(s)),
        Token::Ident(s) => token.map(|_| Expr::Ident(s)),
        Token::If => {
            let body = IfElse::parse_body(lexer)?;
            token.map(|_| Expr::IfElse(Box::new(body)))
        }
        Token::Let => {
            let body = let_in(lexer)?;
            token.map(|_| Expr::LetIn(Box::new(body)))
        }
        Token::Var(kind) => {
            let body = constructor(kind, lexer)?;
            token.map(|_| Expr::Constructor(body))
        }
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

fn ident<'a>(lexer: &mut Lexer<'a>) -> Result<Loc<&'a str>, String> {
    let token = lexer.next().unwrap()?;
    match token.inner {
        Token::Ident(s) => Ok(token.map(|_| s)),
        inner => Err(token.error(&format!("expected identifier got {inner:?}"))),
    }
}

fn colon(lexer: &mut Lexer<'_>) -> Result<(), String> {
    let token = lexer.next().unwrap()?;
    match token.inner {
        Token::Colon => Ok(()),
        inner => Err(token.error(&format!("expected ':' got {inner:?}"))),
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Literal<'a> {
    True,
    False,
    Decimal(&'a str),
    Hexcode(&'a str),
}

fn literal<'a>(lexer: &mut Lexer<'a>) -> Result<Loc<Literal<'a>>, String> {
    let token = lexer.next().unwrap()?;
    match token.inner {
        Token::True => Ok(token.map(|_| Literal::True)),
        Token::False => Ok(token.map(|_| Literal::False)),
        Token::Hexcode(s) => Ok(token.map(|_| Literal::Hexcode(s))),
        Token::Decimal(s) => Ok(token.map(|_| Literal::Decimal(s))),
        inner => Err(token.error(&format!("expected literal got {inner:?}"))),
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Attr<'a> {
    pub name: Loc<&'a str>,
    pub value: Loc<Literal<'a>>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Constructor<'a> {
    pub kind: Var,
    pub attrs: Vec<Attr<'a>>,
}

fn constructor<'a>(kind: Var, lexer: &mut Lexer<'a>) -> Result<Constructor<'a>, String> {
    let token = lexer.next().unwrap()?;
    match &token.inner {
        Token::BraceLeft => {}
        inner => Err(token.error(&format!("expected '{{' got {inner:?}")))?,
    };

    let mut attrs = Vec::new();

    loop {
        if lexer.peek().unwrap()?.inner == Token::BraceRight {
            lexer.next();
            break;
        }

        let name = ident(lexer)?;
        colon(lexer)?;
        let value = literal(lexer)?;

        attrs.push(Attr { name, value });

        let token = lexer.next().unwrap()?;
        match &token.inner {
            Token::BraceRight => break,
            Token::Semicolon => {}
            inner => Err(token.error(&format!("expected ';' or '}}' got {inner:?}")))?,
        };
    }

    Ok(Constructor { kind, attrs })
}

fn let_in<'a>(lexer: &mut Lexer<'a>) -> Result<LetIn<'a>, String> {
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
    Constructor(Constructor<'a>),
    True,
    False,
    Float(&'a str),
    Hexcode(&'a str),
    Ident(&'a str),
    UnOp(Box<UnOp<'a>>),
    BinOp(Box<BinOp<'a>>),
    IfElse(Box<IfElse<'a>>),
    LetIn(Box<LetIn<'a>>),
}

impl<'a> Expr<'a> {
    pub fn parse(lexer: &mut Lexer<'a>) -> Result<Loc<Self>, String> {
        match expr_bp(lexer, 0)? {
            Ok(expr) => Ok(expr),
            Err(token) => Err(token.error(format!(
                "expected 'let', 'if', '(' or an atom got {:?}",
                token.inner
            ))),
        }
    }
}

pub fn parse_source(source: &[u8]) -> Result<Loc<Expr<'_>>, String> {
    let mut lexer = Lexer::new(source);
    let expr = Expr::parse(&mut lexer)?;
    let token = lexer.next().unwrap()?;
    if token.inner == Token::Eof {
        Ok(expr)
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
            Ok(Expr::Float("3.14").loc(1, 1)),
        );
    }

    #[test]
    fn hexcode() {
        assert_eq!(
            parse_source(
                //1234567
                b"#123456",
            ),
            Ok(Expr::Hexcode("123456").loc(1, 1)),
        );
    }

    #[test]
    fn ident() {
        assert_eq!(
            parse_source(
                //123
                b"foo",
            ),
            Ok(Expr::Ident("foo").loc(1, 1)),
        );
    }

    #[test]
    fn let_x() {
        assert_eq!(
            parse_source(
                //         1         2
                //123456789012345678901234
                b"let pi = 3.14 in foo",
            ),
            Ok(Expr::LetIn(Box::new(LetIn {
                term: "pi".loc(1, 5),
                definition: Expr::Float("3.14").loc(1, 10),
                expr: Expr::Ident("foo").loc(1, 18),
            }))
            .loc(1, 1)),
        );
    }

    #[test]
    fn let_x_let_y() {
        assert_eq!(
            parse_source(
                //         1         2         3
                //12345678901234567890123456789012345678
                b"let pi = 3.14 in let tau = 6.28 in foo",
            ),
            Ok(Expr::LetIn(Box::new(LetIn {
                term: "pi".loc(1, 5),
                definition: Expr::Float("3.14").loc(1, 10),
                expr: Expr::LetIn(Box::new(LetIn {
                    term: "tau".loc(1, 22),
                    definition: Expr::Float("6.28").loc(1, 28),
                    expr: Expr::Ident("foo").loc(1, 36),
                }))
                .loc(1, 18),
            }))
            .loc(1, 1)),
        );
    }

    #[test]
    fn if_a_x_else_y() {
        assert_eq!(
            parse_source(
                //         1         2         3
                //123456789012345678901234567890123456789
                b"if 0.6 > 0.5 then brown else cyan",
            ),
            Ok(Expr::IfElse(Box::new(IfElse {
                cond: Expr::BinOp(Box::new(BinOp {
                    op: Op::Greater,
                    lhs: Expr::Float("0.6").loc(1, 4),
                    rhs: Expr::Float("0.5").loc(1, 10),
                }))
                .loc(1, 8),
                if_true: Expr::Ident("brown").loc(1, 19),
                if_false: Expr::Ident("cyan").loc(1, 30),
            }))
            .loc(1, 1)),
        );
    }

    #[test]
    fn if_a_x_else_if_b_y_else_z() {
        assert_eq!(
            parse_source(
                //         1         2         3         4         5         6         7         8
                //12345678901234567890123456789012345678901234567890123456789012345678901234567890123
                b"if 0.6 > 0.5 then cyan else if 0.4 < 0.31 then sandybrown else rosybrown"
            ),
            Ok(Expr::IfElse(Box::new(IfElse {
                cond: Expr::BinOp(Box::new(BinOp {
                    op: Op::Greater,
                    lhs: Expr::Float("0.6").loc(1, 4),
                    rhs: Expr::Float("0.5").loc(1, 10),
                }))
                .loc(1, 8),
                if_true: Expr::Ident("cyan").loc(1, 19),
                if_false: Expr::IfElse(Box::new(IfElse {
                    cond: Expr::BinOp(Box::new(BinOp {
                        op: Op::Less,
                        lhs: Expr::Float("0.4").loc(1, 32),
                        rhs: Expr::Float("0.31").loc(1, 38),
                    }))
                    .loc(1, 36),
                    if_true: Expr::Ident("sandybrown").loc(1, 48),
                    if_false: Expr::Ident("rosybrown").loc(1, 64),
                }))
                .loc(1, 29),
            }))
            .loc(1, 1)),
        );
    }

    #[test]
    fn if_a_if_b_x_else_y_else_z() {
        assert_eq!(
            parse_source(
                //         1         2         3         4         5         6         7         8
                //12345678901234567890123456789012345678901234567890123456789012345678901234567890123
                b"if 0.6 > 0.5 then if 0.4 < 0.31 then sandybrown else rosybrown else cyan",
            ),
            Ok(Expr::IfElse(Box::new(IfElse {
                cond: Expr::BinOp(Box::new(BinOp {
                    op: Op::Greater,
                    lhs: Expr::Float("0.6").loc(1, 4),
                    rhs: Expr::Float("0.5").loc(1, 10),
                }))
                .loc(1, 8),
                if_true: Expr::IfElse(Box::new(IfElse {
                    cond: Expr::BinOp(Box::new(BinOp {
                        op: Op::Less,
                        lhs: Expr::Float("0.4").loc(1, 22),
                        rhs: Expr::Float("0.31").loc(1, 28),
                    }))
                    .loc(1, 26),
                    if_true: Expr::Ident("sandybrown").loc(1, 38),
                    if_false: Expr::Ident("rosybrown").loc(1, 54),
                }))
                .loc(1, 19),
                if_false: Expr::Ident("cyan").loc(1, 69),
            }))
            .loc(1, 1)),
        );
    }

    #[test]
    fn wip() {
        assert_eq!(
            parse_source(
                //         1         2         3           1         2         3
                //123456789012345678901234567890  1234567890123456789012345678901234  1234567
                b"let peak = #A38983 in // brown\nlet mountain = #805C54 in // brown\n#123456"
            ),
            Ok(Expr::LetIn(Box::new(LetIn {
                term: "peak".loc(1, 5),
                definition: Expr::Hexcode("A38983").loc(1, 12),
                expr: Expr::LetIn(Box::new(LetIn {
                    term: "mountain".loc(2, 5),
                    definition: Expr::Hexcode("805C54").loc(2, 16),
                    expr: Expr::Hexcode("123456").loc(3, 1),
                }))
                .loc(2, 1),
            }))
            .loc(1, 1)),
        );
    }
}
