use palette::named;
use palette::rgb::channels::Argb;
use palette::Srgb;

use crate::generate::Cell;
use crate::lexer::Comparator;
use crate::lexer::Lexer;
use crate::lexer::Token;
use crate::lexer::Variable;

pub type Color = Srgb<u8>;

#[derive(Debug, PartialEq)]
struct Cond {
    variable: Variable,
    comparator: Comparator,
    number: f32,
}

impl Cond {
    fn parse<'a>(lexer: &mut Lexer<'a>) -> Result<Self, String> {
        let context = lexer.get_context();
        let variable = match lexer
            .next()
            .unwrap_or_else(|| Err(context.error("unexpected EOF")))?
        {
            Token::Variable(var) => var,
            token => Err(context.error(&format!("expected variable got {token:?}")))?,
        };

        let context = lexer.get_context();
        let comparator = match lexer
            .next()
            .unwrap_or_else(|| Err(context.error("unexpected EOF")))?
        {
            Token::Comparator(cmp) => cmp,
            token => Err(context.error(&format!("expected comparator got {token:?}")))?,
        };

        let context = lexer.get_context();
        let number = match lexer
            .next()
            .unwrap_or_else(|| Err(context.error("unexpected EOF")))?
        {
            Token::Number(number) => number,
            token => Err(context.error(&format!("expected number got {token:?}")))?,
        };
        Ok(Cond {
            variable,
            comparator,
            number,
        })
    }

    fn eval(&self, cell: Cell) -> bool {
        let number = match self.variable {
            Variable::Elevation => cell.elevation,
            Variable::Temperature => cell.temperature,
            Variable::Humidity => cell.humidity,
        };
        match self.comparator {
            Comparator::GreaterThan => number > self.number,
            Comparator::LessThan => number < self.number,
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct Case {
    cond: Cond,
    yes: Box<Expr>,
    no: Box<Expr>,
}

impl Case {
    fn parse<'a>(lexer: &mut Lexer<'a>) -> Result<Self, String> {
        let cond = Cond::parse(lexer)?;
        let yes = Box::new(Expr::parse_inner(lexer)?);

        let context = lexer.get_context();
        match lexer
            .next()
            .unwrap_or_else(|| Err(context.error("unexpected EOF")))?
        {
            Token::Else => {
                let no = Box::new(Expr::parse_inner(lexer)?);
                Ok(Case { cond, yes, no })
            }
            Token::Case => {
                let no = Box::new(Expr::Case(Case::parse(lexer)?));
                Ok(Case { cond, yes, no })
            }
            token => Err(context.error(&format!("expected 'else' got {token:?}")))?,
        }
    }

    fn eval(&self, cell: Cell) -> Color {
        if self.cond.eval(cell) {
            self.yes.eval(cell)
        } else {
            self.no.eval(cell)
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum Expr {
    Color(Color),
    Case(Case),
}

impl Expr {
    fn parse_inner<'a>(lexer: &mut Lexer<'a>) -> Result<Self, String> {
        let context = lexer.get_context();
        match lexer
            .next()
            .unwrap_or_else(|| Err(context.error("unexpected EOF")))?
        {
            Token::Quoted(name) => match named::from_str(&name) {
                Some(color) => Ok(Expr::Color(color)),
                None => Err(context.error("unrecognized color name")),
            },
            Token::Hexcode(rgb) => Ok(Expr::Color(Color::from_u32::<Argb>(rgb))),
            Token::Case => Ok(Expr::Case(Case::parse(lexer)?)),
            token => Err(context.error(&format!("unexpected token {token:?}"))),
        }
    }

    pub fn parse<'a>(lexer: &mut Lexer<'a>) -> Result<Self, String> {
        let expr = Self::parse_inner(lexer)?;

        let context = lexer.get_context();
        if let Some(token) = lexer.next() {
            let token = token?;
            Err(context.error(&format!("expected EOF got {token:?}")))?;
        }
        Ok(expr)
    }

    pub fn eval(&self, cell: Cell) -> Color {
        match self {
            Expr::Color(name) => name.clone(),
            Expr::Case(case) => case.eval(cell),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn check(corpus: &[u8]) -> Result<Expr, String> {
        Expr::parse(&mut Lexer::new(corpus))
    }
    fn named_color(name: &str) -> Expr {
        Expr::Color(named::from_str(name).unwrap())
    }

    #[test]
    fn parse() {
        assert_eq!(check(br#""brown""#), Ok(named_color("brown")));
        assert_eq!(check(br#" "brown""#), Ok(named_color("brown")));
        assert_eq!(
            check(b"#fc9630"),
            Ok(Expr::Color(Srgb::from_u32::<Argb>(0xfc9630)))
        );
        assert_eq!(
            check(br#"case elevation > 0.5 "brown" else "cyan""#),
            Ok(Expr::Case(Case {
                cond: Cond {
                    variable: Variable::Elevation,
                    comparator: Comparator::GreaterThan,
                    number: 0.5,
                },
                yes: Box::new(named_color("brown")),
                no: Box::new(named_color("cyan")),
            }))
        );
        assert_eq!(
            check(b"case xelevation"),
            Err("expected variable got Ident(\"xelevation\") at 1:6".to_string())
        );
        assert_eq!(
            check(b"case\nxelevation"),
            Err("expected variable got Ident(\"xelevation\") at 2:1".to_string())
        );
        assert_eq!(
            check(br#"case elevation > 0.5 case humidity < 0.31 "sandybrown" else "rosybrown" else "cyan""#),
            Ok(Expr::Case(Case {
                cond: Cond {
                    variable: Variable::Elevation,
                    comparator: Comparator::GreaterThan,
                    number: 0.5,
                },
                yes: Box::new(Expr::Case(Case {
                    cond: Cond {
                        variable: Variable::Humidity,
                        comparator: Comparator::LessThan,
                        number: 0.31,
                    },
                    yes: Box::new(named_color("sandybrown")),
                    no: Box::new(named_color("rosybrown")),
                })),
                no: Box::new(named_color("cyan")),
            }))
        );
        assert_eq!(
            check(br#"case elevation < 0.5 "cyan" case humidity < 0.31 "sandybrown" else "rosybrown""#),
            Ok(Expr::Case(Case {
                cond: Cond {
                    variable: Variable::Elevation,
                    comparator: Comparator::LessThan,
                    number: 0.5,
                },
                yes: Box::new(named_color("cyan")),
                no: Box::new(Expr::Case(Case {
                    cond: Cond {
                        variable: Variable::Humidity,
                        comparator: Comparator::LessThan,
                        number: 0.31,
                    },
                    yes: Box::new(named_color("sandybrown")),
                    no: Box::new(named_color("rosybrown")),
                })),
            }))
        );
    }
}
