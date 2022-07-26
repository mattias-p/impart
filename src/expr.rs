use std::collections::hash_map::Entry;
use std::collections::HashMap;

use palette::named;
use palette::rgb::channels::Argb;
use palette::Srgb;

use crate::ast;
use crate::generate::Cell;
use crate::lexer::Loc;

pub type Color = Srgb<u8>;
type Definitions<'a> = HashMap<&'a str, Loc<Literal>>;

#[derive(Clone, Copy)]
pub enum Literal {
    Float(f32),
    Color(Color),
}

impl<'a> TryFrom<ast::Literal<'a>> for Literal {
    type Error = String;

    fn try_from(literal: ast::Literal<'a>) -> Result<Self, Self::Error> {
        match literal {
            ast::Literal::Hexcode(s) => {
                let argb = u32::from_str_radix(s, 16).unwrap();
                let color = Color::from_u32::<Argb>(argb);
                Ok(Literal::Color(color))
            }
            ast::Literal::Float(s) => {
                let x = s.parse::<f32>().unwrap();
                Ok(Literal::Float(x))
            }
        }
    }
}

impl<'a> TryFrom<(ast::Value<'a>, &Definitions<'a>)> for Literal {
    type Error = String;

    fn try_from(pair: (ast::Value<'a>, &Definitions<'a>)) -> Result<Self, Self::Error> {
        let (value, defs) = pair;
        match value {
            ast::Value::Literal(literal) => Literal::try_from(literal),
            ast::Value::Ident(s) => match defs.get(s) {
                Some(literal) => Ok(literal.inner),
                None => match named::from_str(s) {
                    Some(color) => Ok(Literal::Color(color)),
                    None => Err(format!("use of undeclared identifier")),
                },
            },
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct Case {
    variable: ast::Variable,
    comparator: ast::Comparator,
    number: f32,
    yes: Box<Expr>,
    no: Box<Expr>,
}

impl Case {
    fn eval(&self, cell: Cell) -> Color {
        let number = match self.variable {
            ast::Variable::Elevation => cell.elevation,
            ast::Variable::Temperature => cell.temperature,
            ast::Variable::Humidity => cell.humidity,
        };

        let cond = match self.comparator {
            ast::Comparator::GreaterThan => number > self.number,
            ast::Comparator::LessThan => number < self.number,
        };

        if cond {
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
    pub fn compile<'a>(expr: &Loc<ast::Expr<'a>>, defs: &Definitions) -> Result<Self, String> {
        match expr.inner.clone() {
            ast::Expr::Value(value) => match (value, defs).try_into() {
                Ok(Literal::Color(color)) => Ok(Expr::Color(color)),
                Ok(Literal::Float(_)) => Err(expr.error("expected color got float")),
                Err(e) => Err(expr.error(e.to_string()))?,
            },
            ast::Expr::Case(ast::Case {
                variable,
                comparator,
                value,
                yes,
                no,
            }) => {
                let number = match (value.inner, defs).try_into() {
                    Ok(Literal::Float(x)) => x,
                    Ok(Literal::Color(_)) => Err(value.error("expected float got color"))?,
                    Err(e) => Err(expr.error(e.to_string()))?,
                };

                let yes = Box::new(Expr::compile(&*yes, defs)?);
                let no = Box::new(Expr::compile(&*no, defs)?);

                Ok(Expr::Case(Case {
                    variable: variable.inner,
                    comparator: comparator.inner,
                    number,
                    yes,
                    no,
                }))
            }
        }
    }

    pub fn eval(&self, cell: Cell) -> Color {
        match self {
            Expr::Color(name) => name.clone(),
            Expr::Case(case) => case.eval(cell),
        }
    }
}

pub fn compile<'a>(tops: Vec<Loc<ast::Top<'a>>>) -> Result<Expr, String> {
    let mut expr: Option<Loc<_>> = None;
    let mut defs = HashMap::new();
    for top in tops {
        match top.inner.clone() {
            ast::Top::Let(def) => match defs.entry(def.ident.inner) {
                Entry::Vacant(vacant) => {
                    if named::from_str(def.ident.inner).is_some() {
                        Err(format!(
                            "cannot redefine '{}' at {}:{} (predefined)",
                            def.ident.inner, def.ident.line, def.ident.col
                        ))?;
                    } else {
                        let literal = def
                            .ident
                            .try_map(|_| Literal::try_from(def.literal.inner))?;
                        vacant.insert(literal);
                    }
                }
                Entry::Occupied(occupied) => {
                    let old_def = occupied.get();
                    Err(format!(
                        "cannot redefine '{}' at {}:{} (first defined at {}:{})",
                        def.ident.inner, def.ident.line, def.ident.col, old_def.line, old_def.col
                    ))?;
                }
            },
            ast::Top::Expr(inner) => {
                if let Some(old_expr) = &expr {
                    Err(format!("there must be exactly one expression but the first one was given at {}:{} and another one was given at {}:{}", old_expr.line, old_expr.col, top.line, top.col))?;
                }
                expr = Some(top.map(|_| inner));
            }
        }
    }
    match expr {
        None => Err(format!(
            "there must be exactly one expression but none was given"
        )),
        Some(expr) => Expr::compile(&expr, &defs),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::lexer::Lexer;

    fn check(corpus: &[u8]) -> Result<Expr, String> {
        let mut lexer = Lexer::new(corpus);
        let ast = ast::parse(&mut lexer)?;
        compile(ast)
    }

    fn named_color(name: &str) -> Expr {
        Expr::Color(named::from_str(name).unwrap())
    }

    #[test]
    fn parse() {
        assert_eq!(check(b"brown"), Ok(named_color("brown")));
        assert_eq!(
            check(b"#fc9630"),
            Ok(Expr::Color(Srgb::from_u32::<Argb>(0xfc9630)))
        );
        assert_eq!(
            check(b"case elevation > 0.5 brown else cyan"),
            Ok(Expr::Case(Case {
                variable: ast::Variable::Elevation,
                comparator: ast::Comparator::GreaterThan,
                number: 0.5,
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
            check(b"case elevation > 0.5 case humidity < 0.31 sandybrown else rosybrown else cyan"),
            Ok(Expr::Case(Case {
                variable: ast::Variable::Elevation,
                comparator: ast::Comparator::GreaterThan,
                number: 0.5,
                yes: Box::new(Expr::Case(Case {
                    variable: ast::Variable::Humidity,
                    comparator: ast::Comparator::LessThan,
                    number: 0.31,
                    yes: Box::new(named_color("sandybrown")),
                    no: Box::new(named_color("rosybrown")),
                })),
                no: Box::new(named_color("cyan")),
            }))
        );
        assert_eq!(
            check(b"case elevation < 0.5 cyan case humidity < 0.31 sandybrown else rosybrown"),
            Ok(Expr::Case(Case {
                variable: ast::Variable::Elevation,
                comparator: ast::Comparator::LessThan,
                number: 0.5,
                yes: Box::new(named_color("cyan")),
                no: Box::new(Expr::Case(Case {
                    variable: ast::Variable::Humidity,
                    comparator: ast::Comparator::LessThan,
                    number: 0.31,
                    yes: Box::new(named_color("sandybrown")),
                    no: Box::new(named_color("rosybrown")),
                })),
            }))
        );
        assert_eq!(
            check(b"let brown = #123456\nbrown"),
            Err("cannot redefine 'brown' at 1:5 (predefined)".to_string())
        );
        assert_eq!(
            check(b"let foo = #123456\nlet foo = #654321\nfoo"),
            Err("cannot redefine 'foo' at 2:5 (first defined at 1:5)".to_string())
        );
    }
}
