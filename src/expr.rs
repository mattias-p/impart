use std::collections::hash_map::Entry;
use std::collections::HashMap;

use palette::named;
use palette::rgb::channels::Argb;
use palette::Srgb;

use crate::ast;
use crate::generate::Cell;
use crate::lexer::Loc;

pub type Color = Srgb<u8>;
type Definitions<'a> = HashMap<&'a str, Loc<Value>>;

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Variable {
    Elevation,
    Temperature,
    Humidity,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Float {
    Const(f32),
    Variable(Variable),
}

#[derive(Clone, Copy)]
pub enum Value {
    Float(Float),
    Color(Color),
}

impl<'a> TryFrom<ast::Literal<'a>> for Value {
    type Error = String;

    fn try_from(literal: ast::Literal<'a>) -> Result<Self, Self::Error> {
        match literal {
            ast::Literal::Hexcode(s) => {
                let argb = u32::from_str_radix(s, 16).unwrap();
                let color = Color::from_u32::<Argb>(argb);
                Ok(Value::Color(color))
            }
            ast::Literal::Float(s) => {
                let x = s.parse::<f32>().unwrap();
                Ok(Value::Float(Float::Const(x)))
            }
        }
    }
}

impl<'a> TryFrom<(ast::Value<'a>, &Definitions<'a>)> for Value {
    type Error = String;

    fn try_from(pair: (ast::Value<'a>, &Definitions<'a>)) -> Result<Self, Self::Error> {
        let (value, defs) = pair;
        match value {
            ast::Value::Literal(literal) => Value::try_from(literal),
            ast::Value::Ident("elevation") => Ok(Value::Float(Float::Variable(Variable::Elevation))),
            ast::Value::Ident("temperature") => Ok(Value::Float(Float::Variable(Variable::Temperature))),
            ast::Value::Ident("humidity") => Ok(Value::Float(Float::Variable(Variable::Humidity))),
            ast::Value::Ident(s) => match defs.get(s) {
                Some(value) => Ok(value.inner),
                None => match named::from_str(s) {
                    Some(color) => Ok(Value::Color(color)),
                    None => Err(format!("use of undeclared identifier")),
                },
            },
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct Case {
    left: Float,
    comparator: ast::Comparator,
    right: Float,
    yes: Box<Expr>,
    no: Box<Expr>,
}

impl Case {
    fn eval(&self, cell: Cell) -> Color {
        let left = match self.left {
            Float::Const(value) => value,
            Float::Variable(Variable::Elevation) => cell.elevation,
            Float::Variable(Variable::Temperature) => cell.temperature,
            Float::Variable(Variable::Humidity) => cell.humidity,
        };

        let right = match self.right {
            Float::Const(value) => value,
            Float::Variable(Variable::Elevation) => cell.elevation,
            Float::Variable(Variable::Temperature) => cell.temperature,
            Float::Variable(Variable::Humidity) => cell.humidity,
        };

        let cond = match self.comparator {
            ast::Comparator::GreaterThan => left > right,
            ast::Comparator::LessThan => left < right,
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
                Ok(Value::Color(color)) => Ok(Expr::Color(color)),
                Ok(Value::Float(_)) => Err(expr.error("expected color got float")),
                Err(e) => Err(expr.error(e.to_string()))?,
            },
            ast::Expr::Case(ast::Case {
                left,
                comparator,
                right,
                yes,
                no,
            }) => {
                let left = match (left.inner, defs).try_into() {
                    Ok(Value::Float(x)) => x,
                    Ok(Value::Color(_)) => Err(left.error("expected float got color"))?,
                    Err(e) => Err(expr.error(e.to_string()))?,
                };

                let right = match (right.inner, defs).try_into() {
                    Ok(Value::Float(x)) => x,
                    Ok(Value::Color(_)) => Err(right.error("expected float got color"))?,
                    Err(e) => Err(expr.error(e.to_string()))?,
                };

                let yes = Box::new(Expr::compile(&*yes, defs)?);
                let no = Box::new(Expr::compile(&*no, defs)?);

                Ok(Expr::Case(Case {
                    left,
                    comparator: comparator.inner,
                    right,
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
                        let value = def.ident.try_map(|_| Value::try_from(def.literal.inner))?;
                        vacant.insert(value);
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
                left: Float::Variable(Variable::Elevation),
                comparator: ast::Comparator::GreaterThan,
                right: Float::Const(0.5),
                yes: Box::new(named_color("brown")),
                no: Box::new(named_color("cyan")),
            }))
        );
        assert_eq!(
            check(b"case elevation > 0.5 case humidity < 0.31 sandybrown else rosybrown else cyan"),
            Ok(Expr::Case(Case {
                left: Float::Variable(Variable::Elevation),
                comparator: ast::Comparator::GreaterThan,
                right: Float::Const(0.5),
                yes: Box::new(Expr::Case(Case {
                    left: Float::Variable(Variable::Humidity),
                    comparator: ast::Comparator::LessThan,
                    right: Float::Const(0.31),
                    yes: Box::new(named_color("sandybrown")),
                    no: Box::new(named_color("rosybrown")),
                })),
                no: Box::new(named_color("cyan")),
            }))
        );
        assert_eq!(
            check(b"case elevation < 0.5 cyan case humidity < 0.31 sandybrown else rosybrown"),
            Ok(Expr::Case(Case {
                left: Float::Variable(Variable::Elevation),
                comparator: ast::Comparator::LessThan,
                right: Float::Const(0.5),
                yes: Box::new(named_color("cyan")),
                no: Box::new(Expr::Case(Case {
                    left: Float::Variable(Variable::Humidity),
                    comparator: ast::Comparator::LessThan,
                    right: Float::Const(0.31),
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
