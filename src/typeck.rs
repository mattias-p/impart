use std::cell::RefCell;
use std::rc::Rc;

use palette::rgb::channels::Argb;
use palette::Srgb;

use crate::expr::Expr;
use crate::expr::IfThenElse;
use crate::expr::LetIn;
use crate::generate::VarId;
use crate::generate::VarSpec;
use crate::lexer::Loc;
use crate::lexer::Op;
use crate::lexer::Var;
use crate::ops;
use crate::ops::AnyExpr;
use crate::ops::Bool;
use crate::ops::Color;
use crate::ops::Float;
use crate::parser;

pub fn float_literal(literal: &Loc<parser::Literal>) -> Result<f32, String> {
    match literal.inner {
        parser::Literal::Decimal(s) => Ok(s.parse::<f32>().unwrap()),
        parser::Literal::True => Err(literal.error("expected number got bool")),
        parser::Literal::False => Err(literal.error("expected number got bool")),
        parser::Literal::Hexcode(_) => Err(literal.error("expected number got color")),
    }
}

#[derive(Debug)]
pub enum SymTable<'a> {
    Vars {
        vars: RefCell<Vec<VarSpec>>,
    },
    Sym {
        sym: &'a str,
        value: Rc<Loc<AnyExpr>>,
        next: &'a SymTable<'a>,
    },
}

impl<'a> SymTable<'a> {
    pub fn new() -> Self {
        SymTable::Vars {
            vars: RefCell::new(Vec::new()),
        }
    }

    pub fn get_vars(&self) -> Vec<VarSpec> {
        match self {
            SymTable::Sym { next, .. } => next.get_vars(),
            SymTable::Vars { vars } => vars.borrow().clone(),
        }
    }

    pub fn symbol(&self, name: &str) -> Option<Rc<Loc<AnyExpr>>> {
        match &*self {
            SymTable::Sym { sym, value, next } => {
                if *sym == name {
                    Some(value.clone())
                } else {
                    next.symbol(name)
                }
            }
            SymTable::Vars { .. } => None,
        }
    }

    pub fn with_def(&'a self, sym: Loc<&'a str>, value: AnyExpr) -> SymTable<'a> {
        let expr = match value {
            AnyExpr::Bool(expr) => AnyExpr::Bool(Expr::Ref(Rc::new(LetIn {
                value: sym.map(|_| RefCell::new(expr)),
            }))),
            AnyExpr::Color(expr) => AnyExpr::Color(Expr::Ref(Rc::new(LetIn {
                value: sym.map(|_| RefCell::new(expr)),
            }))),
            AnyExpr::Float(expr) => AnyExpr::Float(Expr::Ref(Rc::new(LetIn {
                value: sym.map(|_| RefCell::new(expr)),
            }))),
        };
        SymTable::Sym {
            sym: sym.inner,
            value: Rc::new(sym.map(|_| expr)),
            next: self,
        }
    }

    pub fn new_variable(&self, spec: VarSpec) -> VarId {
        match self {
            SymTable::Sym { next, .. } => next.new_variable(spec),
            SymTable::Vars { vars } => {
                let mut vars = vars.borrow_mut();
                let index = vars.len();
                vars.push(spec);
                VarId::new(index)
            }
        }
    }

    pub fn any_expr(&self, expr: &'a Loc<parser::Expr<'a>>) -> Result<AnyExpr, String> {
        match &expr.inner {
            parser::Expr::True => Ok(AnyExpr::Bool(Expr::Imm(true))),
            parser::Expr::False => Ok(AnyExpr::Bool(Expr::Imm(false))),
            parser::Expr::Float(s) => {
                let decoded = s.parse::<f32>().unwrap();
                Ok(AnyExpr::Float(Expr::Imm(decoded)))
            }
            parser::Expr::Hexcode(s) => {
                let argb = u32::from_str_radix(s, 16).unwrap();
                Ok(AnyExpr::Color(Expr::Imm(Srgb::<u8>::from_u32::<Argb>(
                    argb,
                ))))
            }
            parser::Expr::Ident(s) => match self.symbol(s) {
                Some(value) => Ok(value.inner.clone()),
                None => Err(expr.error("use of undeclared identifier")),
            },
            parser::Expr::Constructor(inner) => match inner.kind {
                Var::Perlin => {
                    let mut octaves = None;
                    let mut frequency = None;
                    let mut persistence = None;
                    for attr in &inner.attrs {
                        match attr.name.inner {
                            "octaves" => {
                                if octaves.is_some() {
                                    Err(attr.name.error("octaves already specified"))?;
                                }
                                let value = float_literal(&attr.value)?;
                                if value.fract().abs() > f32::EPSILON {
                                    Err(attr.value.error("octaves must be an integer"))?;
                                }
                                if value < 1.0 {
                                    Err(attr.value.error("there must be at least one octave"))?;
                                }
                                octaves = Some(value.round());
                            }
                            "frequency" => {
                                if frequency.is_some() {
                                    Err(attr.name.error("frequency already specified"))?;
                                }
                                frequency = Some(float_literal(&attr.value)?);
                            }
                            "persistence" => {
                                if persistence.is_some() {
                                    Err(attr.name.error("persistence already specified"))?;
                                }
                                persistence = Some(float_literal(&attr.value)?);
                            }
                            _ => Err(attr.name.error(format!(
                                "expected 'octaves', 'frequency' or 'persistence' got '{}'",
                                attr.name.inner
                            )))?,
                        }
                    }
                    let octaves =
                        octaves.ok_or_else(|| expr.error("must specify 'octaves'"))? as usize;
                    let frequency =
                        frequency.ok_or_else(|| expr.error("must specify 'frequency'"))?;
                    let persistence =
                        persistence.ok_or_else(|| expr.error("must specify 'persistence'"))?;

                    let variable = self.new_variable(VarSpec::Perlin {
                        octaves,
                        frequency,
                        persistence,
                    });

                    Ok(Float::Variable(variable).into())
                }
                Var::X => {
                    if let Some(attr) = inner.attrs.first() {
                        Err(attr
                            .name
                            .error(format!("expected no attributes got {:?}", attr.name.inner)))?;
                    }
                    let variable = self.new_variable(VarSpec::X);
                    Ok(Float::Variable(variable).into())
                }
                Var::Y => {
                    if let Some(attr) = inner.attrs.first() {
                        Err(attr
                            .name
                            .error(format!("expected no attributes got {:?}", attr.name.inner)))?;
                    }
                    let variable = self.new_variable(VarSpec::Y);
                    Ok(Float::Variable(variable).into())
                }
            },
            parser::Expr::LetIn(inner) => {
                let let_in = self.any_expr(&inner.definition)?;
                self.with_def(inner.term, let_in).any_expr(&inner.expr)
            }
            parser::Expr::UnOp(inner) => match inner.op {
                Op::Not => {
                    let rhs = self.bool_expr(&inner.rhs)?;
                    Ok(ops::Not::new(rhs).into())
                }
                Op::Minus => {
                    let rhs = self.float_expr(&inner.rhs)?;
                    Ok(ops::Neg::new(rhs).into())
                }
                _ => unreachable!("no such unary operator"),
            },
            parser::Expr::BinOp(inner) => match inner.op {
                Op::Asterisk => {
                    let lhs = self.float_expr(&inner.lhs)?;
                    let rhs = self.float_expr(&inner.rhs)?;
                    Ok(ops::Mul::new(lhs, rhs).into())
                }
                Op::Solidus => {
                    let lhs = self.float_expr(&inner.lhs)?;
                    let rhs = self.float_expr(&inner.rhs)?;
                    Ok(ops::Div::new(lhs, rhs).into())
                }
                Op::Plus => {
                    let lhs = self.float_expr(&inner.lhs)?;
                    let rhs = self.float_expr(&inner.rhs)?;
                    Ok(ops::Add::new(lhs, rhs).into())
                }
                Op::Minus => {
                    let lhs = self.float_expr(&inner.lhs)?;
                    let rhs = self.float_expr(&inner.rhs)?;
                    Ok(ops::Sub::new(lhs, rhs).into())
                }
                Op::Less => {
                    let lhs = self.float_expr(&inner.lhs)?;
                    let rhs = self.float_expr(&inner.rhs)?;
                    Ok(ops::Less::new(lhs, rhs).into())
                }
                Op::Greater => {
                    let lhs = self.float_expr(&inner.lhs)?;
                    let rhs = self.float_expr(&inner.rhs)?;
                    Ok(ops::Greater::new(lhs, rhs).into())
                }
                Op::And => {
                    let lhs = self.bool_expr(&inner.lhs)?;
                    let rhs = self.bool_expr(&inner.rhs)?;
                    Ok(ops::And::new(lhs, rhs).into())
                }
                Op::Xor => {
                    let lhs = self.bool_expr(&inner.lhs)?;
                    let rhs = self.bool_expr(&inner.rhs)?;
                    Ok(ops::Xor::new(lhs, rhs).into())
                }
                Op::Or => {
                    let lhs = self.bool_expr(&inner.lhs)?;
                    let rhs = self.bool_expr(&inner.rhs)?;
                    Ok(ops::Or::new(lhs, rhs).into())
                }
                _ => unreachable!("no such binary operator"),
            },
            parser::Expr::IfElse(inner) => {
                let cond = self.bool_expr(&inner.cond)?;
                let if_true = self.any_expr(&inner.if_true)?;
                let if_false = self.any_expr(&inner.if_false)?;
                match (if_true, if_false) {
                    (AnyExpr::Bool(if_true), AnyExpr::Bool(if_false)) => Ok(AnyExpr::Bool(Expr::IfThenElse(Box::new(IfThenElse{cond, if_true, if_false})))),
                    (AnyExpr::Color(if_true), AnyExpr::Color(if_false)) => Ok(AnyExpr::Color(Expr::IfThenElse(Box::new(IfThenElse{cond, if_true, if_false})))),
                    (AnyExpr::Float(if_true), AnyExpr::Float(if_false)) => Ok(AnyExpr::Float(Expr::IfThenElse(Box::new(IfThenElse{cond, if_true, if_false})))),
                    (if_true, if_false) => {
                        Err(format!("expression at {}:{} ({}) has a different type from expression at {}:{} ({})", inner.if_false.line, inner.if_false.col, if_false.get_type()
, inner.if_true.line, inner.if_true.col, if_true.get_type()))
                    }
                }
            }
        }
    }

    fn bool_expr(&self, value: &'a Loc<parser::Expr<'a>>) -> Result<Expr<Bool>, String> {
        match self.any_expr(value)? {
            AnyExpr::Bool(expr) => Ok(expr),
            AnyExpr::Float(expr) => Err(expr.error("expected bool got float")),
            AnyExpr::Color(expr) => Err(expr.error("expected bool got color")),
        }
    }

    fn color_expr(&self, value: &'a Loc<parser::Expr<'a>>) -> Result<Expr<Color>, String> {
        match self.any_expr(value)? {
            AnyExpr::Color(expr) => Ok(expr),
            AnyExpr::Bool(expr) => Err(expr.error("expected color got bool")),
            AnyExpr::Float(expr) => Err(expr.error("expected color got float")),
        }
    }

    fn float_expr(&self, value: &'a Loc<parser::Expr<'a>>) -> Result<Expr<Float>, String> {
        match self.any_expr(value)? {
            AnyExpr::Float(expr) => Ok(expr),
            AnyExpr::Bool(expr) => Err(expr.error("expected float got bool")),
            AnyExpr::Color(expr) => Err(expr.error("expected float got color")),
        }
    }
}

pub fn parse_source(source: &[u8]) -> Result<(Expr<Color>, Vec<VarSpec>), String> {
    let tree = parser::parse_source(source)?;
    let symtable = SymTable::new();
    let expr = symtable.color_expr(&tree)?;
    let vars = symtable.get_vars();
    Ok((expr, vars))
}

#[cfg(test)]
mod tests {
    use super::*;

    use palette::rgb::channels::Argb;

    fn check(corpus: &[u8]) -> Result<Expr<Color>, String> {
        Ok(parse_source(corpus)?.0)
    }

    fn color(hexcode: &str) -> Srgb<u8> {
        let hexcode = u32::from_str_radix(hexcode, 16).unwrap();
        Srgb::from_u32::<Argb>(hexcode)
    }

    #[test]
    fn hexcode() {
        assert_eq!(check(b"#fc9630"), Ok(Expr::Imm(color("fc9630"))));
    }
    #[test]
    fn let_in() {
        assert_eq!(
            check(b"let brown = #123456 in\nbrown"),
            Ok(Expr::Ref(Rc::new(LetIn {
                inner: Loc {
                    line: 1,
                    col: 5,
                    inner: RefCell::new(Expr::Imm(color("123456")))
                }
            }))),
        );
    }
    #[test]
    fn let_in_let_in() {
        assert_eq!(
            check(b"let foo = #123456 in\nlet foo = #654321 in\nfoo"),
            Ok(Expr::Ref(Rc::new(LetIn {
                inner: Loc {
                    line: 2,
                    col: 5,
                    inner: RefCell::new(Expr::Imm(color("654321")))
                }
            }))),
        );
    }
}
