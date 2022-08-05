use std::cell::RefCell;
use std::rc::Rc;

use palette::rgb::channels::Argb;
use palette::Srgb;

use crate::ast;
use crate::generate::VarId;
use crate::generate::VarSpec;
use crate::ir::AnyExpr;
use crate::ir::Bool;
use crate::ir::Color;
use crate::ir::Def;
use crate::ir::Expr;
use crate::ir::Float;
use crate::ir::IfThenElse;
use crate::ir::Neg;
use crate::ir::Not;
use crate::ir::UnaryOp;
use crate::lexer::Loc;
use crate::lexer::Op;
use crate::lexer::Var;

pub fn float_literal(literal: &Loc<ast::Literal>) -> Result<f32, String> {
    match literal.inner {
        ast::Literal::Decimal(s) => Ok(s.parse::<f32>().unwrap()),
        ast::Literal::True => Err(literal.error("expected number got bool")),
        ast::Literal::False => Err(literal.error("expected number got bool")),
        ast::Literal::Hexcode(_) => Err(literal.error("expected number got color")),
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
            AnyExpr::Bool(expr) => AnyExpr::Bool(Expr::Ref(Rc::new(Def {
                inner: sym.map(|_| RefCell::new(expr)),
            }))),
            AnyExpr::Color(expr) => AnyExpr::Color(Expr::Ref(Rc::new(Def {
                inner: sym.map(|_| RefCell::new(expr)),
            }))),
            AnyExpr::Float(expr) => AnyExpr::Float(Expr::Ref(Rc::new(Def {
                inner: sym.map(|_| RefCell::new(expr)),
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

    pub fn any_expr(&self, expr: &'a Loc<ast::Expr<'a>>) -> Result<AnyExpr, String> {
        match &expr.inner {
            ast::Expr::True => Ok(AnyExpr::Bool(Expr::Imm(true))),
            ast::Expr::False => Ok(AnyExpr::Bool(Expr::Imm(false))),
            ast::Expr::Float(s) => {
                let decoded = s.parse::<f32>().unwrap();
                Ok(AnyExpr::Float(Expr::Imm(decoded)))
            }
            ast::Expr::Hexcode(s) => {
                let argb = u32::from_str_radix(s, 16).unwrap();
                Ok(AnyExpr::Color(Expr::Imm(Srgb::<u8>::from_u32::<Argb>(
                    argb,
                ))))
            }
            ast::Expr::Ident(s) => match self.symbol(s) {
                Some(def) => Ok(def.inner.clone()),
                None => Err(expr.error("use of undeclared identifier")),
            },
            ast::Expr::Constructor(inner) => match inner.kind {
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

                    Ok(Float::Variable(variable).into_anyexpr())
                }
                Var::X => {
                    if let Some(attr) = inner.attrs.first() {
                        Err(attr
                            .name
                            .error(format!("expected no attributes got {:?}", attr.name.inner)))?;
                    }
                    let variable = self.new_variable(VarSpec::X);
                    Ok(Float::Variable(variable).into_anyexpr())
                }
                Var::Y => {
                    if let Some(attr) = inner.attrs.first() {
                        Err(attr
                            .name
                            .error(format!("expected no attributes got {:?}", attr.name.inner)))?;
                    }
                    let variable = self.new_variable(VarSpec::Y);
                    Ok(Float::Variable(variable).into_anyexpr())
                }
            },
            ast::Expr::LetIn(inner) => {
                let def = self.any_expr(&inner.definition)?;
                self.with_def(inner.term, def).any_expr(&inner.expr)
            }
            ast::Expr::UnOp(inner) => match inner.op {
                Op::Not => {
                    let rhs = self.bool_expr(&inner.rhs)?;
                    Ok(Not::wrap(rhs).into_anyexpr())
                }
                Op::Minus => {
                    let rhs = self.float_expr(&inner.rhs)?;
                    Ok(Neg::wrap(rhs).into_anyexpr())
                }
                _ => unreachable!("no such unary operator"),
            },
            ast::Expr::BinOp(inner) => match inner.op {
                Op::Asterisk => {
                    let lhs = self.float_expr(&inner.lhs)?;
                    let rhs = self.float_expr(&inner.rhs)?;
                    Ok(Float::Mul(lhs, rhs).into_anyexpr())
                }
                Op::Solidus => {
                    let lhs = self.float_expr(&inner.lhs)?;
                    let rhs = self.float_expr(&inner.rhs)?;
                    Ok(Float::Div(lhs, rhs).into_anyexpr())
                }
                Op::Plus => {
                    let lhs = self.float_expr(&inner.lhs)?;
                    let rhs = self.float_expr(&inner.rhs)?;
                    Ok(Float::Add(lhs, rhs).into_anyexpr())
                }
                Op::Minus => {
                    let lhs = self.float_expr(&inner.lhs)?;
                    let rhs = self.float_expr(&inner.rhs)?;
                    Ok(Float::Sub(lhs, rhs).into_anyexpr())
                }
                Op::Less => {
                    let lhs = self.float_expr(&inner.lhs)?;
                    let rhs = self.float_expr(&inner.rhs)?;
                    Ok(Bool::Less(lhs, rhs).into_anyexpr())
                }
                Op::Greater => {
                    let lhs = self.float_expr(&inner.lhs)?;
                    let rhs = self.float_expr(&inner.rhs)?;
                    Ok(Bool::Greater(lhs, rhs).into_anyexpr())
                }
                Op::And => {
                    let lhs = self.bool_expr(&inner.lhs)?;
                    let rhs = self.bool_expr(&inner.rhs)?;
                    Ok(Bool::And(lhs, rhs).into_anyexpr())
                }
                Op::Xor => {
                    let lhs = self.bool_expr(&inner.lhs)?;
                    let rhs = self.bool_expr(&inner.rhs)?;
                    Ok(Bool::Xor(lhs, rhs).into_anyexpr())
                }
                Op::Or => {
                    let lhs = self.bool_expr(&inner.lhs)?;
                    let rhs = self.bool_expr(&inner.rhs)?;
                    Ok(Bool::Or(lhs, rhs).into_anyexpr())
                }
                _ => unreachable!("no such binary operator"),
            },
            ast::Expr::IfElse(inner) => {
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

    fn bool_expr(&self, value: &'a Loc<ast::Expr<'a>>) -> Result<Expr<Bool>, String> {
        match self.any_expr(value)? {
            AnyExpr::Bool(expr) => Ok(expr),
            AnyExpr::Float(expr) => Err(expr.error("expected bool got float")),
            AnyExpr::Color(expr) => Err(expr.error("expected bool got color")),
        }
    }

    fn color_expr(&self, value: &'a Loc<ast::Expr<'a>>) -> Result<Expr<Color>, String> {
        match self.any_expr(value)? {
            AnyExpr::Color(expr) => Ok(expr),
            AnyExpr::Bool(expr) => Err(expr.error("expected color got bool")),
            AnyExpr::Float(expr) => Err(expr.error("expected color got float")),
        }
    }

    fn float_expr(&self, value: &'a Loc<ast::Expr<'a>>) -> Result<Expr<Float>, String> {
        match self.any_expr(value)? {
            AnyExpr::Float(expr) => Ok(expr),
            AnyExpr::Bool(expr) => Err(expr.error("expected float got bool")),
            AnyExpr::Color(expr) => Err(expr.error("expected float got color")),
        }
    }
}

pub fn parse_source(source: &[u8]) -> Result<(Expr<Color>, Vec<VarSpec>), String> {
    let tree = ast::parse_source(source)?;
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
            Ok(Expr::Ref(Rc::new(Def {
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
            Ok(Expr::Ref(Rc::new(Def {
                inner: Loc {
                    line: 2,
                    col: 5,
                    inner: RefCell::new(Expr::Imm(color("654321")))
                }
            }))),
        );
    }
}
