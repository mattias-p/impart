use std::cell::RefCell;
use std::rc::Rc;

use crate::expr::Expr;
use crate::expr::IfThenElse;
use crate::expr::Type;
use crate::ops::Add;
use crate::ops::And;
use crate::ops::Bool;
use crate::ops::Color;
use crate::ops::Div;
use crate::ops::Float;
use crate::ops::Greater;
use crate::ops::Less;
use crate::ops::Mul;
use crate::ops::Neg;
use crate::ops::Not;
use crate::ops::Or;
use crate::ops::Sub;
use crate::ops::Xor;

pub trait Inline {
    type Output;

    fn inline(self) -> Self::Output;
}

impl Inline for Bool {
    type Output = Expr<Self>;
    fn inline(self) -> Expr<Self> {
        match self {
            Bool::Not(Not { rhs }) => Expr::TypeOp(Box::new(Not::new(rhs.inline()))),
            Bool::And(And { lhs, rhs }) => {
                Expr::TypeOp(Box::new(And::new(lhs.inline(), rhs.inline())))
            }
            Bool::Xor(Xor { lhs, rhs }) => {
                Expr::TypeOp(Box::new(Xor::new(lhs.inline(), rhs.inline())))
            }
            Bool::Or(Or { lhs, rhs }) => {
                Expr::TypeOp(Box::new(Or::new(lhs.inline(), rhs.inline())))
            }
            Bool::Greater(Greater { lhs, rhs }) => {
                Expr::TypeOp(Box::new(Greater::new(lhs.inline(), rhs.inline())))
            }
            Bool::Less(Less { lhs, rhs }) => {
                Expr::TypeOp(Box::new(Less::new(lhs.inline(), rhs.inline())))
            }
        }
    }
}

impl Inline for Color {
    type Output = Expr<Self>;
    fn inline(self) -> Expr<Self> {
        match self {}
    }
}

impl Inline for Float {
    type Output = Expr<Self>;
    fn inline(self) -> Expr<Self> {
        match self {
            Float::Variable(_) => Expr::TypeOp(Box::new(self.clone())),
            Float::Neg(Neg { rhs }) => Expr::TypeOp(Box::new(Neg::new(rhs.inline()))),
            Float::Mul(Mul { lhs, rhs }) => {
                Expr::TypeOp(Box::new(Mul::new(lhs.inline(), rhs.inline())))
            }
            Float::Div(Div { lhs, rhs }) => {
                Expr::TypeOp(Box::new(Div::new(lhs.inline(), rhs.inline())))
            }
            Float::Add(Add { lhs, rhs }) => {
                Expr::TypeOp(Box::new(Add::new(lhs.inline(), rhs.inline())))
            }
            Float::Sub(Sub { lhs, rhs }) => {
                Expr::TypeOp(Box::new(Sub::new(lhs.inline(), rhs.inline())))
            }
        }
    }
}

impl<Output> Inline for Expr<Output>
where
    Output: Type + Inline<Output = Self> + Clone,
    <Output as Type>::Cond: Type<Repr = bool>,
    <Output as Type>::Cond: Type<Cond = <Output as Type>::Cond>,
    <Output as Type>::Cond: Inline<Output = Expr<<Output as Type>::Cond>>,
{
    type Output = Self;
    fn inline(self) -> Self {
        match self {
            expr @ Expr::Imm(_) => expr,
            Expr::TypeOp(op) => op.inline(),
            Expr::IfThenElse(if_then_else) => {
                let cond = if_then_else.cond.inline();
                let if_true = if_then_else.if_true.inline();
                let if_false = if_then_else.if_false.inline();
                Expr::IfThenElse(Box::new(IfThenElse {
                    cond,
                    if_true,
                    if_false,
                }))
            }
            Expr::Ref(def) => {
                let tmp = RefCell::new(Expr::Imm(Default::default()));
                def.inner.inner.swap(&tmp);
                let expr = tmp.into_inner().inline();
                def.inner.inner.replace(expr.clone());
                match Rc::try_unwrap(def) {
                    Ok(def) => def.inner.inner.into_inner(),
                    Err(def) => Expr::Ref(def),
                }
            }
        }
    }
}
