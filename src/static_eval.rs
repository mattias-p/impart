use std::cell::RefCell;

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

pub trait StaticEval {
    type Output;

    fn eval_static(&self) -> Self::Output;
}

impl StaticEval for Not {
    type Output = Expr<Bool>;
    fn eval_static(&self) -> Expr<Bool>
    where
        Self: Sized,
    {
        let rhs = self.rhs.eval_static();
        if let Some(rhs) = rhs.as_imm() {
            Expr::Imm(!rhs)
        } else {
            Expr::TypeOp(Box::new(Bool::Not(Not { rhs })))
        }
    }
}

impl StaticEval for Neg {
    type Output = Expr<Float>;
    fn eval_static(&self) -> Expr<Float>
    where
        Self: Sized,
    {
        let rhs = self.rhs.eval_static();
        if let Some(rhs) = rhs.as_imm() {
            Expr::Imm(-rhs)
        } else {
            Expr::TypeOp(Box::new(Float::Neg(Neg { rhs })))
        }
    }
}

impl StaticEval for And {
    type Output = Expr<Bool>;
    fn eval_static(&self) -> Expr<Bool>
    where
        Self: Sized,
    {
        let lhs = self.lhs.eval_static();
        let rhs = self.rhs.eval_static();
        if let (Some(lhs), Some(rhs)) = (lhs.as_imm(), rhs.as_imm()) {
            Expr::Imm(lhs && rhs)
        } else {
            Expr::TypeOp(Box::new(Bool::And(And { lhs, rhs })))
        }
    }
}

impl StaticEval for Xor {
    type Output = Expr<Bool>;
    fn eval_static(&self) -> Expr<Bool>
    where
        Self: Sized,
    {
        let lhs = self.lhs.eval_static();
        let rhs = self.rhs.eval_static();
        if let (Some(lhs), Some(rhs)) = (lhs.as_imm(), rhs.as_imm()) {
            Expr::Imm(lhs ^ rhs)
        } else {
            Expr::TypeOp(Box::new(Bool::Xor(Xor { lhs, rhs })))
        }
    }
}

impl StaticEval for Or {
    type Output = Expr<Bool>;
    fn eval_static(&self) -> Expr<Bool>
    where
        Self: Sized,
    {
        let lhs = self.lhs.eval_static();
        let rhs = self.rhs.eval_static();
        if let (Some(lhs), Some(rhs)) = (lhs.as_imm(), rhs.as_imm()) {
            Expr::Imm(lhs ^ rhs)
        } else {
            Expr::TypeOp(Box::new(Bool::Or(Or { lhs, rhs })))
        }
    }
}

impl StaticEval for Greater {
    type Output = Expr<Bool>;
    fn eval_static(&self) -> Expr<Bool>
    where
        Self: Sized,
    {
        let lhs = self.lhs.eval_static();
        let rhs = self.rhs.eval_static();
        if let (Some(lhs), Some(rhs)) = (lhs.as_imm(), rhs.as_imm()) {
            Expr::Imm(lhs > rhs)
        } else {
            Expr::TypeOp(Box::new(Bool::Greater(Greater { lhs, rhs })))
        }
    }
}

impl StaticEval for Less {
    type Output = Expr<Bool>;
    fn eval_static(&self) -> Expr<Bool>
    where
        Self: Sized,
    {
        let lhs = self.lhs.eval_static();
        let rhs = self.rhs.eval_static();
        if let (Some(lhs), Some(rhs)) = (lhs.as_imm(), rhs.as_imm()) {
            Expr::Imm(lhs < rhs)
        } else {
            Expr::TypeOp(Box::new(Bool::Less(Less { lhs, rhs })))
        }
    }
}

impl StaticEval for Mul {
    type Output = Expr<Float>;
    fn eval_static(&self) -> Expr<Float>
    where
        Self: Sized,
    {
        let lhs = self.lhs.eval_static();
        let rhs = self.rhs.eval_static();
        if let (Some(lhs), Some(rhs)) = (lhs.as_imm(), rhs.as_imm()) {
            Expr::Imm(lhs * rhs)
        } else {
            Expr::TypeOp(Box::new(Float::Mul(Mul { lhs, rhs })))
        }
    }
}

impl StaticEval for Div {
    type Output = Expr<Float>;
    fn eval_static(&self) -> Expr<Float>
    where
        Self: Sized,
    {
        let lhs = self.lhs.eval_static();
        let rhs = self.rhs.eval_static();
        if let (Some(lhs), Some(rhs)) = (lhs.as_imm(), rhs.as_imm()) {
            Expr::Imm(lhs / rhs)
        } else {
            Expr::TypeOp(Box::new(Float::Div(Div { lhs, rhs })))
        }
    }
}

impl StaticEval for Add {
    type Output = Expr<Float>;
    fn eval_static(&self) -> Expr<Float>
    where
        Self: Sized,
    {
        let lhs = self.lhs.eval_static();
        let rhs = self.rhs.eval_static();
        if let (Some(lhs), Some(rhs)) = (lhs.as_imm(), rhs.as_imm()) {
            Expr::Imm(lhs + rhs)
        } else {
            Expr::TypeOp(Box::new(Float::Add(Add { lhs, rhs })))
        }
    }
}

impl StaticEval for Sub {
    type Output = Expr<Float>;
    fn eval_static(&self) -> Expr<Float>
    where
        Self: Sized,
    {
        let lhs = self.lhs.eval_static();
        let rhs = self.rhs.eval_static();
        if let (Some(lhs), Some(rhs)) = (lhs.as_imm(), rhs.as_imm()) {
            Expr::Imm(lhs - rhs)
        } else {
            Expr::TypeOp(Box::new(Float::Sub(Sub { lhs, rhs })))
        }
    }
}

impl StaticEval for Bool {
    type Output = Expr<Self>;
    fn eval_static(&self) -> Expr<Self> {
        match self {
            Bool::Not(op) => op.eval_static(),
            Bool::And(op) => op.eval_static(),
            Bool::Xor(op) => op.eval_static(),
            Bool::Or(op) => op.eval_static(),
            Bool::Greater(op) => op.eval_static(),
            Bool::Less(op) => op.eval_static(),
        }
    }
}

impl StaticEval for Color {
    type Output = Expr<Self>;
    fn eval_static(&self) -> Expr<Self> {
        match *self {}
    }
}

impl StaticEval for Float {
    type Output = Expr<Self>;
    fn eval_static(&self) -> Expr<Self> {
        match self {
            Float::Variable(_) => Expr::TypeOp(Box::new(self.clone())),
            Float::Neg(op) => op.eval_static(),
            Float::Mul(op) => op.eval_static(),
            Float::Div(op) => op.eval_static(),
            Float::Add(op) => op.eval_static(),
            Float::Sub(op) => op.eval_static(),
        }
    }
}

impl<Output> StaticEval for Expr<Output>
where
    Output: Type + StaticEval<Output = Self> + Clone,
    <Output as Type>::Cond: Type<Repr = bool>,
    <Output as Type>::Cond: Type<Cond = <Output as Type>::Cond>,
    <Output as Type>::Cond: StaticEval<Output = Expr<<Output as Type>::Cond>>,
{
    type Output = Self;
    fn eval_static(&self) -> Self {
        match self {
            Expr::Imm(_) => self.clone(),
            Expr::TypeOp(op) => op.as_ref().eval_static(),
            Expr::IfThenElse(if_then_else) => {
                let cond = if_then_else.cond.eval_static();
                let if_true = if_then_else.if_true.eval_static();
                let if_false = if_then_else.if_false.eval_static();
                if let Some(cond) = cond.as_imm() {
                    if cond {
                        if_true
                    } else {
                        if_false
                    }
                } else {
                    Expr::IfThenElse(Box::new(IfThenElse {
                        cond,
                        if_true,
                        if_false,
                    }))
                }
            }
            Expr::Ref(ref def) => {
                let tmp = RefCell::new(Expr::Imm(Default::default()));
                def.inner.inner.swap(&tmp);
                let expr = tmp.into_inner().eval_static();
                def.inner.inner.replace(expr.clone());
                if expr.as_imm().is_some() {
                    expr
                } else {
                    self.clone()
                }
            }
        }
    }
}
