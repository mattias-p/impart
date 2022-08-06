use std::fmt;

use std::cell::RefCell;
use std::rc::Rc;

use crate::generate::Cell;
use crate::lexer::Loc;

pub trait Type
where
    Self: Clone + fmt::Debug + PartialEq,
{
    type Repr: Clone + Copy + fmt::Debug + Default + PartialEq;
    type Cond: Type<Repr = bool, Cond = Self::Cond>;
    fn eval_cell(&self, cell: &Cell) -> Self::Repr;
}

#[derive(Clone, Debug, PartialEq)]
pub struct LetIn<Output>
where
    Output: Type + Clone,
    <Output as Type>::Cond: Type<Repr = bool, Cond = <Output as Type>::Cond>,
{
    pub value: Loc<RefCell<Expr<Output>>>,
}

impl<Output> LetIn<Output>
where
    Output: Type + Clone,
    <Output as Type>::Cond: Type<Repr = bool, Cond = <Output as Type>::Cond>,
{
    pub fn eval_cell(&self, cell: &Cell) -> Output::Repr {
        self.value.inner.borrow().eval_cell(cell)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Expr<Output>
where
    Output: Type + Clone,
    <Output as Type>::Cond: Type<Repr = bool, Cond = <Output as Type>::Cond>,
{
    Imm(Output::Repr),
    TypeOp(Box<Output>),
    IfThenElse(Box<IfThenElse<Output>>),
    Ref(Rc<LetIn<Output>>),
}

impl<Output> Expr<Output>
where
    Output: Type + Clone,
    <Output as Type>::Cond: Type<Repr = bool, Cond = <Output as Type>::Cond>,
{
    pub fn as_imm(&self) -> Option<Output::Repr> {
        if let Expr::Imm(value) = self {
            Some(*value)
        } else {
            None
        }
    }

    pub fn eval_cell(&self, cell: &Cell) -> Output::Repr {
        match self {
            Expr::Imm(value) => *value,
            Expr::IfThenElse(if_then_else) => if_then_else.eval_cell(cell),
            Expr::TypeOp(op) => op.eval_cell(cell),
            Expr::Ref(let_in) => let_in.eval_cell(cell),
        }
    }

    pub fn error<S: AsRef<str>>(&self, message: S) -> String {
        let message = message.as_ref();
        match self {
            Expr::Ref(let_in) => format!(
                "{message} (defined at {}:{})",
                let_in.value.line, let_in.value.col
            ),
            _ => message.to_string(),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct IfThenElse<Output>
where
    Output: Type + Clone,
    <Output as Type>::Cond: Type<Repr = bool, Cond = <Output as Type>::Cond>,
{
    pub cond: Expr<<Output as Type>::Cond>,
    pub if_true: Expr<Output>,
    pub if_false: Expr<Output>,
}

impl<Output> IfThenElse<Output>
where
    Output: Type + Clone,
    <Output as Type>::Cond: Type<Repr = bool, Cond = <Output as Type>::Cond>,
{
    pub fn eval_cell(&self, cell: &Cell) -> <Output as Type>::Repr {
        if self.cond.eval_cell(cell) {
            self.if_true.eval_cell(cell)
        } else {
            self.if_false.eval_cell(cell)
        }
    }
}
