use std::fmt;

use palette::Srgb;

use crate::expr::Expr;
use crate::expr::Type;
use crate::generate::Cell;
use crate::generate::VarId;

pub enum TyKind {
    Bool,
    Float,
    Color,
}

impl fmt::Display for TyKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            TyKind::Bool => write!(f, "bool"),
            TyKind::Color => write!(f, "color"),
            TyKind::Float => write!(f, "float"),
        }
    }
}

pub trait Operator {
    type Output: Type;

    fn eval_cell(&self, cell: &Cell) -> <Self::Output as Type>::Repr;
}

#[derive(Clone, Debug, PartialEq)]
pub struct Not {
    pub rhs: Expr<Bool>,
}

impl Operator for Not {
    type Output = Bool;
    fn eval_cell(&self, cell: &Cell) -> bool {
        !self.rhs.eval_cell(cell)
    }
}

impl Not {
    pub fn new(rhs: Expr<Bool>) -> Bool {
        Bool::Not(Not { rhs })
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Neg {
    pub rhs: Expr<Float>,
}

impl Operator for Neg {
    type Output = Float;
    fn eval_cell(&self, cell: &Cell) -> f32 {
        -self.rhs.eval_cell(cell)
    }
}

impl Neg {
    pub fn new(rhs: Expr<Float>) -> Float {
        Float::Neg(Neg { rhs })
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct And {
    pub lhs: Expr<Bool>,
    pub rhs: Expr<Bool>,
}

impl Operator for And {
    type Output = Bool;
    fn eval_cell(&self, cell: &Cell) -> bool {
        self.lhs.eval_cell(cell) && self.rhs.eval_cell(cell)
    }
}

impl And {
    pub fn new(lhs: Expr<Bool>, rhs: Expr<Bool>) -> Bool {
        Bool::And(And { lhs, rhs })
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Xor {
    pub lhs: Expr<Bool>,
    pub rhs: Expr<Bool>,
}

impl Operator for Xor {
    type Output = Bool;
    fn eval_cell(&self, cell: &Cell) -> bool {
        self.lhs.eval_cell(cell) ^ self.rhs.eval_cell(cell)
    }
}

impl Xor {
    pub fn new(lhs: Expr<Bool>, rhs: Expr<Bool>) -> Bool {
        Bool::Xor(Xor { lhs, rhs })
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Or {
    pub lhs: Expr<Bool>,
    pub rhs: Expr<Bool>,
}

impl Operator for Or {
    type Output = Bool;
    fn eval_cell(&self, cell: &Cell) -> bool {
        self.lhs.eval_cell(cell) ^ self.rhs.eval_cell(cell)
    }
}

impl Or {
    pub fn new(lhs: Expr<Bool>, rhs: Expr<Bool>) -> Bool {
        Bool::Or(Or { lhs, rhs })
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Greater {
    pub lhs: Expr<Float>,
    pub rhs: Expr<Float>,
}

impl Operator for Greater {
    type Output = Bool;
    fn eval_cell(&self, cell: &Cell) -> bool {
        self.lhs.eval_cell(cell) > self.rhs.eval_cell(cell)
    }
}

impl Greater {
    pub fn new(lhs: Expr<Float>, rhs: Expr<Float>) -> Bool {
        Bool::Greater(Greater { lhs, rhs })
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Less {
    pub lhs: Expr<Float>,
    pub rhs: Expr<Float>,
}

impl Operator for Less {
    type Output = Bool;
    fn eval_cell(&self, cell: &Cell) -> bool {
        self.lhs.eval_cell(cell) < self.rhs.eval_cell(cell)
    }
}

impl Less {
    pub fn new(lhs: Expr<Float>, rhs: Expr<Float>) -> Bool {
        Bool::Less(Less { lhs, rhs })
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Mul {
    pub lhs: Expr<Float>,
    pub rhs: Expr<Float>,
}

impl Operator for Mul {
    type Output = Float;
    fn eval_cell(&self, cell: &Cell) -> f32 {
        self.lhs.eval_cell(cell) * self.rhs.eval_cell(cell)
    }
}

impl Mul {
    pub fn new(lhs: Expr<Float>, rhs: Expr<Float>) -> Float {
        Float::Mul(Mul { lhs, rhs })
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Div {
    pub lhs: Expr<Float>,
    pub rhs: Expr<Float>,
}

impl Operator for Div {
    type Output = Float;
    fn eval_cell(&self, cell: &Cell) -> f32 {
        self.lhs.eval_cell(cell) / self.rhs.eval_cell(cell)
    }
}

impl Div {
    pub fn new(lhs: Expr<Float>, rhs: Expr<Float>) -> Float {
        Float::Div(Div { lhs, rhs })
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Add {
    pub lhs: Expr<Float>,
    pub rhs: Expr<Float>,
}

impl Operator for Add {
    type Output = Float;
    fn eval_cell(&self, cell: &Cell) -> f32 {
        self.lhs.eval_cell(cell) + self.rhs.eval_cell(cell)
    }
}

impl Add {
    pub fn new(lhs: Expr<Float>, rhs: Expr<Float>) -> Float {
        Float::Add(Add { lhs, rhs })
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Sub {
    pub lhs: Expr<Float>,
    pub rhs: Expr<Float>,
}

impl Operator for Sub {
    type Output = Float;
    fn eval_cell(&self, cell: &Cell) -> f32 {
        self.lhs.eval_cell(cell) - self.rhs.eval_cell(cell)
    }
}

impl Sub {
    pub fn new(lhs: Expr<Float>, rhs: Expr<Float>) -> Float {
        Float::Sub(Sub { lhs, rhs })
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Bool {
    Not(Not),
    And(And),
    Xor(Xor),
    Or(Or),
    Greater(Greater),
    Less(Less),
}
impl Type for Bool {
    type Repr = bool;
    type Cond = Self;
    fn eval_cell(&self, cell: &Cell) -> Self::Repr {
        match self {
            Bool::Not(op) => op.eval_cell(cell),
            Bool::And(op) => op.eval_cell(cell),
            Bool::Xor(op) => op.eval_cell(cell),
            Bool::Or(op) => op.eval_cell(cell),
            Bool::Greater(op) => op.eval_cell(cell),
            Bool::Less(op) => op.eval_cell(cell),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Color {}
impl Type for Color {
    type Repr = Srgb<u8>;
    type Cond = Bool;
    fn eval_cell(&self, _cell: &Cell) -> Self::Repr {
        match *self {}
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Float {
    Variable(VarId),
    Neg(Neg),
    Mul(Mul),
    Div(Div),
    Add(Add),
    Sub(Sub),
}
impl Type for Float {
    type Repr = f32;
    type Cond = Bool;
    fn eval_cell(&self, cell: &Cell) -> Self::Repr {
        match self {
            Float::Variable(var) => cell.get(*var),
            Float::Neg(op) => op.eval_cell(cell),
            Float::Mul(op) => op.eval_cell(cell),
            Float::Div(op) => op.eval_cell(cell),
            Float::Add(op) => op.eval_cell(cell),
            Float::Sub(op) => op.eval_cell(cell),
        }
    }
}

#[derive(Clone, Debug)]
pub enum AnyExpr {
    Bool(Expr<Bool>),
    Color(Expr<Color>),
    Float(Expr<Float>),
}

impl AnyExpr {
    pub fn get_type(&self) -> TyKind {
        match self {
            AnyExpr::Bool(_) => TyKind::Bool,
            AnyExpr::Color(_) => TyKind::Color,
            AnyExpr::Float(_) => TyKind::Float,
        }
    }
}

impl From<Float> for AnyExpr {
    fn from(op: Float) -> Self {
        AnyExpr::Float(Expr::TypeOp(Box::new(op)))
    }
}

impl From<Bool> for AnyExpr {
    fn from(op: Bool) -> Self {
        AnyExpr::Bool(Expr::TypeOp(Box::new(op)))
    }
}
