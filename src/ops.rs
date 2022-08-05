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

    fn eval_static(self) -> Expr<Self::Output>;
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
    fn eval_static(self) -> Expr<Self::Output>
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

impl Not {
    pub fn new(rhs: Expr<Bool>) -> Bool {
        Bool::Not(Not { rhs })
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Neg {
    rhs: Expr<Float>,
}

impl Operator for Neg {
    type Output = Float;
    fn eval_cell(&self, cell: &Cell) -> f32 {
        -self.rhs.eval_cell(cell)
    }
    fn eval_static(self) -> Expr<Self::Output>
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

impl Neg {
    pub fn new(rhs: Expr<Float>) -> Float {
        Float::Neg(Neg { rhs })
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct And {
    lhs: Expr<Bool>,
    rhs: Expr<Bool>,
}

impl Operator for And {
    type Output = Bool;
    fn eval_cell(&self, cell: &Cell) -> bool {
        self.lhs.eval_cell(cell) && self.rhs.eval_cell(cell)
    }
    fn eval_static(self) -> Expr<Self::Output>
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

impl And {
    pub fn new(lhs: Expr<Bool>, rhs: Expr<Bool>) -> Bool {
        Bool::And(And { lhs, rhs })
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Xor {
    lhs: Expr<Bool>,
    rhs: Expr<Bool>,
}

impl Operator for Xor {
    type Output = Bool;
    fn eval_cell(&self, cell: &Cell) -> bool {
        self.lhs.eval_cell(cell) ^ self.rhs.eval_cell(cell)
    }
    fn eval_static(self) -> Expr<Self::Output>
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

impl Xor {
    pub fn new(lhs: Expr<Bool>, rhs: Expr<Bool>) -> Bool {
        Bool::Xor(Xor { lhs, rhs })
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Or {
    lhs: Expr<Bool>,
    rhs: Expr<Bool>,
}

impl Operator for Or {
    type Output = Bool;
    fn eval_cell(&self, cell: &Cell) -> bool {
        self.lhs.eval_cell(cell) ^ self.rhs.eval_cell(cell)
    }
    fn eval_static(self) -> Expr<Self::Output>
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

impl Or {
    pub fn new(lhs: Expr<Bool>, rhs: Expr<Bool>) -> Bool {
        Bool::Or(Or { lhs, rhs })
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Greater {
    lhs: Expr<Float>,
    rhs: Expr<Float>,
}

impl Operator for Greater {
    type Output = Bool;
    fn eval_cell(&self, cell: &Cell) -> bool {
        self.lhs.eval_cell(cell) > self.rhs.eval_cell(cell)
    }
    fn eval_static(self) -> Expr<Self::Output>
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

impl Greater {
    pub fn new(lhs: Expr<Float>, rhs: Expr<Float>) -> Bool {
        Bool::Greater(Greater { lhs, rhs })
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Less {
    lhs: Expr<Float>,
    rhs: Expr<Float>,
}

impl Operator for Less {
    type Output = Bool;
    fn eval_cell(&self, cell: &Cell) -> bool {
        self.lhs.eval_cell(cell) < self.rhs.eval_cell(cell)
    }
    fn eval_static(self) -> Expr<Self::Output>
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

impl Less {
    pub fn new(lhs: Expr<Float>, rhs: Expr<Float>) -> Bool {
        Bool::Less(Less { lhs, rhs })
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Mul {
    lhs: Expr<Float>,
    rhs: Expr<Float>,
}

impl Operator for Mul {
    type Output = Float;
    fn eval_cell(&self, cell: &Cell) -> f32 {
        self.lhs.eval_cell(cell) * self.rhs.eval_cell(cell)
    }
    fn eval_static(self) -> Expr<Self::Output>
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

impl Mul {
    pub fn new(lhs: Expr<Float>, rhs: Expr<Float>) -> Float {
        Float::Mul(Mul { lhs, rhs })
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Div {
    lhs: Expr<Float>,
    rhs: Expr<Float>,
}

impl Operator for Div {
    type Output = Float;
    fn eval_cell(&self, cell: &Cell) -> f32 {
        self.lhs.eval_cell(cell) / self.rhs.eval_cell(cell)
    }
    fn eval_static(self) -> Expr<Self::Output>
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

impl Div {
    pub fn new(lhs: Expr<Float>, rhs: Expr<Float>) -> Float {
        Float::Div(Div { lhs, rhs })
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Add {
    lhs: Expr<Float>,
    rhs: Expr<Float>,
}

impl Operator for Add {
    type Output = Float;
    fn eval_cell(&self, cell: &Cell) -> f32 {
        self.lhs.eval_cell(cell) + self.rhs.eval_cell(cell)
    }
    fn eval_static(self) -> Expr<Self::Output>
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

impl Add {
    pub fn new(lhs: Expr<Float>, rhs: Expr<Float>) -> Float {
        Float::Add(Add { lhs, rhs })
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Sub {
    lhs: Expr<Float>,
    rhs: Expr<Float>,
}

impl Operator for Sub {
    type Output = Float;
    fn eval_cell(&self, cell: &Cell) -> f32 {
        self.lhs.eval_cell(cell) - self.rhs.eval_cell(cell)
    }
    fn eval_static(self) -> Expr<Self::Output>
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
    fn eval_static(self) -> Expr<Self> {
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

#[derive(Clone, Debug, PartialEq)]
pub enum Color {}
impl Type for Color {
    type Repr = Srgb<u8>;
    type Cond = Bool;
    fn eval_cell(&self, _cell: &Cell) -> Self::Repr {
        unreachable!("Color does not have any operators");
    }
    fn eval_static(self) -> Expr<Self> {
        unreachable!("Color does not have any operators");
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
    fn eval_static(self) -> Expr<Self> {
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
