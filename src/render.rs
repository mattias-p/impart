use palette::Pixel;

use crate::expr::Expr;
use crate::expr::Immediate;
use crate::expr::Variable;
use crate::generate::Cell;

pub struct Renderer {
    expr: Expr<Variable>,
}

impl Renderer {
    pub fn new(expr: Expr<Variable>) -> Self {
        Renderer { expr }
    }

    pub fn render(&self, cells: &[Cell]) -> Vec<u8> {
        let mut image: Vec<u8> = Vec::with_capacity(cells.len() * 3);

        for cell in cells {
            match self.expr.eval(*cell) {
                Immediate::Color(color) => image.extend(color.into_raw::<[u8; 3]>().into_iter()),
                imm => panic!("expected color got {imm:?}"),
            }
        }

        image
    }
}
