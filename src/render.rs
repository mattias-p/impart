use palette::Pixel;

use crate::expr::Expr;
use crate::generate::Cell;

pub struct Renderer {
    expr: Expr,
}

impl Renderer {
    pub fn new(expr: Expr) -> Self {
        Renderer { expr }
    }

    pub fn render(&self, cells: &[Cell]) -> Vec<u8> {
        let mut image: Vec<u8> = Vec::with_capacity(cells.len() * 3);

        for cell in cells {
            let color = self.expr.eval(*cell);

            image.extend(color.color().into_raw::<[u8; 3]>().into_iter());
        }

        image
    }
}
