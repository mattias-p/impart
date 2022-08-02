use noise::Fbm;
use noise::MultiFractal;
use noise::NoiseFn;
use noise::Seedable;

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct VarId {
    index: usize,
}
impl VarId {
    pub fn new(index: usize) -> Self {
        VarId { index }
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum VarSpec {
    X,
    Y,
    Perlin {
        octaves: usize,
        frequency: f32,
        persistence: f32,
    },
}

pub enum Variable {
    Perlin(Fbm),
    X,
    Y,
}

impl Variable {
    fn eval(&self, x: f64, y: f64) -> f32 {
        match self {
            Variable::Perlin(fbm) => {
                let value = fbm.get([x, y]);
                value.abs().sqrt().copysign(value) as f32
            }
            Variable::X => x as f32,
            Variable::Y => y as f32,
        }
    }
}

/// A Cell describes geographic location
pub struct Cell {
    /// Variables in the range 0.0 - 1.0 inclusive
    pub values: Vec<f32>,
}

impl Cell {
    pub fn get(&self, id: VarId) -> f32 {
        self.values[id.index]
    }
    pub fn as_slice(&self) -> &[f32] {
        &self.values
    }
}

pub struct Generator {
    var_specs: Vec<VarSpec>,
}

impl Generator {
    pub fn new(var_specs: Vec<VarSpec>) -> Self {
        Generator { var_specs }
    }

    pub fn generate(&self, width: u16, height: u16, seed: u32) -> Vec<Cell> {
        let vars: Vec<_> = self
            .var_specs
            .iter()
            .enumerate()
            .map(|(i, spec)| match spec {
                VarSpec::X => Variable::X,
                VarSpec::Y => Variable::Y,
                VarSpec::Perlin {
                    octaves,
                    frequency,
                    persistence,
                } => Variable::Perlin(
                    Fbm::new()
                        .set_seed(seed + i as u32)
                        .set_octaves(*octaves)
                        .set_frequency(*frequency as f64)
                        .set_persistence(*persistence as f64),
                ),
            })
            .collect();

        let num_cells = width as usize * height as usize;
        let mut axes: Vec<_> = self
            .var_specs
            .iter()
            .map(|_| Vec::with_capacity(num_cells))
            .collect();

        let step_x = 2.0 / (width - 1) as f64;
        let step_y = 2.0 / (height - 1) as f64;
        let mut y = 1.0;
        for _ in 0..height {
            let mut x = -1.0;
            for _ in 0..width {
                for (axis, var) in axes.iter_mut().zip(vars.iter()) {
                    axis.push(var.eval(x, y));
                }
                x += step_x;
            }
            y -= step_y;
        }

        let mut cells = Vec::with_capacity(num_cells);
        for i in 0..num_cells {
            let mut values = Vec::with_capacity(self.var_specs.len());
            for axis in &axes {
                values.push(axis[i]);
            }
            cells.push(Cell { values });
        }

        cells
    }
}
