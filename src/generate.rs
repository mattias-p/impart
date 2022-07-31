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

/// A Cell describes geographic location
pub struct Cell {
    /// Variables in the range 0.0 - 1.0 inclusive
    vars: Vec<f32>,
}

impl Cell {
    pub fn get(&self, id: VarId) -> f32 {
        self.vars[id.index]
    }
    pub fn into_vec(self) -> Vec<f32> {
        self.vars
    }
}

pub struct Generator {
    vars: Vec<VarSpec>,
}

pub enum Variable {
    Perlin(Fbm),
    X,
    Y,
}

impl Variable {
    fn eval(&self, x: f64, y: f64) -> f32 {
        match self {
            Variable::Perlin(fbm) => fbm.get([x, y]) as f32,
            Variable::X => x as f32,
            Variable::Y => y as f32,
        }
    }
}

impl Generator {
    pub fn new(vars: Vec<VarSpec>) -> Self {
        Generator { vars }
    }

    pub fn generate(&self, width: u16, height: u16, seed: u32) -> Vec<Cell> {
        let mut noises = vec![];

        noises.extend(self.vars.iter().enumerate().map(|(i, spec)| {
            match spec {
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
            }
        }));

        let mut cells = Vec::with_capacity(width as usize * height as usize);

        let step_x = 2.0 / (width - 1) as f64;
        let step_y = 2.0 / (height - 1) as f64;
        let mut y = 1.0;
        for _ in 0..height {
            let mut x = -1.0;
            for _ in 0..width {
                let vars = noises.iter().map(|noise| noise.eval(x, y)).collect();
                cells.push(Cell { vars });

                x += step_x;
            }
            y -= step_y;
        }
        cells
    }
}
