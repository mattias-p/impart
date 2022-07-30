use noise::Fbm;
use noise::MultiFractal;
use noise::NoiseFn;
use noise::Seedable;

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum VarSpec {
    Elevation,
    Humidity,
    Temperature,
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
    pub vars: Vec<f32>,
}

pub struct Generator {
    slope: f64,
    elevation_octaves: usize,
    elevation_frequency: f64,
    elevation_persistence: f64,
    climate_octaves: usize,
    climate_frequency: f64,
    climate_persistence: f64,
}

impl Generator {
    pub fn new(_vars: Vec<VarSpec>) -> Self {
        Generator {
            slope: 0.5,
            elevation_octaves: Fbm::DEFAULT_OCTAVE_COUNT,
            elevation_frequency: Fbm::DEFAULT_FREQUENCY,
            elevation_persistence: Fbm::DEFAULT_PERSISTENCE,
            climate_octaves: Fbm::DEFAULT_OCTAVE_COUNT,
            climate_frequency: Fbm::DEFAULT_FREQUENCY,
            climate_persistence: Fbm::DEFAULT_PERSISTENCE,
        }
    }

    pub fn set_slope(mut self, value: f64) -> Self {
        self.slope = value;
        self
    }

    pub fn set_elevation_octaves(mut self, value: usize) -> Self {
        self.elevation_octaves = value;
        self
    }

    pub fn set_elevation_frequency(mut self, value: f64) -> Self {
        self.elevation_frequency = value;
        self
    }

    pub fn set_elevation_persistence(mut self, value: f64) -> Self {
        self.elevation_persistence = value;
        self
    }

    pub fn set_climate_octaves(mut self, value: usize) -> Self {
        self.climate_octaves = value;
        self
    }

    pub fn set_climate_frequency(mut self, value: f64) -> Self {
        self.climate_frequency = value;
        self
    }

    pub fn set_climate_persistence(mut self, value: f64) -> Self {
        self.climate_persistence = value;
        self
    }

    pub fn generate(&self, width: u16, height: u16, seed: u32) -> Vec<Cell> {
        let elevation_noise = Fbm::new()
            .set_seed(seed + 0)
            .set_octaves(self.elevation_octaves)
            .set_frequency(self.elevation_frequency)
            .set_persistence(self.elevation_persistence);
        let humidity_noise = Fbm::new()
            .set_seed(seed + 1)
            .set_octaves(self.climate_octaves)
            .set_frequency(self.climate_frequency)
            .set_persistence(self.climate_persistence);
        let temperature_noise = Fbm::new()
            .set_seed(seed + 2)
            .set_octaves(self.climate_octaves)
            .set_frequency(self.climate_frequency)
            .set_persistence(self.climate_persistence);

        let mut cells = Vec::with_capacity(width as usize * height as usize);

        let step_x = 1.0 / (width - 1) as f64;
        let step_y = 1.0 / (height - 1) as f64;
        let mut y = 0.0;
        for _ in 0..height {
            let mut x = 0.0;
            for _ in 0..width {
                let elevation = ((0.5 + self.slope / 2.0)
                    + (0.5 - self.slope / 2.0) * elevation_noise.get([x, y])
                    - self.slope * y) as f32;
                let humidity = (0.5 + 0.5 * humidity_noise.get([x, y])) as f32;
                let temperature = (0.5 + 0.5 * temperature_noise.get([x, y])) as f32;

                cells.push(Cell {
                    vars: vec![elevation, humidity, temperature],
                });

                x += step_x;
            }
            y += step_y;
        }
        cells
    }
}
