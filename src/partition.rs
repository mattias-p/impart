#[derive(Clone)]
pub struct Partition {
    classes: Vec<(f32, f32)>,
    default: f32,
}

impl Partition {
    pub fn from_boundaries(boundaries: &[f32]) -> Self {
        let mut classes = Vec::with_capacity(boundaries.len() + 1);
        let mut prev = 0.0;
        for boundary in boundaries {
            let canonical = (boundary + prev) / 2.0;
            classes.push((*boundary, canonical));
            prev = *boundary
        }
        Partition {
            classes,
            default: (1.0 + prev) / 2.0,
        }
    }

    pub fn project(&self, input: f32) -> f32 {
        for (ubound, canonical) in &self.classes {
            if input <= *ubound {
                return *canonical;
            }
        }
        self.default
    }
}
