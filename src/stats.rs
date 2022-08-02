use std::fmt;

use crate::generate::Field;
use crate::generate::VarSpec;

pub struct Stats {
    var_specs: Vec<VarSpec>,
}

impl Stats {
    pub fn new(var_specs: Vec<VarSpec>) -> Self {
        Stats { var_specs }
    }
    pub fn report(&self, field: &Field) -> Report {
        let init: Vec<_> = self
            .var_specs
            .iter()
            .map(|spec| match spec {
                VarSpec::Perlin { .. } => Some(((1.0f32), (-1.0f32))),
                _ => None,
            })
            .collect();
        let ranges: Vec<Option<(f32, f32)>> = field.cells().fold(init, |ranges, cell| {
            ranges
                .into_iter()
                .zip(cell.as_slice().iter())
                .map(|(range, value)| range.map(|(min, max)| (min.min(*value), max.max(*value))))
                .collect()
        });
        let (min_min, max_min) =
            ranges
                .iter()
                .fold((-1.0f32, 1.0f32), |(min_acc, max_acc), range| match range {
                    Some((min_val, max_val)) => (min_acc.max(*min_val), max_acc.min(*max_val)),
                    None => (min_acc, max_acc),
                });
        let (min_max, max_max) =
            ranges
                .iter()
                .fold((1.0f32, -1.0f32), |(min_acc, max_acc), range| match range {
                    Some((min_val, max_val)) => (min_acc.min(*min_val), max_acc.max(*max_val)),
                    None => (min_acc, max_acc),
                });

        Report {
            ranges,
            min: (min_min, max_min),
            max: (min_max, max_max),
        }
    }
}

pub struct Report {
    ranges: Vec<Option<(f32, f32)>>,
    min: (f32, f32),
    max: (f32, f32),
}

impl fmt::Display for Report {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "")?;
        for (min, max) in self.ranges.iter().flatten() {
            writeln!(f, "var range: [{:.6}; {:.6}] ({:.6})", min, max, max - min)?;
        }
        writeln!(f, "")?;
        writeln!(
            f,
            "min range: [{:.6}; {:.6}] ({:.6})",
            self.min.0,
            self.min.1,
            self.min.1 - self.min.0
        )?;
        writeln!(
            f,
            "max range: [{:.6}; {:.6}] ({:.6})",
            self.max.0,
            self.max.1,
            self.max.1 - self.max.0
        )
    }
}
