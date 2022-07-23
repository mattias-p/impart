mod bremm;

use std::fs::File;
use std::io::BufWriter;
use std::path::PathBuf;

use clap::Parser;
use noise::Fbm;
use noise::NoiseFn;
use noise::Seedable;

use crate::bremm::BREMM;

#[derive(Parser)]
#[clap(version, about)]
struct Cli {
    /// Width in modules (x-coordinates)
    #[clap(short, long, default_value_t = 256)]
    width: u16,

    /// Height in modules (z-coordinates)
    #[clap(short, long, default_value_t = 256)]
    height: u16,

    /// Random seed
    #[clap(short, long, default_value_t = 0)]
    seed: u32,

    /// Output file
    #[clap(short, long, default_value = "out.png")]
    outfile: PathBuf,
}

fn main() {
    let cli = Cli::parse();

    let file = File::create(cli.outfile).unwrap();
    let ref mut w = BufWriter::new(file);

    let elevation = Fbm::new().set_seed(cli.seed);
    let humidity = Fbm::new().set_seed(cli.seed + 1);
    let temperature = Fbm::new().set_seed(cli.seed + 2);

    let mut data: Vec<u8> = Vec::with_capacity(cli.width as usize * cli.height as usize * 3);

    let step_x = 1.0 / (cli.width - 1) as f64;
    let step_y = 1.0 / (cli.height - 1) as f64;
    let mut y = 0.0;
    for _ in 0..cli.height {
        let mut x = 0.0;
        for _ in 0..cli.width {
            let e = 0.75 + 0.25 * elevation.get([x, y]) - 0.5 * y;
            let h = 0.5 - 0.5 * humidity.get([x, y]);
            let t = 0.5 - 0.5 * temperature.get([x, y]);
            data.extend(BREMM.get_pixel(h as f32, t as f32, e as f32).into_iter());

            x += step_x;
        }
        y += step_y;
    }

    let mut encoder = png::Encoder::new(w, cli.width as u32, cli.height as u32);
    encoder.set_color(png::ColorType::Rgb);
    let mut writer = encoder.write_header().unwrap();
    writer.write_image_data(&data).unwrap();
}
