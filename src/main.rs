mod bremm;

use std::fs::File;
use std::io::BufWriter;
use std::path::PathBuf;
use std::time::SystemTime;
use std::time::UNIX_EPOCH;

use clap::Parser;
use noise::Fbm;
use noise::NoiseFn;
use noise::Seedable;

use crate::bremm::BREMM;

#[derive(Parser)]
#[clap(version, about)]
struct Cli {
    /// Output file
    #[clap(short, long, default_value = "out.png")]
    outfile: PathBuf,

    /// Width in modules (x-coordinates)
    #[clap(short, long, default_value_t = 256)]
    width: u16,

    /// Height in modules (z-coordinates)
    #[clap(short, long, default_value_t = 256)]
    height: u16,

    /// Random seed (0 means pseudo-random)
    #[clap(short, long, default_value_t = 0)]
    seed: u32,
}

fn main() {
    let cli = Cli::parse();

    let file = File::create(cli.outfile).unwrap();
    let ref mut w = BufWriter::new(file);

    let seed = if cli.seed == 0 {
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos() as u32
    } else {
        cli.seed
    };
    println!("seed: {seed}");

    let image = generate(cli.width, cli.height, seed);

    let mut encoder = png::Encoder::new(w, cli.width as u32, cli.height as u32);
    encoder.set_color(png::ColorType::Rgb);
    let mut writer = encoder.write_header().unwrap();
    writer.write_image_data(&image).unwrap();
}

fn generate(width: u16, height: u16, seed: u32) -> Vec<u8> {
    let elevation = Fbm::new().set_seed(seed);
    let humidity = Fbm::new().set_seed(seed + 1);
    let temperature = Fbm::new().set_seed(seed + 2);

    let mut image: Vec<u8> = Vec::with_capacity(width as usize * height as usize * 3);

    let step_x = 1.0 / (width - 1) as f64;
    let step_y = 1.0 / (height - 1) as f64;
    let mut y = 0.0;
    for _ in 0..height {
        let mut x = 0.0;
        for _ in 0..width {
            let e = 0.75 + 0.25 * elevation.get([x, y]) - 0.5 * y;
            let h = 0.5 - 0.5 * humidity.get([x, y]);
            let t = 0.5 - 0.5 * temperature.get([x, y]);
            image.extend(BREMM.get_pixel(h as f32, t as f32, e as f32).into_iter());

            x += step_x;
        }
        y += step_y;
    }

    image
}
