mod bremm;
mod generate;
mod partition;
mod render;

use std::fs::File;
use std::io::BufWriter;
use std::path::PathBuf;
use std::time::SystemTime;
use std::time::UNIX_EPOCH;

use clap::Parser;

use crate::generate::Generator;
use crate::render::Renderer;
use crate::partition::Partition;

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

    /// How much elevation is affected by position in y-axis
    #[clap(long, default_value_t = 0.5)]
    slope: f64,

    /// Elevation partition boundaries (colon-separated list of values between 0.0 and 1.0)
    #[clap(long, default_value = "0.375:0.625")]
    elevation: Partition,

    /// Humidity partition boundaries (colon-separated list of values between 0.0 and 1.0)
    #[clap(long, default_value = "0.375:0.625")]
    humidity: Partition,

    /// Temperature partition boundaries (colon-separated list of values between 0.0 and 1.0)
    #[clap(long, default_value = "0.375:0.625")]
    temperature: Partition,
}

fn main() {
    let cli = Cli::parse();

    let file = File::create(cli.outfile).unwrap();
    let ref mut w = BufWriter::new(file);

    let renderer = Renderer::new()
        .elevation_partition(Some(cli.elevation.clone()))
        .humidity_partition(Some(cli.humidity.clone()))
        .temperature_partition(Some(cli.temperature.clone()));

    let generator = Generator::new().slope(cli.slope);

    let seed = if cli.seed == 0 {
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos() as u32
    } else {
        cli.seed
    };
    println!("seed: {seed}");

    let cells = generator.generate(cli.width, cli.height, seed);
    let image = renderer.render(&cells);

    let mut encoder = png::Encoder::new(w, cli.width as u32, cli.height as u32);
    encoder.set_color(png::ColorType::Rgb);
    let mut writer = encoder.write_header().unwrap();
    writer.write_image_data(&image).unwrap();
}
