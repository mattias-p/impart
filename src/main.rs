mod expr;
mod generate;
mod render;

use std::fs::File;
use std::io::BufWriter;
use std::io::Read;
use std::path::PathBuf;
use std::time::SystemTime;
use std::time::UNIX_EPOCH;

use clap::Parser;
use noise::Fbm;

use crate::expr::Expr;
use crate::expr::Lexer;
use crate::generate::Generator;
use crate::render::Renderer;

#[derive(Parser)]
#[clap(version, about)]
struct Cli {
    /// Output file
    #[clap(short, long, default_value = "out.png")]
    outfile: PathBuf,

    /// Expression file
    #[clap(short, long)]
    exprfile: Option<PathBuf>,

    /// Width in modules (x-coordinates)
    #[clap(short, long, default_value_t = 256)]
    width: u16,

    /// Height in modules (z-coordinates)
    #[clap(short, long, default_value_t = 256)]
    height: u16,

    /// Random seed (0 means pseudo-random)
    #[clap(short, long, default_value_t = 0)]
    seed: u32,

    /// Fraction of elevation taken from y-coordinate
    #[clap(long, default_value_t = 0.475)]
    slope: f64,

    /// Elevation noise octave count
    #[clap(long, default_value_t = Fbm::DEFAULT_OCTAVE_COUNT)]
    elevation_octaves: usize,

    /// Elevation noise frequency
    #[clap(long, default_value_t = Fbm::DEFAULT_FREQUENCY)]
    elevation_frequency: f64,

    /// Elevation noise persistence
    #[clap(long, default_value_t = Fbm::DEFAULT_PERSISTENCE)]
    elevation_persistence: f64,

    /// Noise octave count used for temperature and humidity
    #[clap(long, default_value_t = Fbm::DEFAULT_OCTAVE_COUNT)]
    climate_octaves: usize,

    /// Noise frequency used for temperature and humidity
    #[clap(long, default_value_t = Fbm::DEFAULT_FREQUENCY)]
    climate_frequency: f64,

    /// Noise persistence used for temperature and humidity
    #[clap(long, default_value_t = Fbm::DEFAULT_PERSISTENCE)]
    climate_persistence: f64,
}

fn main() {
    let cli = Cli::parse();

    let file = File::create(cli.outfile).unwrap();
    let ref mut w = BufWriter::new(file);

    let mut buffer = Vec::new();
    let expr = if let Some(exprfile) = cli.exprfile {
        let mut f = File::open(exprfile).unwrap();
        f.read_to_end(&mut buffer).unwrap();
        buffer.as_slice()
    } else {
        include_bytes!("default.expr")
    };
    let mut lexer = Lexer::new(expr);
    let expr = Expr::parse(&mut lexer).unwrap();

    let renderer = Renderer::new(expr);

    let generator = Generator::new()
        .set_slope(cli.slope)
        .set_elevation_octaves(cli.elevation_octaves)
        .set_elevation_frequency(cli.elevation_frequency)
        .set_elevation_persistence(cli.elevation_persistence)
        .set_climate_octaves(cli.climate_octaves)
        .set_climate_frequency(cli.climate_frequency)
        .set_climate_persistence(cli.climate_persistence);

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
