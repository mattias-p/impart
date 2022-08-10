mod expr;
mod generate;
mod inline;
mod lexer;
mod ops;
mod parser;
mod render;
mod static_eval;
mod stats;
mod typeck;

use std::fs::File;
use std::io::BufWriter;
use std::io::Read;
use std::path::PathBuf;
use std::time::SystemTime;
use std::time::UNIX_EPOCH;

use anyhow::Context;
use clap::Parser;

use crate::generate::Generator;
use crate::inline::Inline;
use crate::render::Renderer;
use crate::static_eval::StaticEval;
use crate::stats::Stats;

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

    /// Dump some statistics
    #[clap(long, action)]
    dump_stats: bool,

    /// Script file
    script: PathBuf,
}

fn main() -> anyhow::Result<()> {
    let cli = Cli::parse();

    let mut source = Vec::new();
    let mut f = File::open(cli.script).context("Failed to open script file")?;
    f.read_to_end(&mut source)
        .context("Failed to read script file")?;

    let file = File::create(&cli.outfile).context("Failed to open out file")?;
    let w = &mut BufWriter::new(file);

    let (prog, var_specs) = typeck::parse_source(&source)
        .map_err(anyhow::Error::msg)
        .context("Failed to parse source")?;
    let prog = prog.eval_static();
    let prog = prog.inline();

    let generator = Generator::new(var_specs.clone());
    let stats = Stats::new(var_specs);
    let renderer = Renderer::new(prog);

    let seed = if cli.seed == 0 {
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .context("Failed to calculate Unix time")?
            .as_nanos() as u32
    } else {
        cli.seed
    };

    println!("seed: {seed}");
    let cells = generator.generate(cli.width, cli.height, seed);
    if cli.dump_stats {
        let report = stats.report(&cells);
        print!("{}", report);
    }

    let image = renderer.render(&cells);
    let mut encoder = png::Encoder::new(w, cli.width as u32, cli.height as u32);
    encoder.set_color(png::ColorType::Rgb);
    let mut writer = encoder
        .write_header()
        .context("Failed to write out file header")?;
    writer
        .write_image_data(&image)
        .context("Failed to write out file contents")?;

    Ok(())
}
