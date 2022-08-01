mod ast;
mod generate;
mod ir;
mod lexer;
mod render;
mod stats;

use std::fs::File;
use std::io::BufWriter;
use std::io::Read;
use std::io::Write;
use std::path::PathBuf;
use std::time::SystemTime;
use std::time::UNIX_EPOCH;

use anyhow::Context;
use clap::Parser;

use crate::generate::Generator;
use crate::render::Renderer;
use crate::stats::Stats;

#[derive(Parser)]
#[clap(version, about)]
struct Cli {
    /// Output file
    #[clap(short, long, default_value = "out.png")]
    outfile: PathBuf,

    /// Source file
    #[clap(short = 'c', long)]
    sourcefile: Option<PathBuf>,

    /// Width in modules (x-coordinates)
    #[clap(short, long, default_value_t = 256)]
    width: u16,

    /// Height in modules (z-coordinates)
    #[clap(short, long, default_value_t = 256)]
    height: u16,

    /// Random seed (0 means pseudo-random)
    #[clap(short, long, default_value_t = 0)]
    seed: u32,

    /// Dump the source
    #[clap(long, action)]
    dump_source: bool,

    /// Dump some statistics
    #[clap(long, action)]
    dump_stats: bool,
}

fn main() -> anyhow::Result<()> {
    let cli = Cli::parse();

    let mut buffer = Vec::new();
    let source = if let Some(ref sourcefile) = cli.sourcefile {
        let mut f = File::open(sourcefile).context("Failed to open source file")?;
        f.read_to_end(&mut buffer)
            .context("Failed to read source file")?;
        buffer.as_slice()
    } else {
        include_bytes!("default.sbf")
    };

    let file = File::create(&cli.outfile).context("Failed to open out file")?;
    let ref mut w = BufWriter::new(file);

    let (prog, var_specs) = ir::parse_source(&source)
        .map_err(anyhow::Error::msg)
        .context("Failed to parse source")?;

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

    println!("// seed: {seed}");
    if cli.dump_source {
        std::io::stdout()
            .write(&source)
            .context("Failed to write to stdout")?;
    }

    let cells = generator.generate(cli.width, cli.height, seed);
    let image = renderer.render(&cells);
    if cli.dump_stats {
        let report = stats.report(&cells);
        print!("{}", report);
    }

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
