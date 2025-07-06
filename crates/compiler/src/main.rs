use std::path::PathBuf;

use capyc::{
    ast::{collect_errors_and_report, Datum, DatumValue}, expand::{pass1, Cenv}, fix_letrec::pass_fix_letrec, graph::CPS, number::Number, parser::TreeSitter, primitives::resolve_primitives, source::*, with_cps
};
use clap::Parser;
use petgraph::dot::Dot;
use pretty::BoxAllocator;

#[derive(clap::Parser, Debug)]
pub struct CommandArgs {
    #[arg(
        long = "program",
        short,
        default_value_t = true,
        help = "Compile file as a program (default: true)"
    )]
    pub program: bool,

    pub file: PathBuf,

    #[arg(long = "path", help = "Paths to search for libraries")]
    pub path: Vec<PathBuf>,
    #[arg(long = "feature", help = "Features to enable")]
    pub features: Vec<String>,
}

fn main() {
    let args = CommandArgs::parse();

    /*println!("file: {}", args.file.display());
    println!("path: {:?}", args.path);
    println!("features: {:?}", args.features);
    let mut source_manager = SourceManager::new();

    let src = match source_manager.open_file(&args.file) {
        Ok(src) => src,
        Err(e) => {
            eprintln!("Error opening file: {}", e);
            std::process::exit(1);
        }
    };

    let ts = TreeSitter::new(src, &source_manager);
    let _root_span = ts.root_span();
    let program = ts.parse_program();
    let mut errors = Vec::new();
    collect_errors_and_report(program.iter(), &mut errors);
    if !errors.is_empty() {
        for error in errors {
            error.eprint(&source_manager).unwrap();
        }
        std::process::exit(1);
    }

    let mut cenv = Cenv::new();
    let allocator = BoxAllocator;

    let mut seq = vec![];

    for expr in program.iter() {
        let iform = match pass1(&expr, &mut cenv) {
            Ok(form) => form,
            Err(error) => {
                let mut output = Vec::new();
                error.build_reports(&mut output);

                for x in output {
                    x.eprint(&source_manager).unwrap();
                }
                std::process::exit(1);
            }
        };

        let iform = resolve_primitives(&iform);
        let iform = pass_fix_letrec(iform);
        seq.push(iform);
    }

    let mut graph = program_to_graph(&seq);

    let doc = graph.pretty::<BoxAllocator, ()>(&allocator);

    doc.1
        .render(70, &mut std::io::stdout())
        .expect("Failed to render the document");
    println!();
    drop(doc);
    graph.optimize(4);
    println!("After optimization:");

    let doc = graph.pretty::<BoxAllocator, ()>(&allocator);

    doc.1
        .render(70, &mut std::io::stdout())
        .expect("Failed to render the document");
    println!();*/

    let mut cps = CPS::new();

    let v1 = Datum::new(DatumValue::Number(Number::ExactFixnum(42)));
    let v2 = Datum::new(DatumValue::Number(Number::ExactFixnum(43)));

    let x = with_cps!(cps;
        letf f (k, h, a) = with_cps!(cps; 
            letk k1 () = with_cps!(cps; 
                letv v = v1;
                continue k(v)
            );
            letk k2 () = with_cps!(cps; 
                letv v = v2;
                continue k(v)
            );

            case a => k1 | k2 
        );
        # f
    );

    let dot = cps.dot();

    println!("{:?}", dot);
}
