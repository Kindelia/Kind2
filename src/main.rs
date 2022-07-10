#![allow(unused_variables, dead_code)]

pub use clap::Parser;
use clap::Subcommand;

const KI: usize = 1024;
const MI: usize = 1024 * 1024;
const GI: usize = 1024 * 1024 * 1024;
const KIND2_HVM_CODE: &str = include_str!("kind2.hvm");

#[derive(Parser)]
#[clap(author, version, about, long_about = None)]
#[clap(propagate_version = true)]
pub struct Cli {
  #[clap(subcommand)]
  pub command: CliCmd,
}

#[derive(Subcommand)]
pub enum CliCmd {
  /// Runs the Main term of a Kind2 file
  Run { 
    /// Input file
    file: String,
    #[clap(short, long)]
    debug: bool,
  },

  /// Checks a Kind2 file
  Check { 
    /// Input file
    file: String,
    #[clap(short, long)]
    debug: bool,
  },

  /// Compile a Kind2 file to HVM
  Compile {
    /// Input file
    file: String,
  },
}

fn main() {
  match run() {
    Ok(()) => {}
    Err(txt) => {
      eprintln!("{}", txt);
      std::process::exit(1);
    }
  }
}

pub fn build_str_term(txt: &str) -> hvm::language::Term {
  use hvm::language::Term;
  let empty = Term::Ctr { name: "StrNil".to_string(), args: Vec::new() };
  let list = txt.chars().rfold(empty, |t, c| Term::Ctr {
    name: "StrCons".to_string(),
    args: vec![Box::new(Term::Num { numb: c as u64 }), Box::new(t)],
  });
  list
}

fn run() -> Result<(), String> {
  let cli_matches = Cli::parse();

  // reads the local file "kind2.hvm" to string, using fs:
  //let mut kind2_hvm_path = std::env::current_exe().unwrap();
  //kind2_hvm_path.pop();
  //kind2_hvm_path.push("kind2.hvm");
  //println!("-> {:?}", kind2_hvm_path);
  //let kind2_hvm_code = load_file(&String::from(kind2_hvm_path.to_string_lossy()))?;

  match cli_matches.command {
    // TODO: avoid repetition

    CliCmd::Run{ file, debug } => {
      let code_str = load_file(&file)?;

      // Grows the stack. Without this, the code overflows sometimes on debug
      // mode. TODO: Investigate.
      stacker::grow(
        64 * MI, 
        || do_the_thing(&KIND2_HVM_CODE, "Kind2.Run", &code_str)
      )?;
      Ok(())
    }

    CliCmd::Check{ file, debug } => {
      let code_str = load_file(&file)?;

      // Grows the stack. Without this, the code overflows sometimes on debug
      // mode. TODO: Investigate.
      stacker::grow(
        64 * MI, 
        || do_the_thing(&KIND2_HVM_CODE, "Kind2.Check", &code_str)
      )?;
      Ok(())
    }

    CliCmd::Compile { file } => {
      let code_str = load_file(&file)?;

      // Grows the stack. Without this, the code overflows sometimes on debug
      // mode. TODO: Investigate.
      stacker::grow(
        64 * MI, 
        || do_the_thing(&KIND2_HVM_CODE, "Kind2.Compile", &code_str)
      )?;
      Ok(())

    }

  }
}

fn read_string(rt: &hvm::runtime::Worker, host: u64, str_cons: u64, str_nil: u64, i2n: Option<&std::collections::HashMap<u64, String>>) -> String {
  let mut term = hvm::runtime::ask_lnk(rt, host);
  let mut text = String::new();
  //let str_cons = rt.
  loop {
    if hvm::runtime::get_tag(term) == hvm::runtime::CTR {
      let fid = hvm::runtime::get_ext(term);
      if fid == str_cons {
        let head = hvm::runtime::ask_arg(rt, term, 0);
        let tail = hvm::runtime::ask_arg(rt, term, 1);
        if hvm::runtime::get_tag(head) == hvm::runtime::NUM {
          text.push(std::char::from_u32(hvm::runtime::get_num(head) as u32).unwrap_or('?'));
          term = tail;
          continue;
        }
      }
      if fid == str_nil {
        break;
      }
    }
    panic!("Invalid output: {} {}", hvm::runtime::get_tag(term), hvm::runtime::show_term(rt, term, i2n, 0));
  }
  return text;
}

// TODO: this will be renamed, eventually
fn do_the_thing(kind2_code: &str, call_fn_name: &str, call_fn_argm: &str) -> Result<(), String> {
  use hvm::language as lang;
  use hvm::runtime as rt;
  use hvm::rulebook as rb;
  use hvm::builder as bd;
  //use hvm::readback as rd;

  // Parses and reads the input file
  let file = lang::read_file(kind2_code)?;

  // Converts the HVM "file" to a Rulebook
  let book = rb::gen_rulebook(&file);

  let str_cons = *book.name_to_id.get("StrCons").unwrap_or(&0);
  let str_nil  = *book.name_to_id.get("StrNil").unwrap_or(&1);

  // Builds worker
  let mut worker = rt::new_worker();
  worker.funs = bd::build_runtime_functions(&book);
  worker.aris = bd::build_runtime_arities(&book);

  let str_term = build_str_term(call_fn_argm);

  let main_call = lang::Term::Ctr {
    name: call_fn_name.to_string(),
    args: vec![ Box::new(str_term) ],
  };
  let main_pos = bd::alloc_term(&mut worker, &book, &main_call);

  println!("- Reducing.");

  rt::normal(&mut worker, main_pos, Some(&book.id_to_name), false);

  println!("- Reduced. {} rewrites.", worker.cost);

  // Reads it back to a HVM string
  //let book = Some(book);
  //let text = match rd::as_term(&worker, &book, main_pos) {
    //Ok(x)   => format!("{}", x),
    //Err(..) => rd::as_code(&worker, &book, main_pos),
  //};

  // FIXME: this should be a proper function that prints HVM strings (StrCons ...)
  //let mut output = format!("{}", text);
  //if &output[0 .. 2] == "\"\"" {
    //output = "\nAll terms check.\n".to_string();
  //}
  //if &output[0 .. 1] == "\"" {
    //output = output[1 .. output.len() - 1].to_string();
  //}

  let text = read_string(&worker, main_pos, str_cons, str_nil, Some(&book.id_to_name));
  println!("");
  println!("{}", text);

  Ok(())
}

fn load_file(file_name: &str) -> Result<String, String> {
  std::fs::read_to_string(file_name).map_err(|err| err.to_string())
}
