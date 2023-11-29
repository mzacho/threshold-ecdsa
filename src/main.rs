use std::env::args;

mod circuit;
mod groups;
mod nat;
mod node;
mod schnorr;
mod shares;
mod ecdsa;

const ECDSA: &str = "ecdsa";
const SCHNORR: &str = "schnorr";

const AVAILABLE_CMDS: [&str; 2] = [ECDSA, SCHNORR];

fn main() {
    let cmd = read_command();

    match cmd.as_str() {
        SCHNORR => {
            let m = schnorr::read_args_message(args());
            schnorr::run_schnorr(m, true)
        }

        ECDSA => todo!("implement ECDSA"),
        _ => panic!(
            "Use one of the following commands: \"{cmds}\"",
            cmds = AVAILABLE_CMDS.join(", ")
        ),
    }
}

// -------------- parsing inputs
fn read_command() -> String {
    let args: Vec<String> = args().collect();
    let cmd = args.get(1).unwrap().to_string();
    cmd
}
