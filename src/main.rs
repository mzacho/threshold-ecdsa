use std::env::args;

mod circuit;
mod curve;
mod ecdsa;
mod groups;
mod nat;
mod node;
mod schnorr;
mod shares;

const ECDSA: &str = "ecdsa";
const SCHNORR: &str = "schnorr";

const AVAILABLE_CMDS: [&str; 2] = [ECDSA, SCHNORR];

// Main function to run the program
// Usage: cargo run <command> <args>
// <command> is one of the following: "ecdsa", "schnorr"
// <args> depends on the command
// Example: cargo run ecdsa 1337
fn main() {
    let cmd = read_command();

    match cmd.as_str() {
        SCHNORR => {
            let m = schnorr::read_args_message(args());
            let (g_r1, g_r2, r1, r2) = schnorr::preprocess_mod(&groups::GroupSpec::new());
            schnorr::run_schnorr(m, true, g_r1, g_r2, r1, r2, groups::GroupSpec::new())
        }

        ECDSA => {
            let m = ecdsa::read_args_message(args());
            ecdsa::run_ecdsa_bedoza(m)
        }
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
