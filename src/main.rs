use std::{env::{self, args}, process};

use nat::Nat;

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

    println!("Running command: {}", cmd);

    match cmd.as_str() {
        SCHNORR => {
            let m = read_args_message(args());
            let group = groups::GroupSpec::new();
            let (g_r1, g_r2, r1, r2) = schnorr::preprocess_mod(&group);
            schnorr::run_treshold_schnorr(m, false, g_r1, g_r2, r1, r2, group);
        }

        ECDSA => {
            let m = read_args_message(args());
            ecdsa::run_threshold_ecdsa(m);
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

/// Read message after "ecdsa" from command line arguments
pub fn read_args_message(args: env::Args) -> Nat {
    let args: Vec<String> = args.collect();
    if args.len() != 3 {
        print!("ERR: expected message as argument to cargo run [ecdsa|schnorr]");
        process::exit(0);
    }
    let m = args.get(2).unwrap().parse::<u128>();
    if m.is_err() {
        print!("ERR: expected message (int < 2^128) as argument to cargo run [ecdsa|schnorr]");
        process::exit(0);
    }
    Nat::from(m.unwrap())
}
