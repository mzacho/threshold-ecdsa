use std::env::args;

mod bloodtypes;
mod circuit;
mod groups;
mod nat;
mod node;
mod schnorr;
mod shares;

const BT: &str = "bloodtype";
const SN: &str = "schnorr";

const AVAILABLE_CMDS: [&str; 2] = [BT, SN];

fn main() {
    let cmd = read_command();

    match cmd.as_str() {
        BT => {
            let (x, y) = bloodtypes::read_args_bloodtypes(args());
            bloodtypes::run_blood_type(x, y, true);
        }
        SN => {
            let m = schnorr::read_args_message(args());
            schnorr::run_schnorr(m);
        }
        _ => panic!(
            "Use one of the following commands: \"{cmds}\"",
            cmds = AVAILABLE_CMDS.join(", ")
        ),
    }
}

fn read_command() -> String {
    let args: Vec<String> = args().collect();
    let cmd = args.get(1).unwrap().to_string();
    cmd
}
