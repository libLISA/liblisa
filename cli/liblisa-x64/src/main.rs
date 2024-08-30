use clap::Parser;
use liblisa::arch::x64::{PrefixScope, X64Arch};
use liblisa_libcli::CliCommand;
use liblisa_x64_observer::VmOracleSource;
use log::trace;

pub fn main() {
    env_logger::init();

    let args = CliCommand::<X64Arch>::parse();
    trace!("Args: {args:#?}");

    args.run(|affinity| VmOracleSource::new(Some(affinity), 2), PrefixScope);
}
