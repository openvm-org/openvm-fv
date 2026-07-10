use clap::Parser;
use gag::BufferRedirect;
use openvm_sdk::{config::AppConfig, keygen::AppProvingKey};
use openvm_sdk_config::SdkVmConfig;
use openvm_stark_backend::{
    air_builders::symbolic::SymbolicConstraints, lean::extract_constraints_to_lean,
};
use openvm_stark_sdk::config::{app_params_with_100_bits_security, MAX_APP_LOG_STACKED_HEIGHT};
use std::io::{Read, Write};

#[derive(Parser)]
#[command(name = "openvm-fv-extractor")]
#[command(about = "Extract Lean4 constraint definitions from OpenVM AIRs")]
struct Cli {
    /// Name of the AIR to extract (substring match on air_name)
    #[arg(short, long)]
    air: String,
}

fn main() {
    let cli = Cli::parse();

    // SystemParams does not affect the DAG constraints
    let params = app_params_with_100_bits_security(MAX_APP_LOG_STACKED_HEIGHT);
    let config = AppConfig::<SdkVmConfig>::standard(params);

    eprintln!("Running keygen...");
    let app_pk = AppProvingKey::<SdkVmConfig>::keygen(config).expect("keygen failed");
    eprintln!(
        "Keygen complete. Searching for AIR matching '{}'...",
        cli.air
    );

    let vm_pk = &app_pk.app_vm_pk.vm_pk;
    let mut found = false;

    for pk in &vm_pk.per_air {
        if pk.air_name.contains(&cli.air) {
            eprintln!(
                "Found AIR: {} (main_width={:?}, constraints={}, interactions={})",
                pk.air_name,
                pk.vk.params.width.main_widths(),
                pk.vk.symbolic_constraints.constraints.constraint_idx.len(),
                pk.vk.symbolic_constraints.interactions.len(),
            );

            let symbolic: SymbolicConstraints<_> = (&pk.vk.symbolic_constraints).into();
            let mut buf = String::new();
            {
                let mut redirect = BufferRedirect::stdout().expect("stdout capture");
                extract_constraints_to_lean(&symbolic, &pk.air_name);
                redirect.read_to_string(&mut buf).expect("read captured");
            }
            // Tag each shared-subexpression helper `def inter_N` as `@[simp]` so
            // downstream bridge proofs unfold them during `simp`. Done here rather
            // than in stark-backend's `extract_constraints_to_lean` for locality.
            let mut out = std::io::stdout().lock();
            for line in buf.split_inclusive('\n') {
                if line.starts_with("  def inter_") {
                    out.write_all(b"  @[simp]\n").expect("write");
                }
                out.write_all(line.as_bytes()).expect("write");
            }
            found = true;
        }
    }

    if !found {
        eprintln!("No AIR found matching '{}'. Available AIRs:", cli.air);
        for pk in &vm_pk.per_air {
            eprintln!(
                "  - {} (main_width={:?})",
                pk.air_name,
                pk.vk.params.width.main_widths(),
            );
        }
        std::process::exit(1);
    }
}
