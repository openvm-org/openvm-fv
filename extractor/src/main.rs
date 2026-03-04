use clap::Parser;
use openvm_sdk_config::SdkVmConfig;
use openvm_stark_backend::{
    air_builders::symbolic::SymbolicConstraints,
    keygen::lean::extract_constraints_to_lean,
};
use sdk_v2::{
    config::{default_app_params, AppConfig, DEFAULT_APP_LOG_BLOWUP, DEFAULT_APP_L_SKIP},
    keygen::AppProvingKey,
};

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

    let params = default_app_params(DEFAULT_APP_LOG_BLOWUP, DEFAULT_APP_L_SKIP, 1);
    let config = AppConfig::<SdkVmConfig>::standard(params);

    eprintln!("Running keygen...");
    let app_pk = AppProvingKey::<SdkVmConfig>::keygen(config).expect("keygen failed");
    eprintln!("Keygen complete. Searching for AIR matching '{}'...", cli.air);

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
            extract_constraints_to_lean(&symbolic, &pk.air_name);
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
