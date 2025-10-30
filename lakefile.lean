import Lake

open System Lake DSL

package «openvm-fv» where
  version := v!"0.1.0"
  keywords := #["math"]
  leanOptions := #[⟨`pp.unicode.fun, true⟩] -- ⟨`trace.profiler, true⟩
  moreLeanArgs := #["--tstack=400000"]

require "leanprover-community" / mathlib @ git "v4.25.0-rc2"

require LeanZKCircuit from git "https://github.com/NethermindEth/leanzkcircuit.git"@"Ferinko/4.25.0-rc2"

require LeanRV from git "https://github.com/NethermindEth/sail-riscv-lean"@"rv32d"

@[default_target] lean_lib OpenvmFv
