#!/usr/bin/env bash
# One-off helper: re-extract every Lean file in {OpenvmFv,VmExtensions}/Extraction/
# whose AIR has a clean match in the v2 standard SDK config.
set -uo pipefail

EXTR="./extractor/target/release/openvm-fv-extractor"
OK=0
FAIL=0

run() {
  local air="$1"; local out="$2"
  if "$EXTR" --air "$air" > "$out" 2>/dev/null; then
    if [ -s "$out" ] && grep -q "^namespace " "$out"; then
      printf "  ok   %-65s -> %s\n" "$air" "$out"
      OK=$((OK+1))
      return 0
    fi
  fi
  printf "  FAIL %-65s -> %s\n" "$air" "$out"
  FAIL=$((FAIL+1))
  return 1
}

# OpenvmFv/Extraction
run "VariableRangeCheckerAir"        "OpenvmFv/Extraction/VariableRangeCheckerAir.lean"
run "PhantomAir"                     "OpenvmFv/Extraction/PhantomAir.lean"
run "BitwiseOperationLookupAir"      "OpenvmFv/Extraction/BitwiseOperationLookupAir_8.lean"
run "RangeTupleCheckerAir"           "OpenvmFv/Extraction/RangeTupleCheckerAir.lean"
run "BaseAluCoreAir<4"               "OpenvmFv/Extraction/VmAirWrapper_alu.lean"
run "ShiftCoreAir<4"                 "OpenvmFv/Extraction/VmAirWrapper_shift.lean"
run "BaseAluAdapterAir, LessThanCoreAir" "OpenvmFv/Extraction/VmAirWrapper_lt.lean"
run "MultiplicationCoreAir<4"        "OpenvmFv/Extraction/VmAirWrapper_mul.lean"
run "MulHCoreAir<4"                  "OpenvmFv/Extraction/VmAirWrapper_mulh.lean"
run "DivRemCoreAir<4"                "OpenvmFv/Extraction/VmAirWrapper_divrem.lean"
run "BranchLessThanCoreAir<4"        "OpenvmFv/Extraction/VmAirWrapper_branch_lt.lean"
run "BranchEqualCoreAir<4"           "OpenvmFv/Extraction/VmAirWrapper_branch_eq.lean"
run "Rv32JalLuiCoreAir"              "OpenvmFv/Extraction/VmAirWrapper_jallui.lean"
run "Rv32JalrCoreAir"                "OpenvmFv/Extraction/VmAirWrapper_jalr.lean"
run "Rv32AuipcCoreAir"               "OpenvmFv/Extraction/VmAirWrapper_auipc.lean"
run "LoadStoreCoreAir<4>"            "OpenvmFv/Extraction/VmAirWrapper_loadstore.lean"
run "LoadSignExtendCoreAir<4"        "OpenvmFv/Extraction/VmAirWrapper_load_sign_extend.lean"

# VmExtensions/Extraction
run "KeccakfOpAir"                   "VmExtensions/Extraction/KeccakfOpAir.lean"
run "KeccakfPermAir"                 "VmExtensions/Extraction/KeccakfPermAir.lean"
run "Sha2MainAir<Sha256"             "VmExtensions/Extraction/Sha2MainAir_sha256.lean"
run "Sha2MainAir<Sha512"             "VmExtensions/Extraction/Sha2MainAir_sha512.lean"
run "Sha2BlockHasherVmAir<Sha256"    "VmExtensions/Extraction/Sha2BlockHasherVmAir_sha256.lean"
run "Sha2BlockHasherVmAir<Sha512"    "VmExtensions/Extraction/Sha2BlockHasherVmAir_sha512.lean"
run "XorinVmAir"                     "VmExtensions/Extraction/XorinVmAir.lean"

echo
echo "Done: $OK ok, $FAIL fail"
[ "$FAIL" = 0 ]
