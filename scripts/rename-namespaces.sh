#!/usr/bin/env bash
# Apply old-short-name -> new-mangled-name namespace renames inside Constraints/
# files, to match the namespaces the new extractor produces.
#
# Only renames the *extraction* namespace and the two simp attribute names
# associated with each AIR. Does not touch the Constraints namespace, the
# `Valid_*` air type, or filename-based imports.
set -uo pipefail

rename_all() {
  local old="$1"; local new="$2"
  # Apply rename across all .lean files under OpenvmFv/ and VmExtensions/.
  # The patterns are extraction-namespace-scoped, so they don't touch
  # `Valid_*` air types, the `*.constraints` namespace, or filename-based imports.
  local files
  files=$(grep -rlE "${old}_air_simplification|${old}_constraint_and_interaction_simplification|${old}\.extraction" \
            --include="*.lean" OpenvmFv/ VmExtensions/ 2>/dev/null || true)
  if [ -z "$files" ]; then
    printf "  noop     (no matches)         %s -> %s\n" "$old" "$new"
    return
  fi
  echo "$files" | while read -r f; do
    sed -i '' \
      -e "s/${old}_air_simplification/${new}_air_simplification/g" \
      -e "s/${old}_constraint_and_interaction_simplification/${new}_constraint_and_interaction_simplification/g" \
      -e "s/${old}\.extraction/${new}.extraction/g" \
      "$f"
    printf "  patched  %s\n" "$f"
  done
  printf "  --- done %s -> %s ---\n" "$old" "$new"
}

rename_all "RangeTupleCheckerAir"          "RangeTupleCheckerAir_2"
rename_all "VmAirWrapper_alu"              "VmAirWrapper_Rv32BaseAluAdapterAir_BaseAluCoreAir_4_8"
rename_all "VmAirWrapper_shift"            "VmAirWrapper_Rv32BaseAluAdapterAir_ShiftCoreAir_4_8"
rename_all "VmAirWrapper_lt"               "VmAirWrapper_Rv32BaseAluAdapterAir_LessThanCoreAir_4_8"
rename_all "VmAirWrapper_mul"              "VmAirWrapper_Rv32MultAdapterAir_MultiplicationCoreAir_4_8"
rename_all "VmAirWrapper_mulh"             "VmAirWrapper_Rv32MultAdapterAir_MulHCoreAir_4_8"
rename_all "VmAirWrapper_divrem"           "VmAirWrapper_Rv32MultAdapterAir_DivRemCoreAir_4_8"
rename_all "VmAirWrapper_branch_lt"        "VmAirWrapper_Rv32BranchAdapterAir_BranchLessThanCoreAir_4_8"
rename_all "VmAirWrapper_branch_eq"        "VmAirWrapper_Rv32BranchAdapterAir_BranchEqualCoreAir_4"
rename_all "VmAirWrapper_jallui"           "VmAirWrapper_Rv32CondRdWriteAdapterAir_Rv32JalLuiCoreAir"
rename_all "VmAirWrapper_jalr"             "VmAirWrapper_Rv32JalrAdapterAir_Rv32JalrCoreAir"
rename_all "VmAirWrapper_auipc"            "VmAirWrapper_Rv32RdWriteAdapterAir_Rv32AuipcCoreAir"
rename_all "VmAirWrapper_loadstore"        "VmAirWrapper_Rv32LoadStoreAdapterAir_LoadStoreCoreAir_4"
rename_all "VmAirWrapper_load_sign_extend" "VmAirWrapper_Rv32LoadStoreAdapterAir_LoadSignExtendCoreAir_4_8"

echo "Done."
