/-
  Chi + ρπ interface for the KeccakfPermAir single-round correctness
  proof.

  The chi constraints (2910–3009) compute `χ(ρπ(θ(input)))` by reading
  from `a_prime_bit` columns with ρπ rotation baked into the column
  addressing.

  **ρπ direction convention**:

  The AIR column wiring and the spec-level `rho_pi_bits` in
  `StepLimbs.lean` use the same convention:

    `rho_pi_bits A x y k = A (rho_pi_src x y).1 (rho_pi_src x y).2 ⟨(k + rot) % 64⟩`

  where `rho_pi_src (x, y) = ((x + 3*y) % 5, x)` and
  `rot = rotOffset (5 * sy + sx)` with `rotationValues` from the spec.
  Output bit `k` reads input bit `(k + rot) % 64`, which is a
  left-rotation of the source lane by `rot` positions (equivalently,
  `getBit (rotateBy v n) k = getBit v ((k + n) % 64)` from StepLimbs).

  The AIR encodes this as column offset
  `a_prime_bit[320*sy + 64*sx + (16*limb + j + rot) % 64]`,
  which is exactly `chiAPrimeIdx` / `chiIdx` in `ChiHelpers.lean`.
  The match is verified by `chiIdx_eq_chiAPrimeIdx` (decide)
  and `rotNat_eq_rotOffset` (decide).

  **Constraints 2996 and 3000** are chi constraints whose ρπ rotation
  causes the 16-bit limb to wrap around the 64-bit lane boundary.
  They use explicit per-column references for wrapping constraints. The
  remaining constraints use `chi_recompose16_eq` for non-wrapping cases
  where columns are contiguous. The bridge for 2996 (index 86) and 3000
  (index 90) is in `ChiBridge.lean` as `chi_bridge_86` / `chi_bridge_90`,
  each proved by kernel reduction of `chiIdx` (the match-based column table).

  Exports (re-exported from ChiState.lean):
  • `chi_output_state_eq`    — chiOutputState = χ(ρπ(aPrimeState))
  • `chi_preiota_lane_zero`  — pre-iota lane [0][0] from a_prime_prime
    matches `(χ(ρπ(θ(rowInputState))))[0]`
  • `chi_nonzero_lanes`      — for all nonzero lanes i,
    `(rowOutputState air row)[i] = (χ(ρπ(θ(rowInputState))))[i]`

  File structure:
  • `ChiIdx.lean`     — kernel-reducible column index table (1381 match arms)
  • `ChiHelpers.lean` — field↔bool bridges, column mapping, roundtrip lemmas
  • `ChiBridge.lean`  — 100 individual constraint bridges + dispatch
  • `ChiState.lean`   — proofs of chi_output_state_eq and lane theorems
  • `ChiFacts.lean`   — this file: public facade re-exporting those results
-/
import VmExtensions.Soundness.KeccakfPermAir.Round.ChiState

-- Re-export the chi results.
-- The actual proofs live in ChiState.lean (which imports ChiHelpers + ChiBridge).
