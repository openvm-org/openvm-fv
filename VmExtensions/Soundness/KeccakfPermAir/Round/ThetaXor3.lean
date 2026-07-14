/-
  Raw xor3-linking interface for the KeccakfPermAir single-round correctness
  proof.

  This lower-level helper exposes the raw theta xor3 relation without the
  full theta-state interface.

  Provides:
  • `theta_a_eq_xor3_recompose`: for each limb j ∈ [0, 100), the `a` column
    at index j equals the 16-bit xor3 recomposition of corresponding c_bit,
    c_prime_bit, and a_prime_bit chunks.
  • `theta_xor3_raw`: for each limb j ∈ [0, 100), the raw
    `xor3_recompose16_eq` constraint holds, as a direct projection from
    `RoundLocalConstraints`.

  ## Horner-peeling

  The openvm v2.0.0 extraction emits each `xor3_recompose16_eq` dispatch value
  as a nested Horner accumulator chain of `@[simp] inter_*` definitions rather
  than a flat semantic polynomial.  Proving the recomposition equality by a
  single `ring` over the fully-unfolded Horner form is catastrophically slow
  (>9 min per limb-tuple over the concrete air).

  Instead, each concrete constraint is discharged by a private `peel_g_<cnum>`
  lemma that keeps the accumulator `inter_*` nodes OPAQUE and telescopes the
  Horner recursion one level at a time:
  `inter_{A-2(k-1)} = xor3(k) + 2 * inter_{A-2k}` (each a tiny 3-atom `ring`),
  down to the base `inter_{A-28} = xor3(15)`, then a single `linear_combination`
  with weights `2^k`.  Because the inters stay opaque, the final combination is
  effectively the flat form and closes in ~0.5 s.  The columns are abstracted to
  an opaque `mc : ℕ → F` (via the `hmc` hypothesis) so `ring` never unfolds the
  concrete `Circuit` instance dictionary.

  `theta_a_eq_xor3_recompose` then case-splits `j < 100` and dispatches each
  concrete limb to its `peel_g_<cnum>` lemma; every case closes by definitional
  equality in ~0.1 s.
-/
import VmExtensions.Soundness.KeccakfPermAir.Round.Surface

set_option autoImplicit false
set_option linter.all false
set_option maxHeartbeats 8000000

namespace KeccakfPermAir.Soundness

open BabyBear
open KeccakfPermAir.constraints

/-! ## Per-constraint Horner-peeling lemmas

For each concrete `xor3_recompose16_eq` dispatch value (one per limb `j < 100`),
`peel_g_<cnum>` converts the Horner-form constraint into the explicit
little-endian weighted sum of 16 three-way XOR values.  The bit columns are
abstracted to `mc` so the telescoping `ring` steps stay cheap. -/

private theorem peel_g_954 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 225 545 865 125 row) :
    mc 125 = (mc 225 + mc 545 + mc 865 - 2*mc 225*mc 545 - 2*mc 225*mc 865 - 2*mc 545*mc 865 + 4*mc 225*mc 545*mc 865) + 2*(mc 226 + mc 546 + mc 866 - 2*mc 226*mc 546 - 2*mc 226*mc 866 - 2*mc 546*mc 866 + 4*mc 226*mc 546*mc 866) + 4*(mc 227 + mc 547 + mc 867 - 2*mc 227*mc 547 - 2*mc 227*mc 867 - 2*mc 547*mc 867 + 4*mc 227*mc 547*mc 867) + 8*(mc 228 + mc 548 + mc 868 - 2*mc 228*mc 548 - 2*mc 228*mc 868 - 2*mc 548*mc 868 + 4*mc 228*mc 548*mc 868) + 16*(mc 229 + mc 549 + mc 869 - 2*mc 229*mc 549 - 2*mc 229*mc 869 - 2*mc 549*mc 869 + 4*mc 229*mc 549*mc 869) + 32*(mc 230 + mc 550 + mc 870 - 2*mc 230*mc 550 - 2*mc 230*mc 870 - 2*mc 550*mc 870 + 4*mc 230*mc 550*mc 870) + 64*(mc 231 + mc 551 + mc 871 - 2*mc 231*mc 551 - 2*mc 231*mc 871 - 2*mc 551*mc 871 + 4*mc 231*mc 551*mc 871) + 128*(mc 232 + mc 552 + mc 872 - 2*mc 232*mc 552 - 2*mc 232*mc 872 - 2*mc 552*mc 872 + 4*mc 232*mc 552*mc 872) + 256*(mc 233 + mc 553 + mc 873 - 2*mc 233*mc 553 - 2*mc 233*mc 873 - 2*mc 553*mc 873 + 4*mc 233*mc 553*mc 873) + 512*(mc 234 + mc 554 + mc 874 - 2*mc 234*mc 554 - 2*mc 234*mc 874 - 2*mc 554*mc 874 + 4*mc 234*mc 554*mc 874) + 1024*(mc 235 + mc 555 + mc 875 - 2*mc 235*mc 555 - 2*mc 235*mc 875 - 2*mc 555*mc 875 + 4*mc 235*mc 555*mc 875) + 2048*(mc 236 + mc 556 + mc 876 - 2*mc 236*mc 556 - 2*mc 236*mc 876 - 2*mc 556*mc 876 + 4*mc 236*mc 556*mc 876) + 4096*(mc 237 + mc 557 + mc 877 - 2*mc 237*mc 557 - 2*mc 237*mc 877 - 2*mc 557*mc 877 + 4*mc 237*mc 557*mc 877) + 8192*(mc 238 + mc 558 + mc 878 - 2*mc 238*mc 558 - 2*mc 238*mc 878 - 2*mc 558*mc 878 + 4*mc 238*mc 558*mc 878) + 16384*(mc 239 + mc 559 + mc 879 - 2*mc 239*mc 559 - 2*mc 239*mc 879 - 2*mc 559*mc 879 + 4*mc 239*mc 559*mc 879) + 32768*(mc 240 + mc 560 + mc 880 - 2*mc 240*mc 560 - 2*mc 240*mc 880 - 2*mc 560*mc 880 + 4*mc 240*mc 560*mc 880) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_954, KeccakfPermAir.extraction.inter_350, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_349 c row = (mc 226 + mc 546 + mc 866 - 2*mc 226*mc 546 - 2*mc 226*mc 866 - 2*mc 546*mc 866 + 4*mc 226*mc 546*mc 866) + 2 * KeccakfPermAir.extraction.inter_347 c row := by
    simp only [KeccakfPermAir.extraction.inter_349, KeccakfPermAir.extraction.inter_348, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_347 c row = (mc 227 + mc 547 + mc 867 - 2*mc 227*mc 547 - 2*mc 227*mc 867 - 2*mc 547*mc 867 + 4*mc 227*mc 547*mc 867) + 2 * KeccakfPermAir.extraction.inter_345 c row := by
    simp only [KeccakfPermAir.extraction.inter_347, KeccakfPermAir.extraction.inter_346, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_345 c row = (mc 228 + mc 548 + mc 868 - 2*mc 228*mc 548 - 2*mc 228*mc 868 - 2*mc 548*mc 868 + 4*mc 228*mc 548*mc 868) + 2 * KeccakfPermAir.extraction.inter_343 c row := by
    simp only [KeccakfPermAir.extraction.inter_345, KeccakfPermAir.extraction.inter_344, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_343 c row = (mc 229 + mc 549 + mc 869 - 2*mc 229*mc 549 - 2*mc 229*mc 869 - 2*mc 549*mc 869 + 4*mc 229*mc 549*mc 869) + 2 * KeccakfPermAir.extraction.inter_341 c row := by
    simp only [KeccakfPermAir.extraction.inter_343, KeccakfPermAir.extraction.inter_342, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_341 c row = (mc 230 + mc 550 + mc 870 - 2*mc 230*mc 550 - 2*mc 230*mc 870 - 2*mc 550*mc 870 + 4*mc 230*mc 550*mc 870) + 2 * KeccakfPermAir.extraction.inter_339 c row := by
    simp only [KeccakfPermAir.extraction.inter_341, KeccakfPermAir.extraction.inter_340, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_339 c row = (mc 231 + mc 551 + mc 871 - 2*mc 231*mc 551 - 2*mc 231*mc 871 - 2*mc 551*mc 871 + 4*mc 231*mc 551*mc 871) + 2 * KeccakfPermAir.extraction.inter_337 c row := by
    simp only [KeccakfPermAir.extraction.inter_339, KeccakfPermAir.extraction.inter_338, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_337 c row = (mc 232 + mc 552 + mc 872 - 2*mc 232*mc 552 - 2*mc 232*mc 872 - 2*mc 552*mc 872 + 4*mc 232*mc 552*mc 872) + 2 * KeccakfPermAir.extraction.inter_335 c row := by
    simp only [KeccakfPermAir.extraction.inter_337, KeccakfPermAir.extraction.inter_336, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_335 c row = (mc 233 + mc 553 + mc 873 - 2*mc 233*mc 553 - 2*mc 233*mc 873 - 2*mc 553*mc 873 + 4*mc 233*mc 553*mc 873) + 2 * KeccakfPermAir.extraction.inter_333 c row := by
    simp only [KeccakfPermAir.extraction.inter_335, KeccakfPermAir.extraction.inter_334, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_333 c row = (mc 234 + mc 554 + mc 874 - 2*mc 234*mc 554 - 2*mc 234*mc 874 - 2*mc 554*mc 874 + 4*mc 234*mc 554*mc 874) + 2 * KeccakfPermAir.extraction.inter_331 c row := by
    simp only [KeccakfPermAir.extraction.inter_333, KeccakfPermAir.extraction.inter_332, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_331 c row = (mc 235 + mc 555 + mc 875 - 2*mc 235*mc 555 - 2*mc 235*mc 875 - 2*mc 555*mc 875 + 4*mc 235*mc 555*mc 875) + 2 * KeccakfPermAir.extraction.inter_329 c row := by
    simp only [KeccakfPermAir.extraction.inter_331, KeccakfPermAir.extraction.inter_330, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_329 c row = (mc 236 + mc 556 + mc 876 - 2*mc 236*mc 556 - 2*mc 236*mc 876 - 2*mc 556*mc 876 + 4*mc 236*mc 556*mc 876) + 2 * KeccakfPermAir.extraction.inter_327 c row := by
    simp only [KeccakfPermAir.extraction.inter_329, KeccakfPermAir.extraction.inter_328, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_327 c row = (mc 237 + mc 557 + mc 877 - 2*mc 237*mc 557 - 2*mc 237*mc 877 - 2*mc 557*mc 877 + 4*mc 237*mc 557*mc 877) + 2 * KeccakfPermAir.extraction.inter_325 c row := by
    simp only [KeccakfPermAir.extraction.inter_327, KeccakfPermAir.extraction.inter_326, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_325 c row = (mc 238 + mc 558 + mc 878 - 2*mc 238*mc 558 - 2*mc 238*mc 878 - 2*mc 558*mc 878 + 4*mc 238*mc 558*mc 878) + 2 * KeccakfPermAir.extraction.inter_323 c row := by
    simp only [KeccakfPermAir.extraction.inter_325, KeccakfPermAir.extraction.inter_324, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_323 c row = (mc 239 + mc 559 + mc 879 - 2*mc 239*mc 559 - 2*mc 239*mc 879 - 2*mc 559*mc 879 + 4*mc 239*mc 559*mc 879) + 2 * KeccakfPermAir.extraction.inter_321 c row := by
    simp only [KeccakfPermAir.extraction.inter_323, KeccakfPermAir.extraction.inter_322, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_321 c row = (mc 240 + mc 560 + mc 880 - 2*mc 240*mc 560 - 2*mc 240*mc 880 - 2*mc 560*mc 880 + 4*mc 240*mc 560*mc 880) := by
    simp only [KeccakfPermAir.extraction.inter_321, KeccakfPermAir.extraction.inter_320, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_955 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 241 561 881 126 row) :
    mc 126 = (mc 241 + mc 561 + mc 881 - 2*mc 241*mc 561 - 2*mc 241*mc 881 - 2*mc 561*mc 881 + 4*mc 241*mc 561*mc 881) + 2*(mc 242 + mc 562 + mc 882 - 2*mc 242*mc 562 - 2*mc 242*mc 882 - 2*mc 562*mc 882 + 4*mc 242*mc 562*mc 882) + 4*(mc 243 + mc 563 + mc 883 - 2*mc 243*mc 563 - 2*mc 243*mc 883 - 2*mc 563*mc 883 + 4*mc 243*mc 563*mc 883) + 8*(mc 244 + mc 564 + mc 884 - 2*mc 244*mc 564 - 2*mc 244*mc 884 - 2*mc 564*mc 884 + 4*mc 244*mc 564*mc 884) + 16*(mc 245 + mc 565 + mc 885 - 2*mc 245*mc 565 - 2*mc 245*mc 885 - 2*mc 565*mc 885 + 4*mc 245*mc 565*mc 885) + 32*(mc 246 + mc 566 + mc 886 - 2*mc 246*mc 566 - 2*mc 246*mc 886 - 2*mc 566*mc 886 + 4*mc 246*mc 566*mc 886) + 64*(mc 247 + mc 567 + mc 887 - 2*mc 247*mc 567 - 2*mc 247*mc 887 - 2*mc 567*mc 887 + 4*mc 247*mc 567*mc 887) + 128*(mc 248 + mc 568 + mc 888 - 2*mc 248*mc 568 - 2*mc 248*mc 888 - 2*mc 568*mc 888 + 4*mc 248*mc 568*mc 888) + 256*(mc 249 + mc 569 + mc 889 - 2*mc 249*mc 569 - 2*mc 249*mc 889 - 2*mc 569*mc 889 + 4*mc 249*mc 569*mc 889) + 512*(mc 250 + mc 570 + mc 890 - 2*mc 250*mc 570 - 2*mc 250*mc 890 - 2*mc 570*mc 890 + 4*mc 250*mc 570*mc 890) + 1024*(mc 251 + mc 571 + mc 891 - 2*mc 251*mc 571 - 2*mc 251*mc 891 - 2*mc 571*mc 891 + 4*mc 251*mc 571*mc 891) + 2048*(mc 252 + mc 572 + mc 892 - 2*mc 252*mc 572 - 2*mc 252*mc 892 - 2*mc 572*mc 892 + 4*mc 252*mc 572*mc 892) + 4096*(mc 253 + mc 573 + mc 893 - 2*mc 253*mc 573 - 2*mc 253*mc 893 - 2*mc 573*mc 893 + 4*mc 253*mc 573*mc 893) + 8192*(mc 254 + mc 574 + mc 894 - 2*mc 254*mc 574 - 2*mc 254*mc 894 - 2*mc 574*mc 894 + 4*mc 254*mc 574*mc 894) + 16384*(mc 255 + mc 575 + mc 895 - 2*mc 255*mc 575 - 2*mc 255*mc 895 - 2*mc 575*mc 895 + 4*mc 255*mc 575*mc 895) + 32768*(mc 256 + mc 576 + mc 896 - 2*mc 256*mc 576 - 2*mc 256*mc 896 - 2*mc 576*mc 896 + 4*mc 256*mc 576*mc 896) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_955, KeccakfPermAir.extraction.inter_381, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_380 c row = (mc 242 + mc 562 + mc 882 - 2*mc 242*mc 562 - 2*mc 242*mc 882 - 2*mc 562*mc 882 + 4*mc 242*mc 562*mc 882) + 2 * KeccakfPermAir.extraction.inter_378 c row := by
    simp only [KeccakfPermAir.extraction.inter_380, KeccakfPermAir.extraction.inter_379, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_378 c row = (mc 243 + mc 563 + mc 883 - 2*mc 243*mc 563 - 2*mc 243*mc 883 - 2*mc 563*mc 883 + 4*mc 243*mc 563*mc 883) + 2 * KeccakfPermAir.extraction.inter_376 c row := by
    simp only [KeccakfPermAir.extraction.inter_378, KeccakfPermAir.extraction.inter_377, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_376 c row = (mc 244 + mc 564 + mc 884 - 2*mc 244*mc 564 - 2*mc 244*mc 884 - 2*mc 564*mc 884 + 4*mc 244*mc 564*mc 884) + 2 * KeccakfPermAir.extraction.inter_374 c row := by
    simp only [KeccakfPermAir.extraction.inter_376, KeccakfPermAir.extraction.inter_375, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_374 c row = (mc 245 + mc 565 + mc 885 - 2*mc 245*mc 565 - 2*mc 245*mc 885 - 2*mc 565*mc 885 + 4*mc 245*mc 565*mc 885) + 2 * KeccakfPermAir.extraction.inter_372 c row := by
    simp only [KeccakfPermAir.extraction.inter_374, KeccakfPermAir.extraction.inter_373, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_372 c row = (mc 246 + mc 566 + mc 886 - 2*mc 246*mc 566 - 2*mc 246*mc 886 - 2*mc 566*mc 886 + 4*mc 246*mc 566*mc 886) + 2 * KeccakfPermAir.extraction.inter_370 c row := by
    simp only [KeccakfPermAir.extraction.inter_372, KeccakfPermAir.extraction.inter_371, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_370 c row = (mc 247 + mc 567 + mc 887 - 2*mc 247*mc 567 - 2*mc 247*mc 887 - 2*mc 567*mc 887 + 4*mc 247*mc 567*mc 887) + 2 * KeccakfPermAir.extraction.inter_368 c row := by
    simp only [KeccakfPermAir.extraction.inter_370, KeccakfPermAir.extraction.inter_369, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_368 c row = (mc 248 + mc 568 + mc 888 - 2*mc 248*mc 568 - 2*mc 248*mc 888 - 2*mc 568*mc 888 + 4*mc 248*mc 568*mc 888) + 2 * KeccakfPermAir.extraction.inter_366 c row := by
    simp only [KeccakfPermAir.extraction.inter_368, KeccakfPermAir.extraction.inter_367, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_366 c row = (mc 249 + mc 569 + mc 889 - 2*mc 249*mc 569 - 2*mc 249*mc 889 - 2*mc 569*mc 889 + 4*mc 249*mc 569*mc 889) + 2 * KeccakfPermAir.extraction.inter_364 c row := by
    simp only [KeccakfPermAir.extraction.inter_366, KeccakfPermAir.extraction.inter_365, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_364 c row = (mc 250 + mc 570 + mc 890 - 2*mc 250*mc 570 - 2*mc 250*mc 890 - 2*mc 570*mc 890 + 4*mc 250*mc 570*mc 890) + 2 * KeccakfPermAir.extraction.inter_362 c row := by
    simp only [KeccakfPermAir.extraction.inter_364, KeccakfPermAir.extraction.inter_363, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_362 c row = (mc 251 + mc 571 + mc 891 - 2*mc 251*mc 571 - 2*mc 251*mc 891 - 2*mc 571*mc 891 + 4*mc 251*mc 571*mc 891) + 2 * KeccakfPermAir.extraction.inter_360 c row := by
    simp only [KeccakfPermAir.extraction.inter_362, KeccakfPermAir.extraction.inter_361, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_360 c row = (mc 252 + mc 572 + mc 892 - 2*mc 252*mc 572 - 2*mc 252*mc 892 - 2*mc 572*mc 892 + 4*mc 252*mc 572*mc 892) + 2 * KeccakfPermAir.extraction.inter_358 c row := by
    simp only [KeccakfPermAir.extraction.inter_360, KeccakfPermAir.extraction.inter_359, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_358 c row = (mc 253 + mc 573 + mc 893 - 2*mc 253*mc 573 - 2*mc 253*mc 893 - 2*mc 573*mc 893 + 4*mc 253*mc 573*mc 893) + 2 * KeccakfPermAir.extraction.inter_356 c row := by
    simp only [KeccakfPermAir.extraction.inter_358, KeccakfPermAir.extraction.inter_357, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_356 c row = (mc 254 + mc 574 + mc 894 - 2*mc 254*mc 574 - 2*mc 254*mc 894 - 2*mc 574*mc 894 + 4*mc 254*mc 574*mc 894) + 2 * KeccakfPermAir.extraction.inter_354 c row := by
    simp only [KeccakfPermAir.extraction.inter_356, KeccakfPermAir.extraction.inter_355, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_354 c row = (mc 255 + mc 575 + mc 895 - 2*mc 255*mc 575 - 2*mc 255*mc 895 - 2*mc 575*mc 895 + 4*mc 255*mc 575*mc 895) + 2 * KeccakfPermAir.extraction.inter_352 c row := by
    simp only [KeccakfPermAir.extraction.inter_354, KeccakfPermAir.extraction.inter_353, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_352 c row = (mc 256 + mc 576 + mc 896 - 2*mc 256*mc 576 - 2*mc 256*mc 896 - 2*mc 576*mc 896 + 4*mc 256*mc 576*mc 896) := by
    simp only [KeccakfPermAir.extraction.inter_352, KeccakfPermAir.extraction.inter_351, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_956 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 257 577 897 127 row) :
    mc 127 = (mc 257 + mc 577 + mc 897 - 2*mc 257*mc 577 - 2*mc 257*mc 897 - 2*mc 577*mc 897 + 4*mc 257*mc 577*mc 897) + 2*(mc 258 + mc 578 + mc 898 - 2*mc 258*mc 578 - 2*mc 258*mc 898 - 2*mc 578*mc 898 + 4*mc 258*mc 578*mc 898) + 4*(mc 259 + mc 579 + mc 899 - 2*mc 259*mc 579 - 2*mc 259*mc 899 - 2*mc 579*mc 899 + 4*mc 259*mc 579*mc 899) + 8*(mc 260 + mc 580 + mc 900 - 2*mc 260*mc 580 - 2*mc 260*mc 900 - 2*mc 580*mc 900 + 4*mc 260*mc 580*mc 900) + 16*(mc 261 + mc 581 + mc 901 - 2*mc 261*mc 581 - 2*mc 261*mc 901 - 2*mc 581*mc 901 + 4*mc 261*mc 581*mc 901) + 32*(mc 262 + mc 582 + mc 902 - 2*mc 262*mc 582 - 2*mc 262*mc 902 - 2*mc 582*mc 902 + 4*mc 262*mc 582*mc 902) + 64*(mc 263 + mc 583 + mc 903 - 2*mc 263*mc 583 - 2*mc 263*mc 903 - 2*mc 583*mc 903 + 4*mc 263*mc 583*mc 903) + 128*(mc 264 + mc 584 + mc 904 - 2*mc 264*mc 584 - 2*mc 264*mc 904 - 2*mc 584*mc 904 + 4*mc 264*mc 584*mc 904) + 256*(mc 265 + mc 585 + mc 905 - 2*mc 265*mc 585 - 2*mc 265*mc 905 - 2*mc 585*mc 905 + 4*mc 265*mc 585*mc 905) + 512*(mc 266 + mc 586 + mc 906 - 2*mc 266*mc 586 - 2*mc 266*mc 906 - 2*mc 586*mc 906 + 4*mc 266*mc 586*mc 906) + 1024*(mc 267 + mc 587 + mc 907 - 2*mc 267*mc 587 - 2*mc 267*mc 907 - 2*mc 587*mc 907 + 4*mc 267*mc 587*mc 907) + 2048*(mc 268 + mc 588 + mc 908 - 2*mc 268*mc 588 - 2*mc 268*mc 908 - 2*mc 588*mc 908 + 4*mc 268*mc 588*mc 908) + 4096*(mc 269 + mc 589 + mc 909 - 2*mc 269*mc 589 - 2*mc 269*mc 909 - 2*mc 589*mc 909 + 4*mc 269*mc 589*mc 909) + 8192*(mc 270 + mc 590 + mc 910 - 2*mc 270*mc 590 - 2*mc 270*mc 910 - 2*mc 590*mc 910 + 4*mc 270*mc 590*mc 910) + 16384*(mc 271 + mc 591 + mc 911 - 2*mc 271*mc 591 - 2*mc 271*mc 911 - 2*mc 591*mc 911 + 4*mc 271*mc 591*mc 911) + 32768*(mc 272 + mc 592 + mc 912 - 2*mc 272*mc 592 - 2*mc 272*mc 912 - 2*mc 592*mc 912 + 4*mc 272*mc 592*mc 912) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_956, KeccakfPermAir.extraction.inter_412, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_411 c row = (mc 258 + mc 578 + mc 898 - 2*mc 258*mc 578 - 2*mc 258*mc 898 - 2*mc 578*mc 898 + 4*mc 258*mc 578*mc 898) + 2 * KeccakfPermAir.extraction.inter_409 c row := by
    simp only [KeccakfPermAir.extraction.inter_411, KeccakfPermAir.extraction.inter_410, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_409 c row = (mc 259 + mc 579 + mc 899 - 2*mc 259*mc 579 - 2*mc 259*mc 899 - 2*mc 579*mc 899 + 4*mc 259*mc 579*mc 899) + 2 * KeccakfPermAir.extraction.inter_407 c row := by
    simp only [KeccakfPermAir.extraction.inter_409, KeccakfPermAir.extraction.inter_408, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_407 c row = (mc 260 + mc 580 + mc 900 - 2*mc 260*mc 580 - 2*mc 260*mc 900 - 2*mc 580*mc 900 + 4*mc 260*mc 580*mc 900) + 2 * KeccakfPermAir.extraction.inter_405 c row := by
    simp only [KeccakfPermAir.extraction.inter_407, KeccakfPermAir.extraction.inter_406, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_405 c row = (mc 261 + mc 581 + mc 901 - 2*mc 261*mc 581 - 2*mc 261*mc 901 - 2*mc 581*mc 901 + 4*mc 261*mc 581*mc 901) + 2 * KeccakfPermAir.extraction.inter_403 c row := by
    simp only [KeccakfPermAir.extraction.inter_405, KeccakfPermAir.extraction.inter_404, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_403 c row = (mc 262 + mc 582 + mc 902 - 2*mc 262*mc 582 - 2*mc 262*mc 902 - 2*mc 582*mc 902 + 4*mc 262*mc 582*mc 902) + 2 * KeccakfPermAir.extraction.inter_401 c row := by
    simp only [KeccakfPermAir.extraction.inter_403, KeccakfPermAir.extraction.inter_402, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_401 c row = (mc 263 + mc 583 + mc 903 - 2*mc 263*mc 583 - 2*mc 263*mc 903 - 2*mc 583*mc 903 + 4*mc 263*mc 583*mc 903) + 2 * KeccakfPermAir.extraction.inter_399 c row := by
    simp only [KeccakfPermAir.extraction.inter_401, KeccakfPermAir.extraction.inter_400, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_399 c row = (mc 264 + mc 584 + mc 904 - 2*mc 264*mc 584 - 2*mc 264*mc 904 - 2*mc 584*mc 904 + 4*mc 264*mc 584*mc 904) + 2 * KeccakfPermAir.extraction.inter_397 c row := by
    simp only [KeccakfPermAir.extraction.inter_399, KeccakfPermAir.extraction.inter_398, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_397 c row = (mc 265 + mc 585 + mc 905 - 2*mc 265*mc 585 - 2*mc 265*mc 905 - 2*mc 585*mc 905 + 4*mc 265*mc 585*mc 905) + 2 * KeccakfPermAir.extraction.inter_395 c row := by
    simp only [KeccakfPermAir.extraction.inter_397, KeccakfPermAir.extraction.inter_396, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_395 c row = (mc 266 + mc 586 + mc 906 - 2*mc 266*mc 586 - 2*mc 266*mc 906 - 2*mc 586*mc 906 + 4*mc 266*mc 586*mc 906) + 2 * KeccakfPermAir.extraction.inter_393 c row := by
    simp only [KeccakfPermAir.extraction.inter_395, KeccakfPermAir.extraction.inter_394, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_393 c row = (mc 267 + mc 587 + mc 907 - 2*mc 267*mc 587 - 2*mc 267*mc 907 - 2*mc 587*mc 907 + 4*mc 267*mc 587*mc 907) + 2 * KeccakfPermAir.extraction.inter_391 c row := by
    simp only [KeccakfPermAir.extraction.inter_393, KeccakfPermAir.extraction.inter_392, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_391 c row = (mc 268 + mc 588 + mc 908 - 2*mc 268*mc 588 - 2*mc 268*mc 908 - 2*mc 588*mc 908 + 4*mc 268*mc 588*mc 908) + 2 * KeccakfPermAir.extraction.inter_389 c row := by
    simp only [KeccakfPermAir.extraction.inter_391, KeccakfPermAir.extraction.inter_390, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_389 c row = (mc 269 + mc 589 + mc 909 - 2*mc 269*mc 589 - 2*mc 269*mc 909 - 2*mc 589*mc 909 + 4*mc 269*mc 589*mc 909) + 2 * KeccakfPermAir.extraction.inter_387 c row := by
    simp only [KeccakfPermAir.extraction.inter_389, KeccakfPermAir.extraction.inter_388, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_387 c row = (mc 270 + mc 590 + mc 910 - 2*mc 270*mc 590 - 2*mc 270*mc 910 - 2*mc 590*mc 910 + 4*mc 270*mc 590*mc 910) + 2 * KeccakfPermAir.extraction.inter_385 c row := by
    simp only [KeccakfPermAir.extraction.inter_387, KeccakfPermAir.extraction.inter_386, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_385 c row = (mc 271 + mc 591 + mc 911 - 2*mc 271*mc 591 - 2*mc 271*mc 911 - 2*mc 591*mc 911 + 4*mc 271*mc 591*mc 911) + 2 * KeccakfPermAir.extraction.inter_383 c row := by
    simp only [KeccakfPermAir.extraction.inter_385, KeccakfPermAir.extraction.inter_384, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_383 c row = (mc 272 + mc 592 + mc 912 - 2*mc 272*mc 592 - 2*mc 272*mc 912 - 2*mc 592*mc 912 + 4*mc 272*mc 592*mc 912) := by
    simp only [KeccakfPermAir.extraction.inter_383, KeccakfPermAir.extraction.inter_382, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_957 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 273 593 913 128 row) :
    mc 128 = (mc 273 + mc 593 + mc 913 - 2*mc 273*mc 593 - 2*mc 273*mc 913 - 2*mc 593*mc 913 + 4*mc 273*mc 593*mc 913) + 2*(mc 274 + mc 594 + mc 914 - 2*mc 274*mc 594 - 2*mc 274*mc 914 - 2*mc 594*mc 914 + 4*mc 274*mc 594*mc 914) + 4*(mc 275 + mc 595 + mc 915 - 2*mc 275*mc 595 - 2*mc 275*mc 915 - 2*mc 595*mc 915 + 4*mc 275*mc 595*mc 915) + 8*(mc 276 + mc 596 + mc 916 - 2*mc 276*mc 596 - 2*mc 276*mc 916 - 2*mc 596*mc 916 + 4*mc 276*mc 596*mc 916) + 16*(mc 277 + mc 597 + mc 917 - 2*mc 277*mc 597 - 2*mc 277*mc 917 - 2*mc 597*mc 917 + 4*mc 277*mc 597*mc 917) + 32*(mc 278 + mc 598 + mc 918 - 2*mc 278*mc 598 - 2*mc 278*mc 918 - 2*mc 598*mc 918 + 4*mc 278*mc 598*mc 918) + 64*(mc 279 + mc 599 + mc 919 - 2*mc 279*mc 599 - 2*mc 279*mc 919 - 2*mc 599*mc 919 + 4*mc 279*mc 599*mc 919) + 128*(mc 280 + mc 600 + mc 920 - 2*mc 280*mc 600 - 2*mc 280*mc 920 - 2*mc 600*mc 920 + 4*mc 280*mc 600*mc 920) + 256*(mc 281 + mc 601 + mc 921 - 2*mc 281*mc 601 - 2*mc 281*mc 921 - 2*mc 601*mc 921 + 4*mc 281*mc 601*mc 921) + 512*(mc 282 + mc 602 + mc 922 - 2*mc 282*mc 602 - 2*mc 282*mc 922 - 2*mc 602*mc 922 + 4*mc 282*mc 602*mc 922) + 1024*(mc 283 + mc 603 + mc 923 - 2*mc 283*mc 603 - 2*mc 283*mc 923 - 2*mc 603*mc 923 + 4*mc 283*mc 603*mc 923) + 2048*(mc 284 + mc 604 + mc 924 - 2*mc 284*mc 604 - 2*mc 284*mc 924 - 2*mc 604*mc 924 + 4*mc 284*mc 604*mc 924) + 4096*(mc 285 + mc 605 + mc 925 - 2*mc 285*mc 605 - 2*mc 285*mc 925 - 2*mc 605*mc 925 + 4*mc 285*mc 605*mc 925) + 8192*(mc 286 + mc 606 + mc 926 - 2*mc 286*mc 606 - 2*mc 286*mc 926 - 2*mc 606*mc 926 + 4*mc 286*mc 606*mc 926) + 16384*(mc 287 + mc 607 + mc 927 - 2*mc 287*mc 607 - 2*mc 287*mc 927 - 2*mc 607*mc 927 + 4*mc 287*mc 607*mc 927) + 32768*(mc 288 + mc 608 + mc 928 - 2*mc 288*mc 608 - 2*mc 288*mc 928 - 2*mc 608*mc 928 + 4*mc 288*mc 608*mc 928) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_957, KeccakfPermAir.extraction.inter_443, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_442 c row = (mc 274 + mc 594 + mc 914 - 2*mc 274*mc 594 - 2*mc 274*mc 914 - 2*mc 594*mc 914 + 4*mc 274*mc 594*mc 914) + 2 * KeccakfPermAir.extraction.inter_440 c row := by
    simp only [KeccakfPermAir.extraction.inter_442, KeccakfPermAir.extraction.inter_441, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_440 c row = (mc 275 + mc 595 + mc 915 - 2*mc 275*mc 595 - 2*mc 275*mc 915 - 2*mc 595*mc 915 + 4*mc 275*mc 595*mc 915) + 2 * KeccakfPermAir.extraction.inter_438 c row := by
    simp only [KeccakfPermAir.extraction.inter_440, KeccakfPermAir.extraction.inter_439, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_438 c row = (mc 276 + mc 596 + mc 916 - 2*mc 276*mc 596 - 2*mc 276*mc 916 - 2*mc 596*mc 916 + 4*mc 276*mc 596*mc 916) + 2 * KeccakfPermAir.extraction.inter_436 c row := by
    simp only [KeccakfPermAir.extraction.inter_438, KeccakfPermAir.extraction.inter_437, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_436 c row = (mc 277 + mc 597 + mc 917 - 2*mc 277*mc 597 - 2*mc 277*mc 917 - 2*mc 597*mc 917 + 4*mc 277*mc 597*mc 917) + 2 * KeccakfPermAir.extraction.inter_434 c row := by
    simp only [KeccakfPermAir.extraction.inter_436, KeccakfPermAir.extraction.inter_435, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_434 c row = (mc 278 + mc 598 + mc 918 - 2*mc 278*mc 598 - 2*mc 278*mc 918 - 2*mc 598*mc 918 + 4*mc 278*mc 598*mc 918) + 2 * KeccakfPermAir.extraction.inter_432 c row := by
    simp only [KeccakfPermAir.extraction.inter_434, KeccakfPermAir.extraction.inter_433, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_432 c row = (mc 279 + mc 599 + mc 919 - 2*mc 279*mc 599 - 2*mc 279*mc 919 - 2*mc 599*mc 919 + 4*mc 279*mc 599*mc 919) + 2 * KeccakfPermAir.extraction.inter_430 c row := by
    simp only [KeccakfPermAir.extraction.inter_432, KeccakfPermAir.extraction.inter_431, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_430 c row = (mc 280 + mc 600 + mc 920 - 2*mc 280*mc 600 - 2*mc 280*mc 920 - 2*mc 600*mc 920 + 4*mc 280*mc 600*mc 920) + 2 * KeccakfPermAir.extraction.inter_428 c row := by
    simp only [KeccakfPermAir.extraction.inter_430, KeccakfPermAir.extraction.inter_429, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_428 c row = (mc 281 + mc 601 + mc 921 - 2*mc 281*mc 601 - 2*mc 281*mc 921 - 2*mc 601*mc 921 + 4*mc 281*mc 601*mc 921) + 2 * KeccakfPermAir.extraction.inter_426 c row := by
    simp only [KeccakfPermAir.extraction.inter_428, KeccakfPermAir.extraction.inter_427, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_426 c row = (mc 282 + mc 602 + mc 922 - 2*mc 282*mc 602 - 2*mc 282*mc 922 - 2*mc 602*mc 922 + 4*mc 282*mc 602*mc 922) + 2 * KeccakfPermAir.extraction.inter_424 c row := by
    simp only [KeccakfPermAir.extraction.inter_426, KeccakfPermAir.extraction.inter_425, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_424 c row = (mc 283 + mc 603 + mc 923 - 2*mc 283*mc 603 - 2*mc 283*mc 923 - 2*mc 603*mc 923 + 4*mc 283*mc 603*mc 923) + 2 * KeccakfPermAir.extraction.inter_422 c row := by
    simp only [KeccakfPermAir.extraction.inter_424, KeccakfPermAir.extraction.inter_423, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_422 c row = (mc 284 + mc 604 + mc 924 - 2*mc 284*mc 604 - 2*mc 284*mc 924 - 2*mc 604*mc 924 + 4*mc 284*mc 604*mc 924) + 2 * KeccakfPermAir.extraction.inter_420 c row := by
    simp only [KeccakfPermAir.extraction.inter_422, KeccakfPermAir.extraction.inter_421, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_420 c row = (mc 285 + mc 605 + mc 925 - 2*mc 285*mc 605 - 2*mc 285*mc 925 - 2*mc 605*mc 925 + 4*mc 285*mc 605*mc 925) + 2 * KeccakfPermAir.extraction.inter_418 c row := by
    simp only [KeccakfPermAir.extraction.inter_420, KeccakfPermAir.extraction.inter_419, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_418 c row = (mc 286 + mc 606 + mc 926 - 2*mc 286*mc 606 - 2*mc 286*mc 926 - 2*mc 606*mc 926 + 4*mc 286*mc 606*mc 926) + 2 * KeccakfPermAir.extraction.inter_416 c row := by
    simp only [KeccakfPermAir.extraction.inter_418, KeccakfPermAir.extraction.inter_417, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_416 c row = (mc 287 + mc 607 + mc 927 - 2*mc 287*mc 607 - 2*mc 287*mc 927 - 2*mc 607*mc 927 + 4*mc 287*mc 607*mc 927) + 2 * KeccakfPermAir.extraction.inter_414 c row := by
    simp only [KeccakfPermAir.extraction.inter_416, KeccakfPermAir.extraction.inter_415, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_414 c row = (mc 288 + mc 608 + mc 928 - 2*mc 288*mc 608 - 2*mc 288*mc 928 - 2*mc 608*mc 928 + 4*mc 288*mc 608*mc 928) := by
    simp only [KeccakfPermAir.extraction.inter_414, KeccakfPermAir.extraction.inter_413, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1022 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 289 609 929 129 row) :
    mc 129 = (mc 289 + mc 609 + mc 929 - 2*mc 289*mc 609 - 2*mc 289*mc 929 - 2*mc 609*mc 929 + 4*mc 289*mc 609*mc 929) + 2*(mc 290 + mc 610 + mc 930 - 2*mc 290*mc 610 - 2*mc 290*mc 930 - 2*mc 610*mc 930 + 4*mc 290*mc 610*mc 930) + 4*(mc 291 + mc 611 + mc 931 - 2*mc 291*mc 611 - 2*mc 291*mc 931 - 2*mc 611*mc 931 + 4*mc 291*mc 611*mc 931) + 8*(mc 292 + mc 612 + mc 932 - 2*mc 292*mc 612 - 2*mc 292*mc 932 - 2*mc 612*mc 932 + 4*mc 292*mc 612*mc 932) + 16*(mc 293 + mc 613 + mc 933 - 2*mc 293*mc 613 - 2*mc 293*mc 933 - 2*mc 613*mc 933 + 4*mc 293*mc 613*mc 933) + 32*(mc 294 + mc 614 + mc 934 - 2*mc 294*mc 614 - 2*mc 294*mc 934 - 2*mc 614*mc 934 + 4*mc 294*mc 614*mc 934) + 64*(mc 295 + mc 615 + mc 935 - 2*mc 295*mc 615 - 2*mc 295*mc 935 - 2*mc 615*mc 935 + 4*mc 295*mc 615*mc 935) + 128*(mc 296 + mc 616 + mc 936 - 2*mc 296*mc 616 - 2*mc 296*mc 936 - 2*mc 616*mc 936 + 4*mc 296*mc 616*mc 936) + 256*(mc 297 + mc 617 + mc 937 - 2*mc 297*mc 617 - 2*mc 297*mc 937 - 2*mc 617*mc 937 + 4*mc 297*mc 617*mc 937) + 512*(mc 298 + mc 618 + mc 938 - 2*mc 298*mc 618 - 2*mc 298*mc 938 - 2*mc 618*mc 938 + 4*mc 298*mc 618*mc 938) + 1024*(mc 299 + mc 619 + mc 939 - 2*mc 299*mc 619 - 2*mc 299*mc 939 - 2*mc 619*mc 939 + 4*mc 299*mc 619*mc 939) + 2048*(mc 300 + mc 620 + mc 940 - 2*mc 300*mc 620 - 2*mc 300*mc 940 - 2*mc 620*mc 940 + 4*mc 300*mc 620*mc 940) + 4096*(mc 301 + mc 621 + mc 941 - 2*mc 301*mc 621 - 2*mc 301*mc 941 - 2*mc 621*mc 941 + 4*mc 301*mc 621*mc 941) + 8192*(mc 302 + mc 622 + mc 942 - 2*mc 302*mc 622 - 2*mc 302*mc 942 - 2*mc 622*mc 942 + 4*mc 302*mc 622*mc 942) + 16384*(mc 303 + mc 623 + mc 943 - 2*mc 303*mc 623 - 2*mc 303*mc 943 - 2*mc 623*mc 943 + 4*mc 303*mc 623*mc 943) + 32768*(mc 304 + mc 624 + mc 944 - 2*mc 304*mc 624 - 2*mc 304*mc 944 - 2*mc 624*mc 944 + 4*mc 304*mc 624*mc 944) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1022, KeccakfPermAir.extraction.inter_474, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_473 c row = (mc 290 + mc 610 + mc 930 - 2*mc 290*mc 610 - 2*mc 290*mc 930 - 2*mc 610*mc 930 + 4*mc 290*mc 610*mc 930) + 2 * KeccakfPermAir.extraction.inter_471 c row := by
    simp only [KeccakfPermAir.extraction.inter_473, KeccakfPermAir.extraction.inter_472, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_471 c row = (mc 291 + mc 611 + mc 931 - 2*mc 291*mc 611 - 2*mc 291*mc 931 - 2*mc 611*mc 931 + 4*mc 291*mc 611*mc 931) + 2 * KeccakfPermAir.extraction.inter_469 c row := by
    simp only [KeccakfPermAir.extraction.inter_471, KeccakfPermAir.extraction.inter_470, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_469 c row = (mc 292 + mc 612 + mc 932 - 2*mc 292*mc 612 - 2*mc 292*mc 932 - 2*mc 612*mc 932 + 4*mc 292*mc 612*mc 932) + 2 * KeccakfPermAir.extraction.inter_467 c row := by
    simp only [KeccakfPermAir.extraction.inter_469, KeccakfPermAir.extraction.inter_468, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_467 c row = (mc 293 + mc 613 + mc 933 - 2*mc 293*mc 613 - 2*mc 293*mc 933 - 2*mc 613*mc 933 + 4*mc 293*mc 613*mc 933) + 2 * KeccakfPermAir.extraction.inter_465 c row := by
    simp only [KeccakfPermAir.extraction.inter_467, KeccakfPermAir.extraction.inter_466, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_465 c row = (mc 294 + mc 614 + mc 934 - 2*mc 294*mc 614 - 2*mc 294*mc 934 - 2*mc 614*mc 934 + 4*mc 294*mc 614*mc 934) + 2 * KeccakfPermAir.extraction.inter_463 c row := by
    simp only [KeccakfPermAir.extraction.inter_465, KeccakfPermAir.extraction.inter_464, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_463 c row = (mc 295 + mc 615 + mc 935 - 2*mc 295*mc 615 - 2*mc 295*mc 935 - 2*mc 615*mc 935 + 4*mc 295*mc 615*mc 935) + 2 * KeccakfPermAir.extraction.inter_461 c row := by
    simp only [KeccakfPermAir.extraction.inter_463, KeccakfPermAir.extraction.inter_462, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_461 c row = (mc 296 + mc 616 + mc 936 - 2*mc 296*mc 616 - 2*mc 296*mc 936 - 2*mc 616*mc 936 + 4*mc 296*mc 616*mc 936) + 2 * KeccakfPermAir.extraction.inter_459 c row := by
    simp only [KeccakfPermAir.extraction.inter_461, KeccakfPermAir.extraction.inter_460, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_459 c row = (mc 297 + mc 617 + mc 937 - 2*mc 297*mc 617 - 2*mc 297*mc 937 - 2*mc 617*mc 937 + 4*mc 297*mc 617*mc 937) + 2 * KeccakfPermAir.extraction.inter_457 c row := by
    simp only [KeccakfPermAir.extraction.inter_459, KeccakfPermAir.extraction.inter_458, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_457 c row = (mc 298 + mc 618 + mc 938 - 2*mc 298*mc 618 - 2*mc 298*mc 938 - 2*mc 618*mc 938 + 4*mc 298*mc 618*mc 938) + 2 * KeccakfPermAir.extraction.inter_455 c row := by
    simp only [KeccakfPermAir.extraction.inter_457, KeccakfPermAir.extraction.inter_456, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_455 c row = (mc 299 + mc 619 + mc 939 - 2*mc 299*mc 619 - 2*mc 299*mc 939 - 2*mc 619*mc 939 + 4*mc 299*mc 619*mc 939) + 2 * KeccakfPermAir.extraction.inter_453 c row := by
    simp only [KeccakfPermAir.extraction.inter_455, KeccakfPermAir.extraction.inter_454, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_453 c row = (mc 300 + mc 620 + mc 940 - 2*mc 300*mc 620 - 2*mc 300*mc 940 - 2*mc 620*mc 940 + 4*mc 300*mc 620*mc 940) + 2 * KeccakfPermAir.extraction.inter_451 c row := by
    simp only [KeccakfPermAir.extraction.inter_453, KeccakfPermAir.extraction.inter_452, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_451 c row = (mc 301 + mc 621 + mc 941 - 2*mc 301*mc 621 - 2*mc 301*mc 941 - 2*mc 621*mc 941 + 4*mc 301*mc 621*mc 941) + 2 * KeccakfPermAir.extraction.inter_449 c row := by
    simp only [KeccakfPermAir.extraction.inter_451, KeccakfPermAir.extraction.inter_450, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_449 c row = (mc 302 + mc 622 + mc 942 - 2*mc 302*mc 622 - 2*mc 302*mc 942 - 2*mc 622*mc 942 + 4*mc 302*mc 622*mc 942) + 2 * KeccakfPermAir.extraction.inter_447 c row := by
    simp only [KeccakfPermAir.extraction.inter_449, KeccakfPermAir.extraction.inter_448, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_447 c row = (mc 303 + mc 623 + mc 943 - 2*mc 303*mc 623 - 2*mc 303*mc 943 - 2*mc 623*mc 943 + 4*mc 303*mc 623*mc 943) + 2 * KeccakfPermAir.extraction.inter_445 c row := by
    simp only [KeccakfPermAir.extraction.inter_447, KeccakfPermAir.extraction.inter_446, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_445 c row = (mc 304 + mc 624 + mc 944 - 2*mc 304*mc 624 - 2*mc 304*mc 944 - 2*mc 624*mc 944 + 4*mc 304*mc 624*mc 944) := by
    simp only [KeccakfPermAir.extraction.inter_445, KeccakfPermAir.extraction.inter_444, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1023 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 305 625 945 130 row) :
    mc 130 = (mc 305 + mc 625 + mc 945 - 2*mc 305*mc 625 - 2*mc 305*mc 945 - 2*mc 625*mc 945 + 4*mc 305*mc 625*mc 945) + 2*(mc 306 + mc 626 + mc 946 - 2*mc 306*mc 626 - 2*mc 306*mc 946 - 2*mc 626*mc 946 + 4*mc 306*mc 626*mc 946) + 4*(mc 307 + mc 627 + mc 947 - 2*mc 307*mc 627 - 2*mc 307*mc 947 - 2*mc 627*mc 947 + 4*mc 307*mc 627*mc 947) + 8*(mc 308 + mc 628 + mc 948 - 2*mc 308*mc 628 - 2*mc 308*mc 948 - 2*mc 628*mc 948 + 4*mc 308*mc 628*mc 948) + 16*(mc 309 + mc 629 + mc 949 - 2*mc 309*mc 629 - 2*mc 309*mc 949 - 2*mc 629*mc 949 + 4*mc 309*mc 629*mc 949) + 32*(mc 310 + mc 630 + mc 950 - 2*mc 310*mc 630 - 2*mc 310*mc 950 - 2*mc 630*mc 950 + 4*mc 310*mc 630*mc 950) + 64*(mc 311 + mc 631 + mc 951 - 2*mc 311*mc 631 - 2*mc 311*mc 951 - 2*mc 631*mc 951 + 4*mc 311*mc 631*mc 951) + 128*(mc 312 + mc 632 + mc 952 - 2*mc 312*mc 632 - 2*mc 312*mc 952 - 2*mc 632*mc 952 + 4*mc 312*mc 632*mc 952) + 256*(mc 313 + mc 633 + mc 953 - 2*mc 313*mc 633 - 2*mc 313*mc 953 - 2*mc 633*mc 953 + 4*mc 313*mc 633*mc 953) + 512*(mc 314 + mc 634 + mc 954 - 2*mc 314*mc 634 - 2*mc 314*mc 954 - 2*mc 634*mc 954 + 4*mc 314*mc 634*mc 954) + 1024*(mc 315 + mc 635 + mc 955 - 2*mc 315*mc 635 - 2*mc 315*mc 955 - 2*mc 635*mc 955 + 4*mc 315*mc 635*mc 955) + 2048*(mc 316 + mc 636 + mc 956 - 2*mc 316*mc 636 - 2*mc 316*mc 956 - 2*mc 636*mc 956 + 4*mc 316*mc 636*mc 956) + 4096*(mc 317 + mc 637 + mc 957 - 2*mc 317*mc 637 - 2*mc 317*mc 957 - 2*mc 637*mc 957 + 4*mc 317*mc 637*mc 957) + 8192*(mc 318 + mc 638 + mc 958 - 2*mc 318*mc 638 - 2*mc 318*mc 958 - 2*mc 638*mc 958 + 4*mc 318*mc 638*mc 958) + 16384*(mc 319 + mc 639 + mc 959 - 2*mc 319*mc 639 - 2*mc 319*mc 959 - 2*mc 639*mc 959 + 4*mc 319*mc 639*mc 959) + 32768*(mc 320 + mc 640 + mc 960 - 2*mc 320*mc 640 - 2*mc 320*mc 960 - 2*mc 640*mc 960 + 4*mc 320*mc 640*mc 960) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1023, KeccakfPermAir.extraction.inter_505, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_504 c row = (mc 306 + mc 626 + mc 946 - 2*mc 306*mc 626 - 2*mc 306*mc 946 - 2*mc 626*mc 946 + 4*mc 306*mc 626*mc 946) + 2 * KeccakfPermAir.extraction.inter_502 c row := by
    simp only [KeccakfPermAir.extraction.inter_504, KeccakfPermAir.extraction.inter_503, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_502 c row = (mc 307 + mc 627 + mc 947 - 2*mc 307*mc 627 - 2*mc 307*mc 947 - 2*mc 627*mc 947 + 4*mc 307*mc 627*mc 947) + 2 * KeccakfPermAir.extraction.inter_500 c row := by
    simp only [KeccakfPermAir.extraction.inter_502, KeccakfPermAir.extraction.inter_501, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_500 c row = (mc 308 + mc 628 + mc 948 - 2*mc 308*mc 628 - 2*mc 308*mc 948 - 2*mc 628*mc 948 + 4*mc 308*mc 628*mc 948) + 2 * KeccakfPermAir.extraction.inter_498 c row := by
    simp only [KeccakfPermAir.extraction.inter_500, KeccakfPermAir.extraction.inter_499, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_498 c row = (mc 309 + mc 629 + mc 949 - 2*mc 309*mc 629 - 2*mc 309*mc 949 - 2*mc 629*mc 949 + 4*mc 309*mc 629*mc 949) + 2 * KeccakfPermAir.extraction.inter_496 c row := by
    simp only [KeccakfPermAir.extraction.inter_498, KeccakfPermAir.extraction.inter_497, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_496 c row = (mc 310 + mc 630 + mc 950 - 2*mc 310*mc 630 - 2*mc 310*mc 950 - 2*mc 630*mc 950 + 4*mc 310*mc 630*mc 950) + 2 * KeccakfPermAir.extraction.inter_494 c row := by
    simp only [KeccakfPermAir.extraction.inter_496, KeccakfPermAir.extraction.inter_495, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_494 c row = (mc 311 + mc 631 + mc 951 - 2*mc 311*mc 631 - 2*mc 311*mc 951 - 2*mc 631*mc 951 + 4*mc 311*mc 631*mc 951) + 2 * KeccakfPermAir.extraction.inter_492 c row := by
    simp only [KeccakfPermAir.extraction.inter_494, KeccakfPermAir.extraction.inter_493, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_492 c row = (mc 312 + mc 632 + mc 952 - 2*mc 312*mc 632 - 2*mc 312*mc 952 - 2*mc 632*mc 952 + 4*mc 312*mc 632*mc 952) + 2 * KeccakfPermAir.extraction.inter_490 c row := by
    simp only [KeccakfPermAir.extraction.inter_492, KeccakfPermAir.extraction.inter_491, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_490 c row = (mc 313 + mc 633 + mc 953 - 2*mc 313*mc 633 - 2*mc 313*mc 953 - 2*mc 633*mc 953 + 4*mc 313*mc 633*mc 953) + 2 * KeccakfPermAir.extraction.inter_488 c row := by
    simp only [KeccakfPermAir.extraction.inter_490, KeccakfPermAir.extraction.inter_489, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_488 c row = (mc 314 + mc 634 + mc 954 - 2*mc 314*mc 634 - 2*mc 314*mc 954 - 2*mc 634*mc 954 + 4*mc 314*mc 634*mc 954) + 2 * KeccakfPermAir.extraction.inter_486 c row := by
    simp only [KeccakfPermAir.extraction.inter_488, KeccakfPermAir.extraction.inter_487, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_486 c row = (mc 315 + mc 635 + mc 955 - 2*mc 315*mc 635 - 2*mc 315*mc 955 - 2*mc 635*mc 955 + 4*mc 315*mc 635*mc 955) + 2 * KeccakfPermAir.extraction.inter_484 c row := by
    simp only [KeccakfPermAir.extraction.inter_486, KeccakfPermAir.extraction.inter_485, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_484 c row = (mc 316 + mc 636 + mc 956 - 2*mc 316*mc 636 - 2*mc 316*mc 956 - 2*mc 636*mc 956 + 4*mc 316*mc 636*mc 956) + 2 * KeccakfPermAir.extraction.inter_482 c row := by
    simp only [KeccakfPermAir.extraction.inter_484, KeccakfPermAir.extraction.inter_483, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_482 c row = (mc 317 + mc 637 + mc 957 - 2*mc 317*mc 637 - 2*mc 317*mc 957 - 2*mc 637*mc 957 + 4*mc 317*mc 637*mc 957) + 2 * KeccakfPermAir.extraction.inter_480 c row := by
    simp only [KeccakfPermAir.extraction.inter_482, KeccakfPermAir.extraction.inter_481, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_480 c row = (mc 318 + mc 638 + mc 958 - 2*mc 318*mc 638 - 2*mc 318*mc 958 - 2*mc 638*mc 958 + 4*mc 318*mc 638*mc 958) + 2 * KeccakfPermAir.extraction.inter_478 c row := by
    simp only [KeccakfPermAir.extraction.inter_480, KeccakfPermAir.extraction.inter_479, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_478 c row = (mc 319 + mc 639 + mc 959 - 2*mc 319*mc 639 - 2*mc 319*mc 959 - 2*mc 639*mc 959 + 4*mc 319*mc 639*mc 959) + 2 * KeccakfPermAir.extraction.inter_476 c row := by
    simp only [KeccakfPermAir.extraction.inter_478, KeccakfPermAir.extraction.inter_477, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_476 c row = (mc 320 + mc 640 + mc 960 - 2*mc 320*mc 640 - 2*mc 320*mc 960 - 2*mc 640*mc 960 + 4*mc 320*mc 640*mc 960) := by
    simp only [KeccakfPermAir.extraction.inter_476, KeccakfPermAir.extraction.inter_475, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1024 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 321 641 961 131 row) :
    mc 131 = (mc 321 + mc 641 + mc 961 - 2*mc 321*mc 641 - 2*mc 321*mc 961 - 2*mc 641*mc 961 + 4*mc 321*mc 641*mc 961) + 2*(mc 322 + mc 642 + mc 962 - 2*mc 322*mc 642 - 2*mc 322*mc 962 - 2*mc 642*mc 962 + 4*mc 322*mc 642*mc 962) + 4*(mc 323 + mc 643 + mc 963 - 2*mc 323*mc 643 - 2*mc 323*mc 963 - 2*mc 643*mc 963 + 4*mc 323*mc 643*mc 963) + 8*(mc 324 + mc 644 + mc 964 - 2*mc 324*mc 644 - 2*mc 324*mc 964 - 2*mc 644*mc 964 + 4*mc 324*mc 644*mc 964) + 16*(mc 325 + mc 645 + mc 965 - 2*mc 325*mc 645 - 2*mc 325*mc 965 - 2*mc 645*mc 965 + 4*mc 325*mc 645*mc 965) + 32*(mc 326 + mc 646 + mc 966 - 2*mc 326*mc 646 - 2*mc 326*mc 966 - 2*mc 646*mc 966 + 4*mc 326*mc 646*mc 966) + 64*(mc 327 + mc 647 + mc 967 - 2*mc 327*mc 647 - 2*mc 327*mc 967 - 2*mc 647*mc 967 + 4*mc 327*mc 647*mc 967) + 128*(mc 328 + mc 648 + mc 968 - 2*mc 328*mc 648 - 2*mc 328*mc 968 - 2*mc 648*mc 968 + 4*mc 328*mc 648*mc 968) + 256*(mc 329 + mc 649 + mc 969 - 2*mc 329*mc 649 - 2*mc 329*mc 969 - 2*mc 649*mc 969 + 4*mc 329*mc 649*mc 969) + 512*(mc 330 + mc 650 + mc 970 - 2*mc 330*mc 650 - 2*mc 330*mc 970 - 2*mc 650*mc 970 + 4*mc 330*mc 650*mc 970) + 1024*(mc 331 + mc 651 + mc 971 - 2*mc 331*mc 651 - 2*mc 331*mc 971 - 2*mc 651*mc 971 + 4*mc 331*mc 651*mc 971) + 2048*(mc 332 + mc 652 + mc 972 - 2*mc 332*mc 652 - 2*mc 332*mc 972 - 2*mc 652*mc 972 + 4*mc 332*mc 652*mc 972) + 4096*(mc 333 + mc 653 + mc 973 - 2*mc 333*mc 653 - 2*mc 333*mc 973 - 2*mc 653*mc 973 + 4*mc 333*mc 653*mc 973) + 8192*(mc 334 + mc 654 + mc 974 - 2*mc 334*mc 654 - 2*mc 334*mc 974 - 2*mc 654*mc 974 + 4*mc 334*mc 654*mc 974) + 16384*(mc 335 + mc 655 + mc 975 - 2*mc 335*mc 655 - 2*mc 335*mc 975 - 2*mc 655*mc 975 + 4*mc 335*mc 655*mc 975) + 32768*(mc 336 + mc 656 + mc 976 - 2*mc 336*mc 656 - 2*mc 336*mc 976 - 2*mc 656*mc 976 + 4*mc 336*mc 656*mc 976) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1024, KeccakfPermAir.extraction.inter_536, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_535 c row = (mc 322 + mc 642 + mc 962 - 2*mc 322*mc 642 - 2*mc 322*mc 962 - 2*mc 642*mc 962 + 4*mc 322*mc 642*mc 962) + 2 * KeccakfPermAir.extraction.inter_533 c row := by
    simp only [KeccakfPermAir.extraction.inter_535, KeccakfPermAir.extraction.inter_534, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_533 c row = (mc 323 + mc 643 + mc 963 - 2*mc 323*mc 643 - 2*mc 323*mc 963 - 2*mc 643*mc 963 + 4*mc 323*mc 643*mc 963) + 2 * KeccakfPermAir.extraction.inter_531 c row := by
    simp only [KeccakfPermAir.extraction.inter_533, KeccakfPermAir.extraction.inter_532, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_531 c row = (mc 324 + mc 644 + mc 964 - 2*mc 324*mc 644 - 2*mc 324*mc 964 - 2*mc 644*mc 964 + 4*mc 324*mc 644*mc 964) + 2 * KeccakfPermAir.extraction.inter_529 c row := by
    simp only [KeccakfPermAir.extraction.inter_531, KeccakfPermAir.extraction.inter_530, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_529 c row = (mc 325 + mc 645 + mc 965 - 2*mc 325*mc 645 - 2*mc 325*mc 965 - 2*mc 645*mc 965 + 4*mc 325*mc 645*mc 965) + 2 * KeccakfPermAir.extraction.inter_527 c row := by
    simp only [KeccakfPermAir.extraction.inter_529, KeccakfPermAir.extraction.inter_528, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_527 c row = (mc 326 + mc 646 + mc 966 - 2*mc 326*mc 646 - 2*mc 326*mc 966 - 2*mc 646*mc 966 + 4*mc 326*mc 646*mc 966) + 2 * KeccakfPermAir.extraction.inter_525 c row := by
    simp only [KeccakfPermAir.extraction.inter_527, KeccakfPermAir.extraction.inter_526, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_525 c row = (mc 327 + mc 647 + mc 967 - 2*mc 327*mc 647 - 2*mc 327*mc 967 - 2*mc 647*mc 967 + 4*mc 327*mc 647*mc 967) + 2 * KeccakfPermAir.extraction.inter_523 c row := by
    simp only [KeccakfPermAir.extraction.inter_525, KeccakfPermAir.extraction.inter_524, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_523 c row = (mc 328 + mc 648 + mc 968 - 2*mc 328*mc 648 - 2*mc 328*mc 968 - 2*mc 648*mc 968 + 4*mc 328*mc 648*mc 968) + 2 * KeccakfPermAir.extraction.inter_521 c row := by
    simp only [KeccakfPermAir.extraction.inter_523, KeccakfPermAir.extraction.inter_522, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_521 c row = (mc 329 + mc 649 + mc 969 - 2*mc 329*mc 649 - 2*mc 329*mc 969 - 2*mc 649*mc 969 + 4*mc 329*mc 649*mc 969) + 2 * KeccakfPermAir.extraction.inter_519 c row := by
    simp only [KeccakfPermAir.extraction.inter_521, KeccakfPermAir.extraction.inter_520, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_519 c row = (mc 330 + mc 650 + mc 970 - 2*mc 330*mc 650 - 2*mc 330*mc 970 - 2*mc 650*mc 970 + 4*mc 330*mc 650*mc 970) + 2 * KeccakfPermAir.extraction.inter_517 c row := by
    simp only [KeccakfPermAir.extraction.inter_519, KeccakfPermAir.extraction.inter_518, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_517 c row = (mc 331 + mc 651 + mc 971 - 2*mc 331*mc 651 - 2*mc 331*mc 971 - 2*mc 651*mc 971 + 4*mc 331*mc 651*mc 971) + 2 * KeccakfPermAir.extraction.inter_515 c row := by
    simp only [KeccakfPermAir.extraction.inter_517, KeccakfPermAir.extraction.inter_516, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_515 c row = (mc 332 + mc 652 + mc 972 - 2*mc 332*mc 652 - 2*mc 332*mc 972 - 2*mc 652*mc 972 + 4*mc 332*mc 652*mc 972) + 2 * KeccakfPermAir.extraction.inter_513 c row := by
    simp only [KeccakfPermAir.extraction.inter_515, KeccakfPermAir.extraction.inter_514, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_513 c row = (mc 333 + mc 653 + mc 973 - 2*mc 333*mc 653 - 2*mc 333*mc 973 - 2*mc 653*mc 973 + 4*mc 333*mc 653*mc 973) + 2 * KeccakfPermAir.extraction.inter_511 c row := by
    simp only [KeccakfPermAir.extraction.inter_513, KeccakfPermAir.extraction.inter_512, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_511 c row = (mc 334 + mc 654 + mc 974 - 2*mc 334*mc 654 - 2*mc 334*mc 974 - 2*mc 654*mc 974 + 4*mc 334*mc 654*mc 974) + 2 * KeccakfPermAir.extraction.inter_509 c row := by
    simp only [KeccakfPermAir.extraction.inter_511, KeccakfPermAir.extraction.inter_510, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_509 c row = (mc 335 + mc 655 + mc 975 - 2*mc 335*mc 655 - 2*mc 335*mc 975 - 2*mc 655*mc 975 + 4*mc 335*mc 655*mc 975) + 2 * KeccakfPermAir.extraction.inter_507 c row := by
    simp only [KeccakfPermAir.extraction.inter_509, KeccakfPermAir.extraction.inter_508, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_507 c row = (mc 336 + mc 656 + mc 976 - 2*mc 336*mc 656 - 2*mc 336*mc 976 - 2*mc 656*mc 976 + 4*mc 336*mc 656*mc 976) := by
    simp only [KeccakfPermAir.extraction.inter_507, KeccakfPermAir.extraction.inter_506, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1025 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 337 657 977 132 row) :
    mc 132 = (mc 337 + mc 657 + mc 977 - 2*mc 337*mc 657 - 2*mc 337*mc 977 - 2*mc 657*mc 977 + 4*mc 337*mc 657*mc 977) + 2*(mc 338 + mc 658 + mc 978 - 2*mc 338*mc 658 - 2*mc 338*mc 978 - 2*mc 658*mc 978 + 4*mc 338*mc 658*mc 978) + 4*(mc 339 + mc 659 + mc 979 - 2*mc 339*mc 659 - 2*mc 339*mc 979 - 2*mc 659*mc 979 + 4*mc 339*mc 659*mc 979) + 8*(mc 340 + mc 660 + mc 980 - 2*mc 340*mc 660 - 2*mc 340*mc 980 - 2*mc 660*mc 980 + 4*mc 340*mc 660*mc 980) + 16*(mc 341 + mc 661 + mc 981 - 2*mc 341*mc 661 - 2*mc 341*mc 981 - 2*mc 661*mc 981 + 4*mc 341*mc 661*mc 981) + 32*(mc 342 + mc 662 + mc 982 - 2*mc 342*mc 662 - 2*mc 342*mc 982 - 2*mc 662*mc 982 + 4*mc 342*mc 662*mc 982) + 64*(mc 343 + mc 663 + mc 983 - 2*mc 343*mc 663 - 2*mc 343*mc 983 - 2*mc 663*mc 983 + 4*mc 343*mc 663*mc 983) + 128*(mc 344 + mc 664 + mc 984 - 2*mc 344*mc 664 - 2*mc 344*mc 984 - 2*mc 664*mc 984 + 4*mc 344*mc 664*mc 984) + 256*(mc 345 + mc 665 + mc 985 - 2*mc 345*mc 665 - 2*mc 345*mc 985 - 2*mc 665*mc 985 + 4*mc 345*mc 665*mc 985) + 512*(mc 346 + mc 666 + mc 986 - 2*mc 346*mc 666 - 2*mc 346*mc 986 - 2*mc 666*mc 986 + 4*mc 346*mc 666*mc 986) + 1024*(mc 347 + mc 667 + mc 987 - 2*mc 347*mc 667 - 2*mc 347*mc 987 - 2*mc 667*mc 987 + 4*mc 347*mc 667*mc 987) + 2048*(mc 348 + mc 668 + mc 988 - 2*mc 348*mc 668 - 2*mc 348*mc 988 - 2*mc 668*mc 988 + 4*mc 348*mc 668*mc 988) + 4096*(mc 349 + mc 669 + mc 989 - 2*mc 349*mc 669 - 2*mc 349*mc 989 - 2*mc 669*mc 989 + 4*mc 349*mc 669*mc 989) + 8192*(mc 350 + mc 670 + mc 990 - 2*mc 350*mc 670 - 2*mc 350*mc 990 - 2*mc 670*mc 990 + 4*mc 350*mc 670*mc 990) + 16384*(mc 351 + mc 671 + mc 991 - 2*mc 351*mc 671 - 2*mc 351*mc 991 - 2*mc 671*mc 991 + 4*mc 351*mc 671*mc 991) + 32768*(mc 352 + mc 672 + mc 992 - 2*mc 352*mc 672 - 2*mc 352*mc 992 - 2*mc 672*mc 992 + 4*mc 352*mc 672*mc 992) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1025, KeccakfPermAir.extraction.inter_567, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_566 c row = (mc 338 + mc 658 + mc 978 - 2*mc 338*mc 658 - 2*mc 338*mc 978 - 2*mc 658*mc 978 + 4*mc 338*mc 658*mc 978) + 2 * KeccakfPermAir.extraction.inter_564 c row := by
    simp only [KeccakfPermAir.extraction.inter_566, KeccakfPermAir.extraction.inter_565, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_564 c row = (mc 339 + mc 659 + mc 979 - 2*mc 339*mc 659 - 2*mc 339*mc 979 - 2*mc 659*mc 979 + 4*mc 339*mc 659*mc 979) + 2 * KeccakfPermAir.extraction.inter_562 c row := by
    simp only [KeccakfPermAir.extraction.inter_564, KeccakfPermAir.extraction.inter_563, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_562 c row = (mc 340 + mc 660 + mc 980 - 2*mc 340*mc 660 - 2*mc 340*mc 980 - 2*mc 660*mc 980 + 4*mc 340*mc 660*mc 980) + 2 * KeccakfPermAir.extraction.inter_560 c row := by
    simp only [KeccakfPermAir.extraction.inter_562, KeccakfPermAir.extraction.inter_561, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_560 c row = (mc 341 + mc 661 + mc 981 - 2*mc 341*mc 661 - 2*mc 341*mc 981 - 2*mc 661*mc 981 + 4*mc 341*mc 661*mc 981) + 2 * KeccakfPermAir.extraction.inter_558 c row := by
    simp only [KeccakfPermAir.extraction.inter_560, KeccakfPermAir.extraction.inter_559, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_558 c row = (mc 342 + mc 662 + mc 982 - 2*mc 342*mc 662 - 2*mc 342*mc 982 - 2*mc 662*mc 982 + 4*mc 342*mc 662*mc 982) + 2 * KeccakfPermAir.extraction.inter_556 c row := by
    simp only [KeccakfPermAir.extraction.inter_558, KeccakfPermAir.extraction.inter_557, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_556 c row = (mc 343 + mc 663 + mc 983 - 2*mc 343*mc 663 - 2*mc 343*mc 983 - 2*mc 663*mc 983 + 4*mc 343*mc 663*mc 983) + 2 * KeccakfPermAir.extraction.inter_554 c row := by
    simp only [KeccakfPermAir.extraction.inter_556, KeccakfPermAir.extraction.inter_555, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_554 c row = (mc 344 + mc 664 + mc 984 - 2*mc 344*mc 664 - 2*mc 344*mc 984 - 2*mc 664*mc 984 + 4*mc 344*mc 664*mc 984) + 2 * KeccakfPermAir.extraction.inter_552 c row := by
    simp only [KeccakfPermAir.extraction.inter_554, KeccakfPermAir.extraction.inter_553, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_552 c row = (mc 345 + mc 665 + mc 985 - 2*mc 345*mc 665 - 2*mc 345*mc 985 - 2*mc 665*mc 985 + 4*mc 345*mc 665*mc 985) + 2 * KeccakfPermAir.extraction.inter_550 c row := by
    simp only [KeccakfPermAir.extraction.inter_552, KeccakfPermAir.extraction.inter_551, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_550 c row = (mc 346 + mc 666 + mc 986 - 2*mc 346*mc 666 - 2*mc 346*mc 986 - 2*mc 666*mc 986 + 4*mc 346*mc 666*mc 986) + 2 * KeccakfPermAir.extraction.inter_548 c row := by
    simp only [KeccakfPermAir.extraction.inter_550, KeccakfPermAir.extraction.inter_549, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_548 c row = (mc 347 + mc 667 + mc 987 - 2*mc 347*mc 667 - 2*mc 347*mc 987 - 2*mc 667*mc 987 + 4*mc 347*mc 667*mc 987) + 2 * KeccakfPermAir.extraction.inter_546 c row := by
    simp only [KeccakfPermAir.extraction.inter_548, KeccakfPermAir.extraction.inter_547, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_546 c row = (mc 348 + mc 668 + mc 988 - 2*mc 348*mc 668 - 2*mc 348*mc 988 - 2*mc 668*mc 988 + 4*mc 348*mc 668*mc 988) + 2 * KeccakfPermAir.extraction.inter_544 c row := by
    simp only [KeccakfPermAir.extraction.inter_546, KeccakfPermAir.extraction.inter_545, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_544 c row = (mc 349 + mc 669 + mc 989 - 2*mc 349*mc 669 - 2*mc 349*mc 989 - 2*mc 669*mc 989 + 4*mc 349*mc 669*mc 989) + 2 * KeccakfPermAir.extraction.inter_542 c row := by
    simp only [KeccakfPermAir.extraction.inter_544, KeccakfPermAir.extraction.inter_543, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_542 c row = (mc 350 + mc 670 + mc 990 - 2*mc 350*mc 670 - 2*mc 350*mc 990 - 2*mc 670*mc 990 + 4*mc 350*mc 670*mc 990) + 2 * KeccakfPermAir.extraction.inter_540 c row := by
    simp only [KeccakfPermAir.extraction.inter_542, KeccakfPermAir.extraction.inter_541, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_540 c row = (mc 351 + mc 671 + mc 991 - 2*mc 351*mc 671 - 2*mc 351*mc 991 - 2*mc 671*mc 991 + 4*mc 351*mc 671*mc 991) + 2 * KeccakfPermAir.extraction.inter_538 c row := by
    simp only [KeccakfPermAir.extraction.inter_540, KeccakfPermAir.extraction.inter_539, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_538 c row = (mc 352 + mc 672 + mc 992 - 2*mc 352*mc 672 - 2*mc 352*mc 992 - 2*mc 672*mc 992 + 4*mc 352*mc 672*mc 992) := by
    simp only [KeccakfPermAir.extraction.inter_538, KeccakfPermAir.extraction.inter_537, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1090 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 353 673 993 133 row) :
    mc 133 = (mc 353 + mc 673 + mc 993 - 2*mc 353*mc 673 - 2*mc 353*mc 993 - 2*mc 673*mc 993 + 4*mc 353*mc 673*mc 993) + 2*(mc 354 + mc 674 + mc 994 - 2*mc 354*mc 674 - 2*mc 354*mc 994 - 2*mc 674*mc 994 + 4*mc 354*mc 674*mc 994) + 4*(mc 355 + mc 675 + mc 995 - 2*mc 355*mc 675 - 2*mc 355*mc 995 - 2*mc 675*mc 995 + 4*mc 355*mc 675*mc 995) + 8*(mc 356 + mc 676 + mc 996 - 2*mc 356*mc 676 - 2*mc 356*mc 996 - 2*mc 676*mc 996 + 4*mc 356*mc 676*mc 996) + 16*(mc 357 + mc 677 + mc 997 - 2*mc 357*mc 677 - 2*mc 357*mc 997 - 2*mc 677*mc 997 + 4*mc 357*mc 677*mc 997) + 32*(mc 358 + mc 678 + mc 998 - 2*mc 358*mc 678 - 2*mc 358*mc 998 - 2*mc 678*mc 998 + 4*mc 358*mc 678*mc 998) + 64*(mc 359 + mc 679 + mc 999 - 2*mc 359*mc 679 - 2*mc 359*mc 999 - 2*mc 679*mc 999 + 4*mc 359*mc 679*mc 999) + 128*(mc 360 + mc 680 + mc 1000 - 2*mc 360*mc 680 - 2*mc 360*mc 1000 - 2*mc 680*mc 1000 + 4*mc 360*mc 680*mc 1000) + 256*(mc 361 + mc 681 + mc 1001 - 2*mc 361*mc 681 - 2*mc 361*mc 1001 - 2*mc 681*mc 1001 + 4*mc 361*mc 681*mc 1001) + 512*(mc 362 + mc 682 + mc 1002 - 2*mc 362*mc 682 - 2*mc 362*mc 1002 - 2*mc 682*mc 1002 + 4*mc 362*mc 682*mc 1002) + 1024*(mc 363 + mc 683 + mc 1003 - 2*mc 363*mc 683 - 2*mc 363*mc 1003 - 2*mc 683*mc 1003 + 4*mc 363*mc 683*mc 1003) + 2048*(mc 364 + mc 684 + mc 1004 - 2*mc 364*mc 684 - 2*mc 364*mc 1004 - 2*mc 684*mc 1004 + 4*mc 364*mc 684*mc 1004) + 4096*(mc 365 + mc 685 + mc 1005 - 2*mc 365*mc 685 - 2*mc 365*mc 1005 - 2*mc 685*mc 1005 + 4*mc 365*mc 685*mc 1005) + 8192*(mc 366 + mc 686 + mc 1006 - 2*mc 366*mc 686 - 2*mc 366*mc 1006 - 2*mc 686*mc 1006 + 4*mc 366*mc 686*mc 1006) + 16384*(mc 367 + mc 687 + mc 1007 - 2*mc 367*mc 687 - 2*mc 367*mc 1007 - 2*mc 687*mc 1007 + 4*mc 367*mc 687*mc 1007) + 32768*(mc 368 + mc 688 + mc 1008 - 2*mc 368*mc 688 - 2*mc 368*mc 1008 - 2*mc 688*mc 1008 + 4*mc 368*mc 688*mc 1008) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1090, KeccakfPermAir.extraction.inter_598, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_597 c row = (mc 354 + mc 674 + mc 994 - 2*mc 354*mc 674 - 2*mc 354*mc 994 - 2*mc 674*mc 994 + 4*mc 354*mc 674*mc 994) + 2 * KeccakfPermAir.extraction.inter_595 c row := by
    simp only [KeccakfPermAir.extraction.inter_597, KeccakfPermAir.extraction.inter_596, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_595 c row = (mc 355 + mc 675 + mc 995 - 2*mc 355*mc 675 - 2*mc 355*mc 995 - 2*mc 675*mc 995 + 4*mc 355*mc 675*mc 995) + 2 * KeccakfPermAir.extraction.inter_593 c row := by
    simp only [KeccakfPermAir.extraction.inter_595, KeccakfPermAir.extraction.inter_594, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_593 c row = (mc 356 + mc 676 + mc 996 - 2*mc 356*mc 676 - 2*mc 356*mc 996 - 2*mc 676*mc 996 + 4*mc 356*mc 676*mc 996) + 2 * KeccakfPermAir.extraction.inter_591 c row := by
    simp only [KeccakfPermAir.extraction.inter_593, KeccakfPermAir.extraction.inter_592, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_591 c row = (mc 357 + mc 677 + mc 997 - 2*mc 357*mc 677 - 2*mc 357*mc 997 - 2*mc 677*mc 997 + 4*mc 357*mc 677*mc 997) + 2 * KeccakfPermAir.extraction.inter_589 c row := by
    simp only [KeccakfPermAir.extraction.inter_591, KeccakfPermAir.extraction.inter_590, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_589 c row = (mc 358 + mc 678 + mc 998 - 2*mc 358*mc 678 - 2*mc 358*mc 998 - 2*mc 678*mc 998 + 4*mc 358*mc 678*mc 998) + 2 * KeccakfPermAir.extraction.inter_587 c row := by
    simp only [KeccakfPermAir.extraction.inter_589, KeccakfPermAir.extraction.inter_588, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_587 c row = (mc 359 + mc 679 + mc 999 - 2*mc 359*mc 679 - 2*mc 359*mc 999 - 2*mc 679*mc 999 + 4*mc 359*mc 679*mc 999) + 2 * KeccakfPermAir.extraction.inter_585 c row := by
    simp only [KeccakfPermAir.extraction.inter_587, KeccakfPermAir.extraction.inter_586, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_585 c row = (mc 360 + mc 680 + mc 1000 - 2*mc 360*mc 680 - 2*mc 360*mc 1000 - 2*mc 680*mc 1000 + 4*mc 360*mc 680*mc 1000) + 2 * KeccakfPermAir.extraction.inter_583 c row := by
    simp only [KeccakfPermAir.extraction.inter_585, KeccakfPermAir.extraction.inter_584, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_583 c row = (mc 361 + mc 681 + mc 1001 - 2*mc 361*mc 681 - 2*mc 361*mc 1001 - 2*mc 681*mc 1001 + 4*mc 361*mc 681*mc 1001) + 2 * KeccakfPermAir.extraction.inter_581 c row := by
    simp only [KeccakfPermAir.extraction.inter_583, KeccakfPermAir.extraction.inter_582, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_581 c row = (mc 362 + mc 682 + mc 1002 - 2*mc 362*mc 682 - 2*mc 362*mc 1002 - 2*mc 682*mc 1002 + 4*mc 362*mc 682*mc 1002) + 2 * KeccakfPermAir.extraction.inter_579 c row := by
    simp only [KeccakfPermAir.extraction.inter_581, KeccakfPermAir.extraction.inter_580, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_579 c row = (mc 363 + mc 683 + mc 1003 - 2*mc 363*mc 683 - 2*mc 363*mc 1003 - 2*mc 683*mc 1003 + 4*mc 363*mc 683*mc 1003) + 2 * KeccakfPermAir.extraction.inter_577 c row := by
    simp only [KeccakfPermAir.extraction.inter_579, KeccakfPermAir.extraction.inter_578, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_577 c row = (mc 364 + mc 684 + mc 1004 - 2*mc 364*mc 684 - 2*mc 364*mc 1004 - 2*mc 684*mc 1004 + 4*mc 364*mc 684*mc 1004) + 2 * KeccakfPermAir.extraction.inter_575 c row := by
    simp only [KeccakfPermAir.extraction.inter_577, KeccakfPermAir.extraction.inter_576, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_575 c row = (mc 365 + mc 685 + mc 1005 - 2*mc 365*mc 685 - 2*mc 365*mc 1005 - 2*mc 685*mc 1005 + 4*mc 365*mc 685*mc 1005) + 2 * KeccakfPermAir.extraction.inter_573 c row := by
    simp only [KeccakfPermAir.extraction.inter_575, KeccakfPermAir.extraction.inter_574, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_573 c row = (mc 366 + mc 686 + mc 1006 - 2*mc 366*mc 686 - 2*mc 366*mc 1006 - 2*mc 686*mc 1006 + 4*mc 366*mc 686*mc 1006) + 2 * KeccakfPermAir.extraction.inter_571 c row := by
    simp only [KeccakfPermAir.extraction.inter_573, KeccakfPermAir.extraction.inter_572, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_571 c row = (mc 367 + mc 687 + mc 1007 - 2*mc 367*mc 687 - 2*mc 367*mc 1007 - 2*mc 687*mc 1007 + 4*mc 367*mc 687*mc 1007) + 2 * KeccakfPermAir.extraction.inter_569 c row := by
    simp only [KeccakfPermAir.extraction.inter_571, KeccakfPermAir.extraction.inter_570, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_569 c row = (mc 368 + mc 688 + mc 1008 - 2*mc 368*mc 688 - 2*mc 368*mc 1008 - 2*mc 688*mc 1008 + 4*mc 368*mc 688*mc 1008) := by
    simp only [KeccakfPermAir.extraction.inter_569, KeccakfPermAir.extraction.inter_568, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1091 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 369 689 1009 134 row) :
    mc 134 = (mc 369 + mc 689 + mc 1009 - 2*mc 369*mc 689 - 2*mc 369*mc 1009 - 2*mc 689*mc 1009 + 4*mc 369*mc 689*mc 1009) + 2*(mc 370 + mc 690 + mc 1010 - 2*mc 370*mc 690 - 2*mc 370*mc 1010 - 2*mc 690*mc 1010 + 4*mc 370*mc 690*mc 1010) + 4*(mc 371 + mc 691 + mc 1011 - 2*mc 371*mc 691 - 2*mc 371*mc 1011 - 2*mc 691*mc 1011 + 4*mc 371*mc 691*mc 1011) + 8*(mc 372 + mc 692 + mc 1012 - 2*mc 372*mc 692 - 2*mc 372*mc 1012 - 2*mc 692*mc 1012 + 4*mc 372*mc 692*mc 1012) + 16*(mc 373 + mc 693 + mc 1013 - 2*mc 373*mc 693 - 2*mc 373*mc 1013 - 2*mc 693*mc 1013 + 4*mc 373*mc 693*mc 1013) + 32*(mc 374 + mc 694 + mc 1014 - 2*mc 374*mc 694 - 2*mc 374*mc 1014 - 2*mc 694*mc 1014 + 4*mc 374*mc 694*mc 1014) + 64*(mc 375 + mc 695 + mc 1015 - 2*mc 375*mc 695 - 2*mc 375*mc 1015 - 2*mc 695*mc 1015 + 4*mc 375*mc 695*mc 1015) + 128*(mc 376 + mc 696 + mc 1016 - 2*mc 376*mc 696 - 2*mc 376*mc 1016 - 2*mc 696*mc 1016 + 4*mc 376*mc 696*mc 1016) + 256*(mc 377 + mc 697 + mc 1017 - 2*mc 377*mc 697 - 2*mc 377*mc 1017 - 2*mc 697*mc 1017 + 4*mc 377*mc 697*mc 1017) + 512*(mc 378 + mc 698 + mc 1018 - 2*mc 378*mc 698 - 2*mc 378*mc 1018 - 2*mc 698*mc 1018 + 4*mc 378*mc 698*mc 1018) + 1024*(mc 379 + mc 699 + mc 1019 - 2*mc 379*mc 699 - 2*mc 379*mc 1019 - 2*mc 699*mc 1019 + 4*mc 379*mc 699*mc 1019) + 2048*(mc 380 + mc 700 + mc 1020 - 2*mc 380*mc 700 - 2*mc 380*mc 1020 - 2*mc 700*mc 1020 + 4*mc 380*mc 700*mc 1020) + 4096*(mc 381 + mc 701 + mc 1021 - 2*mc 381*mc 701 - 2*mc 381*mc 1021 - 2*mc 701*mc 1021 + 4*mc 381*mc 701*mc 1021) + 8192*(mc 382 + mc 702 + mc 1022 - 2*mc 382*mc 702 - 2*mc 382*mc 1022 - 2*mc 702*mc 1022 + 4*mc 382*mc 702*mc 1022) + 16384*(mc 383 + mc 703 + mc 1023 - 2*mc 383*mc 703 - 2*mc 383*mc 1023 - 2*mc 703*mc 1023 + 4*mc 383*mc 703*mc 1023) + 32768*(mc 384 + mc 704 + mc 1024 - 2*mc 384*mc 704 - 2*mc 384*mc 1024 - 2*mc 704*mc 1024 + 4*mc 384*mc 704*mc 1024) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1091, KeccakfPermAir.extraction.inter_629, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_628 c row = (mc 370 + mc 690 + mc 1010 - 2*mc 370*mc 690 - 2*mc 370*mc 1010 - 2*mc 690*mc 1010 + 4*mc 370*mc 690*mc 1010) + 2 * KeccakfPermAir.extraction.inter_626 c row := by
    simp only [KeccakfPermAir.extraction.inter_628, KeccakfPermAir.extraction.inter_627, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_626 c row = (mc 371 + mc 691 + mc 1011 - 2*mc 371*mc 691 - 2*mc 371*mc 1011 - 2*mc 691*mc 1011 + 4*mc 371*mc 691*mc 1011) + 2 * KeccakfPermAir.extraction.inter_624 c row := by
    simp only [KeccakfPermAir.extraction.inter_626, KeccakfPermAir.extraction.inter_625, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_624 c row = (mc 372 + mc 692 + mc 1012 - 2*mc 372*mc 692 - 2*mc 372*mc 1012 - 2*mc 692*mc 1012 + 4*mc 372*mc 692*mc 1012) + 2 * KeccakfPermAir.extraction.inter_622 c row := by
    simp only [KeccakfPermAir.extraction.inter_624, KeccakfPermAir.extraction.inter_623, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_622 c row = (mc 373 + mc 693 + mc 1013 - 2*mc 373*mc 693 - 2*mc 373*mc 1013 - 2*mc 693*mc 1013 + 4*mc 373*mc 693*mc 1013) + 2 * KeccakfPermAir.extraction.inter_620 c row := by
    simp only [KeccakfPermAir.extraction.inter_622, KeccakfPermAir.extraction.inter_621, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_620 c row = (mc 374 + mc 694 + mc 1014 - 2*mc 374*mc 694 - 2*mc 374*mc 1014 - 2*mc 694*mc 1014 + 4*mc 374*mc 694*mc 1014) + 2 * KeccakfPermAir.extraction.inter_618 c row := by
    simp only [KeccakfPermAir.extraction.inter_620, KeccakfPermAir.extraction.inter_619, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_618 c row = (mc 375 + mc 695 + mc 1015 - 2*mc 375*mc 695 - 2*mc 375*mc 1015 - 2*mc 695*mc 1015 + 4*mc 375*mc 695*mc 1015) + 2 * KeccakfPermAir.extraction.inter_616 c row := by
    simp only [KeccakfPermAir.extraction.inter_618, KeccakfPermAir.extraction.inter_617, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_616 c row = (mc 376 + mc 696 + mc 1016 - 2*mc 376*mc 696 - 2*mc 376*mc 1016 - 2*mc 696*mc 1016 + 4*mc 376*mc 696*mc 1016) + 2 * KeccakfPermAir.extraction.inter_614 c row := by
    simp only [KeccakfPermAir.extraction.inter_616, KeccakfPermAir.extraction.inter_615, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_614 c row = (mc 377 + mc 697 + mc 1017 - 2*mc 377*mc 697 - 2*mc 377*mc 1017 - 2*mc 697*mc 1017 + 4*mc 377*mc 697*mc 1017) + 2 * KeccakfPermAir.extraction.inter_612 c row := by
    simp only [KeccakfPermAir.extraction.inter_614, KeccakfPermAir.extraction.inter_613, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_612 c row = (mc 378 + mc 698 + mc 1018 - 2*mc 378*mc 698 - 2*mc 378*mc 1018 - 2*mc 698*mc 1018 + 4*mc 378*mc 698*mc 1018) + 2 * KeccakfPermAir.extraction.inter_610 c row := by
    simp only [KeccakfPermAir.extraction.inter_612, KeccakfPermAir.extraction.inter_611, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_610 c row = (mc 379 + mc 699 + mc 1019 - 2*mc 379*mc 699 - 2*mc 379*mc 1019 - 2*mc 699*mc 1019 + 4*mc 379*mc 699*mc 1019) + 2 * KeccakfPermAir.extraction.inter_608 c row := by
    simp only [KeccakfPermAir.extraction.inter_610, KeccakfPermAir.extraction.inter_609, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_608 c row = (mc 380 + mc 700 + mc 1020 - 2*mc 380*mc 700 - 2*mc 380*mc 1020 - 2*mc 700*mc 1020 + 4*mc 380*mc 700*mc 1020) + 2 * KeccakfPermAir.extraction.inter_606 c row := by
    simp only [KeccakfPermAir.extraction.inter_608, KeccakfPermAir.extraction.inter_607, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_606 c row = (mc 381 + mc 701 + mc 1021 - 2*mc 381*mc 701 - 2*mc 381*mc 1021 - 2*mc 701*mc 1021 + 4*mc 381*mc 701*mc 1021) + 2 * KeccakfPermAir.extraction.inter_604 c row := by
    simp only [KeccakfPermAir.extraction.inter_606, KeccakfPermAir.extraction.inter_605, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_604 c row = (mc 382 + mc 702 + mc 1022 - 2*mc 382*mc 702 - 2*mc 382*mc 1022 - 2*mc 702*mc 1022 + 4*mc 382*mc 702*mc 1022) + 2 * KeccakfPermAir.extraction.inter_602 c row := by
    simp only [KeccakfPermAir.extraction.inter_604, KeccakfPermAir.extraction.inter_603, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_602 c row = (mc 383 + mc 703 + mc 1023 - 2*mc 383*mc 703 - 2*mc 383*mc 1023 - 2*mc 703*mc 1023 + 4*mc 383*mc 703*mc 1023) + 2 * KeccakfPermAir.extraction.inter_600 c row := by
    simp only [KeccakfPermAir.extraction.inter_602, KeccakfPermAir.extraction.inter_601, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_600 c row = (mc 384 + mc 704 + mc 1024 - 2*mc 384*mc 704 - 2*mc 384*mc 1024 - 2*mc 704*mc 1024 + 4*mc 384*mc 704*mc 1024) := by
    simp only [KeccakfPermAir.extraction.inter_600, KeccakfPermAir.extraction.inter_599, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1092 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 385 705 1025 135 row) :
    mc 135 = (mc 385 + mc 705 + mc 1025 - 2*mc 385*mc 705 - 2*mc 385*mc 1025 - 2*mc 705*mc 1025 + 4*mc 385*mc 705*mc 1025) + 2*(mc 386 + mc 706 + mc 1026 - 2*mc 386*mc 706 - 2*mc 386*mc 1026 - 2*mc 706*mc 1026 + 4*mc 386*mc 706*mc 1026) + 4*(mc 387 + mc 707 + mc 1027 - 2*mc 387*mc 707 - 2*mc 387*mc 1027 - 2*mc 707*mc 1027 + 4*mc 387*mc 707*mc 1027) + 8*(mc 388 + mc 708 + mc 1028 - 2*mc 388*mc 708 - 2*mc 388*mc 1028 - 2*mc 708*mc 1028 + 4*mc 388*mc 708*mc 1028) + 16*(mc 389 + mc 709 + mc 1029 - 2*mc 389*mc 709 - 2*mc 389*mc 1029 - 2*mc 709*mc 1029 + 4*mc 389*mc 709*mc 1029) + 32*(mc 390 + mc 710 + mc 1030 - 2*mc 390*mc 710 - 2*mc 390*mc 1030 - 2*mc 710*mc 1030 + 4*mc 390*mc 710*mc 1030) + 64*(mc 391 + mc 711 + mc 1031 - 2*mc 391*mc 711 - 2*mc 391*mc 1031 - 2*mc 711*mc 1031 + 4*mc 391*mc 711*mc 1031) + 128*(mc 392 + mc 712 + mc 1032 - 2*mc 392*mc 712 - 2*mc 392*mc 1032 - 2*mc 712*mc 1032 + 4*mc 392*mc 712*mc 1032) + 256*(mc 393 + mc 713 + mc 1033 - 2*mc 393*mc 713 - 2*mc 393*mc 1033 - 2*mc 713*mc 1033 + 4*mc 393*mc 713*mc 1033) + 512*(mc 394 + mc 714 + mc 1034 - 2*mc 394*mc 714 - 2*mc 394*mc 1034 - 2*mc 714*mc 1034 + 4*mc 394*mc 714*mc 1034) + 1024*(mc 395 + mc 715 + mc 1035 - 2*mc 395*mc 715 - 2*mc 395*mc 1035 - 2*mc 715*mc 1035 + 4*mc 395*mc 715*mc 1035) + 2048*(mc 396 + mc 716 + mc 1036 - 2*mc 396*mc 716 - 2*mc 396*mc 1036 - 2*mc 716*mc 1036 + 4*mc 396*mc 716*mc 1036) + 4096*(mc 397 + mc 717 + mc 1037 - 2*mc 397*mc 717 - 2*mc 397*mc 1037 - 2*mc 717*mc 1037 + 4*mc 397*mc 717*mc 1037) + 8192*(mc 398 + mc 718 + mc 1038 - 2*mc 398*mc 718 - 2*mc 398*mc 1038 - 2*mc 718*mc 1038 + 4*mc 398*mc 718*mc 1038) + 16384*(mc 399 + mc 719 + mc 1039 - 2*mc 399*mc 719 - 2*mc 399*mc 1039 - 2*mc 719*mc 1039 + 4*mc 399*mc 719*mc 1039) + 32768*(mc 400 + mc 720 + mc 1040 - 2*mc 400*mc 720 - 2*mc 400*mc 1040 - 2*mc 720*mc 1040 + 4*mc 400*mc 720*mc 1040) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1092, KeccakfPermAir.extraction.inter_660, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_659 c row = (mc 386 + mc 706 + mc 1026 - 2*mc 386*mc 706 - 2*mc 386*mc 1026 - 2*mc 706*mc 1026 + 4*mc 386*mc 706*mc 1026) + 2 * KeccakfPermAir.extraction.inter_657 c row := by
    simp only [KeccakfPermAir.extraction.inter_659, KeccakfPermAir.extraction.inter_658, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_657 c row = (mc 387 + mc 707 + mc 1027 - 2*mc 387*mc 707 - 2*mc 387*mc 1027 - 2*mc 707*mc 1027 + 4*mc 387*mc 707*mc 1027) + 2 * KeccakfPermAir.extraction.inter_655 c row := by
    simp only [KeccakfPermAir.extraction.inter_657, KeccakfPermAir.extraction.inter_656, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_655 c row = (mc 388 + mc 708 + mc 1028 - 2*mc 388*mc 708 - 2*mc 388*mc 1028 - 2*mc 708*mc 1028 + 4*mc 388*mc 708*mc 1028) + 2 * KeccakfPermAir.extraction.inter_653 c row := by
    simp only [KeccakfPermAir.extraction.inter_655, KeccakfPermAir.extraction.inter_654, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_653 c row = (mc 389 + mc 709 + mc 1029 - 2*mc 389*mc 709 - 2*mc 389*mc 1029 - 2*mc 709*mc 1029 + 4*mc 389*mc 709*mc 1029) + 2 * KeccakfPermAir.extraction.inter_651 c row := by
    simp only [KeccakfPermAir.extraction.inter_653, KeccakfPermAir.extraction.inter_652, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_651 c row = (mc 390 + mc 710 + mc 1030 - 2*mc 390*mc 710 - 2*mc 390*mc 1030 - 2*mc 710*mc 1030 + 4*mc 390*mc 710*mc 1030) + 2 * KeccakfPermAir.extraction.inter_649 c row := by
    simp only [KeccakfPermAir.extraction.inter_651, KeccakfPermAir.extraction.inter_650, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_649 c row = (mc 391 + mc 711 + mc 1031 - 2*mc 391*mc 711 - 2*mc 391*mc 1031 - 2*mc 711*mc 1031 + 4*mc 391*mc 711*mc 1031) + 2 * KeccakfPermAir.extraction.inter_647 c row := by
    simp only [KeccakfPermAir.extraction.inter_649, KeccakfPermAir.extraction.inter_648, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_647 c row = (mc 392 + mc 712 + mc 1032 - 2*mc 392*mc 712 - 2*mc 392*mc 1032 - 2*mc 712*mc 1032 + 4*mc 392*mc 712*mc 1032) + 2 * KeccakfPermAir.extraction.inter_645 c row := by
    simp only [KeccakfPermAir.extraction.inter_647, KeccakfPermAir.extraction.inter_646, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_645 c row = (mc 393 + mc 713 + mc 1033 - 2*mc 393*mc 713 - 2*mc 393*mc 1033 - 2*mc 713*mc 1033 + 4*mc 393*mc 713*mc 1033) + 2 * KeccakfPermAir.extraction.inter_643 c row := by
    simp only [KeccakfPermAir.extraction.inter_645, KeccakfPermAir.extraction.inter_644, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_643 c row = (mc 394 + mc 714 + mc 1034 - 2*mc 394*mc 714 - 2*mc 394*mc 1034 - 2*mc 714*mc 1034 + 4*mc 394*mc 714*mc 1034) + 2 * KeccakfPermAir.extraction.inter_641 c row := by
    simp only [KeccakfPermAir.extraction.inter_643, KeccakfPermAir.extraction.inter_642, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_641 c row = (mc 395 + mc 715 + mc 1035 - 2*mc 395*mc 715 - 2*mc 395*mc 1035 - 2*mc 715*mc 1035 + 4*mc 395*mc 715*mc 1035) + 2 * KeccakfPermAir.extraction.inter_639 c row := by
    simp only [KeccakfPermAir.extraction.inter_641, KeccakfPermAir.extraction.inter_640, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_639 c row = (mc 396 + mc 716 + mc 1036 - 2*mc 396*mc 716 - 2*mc 396*mc 1036 - 2*mc 716*mc 1036 + 4*mc 396*mc 716*mc 1036) + 2 * KeccakfPermAir.extraction.inter_637 c row := by
    simp only [KeccakfPermAir.extraction.inter_639, KeccakfPermAir.extraction.inter_638, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_637 c row = (mc 397 + mc 717 + mc 1037 - 2*mc 397*mc 717 - 2*mc 397*mc 1037 - 2*mc 717*mc 1037 + 4*mc 397*mc 717*mc 1037) + 2 * KeccakfPermAir.extraction.inter_635 c row := by
    simp only [KeccakfPermAir.extraction.inter_637, KeccakfPermAir.extraction.inter_636, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_635 c row = (mc 398 + mc 718 + mc 1038 - 2*mc 398*mc 718 - 2*mc 398*mc 1038 - 2*mc 718*mc 1038 + 4*mc 398*mc 718*mc 1038) + 2 * KeccakfPermAir.extraction.inter_633 c row := by
    simp only [KeccakfPermAir.extraction.inter_635, KeccakfPermAir.extraction.inter_634, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_633 c row = (mc 399 + mc 719 + mc 1039 - 2*mc 399*mc 719 - 2*mc 399*mc 1039 - 2*mc 719*mc 1039 + 4*mc 399*mc 719*mc 1039) + 2 * KeccakfPermAir.extraction.inter_631 c row := by
    simp only [KeccakfPermAir.extraction.inter_633, KeccakfPermAir.extraction.inter_632, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_631 c row = (mc 400 + mc 720 + mc 1040 - 2*mc 400*mc 720 - 2*mc 400*mc 1040 - 2*mc 720*mc 1040 + 4*mc 400*mc 720*mc 1040) := by
    simp only [KeccakfPermAir.extraction.inter_631, KeccakfPermAir.extraction.inter_630, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1093 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 401 721 1041 136 row) :
    mc 136 = (mc 401 + mc 721 + mc 1041 - 2*mc 401*mc 721 - 2*mc 401*mc 1041 - 2*mc 721*mc 1041 + 4*mc 401*mc 721*mc 1041) + 2*(mc 402 + mc 722 + mc 1042 - 2*mc 402*mc 722 - 2*mc 402*mc 1042 - 2*mc 722*mc 1042 + 4*mc 402*mc 722*mc 1042) + 4*(mc 403 + mc 723 + mc 1043 - 2*mc 403*mc 723 - 2*mc 403*mc 1043 - 2*mc 723*mc 1043 + 4*mc 403*mc 723*mc 1043) + 8*(mc 404 + mc 724 + mc 1044 - 2*mc 404*mc 724 - 2*mc 404*mc 1044 - 2*mc 724*mc 1044 + 4*mc 404*mc 724*mc 1044) + 16*(mc 405 + mc 725 + mc 1045 - 2*mc 405*mc 725 - 2*mc 405*mc 1045 - 2*mc 725*mc 1045 + 4*mc 405*mc 725*mc 1045) + 32*(mc 406 + mc 726 + mc 1046 - 2*mc 406*mc 726 - 2*mc 406*mc 1046 - 2*mc 726*mc 1046 + 4*mc 406*mc 726*mc 1046) + 64*(mc 407 + mc 727 + mc 1047 - 2*mc 407*mc 727 - 2*mc 407*mc 1047 - 2*mc 727*mc 1047 + 4*mc 407*mc 727*mc 1047) + 128*(mc 408 + mc 728 + mc 1048 - 2*mc 408*mc 728 - 2*mc 408*mc 1048 - 2*mc 728*mc 1048 + 4*mc 408*mc 728*mc 1048) + 256*(mc 409 + mc 729 + mc 1049 - 2*mc 409*mc 729 - 2*mc 409*mc 1049 - 2*mc 729*mc 1049 + 4*mc 409*mc 729*mc 1049) + 512*(mc 410 + mc 730 + mc 1050 - 2*mc 410*mc 730 - 2*mc 410*mc 1050 - 2*mc 730*mc 1050 + 4*mc 410*mc 730*mc 1050) + 1024*(mc 411 + mc 731 + mc 1051 - 2*mc 411*mc 731 - 2*mc 411*mc 1051 - 2*mc 731*mc 1051 + 4*mc 411*mc 731*mc 1051) + 2048*(mc 412 + mc 732 + mc 1052 - 2*mc 412*mc 732 - 2*mc 412*mc 1052 - 2*mc 732*mc 1052 + 4*mc 412*mc 732*mc 1052) + 4096*(mc 413 + mc 733 + mc 1053 - 2*mc 413*mc 733 - 2*mc 413*mc 1053 - 2*mc 733*mc 1053 + 4*mc 413*mc 733*mc 1053) + 8192*(mc 414 + mc 734 + mc 1054 - 2*mc 414*mc 734 - 2*mc 414*mc 1054 - 2*mc 734*mc 1054 + 4*mc 414*mc 734*mc 1054) + 16384*(mc 415 + mc 735 + mc 1055 - 2*mc 415*mc 735 - 2*mc 415*mc 1055 - 2*mc 735*mc 1055 + 4*mc 415*mc 735*mc 1055) + 32768*(mc 416 + mc 736 + mc 1056 - 2*mc 416*mc 736 - 2*mc 416*mc 1056 - 2*mc 736*mc 1056 + 4*mc 416*mc 736*mc 1056) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1093, KeccakfPermAir.extraction.inter_691, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_690 c row = (mc 402 + mc 722 + mc 1042 - 2*mc 402*mc 722 - 2*mc 402*mc 1042 - 2*mc 722*mc 1042 + 4*mc 402*mc 722*mc 1042) + 2 * KeccakfPermAir.extraction.inter_688 c row := by
    simp only [KeccakfPermAir.extraction.inter_690, KeccakfPermAir.extraction.inter_689, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_688 c row = (mc 403 + mc 723 + mc 1043 - 2*mc 403*mc 723 - 2*mc 403*mc 1043 - 2*mc 723*mc 1043 + 4*mc 403*mc 723*mc 1043) + 2 * KeccakfPermAir.extraction.inter_686 c row := by
    simp only [KeccakfPermAir.extraction.inter_688, KeccakfPermAir.extraction.inter_687, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_686 c row = (mc 404 + mc 724 + mc 1044 - 2*mc 404*mc 724 - 2*mc 404*mc 1044 - 2*mc 724*mc 1044 + 4*mc 404*mc 724*mc 1044) + 2 * KeccakfPermAir.extraction.inter_684 c row := by
    simp only [KeccakfPermAir.extraction.inter_686, KeccakfPermAir.extraction.inter_685, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_684 c row = (mc 405 + mc 725 + mc 1045 - 2*mc 405*mc 725 - 2*mc 405*mc 1045 - 2*mc 725*mc 1045 + 4*mc 405*mc 725*mc 1045) + 2 * KeccakfPermAir.extraction.inter_682 c row := by
    simp only [KeccakfPermAir.extraction.inter_684, KeccakfPermAir.extraction.inter_683, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_682 c row = (mc 406 + mc 726 + mc 1046 - 2*mc 406*mc 726 - 2*mc 406*mc 1046 - 2*mc 726*mc 1046 + 4*mc 406*mc 726*mc 1046) + 2 * KeccakfPermAir.extraction.inter_680 c row := by
    simp only [KeccakfPermAir.extraction.inter_682, KeccakfPermAir.extraction.inter_681, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_680 c row = (mc 407 + mc 727 + mc 1047 - 2*mc 407*mc 727 - 2*mc 407*mc 1047 - 2*mc 727*mc 1047 + 4*mc 407*mc 727*mc 1047) + 2 * KeccakfPermAir.extraction.inter_678 c row := by
    simp only [KeccakfPermAir.extraction.inter_680, KeccakfPermAir.extraction.inter_679, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_678 c row = (mc 408 + mc 728 + mc 1048 - 2*mc 408*mc 728 - 2*mc 408*mc 1048 - 2*mc 728*mc 1048 + 4*mc 408*mc 728*mc 1048) + 2 * KeccakfPermAir.extraction.inter_676 c row := by
    simp only [KeccakfPermAir.extraction.inter_678, KeccakfPermAir.extraction.inter_677, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_676 c row = (mc 409 + mc 729 + mc 1049 - 2*mc 409*mc 729 - 2*mc 409*mc 1049 - 2*mc 729*mc 1049 + 4*mc 409*mc 729*mc 1049) + 2 * KeccakfPermAir.extraction.inter_674 c row := by
    simp only [KeccakfPermAir.extraction.inter_676, KeccakfPermAir.extraction.inter_675, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_674 c row = (mc 410 + mc 730 + mc 1050 - 2*mc 410*mc 730 - 2*mc 410*mc 1050 - 2*mc 730*mc 1050 + 4*mc 410*mc 730*mc 1050) + 2 * KeccakfPermAir.extraction.inter_672 c row := by
    simp only [KeccakfPermAir.extraction.inter_674, KeccakfPermAir.extraction.inter_673, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_672 c row = (mc 411 + mc 731 + mc 1051 - 2*mc 411*mc 731 - 2*mc 411*mc 1051 - 2*mc 731*mc 1051 + 4*mc 411*mc 731*mc 1051) + 2 * KeccakfPermAir.extraction.inter_670 c row := by
    simp only [KeccakfPermAir.extraction.inter_672, KeccakfPermAir.extraction.inter_671, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_670 c row = (mc 412 + mc 732 + mc 1052 - 2*mc 412*mc 732 - 2*mc 412*mc 1052 - 2*mc 732*mc 1052 + 4*mc 412*mc 732*mc 1052) + 2 * KeccakfPermAir.extraction.inter_668 c row := by
    simp only [KeccakfPermAir.extraction.inter_670, KeccakfPermAir.extraction.inter_669, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_668 c row = (mc 413 + mc 733 + mc 1053 - 2*mc 413*mc 733 - 2*mc 413*mc 1053 - 2*mc 733*mc 1053 + 4*mc 413*mc 733*mc 1053) + 2 * KeccakfPermAir.extraction.inter_666 c row := by
    simp only [KeccakfPermAir.extraction.inter_668, KeccakfPermAir.extraction.inter_667, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_666 c row = (mc 414 + mc 734 + mc 1054 - 2*mc 414*mc 734 - 2*mc 414*mc 1054 - 2*mc 734*mc 1054 + 4*mc 414*mc 734*mc 1054) + 2 * KeccakfPermAir.extraction.inter_664 c row := by
    simp only [KeccakfPermAir.extraction.inter_666, KeccakfPermAir.extraction.inter_665, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_664 c row = (mc 415 + mc 735 + mc 1055 - 2*mc 415*mc 735 - 2*mc 415*mc 1055 - 2*mc 735*mc 1055 + 4*mc 415*mc 735*mc 1055) + 2 * KeccakfPermAir.extraction.inter_662 c row := by
    simp only [KeccakfPermAir.extraction.inter_664, KeccakfPermAir.extraction.inter_663, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_662 c row = (mc 416 + mc 736 + mc 1056 - 2*mc 416*mc 736 - 2*mc 416*mc 1056 - 2*mc 736*mc 1056 + 4*mc 416*mc 736*mc 1056) := by
    simp only [KeccakfPermAir.extraction.inter_662, KeccakfPermAir.extraction.inter_661, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1158 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 417 737 1057 137 row) :
    mc 137 = (mc 417 + mc 737 + mc 1057 - 2*mc 417*mc 737 - 2*mc 417*mc 1057 - 2*mc 737*mc 1057 + 4*mc 417*mc 737*mc 1057) + 2*(mc 418 + mc 738 + mc 1058 - 2*mc 418*mc 738 - 2*mc 418*mc 1058 - 2*mc 738*mc 1058 + 4*mc 418*mc 738*mc 1058) + 4*(mc 419 + mc 739 + mc 1059 - 2*mc 419*mc 739 - 2*mc 419*mc 1059 - 2*mc 739*mc 1059 + 4*mc 419*mc 739*mc 1059) + 8*(mc 420 + mc 740 + mc 1060 - 2*mc 420*mc 740 - 2*mc 420*mc 1060 - 2*mc 740*mc 1060 + 4*mc 420*mc 740*mc 1060) + 16*(mc 421 + mc 741 + mc 1061 - 2*mc 421*mc 741 - 2*mc 421*mc 1061 - 2*mc 741*mc 1061 + 4*mc 421*mc 741*mc 1061) + 32*(mc 422 + mc 742 + mc 1062 - 2*mc 422*mc 742 - 2*mc 422*mc 1062 - 2*mc 742*mc 1062 + 4*mc 422*mc 742*mc 1062) + 64*(mc 423 + mc 743 + mc 1063 - 2*mc 423*mc 743 - 2*mc 423*mc 1063 - 2*mc 743*mc 1063 + 4*mc 423*mc 743*mc 1063) + 128*(mc 424 + mc 744 + mc 1064 - 2*mc 424*mc 744 - 2*mc 424*mc 1064 - 2*mc 744*mc 1064 + 4*mc 424*mc 744*mc 1064) + 256*(mc 425 + mc 745 + mc 1065 - 2*mc 425*mc 745 - 2*mc 425*mc 1065 - 2*mc 745*mc 1065 + 4*mc 425*mc 745*mc 1065) + 512*(mc 426 + mc 746 + mc 1066 - 2*mc 426*mc 746 - 2*mc 426*mc 1066 - 2*mc 746*mc 1066 + 4*mc 426*mc 746*mc 1066) + 1024*(mc 427 + mc 747 + mc 1067 - 2*mc 427*mc 747 - 2*mc 427*mc 1067 - 2*mc 747*mc 1067 + 4*mc 427*mc 747*mc 1067) + 2048*(mc 428 + mc 748 + mc 1068 - 2*mc 428*mc 748 - 2*mc 428*mc 1068 - 2*mc 748*mc 1068 + 4*mc 428*mc 748*mc 1068) + 4096*(mc 429 + mc 749 + mc 1069 - 2*mc 429*mc 749 - 2*mc 429*mc 1069 - 2*mc 749*mc 1069 + 4*mc 429*mc 749*mc 1069) + 8192*(mc 430 + mc 750 + mc 1070 - 2*mc 430*mc 750 - 2*mc 430*mc 1070 - 2*mc 750*mc 1070 + 4*mc 430*mc 750*mc 1070) + 16384*(mc 431 + mc 751 + mc 1071 - 2*mc 431*mc 751 - 2*mc 431*mc 1071 - 2*mc 751*mc 1071 + 4*mc 431*mc 751*mc 1071) + 32768*(mc 432 + mc 752 + mc 1072 - 2*mc 432*mc 752 - 2*mc 432*mc 1072 - 2*mc 752*mc 1072 + 4*mc 432*mc 752*mc 1072) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1158, KeccakfPermAir.extraction.inter_722, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_721 c row = (mc 418 + mc 738 + mc 1058 - 2*mc 418*mc 738 - 2*mc 418*mc 1058 - 2*mc 738*mc 1058 + 4*mc 418*mc 738*mc 1058) + 2 * KeccakfPermAir.extraction.inter_719 c row := by
    simp only [KeccakfPermAir.extraction.inter_721, KeccakfPermAir.extraction.inter_720, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_719 c row = (mc 419 + mc 739 + mc 1059 - 2*mc 419*mc 739 - 2*mc 419*mc 1059 - 2*mc 739*mc 1059 + 4*mc 419*mc 739*mc 1059) + 2 * KeccakfPermAir.extraction.inter_717 c row := by
    simp only [KeccakfPermAir.extraction.inter_719, KeccakfPermAir.extraction.inter_718, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_717 c row = (mc 420 + mc 740 + mc 1060 - 2*mc 420*mc 740 - 2*mc 420*mc 1060 - 2*mc 740*mc 1060 + 4*mc 420*mc 740*mc 1060) + 2 * KeccakfPermAir.extraction.inter_715 c row := by
    simp only [KeccakfPermAir.extraction.inter_717, KeccakfPermAir.extraction.inter_716, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_715 c row = (mc 421 + mc 741 + mc 1061 - 2*mc 421*mc 741 - 2*mc 421*mc 1061 - 2*mc 741*mc 1061 + 4*mc 421*mc 741*mc 1061) + 2 * KeccakfPermAir.extraction.inter_713 c row := by
    simp only [KeccakfPermAir.extraction.inter_715, KeccakfPermAir.extraction.inter_714, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_713 c row = (mc 422 + mc 742 + mc 1062 - 2*mc 422*mc 742 - 2*mc 422*mc 1062 - 2*mc 742*mc 1062 + 4*mc 422*mc 742*mc 1062) + 2 * KeccakfPermAir.extraction.inter_711 c row := by
    simp only [KeccakfPermAir.extraction.inter_713, KeccakfPermAir.extraction.inter_712, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_711 c row = (mc 423 + mc 743 + mc 1063 - 2*mc 423*mc 743 - 2*mc 423*mc 1063 - 2*mc 743*mc 1063 + 4*mc 423*mc 743*mc 1063) + 2 * KeccakfPermAir.extraction.inter_709 c row := by
    simp only [KeccakfPermAir.extraction.inter_711, KeccakfPermAir.extraction.inter_710, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_709 c row = (mc 424 + mc 744 + mc 1064 - 2*mc 424*mc 744 - 2*mc 424*mc 1064 - 2*mc 744*mc 1064 + 4*mc 424*mc 744*mc 1064) + 2 * KeccakfPermAir.extraction.inter_707 c row := by
    simp only [KeccakfPermAir.extraction.inter_709, KeccakfPermAir.extraction.inter_708, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_707 c row = (mc 425 + mc 745 + mc 1065 - 2*mc 425*mc 745 - 2*mc 425*mc 1065 - 2*mc 745*mc 1065 + 4*mc 425*mc 745*mc 1065) + 2 * KeccakfPermAir.extraction.inter_705 c row := by
    simp only [KeccakfPermAir.extraction.inter_707, KeccakfPermAir.extraction.inter_706, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_705 c row = (mc 426 + mc 746 + mc 1066 - 2*mc 426*mc 746 - 2*mc 426*mc 1066 - 2*mc 746*mc 1066 + 4*mc 426*mc 746*mc 1066) + 2 * KeccakfPermAir.extraction.inter_703 c row := by
    simp only [KeccakfPermAir.extraction.inter_705, KeccakfPermAir.extraction.inter_704, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_703 c row = (mc 427 + mc 747 + mc 1067 - 2*mc 427*mc 747 - 2*mc 427*mc 1067 - 2*mc 747*mc 1067 + 4*mc 427*mc 747*mc 1067) + 2 * KeccakfPermAir.extraction.inter_701 c row := by
    simp only [KeccakfPermAir.extraction.inter_703, KeccakfPermAir.extraction.inter_702, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_701 c row = (mc 428 + mc 748 + mc 1068 - 2*mc 428*mc 748 - 2*mc 428*mc 1068 - 2*mc 748*mc 1068 + 4*mc 428*mc 748*mc 1068) + 2 * KeccakfPermAir.extraction.inter_699 c row := by
    simp only [KeccakfPermAir.extraction.inter_701, KeccakfPermAir.extraction.inter_700, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_699 c row = (mc 429 + mc 749 + mc 1069 - 2*mc 429*mc 749 - 2*mc 429*mc 1069 - 2*mc 749*mc 1069 + 4*mc 429*mc 749*mc 1069) + 2 * KeccakfPermAir.extraction.inter_697 c row := by
    simp only [KeccakfPermAir.extraction.inter_699, KeccakfPermAir.extraction.inter_698, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_697 c row = (mc 430 + mc 750 + mc 1070 - 2*mc 430*mc 750 - 2*mc 430*mc 1070 - 2*mc 750*mc 1070 + 4*mc 430*mc 750*mc 1070) + 2 * KeccakfPermAir.extraction.inter_695 c row := by
    simp only [KeccakfPermAir.extraction.inter_697, KeccakfPermAir.extraction.inter_696, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_695 c row = (mc 431 + mc 751 + mc 1071 - 2*mc 431*mc 751 - 2*mc 431*mc 1071 - 2*mc 751*mc 1071 + 4*mc 431*mc 751*mc 1071) + 2 * KeccakfPermAir.extraction.inter_693 c row := by
    simp only [KeccakfPermAir.extraction.inter_695, KeccakfPermAir.extraction.inter_694, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_693 c row = (mc 432 + mc 752 + mc 1072 - 2*mc 432*mc 752 - 2*mc 432*mc 1072 - 2*mc 752*mc 1072 + 4*mc 432*mc 752*mc 1072) := by
    simp only [KeccakfPermAir.extraction.inter_693, KeccakfPermAir.extraction.inter_692, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1159 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 433 753 1073 138 row) :
    mc 138 = (mc 433 + mc 753 + mc 1073 - 2*mc 433*mc 753 - 2*mc 433*mc 1073 - 2*mc 753*mc 1073 + 4*mc 433*mc 753*mc 1073) + 2*(mc 434 + mc 754 + mc 1074 - 2*mc 434*mc 754 - 2*mc 434*mc 1074 - 2*mc 754*mc 1074 + 4*mc 434*mc 754*mc 1074) + 4*(mc 435 + mc 755 + mc 1075 - 2*mc 435*mc 755 - 2*mc 435*mc 1075 - 2*mc 755*mc 1075 + 4*mc 435*mc 755*mc 1075) + 8*(mc 436 + mc 756 + mc 1076 - 2*mc 436*mc 756 - 2*mc 436*mc 1076 - 2*mc 756*mc 1076 + 4*mc 436*mc 756*mc 1076) + 16*(mc 437 + mc 757 + mc 1077 - 2*mc 437*mc 757 - 2*mc 437*mc 1077 - 2*mc 757*mc 1077 + 4*mc 437*mc 757*mc 1077) + 32*(mc 438 + mc 758 + mc 1078 - 2*mc 438*mc 758 - 2*mc 438*mc 1078 - 2*mc 758*mc 1078 + 4*mc 438*mc 758*mc 1078) + 64*(mc 439 + mc 759 + mc 1079 - 2*mc 439*mc 759 - 2*mc 439*mc 1079 - 2*mc 759*mc 1079 + 4*mc 439*mc 759*mc 1079) + 128*(mc 440 + mc 760 + mc 1080 - 2*mc 440*mc 760 - 2*mc 440*mc 1080 - 2*mc 760*mc 1080 + 4*mc 440*mc 760*mc 1080) + 256*(mc 441 + mc 761 + mc 1081 - 2*mc 441*mc 761 - 2*mc 441*mc 1081 - 2*mc 761*mc 1081 + 4*mc 441*mc 761*mc 1081) + 512*(mc 442 + mc 762 + mc 1082 - 2*mc 442*mc 762 - 2*mc 442*mc 1082 - 2*mc 762*mc 1082 + 4*mc 442*mc 762*mc 1082) + 1024*(mc 443 + mc 763 + mc 1083 - 2*mc 443*mc 763 - 2*mc 443*mc 1083 - 2*mc 763*mc 1083 + 4*mc 443*mc 763*mc 1083) + 2048*(mc 444 + mc 764 + mc 1084 - 2*mc 444*mc 764 - 2*mc 444*mc 1084 - 2*mc 764*mc 1084 + 4*mc 444*mc 764*mc 1084) + 4096*(mc 445 + mc 765 + mc 1085 - 2*mc 445*mc 765 - 2*mc 445*mc 1085 - 2*mc 765*mc 1085 + 4*mc 445*mc 765*mc 1085) + 8192*(mc 446 + mc 766 + mc 1086 - 2*mc 446*mc 766 - 2*mc 446*mc 1086 - 2*mc 766*mc 1086 + 4*mc 446*mc 766*mc 1086) + 16384*(mc 447 + mc 767 + mc 1087 - 2*mc 447*mc 767 - 2*mc 447*mc 1087 - 2*mc 767*mc 1087 + 4*mc 447*mc 767*mc 1087) + 32768*(mc 448 + mc 768 + mc 1088 - 2*mc 448*mc 768 - 2*mc 448*mc 1088 - 2*mc 768*mc 1088 + 4*mc 448*mc 768*mc 1088) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1159, KeccakfPermAir.extraction.inter_753, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_752 c row = (mc 434 + mc 754 + mc 1074 - 2*mc 434*mc 754 - 2*mc 434*mc 1074 - 2*mc 754*mc 1074 + 4*mc 434*mc 754*mc 1074) + 2 * KeccakfPermAir.extraction.inter_750 c row := by
    simp only [KeccakfPermAir.extraction.inter_752, KeccakfPermAir.extraction.inter_751, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_750 c row = (mc 435 + mc 755 + mc 1075 - 2*mc 435*mc 755 - 2*mc 435*mc 1075 - 2*mc 755*mc 1075 + 4*mc 435*mc 755*mc 1075) + 2 * KeccakfPermAir.extraction.inter_748 c row := by
    simp only [KeccakfPermAir.extraction.inter_750, KeccakfPermAir.extraction.inter_749, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_748 c row = (mc 436 + mc 756 + mc 1076 - 2*mc 436*mc 756 - 2*mc 436*mc 1076 - 2*mc 756*mc 1076 + 4*mc 436*mc 756*mc 1076) + 2 * KeccakfPermAir.extraction.inter_746 c row := by
    simp only [KeccakfPermAir.extraction.inter_748, KeccakfPermAir.extraction.inter_747, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_746 c row = (mc 437 + mc 757 + mc 1077 - 2*mc 437*mc 757 - 2*mc 437*mc 1077 - 2*mc 757*mc 1077 + 4*mc 437*mc 757*mc 1077) + 2 * KeccakfPermAir.extraction.inter_744 c row := by
    simp only [KeccakfPermAir.extraction.inter_746, KeccakfPermAir.extraction.inter_745, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_744 c row = (mc 438 + mc 758 + mc 1078 - 2*mc 438*mc 758 - 2*mc 438*mc 1078 - 2*mc 758*mc 1078 + 4*mc 438*mc 758*mc 1078) + 2 * KeccakfPermAir.extraction.inter_742 c row := by
    simp only [KeccakfPermAir.extraction.inter_744, KeccakfPermAir.extraction.inter_743, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_742 c row = (mc 439 + mc 759 + mc 1079 - 2*mc 439*mc 759 - 2*mc 439*mc 1079 - 2*mc 759*mc 1079 + 4*mc 439*mc 759*mc 1079) + 2 * KeccakfPermAir.extraction.inter_740 c row := by
    simp only [KeccakfPermAir.extraction.inter_742, KeccakfPermAir.extraction.inter_741, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_740 c row = (mc 440 + mc 760 + mc 1080 - 2*mc 440*mc 760 - 2*mc 440*mc 1080 - 2*mc 760*mc 1080 + 4*mc 440*mc 760*mc 1080) + 2 * KeccakfPermAir.extraction.inter_738 c row := by
    simp only [KeccakfPermAir.extraction.inter_740, KeccakfPermAir.extraction.inter_739, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_738 c row = (mc 441 + mc 761 + mc 1081 - 2*mc 441*mc 761 - 2*mc 441*mc 1081 - 2*mc 761*mc 1081 + 4*mc 441*mc 761*mc 1081) + 2 * KeccakfPermAir.extraction.inter_736 c row := by
    simp only [KeccakfPermAir.extraction.inter_738, KeccakfPermAir.extraction.inter_737, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_736 c row = (mc 442 + mc 762 + mc 1082 - 2*mc 442*mc 762 - 2*mc 442*mc 1082 - 2*mc 762*mc 1082 + 4*mc 442*mc 762*mc 1082) + 2 * KeccakfPermAir.extraction.inter_734 c row := by
    simp only [KeccakfPermAir.extraction.inter_736, KeccakfPermAir.extraction.inter_735, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_734 c row = (mc 443 + mc 763 + mc 1083 - 2*mc 443*mc 763 - 2*mc 443*mc 1083 - 2*mc 763*mc 1083 + 4*mc 443*mc 763*mc 1083) + 2 * KeccakfPermAir.extraction.inter_732 c row := by
    simp only [KeccakfPermAir.extraction.inter_734, KeccakfPermAir.extraction.inter_733, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_732 c row = (mc 444 + mc 764 + mc 1084 - 2*mc 444*mc 764 - 2*mc 444*mc 1084 - 2*mc 764*mc 1084 + 4*mc 444*mc 764*mc 1084) + 2 * KeccakfPermAir.extraction.inter_730 c row := by
    simp only [KeccakfPermAir.extraction.inter_732, KeccakfPermAir.extraction.inter_731, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_730 c row = (mc 445 + mc 765 + mc 1085 - 2*mc 445*mc 765 - 2*mc 445*mc 1085 - 2*mc 765*mc 1085 + 4*mc 445*mc 765*mc 1085) + 2 * KeccakfPermAir.extraction.inter_728 c row := by
    simp only [KeccakfPermAir.extraction.inter_730, KeccakfPermAir.extraction.inter_729, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_728 c row = (mc 446 + mc 766 + mc 1086 - 2*mc 446*mc 766 - 2*mc 446*mc 1086 - 2*mc 766*mc 1086 + 4*mc 446*mc 766*mc 1086) + 2 * KeccakfPermAir.extraction.inter_726 c row := by
    simp only [KeccakfPermAir.extraction.inter_728, KeccakfPermAir.extraction.inter_727, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_726 c row = (mc 447 + mc 767 + mc 1087 - 2*mc 447*mc 767 - 2*mc 447*mc 1087 - 2*mc 767*mc 1087 + 4*mc 447*mc 767*mc 1087) + 2 * KeccakfPermAir.extraction.inter_724 c row := by
    simp only [KeccakfPermAir.extraction.inter_726, KeccakfPermAir.extraction.inter_725, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_724 c row = (mc 448 + mc 768 + mc 1088 - 2*mc 448*mc 768 - 2*mc 448*mc 1088 - 2*mc 768*mc 1088 + 4*mc 448*mc 768*mc 1088) := by
    simp only [KeccakfPermAir.extraction.inter_724, KeccakfPermAir.extraction.inter_723, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1160 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 449 769 1089 139 row) :
    mc 139 = (mc 449 + mc 769 + mc 1089 - 2*mc 449*mc 769 - 2*mc 449*mc 1089 - 2*mc 769*mc 1089 + 4*mc 449*mc 769*mc 1089) + 2*(mc 450 + mc 770 + mc 1090 - 2*mc 450*mc 770 - 2*mc 450*mc 1090 - 2*mc 770*mc 1090 + 4*mc 450*mc 770*mc 1090) + 4*(mc 451 + mc 771 + mc 1091 - 2*mc 451*mc 771 - 2*mc 451*mc 1091 - 2*mc 771*mc 1091 + 4*mc 451*mc 771*mc 1091) + 8*(mc 452 + mc 772 + mc 1092 - 2*mc 452*mc 772 - 2*mc 452*mc 1092 - 2*mc 772*mc 1092 + 4*mc 452*mc 772*mc 1092) + 16*(mc 453 + mc 773 + mc 1093 - 2*mc 453*mc 773 - 2*mc 453*mc 1093 - 2*mc 773*mc 1093 + 4*mc 453*mc 773*mc 1093) + 32*(mc 454 + mc 774 + mc 1094 - 2*mc 454*mc 774 - 2*mc 454*mc 1094 - 2*mc 774*mc 1094 + 4*mc 454*mc 774*mc 1094) + 64*(mc 455 + mc 775 + mc 1095 - 2*mc 455*mc 775 - 2*mc 455*mc 1095 - 2*mc 775*mc 1095 + 4*mc 455*mc 775*mc 1095) + 128*(mc 456 + mc 776 + mc 1096 - 2*mc 456*mc 776 - 2*mc 456*mc 1096 - 2*mc 776*mc 1096 + 4*mc 456*mc 776*mc 1096) + 256*(mc 457 + mc 777 + mc 1097 - 2*mc 457*mc 777 - 2*mc 457*mc 1097 - 2*mc 777*mc 1097 + 4*mc 457*mc 777*mc 1097) + 512*(mc 458 + mc 778 + mc 1098 - 2*mc 458*mc 778 - 2*mc 458*mc 1098 - 2*mc 778*mc 1098 + 4*mc 458*mc 778*mc 1098) + 1024*(mc 459 + mc 779 + mc 1099 - 2*mc 459*mc 779 - 2*mc 459*mc 1099 - 2*mc 779*mc 1099 + 4*mc 459*mc 779*mc 1099) + 2048*(mc 460 + mc 780 + mc 1100 - 2*mc 460*mc 780 - 2*mc 460*mc 1100 - 2*mc 780*mc 1100 + 4*mc 460*mc 780*mc 1100) + 4096*(mc 461 + mc 781 + mc 1101 - 2*mc 461*mc 781 - 2*mc 461*mc 1101 - 2*mc 781*mc 1101 + 4*mc 461*mc 781*mc 1101) + 8192*(mc 462 + mc 782 + mc 1102 - 2*mc 462*mc 782 - 2*mc 462*mc 1102 - 2*mc 782*mc 1102 + 4*mc 462*mc 782*mc 1102) + 16384*(mc 463 + mc 783 + mc 1103 - 2*mc 463*mc 783 - 2*mc 463*mc 1103 - 2*mc 783*mc 1103 + 4*mc 463*mc 783*mc 1103) + 32768*(mc 464 + mc 784 + mc 1104 - 2*mc 464*mc 784 - 2*mc 464*mc 1104 - 2*mc 784*mc 1104 + 4*mc 464*mc 784*mc 1104) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1160, KeccakfPermAir.extraction.inter_784, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_783 c row = (mc 450 + mc 770 + mc 1090 - 2*mc 450*mc 770 - 2*mc 450*mc 1090 - 2*mc 770*mc 1090 + 4*mc 450*mc 770*mc 1090) + 2 * KeccakfPermAir.extraction.inter_781 c row := by
    simp only [KeccakfPermAir.extraction.inter_783, KeccakfPermAir.extraction.inter_782, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_781 c row = (mc 451 + mc 771 + mc 1091 - 2*mc 451*mc 771 - 2*mc 451*mc 1091 - 2*mc 771*mc 1091 + 4*mc 451*mc 771*mc 1091) + 2 * KeccakfPermAir.extraction.inter_779 c row := by
    simp only [KeccakfPermAir.extraction.inter_781, KeccakfPermAir.extraction.inter_780, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_779 c row = (mc 452 + mc 772 + mc 1092 - 2*mc 452*mc 772 - 2*mc 452*mc 1092 - 2*mc 772*mc 1092 + 4*mc 452*mc 772*mc 1092) + 2 * KeccakfPermAir.extraction.inter_777 c row := by
    simp only [KeccakfPermAir.extraction.inter_779, KeccakfPermAir.extraction.inter_778, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_777 c row = (mc 453 + mc 773 + mc 1093 - 2*mc 453*mc 773 - 2*mc 453*mc 1093 - 2*mc 773*mc 1093 + 4*mc 453*mc 773*mc 1093) + 2 * KeccakfPermAir.extraction.inter_775 c row := by
    simp only [KeccakfPermAir.extraction.inter_777, KeccakfPermAir.extraction.inter_776, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_775 c row = (mc 454 + mc 774 + mc 1094 - 2*mc 454*mc 774 - 2*mc 454*mc 1094 - 2*mc 774*mc 1094 + 4*mc 454*mc 774*mc 1094) + 2 * KeccakfPermAir.extraction.inter_773 c row := by
    simp only [KeccakfPermAir.extraction.inter_775, KeccakfPermAir.extraction.inter_774, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_773 c row = (mc 455 + mc 775 + mc 1095 - 2*mc 455*mc 775 - 2*mc 455*mc 1095 - 2*mc 775*mc 1095 + 4*mc 455*mc 775*mc 1095) + 2 * KeccakfPermAir.extraction.inter_771 c row := by
    simp only [KeccakfPermAir.extraction.inter_773, KeccakfPermAir.extraction.inter_772, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_771 c row = (mc 456 + mc 776 + mc 1096 - 2*mc 456*mc 776 - 2*mc 456*mc 1096 - 2*mc 776*mc 1096 + 4*mc 456*mc 776*mc 1096) + 2 * KeccakfPermAir.extraction.inter_769 c row := by
    simp only [KeccakfPermAir.extraction.inter_771, KeccakfPermAir.extraction.inter_770, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_769 c row = (mc 457 + mc 777 + mc 1097 - 2*mc 457*mc 777 - 2*mc 457*mc 1097 - 2*mc 777*mc 1097 + 4*mc 457*mc 777*mc 1097) + 2 * KeccakfPermAir.extraction.inter_767 c row := by
    simp only [KeccakfPermAir.extraction.inter_769, KeccakfPermAir.extraction.inter_768, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_767 c row = (mc 458 + mc 778 + mc 1098 - 2*mc 458*mc 778 - 2*mc 458*mc 1098 - 2*mc 778*mc 1098 + 4*mc 458*mc 778*mc 1098) + 2 * KeccakfPermAir.extraction.inter_765 c row := by
    simp only [KeccakfPermAir.extraction.inter_767, KeccakfPermAir.extraction.inter_766, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_765 c row = (mc 459 + mc 779 + mc 1099 - 2*mc 459*mc 779 - 2*mc 459*mc 1099 - 2*mc 779*mc 1099 + 4*mc 459*mc 779*mc 1099) + 2 * KeccakfPermAir.extraction.inter_763 c row := by
    simp only [KeccakfPermAir.extraction.inter_765, KeccakfPermAir.extraction.inter_764, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_763 c row = (mc 460 + mc 780 + mc 1100 - 2*mc 460*mc 780 - 2*mc 460*mc 1100 - 2*mc 780*mc 1100 + 4*mc 460*mc 780*mc 1100) + 2 * KeccakfPermAir.extraction.inter_761 c row := by
    simp only [KeccakfPermAir.extraction.inter_763, KeccakfPermAir.extraction.inter_762, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_761 c row = (mc 461 + mc 781 + mc 1101 - 2*mc 461*mc 781 - 2*mc 461*mc 1101 - 2*mc 781*mc 1101 + 4*mc 461*mc 781*mc 1101) + 2 * KeccakfPermAir.extraction.inter_759 c row := by
    simp only [KeccakfPermAir.extraction.inter_761, KeccakfPermAir.extraction.inter_760, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_759 c row = (mc 462 + mc 782 + mc 1102 - 2*mc 462*mc 782 - 2*mc 462*mc 1102 - 2*mc 782*mc 1102 + 4*mc 462*mc 782*mc 1102) + 2 * KeccakfPermAir.extraction.inter_757 c row := by
    simp only [KeccakfPermAir.extraction.inter_759, KeccakfPermAir.extraction.inter_758, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_757 c row = (mc 463 + mc 783 + mc 1103 - 2*mc 463*mc 783 - 2*mc 463*mc 1103 - 2*mc 783*mc 1103 + 4*mc 463*mc 783*mc 1103) + 2 * KeccakfPermAir.extraction.inter_755 c row := by
    simp only [KeccakfPermAir.extraction.inter_757, KeccakfPermAir.extraction.inter_756, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_755 c row = (mc 464 + mc 784 + mc 1104 - 2*mc 464*mc 784 - 2*mc 464*mc 1104 - 2*mc 784*mc 1104 + 4*mc 464*mc 784*mc 1104) := by
    simp only [KeccakfPermAir.extraction.inter_755, KeccakfPermAir.extraction.inter_754, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1161 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 465 785 1105 140 row) :
    mc 140 = (mc 465 + mc 785 + mc 1105 - 2*mc 465*mc 785 - 2*mc 465*mc 1105 - 2*mc 785*mc 1105 + 4*mc 465*mc 785*mc 1105) + 2*(mc 466 + mc 786 + mc 1106 - 2*mc 466*mc 786 - 2*mc 466*mc 1106 - 2*mc 786*mc 1106 + 4*mc 466*mc 786*mc 1106) + 4*(mc 467 + mc 787 + mc 1107 - 2*mc 467*mc 787 - 2*mc 467*mc 1107 - 2*mc 787*mc 1107 + 4*mc 467*mc 787*mc 1107) + 8*(mc 468 + mc 788 + mc 1108 - 2*mc 468*mc 788 - 2*mc 468*mc 1108 - 2*mc 788*mc 1108 + 4*mc 468*mc 788*mc 1108) + 16*(mc 469 + mc 789 + mc 1109 - 2*mc 469*mc 789 - 2*mc 469*mc 1109 - 2*mc 789*mc 1109 + 4*mc 469*mc 789*mc 1109) + 32*(mc 470 + mc 790 + mc 1110 - 2*mc 470*mc 790 - 2*mc 470*mc 1110 - 2*mc 790*mc 1110 + 4*mc 470*mc 790*mc 1110) + 64*(mc 471 + mc 791 + mc 1111 - 2*mc 471*mc 791 - 2*mc 471*mc 1111 - 2*mc 791*mc 1111 + 4*mc 471*mc 791*mc 1111) + 128*(mc 472 + mc 792 + mc 1112 - 2*mc 472*mc 792 - 2*mc 472*mc 1112 - 2*mc 792*mc 1112 + 4*mc 472*mc 792*mc 1112) + 256*(mc 473 + mc 793 + mc 1113 - 2*mc 473*mc 793 - 2*mc 473*mc 1113 - 2*mc 793*mc 1113 + 4*mc 473*mc 793*mc 1113) + 512*(mc 474 + mc 794 + mc 1114 - 2*mc 474*mc 794 - 2*mc 474*mc 1114 - 2*mc 794*mc 1114 + 4*mc 474*mc 794*mc 1114) + 1024*(mc 475 + mc 795 + mc 1115 - 2*mc 475*mc 795 - 2*mc 475*mc 1115 - 2*mc 795*mc 1115 + 4*mc 475*mc 795*mc 1115) + 2048*(mc 476 + mc 796 + mc 1116 - 2*mc 476*mc 796 - 2*mc 476*mc 1116 - 2*mc 796*mc 1116 + 4*mc 476*mc 796*mc 1116) + 4096*(mc 477 + mc 797 + mc 1117 - 2*mc 477*mc 797 - 2*mc 477*mc 1117 - 2*mc 797*mc 1117 + 4*mc 477*mc 797*mc 1117) + 8192*(mc 478 + mc 798 + mc 1118 - 2*mc 478*mc 798 - 2*mc 478*mc 1118 - 2*mc 798*mc 1118 + 4*mc 478*mc 798*mc 1118) + 16384*(mc 479 + mc 799 + mc 1119 - 2*mc 479*mc 799 - 2*mc 479*mc 1119 - 2*mc 799*mc 1119 + 4*mc 479*mc 799*mc 1119) + 32768*(mc 480 + mc 800 + mc 1120 - 2*mc 480*mc 800 - 2*mc 480*mc 1120 - 2*mc 800*mc 1120 + 4*mc 480*mc 800*mc 1120) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1161, KeccakfPermAir.extraction.inter_815, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_814 c row = (mc 466 + mc 786 + mc 1106 - 2*mc 466*mc 786 - 2*mc 466*mc 1106 - 2*mc 786*mc 1106 + 4*mc 466*mc 786*mc 1106) + 2 * KeccakfPermAir.extraction.inter_812 c row := by
    simp only [KeccakfPermAir.extraction.inter_814, KeccakfPermAir.extraction.inter_813, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_812 c row = (mc 467 + mc 787 + mc 1107 - 2*mc 467*mc 787 - 2*mc 467*mc 1107 - 2*mc 787*mc 1107 + 4*mc 467*mc 787*mc 1107) + 2 * KeccakfPermAir.extraction.inter_810 c row := by
    simp only [KeccakfPermAir.extraction.inter_812, KeccakfPermAir.extraction.inter_811, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_810 c row = (mc 468 + mc 788 + mc 1108 - 2*mc 468*mc 788 - 2*mc 468*mc 1108 - 2*mc 788*mc 1108 + 4*mc 468*mc 788*mc 1108) + 2 * KeccakfPermAir.extraction.inter_808 c row := by
    simp only [KeccakfPermAir.extraction.inter_810, KeccakfPermAir.extraction.inter_809, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_808 c row = (mc 469 + mc 789 + mc 1109 - 2*mc 469*mc 789 - 2*mc 469*mc 1109 - 2*mc 789*mc 1109 + 4*mc 469*mc 789*mc 1109) + 2 * KeccakfPermAir.extraction.inter_806 c row := by
    simp only [KeccakfPermAir.extraction.inter_808, KeccakfPermAir.extraction.inter_807, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_806 c row = (mc 470 + mc 790 + mc 1110 - 2*mc 470*mc 790 - 2*mc 470*mc 1110 - 2*mc 790*mc 1110 + 4*mc 470*mc 790*mc 1110) + 2 * KeccakfPermAir.extraction.inter_804 c row := by
    simp only [KeccakfPermAir.extraction.inter_806, KeccakfPermAir.extraction.inter_805, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_804 c row = (mc 471 + mc 791 + mc 1111 - 2*mc 471*mc 791 - 2*mc 471*mc 1111 - 2*mc 791*mc 1111 + 4*mc 471*mc 791*mc 1111) + 2 * KeccakfPermAir.extraction.inter_802 c row := by
    simp only [KeccakfPermAir.extraction.inter_804, KeccakfPermAir.extraction.inter_803, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_802 c row = (mc 472 + mc 792 + mc 1112 - 2*mc 472*mc 792 - 2*mc 472*mc 1112 - 2*mc 792*mc 1112 + 4*mc 472*mc 792*mc 1112) + 2 * KeccakfPermAir.extraction.inter_800 c row := by
    simp only [KeccakfPermAir.extraction.inter_802, KeccakfPermAir.extraction.inter_801, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_800 c row = (mc 473 + mc 793 + mc 1113 - 2*mc 473*mc 793 - 2*mc 473*mc 1113 - 2*mc 793*mc 1113 + 4*mc 473*mc 793*mc 1113) + 2 * KeccakfPermAir.extraction.inter_798 c row := by
    simp only [KeccakfPermAir.extraction.inter_800, KeccakfPermAir.extraction.inter_799, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_798 c row = (mc 474 + mc 794 + mc 1114 - 2*mc 474*mc 794 - 2*mc 474*mc 1114 - 2*mc 794*mc 1114 + 4*mc 474*mc 794*mc 1114) + 2 * KeccakfPermAir.extraction.inter_796 c row := by
    simp only [KeccakfPermAir.extraction.inter_798, KeccakfPermAir.extraction.inter_797, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_796 c row = (mc 475 + mc 795 + mc 1115 - 2*mc 475*mc 795 - 2*mc 475*mc 1115 - 2*mc 795*mc 1115 + 4*mc 475*mc 795*mc 1115) + 2 * KeccakfPermAir.extraction.inter_794 c row := by
    simp only [KeccakfPermAir.extraction.inter_796, KeccakfPermAir.extraction.inter_795, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_794 c row = (mc 476 + mc 796 + mc 1116 - 2*mc 476*mc 796 - 2*mc 476*mc 1116 - 2*mc 796*mc 1116 + 4*mc 476*mc 796*mc 1116) + 2 * KeccakfPermAir.extraction.inter_792 c row := by
    simp only [KeccakfPermAir.extraction.inter_794, KeccakfPermAir.extraction.inter_793, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_792 c row = (mc 477 + mc 797 + mc 1117 - 2*mc 477*mc 797 - 2*mc 477*mc 1117 - 2*mc 797*mc 1117 + 4*mc 477*mc 797*mc 1117) + 2 * KeccakfPermAir.extraction.inter_790 c row := by
    simp only [KeccakfPermAir.extraction.inter_792, KeccakfPermAir.extraction.inter_791, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_790 c row = (mc 478 + mc 798 + mc 1118 - 2*mc 478*mc 798 - 2*mc 478*mc 1118 - 2*mc 798*mc 1118 + 4*mc 478*mc 798*mc 1118) + 2 * KeccakfPermAir.extraction.inter_788 c row := by
    simp only [KeccakfPermAir.extraction.inter_790, KeccakfPermAir.extraction.inter_789, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_788 c row = (mc 479 + mc 799 + mc 1119 - 2*mc 479*mc 799 - 2*mc 479*mc 1119 - 2*mc 799*mc 1119 + 4*mc 479*mc 799*mc 1119) + 2 * KeccakfPermAir.extraction.inter_786 c row := by
    simp only [KeccakfPermAir.extraction.inter_788, KeccakfPermAir.extraction.inter_787, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_786 c row = (mc 480 + mc 800 + mc 1120 - 2*mc 480*mc 800 - 2*mc 480*mc 1120 - 2*mc 800*mc 1120 + 4*mc 480*mc 800*mc 1120) := by
    simp only [KeccakfPermAir.extraction.inter_786, KeccakfPermAir.extraction.inter_785, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1226 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 481 801 1121 141 row) :
    mc 141 = (mc 481 + mc 801 + mc 1121 - 2*mc 481*mc 801 - 2*mc 481*mc 1121 - 2*mc 801*mc 1121 + 4*mc 481*mc 801*mc 1121) + 2*(mc 482 + mc 802 + mc 1122 - 2*mc 482*mc 802 - 2*mc 482*mc 1122 - 2*mc 802*mc 1122 + 4*mc 482*mc 802*mc 1122) + 4*(mc 483 + mc 803 + mc 1123 - 2*mc 483*mc 803 - 2*mc 483*mc 1123 - 2*mc 803*mc 1123 + 4*mc 483*mc 803*mc 1123) + 8*(mc 484 + mc 804 + mc 1124 - 2*mc 484*mc 804 - 2*mc 484*mc 1124 - 2*mc 804*mc 1124 + 4*mc 484*mc 804*mc 1124) + 16*(mc 485 + mc 805 + mc 1125 - 2*mc 485*mc 805 - 2*mc 485*mc 1125 - 2*mc 805*mc 1125 + 4*mc 485*mc 805*mc 1125) + 32*(mc 486 + mc 806 + mc 1126 - 2*mc 486*mc 806 - 2*mc 486*mc 1126 - 2*mc 806*mc 1126 + 4*mc 486*mc 806*mc 1126) + 64*(mc 487 + mc 807 + mc 1127 - 2*mc 487*mc 807 - 2*mc 487*mc 1127 - 2*mc 807*mc 1127 + 4*mc 487*mc 807*mc 1127) + 128*(mc 488 + mc 808 + mc 1128 - 2*mc 488*mc 808 - 2*mc 488*mc 1128 - 2*mc 808*mc 1128 + 4*mc 488*mc 808*mc 1128) + 256*(mc 489 + mc 809 + mc 1129 - 2*mc 489*mc 809 - 2*mc 489*mc 1129 - 2*mc 809*mc 1129 + 4*mc 489*mc 809*mc 1129) + 512*(mc 490 + mc 810 + mc 1130 - 2*mc 490*mc 810 - 2*mc 490*mc 1130 - 2*mc 810*mc 1130 + 4*mc 490*mc 810*mc 1130) + 1024*(mc 491 + mc 811 + mc 1131 - 2*mc 491*mc 811 - 2*mc 491*mc 1131 - 2*mc 811*mc 1131 + 4*mc 491*mc 811*mc 1131) + 2048*(mc 492 + mc 812 + mc 1132 - 2*mc 492*mc 812 - 2*mc 492*mc 1132 - 2*mc 812*mc 1132 + 4*mc 492*mc 812*mc 1132) + 4096*(mc 493 + mc 813 + mc 1133 - 2*mc 493*mc 813 - 2*mc 493*mc 1133 - 2*mc 813*mc 1133 + 4*mc 493*mc 813*mc 1133) + 8192*(mc 494 + mc 814 + mc 1134 - 2*mc 494*mc 814 - 2*mc 494*mc 1134 - 2*mc 814*mc 1134 + 4*mc 494*mc 814*mc 1134) + 16384*(mc 495 + mc 815 + mc 1135 - 2*mc 495*mc 815 - 2*mc 495*mc 1135 - 2*mc 815*mc 1135 + 4*mc 495*mc 815*mc 1135) + 32768*(mc 496 + mc 816 + mc 1136 - 2*mc 496*mc 816 - 2*mc 496*mc 1136 - 2*mc 816*mc 1136 + 4*mc 496*mc 816*mc 1136) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1226, KeccakfPermAir.extraction.inter_846, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_845 c row = (mc 482 + mc 802 + mc 1122 - 2*mc 482*mc 802 - 2*mc 482*mc 1122 - 2*mc 802*mc 1122 + 4*mc 482*mc 802*mc 1122) + 2 * KeccakfPermAir.extraction.inter_843 c row := by
    simp only [KeccakfPermAir.extraction.inter_845, KeccakfPermAir.extraction.inter_844, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_843 c row = (mc 483 + mc 803 + mc 1123 - 2*mc 483*mc 803 - 2*mc 483*mc 1123 - 2*mc 803*mc 1123 + 4*mc 483*mc 803*mc 1123) + 2 * KeccakfPermAir.extraction.inter_841 c row := by
    simp only [KeccakfPermAir.extraction.inter_843, KeccakfPermAir.extraction.inter_842, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_841 c row = (mc 484 + mc 804 + mc 1124 - 2*mc 484*mc 804 - 2*mc 484*mc 1124 - 2*mc 804*mc 1124 + 4*mc 484*mc 804*mc 1124) + 2 * KeccakfPermAir.extraction.inter_839 c row := by
    simp only [KeccakfPermAir.extraction.inter_841, KeccakfPermAir.extraction.inter_840, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_839 c row = (mc 485 + mc 805 + mc 1125 - 2*mc 485*mc 805 - 2*mc 485*mc 1125 - 2*mc 805*mc 1125 + 4*mc 485*mc 805*mc 1125) + 2 * KeccakfPermAir.extraction.inter_837 c row := by
    simp only [KeccakfPermAir.extraction.inter_839, KeccakfPermAir.extraction.inter_838, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_837 c row = (mc 486 + mc 806 + mc 1126 - 2*mc 486*mc 806 - 2*mc 486*mc 1126 - 2*mc 806*mc 1126 + 4*mc 486*mc 806*mc 1126) + 2 * KeccakfPermAir.extraction.inter_835 c row := by
    simp only [KeccakfPermAir.extraction.inter_837, KeccakfPermAir.extraction.inter_836, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_835 c row = (mc 487 + mc 807 + mc 1127 - 2*mc 487*mc 807 - 2*mc 487*mc 1127 - 2*mc 807*mc 1127 + 4*mc 487*mc 807*mc 1127) + 2 * KeccakfPermAir.extraction.inter_833 c row := by
    simp only [KeccakfPermAir.extraction.inter_835, KeccakfPermAir.extraction.inter_834, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_833 c row = (mc 488 + mc 808 + mc 1128 - 2*mc 488*mc 808 - 2*mc 488*mc 1128 - 2*mc 808*mc 1128 + 4*mc 488*mc 808*mc 1128) + 2 * KeccakfPermAir.extraction.inter_831 c row := by
    simp only [KeccakfPermAir.extraction.inter_833, KeccakfPermAir.extraction.inter_832, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_831 c row = (mc 489 + mc 809 + mc 1129 - 2*mc 489*mc 809 - 2*mc 489*mc 1129 - 2*mc 809*mc 1129 + 4*mc 489*mc 809*mc 1129) + 2 * KeccakfPermAir.extraction.inter_829 c row := by
    simp only [KeccakfPermAir.extraction.inter_831, KeccakfPermAir.extraction.inter_830, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_829 c row = (mc 490 + mc 810 + mc 1130 - 2*mc 490*mc 810 - 2*mc 490*mc 1130 - 2*mc 810*mc 1130 + 4*mc 490*mc 810*mc 1130) + 2 * KeccakfPermAir.extraction.inter_827 c row := by
    simp only [KeccakfPermAir.extraction.inter_829, KeccakfPermAir.extraction.inter_828, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_827 c row = (mc 491 + mc 811 + mc 1131 - 2*mc 491*mc 811 - 2*mc 491*mc 1131 - 2*mc 811*mc 1131 + 4*mc 491*mc 811*mc 1131) + 2 * KeccakfPermAir.extraction.inter_825 c row := by
    simp only [KeccakfPermAir.extraction.inter_827, KeccakfPermAir.extraction.inter_826, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_825 c row = (mc 492 + mc 812 + mc 1132 - 2*mc 492*mc 812 - 2*mc 492*mc 1132 - 2*mc 812*mc 1132 + 4*mc 492*mc 812*mc 1132) + 2 * KeccakfPermAir.extraction.inter_823 c row := by
    simp only [KeccakfPermAir.extraction.inter_825, KeccakfPermAir.extraction.inter_824, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_823 c row = (mc 493 + mc 813 + mc 1133 - 2*mc 493*mc 813 - 2*mc 493*mc 1133 - 2*mc 813*mc 1133 + 4*mc 493*mc 813*mc 1133) + 2 * KeccakfPermAir.extraction.inter_821 c row := by
    simp only [KeccakfPermAir.extraction.inter_823, KeccakfPermAir.extraction.inter_822, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_821 c row = (mc 494 + mc 814 + mc 1134 - 2*mc 494*mc 814 - 2*mc 494*mc 1134 - 2*mc 814*mc 1134 + 4*mc 494*mc 814*mc 1134) + 2 * KeccakfPermAir.extraction.inter_819 c row := by
    simp only [KeccakfPermAir.extraction.inter_821, KeccakfPermAir.extraction.inter_820, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_819 c row = (mc 495 + mc 815 + mc 1135 - 2*mc 495*mc 815 - 2*mc 495*mc 1135 - 2*mc 815*mc 1135 + 4*mc 495*mc 815*mc 1135) + 2 * KeccakfPermAir.extraction.inter_817 c row := by
    simp only [KeccakfPermAir.extraction.inter_819, KeccakfPermAir.extraction.inter_818, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_817 c row = (mc 496 + mc 816 + mc 1136 - 2*mc 496*mc 816 - 2*mc 496*mc 1136 - 2*mc 816*mc 1136 + 4*mc 496*mc 816*mc 1136) := by
    simp only [KeccakfPermAir.extraction.inter_817, KeccakfPermAir.extraction.inter_816, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1227 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 497 817 1137 142 row) :
    mc 142 = (mc 497 + mc 817 + mc 1137 - 2*mc 497*mc 817 - 2*mc 497*mc 1137 - 2*mc 817*mc 1137 + 4*mc 497*mc 817*mc 1137) + 2*(mc 498 + mc 818 + mc 1138 - 2*mc 498*mc 818 - 2*mc 498*mc 1138 - 2*mc 818*mc 1138 + 4*mc 498*mc 818*mc 1138) + 4*(mc 499 + mc 819 + mc 1139 - 2*mc 499*mc 819 - 2*mc 499*mc 1139 - 2*mc 819*mc 1139 + 4*mc 499*mc 819*mc 1139) + 8*(mc 500 + mc 820 + mc 1140 - 2*mc 500*mc 820 - 2*mc 500*mc 1140 - 2*mc 820*mc 1140 + 4*mc 500*mc 820*mc 1140) + 16*(mc 501 + mc 821 + mc 1141 - 2*mc 501*mc 821 - 2*mc 501*mc 1141 - 2*mc 821*mc 1141 + 4*mc 501*mc 821*mc 1141) + 32*(mc 502 + mc 822 + mc 1142 - 2*mc 502*mc 822 - 2*mc 502*mc 1142 - 2*mc 822*mc 1142 + 4*mc 502*mc 822*mc 1142) + 64*(mc 503 + mc 823 + mc 1143 - 2*mc 503*mc 823 - 2*mc 503*mc 1143 - 2*mc 823*mc 1143 + 4*mc 503*mc 823*mc 1143) + 128*(mc 504 + mc 824 + mc 1144 - 2*mc 504*mc 824 - 2*mc 504*mc 1144 - 2*mc 824*mc 1144 + 4*mc 504*mc 824*mc 1144) + 256*(mc 505 + mc 825 + mc 1145 - 2*mc 505*mc 825 - 2*mc 505*mc 1145 - 2*mc 825*mc 1145 + 4*mc 505*mc 825*mc 1145) + 512*(mc 506 + mc 826 + mc 1146 - 2*mc 506*mc 826 - 2*mc 506*mc 1146 - 2*mc 826*mc 1146 + 4*mc 506*mc 826*mc 1146) + 1024*(mc 507 + mc 827 + mc 1147 - 2*mc 507*mc 827 - 2*mc 507*mc 1147 - 2*mc 827*mc 1147 + 4*mc 507*mc 827*mc 1147) + 2048*(mc 508 + mc 828 + mc 1148 - 2*mc 508*mc 828 - 2*mc 508*mc 1148 - 2*mc 828*mc 1148 + 4*mc 508*mc 828*mc 1148) + 4096*(mc 509 + mc 829 + mc 1149 - 2*mc 509*mc 829 - 2*mc 509*mc 1149 - 2*mc 829*mc 1149 + 4*mc 509*mc 829*mc 1149) + 8192*(mc 510 + mc 830 + mc 1150 - 2*mc 510*mc 830 - 2*mc 510*mc 1150 - 2*mc 830*mc 1150 + 4*mc 510*mc 830*mc 1150) + 16384*(mc 511 + mc 831 + mc 1151 - 2*mc 511*mc 831 - 2*mc 511*mc 1151 - 2*mc 831*mc 1151 + 4*mc 511*mc 831*mc 1151) + 32768*(mc 512 + mc 832 + mc 1152 - 2*mc 512*mc 832 - 2*mc 512*mc 1152 - 2*mc 832*mc 1152 + 4*mc 512*mc 832*mc 1152) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1227, KeccakfPermAir.extraction.inter_877, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_876 c row = (mc 498 + mc 818 + mc 1138 - 2*mc 498*mc 818 - 2*mc 498*mc 1138 - 2*mc 818*mc 1138 + 4*mc 498*mc 818*mc 1138) + 2 * KeccakfPermAir.extraction.inter_874 c row := by
    simp only [KeccakfPermAir.extraction.inter_876, KeccakfPermAir.extraction.inter_875, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_874 c row = (mc 499 + mc 819 + mc 1139 - 2*mc 499*mc 819 - 2*mc 499*mc 1139 - 2*mc 819*mc 1139 + 4*mc 499*mc 819*mc 1139) + 2 * KeccakfPermAir.extraction.inter_872 c row := by
    simp only [KeccakfPermAir.extraction.inter_874, KeccakfPermAir.extraction.inter_873, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_872 c row = (mc 500 + mc 820 + mc 1140 - 2*mc 500*mc 820 - 2*mc 500*mc 1140 - 2*mc 820*mc 1140 + 4*mc 500*mc 820*mc 1140) + 2 * KeccakfPermAir.extraction.inter_870 c row := by
    simp only [KeccakfPermAir.extraction.inter_872, KeccakfPermAir.extraction.inter_871, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_870 c row = (mc 501 + mc 821 + mc 1141 - 2*mc 501*mc 821 - 2*mc 501*mc 1141 - 2*mc 821*mc 1141 + 4*mc 501*mc 821*mc 1141) + 2 * KeccakfPermAir.extraction.inter_868 c row := by
    simp only [KeccakfPermAir.extraction.inter_870, KeccakfPermAir.extraction.inter_869, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_868 c row = (mc 502 + mc 822 + mc 1142 - 2*mc 502*mc 822 - 2*mc 502*mc 1142 - 2*mc 822*mc 1142 + 4*mc 502*mc 822*mc 1142) + 2 * KeccakfPermAir.extraction.inter_866 c row := by
    simp only [KeccakfPermAir.extraction.inter_868, KeccakfPermAir.extraction.inter_867, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_866 c row = (mc 503 + mc 823 + mc 1143 - 2*mc 503*mc 823 - 2*mc 503*mc 1143 - 2*mc 823*mc 1143 + 4*mc 503*mc 823*mc 1143) + 2 * KeccakfPermAir.extraction.inter_864 c row := by
    simp only [KeccakfPermAir.extraction.inter_866, KeccakfPermAir.extraction.inter_865, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_864 c row = (mc 504 + mc 824 + mc 1144 - 2*mc 504*mc 824 - 2*mc 504*mc 1144 - 2*mc 824*mc 1144 + 4*mc 504*mc 824*mc 1144) + 2 * KeccakfPermAir.extraction.inter_862 c row := by
    simp only [KeccakfPermAir.extraction.inter_864, KeccakfPermAir.extraction.inter_863, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_862 c row = (mc 505 + mc 825 + mc 1145 - 2*mc 505*mc 825 - 2*mc 505*mc 1145 - 2*mc 825*mc 1145 + 4*mc 505*mc 825*mc 1145) + 2 * KeccakfPermAir.extraction.inter_860 c row := by
    simp only [KeccakfPermAir.extraction.inter_862, KeccakfPermAir.extraction.inter_861, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_860 c row = (mc 506 + mc 826 + mc 1146 - 2*mc 506*mc 826 - 2*mc 506*mc 1146 - 2*mc 826*mc 1146 + 4*mc 506*mc 826*mc 1146) + 2 * KeccakfPermAir.extraction.inter_858 c row := by
    simp only [KeccakfPermAir.extraction.inter_860, KeccakfPermAir.extraction.inter_859, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_858 c row = (mc 507 + mc 827 + mc 1147 - 2*mc 507*mc 827 - 2*mc 507*mc 1147 - 2*mc 827*mc 1147 + 4*mc 507*mc 827*mc 1147) + 2 * KeccakfPermAir.extraction.inter_856 c row := by
    simp only [KeccakfPermAir.extraction.inter_858, KeccakfPermAir.extraction.inter_857, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_856 c row = (mc 508 + mc 828 + mc 1148 - 2*mc 508*mc 828 - 2*mc 508*mc 1148 - 2*mc 828*mc 1148 + 4*mc 508*mc 828*mc 1148) + 2 * KeccakfPermAir.extraction.inter_854 c row := by
    simp only [KeccakfPermAir.extraction.inter_856, KeccakfPermAir.extraction.inter_855, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_854 c row = (mc 509 + mc 829 + mc 1149 - 2*mc 509*mc 829 - 2*mc 509*mc 1149 - 2*mc 829*mc 1149 + 4*mc 509*mc 829*mc 1149) + 2 * KeccakfPermAir.extraction.inter_852 c row := by
    simp only [KeccakfPermAir.extraction.inter_854, KeccakfPermAir.extraction.inter_853, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_852 c row = (mc 510 + mc 830 + mc 1150 - 2*mc 510*mc 830 - 2*mc 510*mc 1150 - 2*mc 830*mc 1150 + 4*mc 510*mc 830*mc 1150) + 2 * KeccakfPermAir.extraction.inter_850 c row := by
    simp only [KeccakfPermAir.extraction.inter_852, KeccakfPermAir.extraction.inter_851, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_850 c row = (mc 511 + mc 831 + mc 1151 - 2*mc 511*mc 831 - 2*mc 511*mc 1151 - 2*mc 831*mc 1151 + 4*mc 511*mc 831*mc 1151) + 2 * KeccakfPermAir.extraction.inter_848 c row := by
    simp only [KeccakfPermAir.extraction.inter_850, KeccakfPermAir.extraction.inter_849, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_848 c row = (mc 512 + mc 832 + mc 1152 - 2*mc 512*mc 832 - 2*mc 512*mc 1152 - 2*mc 832*mc 1152 + 4*mc 512*mc 832*mc 1152) := by
    simp only [KeccakfPermAir.extraction.inter_848, KeccakfPermAir.extraction.inter_847, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1228 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 513 833 1153 143 row) :
    mc 143 = (mc 513 + mc 833 + mc 1153 - 2*mc 513*mc 833 - 2*mc 513*mc 1153 - 2*mc 833*mc 1153 + 4*mc 513*mc 833*mc 1153) + 2*(mc 514 + mc 834 + mc 1154 - 2*mc 514*mc 834 - 2*mc 514*mc 1154 - 2*mc 834*mc 1154 + 4*mc 514*mc 834*mc 1154) + 4*(mc 515 + mc 835 + mc 1155 - 2*mc 515*mc 835 - 2*mc 515*mc 1155 - 2*mc 835*mc 1155 + 4*mc 515*mc 835*mc 1155) + 8*(mc 516 + mc 836 + mc 1156 - 2*mc 516*mc 836 - 2*mc 516*mc 1156 - 2*mc 836*mc 1156 + 4*mc 516*mc 836*mc 1156) + 16*(mc 517 + mc 837 + mc 1157 - 2*mc 517*mc 837 - 2*mc 517*mc 1157 - 2*mc 837*mc 1157 + 4*mc 517*mc 837*mc 1157) + 32*(mc 518 + mc 838 + mc 1158 - 2*mc 518*mc 838 - 2*mc 518*mc 1158 - 2*mc 838*mc 1158 + 4*mc 518*mc 838*mc 1158) + 64*(mc 519 + mc 839 + mc 1159 - 2*mc 519*mc 839 - 2*mc 519*mc 1159 - 2*mc 839*mc 1159 + 4*mc 519*mc 839*mc 1159) + 128*(mc 520 + mc 840 + mc 1160 - 2*mc 520*mc 840 - 2*mc 520*mc 1160 - 2*mc 840*mc 1160 + 4*mc 520*mc 840*mc 1160) + 256*(mc 521 + mc 841 + mc 1161 - 2*mc 521*mc 841 - 2*mc 521*mc 1161 - 2*mc 841*mc 1161 + 4*mc 521*mc 841*mc 1161) + 512*(mc 522 + mc 842 + mc 1162 - 2*mc 522*mc 842 - 2*mc 522*mc 1162 - 2*mc 842*mc 1162 + 4*mc 522*mc 842*mc 1162) + 1024*(mc 523 + mc 843 + mc 1163 - 2*mc 523*mc 843 - 2*mc 523*mc 1163 - 2*mc 843*mc 1163 + 4*mc 523*mc 843*mc 1163) + 2048*(mc 524 + mc 844 + mc 1164 - 2*mc 524*mc 844 - 2*mc 524*mc 1164 - 2*mc 844*mc 1164 + 4*mc 524*mc 844*mc 1164) + 4096*(mc 525 + mc 845 + mc 1165 - 2*mc 525*mc 845 - 2*mc 525*mc 1165 - 2*mc 845*mc 1165 + 4*mc 525*mc 845*mc 1165) + 8192*(mc 526 + mc 846 + mc 1166 - 2*mc 526*mc 846 - 2*mc 526*mc 1166 - 2*mc 846*mc 1166 + 4*mc 526*mc 846*mc 1166) + 16384*(mc 527 + mc 847 + mc 1167 - 2*mc 527*mc 847 - 2*mc 527*mc 1167 - 2*mc 847*mc 1167 + 4*mc 527*mc 847*mc 1167) + 32768*(mc 528 + mc 848 + mc 1168 - 2*mc 528*mc 848 - 2*mc 528*mc 1168 - 2*mc 848*mc 1168 + 4*mc 528*mc 848*mc 1168) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1228, KeccakfPermAir.extraction.inter_908, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_907 c row = (mc 514 + mc 834 + mc 1154 - 2*mc 514*mc 834 - 2*mc 514*mc 1154 - 2*mc 834*mc 1154 + 4*mc 514*mc 834*mc 1154) + 2 * KeccakfPermAir.extraction.inter_905 c row := by
    simp only [KeccakfPermAir.extraction.inter_907, KeccakfPermAir.extraction.inter_906, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_905 c row = (mc 515 + mc 835 + mc 1155 - 2*mc 515*mc 835 - 2*mc 515*mc 1155 - 2*mc 835*mc 1155 + 4*mc 515*mc 835*mc 1155) + 2 * KeccakfPermAir.extraction.inter_903 c row := by
    simp only [KeccakfPermAir.extraction.inter_905, KeccakfPermAir.extraction.inter_904, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_903 c row = (mc 516 + mc 836 + mc 1156 - 2*mc 516*mc 836 - 2*mc 516*mc 1156 - 2*mc 836*mc 1156 + 4*mc 516*mc 836*mc 1156) + 2 * KeccakfPermAir.extraction.inter_901 c row := by
    simp only [KeccakfPermAir.extraction.inter_903, KeccakfPermAir.extraction.inter_902, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_901 c row = (mc 517 + mc 837 + mc 1157 - 2*mc 517*mc 837 - 2*mc 517*mc 1157 - 2*mc 837*mc 1157 + 4*mc 517*mc 837*mc 1157) + 2 * KeccakfPermAir.extraction.inter_899 c row := by
    simp only [KeccakfPermAir.extraction.inter_901, KeccakfPermAir.extraction.inter_900, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_899 c row = (mc 518 + mc 838 + mc 1158 - 2*mc 518*mc 838 - 2*mc 518*mc 1158 - 2*mc 838*mc 1158 + 4*mc 518*mc 838*mc 1158) + 2 * KeccakfPermAir.extraction.inter_897 c row := by
    simp only [KeccakfPermAir.extraction.inter_899, KeccakfPermAir.extraction.inter_898, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_897 c row = (mc 519 + mc 839 + mc 1159 - 2*mc 519*mc 839 - 2*mc 519*mc 1159 - 2*mc 839*mc 1159 + 4*mc 519*mc 839*mc 1159) + 2 * KeccakfPermAir.extraction.inter_895 c row := by
    simp only [KeccakfPermAir.extraction.inter_897, KeccakfPermAir.extraction.inter_896, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_895 c row = (mc 520 + mc 840 + mc 1160 - 2*mc 520*mc 840 - 2*mc 520*mc 1160 - 2*mc 840*mc 1160 + 4*mc 520*mc 840*mc 1160) + 2 * KeccakfPermAir.extraction.inter_893 c row := by
    simp only [KeccakfPermAir.extraction.inter_895, KeccakfPermAir.extraction.inter_894, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_893 c row = (mc 521 + mc 841 + mc 1161 - 2*mc 521*mc 841 - 2*mc 521*mc 1161 - 2*mc 841*mc 1161 + 4*mc 521*mc 841*mc 1161) + 2 * KeccakfPermAir.extraction.inter_891 c row := by
    simp only [KeccakfPermAir.extraction.inter_893, KeccakfPermAir.extraction.inter_892, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_891 c row = (mc 522 + mc 842 + mc 1162 - 2*mc 522*mc 842 - 2*mc 522*mc 1162 - 2*mc 842*mc 1162 + 4*mc 522*mc 842*mc 1162) + 2 * KeccakfPermAir.extraction.inter_889 c row := by
    simp only [KeccakfPermAir.extraction.inter_891, KeccakfPermAir.extraction.inter_890, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_889 c row = (mc 523 + mc 843 + mc 1163 - 2*mc 523*mc 843 - 2*mc 523*mc 1163 - 2*mc 843*mc 1163 + 4*mc 523*mc 843*mc 1163) + 2 * KeccakfPermAir.extraction.inter_887 c row := by
    simp only [KeccakfPermAir.extraction.inter_889, KeccakfPermAir.extraction.inter_888, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_887 c row = (mc 524 + mc 844 + mc 1164 - 2*mc 524*mc 844 - 2*mc 524*mc 1164 - 2*mc 844*mc 1164 + 4*mc 524*mc 844*mc 1164) + 2 * KeccakfPermAir.extraction.inter_885 c row := by
    simp only [KeccakfPermAir.extraction.inter_887, KeccakfPermAir.extraction.inter_886, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_885 c row = (mc 525 + mc 845 + mc 1165 - 2*mc 525*mc 845 - 2*mc 525*mc 1165 - 2*mc 845*mc 1165 + 4*mc 525*mc 845*mc 1165) + 2 * KeccakfPermAir.extraction.inter_883 c row := by
    simp only [KeccakfPermAir.extraction.inter_885, KeccakfPermAir.extraction.inter_884, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_883 c row = (mc 526 + mc 846 + mc 1166 - 2*mc 526*mc 846 - 2*mc 526*mc 1166 - 2*mc 846*mc 1166 + 4*mc 526*mc 846*mc 1166) + 2 * KeccakfPermAir.extraction.inter_881 c row := by
    simp only [KeccakfPermAir.extraction.inter_883, KeccakfPermAir.extraction.inter_882, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_881 c row = (mc 527 + mc 847 + mc 1167 - 2*mc 527*mc 847 - 2*mc 527*mc 1167 - 2*mc 847*mc 1167 + 4*mc 527*mc 847*mc 1167) + 2 * KeccakfPermAir.extraction.inter_879 c row := by
    simp only [KeccakfPermAir.extraction.inter_881, KeccakfPermAir.extraction.inter_880, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_879 c row = (mc 528 + mc 848 + mc 1168 - 2*mc 528*mc 848 - 2*mc 528*mc 1168 - 2*mc 848*mc 1168 + 4*mc 528*mc 848*mc 1168) := by
    simp only [KeccakfPermAir.extraction.inter_879, KeccakfPermAir.extraction.inter_878, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1229 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 529 849 1169 144 row) :
    mc 144 = (mc 529 + mc 849 + mc 1169 - 2*mc 529*mc 849 - 2*mc 529*mc 1169 - 2*mc 849*mc 1169 + 4*mc 529*mc 849*mc 1169) + 2*(mc 530 + mc 850 + mc 1170 - 2*mc 530*mc 850 - 2*mc 530*mc 1170 - 2*mc 850*mc 1170 + 4*mc 530*mc 850*mc 1170) + 4*(mc 531 + mc 851 + mc 1171 - 2*mc 531*mc 851 - 2*mc 531*mc 1171 - 2*mc 851*mc 1171 + 4*mc 531*mc 851*mc 1171) + 8*(mc 532 + mc 852 + mc 1172 - 2*mc 532*mc 852 - 2*mc 532*mc 1172 - 2*mc 852*mc 1172 + 4*mc 532*mc 852*mc 1172) + 16*(mc 533 + mc 853 + mc 1173 - 2*mc 533*mc 853 - 2*mc 533*mc 1173 - 2*mc 853*mc 1173 + 4*mc 533*mc 853*mc 1173) + 32*(mc 534 + mc 854 + mc 1174 - 2*mc 534*mc 854 - 2*mc 534*mc 1174 - 2*mc 854*mc 1174 + 4*mc 534*mc 854*mc 1174) + 64*(mc 535 + mc 855 + mc 1175 - 2*mc 535*mc 855 - 2*mc 535*mc 1175 - 2*mc 855*mc 1175 + 4*mc 535*mc 855*mc 1175) + 128*(mc 536 + mc 856 + mc 1176 - 2*mc 536*mc 856 - 2*mc 536*mc 1176 - 2*mc 856*mc 1176 + 4*mc 536*mc 856*mc 1176) + 256*(mc 537 + mc 857 + mc 1177 - 2*mc 537*mc 857 - 2*mc 537*mc 1177 - 2*mc 857*mc 1177 + 4*mc 537*mc 857*mc 1177) + 512*(mc 538 + mc 858 + mc 1178 - 2*mc 538*mc 858 - 2*mc 538*mc 1178 - 2*mc 858*mc 1178 + 4*mc 538*mc 858*mc 1178) + 1024*(mc 539 + mc 859 + mc 1179 - 2*mc 539*mc 859 - 2*mc 539*mc 1179 - 2*mc 859*mc 1179 + 4*mc 539*mc 859*mc 1179) + 2048*(mc 540 + mc 860 + mc 1180 - 2*mc 540*mc 860 - 2*mc 540*mc 1180 - 2*mc 860*mc 1180 + 4*mc 540*mc 860*mc 1180) + 4096*(mc 541 + mc 861 + mc 1181 - 2*mc 541*mc 861 - 2*mc 541*mc 1181 - 2*mc 861*mc 1181 + 4*mc 541*mc 861*mc 1181) + 8192*(mc 542 + mc 862 + mc 1182 - 2*mc 542*mc 862 - 2*mc 542*mc 1182 - 2*mc 862*mc 1182 + 4*mc 542*mc 862*mc 1182) + 16384*(mc 543 + mc 863 + mc 1183 - 2*mc 543*mc 863 - 2*mc 543*mc 1183 - 2*mc 863*mc 1183 + 4*mc 543*mc 863*mc 1183) + 32768*(mc 544 + mc 864 + mc 1184 - 2*mc 544*mc 864 - 2*mc 544*mc 1184 - 2*mc 864*mc 1184 + 4*mc 544*mc 864*mc 1184) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1229, KeccakfPermAir.extraction.inter_939, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_938 c row = (mc 530 + mc 850 + mc 1170 - 2*mc 530*mc 850 - 2*mc 530*mc 1170 - 2*mc 850*mc 1170 + 4*mc 530*mc 850*mc 1170) + 2 * KeccakfPermAir.extraction.inter_936 c row := by
    simp only [KeccakfPermAir.extraction.inter_938, KeccakfPermAir.extraction.inter_937, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_936 c row = (mc 531 + mc 851 + mc 1171 - 2*mc 531*mc 851 - 2*mc 531*mc 1171 - 2*mc 851*mc 1171 + 4*mc 531*mc 851*mc 1171) + 2 * KeccakfPermAir.extraction.inter_934 c row := by
    simp only [KeccakfPermAir.extraction.inter_936, KeccakfPermAir.extraction.inter_935, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_934 c row = (mc 532 + mc 852 + mc 1172 - 2*mc 532*mc 852 - 2*mc 532*mc 1172 - 2*mc 852*mc 1172 + 4*mc 532*mc 852*mc 1172) + 2 * KeccakfPermAir.extraction.inter_932 c row := by
    simp only [KeccakfPermAir.extraction.inter_934, KeccakfPermAir.extraction.inter_933, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_932 c row = (mc 533 + mc 853 + mc 1173 - 2*mc 533*mc 853 - 2*mc 533*mc 1173 - 2*mc 853*mc 1173 + 4*mc 533*mc 853*mc 1173) + 2 * KeccakfPermAir.extraction.inter_930 c row := by
    simp only [KeccakfPermAir.extraction.inter_932, KeccakfPermAir.extraction.inter_931, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_930 c row = (mc 534 + mc 854 + mc 1174 - 2*mc 534*mc 854 - 2*mc 534*mc 1174 - 2*mc 854*mc 1174 + 4*mc 534*mc 854*mc 1174) + 2 * KeccakfPermAir.extraction.inter_928 c row := by
    simp only [KeccakfPermAir.extraction.inter_930, KeccakfPermAir.extraction.inter_929, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_928 c row = (mc 535 + mc 855 + mc 1175 - 2*mc 535*mc 855 - 2*mc 535*mc 1175 - 2*mc 855*mc 1175 + 4*mc 535*mc 855*mc 1175) + 2 * KeccakfPermAir.extraction.inter_926 c row := by
    simp only [KeccakfPermAir.extraction.inter_928, KeccakfPermAir.extraction.inter_927, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_926 c row = (mc 536 + mc 856 + mc 1176 - 2*mc 536*mc 856 - 2*mc 536*mc 1176 - 2*mc 856*mc 1176 + 4*mc 536*mc 856*mc 1176) + 2 * KeccakfPermAir.extraction.inter_924 c row := by
    simp only [KeccakfPermAir.extraction.inter_926, KeccakfPermAir.extraction.inter_925, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_924 c row = (mc 537 + mc 857 + mc 1177 - 2*mc 537*mc 857 - 2*mc 537*mc 1177 - 2*mc 857*mc 1177 + 4*mc 537*mc 857*mc 1177) + 2 * KeccakfPermAir.extraction.inter_922 c row := by
    simp only [KeccakfPermAir.extraction.inter_924, KeccakfPermAir.extraction.inter_923, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_922 c row = (mc 538 + mc 858 + mc 1178 - 2*mc 538*mc 858 - 2*mc 538*mc 1178 - 2*mc 858*mc 1178 + 4*mc 538*mc 858*mc 1178) + 2 * KeccakfPermAir.extraction.inter_920 c row := by
    simp only [KeccakfPermAir.extraction.inter_922, KeccakfPermAir.extraction.inter_921, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_920 c row = (mc 539 + mc 859 + mc 1179 - 2*mc 539*mc 859 - 2*mc 539*mc 1179 - 2*mc 859*mc 1179 + 4*mc 539*mc 859*mc 1179) + 2 * KeccakfPermAir.extraction.inter_918 c row := by
    simp only [KeccakfPermAir.extraction.inter_920, KeccakfPermAir.extraction.inter_919, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_918 c row = (mc 540 + mc 860 + mc 1180 - 2*mc 540*mc 860 - 2*mc 540*mc 1180 - 2*mc 860*mc 1180 + 4*mc 540*mc 860*mc 1180) + 2 * KeccakfPermAir.extraction.inter_916 c row := by
    simp only [KeccakfPermAir.extraction.inter_918, KeccakfPermAir.extraction.inter_917, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_916 c row = (mc 541 + mc 861 + mc 1181 - 2*mc 541*mc 861 - 2*mc 541*mc 1181 - 2*mc 861*mc 1181 + 4*mc 541*mc 861*mc 1181) + 2 * KeccakfPermAir.extraction.inter_914 c row := by
    simp only [KeccakfPermAir.extraction.inter_916, KeccakfPermAir.extraction.inter_915, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_914 c row = (mc 542 + mc 862 + mc 1182 - 2*mc 542*mc 862 - 2*mc 542*mc 1182 - 2*mc 862*mc 1182 + 4*mc 542*mc 862*mc 1182) + 2 * KeccakfPermAir.extraction.inter_912 c row := by
    simp only [KeccakfPermAir.extraction.inter_914, KeccakfPermAir.extraction.inter_913, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_912 c row = (mc 543 + mc 863 + mc 1183 - 2*mc 543*mc 863 - 2*mc 543*mc 1183 - 2*mc 863*mc 1183 + 4*mc 543*mc 863*mc 1183) + 2 * KeccakfPermAir.extraction.inter_910 c row := by
    simp only [KeccakfPermAir.extraction.inter_912, KeccakfPermAir.extraction.inter_911, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_910 c row = (mc 544 + mc 864 + mc 1184 - 2*mc 544*mc 864 - 2*mc 544*mc 1184 - 2*mc 864*mc 1184 + 4*mc 544*mc 864*mc 1184) := by
    simp only [KeccakfPermAir.extraction.inter_910, KeccakfPermAir.extraction.inter_909, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1294 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 225 545 1185 145 row) :
    mc 145 = (mc 225 + mc 545 + mc 1185 - 2*mc 225*mc 545 - 2*mc 225*mc 1185 - 2*mc 545*mc 1185 + 4*mc 225*mc 545*mc 1185) + 2*(mc 226 + mc 546 + mc 1186 - 2*mc 226*mc 546 - 2*mc 226*mc 1186 - 2*mc 546*mc 1186 + 4*mc 226*mc 546*mc 1186) + 4*(mc 227 + mc 547 + mc 1187 - 2*mc 227*mc 547 - 2*mc 227*mc 1187 - 2*mc 547*mc 1187 + 4*mc 227*mc 547*mc 1187) + 8*(mc 228 + mc 548 + mc 1188 - 2*mc 228*mc 548 - 2*mc 228*mc 1188 - 2*mc 548*mc 1188 + 4*mc 228*mc 548*mc 1188) + 16*(mc 229 + mc 549 + mc 1189 - 2*mc 229*mc 549 - 2*mc 229*mc 1189 - 2*mc 549*mc 1189 + 4*mc 229*mc 549*mc 1189) + 32*(mc 230 + mc 550 + mc 1190 - 2*mc 230*mc 550 - 2*mc 230*mc 1190 - 2*mc 550*mc 1190 + 4*mc 230*mc 550*mc 1190) + 64*(mc 231 + mc 551 + mc 1191 - 2*mc 231*mc 551 - 2*mc 231*mc 1191 - 2*mc 551*mc 1191 + 4*mc 231*mc 551*mc 1191) + 128*(mc 232 + mc 552 + mc 1192 - 2*mc 232*mc 552 - 2*mc 232*mc 1192 - 2*mc 552*mc 1192 + 4*mc 232*mc 552*mc 1192) + 256*(mc 233 + mc 553 + mc 1193 - 2*mc 233*mc 553 - 2*mc 233*mc 1193 - 2*mc 553*mc 1193 + 4*mc 233*mc 553*mc 1193) + 512*(mc 234 + mc 554 + mc 1194 - 2*mc 234*mc 554 - 2*mc 234*mc 1194 - 2*mc 554*mc 1194 + 4*mc 234*mc 554*mc 1194) + 1024*(mc 235 + mc 555 + mc 1195 - 2*mc 235*mc 555 - 2*mc 235*mc 1195 - 2*mc 555*mc 1195 + 4*mc 235*mc 555*mc 1195) + 2048*(mc 236 + mc 556 + mc 1196 - 2*mc 236*mc 556 - 2*mc 236*mc 1196 - 2*mc 556*mc 1196 + 4*mc 236*mc 556*mc 1196) + 4096*(mc 237 + mc 557 + mc 1197 - 2*mc 237*mc 557 - 2*mc 237*mc 1197 - 2*mc 557*mc 1197 + 4*mc 237*mc 557*mc 1197) + 8192*(mc 238 + mc 558 + mc 1198 - 2*mc 238*mc 558 - 2*mc 238*mc 1198 - 2*mc 558*mc 1198 + 4*mc 238*mc 558*mc 1198) + 16384*(mc 239 + mc 559 + mc 1199 - 2*mc 239*mc 559 - 2*mc 239*mc 1199 - 2*mc 559*mc 1199 + 4*mc 239*mc 559*mc 1199) + 32768*(mc 240 + mc 560 + mc 1200 - 2*mc 240*mc 560 - 2*mc 240*mc 1200 - 2*mc 560*mc 1200 + 4*mc 240*mc 560*mc 1200) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1294, KeccakfPermAir.extraction.inter_970, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_969 c row = (mc 226 + mc 546 + mc 1186 - 2*mc 226*mc 546 - 2*mc 226*mc 1186 - 2*mc 546*mc 1186 + 4*mc 226*mc 546*mc 1186) + 2 * KeccakfPermAir.extraction.inter_967 c row := by
    simp only [KeccakfPermAir.extraction.inter_969, KeccakfPermAir.extraction.inter_968, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_967 c row = (mc 227 + mc 547 + mc 1187 - 2*mc 227*mc 547 - 2*mc 227*mc 1187 - 2*mc 547*mc 1187 + 4*mc 227*mc 547*mc 1187) + 2 * KeccakfPermAir.extraction.inter_965 c row := by
    simp only [KeccakfPermAir.extraction.inter_967, KeccakfPermAir.extraction.inter_966, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_965 c row = (mc 228 + mc 548 + mc 1188 - 2*mc 228*mc 548 - 2*mc 228*mc 1188 - 2*mc 548*mc 1188 + 4*mc 228*mc 548*mc 1188) + 2 * KeccakfPermAir.extraction.inter_963 c row := by
    simp only [KeccakfPermAir.extraction.inter_965, KeccakfPermAir.extraction.inter_964, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_963 c row = (mc 229 + mc 549 + mc 1189 - 2*mc 229*mc 549 - 2*mc 229*mc 1189 - 2*mc 549*mc 1189 + 4*mc 229*mc 549*mc 1189) + 2 * KeccakfPermAir.extraction.inter_961 c row := by
    simp only [KeccakfPermAir.extraction.inter_963, KeccakfPermAir.extraction.inter_962, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_961 c row = (mc 230 + mc 550 + mc 1190 - 2*mc 230*mc 550 - 2*mc 230*mc 1190 - 2*mc 550*mc 1190 + 4*mc 230*mc 550*mc 1190) + 2 * KeccakfPermAir.extraction.inter_959 c row := by
    simp only [KeccakfPermAir.extraction.inter_961, KeccakfPermAir.extraction.inter_960, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_959 c row = (mc 231 + mc 551 + mc 1191 - 2*mc 231*mc 551 - 2*mc 231*mc 1191 - 2*mc 551*mc 1191 + 4*mc 231*mc 551*mc 1191) + 2 * KeccakfPermAir.extraction.inter_957 c row := by
    simp only [KeccakfPermAir.extraction.inter_959, KeccakfPermAir.extraction.inter_958, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_957 c row = (mc 232 + mc 552 + mc 1192 - 2*mc 232*mc 552 - 2*mc 232*mc 1192 - 2*mc 552*mc 1192 + 4*mc 232*mc 552*mc 1192) + 2 * KeccakfPermAir.extraction.inter_955 c row := by
    simp only [KeccakfPermAir.extraction.inter_957, KeccakfPermAir.extraction.inter_956, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_955 c row = (mc 233 + mc 553 + mc 1193 - 2*mc 233*mc 553 - 2*mc 233*mc 1193 - 2*mc 553*mc 1193 + 4*mc 233*mc 553*mc 1193) + 2 * KeccakfPermAir.extraction.inter_953 c row := by
    simp only [KeccakfPermAir.extraction.inter_955, KeccakfPermAir.extraction.inter_954, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_953 c row = (mc 234 + mc 554 + mc 1194 - 2*mc 234*mc 554 - 2*mc 234*mc 1194 - 2*mc 554*mc 1194 + 4*mc 234*mc 554*mc 1194) + 2 * KeccakfPermAir.extraction.inter_951 c row := by
    simp only [KeccakfPermAir.extraction.inter_953, KeccakfPermAir.extraction.inter_952, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_951 c row = (mc 235 + mc 555 + mc 1195 - 2*mc 235*mc 555 - 2*mc 235*mc 1195 - 2*mc 555*mc 1195 + 4*mc 235*mc 555*mc 1195) + 2 * KeccakfPermAir.extraction.inter_949 c row := by
    simp only [KeccakfPermAir.extraction.inter_951, KeccakfPermAir.extraction.inter_950, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_949 c row = (mc 236 + mc 556 + mc 1196 - 2*mc 236*mc 556 - 2*mc 236*mc 1196 - 2*mc 556*mc 1196 + 4*mc 236*mc 556*mc 1196) + 2 * KeccakfPermAir.extraction.inter_947 c row := by
    simp only [KeccakfPermAir.extraction.inter_949, KeccakfPermAir.extraction.inter_948, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_947 c row = (mc 237 + mc 557 + mc 1197 - 2*mc 237*mc 557 - 2*mc 237*mc 1197 - 2*mc 557*mc 1197 + 4*mc 237*mc 557*mc 1197) + 2 * KeccakfPermAir.extraction.inter_945 c row := by
    simp only [KeccakfPermAir.extraction.inter_947, KeccakfPermAir.extraction.inter_946, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_945 c row = (mc 238 + mc 558 + mc 1198 - 2*mc 238*mc 558 - 2*mc 238*mc 1198 - 2*mc 558*mc 1198 + 4*mc 238*mc 558*mc 1198) + 2 * KeccakfPermAir.extraction.inter_943 c row := by
    simp only [KeccakfPermAir.extraction.inter_945, KeccakfPermAir.extraction.inter_944, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_943 c row = (mc 239 + mc 559 + mc 1199 - 2*mc 239*mc 559 - 2*mc 239*mc 1199 - 2*mc 559*mc 1199 + 4*mc 239*mc 559*mc 1199) + 2 * KeccakfPermAir.extraction.inter_941 c row := by
    simp only [KeccakfPermAir.extraction.inter_943, KeccakfPermAir.extraction.inter_942, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_941 c row = (mc 240 + mc 560 + mc 1200 - 2*mc 240*mc 560 - 2*mc 240*mc 1200 - 2*mc 560*mc 1200 + 4*mc 240*mc 560*mc 1200) := by
    simp only [KeccakfPermAir.extraction.inter_941, KeccakfPermAir.extraction.inter_940, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1295 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 241 561 1201 146 row) :
    mc 146 = (mc 241 + mc 561 + mc 1201 - 2*mc 241*mc 561 - 2*mc 241*mc 1201 - 2*mc 561*mc 1201 + 4*mc 241*mc 561*mc 1201) + 2*(mc 242 + mc 562 + mc 1202 - 2*mc 242*mc 562 - 2*mc 242*mc 1202 - 2*mc 562*mc 1202 + 4*mc 242*mc 562*mc 1202) + 4*(mc 243 + mc 563 + mc 1203 - 2*mc 243*mc 563 - 2*mc 243*mc 1203 - 2*mc 563*mc 1203 + 4*mc 243*mc 563*mc 1203) + 8*(mc 244 + mc 564 + mc 1204 - 2*mc 244*mc 564 - 2*mc 244*mc 1204 - 2*mc 564*mc 1204 + 4*mc 244*mc 564*mc 1204) + 16*(mc 245 + mc 565 + mc 1205 - 2*mc 245*mc 565 - 2*mc 245*mc 1205 - 2*mc 565*mc 1205 + 4*mc 245*mc 565*mc 1205) + 32*(mc 246 + mc 566 + mc 1206 - 2*mc 246*mc 566 - 2*mc 246*mc 1206 - 2*mc 566*mc 1206 + 4*mc 246*mc 566*mc 1206) + 64*(mc 247 + mc 567 + mc 1207 - 2*mc 247*mc 567 - 2*mc 247*mc 1207 - 2*mc 567*mc 1207 + 4*mc 247*mc 567*mc 1207) + 128*(mc 248 + mc 568 + mc 1208 - 2*mc 248*mc 568 - 2*mc 248*mc 1208 - 2*mc 568*mc 1208 + 4*mc 248*mc 568*mc 1208) + 256*(mc 249 + mc 569 + mc 1209 - 2*mc 249*mc 569 - 2*mc 249*mc 1209 - 2*mc 569*mc 1209 + 4*mc 249*mc 569*mc 1209) + 512*(mc 250 + mc 570 + mc 1210 - 2*mc 250*mc 570 - 2*mc 250*mc 1210 - 2*mc 570*mc 1210 + 4*mc 250*mc 570*mc 1210) + 1024*(mc 251 + mc 571 + mc 1211 - 2*mc 251*mc 571 - 2*mc 251*mc 1211 - 2*mc 571*mc 1211 + 4*mc 251*mc 571*mc 1211) + 2048*(mc 252 + mc 572 + mc 1212 - 2*mc 252*mc 572 - 2*mc 252*mc 1212 - 2*mc 572*mc 1212 + 4*mc 252*mc 572*mc 1212) + 4096*(mc 253 + mc 573 + mc 1213 - 2*mc 253*mc 573 - 2*mc 253*mc 1213 - 2*mc 573*mc 1213 + 4*mc 253*mc 573*mc 1213) + 8192*(mc 254 + mc 574 + mc 1214 - 2*mc 254*mc 574 - 2*mc 254*mc 1214 - 2*mc 574*mc 1214 + 4*mc 254*mc 574*mc 1214) + 16384*(mc 255 + mc 575 + mc 1215 - 2*mc 255*mc 575 - 2*mc 255*mc 1215 - 2*mc 575*mc 1215 + 4*mc 255*mc 575*mc 1215) + 32768*(mc 256 + mc 576 + mc 1216 - 2*mc 256*mc 576 - 2*mc 256*mc 1216 - 2*mc 576*mc 1216 + 4*mc 256*mc 576*mc 1216) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1295, KeccakfPermAir.extraction.inter_1001, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_1000 c row = (mc 242 + mc 562 + mc 1202 - 2*mc 242*mc 562 - 2*mc 242*mc 1202 - 2*mc 562*mc 1202 + 4*mc 242*mc 562*mc 1202) + 2 * KeccakfPermAir.extraction.inter_998 c row := by
    simp only [KeccakfPermAir.extraction.inter_1000, KeccakfPermAir.extraction.inter_999, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_998 c row = (mc 243 + mc 563 + mc 1203 - 2*mc 243*mc 563 - 2*mc 243*mc 1203 - 2*mc 563*mc 1203 + 4*mc 243*mc 563*mc 1203) + 2 * KeccakfPermAir.extraction.inter_996 c row := by
    simp only [KeccakfPermAir.extraction.inter_998, KeccakfPermAir.extraction.inter_997, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_996 c row = (mc 244 + mc 564 + mc 1204 - 2*mc 244*mc 564 - 2*mc 244*mc 1204 - 2*mc 564*mc 1204 + 4*mc 244*mc 564*mc 1204) + 2 * KeccakfPermAir.extraction.inter_994 c row := by
    simp only [KeccakfPermAir.extraction.inter_996, KeccakfPermAir.extraction.inter_995, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_994 c row = (mc 245 + mc 565 + mc 1205 - 2*mc 245*mc 565 - 2*mc 245*mc 1205 - 2*mc 565*mc 1205 + 4*mc 245*mc 565*mc 1205) + 2 * KeccakfPermAir.extraction.inter_992 c row := by
    simp only [KeccakfPermAir.extraction.inter_994, KeccakfPermAir.extraction.inter_993, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_992 c row = (mc 246 + mc 566 + mc 1206 - 2*mc 246*mc 566 - 2*mc 246*mc 1206 - 2*mc 566*mc 1206 + 4*mc 246*mc 566*mc 1206) + 2 * KeccakfPermAir.extraction.inter_990 c row := by
    simp only [KeccakfPermAir.extraction.inter_992, KeccakfPermAir.extraction.inter_991, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_990 c row = (mc 247 + mc 567 + mc 1207 - 2*mc 247*mc 567 - 2*mc 247*mc 1207 - 2*mc 567*mc 1207 + 4*mc 247*mc 567*mc 1207) + 2 * KeccakfPermAir.extraction.inter_988 c row := by
    simp only [KeccakfPermAir.extraction.inter_990, KeccakfPermAir.extraction.inter_989, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_988 c row = (mc 248 + mc 568 + mc 1208 - 2*mc 248*mc 568 - 2*mc 248*mc 1208 - 2*mc 568*mc 1208 + 4*mc 248*mc 568*mc 1208) + 2 * KeccakfPermAir.extraction.inter_986 c row := by
    simp only [KeccakfPermAir.extraction.inter_988, KeccakfPermAir.extraction.inter_987, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_986 c row = (mc 249 + mc 569 + mc 1209 - 2*mc 249*mc 569 - 2*mc 249*mc 1209 - 2*mc 569*mc 1209 + 4*mc 249*mc 569*mc 1209) + 2 * KeccakfPermAir.extraction.inter_984 c row := by
    simp only [KeccakfPermAir.extraction.inter_986, KeccakfPermAir.extraction.inter_985, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_984 c row = (mc 250 + mc 570 + mc 1210 - 2*mc 250*mc 570 - 2*mc 250*mc 1210 - 2*mc 570*mc 1210 + 4*mc 250*mc 570*mc 1210) + 2 * KeccakfPermAir.extraction.inter_982 c row := by
    simp only [KeccakfPermAir.extraction.inter_984, KeccakfPermAir.extraction.inter_983, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_982 c row = (mc 251 + mc 571 + mc 1211 - 2*mc 251*mc 571 - 2*mc 251*mc 1211 - 2*mc 571*mc 1211 + 4*mc 251*mc 571*mc 1211) + 2 * KeccakfPermAir.extraction.inter_980 c row := by
    simp only [KeccakfPermAir.extraction.inter_982, KeccakfPermAir.extraction.inter_981, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_980 c row = (mc 252 + mc 572 + mc 1212 - 2*mc 252*mc 572 - 2*mc 252*mc 1212 - 2*mc 572*mc 1212 + 4*mc 252*mc 572*mc 1212) + 2 * KeccakfPermAir.extraction.inter_978 c row := by
    simp only [KeccakfPermAir.extraction.inter_980, KeccakfPermAir.extraction.inter_979, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_978 c row = (mc 253 + mc 573 + mc 1213 - 2*mc 253*mc 573 - 2*mc 253*mc 1213 - 2*mc 573*mc 1213 + 4*mc 253*mc 573*mc 1213) + 2 * KeccakfPermAir.extraction.inter_976 c row := by
    simp only [KeccakfPermAir.extraction.inter_978, KeccakfPermAir.extraction.inter_977, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_976 c row = (mc 254 + mc 574 + mc 1214 - 2*mc 254*mc 574 - 2*mc 254*mc 1214 - 2*mc 574*mc 1214 + 4*mc 254*mc 574*mc 1214) + 2 * KeccakfPermAir.extraction.inter_974 c row := by
    simp only [KeccakfPermAir.extraction.inter_976, KeccakfPermAir.extraction.inter_975, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_974 c row = (mc 255 + mc 575 + mc 1215 - 2*mc 255*mc 575 - 2*mc 255*mc 1215 - 2*mc 575*mc 1215 + 4*mc 255*mc 575*mc 1215) + 2 * KeccakfPermAir.extraction.inter_972 c row := by
    simp only [KeccakfPermAir.extraction.inter_974, KeccakfPermAir.extraction.inter_973, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_972 c row = (mc 256 + mc 576 + mc 1216 - 2*mc 256*mc 576 - 2*mc 256*mc 1216 - 2*mc 576*mc 1216 + 4*mc 256*mc 576*mc 1216) := by
    simp only [KeccakfPermAir.extraction.inter_972, KeccakfPermAir.extraction.inter_971, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1296 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 257 577 1217 147 row) :
    mc 147 = (mc 257 + mc 577 + mc 1217 - 2*mc 257*mc 577 - 2*mc 257*mc 1217 - 2*mc 577*mc 1217 + 4*mc 257*mc 577*mc 1217) + 2*(mc 258 + mc 578 + mc 1218 - 2*mc 258*mc 578 - 2*mc 258*mc 1218 - 2*mc 578*mc 1218 + 4*mc 258*mc 578*mc 1218) + 4*(mc 259 + mc 579 + mc 1219 - 2*mc 259*mc 579 - 2*mc 259*mc 1219 - 2*mc 579*mc 1219 + 4*mc 259*mc 579*mc 1219) + 8*(mc 260 + mc 580 + mc 1220 - 2*mc 260*mc 580 - 2*mc 260*mc 1220 - 2*mc 580*mc 1220 + 4*mc 260*mc 580*mc 1220) + 16*(mc 261 + mc 581 + mc 1221 - 2*mc 261*mc 581 - 2*mc 261*mc 1221 - 2*mc 581*mc 1221 + 4*mc 261*mc 581*mc 1221) + 32*(mc 262 + mc 582 + mc 1222 - 2*mc 262*mc 582 - 2*mc 262*mc 1222 - 2*mc 582*mc 1222 + 4*mc 262*mc 582*mc 1222) + 64*(mc 263 + mc 583 + mc 1223 - 2*mc 263*mc 583 - 2*mc 263*mc 1223 - 2*mc 583*mc 1223 + 4*mc 263*mc 583*mc 1223) + 128*(mc 264 + mc 584 + mc 1224 - 2*mc 264*mc 584 - 2*mc 264*mc 1224 - 2*mc 584*mc 1224 + 4*mc 264*mc 584*mc 1224) + 256*(mc 265 + mc 585 + mc 1225 - 2*mc 265*mc 585 - 2*mc 265*mc 1225 - 2*mc 585*mc 1225 + 4*mc 265*mc 585*mc 1225) + 512*(mc 266 + mc 586 + mc 1226 - 2*mc 266*mc 586 - 2*mc 266*mc 1226 - 2*mc 586*mc 1226 + 4*mc 266*mc 586*mc 1226) + 1024*(mc 267 + mc 587 + mc 1227 - 2*mc 267*mc 587 - 2*mc 267*mc 1227 - 2*mc 587*mc 1227 + 4*mc 267*mc 587*mc 1227) + 2048*(mc 268 + mc 588 + mc 1228 - 2*mc 268*mc 588 - 2*mc 268*mc 1228 - 2*mc 588*mc 1228 + 4*mc 268*mc 588*mc 1228) + 4096*(mc 269 + mc 589 + mc 1229 - 2*mc 269*mc 589 - 2*mc 269*mc 1229 - 2*mc 589*mc 1229 + 4*mc 269*mc 589*mc 1229) + 8192*(mc 270 + mc 590 + mc 1230 - 2*mc 270*mc 590 - 2*mc 270*mc 1230 - 2*mc 590*mc 1230 + 4*mc 270*mc 590*mc 1230) + 16384*(mc 271 + mc 591 + mc 1231 - 2*mc 271*mc 591 - 2*mc 271*mc 1231 - 2*mc 591*mc 1231 + 4*mc 271*mc 591*mc 1231) + 32768*(mc 272 + mc 592 + mc 1232 - 2*mc 272*mc 592 - 2*mc 272*mc 1232 - 2*mc 592*mc 1232 + 4*mc 272*mc 592*mc 1232) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1296, KeccakfPermAir.extraction.inter_1032, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_1031 c row = (mc 258 + mc 578 + mc 1218 - 2*mc 258*mc 578 - 2*mc 258*mc 1218 - 2*mc 578*mc 1218 + 4*mc 258*mc 578*mc 1218) + 2 * KeccakfPermAir.extraction.inter_1029 c row := by
    simp only [KeccakfPermAir.extraction.inter_1031, KeccakfPermAir.extraction.inter_1030, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_1029 c row = (mc 259 + mc 579 + mc 1219 - 2*mc 259*mc 579 - 2*mc 259*mc 1219 - 2*mc 579*mc 1219 + 4*mc 259*mc 579*mc 1219) + 2 * KeccakfPermAir.extraction.inter_1027 c row := by
    simp only [KeccakfPermAir.extraction.inter_1029, KeccakfPermAir.extraction.inter_1028, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_1027 c row = (mc 260 + mc 580 + mc 1220 - 2*mc 260*mc 580 - 2*mc 260*mc 1220 - 2*mc 580*mc 1220 + 4*mc 260*mc 580*mc 1220) + 2 * KeccakfPermAir.extraction.inter_1025 c row := by
    simp only [KeccakfPermAir.extraction.inter_1027, KeccakfPermAir.extraction.inter_1026, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_1025 c row = (mc 261 + mc 581 + mc 1221 - 2*mc 261*mc 581 - 2*mc 261*mc 1221 - 2*mc 581*mc 1221 + 4*mc 261*mc 581*mc 1221) + 2 * KeccakfPermAir.extraction.inter_1023 c row := by
    simp only [KeccakfPermAir.extraction.inter_1025, KeccakfPermAir.extraction.inter_1024, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_1023 c row = (mc 262 + mc 582 + mc 1222 - 2*mc 262*mc 582 - 2*mc 262*mc 1222 - 2*mc 582*mc 1222 + 4*mc 262*mc 582*mc 1222) + 2 * KeccakfPermAir.extraction.inter_1021 c row := by
    simp only [KeccakfPermAir.extraction.inter_1023, KeccakfPermAir.extraction.inter_1022, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_1021 c row = (mc 263 + mc 583 + mc 1223 - 2*mc 263*mc 583 - 2*mc 263*mc 1223 - 2*mc 583*mc 1223 + 4*mc 263*mc 583*mc 1223) + 2 * KeccakfPermAir.extraction.inter_1019 c row := by
    simp only [KeccakfPermAir.extraction.inter_1021, KeccakfPermAir.extraction.inter_1020, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_1019 c row = (mc 264 + mc 584 + mc 1224 - 2*mc 264*mc 584 - 2*mc 264*mc 1224 - 2*mc 584*mc 1224 + 4*mc 264*mc 584*mc 1224) + 2 * KeccakfPermAir.extraction.inter_1017 c row := by
    simp only [KeccakfPermAir.extraction.inter_1019, KeccakfPermAir.extraction.inter_1018, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_1017 c row = (mc 265 + mc 585 + mc 1225 - 2*mc 265*mc 585 - 2*mc 265*mc 1225 - 2*mc 585*mc 1225 + 4*mc 265*mc 585*mc 1225) + 2 * KeccakfPermAir.extraction.inter_1015 c row := by
    simp only [KeccakfPermAir.extraction.inter_1017, KeccakfPermAir.extraction.inter_1016, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_1015 c row = (mc 266 + mc 586 + mc 1226 - 2*mc 266*mc 586 - 2*mc 266*mc 1226 - 2*mc 586*mc 1226 + 4*mc 266*mc 586*mc 1226) + 2 * KeccakfPermAir.extraction.inter_1013 c row := by
    simp only [KeccakfPermAir.extraction.inter_1015, KeccakfPermAir.extraction.inter_1014, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_1013 c row = (mc 267 + mc 587 + mc 1227 - 2*mc 267*mc 587 - 2*mc 267*mc 1227 - 2*mc 587*mc 1227 + 4*mc 267*mc 587*mc 1227) + 2 * KeccakfPermAir.extraction.inter_1011 c row := by
    simp only [KeccakfPermAir.extraction.inter_1013, KeccakfPermAir.extraction.inter_1012, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_1011 c row = (mc 268 + mc 588 + mc 1228 - 2*mc 268*mc 588 - 2*mc 268*mc 1228 - 2*mc 588*mc 1228 + 4*mc 268*mc 588*mc 1228) + 2 * KeccakfPermAir.extraction.inter_1009 c row := by
    simp only [KeccakfPermAir.extraction.inter_1011, KeccakfPermAir.extraction.inter_1010, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_1009 c row = (mc 269 + mc 589 + mc 1229 - 2*mc 269*mc 589 - 2*mc 269*mc 1229 - 2*mc 589*mc 1229 + 4*mc 269*mc 589*mc 1229) + 2 * KeccakfPermAir.extraction.inter_1007 c row := by
    simp only [KeccakfPermAir.extraction.inter_1009, KeccakfPermAir.extraction.inter_1008, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_1007 c row = (mc 270 + mc 590 + mc 1230 - 2*mc 270*mc 590 - 2*mc 270*mc 1230 - 2*mc 590*mc 1230 + 4*mc 270*mc 590*mc 1230) + 2 * KeccakfPermAir.extraction.inter_1005 c row := by
    simp only [KeccakfPermAir.extraction.inter_1007, KeccakfPermAir.extraction.inter_1006, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_1005 c row = (mc 271 + mc 591 + mc 1231 - 2*mc 271*mc 591 - 2*mc 271*mc 1231 - 2*mc 591*mc 1231 + 4*mc 271*mc 591*mc 1231) + 2 * KeccakfPermAir.extraction.inter_1003 c row := by
    simp only [KeccakfPermAir.extraction.inter_1005, KeccakfPermAir.extraction.inter_1004, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_1003 c row = (mc 272 + mc 592 + mc 1232 - 2*mc 272*mc 592 - 2*mc 272*mc 1232 - 2*mc 592*mc 1232 + 4*mc 272*mc 592*mc 1232) := by
    simp only [KeccakfPermAir.extraction.inter_1003, KeccakfPermAir.extraction.inter_1002, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1297 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 273 593 1233 148 row) :
    mc 148 = (mc 273 + mc 593 + mc 1233 - 2*mc 273*mc 593 - 2*mc 273*mc 1233 - 2*mc 593*mc 1233 + 4*mc 273*mc 593*mc 1233) + 2*(mc 274 + mc 594 + mc 1234 - 2*mc 274*mc 594 - 2*mc 274*mc 1234 - 2*mc 594*mc 1234 + 4*mc 274*mc 594*mc 1234) + 4*(mc 275 + mc 595 + mc 1235 - 2*mc 275*mc 595 - 2*mc 275*mc 1235 - 2*mc 595*mc 1235 + 4*mc 275*mc 595*mc 1235) + 8*(mc 276 + mc 596 + mc 1236 - 2*mc 276*mc 596 - 2*mc 276*mc 1236 - 2*mc 596*mc 1236 + 4*mc 276*mc 596*mc 1236) + 16*(mc 277 + mc 597 + mc 1237 - 2*mc 277*mc 597 - 2*mc 277*mc 1237 - 2*mc 597*mc 1237 + 4*mc 277*mc 597*mc 1237) + 32*(mc 278 + mc 598 + mc 1238 - 2*mc 278*mc 598 - 2*mc 278*mc 1238 - 2*mc 598*mc 1238 + 4*mc 278*mc 598*mc 1238) + 64*(mc 279 + mc 599 + mc 1239 - 2*mc 279*mc 599 - 2*mc 279*mc 1239 - 2*mc 599*mc 1239 + 4*mc 279*mc 599*mc 1239) + 128*(mc 280 + mc 600 + mc 1240 - 2*mc 280*mc 600 - 2*mc 280*mc 1240 - 2*mc 600*mc 1240 + 4*mc 280*mc 600*mc 1240) + 256*(mc 281 + mc 601 + mc 1241 - 2*mc 281*mc 601 - 2*mc 281*mc 1241 - 2*mc 601*mc 1241 + 4*mc 281*mc 601*mc 1241) + 512*(mc 282 + mc 602 + mc 1242 - 2*mc 282*mc 602 - 2*mc 282*mc 1242 - 2*mc 602*mc 1242 + 4*mc 282*mc 602*mc 1242) + 1024*(mc 283 + mc 603 + mc 1243 - 2*mc 283*mc 603 - 2*mc 283*mc 1243 - 2*mc 603*mc 1243 + 4*mc 283*mc 603*mc 1243) + 2048*(mc 284 + mc 604 + mc 1244 - 2*mc 284*mc 604 - 2*mc 284*mc 1244 - 2*mc 604*mc 1244 + 4*mc 284*mc 604*mc 1244) + 4096*(mc 285 + mc 605 + mc 1245 - 2*mc 285*mc 605 - 2*mc 285*mc 1245 - 2*mc 605*mc 1245 + 4*mc 285*mc 605*mc 1245) + 8192*(mc 286 + mc 606 + mc 1246 - 2*mc 286*mc 606 - 2*mc 286*mc 1246 - 2*mc 606*mc 1246 + 4*mc 286*mc 606*mc 1246) + 16384*(mc 287 + mc 607 + mc 1247 - 2*mc 287*mc 607 - 2*mc 287*mc 1247 - 2*mc 607*mc 1247 + 4*mc 287*mc 607*mc 1247) + 32768*(mc 288 + mc 608 + mc 1248 - 2*mc 288*mc 608 - 2*mc 288*mc 1248 - 2*mc 608*mc 1248 + 4*mc 288*mc 608*mc 1248) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1297, KeccakfPermAir.extraction.inter_1063, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_1062 c row = (mc 274 + mc 594 + mc 1234 - 2*mc 274*mc 594 - 2*mc 274*mc 1234 - 2*mc 594*mc 1234 + 4*mc 274*mc 594*mc 1234) + 2 * KeccakfPermAir.extraction.inter_1060 c row := by
    simp only [KeccakfPermAir.extraction.inter_1062, KeccakfPermAir.extraction.inter_1061, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_1060 c row = (mc 275 + mc 595 + mc 1235 - 2*mc 275*mc 595 - 2*mc 275*mc 1235 - 2*mc 595*mc 1235 + 4*mc 275*mc 595*mc 1235) + 2 * KeccakfPermAir.extraction.inter_1058 c row := by
    simp only [KeccakfPermAir.extraction.inter_1060, KeccakfPermAir.extraction.inter_1059, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_1058 c row = (mc 276 + mc 596 + mc 1236 - 2*mc 276*mc 596 - 2*mc 276*mc 1236 - 2*mc 596*mc 1236 + 4*mc 276*mc 596*mc 1236) + 2 * KeccakfPermAir.extraction.inter_1056 c row := by
    simp only [KeccakfPermAir.extraction.inter_1058, KeccakfPermAir.extraction.inter_1057, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_1056 c row = (mc 277 + mc 597 + mc 1237 - 2*mc 277*mc 597 - 2*mc 277*mc 1237 - 2*mc 597*mc 1237 + 4*mc 277*mc 597*mc 1237) + 2 * KeccakfPermAir.extraction.inter_1054 c row := by
    simp only [KeccakfPermAir.extraction.inter_1056, KeccakfPermAir.extraction.inter_1055, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_1054 c row = (mc 278 + mc 598 + mc 1238 - 2*mc 278*mc 598 - 2*mc 278*mc 1238 - 2*mc 598*mc 1238 + 4*mc 278*mc 598*mc 1238) + 2 * KeccakfPermAir.extraction.inter_1052 c row := by
    simp only [KeccakfPermAir.extraction.inter_1054, KeccakfPermAir.extraction.inter_1053, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_1052 c row = (mc 279 + mc 599 + mc 1239 - 2*mc 279*mc 599 - 2*mc 279*mc 1239 - 2*mc 599*mc 1239 + 4*mc 279*mc 599*mc 1239) + 2 * KeccakfPermAir.extraction.inter_1050 c row := by
    simp only [KeccakfPermAir.extraction.inter_1052, KeccakfPermAir.extraction.inter_1051, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_1050 c row = (mc 280 + mc 600 + mc 1240 - 2*mc 280*mc 600 - 2*mc 280*mc 1240 - 2*mc 600*mc 1240 + 4*mc 280*mc 600*mc 1240) + 2 * KeccakfPermAir.extraction.inter_1048 c row := by
    simp only [KeccakfPermAir.extraction.inter_1050, KeccakfPermAir.extraction.inter_1049, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_1048 c row = (mc 281 + mc 601 + mc 1241 - 2*mc 281*mc 601 - 2*mc 281*mc 1241 - 2*mc 601*mc 1241 + 4*mc 281*mc 601*mc 1241) + 2 * KeccakfPermAir.extraction.inter_1046 c row := by
    simp only [KeccakfPermAir.extraction.inter_1048, KeccakfPermAir.extraction.inter_1047, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_1046 c row = (mc 282 + mc 602 + mc 1242 - 2*mc 282*mc 602 - 2*mc 282*mc 1242 - 2*mc 602*mc 1242 + 4*mc 282*mc 602*mc 1242) + 2 * KeccakfPermAir.extraction.inter_1044 c row := by
    simp only [KeccakfPermAir.extraction.inter_1046, KeccakfPermAir.extraction.inter_1045, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_1044 c row = (mc 283 + mc 603 + mc 1243 - 2*mc 283*mc 603 - 2*mc 283*mc 1243 - 2*mc 603*mc 1243 + 4*mc 283*mc 603*mc 1243) + 2 * KeccakfPermAir.extraction.inter_1042 c row := by
    simp only [KeccakfPermAir.extraction.inter_1044, KeccakfPermAir.extraction.inter_1043, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_1042 c row = (mc 284 + mc 604 + mc 1244 - 2*mc 284*mc 604 - 2*mc 284*mc 1244 - 2*mc 604*mc 1244 + 4*mc 284*mc 604*mc 1244) + 2 * KeccakfPermAir.extraction.inter_1040 c row := by
    simp only [KeccakfPermAir.extraction.inter_1042, KeccakfPermAir.extraction.inter_1041, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_1040 c row = (mc 285 + mc 605 + mc 1245 - 2*mc 285*mc 605 - 2*mc 285*mc 1245 - 2*mc 605*mc 1245 + 4*mc 285*mc 605*mc 1245) + 2 * KeccakfPermAir.extraction.inter_1038 c row := by
    simp only [KeccakfPermAir.extraction.inter_1040, KeccakfPermAir.extraction.inter_1039, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_1038 c row = (mc 286 + mc 606 + mc 1246 - 2*mc 286*mc 606 - 2*mc 286*mc 1246 - 2*mc 606*mc 1246 + 4*mc 286*mc 606*mc 1246) + 2 * KeccakfPermAir.extraction.inter_1036 c row := by
    simp only [KeccakfPermAir.extraction.inter_1038, KeccakfPermAir.extraction.inter_1037, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_1036 c row = (mc 287 + mc 607 + mc 1247 - 2*mc 287*mc 607 - 2*mc 287*mc 1247 - 2*mc 607*mc 1247 + 4*mc 287*mc 607*mc 1247) + 2 * KeccakfPermAir.extraction.inter_1034 c row := by
    simp only [KeccakfPermAir.extraction.inter_1036, KeccakfPermAir.extraction.inter_1035, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_1034 c row = (mc 288 + mc 608 + mc 1248 - 2*mc 288*mc 608 - 2*mc 288*mc 1248 - 2*mc 608*mc 1248 + 4*mc 288*mc 608*mc 1248) := by
    simp only [KeccakfPermAir.extraction.inter_1034, KeccakfPermAir.extraction.inter_1033, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1362 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 289 609 1249 149 row) :
    mc 149 = (mc 289 + mc 609 + mc 1249 - 2*mc 289*mc 609 - 2*mc 289*mc 1249 - 2*mc 609*mc 1249 + 4*mc 289*mc 609*mc 1249) + 2*(mc 290 + mc 610 + mc 1250 - 2*mc 290*mc 610 - 2*mc 290*mc 1250 - 2*mc 610*mc 1250 + 4*mc 290*mc 610*mc 1250) + 4*(mc 291 + mc 611 + mc 1251 - 2*mc 291*mc 611 - 2*mc 291*mc 1251 - 2*mc 611*mc 1251 + 4*mc 291*mc 611*mc 1251) + 8*(mc 292 + mc 612 + mc 1252 - 2*mc 292*mc 612 - 2*mc 292*mc 1252 - 2*mc 612*mc 1252 + 4*mc 292*mc 612*mc 1252) + 16*(mc 293 + mc 613 + mc 1253 - 2*mc 293*mc 613 - 2*mc 293*mc 1253 - 2*mc 613*mc 1253 + 4*mc 293*mc 613*mc 1253) + 32*(mc 294 + mc 614 + mc 1254 - 2*mc 294*mc 614 - 2*mc 294*mc 1254 - 2*mc 614*mc 1254 + 4*mc 294*mc 614*mc 1254) + 64*(mc 295 + mc 615 + mc 1255 - 2*mc 295*mc 615 - 2*mc 295*mc 1255 - 2*mc 615*mc 1255 + 4*mc 295*mc 615*mc 1255) + 128*(mc 296 + mc 616 + mc 1256 - 2*mc 296*mc 616 - 2*mc 296*mc 1256 - 2*mc 616*mc 1256 + 4*mc 296*mc 616*mc 1256) + 256*(mc 297 + mc 617 + mc 1257 - 2*mc 297*mc 617 - 2*mc 297*mc 1257 - 2*mc 617*mc 1257 + 4*mc 297*mc 617*mc 1257) + 512*(mc 298 + mc 618 + mc 1258 - 2*mc 298*mc 618 - 2*mc 298*mc 1258 - 2*mc 618*mc 1258 + 4*mc 298*mc 618*mc 1258) + 1024*(mc 299 + mc 619 + mc 1259 - 2*mc 299*mc 619 - 2*mc 299*mc 1259 - 2*mc 619*mc 1259 + 4*mc 299*mc 619*mc 1259) + 2048*(mc 300 + mc 620 + mc 1260 - 2*mc 300*mc 620 - 2*mc 300*mc 1260 - 2*mc 620*mc 1260 + 4*mc 300*mc 620*mc 1260) + 4096*(mc 301 + mc 621 + mc 1261 - 2*mc 301*mc 621 - 2*mc 301*mc 1261 - 2*mc 621*mc 1261 + 4*mc 301*mc 621*mc 1261) + 8192*(mc 302 + mc 622 + mc 1262 - 2*mc 302*mc 622 - 2*mc 302*mc 1262 - 2*mc 622*mc 1262 + 4*mc 302*mc 622*mc 1262) + 16384*(mc 303 + mc 623 + mc 1263 - 2*mc 303*mc 623 - 2*mc 303*mc 1263 - 2*mc 623*mc 1263 + 4*mc 303*mc 623*mc 1263) + 32768*(mc 304 + mc 624 + mc 1264 - 2*mc 304*mc 624 - 2*mc 304*mc 1264 - 2*mc 624*mc 1264 + 4*mc 304*mc 624*mc 1264) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1362, KeccakfPermAir.extraction.inter_1094, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_1093 c row = (mc 290 + mc 610 + mc 1250 - 2*mc 290*mc 610 - 2*mc 290*mc 1250 - 2*mc 610*mc 1250 + 4*mc 290*mc 610*mc 1250) + 2 * KeccakfPermAir.extraction.inter_1091 c row := by
    simp only [KeccakfPermAir.extraction.inter_1093, KeccakfPermAir.extraction.inter_1092, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_1091 c row = (mc 291 + mc 611 + mc 1251 - 2*mc 291*mc 611 - 2*mc 291*mc 1251 - 2*mc 611*mc 1251 + 4*mc 291*mc 611*mc 1251) + 2 * KeccakfPermAir.extraction.inter_1089 c row := by
    simp only [KeccakfPermAir.extraction.inter_1091, KeccakfPermAir.extraction.inter_1090, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_1089 c row = (mc 292 + mc 612 + mc 1252 - 2*mc 292*mc 612 - 2*mc 292*mc 1252 - 2*mc 612*mc 1252 + 4*mc 292*mc 612*mc 1252) + 2 * KeccakfPermAir.extraction.inter_1087 c row := by
    simp only [KeccakfPermAir.extraction.inter_1089, KeccakfPermAir.extraction.inter_1088, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_1087 c row = (mc 293 + mc 613 + mc 1253 - 2*mc 293*mc 613 - 2*mc 293*mc 1253 - 2*mc 613*mc 1253 + 4*mc 293*mc 613*mc 1253) + 2 * KeccakfPermAir.extraction.inter_1085 c row := by
    simp only [KeccakfPermAir.extraction.inter_1087, KeccakfPermAir.extraction.inter_1086, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_1085 c row = (mc 294 + mc 614 + mc 1254 - 2*mc 294*mc 614 - 2*mc 294*mc 1254 - 2*mc 614*mc 1254 + 4*mc 294*mc 614*mc 1254) + 2 * KeccakfPermAir.extraction.inter_1083 c row := by
    simp only [KeccakfPermAir.extraction.inter_1085, KeccakfPermAir.extraction.inter_1084, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_1083 c row = (mc 295 + mc 615 + mc 1255 - 2*mc 295*mc 615 - 2*mc 295*mc 1255 - 2*mc 615*mc 1255 + 4*mc 295*mc 615*mc 1255) + 2 * KeccakfPermAir.extraction.inter_1081 c row := by
    simp only [KeccakfPermAir.extraction.inter_1083, KeccakfPermAir.extraction.inter_1082, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_1081 c row = (mc 296 + mc 616 + mc 1256 - 2*mc 296*mc 616 - 2*mc 296*mc 1256 - 2*mc 616*mc 1256 + 4*mc 296*mc 616*mc 1256) + 2 * KeccakfPermAir.extraction.inter_1079 c row := by
    simp only [KeccakfPermAir.extraction.inter_1081, KeccakfPermAir.extraction.inter_1080, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_1079 c row = (mc 297 + mc 617 + mc 1257 - 2*mc 297*mc 617 - 2*mc 297*mc 1257 - 2*mc 617*mc 1257 + 4*mc 297*mc 617*mc 1257) + 2 * KeccakfPermAir.extraction.inter_1077 c row := by
    simp only [KeccakfPermAir.extraction.inter_1079, KeccakfPermAir.extraction.inter_1078, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_1077 c row = (mc 298 + mc 618 + mc 1258 - 2*mc 298*mc 618 - 2*mc 298*mc 1258 - 2*mc 618*mc 1258 + 4*mc 298*mc 618*mc 1258) + 2 * KeccakfPermAir.extraction.inter_1075 c row := by
    simp only [KeccakfPermAir.extraction.inter_1077, KeccakfPermAir.extraction.inter_1076, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_1075 c row = (mc 299 + mc 619 + mc 1259 - 2*mc 299*mc 619 - 2*mc 299*mc 1259 - 2*mc 619*mc 1259 + 4*mc 299*mc 619*mc 1259) + 2 * KeccakfPermAir.extraction.inter_1073 c row := by
    simp only [KeccakfPermAir.extraction.inter_1075, KeccakfPermAir.extraction.inter_1074, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_1073 c row = (mc 300 + mc 620 + mc 1260 - 2*mc 300*mc 620 - 2*mc 300*mc 1260 - 2*mc 620*mc 1260 + 4*mc 300*mc 620*mc 1260) + 2 * KeccakfPermAir.extraction.inter_1071 c row := by
    simp only [KeccakfPermAir.extraction.inter_1073, KeccakfPermAir.extraction.inter_1072, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_1071 c row = (mc 301 + mc 621 + mc 1261 - 2*mc 301*mc 621 - 2*mc 301*mc 1261 - 2*mc 621*mc 1261 + 4*mc 301*mc 621*mc 1261) + 2 * KeccakfPermAir.extraction.inter_1069 c row := by
    simp only [KeccakfPermAir.extraction.inter_1071, KeccakfPermAir.extraction.inter_1070, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_1069 c row = (mc 302 + mc 622 + mc 1262 - 2*mc 302*mc 622 - 2*mc 302*mc 1262 - 2*mc 622*mc 1262 + 4*mc 302*mc 622*mc 1262) + 2 * KeccakfPermAir.extraction.inter_1067 c row := by
    simp only [KeccakfPermAir.extraction.inter_1069, KeccakfPermAir.extraction.inter_1068, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_1067 c row = (mc 303 + mc 623 + mc 1263 - 2*mc 303*mc 623 - 2*mc 303*mc 1263 - 2*mc 623*mc 1263 + 4*mc 303*mc 623*mc 1263) + 2 * KeccakfPermAir.extraction.inter_1065 c row := by
    simp only [KeccakfPermAir.extraction.inter_1067, KeccakfPermAir.extraction.inter_1066, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_1065 c row = (mc 304 + mc 624 + mc 1264 - 2*mc 304*mc 624 - 2*mc 304*mc 1264 - 2*mc 624*mc 1264 + 4*mc 304*mc 624*mc 1264) := by
    simp only [KeccakfPermAir.extraction.inter_1065, KeccakfPermAir.extraction.inter_1064, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1363 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 305 625 1265 150 row) :
    mc 150 = (mc 305 + mc 625 + mc 1265 - 2*mc 305*mc 625 - 2*mc 305*mc 1265 - 2*mc 625*mc 1265 + 4*mc 305*mc 625*mc 1265) + 2*(mc 306 + mc 626 + mc 1266 - 2*mc 306*mc 626 - 2*mc 306*mc 1266 - 2*mc 626*mc 1266 + 4*mc 306*mc 626*mc 1266) + 4*(mc 307 + mc 627 + mc 1267 - 2*mc 307*mc 627 - 2*mc 307*mc 1267 - 2*mc 627*mc 1267 + 4*mc 307*mc 627*mc 1267) + 8*(mc 308 + mc 628 + mc 1268 - 2*mc 308*mc 628 - 2*mc 308*mc 1268 - 2*mc 628*mc 1268 + 4*mc 308*mc 628*mc 1268) + 16*(mc 309 + mc 629 + mc 1269 - 2*mc 309*mc 629 - 2*mc 309*mc 1269 - 2*mc 629*mc 1269 + 4*mc 309*mc 629*mc 1269) + 32*(mc 310 + mc 630 + mc 1270 - 2*mc 310*mc 630 - 2*mc 310*mc 1270 - 2*mc 630*mc 1270 + 4*mc 310*mc 630*mc 1270) + 64*(mc 311 + mc 631 + mc 1271 - 2*mc 311*mc 631 - 2*mc 311*mc 1271 - 2*mc 631*mc 1271 + 4*mc 311*mc 631*mc 1271) + 128*(mc 312 + mc 632 + mc 1272 - 2*mc 312*mc 632 - 2*mc 312*mc 1272 - 2*mc 632*mc 1272 + 4*mc 312*mc 632*mc 1272) + 256*(mc 313 + mc 633 + mc 1273 - 2*mc 313*mc 633 - 2*mc 313*mc 1273 - 2*mc 633*mc 1273 + 4*mc 313*mc 633*mc 1273) + 512*(mc 314 + mc 634 + mc 1274 - 2*mc 314*mc 634 - 2*mc 314*mc 1274 - 2*mc 634*mc 1274 + 4*mc 314*mc 634*mc 1274) + 1024*(mc 315 + mc 635 + mc 1275 - 2*mc 315*mc 635 - 2*mc 315*mc 1275 - 2*mc 635*mc 1275 + 4*mc 315*mc 635*mc 1275) + 2048*(mc 316 + mc 636 + mc 1276 - 2*mc 316*mc 636 - 2*mc 316*mc 1276 - 2*mc 636*mc 1276 + 4*mc 316*mc 636*mc 1276) + 4096*(mc 317 + mc 637 + mc 1277 - 2*mc 317*mc 637 - 2*mc 317*mc 1277 - 2*mc 637*mc 1277 + 4*mc 317*mc 637*mc 1277) + 8192*(mc 318 + mc 638 + mc 1278 - 2*mc 318*mc 638 - 2*mc 318*mc 1278 - 2*mc 638*mc 1278 + 4*mc 318*mc 638*mc 1278) + 16384*(mc 319 + mc 639 + mc 1279 - 2*mc 319*mc 639 - 2*mc 319*mc 1279 - 2*mc 639*mc 1279 + 4*mc 319*mc 639*mc 1279) + 32768*(mc 320 + mc 640 + mc 1280 - 2*mc 320*mc 640 - 2*mc 320*mc 1280 - 2*mc 640*mc 1280 + 4*mc 320*mc 640*mc 1280) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1363, KeccakfPermAir.extraction.inter_1125, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_1124 c row = (mc 306 + mc 626 + mc 1266 - 2*mc 306*mc 626 - 2*mc 306*mc 1266 - 2*mc 626*mc 1266 + 4*mc 306*mc 626*mc 1266) + 2 * KeccakfPermAir.extraction.inter_1122 c row := by
    simp only [KeccakfPermAir.extraction.inter_1124, KeccakfPermAir.extraction.inter_1123, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_1122 c row = (mc 307 + mc 627 + mc 1267 - 2*mc 307*mc 627 - 2*mc 307*mc 1267 - 2*mc 627*mc 1267 + 4*mc 307*mc 627*mc 1267) + 2 * KeccakfPermAir.extraction.inter_1120 c row := by
    simp only [KeccakfPermAir.extraction.inter_1122, KeccakfPermAir.extraction.inter_1121, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_1120 c row = (mc 308 + mc 628 + mc 1268 - 2*mc 308*mc 628 - 2*mc 308*mc 1268 - 2*mc 628*mc 1268 + 4*mc 308*mc 628*mc 1268) + 2 * KeccakfPermAir.extraction.inter_1118 c row := by
    simp only [KeccakfPermAir.extraction.inter_1120, KeccakfPermAir.extraction.inter_1119, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_1118 c row = (mc 309 + mc 629 + mc 1269 - 2*mc 309*mc 629 - 2*mc 309*mc 1269 - 2*mc 629*mc 1269 + 4*mc 309*mc 629*mc 1269) + 2 * KeccakfPermAir.extraction.inter_1116 c row := by
    simp only [KeccakfPermAir.extraction.inter_1118, KeccakfPermAir.extraction.inter_1117, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_1116 c row = (mc 310 + mc 630 + mc 1270 - 2*mc 310*mc 630 - 2*mc 310*mc 1270 - 2*mc 630*mc 1270 + 4*mc 310*mc 630*mc 1270) + 2 * KeccakfPermAir.extraction.inter_1114 c row := by
    simp only [KeccakfPermAir.extraction.inter_1116, KeccakfPermAir.extraction.inter_1115, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_1114 c row = (mc 311 + mc 631 + mc 1271 - 2*mc 311*mc 631 - 2*mc 311*mc 1271 - 2*mc 631*mc 1271 + 4*mc 311*mc 631*mc 1271) + 2 * KeccakfPermAir.extraction.inter_1112 c row := by
    simp only [KeccakfPermAir.extraction.inter_1114, KeccakfPermAir.extraction.inter_1113, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_1112 c row = (mc 312 + mc 632 + mc 1272 - 2*mc 312*mc 632 - 2*mc 312*mc 1272 - 2*mc 632*mc 1272 + 4*mc 312*mc 632*mc 1272) + 2 * KeccakfPermAir.extraction.inter_1110 c row := by
    simp only [KeccakfPermAir.extraction.inter_1112, KeccakfPermAir.extraction.inter_1111, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_1110 c row = (mc 313 + mc 633 + mc 1273 - 2*mc 313*mc 633 - 2*mc 313*mc 1273 - 2*mc 633*mc 1273 + 4*mc 313*mc 633*mc 1273) + 2 * KeccakfPermAir.extraction.inter_1108 c row := by
    simp only [KeccakfPermAir.extraction.inter_1110, KeccakfPermAir.extraction.inter_1109, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_1108 c row = (mc 314 + mc 634 + mc 1274 - 2*mc 314*mc 634 - 2*mc 314*mc 1274 - 2*mc 634*mc 1274 + 4*mc 314*mc 634*mc 1274) + 2 * KeccakfPermAir.extraction.inter_1106 c row := by
    simp only [KeccakfPermAir.extraction.inter_1108, KeccakfPermAir.extraction.inter_1107, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_1106 c row = (mc 315 + mc 635 + mc 1275 - 2*mc 315*mc 635 - 2*mc 315*mc 1275 - 2*mc 635*mc 1275 + 4*mc 315*mc 635*mc 1275) + 2 * KeccakfPermAir.extraction.inter_1104 c row := by
    simp only [KeccakfPermAir.extraction.inter_1106, KeccakfPermAir.extraction.inter_1105, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_1104 c row = (mc 316 + mc 636 + mc 1276 - 2*mc 316*mc 636 - 2*mc 316*mc 1276 - 2*mc 636*mc 1276 + 4*mc 316*mc 636*mc 1276) + 2 * KeccakfPermAir.extraction.inter_1102 c row := by
    simp only [KeccakfPermAir.extraction.inter_1104, KeccakfPermAir.extraction.inter_1103, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_1102 c row = (mc 317 + mc 637 + mc 1277 - 2*mc 317*mc 637 - 2*mc 317*mc 1277 - 2*mc 637*mc 1277 + 4*mc 317*mc 637*mc 1277) + 2 * KeccakfPermAir.extraction.inter_1100 c row := by
    simp only [KeccakfPermAir.extraction.inter_1102, KeccakfPermAir.extraction.inter_1101, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_1100 c row = (mc 318 + mc 638 + mc 1278 - 2*mc 318*mc 638 - 2*mc 318*mc 1278 - 2*mc 638*mc 1278 + 4*mc 318*mc 638*mc 1278) + 2 * KeccakfPermAir.extraction.inter_1098 c row := by
    simp only [KeccakfPermAir.extraction.inter_1100, KeccakfPermAir.extraction.inter_1099, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_1098 c row = (mc 319 + mc 639 + mc 1279 - 2*mc 319*mc 639 - 2*mc 319*mc 1279 - 2*mc 639*mc 1279 + 4*mc 319*mc 639*mc 1279) + 2 * KeccakfPermAir.extraction.inter_1096 c row := by
    simp only [KeccakfPermAir.extraction.inter_1098, KeccakfPermAir.extraction.inter_1097, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_1096 c row = (mc 320 + mc 640 + mc 1280 - 2*mc 320*mc 640 - 2*mc 320*mc 1280 - 2*mc 640*mc 1280 + 4*mc 320*mc 640*mc 1280) := by
    simp only [KeccakfPermAir.extraction.inter_1096, KeccakfPermAir.extraction.inter_1095, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1364 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 321 641 1281 151 row) :
    mc 151 = (mc 321 + mc 641 + mc 1281 - 2*mc 321*mc 641 - 2*mc 321*mc 1281 - 2*mc 641*mc 1281 + 4*mc 321*mc 641*mc 1281) + 2*(mc 322 + mc 642 + mc 1282 - 2*mc 322*mc 642 - 2*mc 322*mc 1282 - 2*mc 642*mc 1282 + 4*mc 322*mc 642*mc 1282) + 4*(mc 323 + mc 643 + mc 1283 - 2*mc 323*mc 643 - 2*mc 323*mc 1283 - 2*mc 643*mc 1283 + 4*mc 323*mc 643*mc 1283) + 8*(mc 324 + mc 644 + mc 1284 - 2*mc 324*mc 644 - 2*mc 324*mc 1284 - 2*mc 644*mc 1284 + 4*mc 324*mc 644*mc 1284) + 16*(mc 325 + mc 645 + mc 1285 - 2*mc 325*mc 645 - 2*mc 325*mc 1285 - 2*mc 645*mc 1285 + 4*mc 325*mc 645*mc 1285) + 32*(mc 326 + mc 646 + mc 1286 - 2*mc 326*mc 646 - 2*mc 326*mc 1286 - 2*mc 646*mc 1286 + 4*mc 326*mc 646*mc 1286) + 64*(mc 327 + mc 647 + mc 1287 - 2*mc 327*mc 647 - 2*mc 327*mc 1287 - 2*mc 647*mc 1287 + 4*mc 327*mc 647*mc 1287) + 128*(mc 328 + mc 648 + mc 1288 - 2*mc 328*mc 648 - 2*mc 328*mc 1288 - 2*mc 648*mc 1288 + 4*mc 328*mc 648*mc 1288) + 256*(mc 329 + mc 649 + mc 1289 - 2*mc 329*mc 649 - 2*mc 329*mc 1289 - 2*mc 649*mc 1289 + 4*mc 329*mc 649*mc 1289) + 512*(mc 330 + mc 650 + mc 1290 - 2*mc 330*mc 650 - 2*mc 330*mc 1290 - 2*mc 650*mc 1290 + 4*mc 330*mc 650*mc 1290) + 1024*(mc 331 + mc 651 + mc 1291 - 2*mc 331*mc 651 - 2*mc 331*mc 1291 - 2*mc 651*mc 1291 + 4*mc 331*mc 651*mc 1291) + 2048*(mc 332 + mc 652 + mc 1292 - 2*mc 332*mc 652 - 2*mc 332*mc 1292 - 2*mc 652*mc 1292 + 4*mc 332*mc 652*mc 1292) + 4096*(mc 333 + mc 653 + mc 1293 - 2*mc 333*mc 653 - 2*mc 333*mc 1293 - 2*mc 653*mc 1293 + 4*mc 333*mc 653*mc 1293) + 8192*(mc 334 + mc 654 + mc 1294 - 2*mc 334*mc 654 - 2*mc 334*mc 1294 - 2*mc 654*mc 1294 + 4*mc 334*mc 654*mc 1294) + 16384*(mc 335 + mc 655 + mc 1295 - 2*mc 335*mc 655 - 2*mc 335*mc 1295 - 2*mc 655*mc 1295 + 4*mc 335*mc 655*mc 1295) + 32768*(mc 336 + mc 656 + mc 1296 - 2*mc 336*mc 656 - 2*mc 336*mc 1296 - 2*mc 656*mc 1296 + 4*mc 336*mc 656*mc 1296) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1364, KeccakfPermAir.extraction.inter_1156, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_1155 c row = (mc 322 + mc 642 + mc 1282 - 2*mc 322*mc 642 - 2*mc 322*mc 1282 - 2*mc 642*mc 1282 + 4*mc 322*mc 642*mc 1282) + 2 * KeccakfPermAir.extraction.inter_1153 c row := by
    simp only [KeccakfPermAir.extraction.inter_1155, KeccakfPermAir.extraction.inter_1154, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_1153 c row = (mc 323 + mc 643 + mc 1283 - 2*mc 323*mc 643 - 2*mc 323*mc 1283 - 2*mc 643*mc 1283 + 4*mc 323*mc 643*mc 1283) + 2 * KeccakfPermAir.extraction.inter_1151 c row := by
    simp only [KeccakfPermAir.extraction.inter_1153, KeccakfPermAir.extraction.inter_1152, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_1151 c row = (mc 324 + mc 644 + mc 1284 - 2*mc 324*mc 644 - 2*mc 324*mc 1284 - 2*mc 644*mc 1284 + 4*mc 324*mc 644*mc 1284) + 2 * KeccakfPermAir.extraction.inter_1149 c row := by
    simp only [KeccakfPermAir.extraction.inter_1151, KeccakfPermAir.extraction.inter_1150, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_1149 c row = (mc 325 + mc 645 + mc 1285 - 2*mc 325*mc 645 - 2*mc 325*mc 1285 - 2*mc 645*mc 1285 + 4*mc 325*mc 645*mc 1285) + 2 * KeccakfPermAir.extraction.inter_1147 c row := by
    simp only [KeccakfPermAir.extraction.inter_1149, KeccakfPermAir.extraction.inter_1148, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_1147 c row = (mc 326 + mc 646 + mc 1286 - 2*mc 326*mc 646 - 2*mc 326*mc 1286 - 2*mc 646*mc 1286 + 4*mc 326*mc 646*mc 1286) + 2 * KeccakfPermAir.extraction.inter_1145 c row := by
    simp only [KeccakfPermAir.extraction.inter_1147, KeccakfPermAir.extraction.inter_1146, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_1145 c row = (mc 327 + mc 647 + mc 1287 - 2*mc 327*mc 647 - 2*mc 327*mc 1287 - 2*mc 647*mc 1287 + 4*mc 327*mc 647*mc 1287) + 2 * KeccakfPermAir.extraction.inter_1143 c row := by
    simp only [KeccakfPermAir.extraction.inter_1145, KeccakfPermAir.extraction.inter_1144, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_1143 c row = (mc 328 + mc 648 + mc 1288 - 2*mc 328*mc 648 - 2*mc 328*mc 1288 - 2*mc 648*mc 1288 + 4*mc 328*mc 648*mc 1288) + 2 * KeccakfPermAir.extraction.inter_1141 c row := by
    simp only [KeccakfPermAir.extraction.inter_1143, KeccakfPermAir.extraction.inter_1142, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_1141 c row = (mc 329 + mc 649 + mc 1289 - 2*mc 329*mc 649 - 2*mc 329*mc 1289 - 2*mc 649*mc 1289 + 4*mc 329*mc 649*mc 1289) + 2 * KeccakfPermAir.extraction.inter_1139 c row := by
    simp only [KeccakfPermAir.extraction.inter_1141, KeccakfPermAir.extraction.inter_1140, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_1139 c row = (mc 330 + mc 650 + mc 1290 - 2*mc 330*mc 650 - 2*mc 330*mc 1290 - 2*mc 650*mc 1290 + 4*mc 330*mc 650*mc 1290) + 2 * KeccakfPermAir.extraction.inter_1137 c row := by
    simp only [KeccakfPermAir.extraction.inter_1139, KeccakfPermAir.extraction.inter_1138, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_1137 c row = (mc 331 + mc 651 + mc 1291 - 2*mc 331*mc 651 - 2*mc 331*mc 1291 - 2*mc 651*mc 1291 + 4*mc 331*mc 651*mc 1291) + 2 * KeccakfPermAir.extraction.inter_1135 c row := by
    simp only [KeccakfPermAir.extraction.inter_1137, KeccakfPermAir.extraction.inter_1136, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_1135 c row = (mc 332 + mc 652 + mc 1292 - 2*mc 332*mc 652 - 2*mc 332*mc 1292 - 2*mc 652*mc 1292 + 4*mc 332*mc 652*mc 1292) + 2 * KeccakfPermAir.extraction.inter_1133 c row := by
    simp only [KeccakfPermAir.extraction.inter_1135, KeccakfPermAir.extraction.inter_1134, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_1133 c row = (mc 333 + mc 653 + mc 1293 - 2*mc 333*mc 653 - 2*mc 333*mc 1293 - 2*mc 653*mc 1293 + 4*mc 333*mc 653*mc 1293) + 2 * KeccakfPermAir.extraction.inter_1131 c row := by
    simp only [KeccakfPermAir.extraction.inter_1133, KeccakfPermAir.extraction.inter_1132, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_1131 c row = (mc 334 + mc 654 + mc 1294 - 2*mc 334*mc 654 - 2*mc 334*mc 1294 - 2*mc 654*mc 1294 + 4*mc 334*mc 654*mc 1294) + 2 * KeccakfPermAir.extraction.inter_1129 c row := by
    simp only [KeccakfPermAir.extraction.inter_1131, KeccakfPermAir.extraction.inter_1130, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_1129 c row = (mc 335 + mc 655 + mc 1295 - 2*mc 335*mc 655 - 2*mc 335*mc 1295 - 2*mc 655*mc 1295 + 4*mc 335*mc 655*mc 1295) + 2 * KeccakfPermAir.extraction.inter_1127 c row := by
    simp only [KeccakfPermAir.extraction.inter_1129, KeccakfPermAir.extraction.inter_1128, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_1127 c row = (mc 336 + mc 656 + mc 1296 - 2*mc 336*mc 656 - 2*mc 336*mc 1296 - 2*mc 656*mc 1296 + 4*mc 336*mc 656*mc 1296) := by
    simp only [KeccakfPermAir.extraction.inter_1127, KeccakfPermAir.extraction.inter_1126, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1365 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 337 657 1297 152 row) :
    mc 152 = (mc 337 + mc 657 + mc 1297 - 2*mc 337*mc 657 - 2*mc 337*mc 1297 - 2*mc 657*mc 1297 + 4*mc 337*mc 657*mc 1297) + 2*(mc 338 + mc 658 + mc 1298 - 2*mc 338*mc 658 - 2*mc 338*mc 1298 - 2*mc 658*mc 1298 + 4*mc 338*mc 658*mc 1298) + 4*(mc 339 + mc 659 + mc 1299 - 2*mc 339*mc 659 - 2*mc 339*mc 1299 - 2*mc 659*mc 1299 + 4*mc 339*mc 659*mc 1299) + 8*(mc 340 + mc 660 + mc 1300 - 2*mc 340*mc 660 - 2*mc 340*mc 1300 - 2*mc 660*mc 1300 + 4*mc 340*mc 660*mc 1300) + 16*(mc 341 + mc 661 + mc 1301 - 2*mc 341*mc 661 - 2*mc 341*mc 1301 - 2*mc 661*mc 1301 + 4*mc 341*mc 661*mc 1301) + 32*(mc 342 + mc 662 + mc 1302 - 2*mc 342*mc 662 - 2*mc 342*mc 1302 - 2*mc 662*mc 1302 + 4*mc 342*mc 662*mc 1302) + 64*(mc 343 + mc 663 + mc 1303 - 2*mc 343*mc 663 - 2*mc 343*mc 1303 - 2*mc 663*mc 1303 + 4*mc 343*mc 663*mc 1303) + 128*(mc 344 + mc 664 + mc 1304 - 2*mc 344*mc 664 - 2*mc 344*mc 1304 - 2*mc 664*mc 1304 + 4*mc 344*mc 664*mc 1304) + 256*(mc 345 + mc 665 + mc 1305 - 2*mc 345*mc 665 - 2*mc 345*mc 1305 - 2*mc 665*mc 1305 + 4*mc 345*mc 665*mc 1305) + 512*(mc 346 + mc 666 + mc 1306 - 2*mc 346*mc 666 - 2*mc 346*mc 1306 - 2*mc 666*mc 1306 + 4*mc 346*mc 666*mc 1306) + 1024*(mc 347 + mc 667 + mc 1307 - 2*mc 347*mc 667 - 2*mc 347*mc 1307 - 2*mc 667*mc 1307 + 4*mc 347*mc 667*mc 1307) + 2048*(mc 348 + mc 668 + mc 1308 - 2*mc 348*mc 668 - 2*mc 348*mc 1308 - 2*mc 668*mc 1308 + 4*mc 348*mc 668*mc 1308) + 4096*(mc 349 + mc 669 + mc 1309 - 2*mc 349*mc 669 - 2*mc 349*mc 1309 - 2*mc 669*mc 1309 + 4*mc 349*mc 669*mc 1309) + 8192*(mc 350 + mc 670 + mc 1310 - 2*mc 350*mc 670 - 2*mc 350*mc 1310 - 2*mc 670*mc 1310 + 4*mc 350*mc 670*mc 1310) + 16384*(mc 351 + mc 671 + mc 1311 - 2*mc 351*mc 671 - 2*mc 351*mc 1311 - 2*mc 671*mc 1311 + 4*mc 351*mc 671*mc 1311) + 32768*(mc 352 + mc 672 + mc 1312 - 2*mc 352*mc 672 - 2*mc 352*mc 1312 - 2*mc 672*mc 1312 + 4*mc 352*mc 672*mc 1312) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1365, KeccakfPermAir.extraction.inter_1187, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_1186 c row = (mc 338 + mc 658 + mc 1298 - 2*mc 338*mc 658 - 2*mc 338*mc 1298 - 2*mc 658*mc 1298 + 4*mc 338*mc 658*mc 1298) + 2 * KeccakfPermAir.extraction.inter_1184 c row := by
    simp only [KeccakfPermAir.extraction.inter_1186, KeccakfPermAir.extraction.inter_1185, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_1184 c row = (mc 339 + mc 659 + mc 1299 - 2*mc 339*mc 659 - 2*mc 339*mc 1299 - 2*mc 659*mc 1299 + 4*mc 339*mc 659*mc 1299) + 2 * KeccakfPermAir.extraction.inter_1182 c row := by
    simp only [KeccakfPermAir.extraction.inter_1184, KeccakfPermAir.extraction.inter_1183, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_1182 c row = (mc 340 + mc 660 + mc 1300 - 2*mc 340*mc 660 - 2*mc 340*mc 1300 - 2*mc 660*mc 1300 + 4*mc 340*mc 660*mc 1300) + 2 * KeccakfPermAir.extraction.inter_1180 c row := by
    simp only [KeccakfPermAir.extraction.inter_1182, KeccakfPermAir.extraction.inter_1181, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_1180 c row = (mc 341 + mc 661 + mc 1301 - 2*mc 341*mc 661 - 2*mc 341*mc 1301 - 2*mc 661*mc 1301 + 4*mc 341*mc 661*mc 1301) + 2 * KeccakfPermAir.extraction.inter_1178 c row := by
    simp only [KeccakfPermAir.extraction.inter_1180, KeccakfPermAir.extraction.inter_1179, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_1178 c row = (mc 342 + mc 662 + mc 1302 - 2*mc 342*mc 662 - 2*mc 342*mc 1302 - 2*mc 662*mc 1302 + 4*mc 342*mc 662*mc 1302) + 2 * KeccakfPermAir.extraction.inter_1176 c row := by
    simp only [KeccakfPermAir.extraction.inter_1178, KeccakfPermAir.extraction.inter_1177, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_1176 c row = (mc 343 + mc 663 + mc 1303 - 2*mc 343*mc 663 - 2*mc 343*mc 1303 - 2*mc 663*mc 1303 + 4*mc 343*mc 663*mc 1303) + 2 * KeccakfPermAir.extraction.inter_1174 c row := by
    simp only [KeccakfPermAir.extraction.inter_1176, KeccakfPermAir.extraction.inter_1175, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_1174 c row = (mc 344 + mc 664 + mc 1304 - 2*mc 344*mc 664 - 2*mc 344*mc 1304 - 2*mc 664*mc 1304 + 4*mc 344*mc 664*mc 1304) + 2 * KeccakfPermAir.extraction.inter_1172 c row := by
    simp only [KeccakfPermAir.extraction.inter_1174, KeccakfPermAir.extraction.inter_1173, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_1172 c row = (mc 345 + mc 665 + mc 1305 - 2*mc 345*mc 665 - 2*mc 345*mc 1305 - 2*mc 665*mc 1305 + 4*mc 345*mc 665*mc 1305) + 2 * KeccakfPermAir.extraction.inter_1170 c row := by
    simp only [KeccakfPermAir.extraction.inter_1172, KeccakfPermAir.extraction.inter_1171, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_1170 c row = (mc 346 + mc 666 + mc 1306 - 2*mc 346*mc 666 - 2*mc 346*mc 1306 - 2*mc 666*mc 1306 + 4*mc 346*mc 666*mc 1306) + 2 * KeccakfPermAir.extraction.inter_1168 c row := by
    simp only [KeccakfPermAir.extraction.inter_1170, KeccakfPermAir.extraction.inter_1169, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_1168 c row = (mc 347 + mc 667 + mc 1307 - 2*mc 347*mc 667 - 2*mc 347*mc 1307 - 2*mc 667*mc 1307 + 4*mc 347*mc 667*mc 1307) + 2 * KeccakfPermAir.extraction.inter_1166 c row := by
    simp only [KeccakfPermAir.extraction.inter_1168, KeccakfPermAir.extraction.inter_1167, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_1166 c row = (mc 348 + mc 668 + mc 1308 - 2*mc 348*mc 668 - 2*mc 348*mc 1308 - 2*mc 668*mc 1308 + 4*mc 348*mc 668*mc 1308) + 2 * KeccakfPermAir.extraction.inter_1164 c row := by
    simp only [KeccakfPermAir.extraction.inter_1166, KeccakfPermAir.extraction.inter_1165, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_1164 c row = (mc 349 + mc 669 + mc 1309 - 2*mc 349*mc 669 - 2*mc 349*mc 1309 - 2*mc 669*mc 1309 + 4*mc 349*mc 669*mc 1309) + 2 * KeccakfPermAir.extraction.inter_1162 c row := by
    simp only [KeccakfPermAir.extraction.inter_1164, KeccakfPermAir.extraction.inter_1163, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_1162 c row = (mc 350 + mc 670 + mc 1310 - 2*mc 350*mc 670 - 2*mc 350*mc 1310 - 2*mc 670*mc 1310 + 4*mc 350*mc 670*mc 1310) + 2 * KeccakfPermAir.extraction.inter_1160 c row := by
    simp only [KeccakfPermAir.extraction.inter_1162, KeccakfPermAir.extraction.inter_1161, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_1160 c row = (mc 351 + mc 671 + mc 1311 - 2*mc 351*mc 671 - 2*mc 351*mc 1311 - 2*mc 671*mc 1311 + 4*mc 351*mc 671*mc 1311) + 2 * KeccakfPermAir.extraction.inter_1158 c row := by
    simp only [KeccakfPermAir.extraction.inter_1160, KeccakfPermAir.extraction.inter_1159, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_1158 c row = (mc 352 + mc 672 + mc 1312 - 2*mc 352*mc 672 - 2*mc 352*mc 1312 - 2*mc 672*mc 1312 + 4*mc 352*mc 672*mc 1312) := by
    simp only [KeccakfPermAir.extraction.inter_1158, KeccakfPermAir.extraction.inter_1157, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1430 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 353 673 1313 153 row) :
    mc 153 = (mc 353 + mc 673 + mc 1313 - 2*mc 353*mc 673 - 2*mc 353*mc 1313 - 2*mc 673*mc 1313 + 4*mc 353*mc 673*mc 1313) + 2*(mc 354 + mc 674 + mc 1314 - 2*mc 354*mc 674 - 2*mc 354*mc 1314 - 2*mc 674*mc 1314 + 4*mc 354*mc 674*mc 1314) + 4*(mc 355 + mc 675 + mc 1315 - 2*mc 355*mc 675 - 2*mc 355*mc 1315 - 2*mc 675*mc 1315 + 4*mc 355*mc 675*mc 1315) + 8*(mc 356 + mc 676 + mc 1316 - 2*mc 356*mc 676 - 2*mc 356*mc 1316 - 2*mc 676*mc 1316 + 4*mc 356*mc 676*mc 1316) + 16*(mc 357 + mc 677 + mc 1317 - 2*mc 357*mc 677 - 2*mc 357*mc 1317 - 2*mc 677*mc 1317 + 4*mc 357*mc 677*mc 1317) + 32*(mc 358 + mc 678 + mc 1318 - 2*mc 358*mc 678 - 2*mc 358*mc 1318 - 2*mc 678*mc 1318 + 4*mc 358*mc 678*mc 1318) + 64*(mc 359 + mc 679 + mc 1319 - 2*mc 359*mc 679 - 2*mc 359*mc 1319 - 2*mc 679*mc 1319 + 4*mc 359*mc 679*mc 1319) + 128*(mc 360 + mc 680 + mc 1320 - 2*mc 360*mc 680 - 2*mc 360*mc 1320 - 2*mc 680*mc 1320 + 4*mc 360*mc 680*mc 1320) + 256*(mc 361 + mc 681 + mc 1321 - 2*mc 361*mc 681 - 2*mc 361*mc 1321 - 2*mc 681*mc 1321 + 4*mc 361*mc 681*mc 1321) + 512*(mc 362 + mc 682 + mc 1322 - 2*mc 362*mc 682 - 2*mc 362*mc 1322 - 2*mc 682*mc 1322 + 4*mc 362*mc 682*mc 1322) + 1024*(mc 363 + mc 683 + mc 1323 - 2*mc 363*mc 683 - 2*mc 363*mc 1323 - 2*mc 683*mc 1323 + 4*mc 363*mc 683*mc 1323) + 2048*(mc 364 + mc 684 + mc 1324 - 2*mc 364*mc 684 - 2*mc 364*mc 1324 - 2*mc 684*mc 1324 + 4*mc 364*mc 684*mc 1324) + 4096*(mc 365 + mc 685 + mc 1325 - 2*mc 365*mc 685 - 2*mc 365*mc 1325 - 2*mc 685*mc 1325 + 4*mc 365*mc 685*mc 1325) + 8192*(mc 366 + mc 686 + mc 1326 - 2*mc 366*mc 686 - 2*mc 366*mc 1326 - 2*mc 686*mc 1326 + 4*mc 366*mc 686*mc 1326) + 16384*(mc 367 + mc 687 + mc 1327 - 2*mc 367*mc 687 - 2*mc 367*mc 1327 - 2*mc 687*mc 1327 + 4*mc 367*mc 687*mc 1327) + 32768*(mc 368 + mc 688 + mc 1328 - 2*mc 368*mc 688 - 2*mc 368*mc 1328 - 2*mc 688*mc 1328 + 4*mc 368*mc 688*mc 1328) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1430, KeccakfPermAir.extraction.inter_1218, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_1217 c row = (mc 354 + mc 674 + mc 1314 - 2*mc 354*mc 674 - 2*mc 354*mc 1314 - 2*mc 674*mc 1314 + 4*mc 354*mc 674*mc 1314) + 2 * KeccakfPermAir.extraction.inter_1215 c row := by
    simp only [KeccakfPermAir.extraction.inter_1217, KeccakfPermAir.extraction.inter_1216, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_1215 c row = (mc 355 + mc 675 + mc 1315 - 2*mc 355*mc 675 - 2*mc 355*mc 1315 - 2*mc 675*mc 1315 + 4*mc 355*mc 675*mc 1315) + 2 * KeccakfPermAir.extraction.inter_1213 c row := by
    simp only [KeccakfPermAir.extraction.inter_1215, KeccakfPermAir.extraction.inter_1214, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_1213 c row = (mc 356 + mc 676 + mc 1316 - 2*mc 356*mc 676 - 2*mc 356*mc 1316 - 2*mc 676*mc 1316 + 4*mc 356*mc 676*mc 1316) + 2 * KeccakfPermAir.extraction.inter_1211 c row := by
    simp only [KeccakfPermAir.extraction.inter_1213, KeccakfPermAir.extraction.inter_1212, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_1211 c row = (mc 357 + mc 677 + mc 1317 - 2*mc 357*mc 677 - 2*mc 357*mc 1317 - 2*mc 677*mc 1317 + 4*mc 357*mc 677*mc 1317) + 2 * KeccakfPermAir.extraction.inter_1209 c row := by
    simp only [KeccakfPermAir.extraction.inter_1211, KeccakfPermAir.extraction.inter_1210, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_1209 c row = (mc 358 + mc 678 + mc 1318 - 2*mc 358*mc 678 - 2*mc 358*mc 1318 - 2*mc 678*mc 1318 + 4*mc 358*mc 678*mc 1318) + 2 * KeccakfPermAir.extraction.inter_1207 c row := by
    simp only [KeccakfPermAir.extraction.inter_1209, KeccakfPermAir.extraction.inter_1208, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_1207 c row = (mc 359 + mc 679 + mc 1319 - 2*mc 359*mc 679 - 2*mc 359*mc 1319 - 2*mc 679*mc 1319 + 4*mc 359*mc 679*mc 1319) + 2 * KeccakfPermAir.extraction.inter_1205 c row := by
    simp only [KeccakfPermAir.extraction.inter_1207, KeccakfPermAir.extraction.inter_1206, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_1205 c row = (mc 360 + mc 680 + mc 1320 - 2*mc 360*mc 680 - 2*mc 360*mc 1320 - 2*mc 680*mc 1320 + 4*mc 360*mc 680*mc 1320) + 2 * KeccakfPermAir.extraction.inter_1203 c row := by
    simp only [KeccakfPermAir.extraction.inter_1205, KeccakfPermAir.extraction.inter_1204, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_1203 c row = (mc 361 + mc 681 + mc 1321 - 2*mc 361*mc 681 - 2*mc 361*mc 1321 - 2*mc 681*mc 1321 + 4*mc 361*mc 681*mc 1321) + 2 * KeccakfPermAir.extraction.inter_1201 c row := by
    simp only [KeccakfPermAir.extraction.inter_1203, KeccakfPermAir.extraction.inter_1202, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_1201 c row = (mc 362 + mc 682 + mc 1322 - 2*mc 362*mc 682 - 2*mc 362*mc 1322 - 2*mc 682*mc 1322 + 4*mc 362*mc 682*mc 1322) + 2 * KeccakfPermAir.extraction.inter_1199 c row := by
    simp only [KeccakfPermAir.extraction.inter_1201, KeccakfPermAir.extraction.inter_1200, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_1199 c row = (mc 363 + mc 683 + mc 1323 - 2*mc 363*mc 683 - 2*mc 363*mc 1323 - 2*mc 683*mc 1323 + 4*mc 363*mc 683*mc 1323) + 2 * KeccakfPermAir.extraction.inter_1197 c row := by
    simp only [KeccakfPermAir.extraction.inter_1199, KeccakfPermAir.extraction.inter_1198, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_1197 c row = (mc 364 + mc 684 + mc 1324 - 2*mc 364*mc 684 - 2*mc 364*mc 1324 - 2*mc 684*mc 1324 + 4*mc 364*mc 684*mc 1324) + 2 * KeccakfPermAir.extraction.inter_1195 c row := by
    simp only [KeccakfPermAir.extraction.inter_1197, KeccakfPermAir.extraction.inter_1196, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_1195 c row = (mc 365 + mc 685 + mc 1325 - 2*mc 365*mc 685 - 2*mc 365*mc 1325 - 2*mc 685*mc 1325 + 4*mc 365*mc 685*mc 1325) + 2 * KeccakfPermAir.extraction.inter_1193 c row := by
    simp only [KeccakfPermAir.extraction.inter_1195, KeccakfPermAir.extraction.inter_1194, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_1193 c row = (mc 366 + mc 686 + mc 1326 - 2*mc 366*mc 686 - 2*mc 366*mc 1326 - 2*mc 686*mc 1326 + 4*mc 366*mc 686*mc 1326) + 2 * KeccakfPermAir.extraction.inter_1191 c row := by
    simp only [KeccakfPermAir.extraction.inter_1193, KeccakfPermAir.extraction.inter_1192, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_1191 c row = (mc 367 + mc 687 + mc 1327 - 2*mc 367*mc 687 - 2*mc 367*mc 1327 - 2*mc 687*mc 1327 + 4*mc 367*mc 687*mc 1327) + 2 * KeccakfPermAir.extraction.inter_1189 c row := by
    simp only [KeccakfPermAir.extraction.inter_1191, KeccakfPermAir.extraction.inter_1190, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_1189 c row = (mc 368 + mc 688 + mc 1328 - 2*mc 368*mc 688 - 2*mc 368*mc 1328 - 2*mc 688*mc 1328 + 4*mc 368*mc 688*mc 1328) := by
    simp only [KeccakfPermAir.extraction.inter_1189, KeccakfPermAir.extraction.inter_1188, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1431 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 369 689 1329 154 row) :
    mc 154 = (mc 369 + mc 689 + mc 1329 - 2*mc 369*mc 689 - 2*mc 369*mc 1329 - 2*mc 689*mc 1329 + 4*mc 369*mc 689*mc 1329) + 2*(mc 370 + mc 690 + mc 1330 - 2*mc 370*mc 690 - 2*mc 370*mc 1330 - 2*mc 690*mc 1330 + 4*mc 370*mc 690*mc 1330) + 4*(mc 371 + mc 691 + mc 1331 - 2*mc 371*mc 691 - 2*mc 371*mc 1331 - 2*mc 691*mc 1331 + 4*mc 371*mc 691*mc 1331) + 8*(mc 372 + mc 692 + mc 1332 - 2*mc 372*mc 692 - 2*mc 372*mc 1332 - 2*mc 692*mc 1332 + 4*mc 372*mc 692*mc 1332) + 16*(mc 373 + mc 693 + mc 1333 - 2*mc 373*mc 693 - 2*mc 373*mc 1333 - 2*mc 693*mc 1333 + 4*mc 373*mc 693*mc 1333) + 32*(mc 374 + mc 694 + mc 1334 - 2*mc 374*mc 694 - 2*mc 374*mc 1334 - 2*mc 694*mc 1334 + 4*mc 374*mc 694*mc 1334) + 64*(mc 375 + mc 695 + mc 1335 - 2*mc 375*mc 695 - 2*mc 375*mc 1335 - 2*mc 695*mc 1335 + 4*mc 375*mc 695*mc 1335) + 128*(mc 376 + mc 696 + mc 1336 - 2*mc 376*mc 696 - 2*mc 376*mc 1336 - 2*mc 696*mc 1336 + 4*mc 376*mc 696*mc 1336) + 256*(mc 377 + mc 697 + mc 1337 - 2*mc 377*mc 697 - 2*mc 377*mc 1337 - 2*mc 697*mc 1337 + 4*mc 377*mc 697*mc 1337) + 512*(mc 378 + mc 698 + mc 1338 - 2*mc 378*mc 698 - 2*mc 378*mc 1338 - 2*mc 698*mc 1338 + 4*mc 378*mc 698*mc 1338) + 1024*(mc 379 + mc 699 + mc 1339 - 2*mc 379*mc 699 - 2*mc 379*mc 1339 - 2*mc 699*mc 1339 + 4*mc 379*mc 699*mc 1339) + 2048*(mc 380 + mc 700 + mc 1340 - 2*mc 380*mc 700 - 2*mc 380*mc 1340 - 2*mc 700*mc 1340 + 4*mc 380*mc 700*mc 1340) + 4096*(mc 381 + mc 701 + mc 1341 - 2*mc 381*mc 701 - 2*mc 381*mc 1341 - 2*mc 701*mc 1341 + 4*mc 381*mc 701*mc 1341) + 8192*(mc 382 + mc 702 + mc 1342 - 2*mc 382*mc 702 - 2*mc 382*mc 1342 - 2*mc 702*mc 1342 + 4*mc 382*mc 702*mc 1342) + 16384*(mc 383 + mc 703 + mc 1343 - 2*mc 383*mc 703 - 2*mc 383*mc 1343 - 2*mc 703*mc 1343 + 4*mc 383*mc 703*mc 1343) + 32768*(mc 384 + mc 704 + mc 1344 - 2*mc 384*mc 704 - 2*mc 384*mc 1344 - 2*mc 704*mc 1344 + 4*mc 384*mc 704*mc 1344) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1431, KeccakfPermAir.extraction.inter_1249, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_1248 c row = (mc 370 + mc 690 + mc 1330 - 2*mc 370*mc 690 - 2*mc 370*mc 1330 - 2*mc 690*mc 1330 + 4*mc 370*mc 690*mc 1330) + 2 * KeccakfPermAir.extraction.inter_1246 c row := by
    simp only [KeccakfPermAir.extraction.inter_1248, KeccakfPermAir.extraction.inter_1247, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_1246 c row = (mc 371 + mc 691 + mc 1331 - 2*mc 371*mc 691 - 2*mc 371*mc 1331 - 2*mc 691*mc 1331 + 4*mc 371*mc 691*mc 1331) + 2 * KeccakfPermAir.extraction.inter_1244 c row := by
    simp only [KeccakfPermAir.extraction.inter_1246, KeccakfPermAir.extraction.inter_1245, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_1244 c row = (mc 372 + mc 692 + mc 1332 - 2*mc 372*mc 692 - 2*mc 372*mc 1332 - 2*mc 692*mc 1332 + 4*mc 372*mc 692*mc 1332) + 2 * KeccakfPermAir.extraction.inter_1242 c row := by
    simp only [KeccakfPermAir.extraction.inter_1244, KeccakfPermAir.extraction.inter_1243, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_1242 c row = (mc 373 + mc 693 + mc 1333 - 2*mc 373*mc 693 - 2*mc 373*mc 1333 - 2*mc 693*mc 1333 + 4*mc 373*mc 693*mc 1333) + 2 * KeccakfPermAir.extraction.inter_1240 c row := by
    simp only [KeccakfPermAir.extraction.inter_1242, KeccakfPermAir.extraction.inter_1241, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_1240 c row = (mc 374 + mc 694 + mc 1334 - 2*mc 374*mc 694 - 2*mc 374*mc 1334 - 2*mc 694*mc 1334 + 4*mc 374*mc 694*mc 1334) + 2 * KeccakfPermAir.extraction.inter_1238 c row := by
    simp only [KeccakfPermAir.extraction.inter_1240, KeccakfPermAir.extraction.inter_1239, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_1238 c row = (mc 375 + mc 695 + mc 1335 - 2*mc 375*mc 695 - 2*mc 375*mc 1335 - 2*mc 695*mc 1335 + 4*mc 375*mc 695*mc 1335) + 2 * KeccakfPermAir.extraction.inter_1236 c row := by
    simp only [KeccakfPermAir.extraction.inter_1238, KeccakfPermAir.extraction.inter_1237, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_1236 c row = (mc 376 + mc 696 + mc 1336 - 2*mc 376*mc 696 - 2*mc 376*mc 1336 - 2*mc 696*mc 1336 + 4*mc 376*mc 696*mc 1336) + 2 * KeccakfPermAir.extraction.inter_1234 c row := by
    simp only [KeccakfPermAir.extraction.inter_1236, KeccakfPermAir.extraction.inter_1235, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_1234 c row = (mc 377 + mc 697 + mc 1337 - 2*mc 377*mc 697 - 2*mc 377*mc 1337 - 2*mc 697*mc 1337 + 4*mc 377*mc 697*mc 1337) + 2 * KeccakfPermAir.extraction.inter_1232 c row := by
    simp only [KeccakfPermAir.extraction.inter_1234, KeccakfPermAir.extraction.inter_1233, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_1232 c row = (mc 378 + mc 698 + mc 1338 - 2*mc 378*mc 698 - 2*mc 378*mc 1338 - 2*mc 698*mc 1338 + 4*mc 378*mc 698*mc 1338) + 2 * KeccakfPermAir.extraction.inter_1230 c row := by
    simp only [KeccakfPermAir.extraction.inter_1232, KeccakfPermAir.extraction.inter_1231, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_1230 c row = (mc 379 + mc 699 + mc 1339 - 2*mc 379*mc 699 - 2*mc 379*mc 1339 - 2*mc 699*mc 1339 + 4*mc 379*mc 699*mc 1339) + 2 * KeccakfPermAir.extraction.inter_1228 c row := by
    simp only [KeccakfPermAir.extraction.inter_1230, KeccakfPermAir.extraction.inter_1229, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_1228 c row = (mc 380 + mc 700 + mc 1340 - 2*mc 380*mc 700 - 2*mc 380*mc 1340 - 2*mc 700*mc 1340 + 4*mc 380*mc 700*mc 1340) + 2 * KeccakfPermAir.extraction.inter_1226 c row := by
    simp only [KeccakfPermAir.extraction.inter_1228, KeccakfPermAir.extraction.inter_1227, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_1226 c row = (mc 381 + mc 701 + mc 1341 - 2*mc 381*mc 701 - 2*mc 381*mc 1341 - 2*mc 701*mc 1341 + 4*mc 381*mc 701*mc 1341) + 2 * KeccakfPermAir.extraction.inter_1224 c row := by
    simp only [KeccakfPermAir.extraction.inter_1226, KeccakfPermAir.extraction.inter_1225, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_1224 c row = (mc 382 + mc 702 + mc 1342 - 2*mc 382*mc 702 - 2*mc 382*mc 1342 - 2*mc 702*mc 1342 + 4*mc 382*mc 702*mc 1342) + 2 * KeccakfPermAir.extraction.inter_1222 c row := by
    simp only [KeccakfPermAir.extraction.inter_1224, KeccakfPermAir.extraction.inter_1223, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_1222 c row = (mc 383 + mc 703 + mc 1343 - 2*mc 383*mc 703 - 2*mc 383*mc 1343 - 2*mc 703*mc 1343 + 4*mc 383*mc 703*mc 1343) + 2 * KeccakfPermAir.extraction.inter_1220 c row := by
    simp only [KeccakfPermAir.extraction.inter_1222, KeccakfPermAir.extraction.inter_1221, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_1220 c row = (mc 384 + mc 704 + mc 1344 - 2*mc 384*mc 704 - 2*mc 384*mc 1344 - 2*mc 704*mc 1344 + 4*mc 384*mc 704*mc 1344) := by
    simp only [KeccakfPermAir.extraction.inter_1220, KeccakfPermAir.extraction.inter_1219, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1432 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 385 705 1345 155 row) :
    mc 155 = (mc 385 + mc 705 + mc 1345 - 2*mc 385*mc 705 - 2*mc 385*mc 1345 - 2*mc 705*mc 1345 + 4*mc 385*mc 705*mc 1345) + 2*(mc 386 + mc 706 + mc 1346 - 2*mc 386*mc 706 - 2*mc 386*mc 1346 - 2*mc 706*mc 1346 + 4*mc 386*mc 706*mc 1346) + 4*(mc 387 + mc 707 + mc 1347 - 2*mc 387*mc 707 - 2*mc 387*mc 1347 - 2*mc 707*mc 1347 + 4*mc 387*mc 707*mc 1347) + 8*(mc 388 + mc 708 + mc 1348 - 2*mc 388*mc 708 - 2*mc 388*mc 1348 - 2*mc 708*mc 1348 + 4*mc 388*mc 708*mc 1348) + 16*(mc 389 + mc 709 + mc 1349 - 2*mc 389*mc 709 - 2*mc 389*mc 1349 - 2*mc 709*mc 1349 + 4*mc 389*mc 709*mc 1349) + 32*(mc 390 + mc 710 + mc 1350 - 2*mc 390*mc 710 - 2*mc 390*mc 1350 - 2*mc 710*mc 1350 + 4*mc 390*mc 710*mc 1350) + 64*(mc 391 + mc 711 + mc 1351 - 2*mc 391*mc 711 - 2*mc 391*mc 1351 - 2*mc 711*mc 1351 + 4*mc 391*mc 711*mc 1351) + 128*(mc 392 + mc 712 + mc 1352 - 2*mc 392*mc 712 - 2*mc 392*mc 1352 - 2*mc 712*mc 1352 + 4*mc 392*mc 712*mc 1352) + 256*(mc 393 + mc 713 + mc 1353 - 2*mc 393*mc 713 - 2*mc 393*mc 1353 - 2*mc 713*mc 1353 + 4*mc 393*mc 713*mc 1353) + 512*(mc 394 + mc 714 + mc 1354 - 2*mc 394*mc 714 - 2*mc 394*mc 1354 - 2*mc 714*mc 1354 + 4*mc 394*mc 714*mc 1354) + 1024*(mc 395 + mc 715 + mc 1355 - 2*mc 395*mc 715 - 2*mc 395*mc 1355 - 2*mc 715*mc 1355 + 4*mc 395*mc 715*mc 1355) + 2048*(mc 396 + mc 716 + mc 1356 - 2*mc 396*mc 716 - 2*mc 396*mc 1356 - 2*mc 716*mc 1356 + 4*mc 396*mc 716*mc 1356) + 4096*(mc 397 + mc 717 + mc 1357 - 2*mc 397*mc 717 - 2*mc 397*mc 1357 - 2*mc 717*mc 1357 + 4*mc 397*mc 717*mc 1357) + 8192*(mc 398 + mc 718 + mc 1358 - 2*mc 398*mc 718 - 2*mc 398*mc 1358 - 2*mc 718*mc 1358 + 4*mc 398*mc 718*mc 1358) + 16384*(mc 399 + mc 719 + mc 1359 - 2*mc 399*mc 719 - 2*mc 399*mc 1359 - 2*mc 719*mc 1359 + 4*mc 399*mc 719*mc 1359) + 32768*(mc 400 + mc 720 + mc 1360 - 2*mc 400*mc 720 - 2*mc 400*mc 1360 - 2*mc 720*mc 1360 + 4*mc 400*mc 720*mc 1360) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1432, KeccakfPermAir.extraction.inter_1280, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_1279 c row = (mc 386 + mc 706 + mc 1346 - 2*mc 386*mc 706 - 2*mc 386*mc 1346 - 2*mc 706*mc 1346 + 4*mc 386*mc 706*mc 1346) + 2 * KeccakfPermAir.extraction.inter_1277 c row := by
    simp only [KeccakfPermAir.extraction.inter_1279, KeccakfPermAir.extraction.inter_1278, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_1277 c row = (mc 387 + mc 707 + mc 1347 - 2*mc 387*mc 707 - 2*mc 387*mc 1347 - 2*mc 707*mc 1347 + 4*mc 387*mc 707*mc 1347) + 2 * KeccakfPermAir.extraction.inter_1275 c row := by
    simp only [KeccakfPermAir.extraction.inter_1277, KeccakfPermAir.extraction.inter_1276, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_1275 c row = (mc 388 + mc 708 + mc 1348 - 2*mc 388*mc 708 - 2*mc 388*mc 1348 - 2*mc 708*mc 1348 + 4*mc 388*mc 708*mc 1348) + 2 * KeccakfPermAir.extraction.inter_1273 c row := by
    simp only [KeccakfPermAir.extraction.inter_1275, KeccakfPermAir.extraction.inter_1274, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_1273 c row = (mc 389 + mc 709 + mc 1349 - 2*mc 389*mc 709 - 2*mc 389*mc 1349 - 2*mc 709*mc 1349 + 4*mc 389*mc 709*mc 1349) + 2 * KeccakfPermAir.extraction.inter_1271 c row := by
    simp only [KeccakfPermAir.extraction.inter_1273, KeccakfPermAir.extraction.inter_1272, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_1271 c row = (mc 390 + mc 710 + mc 1350 - 2*mc 390*mc 710 - 2*mc 390*mc 1350 - 2*mc 710*mc 1350 + 4*mc 390*mc 710*mc 1350) + 2 * KeccakfPermAir.extraction.inter_1269 c row := by
    simp only [KeccakfPermAir.extraction.inter_1271, KeccakfPermAir.extraction.inter_1270, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_1269 c row = (mc 391 + mc 711 + mc 1351 - 2*mc 391*mc 711 - 2*mc 391*mc 1351 - 2*mc 711*mc 1351 + 4*mc 391*mc 711*mc 1351) + 2 * KeccakfPermAir.extraction.inter_1267 c row := by
    simp only [KeccakfPermAir.extraction.inter_1269, KeccakfPermAir.extraction.inter_1268, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_1267 c row = (mc 392 + mc 712 + mc 1352 - 2*mc 392*mc 712 - 2*mc 392*mc 1352 - 2*mc 712*mc 1352 + 4*mc 392*mc 712*mc 1352) + 2 * KeccakfPermAir.extraction.inter_1265 c row := by
    simp only [KeccakfPermAir.extraction.inter_1267, KeccakfPermAir.extraction.inter_1266, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_1265 c row = (mc 393 + mc 713 + mc 1353 - 2*mc 393*mc 713 - 2*mc 393*mc 1353 - 2*mc 713*mc 1353 + 4*mc 393*mc 713*mc 1353) + 2 * KeccakfPermAir.extraction.inter_1263 c row := by
    simp only [KeccakfPermAir.extraction.inter_1265, KeccakfPermAir.extraction.inter_1264, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_1263 c row = (mc 394 + mc 714 + mc 1354 - 2*mc 394*mc 714 - 2*mc 394*mc 1354 - 2*mc 714*mc 1354 + 4*mc 394*mc 714*mc 1354) + 2 * KeccakfPermAir.extraction.inter_1261 c row := by
    simp only [KeccakfPermAir.extraction.inter_1263, KeccakfPermAir.extraction.inter_1262, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_1261 c row = (mc 395 + mc 715 + mc 1355 - 2*mc 395*mc 715 - 2*mc 395*mc 1355 - 2*mc 715*mc 1355 + 4*mc 395*mc 715*mc 1355) + 2 * KeccakfPermAir.extraction.inter_1259 c row := by
    simp only [KeccakfPermAir.extraction.inter_1261, KeccakfPermAir.extraction.inter_1260, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_1259 c row = (mc 396 + mc 716 + mc 1356 - 2*mc 396*mc 716 - 2*mc 396*mc 1356 - 2*mc 716*mc 1356 + 4*mc 396*mc 716*mc 1356) + 2 * KeccakfPermAir.extraction.inter_1257 c row := by
    simp only [KeccakfPermAir.extraction.inter_1259, KeccakfPermAir.extraction.inter_1258, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_1257 c row = (mc 397 + mc 717 + mc 1357 - 2*mc 397*mc 717 - 2*mc 397*mc 1357 - 2*mc 717*mc 1357 + 4*mc 397*mc 717*mc 1357) + 2 * KeccakfPermAir.extraction.inter_1255 c row := by
    simp only [KeccakfPermAir.extraction.inter_1257, KeccakfPermAir.extraction.inter_1256, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_1255 c row = (mc 398 + mc 718 + mc 1358 - 2*mc 398*mc 718 - 2*mc 398*mc 1358 - 2*mc 718*mc 1358 + 4*mc 398*mc 718*mc 1358) + 2 * KeccakfPermAir.extraction.inter_1253 c row := by
    simp only [KeccakfPermAir.extraction.inter_1255, KeccakfPermAir.extraction.inter_1254, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_1253 c row = (mc 399 + mc 719 + mc 1359 - 2*mc 399*mc 719 - 2*mc 399*mc 1359 - 2*mc 719*mc 1359 + 4*mc 399*mc 719*mc 1359) + 2 * KeccakfPermAir.extraction.inter_1251 c row := by
    simp only [KeccakfPermAir.extraction.inter_1253, KeccakfPermAir.extraction.inter_1252, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_1251 c row = (mc 400 + mc 720 + mc 1360 - 2*mc 400*mc 720 - 2*mc 400*mc 1360 - 2*mc 720*mc 1360 + 4*mc 400*mc 720*mc 1360) := by
    simp only [KeccakfPermAir.extraction.inter_1251, KeccakfPermAir.extraction.inter_1250, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1433 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 401 721 1361 156 row) :
    mc 156 = (mc 401 + mc 721 + mc 1361 - 2*mc 401*mc 721 - 2*mc 401*mc 1361 - 2*mc 721*mc 1361 + 4*mc 401*mc 721*mc 1361) + 2*(mc 402 + mc 722 + mc 1362 - 2*mc 402*mc 722 - 2*mc 402*mc 1362 - 2*mc 722*mc 1362 + 4*mc 402*mc 722*mc 1362) + 4*(mc 403 + mc 723 + mc 1363 - 2*mc 403*mc 723 - 2*mc 403*mc 1363 - 2*mc 723*mc 1363 + 4*mc 403*mc 723*mc 1363) + 8*(mc 404 + mc 724 + mc 1364 - 2*mc 404*mc 724 - 2*mc 404*mc 1364 - 2*mc 724*mc 1364 + 4*mc 404*mc 724*mc 1364) + 16*(mc 405 + mc 725 + mc 1365 - 2*mc 405*mc 725 - 2*mc 405*mc 1365 - 2*mc 725*mc 1365 + 4*mc 405*mc 725*mc 1365) + 32*(mc 406 + mc 726 + mc 1366 - 2*mc 406*mc 726 - 2*mc 406*mc 1366 - 2*mc 726*mc 1366 + 4*mc 406*mc 726*mc 1366) + 64*(mc 407 + mc 727 + mc 1367 - 2*mc 407*mc 727 - 2*mc 407*mc 1367 - 2*mc 727*mc 1367 + 4*mc 407*mc 727*mc 1367) + 128*(mc 408 + mc 728 + mc 1368 - 2*mc 408*mc 728 - 2*mc 408*mc 1368 - 2*mc 728*mc 1368 + 4*mc 408*mc 728*mc 1368) + 256*(mc 409 + mc 729 + mc 1369 - 2*mc 409*mc 729 - 2*mc 409*mc 1369 - 2*mc 729*mc 1369 + 4*mc 409*mc 729*mc 1369) + 512*(mc 410 + mc 730 + mc 1370 - 2*mc 410*mc 730 - 2*mc 410*mc 1370 - 2*mc 730*mc 1370 + 4*mc 410*mc 730*mc 1370) + 1024*(mc 411 + mc 731 + mc 1371 - 2*mc 411*mc 731 - 2*mc 411*mc 1371 - 2*mc 731*mc 1371 + 4*mc 411*mc 731*mc 1371) + 2048*(mc 412 + mc 732 + mc 1372 - 2*mc 412*mc 732 - 2*mc 412*mc 1372 - 2*mc 732*mc 1372 + 4*mc 412*mc 732*mc 1372) + 4096*(mc 413 + mc 733 + mc 1373 - 2*mc 413*mc 733 - 2*mc 413*mc 1373 - 2*mc 733*mc 1373 + 4*mc 413*mc 733*mc 1373) + 8192*(mc 414 + mc 734 + mc 1374 - 2*mc 414*mc 734 - 2*mc 414*mc 1374 - 2*mc 734*mc 1374 + 4*mc 414*mc 734*mc 1374) + 16384*(mc 415 + mc 735 + mc 1375 - 2*mc 415*mc 735 - 2*mc 415*mc 1375 - 2*mc 735*mc 1375 + 4*mc 415*mc 735*mc 1375) + 32768*(mc 416 + mc 736 + mc 1376 - 2*mc 416*mc 736 - 2*mc 416*mc 1376 - 2*mc 736*mc 1376 + 4*mc 416*mc 736*mc 1376) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1433, KeccakfPermAir.extraction.inter_1311, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_1310 c row = (mc 402 + mc 722 + mc 1362 - 2*mc 402*mc 722 - 2*mc 402*mc 1362 - 2*mc 722*mc 1362 + 4*mc 402*mc 722*mc 1362) + 2 * KeccakfPermAir.extraction.inter_1308 c row := by
    simp only [KeccakfPermAir.extraction.inter_1310, KeccakfPermAir.extraction.inter_1309, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_1308 c row = (mc 403 + mc 723 + mc 1363 - 2*mc 403*mc 723 - 2*mc 403*mc 1363 - 2*mc 723*mc 1363 + 4*mc 403*mc 723*mc 1363) + 2 * KeccakfPermAir.extraction.inter_1306 c row := by
    simp only [KeccakfPermAir.extraction.inter_1308, KeccakfPermAir.extraction.inter_1307, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_1306 c row = (mc 404 + mc 724 + mc 1364 - 2*mc 404*mc 724 - 2*mc 404*mc 1364 - 2*mc 724*mc 1364 + 4*mc 404*mc 724*mc 1364) + 2 * KeccakfPermAir.extraction.inter_1304 c row := by
    simp only [KeccakfPermAir.extraction.inter_1306, KeccakfPermAir.extraction.inter_1305, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_1304 c row = (mc 405 + mc 725 + mc 1365 - 2*mc 405*mc 725 - 2*mc 405*mc 1365 - 2*mc 725*mc 1365 + 4*mc 405*mc 725*mc 1365) + 2 * KeccakfPermAir.extraction.inter_1302 c row := by
    simp only [KeccakfPermAir.extraction.inter_1304, KeccakfPermAir.extraction.inter_1303, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_1302 c row = (mc 406 + mc 726 + mc 1366 - 2*mc 406*mc 726 - 2*mc 406*mc 1366 - 2*mc 726*mc 1366 + 4*mc 406*mc 726*mc 1366) + 2 * KeccakfPermAir.extraction.inter_1300 c row := by
    simp only [KeccakfPermAir.extraction.inter_1302, KeccakfPermAir.extraction.inter_1301, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_1300 c row = (mc 407 + mc 727 + mc 1367 - 2*mc 407*mc 727 - 2*mc 407*mc 1367 - 2*mc 727*mc 1367 + 4*mc 407*mc 727*mc 1367) + 2 * KeccakfPermAir.extraction.inter_1298 c row := by
    simp only [KeccakfPermAir.extraction.inter_1300, KeccakfPermAir.extraction.inter_1299, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_1298 c row = (mc 408 + mc 728 + mc 1368 - 2*mc 408*mc 728 - 2*mc 408*mc 1368 - 2*mc 728*mc 1368 + 4*mc 408*mc 728*mc 1368) + 2 * KeccakfPermAir.extraction.inter_1296 c row := by
    simp only [KeccakfPermAir.extraction.inter_1298, KeccakfPermAir.extraction.inter_1297, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_1296 c row = (mc 409 + mc 729 + mc 1369 - 2*mc 409*mc 729 - 2*mc 409*mc 1369 - 2*mc 729*mc 1369 + 4*mc 409*mc 729*mc 1369) + 2 * KeccakfPermAir.extraction.inter_1294 c row := by
    simp only [KeccakfPermAir.extraction.inter_1296, KeccakfPermAir.extraction.inter_1295, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_1294 c row = (mc 410 + mc 730 + mc 1370 - 2*mc 410*mc 730 - 2*mc 410*mc 1370 - 2*mc 730*mc 1370 + 4*mc 410*mc 730*mc 1370) + 2 * KeccakfPermAir.extraction.inter_1292 c row := by
    simp only [KeccakfPermAir.extraction.inter_1294, KeccakfPermAir.extraction.inter_1293, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_1292 c row = (mc 411 + mc 731 + mc 1371 - 2*mc 411*mc 731 - 2*mc 411*mc 1371 - 2*mc 731*mc 1371 + 4*mc 411*mc 731*mc 1371) + 2 * KeccakfPermAir.extraction.inter_1290 c row := by
    simp only [KeccakfPermAir.extraction.inter_1292, KeccakfPermAir.extraction.inter_1291, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_1290 c row = (mc 412 + mc 732 + mc 1372 - 2*mc 412*mc 732 - 2*mc 412*mc 1372 - 2*mc 732*mc 1372 + 4*mc 412*mc 732*mc 1372) + 2 * KeccakfPermAir.extraction.inter_1288 c row := by
    simp only [KeccakfPermAir.extraction.inter_1290, KeccakfPermAir.extraction.inter_1289, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_1288 c row = (mc 413 + mc 733 + mc 1373 - 2*mc 413*mc 733 - 2*mc 413*mc 1373 - 2*mc 733*mc 1373 + 4*mc 413*mc 733*mc 1373) + 2 * KeccakfPermAir.extraction.inter_1286 c row := by
    simp only [KeccakfPermAir.extraction.inter_1288, KeccakfPermAir.extraction.inter_1287, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_1286 c row = (mc 414 + mc 734 + mc 1374 - 2*mc 414*mc 734 - 2*mc 414*mc 1374 - 2*mc 734*mc 1374 + 4*mc 414*mc 734*mc 1374) + 2 * KeccakfPermAir.extraction.inter_1284 c row := by
    simp only [KeccakfPermAir.extraction.inter_1286, KeccakfPermAir.extraction.inter_1285, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_1284 c row = (mc 415 + mc 735 + mc 1375 - 2*mc 415*mc 735 - 2*mc 415*mc 1375 - 2*mc 735*mc 1375 + 4*mc 415*mc 735*mc 1375) + 2 * KeccakfPermAir.extraction.inter_1282 c row := by
    simp only [KeccakfPermAir.extraction.inter_1284, KeccakfPermAir.extraction.inter_1283, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_1282 c row = (mc 416 + mc 736 + mc 1376 - 2*mc 416*mc 736 - 2*mc 416*mc 1376 - 2*mc 736*mc 1376 + 4*mc 416*mc 736*mc 1376) := by
    simp only [KeccakfPermAir.extraction.inter_1282, KeccakfPermAir.extraction.inter_1281, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1498 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 417 737 1377 157 row) :
    mc 157 = (mc 417 + mc 737 + mc 1377 - 2*mc 417*mc 737 - 2*mc 417*mc 1377 - 2*mc 737*mc 1377 + 4*mc 417*mc 737*mc 1377) + 2*(mc 418 + mc 738 + mc 1378 - 2*mc 418*mc 738 - 2*mc 418*mc 1378 - 2*mc 738*mc 1378 + 4*mc 418*mc 738*mc 1378) + 4*(mc 419 + mc 739 + mc 1379 - 2*mc 419*mc 739 - 2*mc 419*mc 1379 - 2*mc 739*mc 1379 + 4*mc 419*mc 739*mc 1379) + 8*(mc 420 + mc 740 + mc 1380 - 2*mc 420*mc 740 - 2*mc 420*mc 1380 - 2*mc 740*mc 1380 + 4*mc 420*mc 740*mc 1380) + 16*(mc 421 + mc 741 + mc 1381 - 2*mc 421*mc 741 - 2*mc 421*mc 1381 - 2*mc 741*mc 1381 + 4*mc 421*mc 741*mc 1381) + 32*(mc 422 + mc 742 + mc 1382 - 2*mc 422*mc 742 - 2*mc 422*mc 1382 - 2*mc 742*mc 1382 + 4*mc 422*mc 742*mc 1382) + 64*(mc 423 + mc 743 + mc 1383 - 2*mc 423*mc 743 - 2*mc 423*mc 1383 - 2*mc 743*mc 1383 + 4*mc 423*mc 743*mc 1383) + 128*(mc 424 + mc 744 + mc 1384 - 2*mc 424*mc 744 - 2*mc 424*mc 1384 - 2*mc 744*mc 1384 + 4*mc 424*mc 744*mc 1384) + 256*(mc 425 + mc 745 + mc 1385 - 2*mc 425*mc 745 - 2*mc 425*mc 1385 - 2*mc 745*mc 1385 + 4*mc 425*mc 745*mc 1385) + 512*(mc 426 + mc 746 + mc 1386 - 2*mc 426*mc 746 - 2*mc 426*mc 1386 - 2*mc 746*mc 1386 + 4*mc 426*mc 746*mc 1386) + 1024*(mc 427 + mc 747 + mc 1387 - 2*mc 427*mc 747 - 2*mc 427*mc 1387 - 2*mc 747*mc 1387 + 4*mc 427*mc 747*mc 1387) + 2048*(mc 428 + mc 748 + mc 1388 - 2*mc 428*mc 748 - 2*mc 428*mc 1388 - 2*mc 748*mc 1388 + 4*mc 428*mc 748*mc 1388) + 4096*(mc 429 + mc 749 + mc 1389 - 2*mc 429*mc 749 - 2*mc 429*mc 1389 - 2*mc 749*mc 1389 + 4*mc 429*mc 749*mc 1389) + 8192*(mc 430 + mc 750 + mc 1390 - 2*mc 430*mc 750 - 2*mc 430*mc 1390 - 2*mc 750*mc 1390 + 4*mc 430*mc 750*mc 1390) + 16384*(mc 431 + mc 751 + mc 1391 - 2*mc 431*mc 751 - 2*mc 431*mc 1391 - 2*mc 751*mc 1391 + 4*mc 431*mc 751*mc 1391) + 32768*(mc 432 + mc 752 + mc 1392 - 2*mc 432*mc 752 - 2*mc 432*mc 1392 - 2*mc 752*mc 1392 + 4*mc 432*mc 752*mc 1392) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1498, KeccakfPermAir.extraction.inter_1342, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_1341 c row = (mc 418 + mc 738 + mc 1378 - 2*mc 418*mc 738 - 2*mc 418*mc 1378 - 2*mc 738*mc 1378 + 4*mc 418*mc 738*mc 1378) + 2 * KeccakfPermAir.extraction.inter_1339 c row := by
    simp only [KeccakfPermAir.extraction.inter_1341, KeccakfPermAir.extraction.inter_1340, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_1339 c row = (mc 419 + mc 739 + mc 1379 - 2*mc 419*mc 739 - 2*mc 419*mc 1379 - 2*mc 739*mc 1379 + 4*mc 419*mc 739*mc 1379) + 2 * KeccakfPermAir.extraction.inter_1337 c row := by
    simp only [KeccakfPermAir.extraction.inter_1339, KeccakfPermAir.extraction.inter_1338, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_1337 c row = (mc 420 + mc 740 + mc 1380 - 2*mc 420*mc 740 - 2*mc 420*mc 1380 - 2*mc 740*mc 1380 + 4*mc 420*mc 740*mc 1380) + 2 * KeccakfPermAir.extraction.inter_1335 c row := by
    simp only [KeccakfPermAir.extraction.inter_1337, KeccakfPermAir.extraction.inter_1336, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_1335 c row = (mc 421 + mc 741 + mc 1381 - 2*mc 421*mc 741 - 2*mc 421*mc 1381 - 2*mc 741*mc 1381 + 4*mc 421*mc 741*mc 1381) + 2 * KeccakfPermAir.extraction.inter_1333 c row := by
    simp only [KeccakfPermAir.extraction.inter_1335, KeccakfPermAir.extraction.inter_1334, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_1333 c row = (mc 422 + mc 742 + mc 1382 - 2*mc 422*mc 742 - 2*mc 422*mc 1382 - 2*mc 742*mc 1382 + 4*mc 422*mc 742*mc 1382) + 2 * KeccakfPermAir.extraction.inter_1331 c row := by
    simp only [KeccakfPermAir.extraction.inter_1333, KeccakfPermAir.extraction.inter_1332, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_1331 c row = (mc 423 + mc 743 + mc 1383 - 2*mc 423*mc 743 - 2*mc 423*mc 1383 - 2*mc 743*mc 1383 + 4*mc 423*mc 743*mc 1383) + 2 * KeccakfPermAir.extraction.inter_1329 c row := by
    simp only [KeccakfPermAir.extraction.inter_1331, KeccakfPermAir.extraction.inter_1330, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_1329 c row = (mc 424 + mc 744 + mc 1384 - 2*mc 424*mc 744 - 2*mc 424*mc 1384 - 2*mc 744*mc 1384 + 4*mc 424*mc 744*mc 1384) + 2 * KeccakfPermAir.extraction.inter_1327 c row := by
    simp only [KeccakfPermAir.extraction.inter_1329, KeccakfPermAir.extraction.inter_1328, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_1327 c row = (mc 425 + mc 745 + mc 1385 - 2*mc 425*mc 745 - 2*mc 425*mc 1385 - 2*mc 745*mc 1385 + 4*mc 425*mc 745*mc 1385) + 2 * KeccakfPermAir.extraction.inter_1325 c row := by
    simp only [KeccakfPermAir.extraction.inter_1327, KeccakfPermAir.extraction.inter_1326, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_1325 c row = (mc 426 + mc 746 + mc 1386 - 2*mc 426*mc 746 - 2*mc 426*mc 1386 - 2*mc 746*mc 1386 + 4*mc 426*mc 746*mc 1386) + 2 * KeccakfPermAir.extraction.inter_1323 c row := by
    simp only [KeccakfPermAir.extraction.inter_1325, KeccakfPermAir.extraction.inter_1324, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_1323 c row = (mc 427 + mc 747 + mc 1387 - 2*mc 427*mc 747 - 2*mc 427*mc 1387 - 2*mc 747*mc 1387 + 4*mc 427*mc 747*mc 1387) + 2 * KeccakfPermAir.extraction.inter_1321 c row := by
    simp only [KeccakfPermAir.extraction.inter_1323, KeccakfPermAir.extraction.inter_1322, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_1321 c row = (mc 428 + mc 748 + mc 1388 - 2*mc 428*mc 748 - 2*mc 428*mc 1388 - 2*mc 748*mc 1388 + 4*mc 428*mc 748*mc 1388) + 2 * KeccakfPermAir.extraction.inter_1319 c row := by
    simp only [KeccakfPermAir.extraction.inter_1321, KeccakfPermAir.extraction.inter_1320, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_1319 c row = (mc 429 + mc 749 + mc 1389 - 2*mc 429*mc 749 - 2*mc 429*mc 1389 - 2*mc 749*mc 1389 + 4*mc 429*mc 749*mc 1389) + 2 * KeccakfPermAir.extraction.inter_1317 c row := by
    simp only [KeccakfPermAir.extraction.inter_1319, KeccakfPermAir.extraction.inter_1318, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_1317 c row = (mc 430 + mc 750 + mc 1390 - 2*mc 430*mc 750 - 2*mc 430*mc 1390 - 2*mc 750*mc 1390 + 4*mc 430*mc 750*mc 1390) + 2 * KeccakfPermAir.extraction.inter_1315 c row := by
    simp only [KeccakfPermAir.extraction.inter_1317, KeccakfPermAir.extraction.inter_1316, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_1315 c row = (mc 431 + mc 751 + mc 1391 - 2*mc 431*mc 751 - 2*mc 431*mc 1391 - 2*mc 751*mc 1391 + 4*mc 431*mc 751*mc 1391) + 2 * KeccakfPermAir.extraction.inter_1313 c row := by
    simp only [KeccakfPermAir.extraction.inter_1315, KeccakfPermAir.extraction.inter_1314, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_1313 c row = (mc 432 + mc 752 + mc 1392 - 2*mc 432*mc 752 - 2*mc 432*mc 1392 - 2*mc 752*mc 1392 + 4*mc 432*mc 752*mc 1392) := by
    simp only [KeccakfPermAir.extraction.inter_1313, KeccakfPermAir.extraction.inter_1312, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1499 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 433 753 1393 158 row) :
    mc 158 = (mc 433 + mc 753 + mc 1393 - 2*mc 433*mc 753 - 2*mc 433*mc 1393 - 2*mc 753*mc 1393 + 4*mc 433*mc 753*mc 1393) + 2*(mc 434 + mc 754 + mc 1394 - 2*mc 434*mc 754 - 2*mc 434*mc 1394 - 2*mc 754*mc 1394 + 4*mc 434*mc 754*mc 1394) + 4*(mc 435 + mc 755 + mc 1395 - 2*mc 435*mc 755 - 2*mc 435*mc 1395 - 2*mc 755*mc 1395 + 4*mc 435*mc 755*mc 1395) + 8*(mc 436 + mc 756 + mc 1396 - 2*mc 436*mc 756 - 2*mc 436*mc 1396 - 2*mc 756*mc 1396 + 4*mc 436*mc 756*mc 1396) + 16*(mc 437 + mc 757 + mc 1397 - 2*mc 437*mc 757 - 2*mc 437*mc 1397 - 2*mc 757*mc 1397 + 4*mc 437*mc 757*mc 1397) + 32*(mc 438 + mc 758 + mc 1398 - 2*mc 438*mc 758 - 2*mc 438*mc 1398 - 2*mc 758*mc 1398 + 4*mc 438*mc 758*mc 1398) + 64*(mc 439 + mc 759 + mc 1399 - 2*mc 439*mc 759 - 2*mc 439*mc 1399 - 2*mc 759*mc 1399 + 4*mc 439*mc 759*mc 1399) + 128*(mc 440 + mc 760 + mc 1400 - 2*mc 440*mc 760 - 2*mc 440*mc 1400 - 2*mc 760*mc 1400 + 4*mc 440*mc 760*mc 1400) + 256*(mc 441 + mc 761 + mc 1401 - 2*mc 441*mc 761 - 2*mc 441*mc 1401 - 2*mc 761*mc 1401 + 4*mc 441*mc 761*mc 1401) + 512*(mc 442 + mc 762 + mc 1402 - 2*mc 442*mc 762 - 2*mc 442*mc 1402 - 2*mc 762*mc 1402 + 4*mc 442*mc 762*mc 1402) + 1024*(mc 443 + mc 763 + mc 1403 - 2*mc 443*mc 763 - 2*mc 443*mc 1403 - 2*mc 763*mc 1403 + 4*mc 443*mc 763*mc 1403) + 2048*(mc 444 + mc 764 + mc 1404 - 2*mc 444*mc 764 - 2*mc 444*mc 1404 - 2*mc 764*mc 1404 + 4*mc 444*mc 764*mc 1404) + 4096*(mc 445 + mc 765 + mc 1405 - 2*mc 445*mc 765 - 2*mc 445*mc 1405 - 2*mc 765*mc 1405 + 4*mc 445*mc 765*mc 1405) + 8192*(mc 446 + mc 766 + mc 1406 - 2*mc 446*mc 766 - 2*mc 446*mc 1406 - 2*mc 766*mc 1406 + 4*mc 446*mc 766*mc 1406) + 16384*(mc 447 + mc 767 + mc 1407 - 2*mc 447*mc 767 - 2*mc 447*mc 1407 - 2*mc 767*mc 1407 + 4*mc 447*mc 767*mc 1407) + 32768*(mc 448 + mc 768 + mc 1408 - 2*mc 448*mc 768 - 2*mc 448*mc 1408 - 2*mc 768*mc 1408 + 4*mc 448*mc 768*mc 1408) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1499, KeccakfPermAir.extraction.inter_1373, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_1372 c row = (mc 434 + mc 754 + mc 1394 - 2*mc 434*mc 754 - 2*mc 434*mc 1394 - 2*mc 754*mc 1394 + 4*mc 434*mc 754*mc 1394) + 2 * KeccakfPermAir.extraction.inter_1370 c row := by
    simp only [KeccakfPermAir.extraction.inter_1372, KeccakfPermAir.extraction.inter_1371, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_1370 c row = (mc 435 + mc 755 + mc 1395 - 2*mc 435*mc 755 - 2*mc 435*mc 1395 - 2*mc 755*mc 1395 + 4*mc 435*mc 755*mc 1395) + 2 * KeccakfPermAir.extraction.inter_1368 c row := by
    simp only [KeccakfPermAir.extraction.inter_1370, KeccakfPermAir.extraction.inter_1369, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_1368 c row = (mc 436 + mc 756 + mc 1396 - 2*mc 436*mc 756 - 2*mc 436*mc 1396 - 2*mc 756*mc 1396 + 4*mc 436*mc 756*mc 1396) + 2 * KeccakfPermAir.extraction.inter_1366 c row := by
    simp only [KeccakfPermAir.extraction.inter_1368, KeccakfPermAir.extraction.inter_1367, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_1366 c row = (mc 437 + mc 757 + mc 1397 - 2*mc 437*mc 757 - 2*mc 437*mc 1397 - 2*mc 757*mc 1397 + 4*mc 437*mc 757*mc 1397) + 2 * KeccakfPermAir.extraction.inter_1364 c row := by
    simp only [KeccakfPermAir.extraction.inter_1366, KeccakfPermAir.extraction.inter_1365, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_1364 c row = (mc 438 + mc 758 + mc 1398 - 2*mc 438*mc 758 - 2*mc 438*mc 1398 - 2*mc 758*mc 1398 + 4*mc 438*mc 758*mc 1398) + 2 * KeccakfPermAir.extraction.inter_1362 c row := by
    simp only [KeccakfPermAir.extraction.inter_1364, KeccakfPermAir.extraction.inter_1363, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_1362 c row = (mc 439 + mc 759 + mc 1399 - 2*mc 439*mc 759 - 2*mc 439*mc 1399 - 2*mc 759*mc 1399 + 4*mc 439*mc 759*mc 1399) + 2 * KeccakfPermAir.extraction.inter_1360 c row := by
    simp only [KeccakfPermAir.extraction.inter_1362, KeccakfPermAir.extraction.inter_1361, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_1360 c row = (mc 440 + mc 760 + mc 1400 - 2*mc 440*mc 760 - 2*mc 440*mc 1400 - 2*mc 760*mc 1400 + 4*mc 440*mc 760*mc 1400) + 2 * KeccakfPermAir.extraction.inter_1358 c row := by
    simp only [KeccakfPermAir.extraction.inter_1360, KeccakfPermAir.extraction.inter_1359, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_1358 c row = (mc 441 + mc 761 + mc 1401 - 2*mc 441*mc 761 - 2*mc 441*mc 1401 - 2*mc 761*mc 1401 + 4*mc 441*mc 761*mc 1401) + 2 * KeccakfPermAir.extraction.inter_1356 c row := by
    simp only [KeccakfPermAir.extraction.inter_1358, KeccakfPermAir.extraction.inter_1357, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_1356 c row = (mc 442 + mc 762 + mc 1402 - 2*mc 442*mc 762 - 2*mc 442*mc 1402 - 2*mc 762*mc 1402 + 4*mc 442*mc 762*mc 1402) + 2 * KeccakfPermAir.extraction.inter_1354 c row := by
    simp only [KeccakfPermAir.extraction.inter_1356, KeccakfPermAir.extraction.inter_1355, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_1354 c row = (mc 443 + mc 763 + mc 1403 - 2*mc 443*mc 763 - 2*mc 443*mc 1403 - 2*mc 763*mc 1403 + 4*mc 443*mc 763*mc 1403) + 2 * KeccakfPermAir.extraction.inter_1352 c row := by
    simp only [KeccakfPermAir.extraction.inter_1354, KeccakfPermAir.extraction.inter_1353, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_1352 c row = (mc 444 + mc 764 + mc 1404 - 2*mc 444*mc 764 - 2*mc 444*mc 1404 - 2*mc 764*mc 1404 + 4*mc 444*mc 764*mc 1404) + 2 * KeccakfPermAir.extraction.inter_1350 c row := by
    simp only [KeccakfPermAir.extraction.inter_1352, KeccakfPermAir.extraction.inter_1351, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_1350 c row = (mc 445 + mc 765 + mc 1405 - 2*mc 445*mc 765 - 2*mc 445*mc 1405 - 2*mc 765*mc 1405 + 4*mc 445*mc 765*mc 1405) + 2 * KeccakfPermAir.extraction.inter_1348 c row := by
    simp only [KeccakfPermAir.extraction.inter_1350, KeccakfPermAir.extraction.inter_1349, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_1348 c row = (mc 446 + mc 766 + mc 1406 - 2*mc 446*mc 766 - 2*mc 446*mc 1406 - 2*mc 766*mc 1406 + 4*mc 446*mc 766*mc 1406) + 2 * KeccakfPermAir.extraction.inter_1346 c row := by
    simp only [KeccakfPermAir.extraction.inter_1348, KeccakfPermAir.extraction.inter_1347, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_1346 c row = (mc 447 + mc 767 + mc 1407 - 2*mc 447*mc 767 - 2*mc 447*mc 1407 - 2*mc 767*mc 1407 + 4*mc 447*mc 767*mc 1407) + 2 * KeccakfPermAir.extraction.inter_1344 c row := by
    simp only [KeccakfPermAir.extraction.inter_1346, KeccakfPermAir.extraction.inter_1345, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_1344 c row = (mc 448 + mc 768 + mc 1408 - 2*mc 448*mc 768 - 2*mc 448*mc 1408 - 2*mc 768*mc 1408 + 4*mc 448*mc 768*mc 1408) := by
    simp only [KeccakfPermAir.extraction.inter_1344, KeccakfPermAir.extraction.inter_1343, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1500 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 449 769 1409 159 row) :
    mc 159 = (mc 449 + mc 769 + mc 1409 - 2*mc 449*mc 769 - 2*mc 449*mc 1409 - 2*mc 769*mc 1409 + 4*mc 449*mc 769*mc 1409) + 2*(mc 450 + mc 770 + mc 1410 - 2*mc 450*mc 770 - 2*mc 450*mc 1410 - 2*mc 770*mc 1410 + 4*mc 450*mc 770*mc 1410) + 4*(mc 451 + mc 771 + mc 1411 - 2*mc 451*mc 771 - 2*mc 451*mc 1411 - 2*mc 771*mc 1411 + 4*mc 451*mc 771*mc 1411) + 8*(mc 452 + mc 772 + mc 1412 - 2*mc 452*mc 772 - 2*mc 452*mc 1412 - 2*mc 772*mc 1412 + 4*mc 452*mc 772*mc 1412) + 16*(mc 453 + mc 773 + mc 1413 - 2*mc 453*mc 773 - 2*mc 453*mc 1413 - 2*mc 773*mc 1413 + 4*mc 453*mc 773*mc 1413) + 32*(mc 454 + mc 774 + mc 1414 - 2*mc 454*mc 774 - 2*mc 454*mc 1414 - 2*mc 774*mc 1414 + 4*mc 454*mc 774*mc 1414) + 64*(mc 455 + mc 775 + mc 1415 - 2*mc 455*mc 775 - 2*mc 455*mc 1415 - 2*mc 775*mc 1415 + 4*mc 455*mc 775*mc 1415) + 128*(mc 456 + mc 776 + mc 1416 - 2*mc 456*mc 776 - 2*mc 456*mc 1416 - 2*mc 776*mc 1416 + 4*mc 456*mc 776*mc 1416) + 256*(mc 457 + mc 777 + mc 1417 - 2*mc 457*mc 777 - 2*mc 457*mc 1417 - 2*mc 777*mc 1417 + 4*mc 457*mc 777*mc 1417) + 512*(mc 458 + mc 778 + mc 1418 - 2*mc 458*mc 778 - 2*mc 458*mc 1418 - 2*mc 778*mc 1418 + 4*mc 458*mc 778*mc 1418) + 1024*(mc 459 + mc 779 + mc 1419 - 2*mc 459*mc 779 - 2*mc 459*mc 1419 - 2*mc 779*mc 1419 + 4*mc 459*mc 779*mc 1419) + 2048*(mc 460 + mc 780 + mc 1420 - 2*mc 460*mc 780 - 2*mc 460*mc 1420 - 2*mc 780*mc 1420 + 4*mc 460*mc 780*mc 1420) + 4096*(mc 461 + mc 781 + mc 1421 - 2*mc 461*mc 781 - 2*mc 461*mc 1421 - 2*mc 781*mc 1421 + 4*mc 461*mc 781*mc 1421) + 8192*(mc 462 + mc 782 + mc 1422 - 2*mc 462*mc 782 - 2*mc 462*mc 1422 - 2*mc 782*mc 1422 + 4*mc 462*mc 782*mc 1422) + 16384*(mc 463 + mc 783 + mc 1423 - 2*mc 463*mc 783 - 2*mc 463*mc 1423 - 2*mc 783*mc 1423 + 4*mc 463*mc 783*mc 1423) + 32768*(mc 464 + mc 784 + mc 1424 - 2*mc 464*mc 784 - 2*mc 464*mc 1424 - 2*mc 784*mc 1424 + 4*mc 464*mc 784*mc 1424) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1500, KeccakfPermAir.extraction.inter_1404, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_1403 c row = (mc 450 + mc 770 + mc 1410 - 2*mc 450*mc 770 - 2*mc 450*mc 1410 - 2*mc 770*mc 1410 + 4*mc 450*mc 770*mc 1410) + 2 * KeccakfPermAir.extraction.inter_1401 c row := by
    simp only [KeccakfPermAir.extraction.inter_1403, KeccakfPermAir.extraction.inter_1402, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_1401 c row = (mc 451 + mc 771 + mc 1411 - 2*mc 451*mc 771 - 2*mc 451*mc 1411 - 2*mc 771*mc 1411 + 4*mc 451*mc 771*mc 1411) + 2 * KeccakfPermAir.extraction.inter_1399 c row := by
    simp only [KeccakfPermAir.extraction.inter_1401, KeccakfPermAir.extraction.inter_1400, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_1399 c row = (mc 452 + mc 772 + mc 1412 - 2*mc 452*mc 772 - 2*mc 452*mc 1412 - 2*mc 772*mc 1412 + 4*mc 452*mc 772*mc 1412) + 2 * KeccakfPermAir.extraction.inter_1397 c row := by
    simp only [KeccakfPermAir.extraction.inter_1399, KeccakfPermAir.extraction.inter_1398, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_1397 c row = (mc 453 + mc 773 + mc 1413 - 2*mc 453*mc 773 - 2*mc 453*mc 1413 - 2*mc 773*mc 1413 + 4*mc 453*mc 773*mc 1413) + 2 * KeccakfPermAir.extraction.inter_1395 c row := by
    simp only [KeccakfPermAir.extraction.inter_1397, KeccakfPermAir.extraction.inter_1396, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_1395 c row = (mc 454 + mc 774 + mc 1414 - 2*mc 454*mc 774 - 2*mc 454*mc 1414 - 2*mc 774*mc 1414 + 4*mc 454*mc 774*mc 1414) + 2 * KeccakfPermAir.extraction.inter_1393 c row := by
    simp only [KeccakfPermAir.extraction.inter_1395, KeccakfPermAir.extraction.inter_1394, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_1393 c row = (mc 455 + mc 775 + mc 1415 - 2*mc 455*mc 775 - 2*mc 455*mc 1415 - 2*mc 775*mc 1415 + 4*mc 455*mc 775*mc 1415) + 2 * KeccakfPermAir.extraction.inter_1391 c row := by
    simp only [KeccakfPermAir.extraction.inter_1393, KeccakfPermAir.extraction.inter_1392, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_1391 c row = (mc 456 + mc 776 + mc 1416 - 2*mc 456*mc 776 - 2*mc 456*mc 1416 - 2*mc 776*mc 1416 + 4*mc 456*mc 776*mc 1416) + 2 * KeccakfPermAir.extraction.inter_1389 c row := by
    simp only [KeccakfPermAir.extraction.inter_1391, KeccakfPermAir.extraction.inter_1390, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_1389 c row = (mc 457 + mc 777 + mc 1417 - 2*mc 457*mc 777 - 2*mc 457*mc 1417 - 2*mc 777*mc 1417 + 4*mc 457*mc 777*mc 1417) + 2 * KeccakfPermAir.extraction.inter_1387 c row := by
    simp only [KeccakfPermAir.extraction.inter_1389, KeccakfPermAir.extraction.inter_1388, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_1387 c row = (mc 458 + mc 778 + mc 1418 - 2*mc 458*mc 778 - 2*mc 458*mc 1418 - 2*mc 778*mc 1418 + 4*mc 458*mc 778*mc 1418) + 2 * KeccakfPermAir.extraction.inter_1385 c row := by
    simp only [KeccakfPermAir.extraction.inter_1387, KeccakfPermAir.extraction.inter_1386, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_1385 c row = (mc 459 + mc 779 + mc 1419 - 2*mc 459*mc 779 - 2*mc 459*mc 1419 - 2*mc 779*mc 1419 + 4*mc 459*mc 779*mc 1419) + 2 * KeccakfPermAir.extraction.inter_1383 c row := by
    simp only [KeccakfPermAir.extraction.inter_1385, KeccakfPermAir.extraction.inter_1384, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_1383 c row = (mc 460 + mc 780 + mc 1420 - 2*mc 460*mc 780 - 2*mc 460*mc 1420 - 2*mc 780*mc 1420 + 4*mc 460*mc 780*mc 1420) + 2 * KeccakfPermAir.extraction.inter_1381 c row := by
    simp only [KeccakfPermAir.extraction.inter_1383, KeccakfPermAir.extraction.inter_1382, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_1381 c row = (mc 461 + mc 781 + mc 1421 - 2*mc 461*mc 781 - 2*mc 461*mc 1421 - 2*mc 781*mc 1421 + 4*mc 461*mc 781*mc 1421) + 2 * KeccakfPermAir.extraction.inter_1379 c row := by
    simp only [KeccakfPermAir.extraction.inter_1381, KeccakfPermAir.extraction.inter_1380, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_1379 c row = (mc 462 + mc 782 + mc 1422 - 2*mc 462*mc 782 - 2*mc 462*mc 1422 - 2*mc 782*mc 1422 + 4*mc 462*mc 782*mc 1422) + 2 * KeccakfPermAir.extraction.inter_1377 c row := by
    simp only [KeccakfPermAir.extraction.inter_1379, KeccakfPermAir.extraction.inter_1378, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_1377 c row = (mc 463 + mc 783 + mc 1423 - 2*mc 463*mc 783 - 2*mc 463*mc 1423 - 2*mc 783*mc 1423 + 4*mc 463*mc 783*mc 1423) + 2 * KeccakfPermAir.extraction.inter_1375 c row := by
    simp only [KeccakfPermAir.extraction.inter_1377, KeccakfPermAir.extraction.inter_1376, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_1375 c row = (mc 464 + mc 784 + mc 1424 - 2*mc 464*mc 784 - 2*mc 464*mc 1424 - 2*mc 784*mc 1424 + 4*mc 464*mc 784*mc 1424) := by
    simp only [KeccakfPermAir.extraction.inter_1375, KeccakfPermAir.extraction.inter_1374, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1501 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 465 785 1425 160 row) :
    mc 160 = (mc 465 + mc 785 + mc 1425 - 2*mc 465*mc 785 - 2*mc 465*mc 1425 - 2*mc 785*mc 1425 + 4*mc 465*mc 785*mc 1425) + 2*(mc 466 + mc 786 + mc 1426 - 2*mc 466*mc 786 - 2*mc 466*mc 1426 - 2*mc 786*mc 1426 + 4*mc 466*mc 786*mc 1426) + 4*(mc 467 + mc 787 + mc 1427 - 2*mc 467*mc 787 - 2*mc 467*mc 1427 - 2*mc 787*mc 1427 + 4*mc 467*mc 787*mc 1427) + 8*(mc 468 + mc 788 + mc 1428 - 2*mc 468*mc 788 - 2*mc 468*mc 1428 - 2*mc 788*mc 1428 + 4*mc 468*mc 788*mc 1428) + 16*(mc 469 + mc 789 + mc 1429 - 2*mc 469*mc 789 - 2*mc 469*mc 1429 - 2*mc 789*mc 1429 + 4*mc 469*mc 789*mc 1429) + 32*(mc 470 + mc 790 + mc 1430 - 2*mc 470*mc 790 - 2*mc 470*mc 1430 - 2*mc 790*mc 1430 + 4*mc 470*mc 790*mc 1430) + 64*(mc 471 + mc 791 + mc 1431 - 2*mc 471*mc 791 - 2*mc 471*mc 1431 - 2*mc 791*mc 1431 + 4*mc 471*mc 791*mc 1431) + 128*(mc 472 + mc 792 + mc 1432 - 2*mc 472*mc 792 - 2*mc 472*mc 1432 - 2*mc 792*mc 1432 + 4*mc 472*mc 792*mc 1432) + 256*(mc 473 + mc 793 + mc 1433 - 2*mc 473*mc 793 - 2*mc 473*mc 1433 - 2*mc 793*mc 1433 + 4*mc 473*mc 793*mc 1433) + 512*(mc 474 + mc 794 + mc 1434 - 2*mc 474*mc 794 - 2*mc 474*mc 1434 - 2*mc 794*mc 1434 + 4*mc 474*mc 794*mc 1434) + 1024*(mc 475 + mc 795 + mc 1435 - 2*mc 475*mc 795 - 2*mc 475*mc 1435 - 2*mc 795*mc 1435 + 4*mc 475*mc 795*mc 1435) + 2048*(mc 476 + mc 796 + mc 1436 - 2*mc 476*mc 796 - 2*mc 476*mc 1436 - 2*mc 796*mc 1436 + 4*mc 476*mc 796*mc 1436) + 4096*(mc 477 + mc 797 + mc 1437 - 2*mc 477*mc 797 - 2*mc 477*mc 1437 - 2*mc 797*mc 1437 + 4*mc 477*mc 797*mc 1437) + 8192*(mc 478 + mc 798 + mc 1438 - 2*mc 478*mc 798 - 2*mc 478*mc 1438 - 2*mc 798*mc 1438 + 4*mc 478*mc 798*mc 1438) + 16384*(mc 479 + mc 799 + mc 1439 - 2*mc 479*mc 799 - 2*mc 479*mc 1439 - 2*mc 799*mc 1439 + 4*mc 479*mc 799*mc 1439) + 32768*(mc 480 + mc 800 + mc 1440 - 2*mc 480*mc 800 - 2*mc 480*mc 1440 - 2*mc 800*mc 1440 + 4*mc 480*mc 800*mc 1440) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1501, KeccakfPermAir.extraction.inter_1435, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_1434 c row = (mc 466 + mc 786 + mc 1426 - 2*mc 466*mc 786 - 2*mc 466*mc 1426 - 2*mc 786*mc 1426 + 4*mc 466*mc 786*mc 1426) + 2 * KeccakfPermAir.extraction.inter_1432 c row := by
    simp only [KeccakfPermAir.extraction.inter_1434, KeccakfPermAir.extraction.inter_1433, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_1432 c row = (mc 467 + mc 787 + mc 1427 - 2*mc 467*mc 787 - 2*mc 467*mc 1427 - 2*mc 787*mc 1427 + 4*mc 467*mc 787*mc 1427) + 2 * KeccakfPermAir.extraction.inter_1430 c row := by
    simp only [KeccakfPermAir.extraction.inter_1432, KeccakfPermAir.extraction.inter_1431, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_1430 c row = (mc 468 + mc 788 + mc 1428 - 2*mc 468*mc 788 - 2*mc 468*mc 1428 - 2*mc 788*mc 1428 + 4*mc 468*mc 788*mc 1428) + 2 * KeccakfPermAir.extraction.inter_1428 c row := by
    simp only [KeccakfPermAir.extraction.inter_1430, KeccakfPermAir.extraction.inter_1429, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_1428 c row = (mc 469 + mc 789 + mc 1429 - 2*mc 469*mc 789 - 2*mc 469*mc 1429 - 2*mc 789*mc 1429 + 4*mc 469*mc 789*mc 1429) + 2 * KeccakfPermAir.extraction.inter_1426 c row := by
    simp only [KeccakfPermAir.extraction.inter_1428, KeccakfPermAir.extraction.inter_1427, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_1426 c row = (mc 470 + mc 790 + mc 1430 - 2*mc 470*mc 790 - 2*mc 470*mc 1430 - 2*mc 790*mc 1430 + 4*mc 470*mc 790*mc 1430) + 2 * KeccakfPermAir.extraction.inter_1424 c row := by
    simp only [KeccakfPermAir.extraction.inter_1426, KeccakfPermAir.extraction.inter_1425, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_1424 c row = (mc 471 + mc 791 + mc 1431 - 2*mc 471*mc 791 - 2*mc 471*mc 1431 - 2*mc 791*mc 1431 + 4*mc 471*mc 791*mc 1431) + 2 * KeccakfPermAir.extraction.inter_1422 c row := by
    simp only [KeccakfPermAir.extraction.inter_1424, KeccakfPermAir.extraction.inter_1423, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_1422 c row = (mc 472 + mc 792 + mc 1432 - 2*mc 472*mc 792 - 2*mc 472*mc 1432 - 2*mc 792*mc 1432 + 4*mc 472*mc 792*mc 1432) + 2 * KeccakfPermAir.extraction.inter_1420 c row := by
    simp only [KeccakfPermAir.extraction.inter_1422, KeccakfPermAir.extraction.inter_1421, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_1420 c row = (mc 473 + mc 793 + mc 1433 - 2*mc 473*mc 793 - 2*mc 473*mc 1433 - 2*mc 793*mc 1433 + 4*mc 473*mc 793*mc 1433) + 2 * KeccakfPermAir.extraction.inter_1418 c row := by
    simp only [KeccakfPermAir.extraction.inter_1420, KeccakfPermAir.extraction.inter_1419, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_1418 c row = (mc 474 + mc 794 + mc 1434 - 2*mc 474*mc 794 - 2*mc 474*mc 1434 - 2*mc 794*mc 1434 + 4*mc 474*mc 794*mc 1434) + 2 * KeccakfPermAir.extraction.inter_1416 c row := by
    simp only [KeccakfPermAir.extraction.inter_1418, KeccakfPermAir.extraction.inter_1417, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_1416 c row = (mc 475 + mc 795 + mc 1435 - 2*mc 475*mc 795 - 2*mc 475*mc 1435 - 2*mc 795*mc 1435 + 4*mc 475*mc 795*mc 1435) + 2 * KeccakfPermAir.extraction.inter_1414 c row := by
    simp only [KeccakfPermAir.extraction.inter_1416, KeccakfPermAir.extraction.inter_1415, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_1414 c row = (mc 476 + mc 796 + mc 1436 - 2*mc 476*mc 796 - 2*mc 476*mc 1436 - 2*mc 796*mc 1436 + 4*mc 476*mc 796*mc 1436) + 2 * KeccakfPermAir.extraction.inter_1412 c row := by
    simp only [KeccakfPermAir.extraction.inter_1414, KeccakfPermAir.extraction.inter_1413, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_1412 c row = (mc 477 + mc 797 + mc 1437 - 2*mc 477*mc 797 - 2*mc 477*mc 1437 - 2*mc 797*mc 1437 + 4*mc 477*mc 797*mc 1437) + 2 * KeccakfPermAir.extraction.inter_1410 c row := by
    simp only [KeccakfPermAir.extraction.inter_1412, KeccakfPermAir.extraction.inter_1411, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_1410 c row = (mc 478 + mc 798 + mc 1438 - 2*mc 478*mc 798 - 2*mc 478*mc 1438 - 2*mc 798*mc 1438 + 4*mc 478*mc 798*mc 1438) + 2 * KeccakfPermAir.extraction.inter_1408 c row := by
    simp only [KeccakfPermAir.extraction.inter_1410, KeccakfPermAir.extraction.inter_1409, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_1408 c row = (mc 479 + mc 799 + mc 1439 - 2*mc 479*mc 799 - 2*mc 479*mc 1439 - 2*mc 799*mc 1439 + 4*mc 479*mc 799*mc 1439) + 2 * KeccakfPermAir.extraction.inter_1406 c row := by
    simp only [KeccakfPermAir.extraction.inter_1408, KeccakfPermAir.extraction.inter_1407, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_1406 c row = (mc 480 + mc 800 + mc 1440 - 2*mc 480*mc 800 - 2*mc 480*mc 1440 - 2*mc 800*mc 1440 + 4*mc 480*mc 800*mc 1440) := by
    simp only [KeccakfPermAir.extraction.inter_1406, KeccakfPermAir.extraction.inter_1405, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1566 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 481 801 1441 161 row) :
    mc 161 = (mc 481 + mc 801 + mc 1441 - 2*mc 481*mc 801 - 2*mc 481*mc 1441 - 2*mc 801*mc 1441 + 4*mc 481*mc 801*mc 1441) + 2*(mc 482 + mc 802 + mc 1442 - 2*mc 482*mc 802 - 2*mc 482*mc 1442 - 2*mc 802*mc 1442 + 4*mc 482*mc 802*mc 1442) + 4*(mc 483 + mc 803 + mc 1443 - 2*mc 483*mc 803 - 2*mc 483*mc 1443 - 2*mc 803*mc 1443 + 4*mc 483*mc 803*mc 1443) + 8*(mc 484 + mc 804 + mc 1444 - 2*mc 484*mc 804 - 2*mc 484*mc 1444 - 2*mc 804*mc 1444 + 4*mc 484*mc 804*mc 1444) + 16*(mc 485 + mc 805 + mc 1445 - 2*mc 485*mc 805 - 2*mc 485*mc 1445 - 2*mc 805*mc 1445 + 4*mc 485*mc 805*mc 1445) + 32*(mc 486 + mc 806 + mc 1446 - 2*mc 486*mc 806 - 2*mc 486*mc 1446 - 2*mc 806*mc 1446 + 4*mc 486*mc 806*mc 1446) + 64*(mc 487 + mc 807 + mc 1447 - 2*mc 487*mc 807 - 2*mc 487*mc 1447 - 2*mc 807*mc 1447 + 4*mc 487*mc 807*mc 1447) + 128*(mc 488 + mc 808 + mc 1448 - 2*mc 488*mc 808 - 2*mc 488*mc 1448 - 2*mc 808*mc 1448 + 4*mc 488*mc 808*mc 1448) + 256*(mc 489 + mc 809 + mc 1449 - 2*mc 489*mc 809 - 2*mc 489*mc 1449 - 2*mc 809*mc 1449 + 4*mc 489*mc 809*mc 1449) + 512*(mc 490 + mc 810 + mc 1450 - 2*mc 490*mc 810 - 2*mc 490*mc 1450 - 2*mc 810*mc 1450 + 4*mc 490*mc 810*mc 1450) + 1024*(mc 491 + mc 811 + mc 1451 - 2*mc 491*mc 811 - 2*mc 491*mc 1451 - 2*mc 811*mc 1451 + 4*mc 491*mc 811*mc 1451) + 2048*(mc 492 + mc 812 + mc 1452 - 2*mc 492*mc 812 - 2*mc 492*mc 1452 - 2*mc 812*mc 1452 + 4*mc 492*mc 812*mc 1452) + 4096*(mc 493 + mc 813 + mc 1453 - 2*mc 493*mc 813 - 2*mc 493*mc 1453 - 2*mc 813*mc 1453 + 4*mc 493*mc 813*mc 1453) + 8192*(mc 494 + mc 814 + mc 1454 - 2*mc 494*mc 814 - 2*mc 494*mc 1454 - 2*mc 814*mc 1454 + 4*mc 494*mc 814*mc 1454) + 16384*(mc 495 + mc 815 + mc 1455 - 2*mc 495*mc 815 - 2*mc 495*mc 1455 - 2*mc 815*mc 1455 + 4*mc 495*mc 815*mc 1455) + 32768*(mc 496 + mc 816 + mc 1456 - 2*mc 496*mc 816 - 2*mc 496*mc 1456 - 2*mc 816*mc 1456 + 4*mc 496*mc 816*mc 1456) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1566, KeccakfPermAir.extraction.inter_1466, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_1465 c row = (mc 482 + mc 802 + mc 1442 - 2*mc 482*mc 802 - 2*mc 482*mc 1442 - 2*mc 802*mc 1442 + 4*mc 482*mc 802*mc 1442) + 2 * KeccakfPermAir.extraction.inter_1463 c row := by
    simp only [KeccakfPermAir.extraction.inter_1465, KeccakfPermAir.extraction.inter_1464, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_1463 c row = (mc 483 + mc 803 + mc 1443 - 2*mc 483*mc 803 - 2*mc 483*mc 1443 - 2*mc 803*mc 1443 + 4*mc 483*mc 803*mc 1443) + 2 * KeccakfPermAir.extraction.inter_1461 c row := by
    simp only [KeccakfPermAir.extraction.inter_1463, KeccakfPermAir.extraction.inter_1462, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_1461 c row = (mc 484 + mc 804 + mc 1444 - 2*mc 484*mc 804 - 2*mc 484*mc 1444 - 2*mc 804*mc 1444 + 4*mc 484*mc 804*mc 1444) + 2 * KeccakfPermAir.extraction.inter_1459 c row := by
    simp only [KeccakfPermAir.extraction.inter_1461, KeccakfPermAir.extraction.inter_1460, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_1459 c row = (mc 485 + mc 805 + mc 1445 - 2*mc 485*mc 805 - 2*mc 485*mc 1445 - 2*mc 805*mc 1445 + 4*mc 485*mc 805*mc 1445) + 2 * KeccakfPermAir.extraction.inter_1457 c row := by
    simp only [KeccakfPermAir.extraction.inter_1459, KeccakfPermAir.extraction.inter_1458, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_1457 c row = (mc 486 + mc 806 + mc 1446 - 2*mc 486*mc 806 - 2*mc 486*mc 1446 - 2*mc 806*mc 1446 + 4*mc 486*mc 806*mc 1446) + 2 * KeccakfPermAir.extraction.inter_1455 c row := by
    simp only [KeccakfPermAir.extraction.inter_1457, KeccakfPermAir.extraction.inter_1456, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_1455 c row = (mc 487 + mc 807 + mc 1447 - 2*mc 487*mc 807 - 2*mc 487*mc 1447 - 2*mc 807*mc 1447 + 4*mc 487*mc 807*mc 1447) + 2 * KeccakfPermAir.extraction.inter_1453 c row := by
    simp only [KeccakfPermAir.extraction.inter_1455, KeccakfPermAir.extraction.inter_1454, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_1453 c row = (mc 488 + mc 808 + mc 1448 - 2*mc 488*mc 808 - 2*mc 488*mc 1448 - 2*mc 808*mc 1448 + 4*mc 488*mc 808*mc 1448) + 2 * KeccakfPermAir.extraction.inter_1451 c row := by
    simp only [KeccakfPermAir.extraction.inter_1453, KeccakfPermAir.extraction.inter_1452, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_1451 c row = (mc 489 + mc 809 + mc 1449 - 2*mc 489*mc 809 - 2*mc 489*mc 1449 - 2*mc 809*mc 1449 + 4*mc 489*mc 809*mc 1449) + 2 * KeccakfPermAir.extraction.inter_1449 c row := by
    simp only [KeccakfPermAir.extraction.inter_1451, KeccakfPermAir.extraction.inter_1450, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_1449 c row = (mc 490 + mc 810 + mc 1450 - 2*mc 490*mc 810 - 2*mc 490*mc 1450 - 2*mc 810*mc 1450 + 4*mc 490*mc 810*mc 1450) + 2 * KeccakfPermAir.extraction.inter_1447 c row := by
    simp only [KeccakfPermAir.extraction.inter_1449, KeccakfPermAir.extraction.inter_1448, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_1447 c row = (mc 491 + mc 811 + mc 1451 - 2*mc 491*mc 811 - 2*mc 491*mc 1451 - 2*mc 811*mc 1451 + 4*mc 491*mc 811*mc 1451) + 2 * KeccakfPermAir.extraction.inter_1445 c row := by
    simp only [KeccakfPermAir.extraction.inter_1447, KeccakfPermAir.extraction.inter_1446, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_1445 c row = (mc 492 + mc 812 + mc 1452 - 2*mc 492*mc 812 - 2*mc 492*mc 1452 - 2*mc 812*mc 1452 + 4*mc 492*mc 812*mc 1452) + 2 * KeccakfPermAir.extraction.inter_1443 c row := by
    simp only [KeccakfPermAir.extraction.inter_1445, KeccakfPermAir.extraction.inter_1444, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_1443 c row = (mc 493 + mc 813 + mc 1453 - 2*mc 493*mc 813 - 2*mc 493*mc 1453 - 2*mc 813*mc 1453 + 4*mc 493*mc 813*mc 1453) + 2 * KeccakfPermAir.extraction.inter_1441 c row := by
    simp only [KeccakfPermAir.extraction.inter_1443, KeccakfPermAir.extraction.inter_1442, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_1441 c row = (mc 494 + mc 814 + mc 1454 - 2*mc 494*mc 814 - 2*mc 494*mc 1454 - 2*mc 814*mc 1454 + 4*mc 494*mc 814*mc 1454) + 2 * KeccakfPermAir.extraction.inter_1439 c row := by
    simp only [KeccakfPermAir.extraction.inter_1441, KeccakfPermAir.extraction.inter_1440, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_1439 c row = (mc 495 + mc 815 + mc 1455 - 2*mc 495*mc 815 - 2*mc 495*mc 1455 - 2*mc 815*mc 1455 + 4*mc 495*mc 815*mc 1455) + 2 * KeccakfPermAir.extraction.inter_1437 c row := by
    simp only [KeccakfPermAir.extraction.inter_1439, KeccakfPermAir.extraction.inter_1438, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_1437 c row = (mc 496 + mc 816 + mc 1456 - 2*mc 496*mc 816 - 2*mc 496*mc 1456 - 2*mc 816*mc 1456 + 4*mc 496*mc 816*mc 1456) := by
    simp only [KeccakfPermAir.extraction.inter_1437, KeccakfPermAir.extraction.inter_1436, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1567 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 497 817 1457 162 row) :
    mc 162 = (mc 497 + mc 817 + mc 1457 - 2*mc 497*mc 817 - 2*mc 497*mc 1457 - 2*mc 817*mc 1457 + 4*mc 497*mc 817*mc 1457) + 2*(mc 498 + mc 818 + mc 1458 - 2*mc 498*mc 818 - 2*mc 498*mc 1458 - 2*mc 818*mc 1458 + 4*mc 498*mc 818*mc 1458) + 4*(mc 499 + mc 819 + mc 1459 - 2*mc 499*mc 819 - 2*mc 499*mc 1459 - 2*mc 819*mc 1459 + 4*mc 499*mc 819*mc 1459) + 8*(mc 500 + mc 820 + mc 1460 - 2*mc 500*mc 820 - 2*mc 500*mc 1460 - 2*mc 820*mc 1460 + 4*mc 500*mc 820*mc 1460) + 16*(mc 501 + mc 821 + mc 1461 - 2*mc 501*mc 821 - 2*mc 501*mc 1461 - 2*mc 821*mc 1461 + 4*mc 501*mc 821*mc 1461) + 32*(mc 502 + mc 822 + mc 1462 - 2*mc 502*mc 822 - 2*mc 502*mc 1462 - 2*mc 822*mc 1462 + 4*mc 502*mc 822*mc 1462) + 64*(mc 503 + mc 823 + mc 1463 - 2*mc 503*mc 823 - 2*mc 503*mc 1463 - 2*mc 823*mc 1463 + 4*mc 503*mc 823*mc 1463) + 128*(mc 504 + mc 824 + mc 1464 - 2*mc 504*mc 824 - 2*mc 504*mc 1464 - 2*mc 824*mc 1464 + 4*mc 504*mc 824*mc 1464) + 256*(mc 505 + mc 825 + mc 1465 - 2*mc 505*mc 825 - 2*mc 505*mc 1465 - 2*mc 825*mc 1465 + 4*mc 505*mc 825*mc 1465) + 512*(mc 506 + mc 826 + mc 1466 - 2*mc 506*mc 826 - 2*mc 506*mc 1466 - 2*mc 826*mc 1466 + 4*mc 506*mc 826*mc 1466) + 1024*(mc 507 + mc 827 + mc 1467 - 2*mc 507*mc 827 - 2*mc 507*mc 1467 - 2*mc 827*mc 1467 + 4*mc 507*mc 827*mc 1467) + 2048*(mc 508 + mc 828 + mc 1468 - 2*mc 508*mc 828 - 2*mc 508*mc 1468 - 2*mc 828*mc 1468 + 4*mc 508*mc 828*mc 1468) + 4096*(mc 509 + mc 829 + mc 1469 - 2*mc 509*mc 829 - 2*mc 509*mc 1469 - 2*mc 829*mc 1469 + 4*mc 509*mc 829*mc 1469) + 8192*(mc 510 + mc 830 + mc 1470 - 2*mc 510*mc 830 - 2*mc 510*mc 1470 - 2*mc 830*mc 1470 + 4*mc 510*mc 830*mc 1470) + 16384*(mc 511 + mc 831 + mc 1471 - 2*mc 511*mc 831 - 2*mc 511*mc 1471 - 2*mc 831*mc 1471 + 4*mc 511*mc 831*mc 1471) + 32768*(mc 512 + mc 832 + mc 1472 - 2*mc 512*mc 832 - 2*mc 512*mc 1472 - 2*mc 832*mc 1472 + 4*mc 512*mc 832*mc 1472) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1567, KeccakfPermAir.extraction.inter_1497, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_1496 c row = (mc 498 + mc 818 + mc 1458 - 2*mc 498*mc 818 - 2*mc 498*mc 1458 - 2*mc 818*mc 1458 + 4*mc 498*mc 818*mc 1458) + 2 * KeccakfPermAir.extraction.inter_1494 c row := by
    simp only [KeccakfPermAir.extraction.inter_1496, KeccakfPermAir.extraction.inter_1495, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_1494 c row = (mc 499 + mc 819 + mc 1459 - 2*mc 499*mc 819 - 2*mc 499*mc 1459 - 2*mc 819*mc 1459 + 4*mc 499*mc 819*mc 1459) + 2 * KeccakfPermAir.extraction.inter_1492 c row := by
    simp only [KeccakfPermAir.extraction.inter_1494, KeccakfPermAir.extraction.inter_1493, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_1492 c row = (mc 500 + mc 820 + mc 1460 - 2*mc 500*mc 820 - 2*mc 500*mc 1460 - 2*mc 820*mc 1460 + 4*mc 500*mc 820*mc 1460) + 2 * KeccakfPermAir.extraction.inter_1490 c row := by
    simp only [KeccakfPermAir.extraction.inter_1492, KeccakfPermAir.extraction.inter_1491, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_1490 c row = (mc 501 + mc 821 + mc 1461 - 2*mc 501*mc 821 - 2*mc 501*mc 1461 - 2*mc 821*mc 1461 + 4*mc 501*mc 821*mc 1461) + 2 * KeccakfPermAir.extraction.inter_1488 c row := by
    simp only [KeccakfPermAir.extraction.inter_1490, KeccakfPermAir.extraction.inter_1489, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_1488 c row = (mc 502 + mc 822 + mc 1462 - 2*mc 502*mc 822 - 2*mc 502*mc 1462 - 2*mc 822*mc 1462 + 4*mc 502*mc 822*mc 1462) + 2 * KeccakfPermAir.extraction.inter_1486 c row := by
    simp only [KeccakfPermAir.extraction.inter_1488, KeccakfPermAir.extraction.inter_1487, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_1486 c row = (mc 503 + mc 823 + mc 1463 - 2*mc 503*mc 823 - 2*mc 503*mc 1463 - 2*mc 823*mc 1463 + 4*mc 503*mc 823*mc 1463) + 2 * KeccakfPermAir.extraction.inter_1484 c row := by
    simp only [KeccakfPermAir.extraction.inter_1486, KeccakfPermAir.extraction.inter_1485, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_1484 c row = (mc 504 + mc 824 + mc 1464 - 2*mc 504*mc 824 - 2*mc 504*mc 1464 - 2*mc 824*mc 1464 + 4*mc 504*mc 824*mc 1464) + 2 * KeccakfPermAir.extraction.inter_1482 c row := by
    simp only [KeccakfPermAir.extraction.inter_1484, KeccakfPermAir.extraction.inter_1483, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_1482 c row = (mc 505 + mc 825 + mc 1465 - 2*mc 505*mc 825 - 2*mc 505*mc 1465 - 2*mc 825*mc 1465 + 4*mc 505*mc 825*mc 1465) + 2 * KeccakfPermAir.extraction.inter_1480 c row := by
    simp only [KeccakfPermAir.extraction.inter_1482, KeccakfPermAir.extraction.inter_1481, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_1480 c row = (mc 506 + mc 826 + mc 1466 - 2*mc 506*mc 826 - 2*mc 506*mc 1466 - 2*mc 826*mc 1466 + 4*mc 506*mc 826*mc 1466) + 2 * KeccakfPermAir.extraction.inter_1478 c row := by
    simp only [KeccakfPermAir.extraction.inter_1480, KeccakfPermAir.extraction.inter_1479, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_1478 c row = (mc 507 + mc 827 + mc 1467 - 2*mc 507*mc 827 - 2*mc 507*mc 1467 - 2*mc 827*mc 1467 + 4*mc 507*mc 827*mc 1467) + 2 * KeccakfPermAir.extraction.inter_1476 c row := by
    simp only [KeccakfPermAir.extraction.inter_1478, KeccakfPermAir.extraction.inter_1477, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_1476 c row = (mc 508 + mc 828 + mc 1468 - 2*mc 508*mc 828 - 2*mc 508*mc 1468 - 2*mc 828*mc 1468 + 4*mc 508*mc 828*mc 1468) + 2 * KeccakfPermAir.extraction.inter_1474 c row := by
    simp only [KeccakfPermAir.extraction.inter_1476, KeccakfPermAir.extraction.inter_1475, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_1474 c row = (mc 509 + mc 829 + mc 1469 - 2*mc 509*mc 829 - 2*mc 509*mc 1469 - 2*mc 829*mc 1469 + 4*mc 509*mc 829*mc 1469) + 2 * KeccakfPermAir.extraction.inter_1472 c row := by
    simp only [KeccakfPermAir.extraction.inter_1474, KeccakfPermAir.extraction.inter_1473, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_1472 c row = (mc 510 + mc 830 + mc 1470 - 2*mc 510*mc 830 - 2*mc 510*mc 1470 - 2*mc 830*mc 1470 + 4*mc 510*mc 830*mc 1470) + 2 * KeccakfPermAir.extraction.inter_1470 c row := by
    simp only [KeccakfPermAir.extraction.inter_1472, KeccakfPermAir.extraction.inter_1471, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_1470 c row = (mc 511 + mc 831 + mc 1471 - 2*mc 511*mc 831 - 2*mc 511*mc 1471 - 2*mc 831*mc 1471 + 4*mc 511*mc 831*mc 1471) + 2 * KeccakfPermAir.extraction.inter_1468 c row := by
    simp only [KeccakfPermAir.extraction.inter_1470, KeccakfPermAir.extraction.inter_1469, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_1468 c row = (mc 512 + mc 832 + mc 1472 - 2*mc 512*mc 832 - 2*mc 512*mc 1472 - 2*mc 832*mc 1472 + 4*mc 512*mc 832*mc 1472) := by
    simp only [KeccakfPermAir.extraction.inter_1468, KeccakfPermAir.extraction.inter_1467, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1568 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 513 833 1473 163 row) :
    mc 163 = (mc 513 + mc 833 + mc 1473 - 2*mc 513*mc 833 - 2*mc 513*mc 1473 - 2*mc 833*mc 1473 + 4*mc 513*mc 833*mc 1473) + 2*(mc 514 + mc 834 + mc 1474 - 2*mc 514*mc 834 - 2*mc 514*mc 1474 - 2*mc 834*mc 1474 + 4*mc 514*mc 834*mc 1474) + 4*(mc 515 + mc 835 + mc 1475 - 2*mc 515*mc 835 - 2*mc 515*mc 1475 - 2*mc 835*mc 1475 + 4*mc 515*mc 835*mc 1475) + 8*(mc 516 + mc 836 + mc 1476 - 2*mc 516*mc 836 - 2*mc 516*mc 1476 - 2*mc 836*mc 1476 + 4*mc 516*mc 836*mc 1476) + 16*(mc 517 + mc 837 + mc 1477 - 2*mc 517*mc 837 - 2*mc 517*mc 1477 - 2*mc 837*mc 1477 + 4*mc 517*mc 837*mc 1477) + 32*(mc 518 + mc 838 + mc 1478 - 2*mc 518*mc 838 - 2*mc 518*mc 1478 - 2*mc 838*mc 1478 + 4*mc 518*mc 838*mc 1478) + 64*(mc 519 + mc 839 + mc 1479 - 2*mc 519*mc 839 - 2*mc 519*mc 1479 - 2*mc 839*mc 1479 + 4*mc 519*mc 839*mc 1479) + 128*(mc 520 + mc 840 + mc 1480 - 2*mc 520*mc 840 - 2*mc 520*mc 1480 - 2*mc 840*mc 1480 + 4*mc 520*mc 840*mc 1480) + 256*(mc 521 + mc 841 + mc 1481 - 2*mc 521*mc 841 - 2*mc 521*mc 1481 - 2*mc 841*mc 1481 + 4*mc 521*mc 841*mc 1481) + 512*(mc 522 + mc 842 + mc 1482 - 2*mc 522*mc 842 - 2*mc 522*mc 1482 - 2*mc 842*mc 1482 + 4*mc 522*mc 842*mc 1482) + 1024*(mc 523 + mc 843 + mc 1483 - 2*mc 523*mc 843 - 2*mc 523*mc 1483 - 2*mc 843*mc 1483 + 4*mc 523*mc 843*mc 1483) + 2048*(mc 524 + mc 844 + mc 1484 - 2*mc 524*mc 844 - 2*mc 524*mc 1484 - 2*mc 844*mc 1484 + 4*mc 524*mc 844*mc 1484) + 4096*(mc 525 + mc 845 + mc 1485 - 2*mc 525*mc 845 - 2*mc 525*mc 1485 - 2*mc 845*mc 1485 + 4*mc 525*mc 845*mc 1485) + 8192*(mc 526 + mc 846 + mc 1486 - 2*mc 526*mc 846 - 2*mc 526*mc 1486 - 2*mc 846*mc 1486 + 4*mc 526*mc 846*mc 1486) + 16384*(mc 527 + mc 847 + mc 1487 - 2*mc 527*mc 847 - 2*mc 527*mc 1487 - 2*mc 847*mc 1487 + 4*mc 527*mc 847*mc 1487) + 32768*(mc 528 + mc 848 + mc 1488 - 2*mc 528*mc 848 - 2*mc 528*mc 1488 - 2*mc 848*mc 1488 + 4*mc 528*mc 848*mc 1488) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1568, KeccakfPermAir.extraction.inter_1528, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_1527 c row = (mc 514 + mc 834 + mc 1474 - 2*mc 514*mc 834 - 2*mc 514*mc 1474 - 2*mc 834*mc 1474 + 4*mc 514*mc 834*mc 1474) + 2 * KeccakfPermAir.extraction.inter_1525 c row := by
    simp only [KeccakfPermAir.extraction.inter_1527, KeccakfPermAir.extraction.inter_1526, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_1525 c row = (mc 515 + mc 835 + mc 1475 - 2*mc 515*mc 835 - 2*mc 515*mc 1475 - 2*mc 835*mc 1475 + 4*mc 515*mc 835*mc 1475) + 2 * KeccakfPermAir.extraction.inter_1523 c row := by
    simp only [KeccakfPermAir.extraction.inter_1525, KeccakfPermAir.extraction.inter_1524, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_1523 c row = (mc 516 + mc 836 + mc 1476 - 2*mc 516*mc 836 - 2*mc 516*mc 1476 - 2*mc 836*mc 1476 + 4*mc 516*mc 836*mc 1476) + 2 * KeccakfPermAir.extraction.inter_1521 c row := by
    simp only [KeccakfPermAir.extraction.inter_1523, KeccakfPermAir.extraction.inter_1522, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_1521 c row = (mc 517 + mc 837 + mc 1477 - 2*mc 517*mc 837 - 2*mc 517*mc 1477 - 2*mc 837*mc 1477 + 4*mc 517*mc 837*mc 1477) + 2 * KeccakfPermAir.extraction.inter_1519 c row := by
    simp only [KeccakfPermAir.extraction.inter_1521, KeccakfPermAir.extraction.inter_1520, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_1519 c row = (mc 518 + mc 838 + mc 1478 - 2*mc 518*mc 838 - 2*mc 518*mc 1478 - 2*mc 838*mc 1478 + 4*mc 518*mc 838*mc 1478) + 2 * KeccakfPermAir.extraction.inter_1517 c row := by
    simp only [KeccakfPermAir.extraction.inter_1519, KeccakfPermAir.extraction.inter_1518, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_1517 c row = (mc 519 + mc 839 + mc 1479 - 2*mc 519*mc 839 - 2*mc 519*mc 1479 - 2*mc 839*mc 1479 + 4*mc 519*mc 839*mc 1479) + 2 * KeccakfPermAir.extraction.inter_1515 c row := by
    simp only [KeccakfPermAir.extraction.inter_1517, KeccakfPermAir.extraction.inter_1516, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_1515 c row = (mc 520 + mc 840 + mc 1480 - 2*mc 520*mc 840 - 2*mc 520*mc 1480 - 2*mc 840*mc 1480 + 4*mc 520*mc 840*mc 1480) + 2 * KeccakfPermAir.extraction.inter_1513 c row := by
    simp only [KeccakfPermAir.extraction.inter_1515, KeccakfPermAir.extraction.inter_1514, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_1513 c row = (mc 521 + mc 841 + mc 1481 - 2*mc 521*mc 841 - 2*mc 521*mc 1481 - 2*mc 841*mc 1481 + 4*mc 521*mc 841*mc 1481) + 2 * KeccakfPermAir.extraction.inter_1511 c row := by
    simp only [KeccakfPermAir.extraction.inter_1513, KeccakfPermAir.extraction.inter_1512, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_1511 c row = (mc 522 + mc 842 + mc 1482 - 2*mc 522*mc 842 - 2*mc 522*mc 1482 - 2*mc 842*mc 1482 + 4*mc 522*mc 842*mc 1482) + 2 * KeccakfPermAir.extraction.inter_1509 c row := by
    simp only [KeccakfPermAir.extraction.inter_1511, KeccakfPermAir.extraction.inter_1510, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_1509 c row = (mc 523 + mc 843 + mc 1483 - 2*mc 523*mc 843 - 2*mc 523*mc 1483 - 2*mc 843*mc 1483 + 4*mc 523*mc 843*mc 1483) + 2 * KeccakfPermAir.extraction.inter_1507 c row := by
    simp only [KeccakfPermAir.extraction.inter_1509, KeccakfPermAir.extraction.inter_1508, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_1507 c row = (mc 524 + mc 844 + mc 1484 - 2*mc 524*mc 844 - 2*mc 524*mc 1484 - 2*mc 844*mc 1484 + 4*mc 524*mc 844*mc 1484) + 2 * KeccakfPermAir.extraction.inter_1505 c row := by
    simp only [KeccakfPermAir.extraction.inter_1507, KeccakfPermAir.extraction.inter_1506, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_1505 c row = (mc 525 + mc 845 + mc 1485 - 2*mc 525*mc 845 - 2*mc 525*mc 1485 - 2*mc 845*mc 1485 + 4*mc 525*mc 845*mc 1485) + 2 * KeccakfPermAir.extraction.inter_1503 c row := by
    simp only [KeccakfPermAir.extraction.inter_1505, KeccakfPermAir.extraction.inter_1504, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_1503 c row = (mc 526 + mc 846 + mc 1486 - 2*mc 526*mc 846 - 2*mc 526*mc 1486 - 2*mc 846*mc 1486 + 4*mc 526*mc 846*mc 1486) + 2 * KeccakfPermAir.extraction.inter_1501 c row := by
    simp only [KeccakfPermAir.extraction.inter_1503, KeccakfPermAir.extraction.inter_1502, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_1501 c row = (mc 527 + mc 847 + mc 1487 - 2*mc 527*mc 847 - 2*mc 527*mc 1487 - 2*mc 847*mc 1487 + 4*mc 527*mc 847*mc 1487) + 2 * KeccakfPermAir.extraction.inter_1499 c row := by
    simp only [KeccakfPermAir.extraction.inter_1501, KeccakfPermAir.extraction.inter_1500, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_1499 c row = (mc 528 + mc 848 + mc 1488 - 2*mc 528*mc 848 - 2*mc 528*mc 1488 - 2*mc 848*mc 1488 + 4*mc 528*mc 848*mc 1488) := by
    simp only [KeccakfPermAir.extraction.inter_1499, KeccakfPermAir.extraction.inter_1498, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1569 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 529 849 1489 164 row) :
    mc 164 = (mc 529 + mc 849 + mc 1489 - 2*mc 529*mc 849 - 2*mc 529*mc 1489 - 2*mc 849*mc 1489 + 4*mc 529*mc 849*mc 1489) + 2*(mc 530 + mc 850 + mc 1490 - 2*mc 530*mc 850 - 2*mc 530*mc 1490 - 2*mc 850*mc 1490 + 4*mc 530*mc 850*mc 1490) + 4*(mc 531 + mc 851 + mc 1491 - 2*mc 531*mc 851 - 2*mc 531*mc 1491 - 2*mc 851*mc 1491 + 4*mc 531*mc 851*mc 1491) + 8*(mc 532 + mc 852 + mc 1492 - 2*mc 532*mc 852 - 2*mc 532*mc 1492 - 2*mc 852*mc 1492 + 4*mc 532*mc 852*mc 1492) + 16*(mc 533 + mc 853 + mc 1493 - 2*mc 533*mc 853 - 2*mc 533*mc 1493 - 2*mc 853*mc 1493 + 4*mc 533*mc 853*mc 1493) + 32*(mc 534 + mc 854 + mc 1494 - 2*mc 534*mc 854 - 2*mc 534*mc 1494 - 2*mc 854*mc 1494 + 4*mc 534*mc 854*mc 1494) + 64*(mc 535 + mc 855 + mc 1495 - 2*mc 535*mc 855 - 2*mc 535*mc 1495 - 2*mc 855*mc 1495 + 4*mc 535*mc 855*mc 1495) + 128*(mc 536 + mc 856 + mc 1496 - 2*mc 536*mc 856 - 2*mc 536*mc 1496 - 2*mc 856*mc 1496 + 4*mc 536*mc 856*mc 1496) + 256*(mc 537 + mc 857 + mc 1497 - 2*mc 537*mc 857 - 2*mc 537*mc 1497 - 2*mc 857*mc 1497 + 4*mc 537*mc 857*mc 1497) + 512*(mc 538 + mc 858 + mc 1498 - 2*mc 538*mc 858 - 2*mc 538*mc 1498 - 2*mc 858*mc 1498 + 4*mc 538*mc 858*mc 1498) + 1024*(mc 539 + mc 859 + mc 1499 - 2*mc 539*mc 859 - 2*mc 539*mc 1499 - 2*mc 859*mc 1499 + 4*mc 539*mc 859*mc 1499) + 2048*(mc 540 + mc 860 + mc 1500 - 2*mc 540*mc 860 - 2*mc 540*mc 1500 - 2*mc 860*mc 1500 + 4*mc 540*mc 860*mc 1500) + 4096*(mc 541 + mc 861 + mc 1501 - 2*mc 541*mc 861 - 2*mc 541*mc 1501 - 2*mc 861*mc 1501 + 4*mc 541*mc 861*mc 1501) + 8192*(mc 542 + mc 862 + mc 1502 - 2*mc 542*mc 862 - 2*mc 542*mc 1502 - 2*mc 862*mc 1502 + 4*mc 542*mc 862*mc 1502) + 16384*(mc 543 + mc 863 + mc 1503 - 2*mc 543*mc 863 - 2*mc 543*mc 1503 - 2*mc 863*mc 1503 + 4*mc 543*mc 863*mc 1503) + 32768*(mc 544 + mc 864 + mc 1504 - 2*mc 544*mc 864 - 2*mc 544*mc 1504 - 2*mc 864*mc 1504 + 4*mc 544*mc 864*mc 1504) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1569, KeccakfPermAir.extraction.inter_1559, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_1558 c row = (mc 530 + mc 850 + mc 1490 - 2*mc 530*mc 850 - 2*mc 530*mc 1490 - 2*mc 850*mc 1490 + 4*mc 530*mc 850*mc 1490) + 2 * KeccakfPermAir.extraction.inter_1556 c row := by
    simp only [KeccakfPermAir.extraction.inter_1558, KeccakfPermAir.extraction.inter_1557, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_1556 c row = (mc 531 + mc 851 + mc 1491 - 2*mc 531*mc 851 - 2*mc 531*mc 1491 - 2*mc 851*mc 1491 + 4*mc 531*mc 851*mc 1491) + 2 * KeccakfPermAir.extraction.inter_1554 c row := by
    simp only [KeccakfPermAir.extraction.inter_1556, KeccakfPermAir.extraction.inter_1555, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_1554 c row = (mc 532 + mc 852 + mc 1492 - 2*mc 532*mc 852 - 2*mc 532*mc 1492 - 2*mc 852*mc 1492 + 4*mc 532*mc 852*mc 1492) + 2 * KeccakfPermAir.extraction.inter_1552 c row := by
    simp only [KeccakfPermAir.extraction.inter_1554, KeccakfPermAir.extraction.inter_1553, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_1552 c row = (mc 533 + mc 853 + mc 1493 - 2*mc 533*mc 853 - 2*mc 533*mc 1493 - 2*mc 853*mc 1493 + 4*mc 533*mc 853*mc 1493) + 2 * KeccakfPermAir.extraction.inter_1550 c row := by
    simp only [KeccakfPermAir.extraction.inter_1552, KeccakfPermAir.extraction.inter_1551, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_1550 c row = (mc 534 + mc 854 + mc 1494 - 2*mc 534*mc 854 - 2*mc 534*mc 1494 - 2*mc 854*mc 1494 + 4*mc 534*mc 854*mc 1494) + 2 * KeccakfPermAir.extraction.inter_1548 c row := by
    simp only [KeccakfPermAir.extraction.inter_1550, KeccakfPermAir.extraction.inter_1549, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_1548 c row = (mc 535 + mc 855 + mc 1495 - 2*mc 535*mc 855 - 2*mc 535*mc 1495 - 2*mc 855*mc 1495 + 4*mc 535*mc 855*mc 1495) + 2 * KeccakfPermAir.extraction.inter_1546 c row := by
    simp only [KeccakfPermAir.extraction.inter_1548, KeccakfPermAir.extraction.inter_1547, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_1546 c row = (mc 536 + mc 856 + mc 1496 - 2*mc 536*mc 856 - 2*mc 536*mc 1496 - 2*mc 856*mc 1496 + 4*mc 536*mc 856*mc 1496) + 2 * KeccakfPermAir.extraction.inter_1544 c row := by
    simp only [KeccakfPermAir.extraction.inter_1546, KeccakfPermAir.extraction.inter_1545, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_1544 c row = (mc 537 + mc 857 + mc 1497 - 2*mc 537*mc 857 - 2*mc 537*mc 1497 - 2*mc 857*mc 1497 + 4*mc 537*mc 857*mc 1497) + 2 * KeccakfPermAir.extraction.inter_1542 c row := by
    simp only [KeccakfPermAir.extraction.inter_1544, KeccakfPermAir.extraction.inter_1543, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_1542 c row = (mc 538 + mc 858 + mc 1498 - 2*mc 538*mc 858 - 2*mc 538*mc 1498 - 2*mc 858*mc 1498 + 4*mc 538*mc 858*mc 1498) + 2 * KeccakfPermAir.extraction.inter_1540 c row := by
    simp only [KeccakfPermAir.extraction.inter_1542, KeccakfPermAir.extraction.inter_1541, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_1540 c row = (mc 539 + mc 859 + mc 1499 - 2*mc 539*mc 859 - 2*mc 539*mc 1499 - 2*mc 859*mc 1499 + 4*mc 539*mc 859*mc 1499) + 2 * KeccakfPermAir.extraction.inter_1538 c row := by
    simp only [KeccakfPermAir.extraction.inter_1540, KeccakfPermAir.extraction.inter_1539, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_1538 c row = (mc 540 + mc 860 + mc 1500 - 2*mc 540*mc 860 - 2*mc 540*mc 1500 - 2*mc 860*mc 1500 + 4*mc 540*mc 860*mc 1500) + 2 * KeccakfPermAir.extraction.inter_1536 c row := by
    simp only [KeccakfPermAir.extraction.inter_1538, KeccakfPermAir.extraction.inter_1537, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_1536 c row = (mc 541 + mc 861 + mc 1501 - 2*mc 541*mc 861 - 2*mc 541*mc 1501 - 2*mc 861*mc 1501 + 4*mc 541*mc 861*mc 1501) + 2 * KeccakfPermAir.extraction.inter_1534 c row := by
    simp only [KeccakfPermAir.extraction.inter_1536, KeccakfPermAir.extraction.inter_1535, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_1534 c row = (mc 542 + mc 862 + mc 1502 - 2*mc 542*mc 862 - 2*mc 542*mc 1502 - 2*mc 862*mc 1502 + 4*mc 542*mc 862*mc 1502) + 2 * KeccakfPermAir.extraction.inter_1532 c row := by
    simp only [KeccakfPermAir.extraction.inter_1534, KeccakfPermAir.extraction.inter_1533, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_1532 c row = (mc 543 + mc 863 + mc 1503 - 2*mc 543*mc 863 - 2*mc 543*mc 1503 - 2*mc 863*mc 1503 + 4*mc 543*mc 863*mc 1503) + 2 * KeccakfPermAir.extraction.inter_1530 c row := by
    simp only [KeccakfPermAir.extraction.inter_1532, KeccakfPermAir.extraction.inter_1531, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_1530 c row = (mc 544 + mc 864 + mc 1504 - 2*mc 544*mc 864 - 2*mc 544*mc 1504 - 2*mc 864*mc 1504 + 4*mc 544*mc 864*mc 1504) := by
    simp only [KeccakfPermAir.extraction.inter_1530, KeccakfPermAir.extraction.inter_1529, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1634 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 225 545 1505 165 row) :
    mc 165 = (mc 225 + mc 545 + mc 1505 - 2*mc 225*mc 545 - 2*mc 225*mc 1505 - 2*mc 545*mc 1505 + 4*mc 225*mc 545*mc 1505) + 2*(mc 226 + mc 546 + mc 1506 - 2*mc 226*mc 546 - 2*mc 226*mc 1506 - 2*mc 546*mc 1506 + 4*mc 226*mc 546*mc 1506) + 4*(mc 227 + mc 547 + mc 1507 - 2*mc 227*mc 547 - 2*mc 227*mc 1507 - 2*mc 547*mc 1507 + 4*mc 227*mc 547*mc 1507) + 8*(mc 228 + mc 548 + mc 1508 - 2*mc 228*mc 548 - 2*mc 228*mc 1508 - 2*mc 548*mc 1508 + 4*mc 228*mc 548*mc 1508) + 16*(mc 229 + mc 549 + mc 1509 - 2*mc 229*mc 549 - 2*mc 229*mc 1509 - 2*mc 549*mc 1509 + 4*mc 229*mc 549*mc 1509) + 32*(mc 230 + mc 550 + mc 1510 - 2*mc 230*mc 550 - 2*mc 230*mc 1510 - 2*mc 550*mc 1510 + 4*mc 230*mc 550*mc 1510) + 64*(mc 231 + mc 551 + mc 1511 - 2*mc 231*mc 551 - 2*mc 231*mc 1511 - 2*mc 551*mc 1511 + 4*mc 231*mc 551*mc 1511) + 128*(mc 232 + mc 552 + mc 1512 - 2*mc 232*mc 552 - 2*mc 232*mc 1512 - 2*mc 552*mc 1512 + 4*mc 232*mc 552*mc 1512) + 256*(mc 233 + mc 553 + mc 1513 - 2*mc 233*mc 553 - 2*mc 233*mc 1513 - 2*mc 553*mc 1513 + 4*mc 233*mc 553*mc 1513) + 512*(mc 234 + mc 554 + mc 1514 - 2*mc 234*mc 554 - 2*mc 234*mc 1514 - 2*mc 554*mc 1514 + 4*mc 234*mc 554*mc 1514) + 1024*(mc 235 + mc 555 + mc 1515 - 2*mc 235*mc 555 - 2*mc 235*mc 1515 - 2*mc 555*mc 1515 + 4*mc 235*mc 555*mc 1515) + 2048*(mc 236 + mc 556 + mc 1516 - 2*mc 236*mc 556 - 2*mc 236*mc 1516 - 2*mc 556*mc 1516 + 4*mc 236*mc 556*mc 1516) + 4096*(mc 237 + mc 557 + mc 1517 - 2*mc 237*mc 557 - 2*mc 237*mc 1517 - 2*mc 557*mc 1517 + 4*mc 237*mc 557*mc 1517) + 8192*(mc 238 + mc 558 + mc 1518 - 2*mc 238*mc 558 - 2*mc 238*mc 1518 - 2*mc 558*mc 1518 + 4*mc 238*mc 558*mc 1518) + 16384*(mc 239 + mc 559 + mc 1519 - 2*mc 239*mc 559 - 2*mc 239*mc 1519 - 2*mc 559*mc 1519 + 4*mc 239*mc 559*mc 1519) + 32768*(mc 240 + mc 560 + mc 1520 - 2*mc 240*mc 560 - 2*mc 240*mc 1520 - 2*mc 560*mc 1520 + 4*mc 240*mc 560*mc 1520) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1634, KeccakfPermAir.extraction.inter_1590, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_1589 c row = (mc 226 + mc 546 + mc 1506 - 2*mc 226*mc 546 - 2*mc 226*mc 1506 - 2*mc 546*mc 1506 + 4*mc 226*mc 546*mc 1506) + 2 * KeccakfPermAir.extraction.inter_1587 c row := by
    simp only [KeccakfPermAir.extraction.inter_1589, KeccakfPermAir.extraction.inter_1588, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_1587 c row = (mc 227 + mc 547 + mc 1507 - 2*mc 227*mc 547 - 2*mc 227*mc 1507 - 2*mc 547*mc 1507 + 4*mc 227*mc 547*mc 1507) + 2 * KeccakfPermAir.extraction.inter_1585 c row := by
    simp only [KeccakfPermAir.extraction.inter_1587, KeccakfPermAir.extraction.inter_1586, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_1585 c row = (mc 228 + mc 548 + mc 1508 - 2*mc 228*mc 548 - 2*mc 228*mc 1508 - 2*mc 548*mc 1508 + 4*mc 228*mc 548*mc 1508) + 2 * KeccakfPermAir.extraction.inter_1583 c row := by
    simp only [KeccakfPermAir.extraction.inter_1585, KeccakfPermAir.extraction.inter_1584, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_1583 c row = (mc 229 + mc 549 + mc 1509 - 2*mc 229*mc 549 - 2*mc 229*mc 1509 - 2*mc 549*mc 1509 + 4*mc 229*mc 549*mc 1509) + 2 * KeccakfPermAir.extraction.inter_1581 c row := by
    simp only [KeccakfPermAir.extraction.inter_1583, KeccakfPermAir.extraction.inter_1582, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_1581 c row = (mc 230 + mc 550 + mc 1510 - 2*mc 230*mc 550 - 2*mc 230*mc 1510 - 2*mc 550*mc 1510 + 4*mc 230*mc 550*mc 1510) + 2 * KeccakfPermAir.extraction.inter_1579 c row := by
    simp only [KeccakfPermAir.extraction.inter_1581, KeccakfPermAir.extraction.inter_1580, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_1579 c row = (mc 231 + mc 551 + mc 1511 - 2*mc 231*mc 551 - 2*mc 231*mc 1511 - 2*mc 551*mc 1511 + 4*mc 231*mc 551*mc 1511) + 2 * KeccakfPermAir.extraction.inter_1577 c row := by
    simp only [KeccakfPermAir.extraction.inter_1579, KeccakfPermAir.extraction.inter_1578, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_1577 c row = (mc 232 + mc 552 + mc 1512 - 2*mc 232*mc 552 - 2*mc 232*mc 1512 - 2*mc 552*mc 1512 + 4*mc 232*mc 552*mc 1512) + 2 * KeccakfPermAir.extraction.inter_1575 c row := by
    simp only [KeccakfPermAir.extraction.inter_1577, KeccakfPermAir.extraction.inter_1576, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_1575 c row = (mc 233 + mc 553 + mc 1513 - 2*mc 233*mc 553 - 2*mc 233*mc 1513 - 2*mc 553*mc 1513 + 4*mc 233*mc 553*mc 1513) + 2 * KeccakfPermAir.extraction.inter_1573 c row := by
    simp only [KeccakfPermAir.extraction.inter_1575, KeccakfPermAir.extraction.inter_1574, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_1573 c row = (mc 234 + mc 554 + mc 1514 - 2*mc 234*mc 554 - 2*mc 234*mc 1514 - 2*mc 554*mc 1514 + 4*mc 234*mc 554*mc 1514) + 2 * KeccakfPermAir.extraction.inter_1571 c row := by
    simp only [KeccakfPermAir.extraction.inter_1573, KeccakfPermAir.extraction.inter_1572, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_1571 c row = (mc 235 + mc 555 + mc 1515 - 2*mc 235*mc 555 - 2*mc 235*mc 1515 - 2*mc 555*mc 1515 + 4*mc 235*mc 555*mc 1515) + 2 * KeccakfPermAir.extraction.inter_1569 c row := by
    simp only [KeccakfPermAir.extraction.inter_1571, KeccakfPermAir.extraction.inter_1570, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_1569 c row = (mc 236 + mc 556 + mc 1516 - 2*mc 236*mc 556 - 2*mc 236*mc 1516 - 2*mc 556*mc 1516 + 4*mc 236*mc 556*mc 1516) + 2 * KeccakfPermAir.extraction.inter_1567 c row := by
    simp only [KeccakfPermAir.extraction.inter_1569, KeccakfPermAir.extraction.inter_1568, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_1567 c row = (mc 237 + mc 557 + mc 1517 - 2*mc 237*mc 557 - 2*mc 237*mc 1517 - 2*mc 557*mc 1517 + 4*mc 237*mc 557*mc 1517) + 2 * KeccakfPermAir.extraction.inter_1565 c row := by
    simp only [KeccakfPermAir.extraction.inter_1567, KeccakfPermAir.extraction.inter_1566, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_1565 c row = (mc 238 + mc 558 + mc 1518 - 2*mc 238*mc 558 - 2*mc 238*mc 1518 - 2*mc 558*mc 1518 + 4*mc 238*mc 558*mc 1518) + 2 * KeccakfPermAir.extraction.inter_1563 c row := by
    simp only [KeccakfPermAir.extraction.inter_1565, KeccakfPermAir.extraction.inter_1564, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_1563 c row = (mc 239 + mc 559 + mc 1519 - 2*mc 239*mc 559 - 2*mc 239*mc 1519 - 2*mc 559*mc 1519 + 4*mc 239*mc 559*mc 1519) + 2 * KeccakfPermAir.extraction.inter_1561 c row := by
    simp only [KeccakfPermAir.extraction.inter_1563, KeccakfPermAir.extraction.inter_1562, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_1561 c row = (mc 240 + mc 560 + mc 1520 - 2*mc 240*mc 560 - 2*mc 240*mc 1520 - 2*mc 560*mc 1520 + 4*mc 240*mc 560*mc 1520) := by
    simp only [KeccakfPermAir.extraction.inter_1561, KeccakfPermAir.extraction.inter_1560, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1635 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 241 561 1521 166 row) :
    mc 166 = (mc 241 + mc 561 + mc 1521 - 2*mc 241*mc 561 - 2*mc 241*mc 1521 - 2*mc 561*mc 1521 + 4*mc 241*mc 561*mc 1521) + 2*(mc 242 + mc 562 + mc 1522 - 2*mc 242*mc 562 - 2*mc 242*mc 1522 - 2*mc 562*mc 1522 + 4*mc 242*mc 562*mc 1522) + 4*(mc 243 + mc 563 + mc 1523 - 2*mc 243*mc 563 - 2*mc 243*mc 1523 - 2*mc 563*mc 1523 + 4*mc 243*mc 563*mc 1523) + 8*(mc 244 + mc 564 + mc 1524 - 2*mc 244*mc 564 - 2*mc 244*mc 1524 - 2*mc 564*mc 1524 + 4*mc 244*mc 564*mc 1524) + 16*(mc 245 + mc 565 + mc 1525 - 2*mc 245*mc 565 - 2*mc 245*mc 1525 - 2*mc 565*mc 1525 + 4*mc 245*mc 565*mc 1525) + 32*(mc 246 + mc 566 + mc 1526 - 2*mc 246*mc 566 - 2*mc 246*mc 1526 - 2*mc 566*mc 1526 + 4*mc 246*mc 566*mc 1526) + 64*(mc 247 + mc 567 + mc 1527 - 2*mc 247*mc 567 - 2*mc 247*mc 1527 - 2*mc 567*mc 1527 + 4*mc 247*mc 567*mc 1527) + 128*(mc 248 + mc 568 + mc 1528 - 2*mc 248*mc 568 - 2*mc 248*mc 1528 - 2*mc 568*mc 1528 + 4*mc 248*mc 568*mc 1528) + 256*(mc 249 + mc 569 + mc 1529 - 2*mc 249*mc 569 - 2*mc 249*mc 1529 - 2*mc 569*mc 1529 + 4*mc 249*mc 569*mc 1529) + 512*(mc 250 + mc 570 + mc 1530 - 2*mc 250*mc 570 - 2*mc 250*mc 1530 - 2*mc 570*mc 1530 + 4*mc 250*mc 570*mc 1530) + 1024*(mc 251 + mc 571 + mc 1531 - 2*mc 251*mc 571 - 2*mc 251*mc 1531 - 2*mc 571*mc 1531 + 4*mc 251*mc 571*mc 1531) + 2048*(mc 252 + mc 572 + mc 1532 - 2*mc 252*mc 572 - 2*mc 252*mc 1532 - 2*mc 572*mc 1532 + 4*mc 252*mc 572*mc 1532) + 4096*(mc 253 + mc 573 + mc 1533 - 2*mc 253*mc 573 - 2*mc 253*mc 1533 - 2*mc 573*mc 1533 + 4*mc 253*mc 573*mc 1533) + 8192*(mc 254 + mc 574 + mc 1534 - 2*mc 254*mc 574 - 2*mc 254*mc 1534 - 2*mc 574*mc 1534 + 4*mc 254*mc 574*mc 1534) + 16384*(mc 255 + mc 575 + mc 1535 - 2*mc 255*mc 575 - 2*mc 255*mc 1535 - 2*mc 575*mc 1535 + 4*mc 255*mc 575*mc 1535) + 32768*(mc 256 + mc 576 + mc 1536 - 2*mc 256*mc 576 - 2*mc 256*mc 1536 - 2*mc 576*mc 1536 + 4*mc 256*mc 576*mc 1536) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1635, KeccakfPermAir.extraction.inter_1621, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_1620 c row = (mc 242 + mc 562 + mc 1522 - 2*mc 242*mc 562 - 2*mc 242*mc 1522 - 2*mc 562*mc 1522 + 4*mc 242*mc 562*mc 1522) + 2 * KeccakfPermAir.extraction.inter_1618 c row := by
    simp only [KeccakfPermAir.extraction.inter_1620, KeccakfPermAir.extraction.inter_1619, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_1618 c row = (mc 243 + mc 563 + mc 1523 - 2*mc 243*mc 563 - 2*mc 243*mc 1523 - 2*mc 563*mc 1523 + 4*mc 243*mc 563*mc 1523) + 2 * KeccakfPermAir.extraction.inter_1616 c row := by
    simp only [KeccakfPermAir.extraction.inter_1618, KeccakfPermAir.extraction.inter_1617, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_1616 c row = (mc 244 + mc 564 + mc 1524 - 2*mc 244*mc 564 - 2*mc 244*mc 1524 - 2*mc 564*mc 1524 + 4*mc 244*mc 564*mc 1524) + 2 * KeccakfPermAir.extraction.inter_1614 c row := by
    simp only [KeccakfPermAir.extraction.inter_1616, KeccakfPermAir.extraction.inter_1615, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_1614 c row = (mc 245 + mc 565 + mc 1525 - 2*mc 245*mc 565 - 2*mc 245*mc 1525 - 2*mc 565*mc 1525 + 4*mc 245*mc 565*mc 1525) + 2 * KeccakfPermAir.extraction.inter_1612 c row := by
    simp only [KeccakfPermAir.extraction.inter_1614, KeccakfPermAir.extraction.inter_1613, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_1612 c row = (mc 246 + mc 566 + mc 1526 - 2*mc 246*mc 566 - 2*mc 246*mc 1526 - 2*mc 566*mc 1526 + 4*mc 246*mc 566*mc 1526) + 2 * KeccakfPermAir.extraction.inter_1610 c row := by
    simp only [KeccakfPermAir.extraction.inter_1612, KeccakfPermAir.extraction.inter_1611, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_1610 c row = (mc 247 + mc 567 + mc 1527 - 2*mc 247*mc 567 - 2*mc 247*mc 1527 - 2*mc 567*mc 1527 + 4*mc 247*mc 567*mc 1527) + 2 * KeccakfPermAir.extraction.inter_1608 c row := by
    simp only [KeccakfPermAir.extraction.inter_1610, KeccakfPermAir.extraction.inter_1609, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_1608 c row = (mc 248 + mc 568 + mc 1528 - 2*mc 248*mc 568 - 2*mc 248*mc 1528 - 2*mc 568*mc 1528 + 4*mc 248*mc 568*mc 1528) + 2 * KeccakfPermAir.extraction.inter_1606 c row := by
    simp only [KeccakfPermAir.extraction.inter_1608, KeccakfPermAir.extraction.inter_1607, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_1606 c row = (mc 249 + mc 569 + mc 1529 - 2*mc 249*mc 569 - 2*mc 249*mc 1529 - 2*mc 569*mc 1529 + 4*mc 249*mc 569*mc 1529) + 2 * KeccakfPermAir.extraction.inter_1604 c row := by
    simp only [KeccakfPermAir.extraction.inter_1606, KeccakfPermAir.extraction.inter_1605, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_1604 c row = (mc 250 + mc 570 + mc 1530 - 2*mc 250*mc 570 - 2*mc 250*mc 1530 - 2*mc 570*mc 1530 + 4*mc 250*mc 570*mc 1530) + 2 * KeccakfPermAir.extraction.inter_1602 c row := by
    simp only [KeccakfPermAir.extraction.inter_1604, KeccakfPermAir.extraction.inter_1603, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_1602 c row = (mc 251 + mc 571 + mc 1531 - 2*mc 251*mc 571 - 2*mc 251*mc 1531 - 2*mc 571*mc 1531 + 4*mc 251*mc 571*mc 1531) + 2 * KeccakfPermAir.extraction.inter_1600 c row := by
    simp only [KeccakfPermAir.extraction.inter_1602, KeccakfPermAir.extraction.inter_1601, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_1600 c row = (mc 252 + mc 572 + mc 1532 - 2*mc 252*mc 572 - 2*mc 252*mc 1532 - 2*mc 572*mc 1532 + 4*mc 252*mc 572*mc 1532) + 2 * KeccakfPermAir.extraction.inter_1598 c row := by
    simp only [KeccakfPermAir.extraction.inter_1600, KeccakfPermAir.extraction.inter_1599, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_1598 c row = (mc 253 + mc 573 + mc 1533 - 2*mc 253*mc 573 - 2*mc 253*mc 1533 - 2*mc 573*mc 1533 + 4*mc 253*mc 573*mc 1533) + 2 * KeccakfPermAir.extraction.inter_1596 c row := by
    simp only [KeccakfPermAir.extraction.inter_1598, KeccakfPermAir.extraction.inter_1597, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_1596 c row = (mc 254 + mc 574 + mc 1534 - 2*mc 254*mc 574 - 2*mc 254*mc 1534 - 2*mc 574*mc 1534 + 4*mc 254*mc 574*mc 1534) + 2 * KeccakfPermAir.extraction.inter_1594 c row := by
    simp only [KeccakfPermAir.extraction.inter_1596, KeccakfPermAir.extraction.inter_1595, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_1594 c row = (mc 255 + mc 575 + mc 1535 - 2*mc 255*mc 575 - 2*mc 255*mc 1535 - 2*mc 575*mc 1535 + 4*mc 255*mc 575*mc 1535) + 2 * KeccakfPermAir.extraction.inter_1592 c row := by
    simp only [KeccakfPermAir.extraction.inter_1594, KeccakfPermAir.extraction.inter_1593, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_1592 c row = (mc 256 + mc 576 + mc 1536 - 2*mc 256*mc 576 - 2*mc 256*mc 1536 - 2*mc 576*mc 1536 + 4*mc 256*mc 576*mc 1536) := by
    simp only [KeccakfPermAir.extraction.inter_1592, KeccakfPermAir.extraction.inter_1591, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1636 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 257 577 1537 167 row) :
    mc 167 = (mc 257 + mc 577 + mc 1537 - 2*mc 257*mc 577 - 2*mc 257*mc 1537 - 2*mc 577*mc 1537 + 4*mc 257*mc 577*mc 1537) + 2*(mc 258 + mc 578 + mc 1538 - 2*mc 258*mc 578 - 2*mc 258*mc 1538 - 2*mc 578*mc 1538 + 4*mc 258*mc 578*mc 1538) + 4*(mc 259 + mc 579 + mc 1539 - 2*mc 259*mc 579 - 2*mc 259*mc 1539 - 2*mc 579*mc 1539 + 4*mc 259*mc 579*mc 1539) + 8*(mc 260 + mc 580 + mc 1540 - 2*mc 260*mc 580 - 2*mc 260*mc 1540 - 2*mc 580*mc 1540 + 4*mc 260*mc 580*mc 1540) + 16*(mc 261 + mc 581 + mc 1541 - 2*mc 261*mc 581 - 2*mc 261*mc 1541 - 2*mc 581*mc 1541 + 4*mc 261*mc 581*mc 1541) + 32*(mc 262 + mc 582 + mc 1542 - 2*mc 262*mc 582 - 2*mc 262*mc 1542 - 2*mc 582*mc 1542 + 4*mc 262*mc 582*mc 1542) + 64*(mc 263 + mc 583 + mc 1543 - 2*mc 263*mc 583 - 2*mc 263*mc 1543 - 2*mc 583*mc 1543 + 4*mc 263*mc 583*mc 1543) + 128*(mc 264 + mc 584 + mc 1544 - 2*mc 264*mc 584 - 2*mc 264*mc 1544 - 2*mc 584*mc 1544 + 4*mc 264*mc 584*mc 1544) + 256*(mc 265 + mc 585 + mc 1545 - 2*mc 265*mc 585 - 2*mc 265*mc 1545 - 2*mc 585*mc 1545 + 4*mc 265*mc 585*mc 1545) + 512*(mc 266 + mc 586 + mc 1546 - 2*mc 266*mc 586 - 2*mc 266*mc 1546 - 2*mc 586*mc 1546 + 4*mc 266*mc 586*mc 1546) + 1024*(mc 267 + mc 587 + mc 1547 - 2*mc 267*mc 587 - 2*mc 267*mc 1547 - 2*mc 587*mc 1547 + 4*mc 267*mc 587*mc 1547) + 2048*(mc 268 + mc 588 + mc 1548 - 2*mc 268*mc 588 - 2*mc 268*mc 1548 - 2*mc 588*mc 1548 + 4*mc 268*mc 588*mc 1548) + 4096*(mc 269 + mc 589 + mc 1549 - 2*mc 269*mc 589 - 2*mc 269*mc 1549 - 2*mc 589*mc 1549 + 4*mc 269*mc 589*mc 1549) + 8192*(mc 270 + mc 590 + mc 1550 - 2*mc 270*mc 590 - 2*mc 270*mc 1550 - 2*mc 590*mc 1550 + 4*mc 270*mc 590*mc 1550) + 16384*(mc 271 + mc 591 + mc 1551 - 2*mc 271*mc 591 - 2*mc 271*mc 1551 - 2*mc 591*mc 1551 + 4*mc 271*mc 591*mc 1551) + 32768*(mc 272 + mc 592 + mc 1552 - 2*mc 272*mc 592 - 2*mc 272*mc 1552 - 2*mc 592*mc 1552 + 4*mc 272*mc 592*mc 1552) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1636, KeccakfPermAir.extraction.inter_1652, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_1651 c row = (mc 258 + mc 578 + mc 1538 - 2*mc 258*mc 578 - 2*mc 258*mc 1538 - 2*mc 578*mc 1538 + 4*mc 258*mc 578*mc 1538) + 2 * KeccakfPermAir.extraction.inter_1649 c row := by
    simp only [KeccakfPermAir.extraction.inter_1651, KeccakfPermAir.extraction.inter_1650, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_1649 c row = (mc 259 + mc 579 + mc 1539 - 2*mc 259*mc 579 - 2*mc 259*mc 1539 - 2*mc 579*mc 1539 + 4*mc 259*mc 579*mc 1539) + 2 * KeccakfPermAir.extraction.inter_1647 c row := by
    simp only [KeccakfPermAir.extraction.inter_1649, KeccakfPermAir.extraction.inter_1648, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_1647 c row = (mc 260 + mc 580 + mc 1540 - 2*mc 260*mc 580 - 2*mc 260*mc 1540 - 2*mc 580*mc 1540 + 4*mc 260*mc 580*mc 1540) + 2 * KeccakfPermAir.extraction.inter_1645 c row := by
    simp only [KeccakfPermAir.extraction.inter_1647, KeccakfPermAir.extraction.inter_1646, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_1645 c row = (mc 261 + mc 581 + mc 1541 - 2*mc 261*mc 581 - 2*mc 261*mc 1541 - 2*mc 581*mc 1541 + 4*mc 261*mc 581*mc 1541) + 2 * KeccakfPermAir.extraction.inter_1643 c row := by
    simp only [KeccakfPermAir.extraction.inter_1645, KeccakfPermAir.extraction.inter_1644, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_1643 c row = (mc 262 + mc 582 + mc 1542 - 2*mc 262*mc 582 - 2*mc 262*mc 1542 - 2*mc 582*mc 1542 + 4*mc 262*mc 582*mc 1542) + 2 * KeccakfPermAir.extraction.inter_1641 c row := by
    simp only [KeccakfPermAir.extraction.inter_1643, KeccakfPermAir.extraction.inter_1642, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_1641 c row = (mc 263 + mc 583 + mc 1543 - 2*mc 263*mc 583 - 2*mc 263*mc 1543 - 2*mc 583*mc 1543 + 4*mc 263*mc 583*mc 1543) + 2 * KeccakfPermAir.extraction.inter_1639 c row := by
    simp only [KeccakfPermAir.extraction.inter_1641, KeccakfPermAir.extraction.inter_1640, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_1639 c row = (mc 264 + mc 584 + mc 1544 - 2*mc 264*mc 584 - 2*mc 264*mc 1544 - 2*mc 584*mc 1544 + 4*mc 264*mc 584*mc 1544) + 2 * KeccakfPermAir.extraction.inter_1637 c row := by
    simp only [KeccakfPermAir.extraction.inter_1639, KeccakfPermAir.extraction.inter_1638, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_1637 c row = (mc 265 + mc 585 + mc 1545 - 2*mc 265*mc 585 - 2*mc 265*mc 1545 - 2*mc 585*mc 1545 + 4*mc 265*mc 585*mc 1545) + 2 * KeccakfPermAir.extraction.inter_1635 c row := by
    simp only [KeccakfPermAir.extraction.inter_1637, KeccakfPermAir.extraction.inter_1636, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_1635 c row = (mc 266 + mc 586 + mc 1546 - 2*mc 266*mc 586 - 2*mc 266*mc 1546 - 2*mc 586*mc 1546 + 4*mc 266*mc 586*mc 1546) + 2 * KeccakfPermAir.extraction.inter_1633 c row := by
    simp only [KeccakfPermAir.extraction.inter_1635, KeccakfPermAir.extraction.inter_1634, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_1633 c row = (mc 267 + mc 587 + mc 1547 - 2*mc 267*mc 587 - 2*mc 267*mc 1547 - 2*mc 587*mc 1547 + 4*mc 267*mc 587*mc 1547) + 2 * KeccakfPermAir.extraction.inter_1631 c row := by
    simp only [KeccakfPermAir.extraction.inter_1633, KeccakfPermAir.extraction.inter_1632, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_1631 c row = (mc 268 + mc 588 + mc 1548 - 2*mc 268*mc 588 - 2*mc 268*mc 1548 - 2*mc 588*mc 1548 + 4*mc 268*mc 588*mc 1548) + 2 * KeccakfPermAir.extraction.inter_1629 c row := by
    simp only [KeccakfPermAir.extraction.inter_1631, KeccakfPermAir.extraction.inter_1630, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_1629 c row = (mc 269 + mc 589 + mc 1549 - 2*mc 269*mc 589 - 2*mc 269*mc 1549 - 2*mc 589*mc 1549 + 4*mc 269*mc 589*mc 1549) + 2 * KeccakfPermAir.extraction.inter_1627 c row := by
    simp only [KeccakfPermAir.extraction.inter_1629, KeccakfPermAir.extraction.inter_1628, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_1627 c row = (mc 270 + mc 590 + mc 1550 - 2*mc 270*mc 590 - 2*mc 270*mc 1550 - 2*mc 590*mc 1550 + 4*mc 270*mc 590*mc 1550) + 2 * KeccakfPermAir.extraction.inter_1625 c row := by
    simp only [KeccakfPermAir.extraction.inter_1627, KeccakfPermAir.extraction.inter_1626, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_1625 c row = (mc 271 + mc 591 + mc 1551 - 2*mc 271*mc 591 - 2*mc 271*mc 1551 - 2*mc 591*mc 1551 + 4*mc 271*mc 591*mc 1551) + 2 * KeccakfPermAir.extraction.inter_1623 c row := by
    simp only [KeccakfPermAir.extraction.inter_1625, KeccakfPermAir.extraction.inter_1624, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_1623 c row = (mc 272 + mc 592 + mc 1552 - 2*mc 272*mc 592 - 2*mc 272*mc 1552 - 2*mc 592*mc 1552 + 4*mc 272*mc 592*mc 1552) := by
    simp only [KeccakfPermAir.extraction.inter_1623, KeccakfPermAir.extraction.inter_1622, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1637 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 273 593 1553 168 row) :
    mc 168 = (mc 273 + mc 593 + mc 1553 - 2*mc 273*mc 593 - 2*mc 273*mc 1553 - 2*mc 593*mc 1553 + 4*mc 273*mc 593*mc 1553) + 2*(mc 274 + mc 594 + mc 1554 - 2*mc 274*mc 594 - 2*mc 274*mc 1554 - 2*mc 594*mc 1554 + 4*mc 274*mc 594*mc 1554) + 4*(mc 275 + mc 595 + mc 1555 - 2*mc 275*mc 595 - 2*mc 275*mc 1555 - 2*mc 595*mc 1555 + 4*mc 275*mc 595*mc 1555) + 8*(mc 276 + mc 596 + mc 1556 - 2*mc 276*mc 596 - 2*mc 276*mc 1556 - 2*mc 596*mc 1556 + 4*mc 276*mc 596*mc 1556) + 16*(mc 277 + mc 597 + mc 1557 - 2*mc 277*mc 597 - 2*mc 277*mc 1557 - 2*mc 597*mc 1557 + 4*mc 277*mc 597*mc 1557) + 32*(mc 278 + mc 598 + mc 1558 - 2*mc 278*mc 598 - 2*mc 278*mc 1558 - 2*mc 598*mc 1558 + 4*mc 278*mc 598*mc 1558) + 64*(mc 279 + mc 599 + mc 1559 - 2*mc 279*mc 599 - 2*mc 279*mc 1559 - 2*mc 599*mc 1559 + 4*mc 279*mc 599*mc 1559) + 128*(mc 280 + mc 600 + mc 1560 - 2*mc 280*mc 600 - 2*mc 280*mc 1560 - 2*mc 600*mc 1560 + 4*mc 280*mc 600*mc 1560) + 256*(mc 281 + mc 601 + mc 1561 - 2*mc 281*mc 601 - 2*mc 281*mc 1561 - 2*mc 601*mc 1561 + 4*mc 281*mc 601*mc 1561) + 512*(mc 282 + mc 602 + mc 1562 - 2*mc 282*mc 602 - 2*mc 282*mc 1562 - 2*mc 602*mc 1562 + 4*mc 282*mc 602*mc 1562) + 1024*(mc 283 + mc 603 + mc 1563 - 2*mc 283*mc 603 - 2*mc 283*mc 1563 - 2*mc 603*mc 1563 + 4*mc 283*mc 603*mc 1563) + 2048*(mc 284 + mc 604 + mc 1564 - 2*mc 284*mc 604 - 2*mc 284*mc 1564 - 2*mc 604*mc 1564 + 4*mc 284*mc 604*mc 1564) + 4096*(mc 285 + mc 605 + mc 1565 - 2*mc 285*mc 605 - 2*mc 285*mc 1565 - 2*mc 605*mc 1565 + 4*mc 285*mc 605*mc 1565) + 8192*(mc 286 + mc 606 + mc 1566 - 2*mc 286*mc 606 - 2*mc 286*mc 1566 - 2*mc 606*mc 1566 + 4*mc 286*mc 606*mc 1566) + 16384*(mc 287 + mc 607 + mc 1567 - 2*mc 287*mc 607 - 2*mc 287*mc 1567 - 2*mc 607*mc 1567 + 4*mc 287*mc 607*mc 1567) + 32768*(mc 288 + mc 608 + mc 1568 - 2*mc 288*mc 608 - 2*mc 288*mc 1568 - 2*mc 608*mc 1568 + 4*mc 288*mc 608*mc 1568) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1637, KeccakfPermAir.extraction.inter_1683, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_1682 c row = (mc 274 + mc 594 + mc 1554 - 2*mc 274*mc 594 - 2*mc 274*mc 1554 - 2*mc 594*mc 1554 + 4*mc 274*mc 594*mc 1554) + 2 * KeccakfPermAir.extraction.inter_1680 c row := by
    simp only [KeccakfPermAir.extraction.inter_1682, KeccakfPermAir.extraction.inter_1681, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_1680 c row = (mc 275 + mc 595 + mc 1555 - 2*mc 275*mc 595 - 2*mc 275*mc 1555 - 2*mc 595*mc 1555 + 4*mc 275*mc 595*mc 1555) + 2 * KeccakfPermAir.extraction.inter_1678 c row := by
    simp only [KeccakfPermAir.extraction.inter_1680, KeccakfPermAir.extraction.inter_1679, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_1678 c row = (mc 276 + mc 596 + mc 1556 - 2*mc 276*mc 596 - 2*mc 276*mc 1556 - 2*mc 596*mc 1556 + 4*mc 276*mc 596*mc 1556) + 2 * KeccakfPermAir.extraction.inter_1676 c row := by
    simp only [KeccakfPermAir.extraction.inter_1678, KeccakfPermAir.extraction.inter_1677, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_1676 c row = (mc 277 + mc 597 + mc 1557 - 2*mc 277*mc 597 - 2*mc 277*mc 1557 - 2*mc 597*mc 1557 + 4*mc 277*mc 597*mc 1557) + 2 * KeccakfPermAir.extraction.inter_1674 c row := by
    simp only [KeccakfPermAir.extraction.inter_1676, KeccakfPermAir.extraction.inter_1675, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_1674 c row = (mc 278 + mc 598 + mc 1558 - 2*mc 278*mc 598 - 2*mc 278*mc 1558 - 2*mc 598*mc 1558 + 4*mc 278*mc 598*mc 1558) + 2 * KeccakfPermAir.extraction.inter_1672 c row := by
    simp only [KeccakfPermAir.extraction.inter_1674, KeccakfPermAir.extraction.inter_1673, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_1672 c row = (mc 279 + mc 599 + mc 1559 - 2*mc 279*mc 599 - 2*mc 279*mc 1559 - 2*mc 599*mc 1559 + 4*mc 279*mc 599*mc 1559) + 2 * KeccakfPermAir.extraction.inter_1670 c row := by
    simp only [KeccakfPermAir.extraction.inter_1672, KeccakfPermAir.extraction.inter_1671, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_1670 c row = (mc 280 + mc 600 + mc 1560 - 2*mc 280*mc 600 - 2*mc 280*mc 1560 - 2*mc 600*mc 1560 + 4*mc 280*mc 600*mc 1560) + 2 * KeccakfPermAir.extraction.inter_1668 c row := by
    simp only [KeccakfPermAir.extraction.inter_1670, KeccakfPermAir.extraction.inter_1669, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_1668 c row = (mc 281 + mc 601 + mc 1561 - 2*mc 281*mc 601 - 2*mc 281*mc 1561 - 2*mc 601*mc 1561 + 4*mc 281*mc 601*mc 1561) + 2 * KeccakfPermAir.extraction.inter_1666 c row := by
    simp only [KeccakfPermAir.extraction.inter_1668, KeccakfPermAir.extraction.inter_1667, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_1666 c row = (mc 282 + mc 602 + mc 1562 - 2*mc 282*mc 602 - 2*mc 282*mc 1562 - 2*mc 602*mc 1562 + 4*mc 282*mc 602*mc 1562) + 2 * KeccakfPermAir.extraction.inter_1664 c row := by
    simp only [KeccakfPermAir.extraction.inter_1666, KeccakfPermAir.extraction.inter_1665, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_1664 c row = (mc 283 + mc 603 + mc 1563 - 2*mc 283*mc 603 - 2*mc 283*mc 1563 - 2*mc 603*mc 1563 + 4*mc 283*mc 603*mc 1563) + 2 * KeccakfPermAir.extraction.inter_1662 c row := by
    simp only [KeccakfPermAir.extraction.inter_1664, KeccakfPermAir.extraction.inter_1663, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_1662 c row = (mc 284 + mc 604 + mc 1564 - 2*mc 284*mc 604 - 2*mc 284*mc 1564 - 2*mc 604*mc 1564 + 4*mc 284*mc 604*mc 1564) + 2 * KeccakfPermAir.extraction.inter_1660 c row := by
    simp only [KeccakfPermAir.extraction.inter_1662, KeccakfPermAir.extraction.inter_1661, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_1660 c row = (mc 285 + mc 605 + mc 1565 - 2*mc 285*mc 605 - 2*mc 285*mc 1565 - 2*mc 605*mc 1565 + 4*mc 285*mc 605*mc 1565) + 2 * KeccakfPermAir.extraction.inter_1658 c row := by
    simp only [KeccakfPermAir.extraction.inter_1660, KeccakfPermAir.extraction.inter_1659, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_1658 c row = (mc 286 + mc 606 + mc 1566 - 2*mc 286*mc 606 - 2*mc 286*mc 1566 - 2*mc 606*mc 1566 + 4*mc 286*mc 606*mc 1566) + 2 * KeccakfPermAir.extraction.inter_1656 c row := by
    simp only [KeccakfPermAir.extraction.inter_1658, KeccakfPermAir.extraction.inter_1657, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_1656 c row = (mc 287 + mc 607 + mc 1567 - 2*mc 287*mc 607 - 2*mc 287*mc 1567 - 2*mc 607*mc 1567 + 4*mc 287*mc 607*mc 1567) + 2 * KeccakfPermAir.extraction.inter_1654 c row := by
    simp only [KeccakfPermAir.extraction.inter_1656, KeccakfPermAir.extraction.inter_1655, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_1654 c row = (mc 288 + mc 608 + mc 1568 - 2*mc 288*mc 608 - 2*mc 288*mc 1568 - 2*mc 608*mc 1568 + 4*mc 288*mc 608*mc 1568) := by
    simp only [KeccakfPermAir.extraction.inter_1654, KeccakfPermAir.extraction.inter_1653, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1702 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 289 609 1569 169 row) :
    mc 169 = (mc 289 + mc 609 + mc 1569 - 2*mc 289*mc 609 - 2*mc 289*mc 1569 - 2*mc 609*mc 1569 + 4*mc 289*mc 609*mc 1569) + 2*(mc 290 + mc 610 + mc 1570 - 2*mc 290*mc 610 - 2*mc 290*mc 1570 - 2*mc 610*mc 1570 + 4*mc 290*mc 610*mc 1570) + 4*(mc 291 + mc 611 + mc 1571 - 2*mc 291*mc 611 - 2*mc 291*mc 1571 - 2*mc 611*mc 1571 + 4*mc 291*mc 611*mc 1571) + 8*(mc 292 + mc 612 + mc 1572 - 2*mc 292*mc 612 - 2*mc 292*mc 1572 - 2*mc 612*mc 1572 + 4*mc 292*mc 612*mc 1572) + 16*(mc 293 + mc 613 + mc 1573 - 2*mc 293*mc 613 - 2*mc 293*mc 1573 - 2*mc 613*mc 1573 + 4*mc 293*mc 613*mc 1573) + 32*(mc 294 + mc 614 + mc 1574 - 2*mc 294*mc 614 - 2*mc 294*mc 1574 - 2*mc 614*mc 1574 + 4*mc 294*mc 614*mc 1574) + 64*(mc 295 + mc 615 + mc 1575 - 2*mc 295*mc 615 - 2*mc 295*mc 1575 - 2*mc 615*mc 1575 + 4*mc 295*mc 615*mc 1575) + 128*(mc 296 + mc 616 + mc 1576 - 2*mc 296*mc 616 - 2*mc 296*mc 1576 - 2*mc 616*mc 1576 + 4*mc 296*mc 616*mc 1576) + 256*(mc 297 + mc 617 + mc 1577 - 2*mc 297*mc 617 - 2*mc 297*mc 1577 - 2*mc 617*mc 1577 + 4*mc 297*mc 617*mc 1577) + 512*(mc 298 + mc 618 + mc 1578 - 2*mc 298*mc 618 - 2*mc 298*mc 1578 - 2*mc 618*mc 1578 + 4*mc 298*mc 618*mc 1578) + 1024*(mc 299 + mc 619 + mc 1579 - 2*mc 299*mc 619 - 2*mc 299*mc 1579 - 2*mc 619*mc 1579 + 4*mc 299*mc 619*mc 1579) + 2048*(mc 300 + mc 620 + mc 1580 - 2*mc 300*mc 620 - 2*mc 300*mc 1580 - 2*mc 620*mc 1580 + 4*mc 300*mc 620*mc 1580) + 4096*(mc 301 + mc 621 + mc 1581 - 2*mc 301*mc 621 - 2*mc 301*mc 1581 - 2*mc 621*mc 1581 + 4*mc 301*mc 621*mc 1581) + 8192*(mc 302 + mc 622 + mc 1582 - 2*mc 302*mc 622 - 2*mc 302*mc 1582 - 2*mc 622*mc 1582 + 4*mc 302*mc 622*mc 1582) + 16384*(mc 303 + mc 623 + mc 1583 - 2*mc 303*mc 623 - 2*mc 303*mc 1583 - 2*mc 623*mc 1583 + 4*mc 303*mc 623*mc 1583) + 32768*(mc 304 + mc 624 + mc 1584 - 2*mc 304*mc 624 - 2*mc 304*mc 1584 - 2*mc 624*mc 1584 + 4*mc 304*mc 624*mc 1584) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1702, KeccakfPermAir.extraction.inter_1714, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_1713 c row = (mc 290 + mc 610 + mc 1570 - 2*mc 290*mc 610 - 2*mc 290*mc 1570 - 2*mc 610*mc 1570 + 4*mc 290*mc 610*mc 1570) + 2 * KeccakfPermAir.extraction.inter_1711 c row := by
    simp only [KeccakfPermAir.extraction.inter_1713, KeccakfPermAir.extraction.inter_1712, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_1711 c row = (mc 291 + mc 611 + mc 1571 - 2*mc 291*mc 611 - 2*mc 291*mc 1571 - 2*mc 611*mc 1571 + 4*mc 291*mc 611*mc 1571) + 2 * KeccakfPermAir.extraction.inter_1709 c row := by
    simp only [KeccakfPermAir.extraction.inter_1711, KeccakfPermAir.extraction.inter_1710, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_1709 c row = (mc 292 + mc 612 + mc 1572 - 2*mc 292*mc 612 - 2*mc 292*mc 1572 - 2*mc 612*mc 1572 + 4*mc 292*mc 612*mc 1572) + 2 * KeccakfPermAir.extraction.inter_1707 c row := by
    simp only [KeccakfPermAir.extraction.inter_1709, KeccakfPermAir.extraction.inter_1708, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_1707 c row = (mc 293 + mc 613 + mc 1573 - 2*mc 293*mc 613 - 2*mc 293*mc 1573 - 2*mc 613*mc 1573 + 4*mc 293*mc 613*mc 1573) + 2 * KeccakfPermAir.extraction.inter_1705 c row := by
    simp only [KeccakfPermAir.extraction.inter_1707, KeccakfPermAir.extraction.inter_1706, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_1705 c row = (mc 294 + mc 614 + mc 1574 - 2*mc 294*mc 614 - 2*mc 294*mc 1574 - 2*mc 614*mc 1574 + 4*mc 294*mc 614*mc 1574) + 2 * KeccakfPermAir.extraction.inter_1703 c row := by
    simp only [KeccakfPermAir.extraction.inter_1705, KeccakfPermAir.extraction.inter_1704, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_1703 c row = (mc 295 + mc 615 + mc 1575 - 2*mc 295*mc 615 - 2*mc 295*mc 1575 - 2*mc 615*mc 1575 + 4*mc 295*mc 615*mc 1575) + 2 * KeccakfPermAir.extraction.inter_1701 c row := by
    simp only [KeccakfPermAir.extraction.inter_1703, KeccakfPermAir.extraction.inter_1702, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_1701 c row = (mc 296 + mc 616 + mc 1576 - 2*mc 296*mc 616 - 2*mc 296*mc 1576 - 2*mc 616*mc 1576 + 4*mc 296*mc 616*mc 1576) + 2 * KeccakfPermAir.extraction.inter_1699 c row := by
    simp only [KeccakfPermAir.extraction.inter_1701, KeccakfPermAir.extraction.inter_1700, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_1699 c row = (mc 297 + mc 617 + mc 1577 - 2*mc 297*mc 617 - 2*mc 297*mc 1577 - 2*mc 617*mc 1577 + 4*mc 297*mc 617*mc 1577) + 2 * KeccakfPermAir.extraction.inter_1697 c row := by
    simp only [KeccakfPermAir.extraction.inter_1699, KeccakfPermAir.extraction.inter_1698, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_1697 c row = (mc 298 + mc 618 + mc 1578 - 2*mc 298*mc 618 - 2*mc 298*mc 1578 - 2*mc 618*mc 1578 + 4*mc 298*mc 618*mc 1578) + 2 * KeccakfPermAir.extraction.inter_1695 c row := by
    simp only [KeccakfPermAir.extraction.inter_1697, KeccakfPermAir.extraction.inter_1696, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_1695 c row = (mc 299 + mc 619 + mc 1579 - 2*mc 299*mc 619 - 2*mc 299*mc 1579 - 2*mc 619*mc 1579 + 4*mc 299*mc 619*mc 1579) + 2 * KeccakfPermAir.extraction.inter_1693 c row := by
    simp only [KeccakfPermAir.extraction.inter_1695, KeccakfPermAir.extraction.inter_1694, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_1693 c row = (mc 300 + mc 620 + mc 1580 - 2*mc 300*mc 620 - 2*mc 300*mc 1580 - 2*mc 620*mc 1580 + 4*mc 300*mc 620*mc 1580) + 2 * KeccakfPermAir.extraction.inter_1691 c row := by
    simp only [KeccakfPermAir.extraction.inter_1693, KeccakfPermAir.extraction.inter_1692, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_1691 c row = (mc 301 + mc 621 + mc 1581 - 2*mc 301*mc 621 - 2*mc 301*mc 1581 - 2*mc 621*mc 1581 + 4*mc 301*mc 621*mc 1581) + 2 * KeccakfPermAir.extraction.inter_1689 c row := by
    simp only [KeccakfPermAir.extraction.inter_1691, KeccakfPermAir.extraction.inter_1690, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_1689 c row = (mc 302 + mc 622 + mc 1582 - 2*mc 302*mc 622 - 2*mc 302*mc 1582 - 2*mc 622*mc 1582 + 4*mc 302*mc 622*mc 1582) + 2 * KeccakfPermAir.extraction.inter_1687 c row := by
    simp only [KeccakfPermAir.extraction.inter_1689, KeccakfPermAir.extraction.inter_1688, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_1687 c row = (mc 303 + mc 623 + mc 1583 - 2*mc 303*mc 623 - 2*mc 303*mc 1583 - 2*mc 623*mc 1583 + 4*mc 303*mc 623*mc 1583) + 2 * KeccakfPermAir.extraction.inter_1685 c row := by
    simp only [KeccakfPermAir.extraction.inter_1687, KeccakfPermAir.extraction.inter_1686, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_1685 c row = (mc 304 + mc 624 + mc 1584 - 2*mc 304*mc 624 - 2*mc 304*mc 1584 - 2*mc 624*mc 1584 + 4*mc 304*mc 624*mc 1584) := by
    simp only [KeccakfPermAir.extraction.inter_1685, KeccakfPermAir.extraction.inter_1684, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1703 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 305 625 1585 170 row) :
    mc 170 = (mc 305 + mc 625 + mc 1585 - 2*mc 305*mc 625 - 2*mc 305*mc 1585 - 2*mc 625*mc 1585 + 4*mc 305*mc 625*mc 1585) + 2*(mc 306 + mc 626 + mc 1586 - 2*mc 306*mc 626 - 2*mc 306*mc 1586 - 2*mc 626*mc 1586 + 4*mc 306*mc 626*mc 1586) + 4*(mc 307 + mc 627 + mc 1587 - 2*mc 307*mc 627 - 2*mc 307*mc 1587 - 2*mc 627*mc 1587 + 4*mc 307*mc 627*mc 1587) + 8*(mc 308 + mc 628 + mc 1588 - 2*mc 308*mc 628 - 2*mc 308*mc 1588 - 2*mc 628*mc 1588 + 4*mc 308*mc 628*mc 1588) + 16*(mc 309 + mc 629 + mc 1589 - 2*mc 309*mc 629 - 2*mc 309*mc 1589 - 2*mc 629*mc 1589 + 4*mc 309*mc 629*mc 1589) + 32*(mc 310 + mc 630 + mc 1590 - 2*mc 310*mc 630 - 2*mc 310*mc 1590 - 2*mc 630*mc 1590 + 4*mc 310*mc 630*mc 1590) + 64*(mc 311 + mc 631 + mc 1591 - 2*mc 311*mc 631 - 2*mc 311*mc 1591 - 2*mc 631*mc 1591 + 4*mc 311*mc 631*mc 1591) + 128*(mc 312 + mc 632 + mc 1592 - 2*mc 312*mc 632 - 2*mc 312*mc 1592 - 2*mc 632*mc 1592 + 4*mc 312*mc 632*mc 1592) + 256*(mc 313 + mc 633 + mc 1593 - 2*mc 313*mc 633 - 2*mc 313*mc 1593 - 2*mc 633*mc 1593 + 4*mc 313*mc 633*mc 1593) + 512*(mc 314 + mc 634 + mc 1594 - 2*mc 314*mc 634 - 2*mc 314*mc 1594 - 2*mc 634*mc 1594 + 4*mc 314*mc 634*mc 1594) + 1024*(mc 315 + mc 635 + mc 1595 - 2*mc 315*mc 635 - 2*mc 315*mc 1595 - 2*mc 635*mc 1595 + 4*mc 315*mc 635*mc 1595) + 2048*(mc 316 + mc 636 + mc 1596 - 2*mc 316*mc 636 - 2*mc 316*mc 1596 - 2*mc 636*mc 1596 + 4*mc 316*mc 636*mc 1596) + 4096*(mc 317 + mc 637 + mc 1597 - 2*mc 317*mc 637 - 2*mc 317*mc 1597 - 2*mc 637*mc 1597 + 4*mc 317*mc 637*mc 1597) + 8192*(mc 318 + mc 638 + mc 1598 - 2*mc 318*mc 638 - 2*mc 318*mc 1598 - 2*mc 638*mc 1598 + 4*mc 318*mc 638*mc 1598) + 16384*(mc 319 + mc 639 + mc 1599 - 2*mc 319*mc 639 - 2*mc 319*mc 1599 - 2*mc 639*mc 1599 + 4*mc 319*mc 639*mc 1599) + 32768*(mc 320 + mc 640 + mc 1600 - 2*mc 320*mc 640 - 2*mc 320*mc 1600 - 2*mc 640*mc 1600 + 4*mc 320*mc 640*mc 1600) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1703, KeccakfPermAir.extraction.inter_1745, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_1744 c row = (mc 306 + mc 626 + mc 1586 - 2*mc 306*mc 626 - 2*mc 306*mc 1586 - 2*mc 626*mc 1586 + 4*mc 306*mc 626*mc 1586) + 2 * KeccakfPermAir.extraction.inter_1742 c row := by
    simp only [KeccakfPermAir.extraction.inter_1744, KeccakfPermAir.extraction.inter_1743, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_1742 c row = (mc 307 + mc 627 + mc 1587 - 2*mc 307*mc 627 - 2*mc 307*mc 1587 - 2*mc 627*mc 1587 + 4*mc 307*mc 627*mc 1587) + 2 * KeccakfPermAir.extraction.inter_1740 c row := by
    simp only [KeccakfPermAir.extraction.inter_1742, KeccakfPermAir.extraction.inter_1741, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_1740 c row = (mc 308 + mc 628 + mc 1588 - 2*mc 308*mc 628 - 2*mc 308*mc 1588 - 2*mc 628*mc 1588 + 4*mc 308*mc 628*mc 1588) + 2 * KeccakfPermAir.extraction.inter_1738 c row := by
    simp only [KeccakfPermAir.extraction.inter_1740, KeccakfPermAir.extraction.inter_1739, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_1738 c row = (mc 309 + mc 629 + mc 1589 - 2*mc 309*mc 629 - 2*mc 309*mc 1589 - 2*mc 629*mc 1589 + 4*mc 309*mc 629*mc 1589) + 2 * KeccakfPermAir.extraction.inter_1736 c row := by
    simp only [KeccakfPermAir.extraction.inter_1738, KeccakfPermAir.extraction.inter_1737, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_1736 c row = (mc 310 + mc 630 + mc 1590 - 2*mc 310*mc 630 - 2*mc 310*mc 1590 - 2*mc 630*mc 1590 + 4*mc 310*mc 630*mc 1590) + 2 * KeccakfPermAir.extraction.inter_1734 c row := by
    simp only [KeccakfPermAir.extraction.inter_1736, KeccakfPermAir.extraction.inter_1735, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_1734 c row = (mc 311 + mc 631 + mc 1591 - 2*mc 311*mc 631 - 2*mc 311*mc 1591 - 2*mc 631*mc 1591 + 4*mc 311*mc 631*mc 1591) + 2 * KeccakfPermAir.extraction.inter_1732 c row := by
    simp only [KeccakfPermAir.extraction.inter_1734, KeccakfPermAir.extraction.inter_1733, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_1732 c row = (mc 312 + mc 632 + mc 1592 - 2*mc 312*mc 632 - 2*mc 312*mc 1592 - 2*mc 632*mc 1592 + 4*mc 312*mc 632*mc 1592) + 2 * KeccakfPermAir.extraction.inter_1730 c row := by
    simp only [KeccakfPermAir.extraction.inter_1732, KeccakfPermAir.extraction.inter_1731, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_1730 c row = (mc 313 + mc 633 + mc 1593 - 2*mc 313*mc 633 - 2*mc 313*mc 1593 - 2*mc 633*mc 1593 + 4*mc 313*mc 633*mc 1593) + 2 * KeccakfPermAir.extraction.inter_1728 c row := by
    simp only [KeccakfPermAir.extraction.inter_1730, KeccakfPermAir.extraction.inter_1729, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_1728 c row = (mc 314 + mc 634 + mc 1594 - 2*mc 314*mc 634 - 2*mc 314*mc 1594 - 2*mc 634*mc 1594 + 4*mc 314*mc 634*mc 1594) + 2 * KeccakfPermAir.extraction.inter_1726 c row := by
    simp only [KeccakfPermAir.extraction.inter_1728, KeccakfPermAir.extraction.inter_1727, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_1726 c row = (mc 315 + mc 635 + mc 1595 - 2*mc 315*mc 635 - 2*mc 315*mc 1595 - 2*mc 635*mc 1595 + 4*mc 315*mc 635*mc 1595) + 2 * KeccakfPermAir.extraction.inter_1724 c row := by
    simp only [KeccakfPermAir.extraction.inter_1726, KeccakfPermAir.extraction.inter_1725, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_1724 c row = (mc 316 + mc 636 + mc 1596 - 2*mc 316*mc 636 - 2*mc 316*mc 1596 - 2*mc 636*mc 1596 + 4*mc 316*mc 636*mc 1596) + 2 * KeccakfPermAir.extraction.inter_1722 c row := by
    simp only [KeccakfPermAir.extraction.inter_1724, KeccakfPermAir.extraction.inter_1723, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_1722 c row = (mc 317 + mc 637 + mc 1597 - 2*mc 317*mc 637 - 2*mc 317*mc 1597 - 2*mc 637*mc 1597 + 4*mc 317*mc 637*mc 1597) + 2 * KeccakfPermAir.extraction.inter_1720 c row := by
    simp only [KeccakfPermAir.extraction.inter_1722, KeccakfPermAir.extraction.inter_1721, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_1720 c row = (mc 318 + mc 638 + mc 1598 - 2*mc 318*mc 638 - 2*mc 318*mc 1598 - 2*mc 638*mc 1598 + 4*mc 318*mc 638*mc 1598) + 2 * KeccakfPermAir.extraction.inter_1718 c row := by
    simp only [KeccakfPermAir.extraction.inter_1720, KeccakfPermAir.extraction.inter_1719, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_1718 c row = (mc 319 + mc 639 + mc 1599 - 2*mc 319*mc 639 - 2*mc 319*mc 1599 - 2*mc 639*mc 1599 + 4*mc 319*mc 639*mc 1599) + 2 * KeccakfPermAir.extraction.inter_1716 c row := by
    simp only [KeccakfPermAir.extraction.inter_1718, KeccakfPermAir.extraction.inter_1717, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_1716 c row = (mc 320 + mc 640 + mc 1600 - 2*mc 320*mc 640 - 2*mc 320*mc 1600 - 2*mc 640*mc 1600 + 4*mc 320*mc 640*mc 1600) := by
    simp only [KeccakfPermAir.extraction.inter_1716, KeccakfPermAir.extraction.inter_1715, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1704 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 321 641 1601 171 row) :
    mc 171 = (mc 321 + mc 641 + mc 1601 - 2*mc 321*mc 641 - 2*mc 321*mc 1601 - 2*mc 641*mc 1601 + 4*mc 321*mc 641*mc 1601) + 2*(mc 322 + mc 642 + mc 1602 - 2*mc 322*mc 642 - 2*mc 322*mc 1602 - 2*mc 642*mc 1602 + 4*mc 322*mc 642*mc 1602) + 4*(mc 323 + mc 643 + mc 1603 - 2*mc 323*mc 643 - 2*mc 323*mc 1603 - 2*mc 643*mc 1603 + 4*mc 323*mc 643*mc 1603) + 8*(mc 324 + mc 644 + mc 1604 - 2*mc 324*mc 644 - 2*mc 324*mc 1604 - 2*mc 644*mc 1604 + 4*mc 324*mc 644*mc 1604) + 16*(mc 325 + mc 645 + mc 1605 - 2*mc 325*mc 645 - 2*mc 325*mc 1605 - 2*mc 645*mc 1605 + 4*mc 325*mc 645*mc 1605) + 32*(mc 326 + mc 646 + mc 1606 - 2*mc 326*mc 646 - 2*mc 326*mc 1606 - 2*mc 646*mc 1606 + 4*mc 326*mc 646*mc 1606) + 64*(mc 327 + mc 647 + mc 1607 - 2*mc 327*mc 647 - 2*mc 327*mc 1607 - 2*mc 647*mc 1607 + 4*mc 327*mc 647*mc 1607) + 128*(mc 328 + mc 648 + mc 1608 - 2*mc 328*mc 648 - 2*mc 328*mc 1608 - 2*mc 648*mc 1608 + 4*mc 328*mc 648*mc 1608) + 256*(mc 329 + mc 649 + mc 1609 - 2*mc 329*mc 649 - 2*mc 329*mc 1609 - 2*mc 649*mc 1609 + 4*mc 329*mc 649*mc 1609) + 512*(mc 330 + mc 650 + mc 1610 - 2*mc 330*mc 650 - 2*mc 330*mc 1610 - 2*mc 650*mc 1610 + 4*mc 330*mc 650*mc 1610) + 1024*(mc 331 + mc 651 + mc 1611 - 2*mc 331*mc 651 - 2*mc 331*mc 1611 - 2*mc 651*mc 1611 + 4*mc 331*mc 651*mc 1611) + 2048*(mc 332 + mc 652 + mc 1612 - 2*mc 332*mc 652 - 2*mc 332*mc 1612 - 2*mc 652*mc 1612 + 4*mc 332*mc 652*mc 1612) + 4096*(mc 333 + mc 653 + mc 1613 - 2*mc 333*mc 653 - 2*mc 333*mc 1613 - 2*mc 653*mc 1613 + 4*mc 333*mc 653*mc 1613) + 8192*(mc 334 + mc 654 + mc 1614 - 2*mc 334*mc 654 - 2*mc 334*mc 1614 - 2*mc 654*mc 1614 + 4*mc 334*mc 654*mc 1614) + 16384*(mc 335 + mc 655 + mc 1615 - 2*mc 335*mc 655 - 2*mc 335*mc 1615 - 2*mc 655*mc 1615 + 4*mc 335*mc 655*mc 1615) + 32768*(mc 336 + mc 656 + mc 1616 - 2*mc 336*mc 656 - 2*mc 336*mc 1616 - 2*mc 656*mc 1616 + 4*mc 336*mc 656*mc 1616) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1704, KeccakfPermAir.extraction.inter_1776, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_1775 c row = (mc 322 + mc 642 + mc 1602 - 2*mc 322*mc 642 - 2*mc 322*mc 1602 - 2*mc 642*mc 1602 + 4*mc 322*mc 642*mc 1602) + 2 * KeccakfPermAir.extraction.inter_1773 c row := by
    simp only [KeccakfPermAir.extraction.inter_1775, KeccakfPermAir.extraction.inter_1774, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_1773 c row = (mc 323 + mc 643 + mc 1603 - 2*mc 323*mc 643 - 2*mc 323*mc 1603 - 2*mc 643*mc 1603 + 4*mc 323*mc 643*mc 1603) + 2 * KeccakfPermAir.extraction.inter_1771 c row := by
    simp only [KeccakfPermAir.extraction.inter_1773, KeccakfPermAir.extraction.inter_1772, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_1771 c row = (mc 324 + mc 644 + mc 1604 - 2*mc 324*mc 644 - 2*mc 324*mc 1604 - 2*mc 644*mc 1604 + 4*mc 324*mc 644*mc 1604) + 2 * KeccakfPermAir.extraction.inter_1769 c row := by
    simp only [KeccakfPermAir.extraction.inter_1771, KeccakfPermAir.extraction.inter_1770, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_1769 c row = (mc 325 + mc 645 + mc 1605 - 2*mc 325*mc 645 - 2*mc 325*mc 1605 - 2*mc 645*mc 1605 + 4*mc 325*mc 645*mc 1605) + 2 * KeccakfPermAir.extraction.inter_1767 c row := by
    simp only [KeccakfPermAir.extraction.inter_1769, KeccakfPermAir.extraction.inter_1768, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_1767 c row = (mc 326 + mc 646 + mc 1606 - 2*mc 326*mc 646 - 2*mc 326*mc 1606 - 2*mc 646*mc 1606 + 4*mc 326*mc 646*mc 1606) + 2 * KeccakfPermAir.extraction.inter_1765 c row := by
    simp only [KeccakfPermAir.extraction.inter_1767, KeccakfPermAir.extraction.inter_1766, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_1765 c row = (mc 327 + mc 647 + mc 1607 - 2*mc 327*mc 647 - 2*mc 327*mc 1607 - 2*mc 647*mc 1607 + 4*mc 327*mc 647*mc 1607) + 2 * KeccakfPermAir.extraction.inter_1763 c row := by
    simp only [KeccakfPermAir.extraction.inter_1765, KeccakfPermAir.extraction.inter_1764, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_1763 c row = (mc 328 + mc 648 + mc 1608 - 2*mc 328*mc 648 - 2*mc 328*mc 1608 - 2*mc 648*mc 1608 + 4*mc 328*mc 648*mc 1608) + 2 * KeccakfPermAir.extraction.inter_1761 c row := by
    simp only [KeccakfPermAir.extraction.inter_1763, KeccakfPermAir.extraction.inter_1762, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_1761 c row = (mc 329 + mc 649 + mc 1609 - 2*mc 329*mc 649 - 2*mc 329*mc 1609 - 2*mc 649*mc 1609 + 4*mc 329*mc 649*mc 1609) + 2 * KeccakfPermAir.extraction.inter_1759 c row := by
    simp only [KeccakfPermAir.extraction.inter_1761, KeccakfPermAir.extraction.inter_1760, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_1759 c row = (mc 330 + mc 650 + mc 1610 - 2*mc 330*mc 650 - 2*mc 330*mc 1610 - 2*mc 650*mc 1610 + 4*mc 330*mc 650*mc 1610) + 2 * KeccakfPermAir.extraction.inter_1757 c row := by
    simp only [KeccakfPermAir.extraction.inter_1759, KeccakfPermAir.extraction.inter_1758, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_1757 c row = (mc 331 + mc 651 + mc 1611 - 2*mc 331*mc 651 - 2*mc 331*mc 1611 - 2*mc 651*mc 1611 + 4*mc 331*mc 651*mc 1611) + 2 * KeccakfPermAir.extraction.inter_1755 c row := by
    simp only [KeccakfPermAir.extraction.inter_1757, KeccakfPermAir.extraction.inter_1756, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_1755 c row = (mc 332 + mc 652 + mc 1612 - 2*mc 332*mc 652 - 2*mc 332*mc 1612 - 2*mc 652*mc 1612 + 4*mc 332*mc 652*mc 1612) + 2 * KeccakfPermAir.extraction.inter_1753 c row := by
    simp only [KeccakfPermAir.extraction.inter_1755, KeccakfPermAir.extraction.inter_1754, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_1753 c row = (mc 333 + mc 653 + mc 1613 - 2*mc 333*mc 653 - 2*mc 333*mc 1613 - 2*mc 653*mc 1613 + 4*mc 333*mc 653*mc 1613) + 2 * KeccakfPermAir.extraction.inter_1751 c row := by
    simp only [KeccakfPermAir.extraction.inter_1753, KeccakfPermAir.extraction.inter_1752, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_1751 c row = (mc 334 + mc 654 + mc 1614 - 2*mc 334*mc 654 - 2*mc 334*mc 1614 - 2*mc 654*mc 1614 + 4*mc 334*mc 654*mc 1614) + 2 * KeccakfPermAir.extraction.inter_1749 c row := by
    simp only [KeccakfPermAir.extraction.inter_1751, KeccakfPermAir.extraction.inter_1750, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_1749 c row = (mc 335 + mc 655 + mc 1615 - 2*mc 335*mc 655 - 2*mc 335*mc 1615 - 2*mc 655*mc 1615 + 4*mc 335*mc 655*mc 1615) + 2 * KeccakfPermAir.extraction.inter_1747 c row := by
    simp only [KeccakfPermAir.extraction.inter_1749, KeccakfPermAir.extraction.inter_1748, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_1747 c row = (mc 336 + mc 656 + mc 1616 - 2*mc 336*mc 656 - 2*mc 336*mc 1616 - 2*mc 656*mc 1616 + 4*mc 336*mc 656*mc 1616) := by
    simp only [KeccakfPermAir.extraction.inter_1747, KeccakfPermAir.extraction.inter_1746, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1705 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 337 657 1617 172 row) :
    mc 172 = (mc 337 + mc 657 + mc 1617 - 2*mc 337*mc 657 - 2*mc 337*mc 1617 - 2*mc 657*mc 1617 + 4*mc 337*mc 657*mc 1617) + 2*(mc 338 + mc 658 + mc 1618 - 2*mc 338*mc 658 - 2*mc 338*mc 1618 - 2*mc 658*mc 1618 + 4*mc 338*mc 658*mc 1618) + 4*(mc 339 + mc 659 + mc 1619 - 2*mc 339*mc 659 - 2*mc 339*mc 1619 - 2*mc 659*mc 1619 + 4*mc 339*mc 659*mc 1619) + 8*(mc 340 + mc 660 + mc 1620 - 2*mc 340*mc 660 - 2*mc 340*mc 1620 - 2*mc 660*mc 1620 + 4*mc 340*mc 660*mc 1620) + 16*(mc 341 + mc 661 + mc 1621 - 2*mc 341*mc 661 - 2*mc 341*mc 1621 - 2*mc 661*mc 1621 + 4*mc 341*mc 661*mc 1621) + 32*(mc 342 + mc 662 + mc 1622 - 2*mc 342*mc 662 - 2*mc 342*mc 1622 - 2*mc 662*mc 1622 + 4*mc 342*mc 662*mc 1622) + 64*(mc 343 + mc 663 + mc 1623 - 2*mc 343*mc 663 - 2*mc 343*mc 1623 - 2*mc 663*mc 1623 + 4*mc 343*mc 663*mc 1623) + 128*(mc 344 + mc 664 + mc 1624 - 2*mc 344*mc 664 - 2*mc 344*mc 1624 - 2*mc 664*mc 1624 + 4*mc 344*mc 664*mc 1624) + 256*(mc 345 + mc 665 + mc 1625 - 2*mc 345*mc 665 - 2*mc 345*mc 1625 - 2*mc 665*mc 1625 + 4*mc 345*mc 665*mc 1625) + 512*(mc 346 + mc 666 + mc 1626 - 2*mc 346*mc 666 - 2*mc 346*mc 1626 - 2*mc 666*mc 1626 + 4*mc 346*mc 666*mc 1626) + 1024*(mc 347 + mc 667 + mc 1627 - 2*mc 347*mc 667 - 2*mc 347*mc 1627 - 2*mc 667*mc 1627 + 4*mc 347*mc 667*mc 1627) + 2048*(mc 348 + mc 668 + mc 1628 - 2*mc 348*mc 668 - 2*mc 348*mc 1628 - 2*mc 668*mc 1628 + 4*mc 348*mc 668*mc 1628) + 4096*(mc 349 + mc 669 + mc 1629 - 2*mc 349*mc 669 - 2*mc 349*mc 1629 - 2*mc 669*mc 1629 + 4*mc 349*mc 669*mc 1629) + 8192*(mc 350 + mc 670 + mc 1630 - 2*mc 350*mc 670 - 2*mc 350*mc 1630 - 2*mc 670*mc 1630 + 4*mc 350*mc 670*mc 1630) + 16384*(mc 351 + mc 671 + mc 1631 - 2*mc 351*mc 671 - 2*mc 351*mc 1631 - 2*mc 671*mc 1631 + 4*mc 351*mc 671*mc 1631) + 32768*(mc 352 + mc 672 + mc 1632 - 2*mc 352*mc 672 - 2*mc 352*mc 1632 - 2*mc 672*mc 1632 + 4*mc 352*mc 672*mc 1632) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1705, KeccakfPermAir.extraction.inter_1807, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_1806 c row = (mc 338 + mc 658 + mc 1618 - 2*mc 338*mc 658 - 2*mc 338*mc 1618 - 2*mc 658*mc 1618 + 4*mc 338*mc 658*mc 1618) + 2 * KeccakfPermAir.extraction.inter_1804 c row := by
    simp only [KeccakfPermAir.extraction.inter_1806, KeccakfPermAir.extraction.inter_1805, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_1804 c row = (mc 339 + mc 659 + mc 1619 - 2*mc 339*mc 659 - 2*mc 339*mc 1619 - 2*mc 659*mc 1619 + 4*mc 339*mc 659*mc 1619) + 2 * KeccakfPermAir.extraction.inter_1802 c row := by
    simp only [KeccakfPermAir.extraction.inter_1804, KeccakfPermAir.extraction.inter_1803, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_1802 c row = (mc 340 + mc 660 + mc 1620 - 2*mc 340*mc 660 - 2*mc 340*mc 1620 - 2*mc 660*mc 1620 + 4*mc 340*mc 660*mc 1620) + 2 * KeccakfPermAir.extraction.inter_1800 c row := by
    simp only [KeccakfPermAir.extraction.inter_1802, KeccakfPermAir.extraction.inter_1801, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_1800 c row = (mc 341 + mc 661 + mc 1621 - 2*mc 341*mc 661 - 2*mc 341*mc 1621 - 2*mc 661*mc 1621 + 4*mc 341*mc 661*mc 1621) + 2 * KeccakfPermAir.extraction.inter_1798 c row := by
    simp only [KeccakfPermAir.extraction.inter_1800, KeccakfPermAir.extraction.inter_1799, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_1798 c row = (mc 342 + mc 662 + mc 1622 - 2*mc 342*mc 662 - 2*mc 342*mc 1622 - 2*mc 662*mc 1622 + 4*mc 342*mc 662*mc 1622) + 2 * KeccakfPermAir.extraction.inter_1796 c row := by
    simp only [KeccakfPermAir.extraction.inter_1798, KeccakfPermAir.extraction.inter_1797, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_1796 c row = (mc 343 + mc 663 + mc 1623 - 2*mc 343*mc 663 - 2*mc 343*mc 1623 - 2*mc 663*mc 1623 + 4*mc 343*mc 663*mc 1623) + 2 * KeccakfPermAir.extraction.inter_1794 c row := by
    simp only [KeccakfPermAir.extraction.inter_1796, KeccakfPermAir.extraction.inter_1795, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_1794 c row = (mc 344 + mc 664 + mc 1624 - 2*mc 344*mc 664 - 2*mc 344*mc 1624 - 2*mc 664*mc 1624 + 4*mc 344*mc 664*mc 1624) + 2 * KeccakfPermAir.extraction.inter_1792 c row := by
    simp only [KeccakfPermAir.extraction.inter_1794, KeccakfPermAir.extraction.inter_1793, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_1792 c row = (mc 345 + mc 665 + mc 1625 - 2*mc 345*mc 665 - 2*mc 345*mc 1625 - 2*mc 665*mc 1625 + 4*mc 345*mc 665*mc 1625) + 2 * KeccakfPermAir.extraction.inter_1790 c row := by
    simp only [KeccakfPermAir.extraction.inter_1792, KeccakfPermAir.extraction.inter_1791, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_1790 c row = (mc 346 + mc 666 + mc 1626 - 2*mc 346*mc 666 - 2*mc 346*mc 1626 - 2*mc 666*mc 1626 + 4*mc 346*mc 666*mc 1626) + 2 * KeccakfPermAir.extraction.inter_1788 c row := by
    simp only [KeccakfPermAir.extraction.inter_1790, KeccakfPermAir.extraction.inter_1789, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_1788 c row = (mc 347 + mc 667 + mc 1627 - 2*mc 347*mc 667 - 2*mc 347*mc 1627 - 2*mc 667*mc 1627 + 4*mc 347*mc 667*mc 1627) + 2 * KeccakfPermAir.extraction.inter_1786 c row := by
    simp only [KeccakfPermAir.extraction.inter_1788, KeccakfPermAir.extraction.inter_1787, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_1786 c row = (mc 348 + mc 668 + mc 1628 - 2*mc 348*mc 668 - 2*mc 348*mc 1628 - 2*mc 668*mc 1628 + 4*mc 348*mc 668*mc 1628) + 2 * KeccakfPermAir.extraction.inter_1784 c row := by
    simp only [KeccakfPermAir.extraction.inter_1786, KeccakfPermAir.extraction.inter_1785, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_1784 c row = (mc 349 + mc 669 + mc 1629 - 2*mc 349*mc 669 - 2*mc 349*mc 1629 - 2*mc 669*mc 1629 + 4*mc 349*mc 669*mc 1629) + 2 * KeccakfPermAir.extraction.inter_1782 c row := by
    simp only [KeccakfPermAir.extraction.inter_1784, KeccakfPermAir.extraction.inter_1783, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_1782 c row = (mc 350 + mc 670 + mc 1630 - 2*mc 350*mc 670 - 2*mc 350*mc 1630 - 2*mc 670*mc 1630 + 4*mc 350*mc 670*mc 1630) + 2 * KeccakfPermAir.extraction.inter_1780 c row := by
    simp only [KeccakfPermAir.extraction.inter_1782, KeccakfPermAir.extraction.inter_1781, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_1780 c row = (mc 351 + mc 671 + mc 1631 - 2*mc 351*mc 671 - 2*mc 351*mc 1631 - 2*mc 671*mc 1631 + 4*mc 351*mc 671*mc 1631) + 2 * KeccakfPermAir.extraction.inter_1778 c row := by
    simp only [KeccakfPermAir.extraction.inter_1780, KeccakfPermAir.extraction.inter_1779, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_1778 c row = (mc 352 + mc 672 + mc 1632 - 2*mc 352*mc 672 - 2*mc 352*mc 1632 - 2*mc 672*mc 1632 + 4*mc 352*mc 672*mc 1632) := by
    simp only [KeccakfPermAir.extraction.inter_1778, KeccakfPermAir.extraction.inter_1777, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1770 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 353 673 1633 173 row) :
    mc 173 = (mc 353 + mc 673 + mc 1633 - 2*mc 353*mc 673 - 2*mc 353*mc 1633 - 2*mc 673*mc 1633 + 4*mc 353*mc 673*mc 1633) + 2*(mc 354 + mc 674 + mc 1634 - 2*mc 354*mc 674 - 2*mc 354*mc 1634 - 2*mc 674*mc 1634 + 4*mc 354*mc 674*mc 1634) + 4*(mc 355 + mc 675 + mc 1635 - 2*mc 355*mc 675 - 2*mc 355*mc 1635 - 2*mc 675*mc 1635 + 4*mc 355*mc 675*mc 1635) + 8*(mc 356 + mc 676 + mc 1636 - 2*mc 356*mc 676 - 2*mc 356*mc 1636 - 2*mc 676*mc 1636 + 4*mc 356*mc 676*mc 1636) + 16*(mc 357 + mc 677 + mc 1637 - 2*mc 357*mc 677 - 2*mc 357*mc 1637 - 2*mc 677*mc 1637 + 4*mc 357*mc 677*mc 1637) + 32*(mc 358 + mc 678 + mc 1638 - 2*mc 358*mc 678 - 2*mc 358*mc 1638 - 2*mc 678*mc 1638 + 4*mc 358*mc 678*mc 1638) + 64*(mc 359 + mc 679 + mc 1639 - 2*mc 359*mc 679 - 2*mc 359*mc 1639 - 2*mc 679*mc 1639 + 4*mc 359*mc 679*mc 1639) + 128*(mc 360 + mc 680 + mc 1640 - 2*mc 360*mc 680 - 2*mc 360*mc 1640 - 2*mc 680*mc 1640 + 4*mc 360*mc 680*mc 1640) + 256*(mc 361 + mc 681 + mc 1641 - 2*mc 361*mc 681 - 2*mc 361*mc 1641 - 2*mc 681*mc 1641 + 4*mc 361*mc 681*mc 1641) + 512*(mc 362 + mc 682 + mc 1642 - 2*mc 362*mc 682 - 2*mc 362*mc 1642 - 2*mc 682*mc 1642 + 4*mc 362*mc 682*mc 1642) + 1024*(mc 363 + mc 683 + mc 1643 - 2*mc 363*mc 683 - 2*mc 363*mc 1643 - 2*mc 683*mc 1643 + 4*mc 363*mc 683*mc 1643) + 2048*(mc 364 + mc 684 + mc 1644 - 2*mc 364*mc 684 - 2*mc 364*mc 1644 - 2*mc 684*mc 1644 + 4*mc 364*mc 684*mc 1644) + 4096*(mc 365 + mc 685 + mc 1645 - 2*mc 365*mc 685 - 2*mc 365*mc 1645 - 2*mc 685*mc 1645 + 4*mc 365*mc 685*mc 1645) + 8192*(mc 366 + mc 686 + mc 1646 - 2*mc 366*mc 686 - 2*mc 366*mc 1646 - 2*mc 686*mc 1646 + 4*mc 366*mc 686*mc 1646) + 16384*(mc 367 + mc 687 + mc 1647 - 2*mc 367*mc 687 - 2*mc 367*mc 1647 - 2*mc 687*mc 1647 + 4*mc 367*mc 687*mc 1647) + 32768*(mc 368 + mc 688 + mc 1648 - 2*mc 368*mc 688 - 2*mc 368*mc 1648 - 2*mc 688*mc 1648 + 4*mc 368*mc 688*mc 1648) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1770, KeccakfPermAir.extraction.inter_1838, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_1837 c row = (mc 354 + mc 674 + mc 1634 - 2*mc 354*mc 674 - 2*mc 354*mc 1634 - 2*mc 674*mc 1634 + 4*mc 354*mc 674*mc 1634) + 2 * KeccakfPermAir.extraction.inter_1835 c row := by
    simp only [KeccakfPermAir.extraction.inter_1837, KeccakfPermAir.extraction.inter_1836, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_1835 c row = (mc 355 + mc 675 + mc 1635 - 2*mc 355*mc 675 - 2*mc 355*mc 1635 - 2*mc 675*mc 1635 + 4*mc 355*mc 675*mc 1635) + 2 * KeccakfPermAir.extraction.inter_1833 c row := by
    simp only [KeccakfPermAir.extraction.inter_1835, KeccakfPermAir.extraction.inter_1834, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_1833 c row = (mc 356 + mc 676 + mc 1636 - 2*mc 356*mc 676 - 2*mc 356*mc 1636 - 2*mc 676*mc 1636 + 4*mc 356*mc 676*mc 1636) + 2 * KeccakfPermAir.extraction.inter_1831 c row := by
    simp only [KeccakfPermAir.extraction.inter_1833, KeccakfPermAir.extraction.inter_1832, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_1831 c row = (mc 357 + mc 677 + mc 1637 - 2*mc 357*mc 677 - 2*mc 357*mc 1637 - 2*mc 677*mc 1637 + 4*mc 357*mc 677*mc 1637) + 2 * KeccakfPermAir.extraction.inter_1829 c row := by
    simp only [KeccakfPermAir.extraction.inter_1831, KeccakfPermAir.extraction.inter_1830, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_1829 c row = (mc 358 + mc 678 + mc 1638 - 2*mc 358*mc 678 - 2*mc 358*mc 1638 - 2*mc 678*mc 1638 + 4*mc 358*mc 678*mc 1638) + 2 * KeccakfPermAir.extraction.inter_1827 c row := by
    simp only [KeccakfPermAir.extraction.inter_1829, KeccakfPermAir.extraction.inter_1828, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_1827 c row = (mc 359 + mc 679 + mc 1639 - 2*mc 359*mc 679 - 2*mc 359*mc 1639 - 2*mc 679*mc 1639 + 4*mc 359*mc 679*mc 1639) + 2 * KeccakfPermAir.extraction.inter_1825 c row := by
    simp only [KeccakfPermAir.extraction.inter_1827, KeccakfPermAir.extraction.inter_1826, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_1825 c row = (mc 360 + mc 680 + mc 1640 - 2*mc 360*mc 680 - 2*mc 360*mc 1640 - 2*mc 680*mc 1640 + 4*mc 360*mc 680*mc 1640) + 2 * KeccakfPermAir.extraction.inter_1823 c row := by
    simp only [KeccakfPermAir.extraction.inter_1825, KeccakfPermAir.extraction.inter_1824, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_1823 c row = (mc 361 + mc 681 + mc 1641 - 2*mc 361*mc 681 - 2*mc 361*mc 1641 - 2*mc 681*mc 1641 + 4*mc 361*mc 681*mc 1641) + 2 * KeccakfPermAir.extraction.inter_1821 c row := by
    simp only [KeccakfPermAir.extraction.inter_1823, KeccakfPermAir.extraction.inter_1822, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_1821 c row = (mc 362 + mc 682 + mc 1642 - 2*mc 362*mc 682 - 2*mc 362*mc 1642 - 2*mc 682*mc 1642 + 4*mc 362*mc 682*mc 1642) + 2 * KeccakfPermAir.extraction.inter_1819 c row := by
    simp only [KeccakfPermAir.extraction.inter_1821, KeccakfPermAir.extraction.inter_1820, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_1819 c row = (mc 363 + mc 683 + mc 1643 - 2*mc 363*mc 683 - 2*mc 363*mc 1643 - 2*mc 683*mc 1643 + 4*mc 363*mc 683*mc 1643) + 2 * KeccakfPermAir.extraction.inter_1817 c row := by
    simp only [KeccakfPermAir.extraction.inter_1819, KeccakfPermAir.extraction.inter_1818, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_1817 c row = (mc 364 + mc 684 + mc 1644 - 2*mc 364*mc 684 - 2*mc 364*mc 1644 - 2*mc 684*mc 1644 + 4*mc 364*mc 684*mc 1644) + 2 * KeccakfPermAir.extraction.inter_1815 c row := by
    simp only [KeccakfPermAir.extraction.inter_1817, KeccakfPermAir.extraction.inter_1816, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_1815 c row = (mc 365 + mc 685 + mc 1645 - 2*mc 365*mc 685 - 2*mc 365*mc 1645 - 2*mc 685*mc 1645 + 4*mc 365*mc 685*mc 1645) + 2 * KeccakfPermAir.extraction.inter_1813 c row := by
    simp only [KeccakfPermAir.extraction.inter_1815, KeccakfPermAir.extraction.inter_1814, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_1813 c row = (mc 366 + mc 686 + mc 1646 - 2*mc 366*mc 686 - 2*mc 366*mc 1646 - 2*mc 686*mc 1646 + 4*mc 366*mc 686*mc 1646) + 2 * KeccakfPermAir.extraction.inter_1811 c row := by
    simp only [KeccakfPermAir.extraction.inter_1813, KeccakfPermAir.extraction.inter_1812, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_1811 c row = (mc 367 + mc 687 + mc 1647 - 2*mc 367*mc 687 - 2*mc 367*mc 1647 - 2*mc 687*mc 1647 + 4*mc 367*mc 687*mc 1647) + 2 * KeccakfPermAir.extraction.inter_1809 c row := by
    simp only [KeccakfPermAir.extraction.inter_1811, KeccakfPermAir.extraction.inter_1810, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_1809 c row = (mc 368 + mc 688 + mc 1648 - 2*mc 368*mc 688 - 2*mc 368*mc 1648 - 2*mc 688*mc 1648 + 4*mc 368*mc 688*mc 1648) := by
    simp only [KeccakfPermAir.extraction.inter_1809, KeccakfPermAir.extraction.inter_1808, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1771 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 369 689 1649 174 row) :
    mc 174 = (mc 369 + mc 689 + mc 1649 - 2*mc 369*mc 689 - 2*mc 369*mc 1649 - 2*mc 689*mc 1649 + 4*mc 369*mc 689*mc 1649) + 2*(mc 370 + mc 690 + mc 1650 - 2*mc 370*mc 690 - 2*mc 370*mc 1650 - 2*mc 690*mc 1650 + 4*mc 370*mc 690*mc 1650) + 4*(mc 371 + mc 691 + mc 1651 - 2*mc 371*mc 691 - 2*mc 371*mc 1651 - 2*mc 691*mc 1651 + 4*mc 371*mc 691*mc 1651) + 8*(mc 372 + mc 692 + mc 1652 - 2*mc 372*mc 692 - 2*mc 372*mc 1652 - 2*mc 692*mc 1652 + 4*mc 372*mc 692*mc 1652) + 16*(mc 373 + mc 693 + mc 1653 - 2*mc 373*mc 693 - 2*mc 373*mc 1653 - 2*mc 693*mc 1653 + 4*mc 373*mc 693*mc 1653) + 32*(mc 374 + mc 694 + mc 1654 - 2*mc 374*mc 694 - 2*mc 374*mc 1654 - 2*mc 694*mc 1654 + 4*mc 374*mc 694*mc 1654) + 64*(mc 375 + mc 695 + mc 1655 - 2*mc 375*mc 695 - 2*mc 375*mc 1655 - 2*mc 695*mc 1655 + 4*mc 375*mc 695*mc 1655) + 128*(mc 376 + mc 696 + mc 1656 - 2*mc 376*mc 696 - 2*mc 376*mc 1656 - 2*mc 696*mc 1656 + 4*mc 376*mc 696*mc 1656) + 256*(mc 377 + mc 697 + mc 1657 - 2*mc 377*mc 697 - 2*mc 377*mc 1657 - 2*mc 697*mc 1657 + 4*mc 377*mc 697*mc 1657) + 512*(mc 378 + mc 698 + mc 1658 - 2*mc 378*mc 698 - 2*mc 378*mc 1658 - 2*mc 698*mc 1658 + 4*mc 378*mc 698*mc 1658) + 1024*(mc 379 + mc 699 + mc 1659 - 2*mc 379*mc 699 - 2*mc 379*mc 1659 - 2*mc 699*mc 1659 + 4*mc 379*mc 699*mc 1659) + 2048*(mc 380 + mc 700 + mc 1660 - 2*mc 380*mc 700 - 2*mc 380*mc 1660 - 2*mc 700*mc 1660 + 4*mc 380*mc 700*mc 1660) + 4096*(mc 381 + mc 701 + mc 1661 - 2*mc 381*mc 701 - 2*mc 381*mc 1661 - 2*mc 701*mc 1661 + 4*mc 381*mc 701*mc 1661) + 8192*(mc 382 + mc 702 + mc 1662 - 2*mc 382*mc 702 - 2*mc 382*mc 1662 - 2*mc 702*mc 1662 + 4*mc 382*mc 702*mc 1662) + 16384*(mc 383 + mc 703 + mc 1663 - 2*mc 383*mc 703 - 2*mc 383*mc 1663 - 2*mc 703*mc 1663 + 4*mc 383*mc 703*mc 1663) + 32768*(mc 384 + mc 704 + mc 1664 - 2*mc 384*mc 704 - 2*mc 384*mc 1664 - 2*mc 704*mc 1664 + 4*mc 384*mc 704*mc 1664) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1771, KeccakfPermAir.extraction.inter_1869, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_1868 c row = (mc 370 + mc 690 + mc 1650 - 2*mc 370*mc 690 - 2*mc 370*mc 1650 - 2*mc 690*mc 1650 + 4*mc 370*mc 690*mc 1650) + 2 * KeccakfPermAir.extraction.inter_1866 c row := by
    simp only [KeccakfPermAir.extraction.inter_1868, KeccakfPermAir.extraction.inter_1867, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_1866 c row = (mc 371 + mc 691 + mc 1651 - 2*mc 371*mc 691 - 2*mc 371*mc 1651 - 2*mc 691*mc 1651 + 4*mc 371*mc 691*mc 1651) + 2 * KeccakfPermAir.extraction.inter_1864 c row := by
    simp only [KeccakfPermAir.extraction.inter_1866, KeccakfPermAir.extraction.inter_1865, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_1864 c row = (mc 372 + mc 692 + mc 1652 - 2*mc 372*mc 692 - 2*mc 372*mc 1652 - 2*mc 692*mc 1652 + 4*mc 372*mc 692*mc 1652) + 2 * KeccakfPermAir.extraction.inter_1862 c row := by
    simp only [KeccakfPermAir.extraction.inter_1864, KeccakfPermAir.extraction.inter_1863, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_1862 c row = (mc 373 + mc 693 + mc 1653 - 2*mc 373*mc 693 - 2*mc 373*mc 1653 - 2*mc 693*mc 1653 + 4*mc 373*mc 693*mc 1653) + 2 * KeccakfPermAir.extraction.inter_1860 c row := by
    simp only [KeccakfPermAir.extraction.inter_1862, KeccakfPermAir.extraction.inter_1861, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_1860 c row = (mc 374 + mc 694 + mc 1654 - 2*mc 374*mc 694 - 2*mc 374*mc 1654 - 2*mc 694*mc 1654 + 4*mc 374*mc 694*mc 1654) + 2 * KeccakfPermAir.extraction.inter_1858 c row := by
    simp only [KeccakfPermAir.extraction.inter_1860, KeccakfPermAir.extraction.inter_1859, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_1858 c row = (mc 375 + mc 695 + mc 1655 - 2*mc 375*mc 695 - 2*mc 375*mc 1655 - 2*mc 695*mc 1655 + 4*mc 375*mc 695*mc 1655) + 2 * KeccakfPermAir.extraction.inter_1856 c row := by
    simp only [KeccakfPermAir.extraction.inter_1858, KeccakfPermAir.extraction.inter_1857, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_1856 c row = (mc 376 + mc 696 + mc 1656 - 2*mc 376*mc 696 - 2*mc 376*mc 1656 - 2*mc 696*mc 1656 + 4*mc 376*mc 696*mc 1656) + 2 * KeccakfPermAir.extraction.inter_1854 c row := by
    simp only [KeccakfPermAir.extraction.inter_1856, KeccakfPermAir.extraction.inter_1855, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_1854 c row = (mc 377 + mc 697 + mc 1657 - 2*mc 377*mc 697 - 2*mc 377*mc 1657 - 2*mc 697*mc 1657 + 4*mc 377*mc 697*mc 1657) + 2 * KeccakfPermAir.extraction.inter_1852 c row := by
    simp only [KeccakfPermAir.extraction.inter_1854, KeccakfPermAir.extraction.inter_1853, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_1852 c row = (mc 378 + mc 698 + mc 1658 - 2*mc 378*mc 698 - 2*mc 378*mc 1658 - 2*mc 698*mc 1658 + 4*mc 378*mc 698*mc 1658) + 2 * KeccakfPermAir.extraction.inter_1850 c row := by
    simp only [KeccakfPermAir.extraction.inter_1852, KeccakfPermAir.extraction.inter_1851, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_1850 c row = (mc 379 + mc 699 + mc 1659 - 2*mc 379*mc 699 - 2*mc 379*mc 1659 - 2*mc 699*mc 1659 + 4*mc 379*mc 699*mc 1659) + 2 * KeccakfPermAir.extraction.inter_1848 c row := by
    simp only [KeccakfPermAir.extraction.inter_1850, KeccakfPermAir.extraction.inter_1849, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_1848 c row = (mc 380 + mc 700 + mc 1660 - 2*mc 380*mc 700 - 2*mc 380*mc 1660 - 2*mc 700*mc 1660 + 4*mc 380*mc 700*mc 1660) + 2 * KeccakfPermAir.extraction.inter_1846 c row := by
    simp only [KeccakfPermAir.extraction.inter_1848, KeccakfPermAir.extraction.inter_1847, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_1846 c row = (mc 381 + mc 701 + mc 1661 - 2*mc 381*mc 701 - 2*mc 381*mc 1661 - 2*mc 701*mc 1661 + 4*mc 381*mc 701*mc 1661) + 2 * KeccakfPermAir.extraction.inter_1844 c row := by
    simp only [KeccakfPermAir.extraction.inter_1846, KeccakfPermAir.extraction.inter_1845, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_1844 c row = (mc 382 + mc 702 + mc 1662 - 2*mc 382*mc 702 - 2*mc 382*mc 1662 - 2*mc 702*mc 1662 + 4*mc 382*mc 702*mc 1662) + 2 * KeccakfPermAir.extraction.inter_1842 c row := by
    simp only [KeccakfPermAir.extraction.inter_1844, KeccakfPermAir.extraction.inter_1843, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_1842 c row = (mc 383 + mc 703 + mc 1663 - 2*mc 383*mc 703 - 2*mc 383*mc 1663 - 2*mc 703*mc 1663 + 4*mc 383*mc 703*mc 1663) + 2 * KeccakfPermAir.extraction.inter_1840 c row := by
    simp only [KeccakfPermAir.extraction.inter_1842, KeccakfPermAir.extraction.inter_1841, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_1840 c row = (mc 384 + mc 704 + mc 1664 - 2*mc 384*mc 704 - 2*mc 384*mc 1664 - 2*mc 704*mc 1664 + 4*mc 384*mc 704*mc 1664) := by
    simp only [KeccakfPermAir.extraction.inter_1840, KeccakfPermAir.extraction.inter_1839, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1772 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 385 705 1665 175 row) :
    mc 175 = (mc 385 + mc 705 + mc 1665 - 2*mc 385*mc 705 - 2*mc 385*mc 1665 - 2*mc 705*mc 1665 + 4*mc 385*mc 705*mc 1665) + 2*(mc 386 + mc 706 + mc 1666 - 2*mc 386*mc 706 - 2*mc 386*mc 1666 - 2*mc 706*mc 1666 + 4*mc 386*mc 706*mc 1666) + 4*(mc 387 + mc 707 + mc 1667 - 2*mc 387*mc 707 - 2*mc 387*mc 1667 - 2*mc 707*mc 1667 + 4*mc 387*mc 707*mc 1667) + 8*(mc 388 + mc 708 + mc 1668 - 2*mc 388*mc 708 - 2*mc 388*mc 1668 - 2*mc 708*mc 1668 + 4*mc 388*mc 708*mc 1668) + 16*(mc 389 + mc 709 + mc 1669 - 2*mc 389*mc 709 - 2*mc 389*mc 1669 - 2*mc 709*mc 1669 + 4*mc 389*mc 709*mc 1669) + 32*(mc 390 + mc 710 + mc 1670 - 2*mc 390*mc 710 - 2*mc 390*mc 1670 - 2*mc 710*mc 1670 + 4*mc 390*mc 710*mc 1670) + 64*(mc 391 + mc 711 + mc 1671 - 2*mc 391*mc 711 - 2*mc 391*mc 1671 - 2*mc 711*mc 1671 + 4*mc 391*mc 711*mc 1671) + 128*(mc 392 + mc 712 + mc 1672 - 2*mc 392*mc 712 - 2*mc 392*mc 1672 - 2*mc 712*mc 1672 + 4*mc 392*mc 712*mc 1672) + 256*(mc 393 + mc 713 + mc 1673 - 2*mc 393*mc 713 - 2*mc 393*mc 1673 - 2*mc 713*mc 1673 + 4*mc 393*mc 713*mc 1673) + 512*(mc 394 + mc 714 + mc 1674 - 2*mc 394*mc 714 - 2*mc 394*mc 1674 - 2*mc 714*mc 1674 + 4*mc 394*mc 714*mc 1674) + 1024*(mc 395 + mc 715 + mc 1675 - 2*mc 395*mc 715 - 2*mc 395*mc 1675 - 2*mc 715*mc 1675 + 4*mc 395*mc 715*mc 1675) + 2048*(mc 396 + mc 716 + mc 1676 - 2*mc 396*mc 716 - 2*mc 396*mc 1676 - 2*mc 716*mc 1676 + 4*mc 396*mc 716*mc 1676) + 4096*(mc 397 + mc 717 + mc 1677 - 2*mc 397*mc 717 - 2*mc 397*mc 1677 - 2*mc 717*mc 1677 + 4*mc 397*mc 717*mc 1677) + 8192*(mc 398 + mc 718 + mc 1678 - 2*mc 398*mc 718 - 2*mc 398*mc 1678 - 2*mc 718*mc 1678 + 4*mc 398*mc 718*mc 1678) + 16384*(mc 399 + mc 719 + mc 1679 - 2*mc 399*mc 719 - 2*mc 399*mc 1679 - 2*mc 719*mc 1679 + 4*mc 399*mc 719*mc 1679) + 32768*(mc 400 + mc 720 + mc 1680 - 2*mc 400*mc 720 - 2*mc 400*mc 1680 - 2*mc 720*mc 1680 + 4*mc 400*mc 720*mc 1680) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1772, KeccakfPermAir.extraction.inter_1900, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_1899 c row = (mc 386 + mc 706 + mc 1666 - 2*mc 386*mc 706 - 2*mc 386*mc 1666 - 2*mc 706*mc 1666 + 4*mc 386*mc 706*mc 1666) + 2 * KeccakfPermAir.extraction.inter_1897 c row := by
    simp only [KeccakfPermAir.extraction.inter_1899, KeccakfPermAir.extraction.inter_1898, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_1897 c row = (mc 387 + mc 707 + mc 1667 - 2*mc 387*mc 707 - 2*mc 387*mc 1667 - 2*mc 707*mc 1667 + 4*mc 387*mc 707*mc 1667) + 2 * KeccakfPermAir.extraction.inter_1895 c row := by
    simp only [KeccakfPermAir.extraction.inter_1897, KeccakfPermAir.extraction.inter_1896, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_1895 c row = (mc 388 + mc 708 + mc 1668 - 2*mc 388*mc 708 - 2*mc 388*mc 1668 - 2*mc 708*mc 1668 + 4*mc 388*mc 708*mc 1668) + 2 * KeccakfPermAir.extraction.inter_1893 c row := by
    simp only [KeccakfPermAir.extraction.inter_1895, KeccakfPermAir.extraction.inter_1894, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_1893 c row = (mc 389 + mc 709 + mc 1669 - 2*mc 389*mc 709 - 2*mc 389*mc 1669 - 2*mc 709*mc 1669 + 4*mc 389*mc 709*mc 1669) + 2 * KeccakfPermAir.extraction.inter_1891 c row := by
    simp only [KeccakfPermAir.extraction.inter_1893, KeccakfPermAir.extraction.inter_1892, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_1891 c row = (mc 390 + mc 710 + mc 1670 - 2*mc 390*mc 710 - 2*mc 390*mc 1670 - 2*mc 710*mc 1670 + 4*mc 390*mc 710*mc 1670) + 2 * KeccakfPermAir.extraction.inter_1889 c row := by
    simp only [KeccakfPermAir.extraction.inter_1891, KeccakfPermAir.extraction.inter_1890, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_1889 c row = (mc 391 + mc 711 + mc 1671 - 2*mc 391*mc 711 - 2*mc 391*mc 1671 - 2*mc 711*mc 1671 + 4*mc 391*mc 711*mc 1671) + 2 * KeccakfPermAir.extraction.inter_1887 c row := by
    simp only [KeccakfPermAir.extraction.inter_1889, KeccakfPermAir.extraction.inter_1888, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_1887 c row = (mc 392 + mc 712 + mc 1672 - 2*mc 392*mc 712 - 2*mc 392*mc 1672 - 2*mc 712*mc 1672 + 4*mc 392*mc 712*mc 1672) + 2 * KeccakfPermAir.extraction.inter_1885 c row := by
    simp only [KeccakfPermAir.extraction.inter_1887, KeccakfPermAir.extraction.inter_1886, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_1885 c row = (mc 393 + mc 713 + mc 1673 - 2*mc 393*mc 713 - 2*mc 393*mc 1673 - 2*mc 713*mc 1673 + 4*mc 393*mc 713*mc 1673) + 2 * KeccakfPermAir.extraction.inter_1883 c row := by
    simp only [KeccakfPermAir.extraction.inter_1885, KeccakfPermAir.extraction.inter_1884, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_1883 c row = (mc 394 + mc 714 + mc 1674 - 2*mc 394*mc 714 - 2*mc 394*mc 1674 - 2*mc 714*mc 1674 + 4*mc 394*mc 714*mc 1674) + 2 * KeccakfPermAir.extraction.inter_1881 c row := by
    simp only [KeccakfPermAir.extraction.inter_1883, KeccakfPermAir.extraction.inter_1882, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_1881 c row = (mc 395 + mc 715 + mc 1675 - 2*mc 395*mc 715 - 2*mc 395*mc 1675 - 2*mc 715*mc 1675 + 4*mc 395*mc 715*mc 1675) + 2 * KeccakfPermAir.extraction.inter_1879 c row := by
    simp only [KeccakfPermAir.extraction.inter_1881, KeccakfPermAir.extraction.inter_1880, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_1879 c row = (mc 396 + mc 716 + mc 1676 - 2*mc 396*mc 716 - 2*mc 396*mc 1676 - 2*mc 716*mc 1676 + 4*mc 396*mc 716*mc 1676) + 2 * KeccakfPermAir.extraction.inter_1877 c row := by
    simp only [KeccakfPermAir.extraction.inter_1879, KeccakfPermAir.extraction.inter_1878, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_1877 c row = (mc 397 + mc 717 + mc 1677 - 2*mc 397*mc 717 - 2*mc 397*mc 1677 - 2*mc 717*mc 1677 + 4*mc 397*mc 717*mc 1677) + 2 * KeccakfPermAir.extraction.inter_1875 c row := by
    simp only [KeccakfPermAir.extraction.inter_1877, KeccakfPermAir.extraction.inter_1876, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_1875 c row = (mc 398 + mc 718 + mc 1678 - 2*mc 398*mc 718 - 2*mc 398*mc 1678 - 2*mc 718*mc 1678 + 4*mc 398*mc 718*mc 1678) + 2 * KeccakfPermAir.extraction.inter_1873 c row := by
    simp only [KeccakfPermAir.extraction.inter_1875, KeccakfPermAir.extraction.inter_1874, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_1873 c row = (mc 399 + mc 719 + mc 1679 - 2*mc 399*mc 719 - 2*mc 399*mc 1679 - 2*mc 719*mc 1679 + 4*mc 399*mc 719*mc 1679) + 2 * KeccakfPermAir.extraction.inter_1871 c row := by
    simp only [KeccakfPermAir.extraction.inter_1873, KeccakfPermAir.extraction.inter_1872, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_1871 c row = (mc 400 + mc 720 + mc 1680 - 2*mc 400*mc 720 - 2*mc 400*mc 1680 - 2*mc 720*mc 1680 + 4*mc 400*mc 720*mc 1680) := by
    simp only [KeccakfPermAir.extraction.inter_1871, KeccakfPermAir.extraction.inter_1870, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1773 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 401 721 1681 176 row) :
    mc 176 = (mc 401 + mc 721 + mc 1681 - 2*mc 401*mc 721 - 2*mc 401*mc 1681 - 2*mc 721*mc 1681 + 4*mc 401*mc 721*mc 1681) + 2*(mc 402 + mc 722 + mc 1682 - 2*mc 402*mc 722 - 2*mc 402*mc 1682 - 2*mc 722*mc 1682 + 4*mc 402*mc 722*mc 1682) + 4*(mc 403 + mc 723 + mc 1683 - 2*mc 403*mc 723 - 2*mc 403*mc 1683 - 2*mc 723*mc 1683 + 4*mc 403*mc 723*mc 1683) + 8*(mc 404 + mc 724 + mc 1684 - 2*mc 404*mc 724 - 2*mc 404*mc 1684 - 2*mc 724*mc 1684 + 4*mc 404*mc 724*mc 1684) + 16*(mc 405 + mc 725 + mc 1685 - 2*mc 405*mc 725 - 2*mc 405*mc 1685 - 2*mc 725*mc 1685 + 4*mc 405*mc 725*mc 1685) + 32*(mc 406 + mc 726 + mc 1686 - 2*mc 406*mc 726 - 2*mc 406*mc 1686 - 2*mc 726*mc 1686 + 4*mc 406*mc 726*mc 1686) + 64*(mc 407 + mc 727 + mc 1687 - 2*mc 407*mc 727 - 2*mc 407*mc 1687 - 2*mc 727*mc 1687 + 4*mc 407*mc 727*mc 1687) + 128*(mc 408 + mc 728 + mc 1688 - 2*mc 408*mc 728 - 2*mc 408*mc 1688 - 2*mc 728*mc 1688 + 4*mc 408*mc 728*mc 1688) + 256*(mc 409 + mc 729 + mc 1689 - 2*mc 409*mc 729 - 2*mc 409*mc 1689 - 2*mc 729*mc 1689 + 4*mc 409*mc 729*mc 1689) + 512*(mc 410 + mc 730 + mc 1690 - 2*mc 410*mc 730 - 2*mc 410*mc 1690 - 2*mc 730*mc 1690 + 4*mc 410*mc 730*mc 1690) + 1024*(mc 411 + mc 731 + mc 1691 - 2*mc 411*mc 731 - 2*mc 411*mc 1691 - 2*mc 731*mc 1691 + 4*mc 411*mc 731*mc 1691) + 2048*(mc 412 + mc 732 + mc 1692 - 2*mc 412*mc 732 - 2*mc 412*mc 1692 - 2*mc 732*mc 1692 + 4*mc 412*mc 732*mc 1692) + 4096*(mc 413 + mc 733 + mc 1693 - 2*mc 413*mc 733 - 2*mc 413*mc 1693 - 2*mc 733*mc 1693 + 4*mc 413*mc 733*mc 1693) + 8192*(mc 414 + mc 734 + mc 1694 - 2*mc 414*mc 734 - 2*mc 414*mc 1694 - 2*mc 734*mc 1694 + 4*mc 414*mc 734*mc 1694) + 16384*(mc 415 + mc 735 + mc 1695 - 2*mc 415*mc 735 - 2*mc 415*mc 1695 - 2*mc 735*mc 1695 + 4*mc 415*mc 735*mc 1695) + 32768*(mc 416 + mc 736 + mc 1696 - 2*mc 416*mc 736 - 2*mc 416*mc 1696 - 2*mc 736*mc 1696 + 4*mc 416*mc 736*mc 1696) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1773, KeccakfPermAir.extraction.inter_1931, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_1930 c row = (mc 402 + mc 722 + mc 1682 - 2*mc 402*mc 722 - 2*mc 402*mc 1682 - 2*mc 722*mc 1682 + 4*mc 402*mc 722*mc 1682) + 2 * KeccakfPermAir.extraction.inter_1928 c row := by
    simp only [KeccakfPermAir.extraction.inter_1930, KeccakfPermAir.extraction.inter_1929, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_1928 c row = (mc 403 + mc 723 + mc 1683 - 2*mc 403*mc 723 - 2*mc 403*mc 1683 - 2*mc 723*mc 1683 + 4*mc 403*mc 723*mc 1683) + 2 * KeccakfPermAir.extraction.inter_1926 c row := by
    simp only [KeccakfPermAir.extraction.inter_1928, KeccakfPermAir.extraction.inter_1927, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_1926 c row = (mc 404 + mc 724 + mc 1684 - 2*mc 404*mc 724 - 2*mc 404*mc 1684 - 2*mc 724*mc 1684 + 4*mc 404*mc 724*mc 1684) + 2 * KeccakfPermAir.extraction.inter_1924 c row := by
    simp only [KeccakfPermAir.extraction.inter_1926, KeccakfPermAir.extraction.inter_1925, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_1924 c row = (mc 405 + mc 725 + mc 1685 - 2*mc 405*mc 725 - 2*mc 405*mc 1685 - 2*mc 725*mc 1685 + 4*mc 405*mc 725*mc 1685) + 2 * KeccakfPermAir.extraction.inter_1922 c row := by
    simp only [KeccakfPermAir.extraction.inter_1924, KeccakfPermAir.extraction.inter_1923, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_1922 c row = (mc 406 + mc 726 + mc 1686 - 2*mc 406*mc 726 - 2*mc 406*mc 1686 - 2*mc 726*mc 1686 + 4*mc 406*mc 726*mc 1686) + 2 * KeccakfPermAir.extraction.inter_1920 c row := by
    simp only [KeccakfPermAir.extraction.inter_1922, KeccakfPermAir.extraction.inter_1921, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_1920 c row = (mc 407 + mc 727 + mc 1687 - 2*mc 407*mc 727 - 2*mc 407*mc 1687 - 2*mc 727*mc 1687 + 4*mc 407*mc 727*mc 1687) + 2 * KeccakfPermAir.extraction.inter_1918 c row := by
    simp only [KeccakfPermAir.extraction.inter_1920, KeccakfPermAir.extraction.inter_1919, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_1918 c row = (mc 408 + mc 728 + mc 1688 - 2*mc 408*mc 728 - 2*mc 408*mc 1688 - 2*mc 728*mc 1688 + 4*mc 408*mc 728*mc 1688) + 2 * KeccakfPermAir.extraction.inter_1916 c row := by
    simp only [KeccakfPermAir.extraction.inter_1918, KeccakfPermAir.extraction.inter_1917, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_1916 c row = (mc 409 + mc 729 + mc 1689 - 2*mc 409*mc 729 - 2*mc 409*mc 1689 - 2*mc 729*mc 1689 + 4*mc 409*mc 729*mc 1689) + 2 * KeccakfPermAir.extraction.inter_1914 c row := by
    simp only [KeccakfPermAir.extraction.inter_1916, KeccakfPermAir.extraction.inter_1915, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_1914 c row = (mc 410 + mc 730 + mc 1690 - 2*mc 410*mc 730 - 2*mc 410*mc 1690 - 2*mc 730*mc 1690 + 4*mc 410*mc 730*mc 1690) + 2 * KeccakfPermAir.extraction.inter_1912 c row := by
    simp only [KeccakfPermAir.extraction.inter_1914, KeccakfPermAir.extraction.inter_1913, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_1912 c row = (mc 411 + mc 731 + mc 1691 - 2*mc 411*mc 731 - 2*mc 411*mc 1691 - 2*mc 731*mc 1691 + 4*mc 411*mc 731*mc 1691) + 2 * KeccakfPermAir.extraction.inter_1910 c row := by
    simp only [KeccakfPermAir.extraction.inter_1912, KeccakfPermAir.extraction.inter_1911, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_1910 c row = (mc 412 + mc 732 + mc 1692 - 2*mc 412*mc 732 - 2*mc 412*mc 1692 - 2*mc 732*mc 1692 + 4*mc 412*mc 732*mc 1692) + 2 * KeccakfPermAir.extraction.inter_1908 c row := by
    simp only [KeccakfPermAir.extraction.inter_1910, KeccakfPermAir.extraction.inter_1909, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_1908 c row = (mc 413 + mc 733 + mc 1693 - 2*mc 413*mc 733 - 2*mc 413*mc 1693 - 2*mc 733*mc 1693 + 4*mc 413*mc 733*mc 1693) + 2 * KeccakfPermAir.extraction.inter_1906 c row := by
    simp only [KeccakfPermAir.extraction.inter_1908, KeccakfPermAir.extraction.inter_1907, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_1906 c row = (mc 414 + mc 734 + mc 1694 - 2*mc 414*mc 734 - 2*mc 414*mc 1694 - 2*mc 734*mc 1694 + 4*mc 414*mc 734*mc 1694) + 2 * KeccakfPermAir.extraction.inter_1904 c row := by
    simp only [KeccakfPermAir.extraction.inter_1906, KeccakfPermAir.extraction.inter_1905, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_1904 c row = (mc 415 + mc 735 + mc 1695 - 2*mc 415*mc 735 - 2*mc 415*mc 1695 - 2*mc 735*mc 1695 + 4*mc 415*mc 735*mc 1695) + 2 * KeccakfPermAir.extraction.inter_1902 c row := by
    simp only [KeccakfPermAir.extraction.inter_1904, KeccakfPermAir.extraction.inter_1903, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_1902 c row = (mc 416 + mc 736 + mc 1696 - 2*mc 416*mc 736 - 2*mc 416*mc 1696 - 2*mc 736*mc 1696 + 4*mc 416*mc 736*mc 1696) := by
    simp only [KeccakfPermAir.extraction.inter_1902, KeccakfPermAir.extraction.inter_1901, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1838 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 417 737 1697 177 row) :
    mc 177 = (mc 417 + mc 737 + mc 1697 - 2*mc 417*mc 737 - 2*mc 417*mc 1697 - 2*mc 737*mc 1697 + 4*mc 417*mc 737*mc 1697) + 2*(mc 418 + mc 738 + mc 1698 - 2*mc 418*mc 738 - 2*mc 418*mc 1698 - 2*mc 738*mc 1698 + 4*mc 418*mc 738*mc 1698) + 4*(mc 419 + mc 739 + mc 1699 - 2*mc 419*mc 739 - 2*mc 419*mc 1699 - 2*mc 739*mc 1699 + 4*mc 419*mc 739*mc 1699) + 8*(mc 420 + mc 740 + mc 1700 - 2*mc 420*mc 740 - 2*mc 420*mc 1700 - 2*mc 740*mc 1700 + 4*mc 420*mc 740*mc 1700) + 16*(mc 421 + mc 741 + mc 1701 - 2*mc 421*mc 741 - 2*mc 421*mc 1701 - 2*mc 741*mc 1701 + 4*mc 421*mc 741*mc 1701) + 32*(mc 422 + mc 742 + mc 1702 - 2*mc 422*mc 742 - 2*mc 422*mc 1702 - 2*mc 742*mc 1702 + 4*mc 422*mc 742*mc 1702) + 64*(mc 423 + mc 743 + mc 1703 - 2*mc 423*mc 743 - 2*mc 423*mc 1703 - 2*mc 743*mc 1703 + 4*mc 423*mc 743*mc 1703) + 128*(mc 424 + mc 744 + mc 1704 - 2*mc 424*mc 744 - 2*mc 424*mc 1704 - 2*mc 744*mc 1704 + 4*mc 424*mc 744*mc 1704) + 256*(mc 425 + mc 745 + mc 1705 - 2*mc 425*mc 745 - 2*mc 425*mc 1705 - 2*mc 745*mc 1705 + 4*mc 425*mc 745*mc 1705) + 512*(mc 426 + mc 746 + mc 1706 - 2*mc 426*mc 746 - 2*mc 426*mc 1706 - 2*mc 746*mc 1706 + 4*mc 426*mc 746*mc 1706) + 1024*(mc 427 + mc 747 + mc 1707 - 2*mc 427*mc 747 - 2*mc 427*mc 1707 - 2*mc 747*mc 1707 + 4*mc 427*mc 747*mc 1707) + 2048*(mc 428 + mc 748 + mc 1708 - 2*mc 428*mc 748 - 2*mc 428*mc 1708 - 2*mc 748*mc 1708 + 4*mc 428*mc 748*mc 1708) + 4096*(mc 429 + mc 749 + mc 1709 - 2*mc 429*mc 749 - 2*mc 429*mc 1709 - 2*mc 749*mc 1709 + 4*mc 429*mc 749*mc 1709) + 8192*(mc 430 + mc 750 + mc 1710 - 2*mc 430*mc 750 - 2*mc 430*mc 1710 - 2*mc 750*mc 1710 + 4*mc 430*mc 750*mc 1710) + 16384*(mc 431 + mc 751 + mc 1711 - 2*mc 431*mc 751 - 2*mc 431*mc 1711 - 2*mc 751*mc 1711 + 4*mc 431*mc 751*mc 1711) + 32768*(mc 432 + mc 752 + mc 1712 - 2*mc 432*mc 752 - 2*mc 432*mc 1712 - 2*mc 752*mc 1712 + 4*mc 432*mc 752*mc 1712) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1838, KeccakfPermAir.extraction.inter_1962, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_1961 c row = (mc 418 + mc 738 + mc 1698 - 2*mc 418*mc 738 - 2*mc 418*mc 1698 - 2*mc 738*mc 1698 + 4*mc 418*mc 738*mc 1698) + 2 * KeccakfPermAir.extraction.inter_1959 c row := by
    simp only [KeccakfPermAir.extraction.inter_1961, KeccakfPermAir.extraction.inter_1960, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_1959 c row = (mc 419 + mc 739 + mc 1699 - 2*mc 419*mc 739 - 2*mc 419*mc 1699 - 2*mc 739*mc 1699 + 4*mc 419*mc 739*mc 1699) + 2 * KeccakfPermAir.extraction.inter_1957 c row := by
    simp only [KeccakfPermAir.extraction.inter_1959, KeccakfPermAir.extraction.inter_1958, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_1957 c row = (mc 420 + mc 740 + mc 1700 - 2*mc 420*mc 740 - 2*mc 420*mc 1700 - 2*mc 740*mc 1700 + 4*mc 420*mc 740*mc 1700) + 2 * KeccakfPermAir.extraction.inter_1955 c row := by
    simp only [KeccakfPermAir.extraction.inter_1957, KeccakfPermAir.extraction.inter_1956, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_1955 c row = (mc 421 + mc 741 + mc 1701 - 2*mc 421*mc 741 - 2*mc 421*mc 1701 - 2*mc 741*mc 1701 + 4*mc 421*mc 741*mc 1701) + 2 * KeccakfPermAir.extraction.inter_1953 c row := by
    simp only [KeccakfPermAir.extraction.inter_1955, KeccakfPermAir.extraction.inter_1954, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_1953 c row = (mc 422 + mc 742 + mc 1702 - 2*mc 422*mc 742 - 2*mc 422*mc 1702 - 2*mc 742*mc 1702 + 4*mc 422*mc 742*mc 1702) + 2 * KeccakfPermAir.extraction.inter_1951 c row := by
    simp only [KeccakfPermAir.extraction.inter_1953, KeccakfPermAir.extraction.inter_1952, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_1951 c row = (mc 423 + mc 743 + mc 1703 - 2*mc 423*mc 743 - 2*mc 423*mc 1703 - 2*mc 743*mc 1703 + 4*mc 423*mc 743*mc 1703) + 2 * KeccakfPermAir.extraction.inter_1949 c row := by
    simp only [KeccakfPermAir.extraction.inter_1951, KeccakfPermAir.extraction.inter_1950, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_1949 c row = (mc 424 + mc 744 + mc 1704 - 2*mc 424*mc 744 - 2*mc 424*mc 1704 - 2*mc 744*mc 1704 + 4*mc 424*mc 744*mc 1704) + 2 * KeccakfPermAir.extraction.inter_1947 c row := by
    simp only [KeccakfPermAir.extraction.inter_1949, KeccakfPermAir.extraction.inter_1948, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_1947 c row = (mc 425 + mc 745 + mc 1705 - 2*mc 425*mc 745 - 2*mc 425*mc 1705 - 2*mc 745*mc 1705 + 4*mc 425*mc 745*mc 1705) + 2 * KeccakfPermAir.extraction.inter_1945 c row := by
    simp only [KeccakfPermAir.extraction.inter_1947, KeccakfPermAir.extraction.inter_1946, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_1945 c row = (mc 426 + mc 746 + mc 1706 - 2*mc 426*mc 746 - 2*mc 426*mc 1706 - 2*mc 746*mc 1706 + 4*mc 426*mc 746*mc 1706) + 2 * KeccakfPermAir.extraction.inter_1943 c row := by
    simp only [KeccakfPermAir.extraction.inter_1945, KeccakfPermAir.extraction.inter_1944, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_1943 c row = (mc 427 + mc 747 + mc 1707 - 2*mc 427*mc 747 - 2*mc 427*mc 1707 - 2*mc 747*mc 1707 + 4*mc 427*mc 747*mc 1707) + 2 * KeccakfPermAir.extraction.inter_1941 c row := by
    simp only [KeccakfPermAir.extraction.inter_1943, KeccakfPermAir.extraction.inter_1942, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_1941 c row = (mc 428 + mc 748 + mc 1708 - 2*mc 428*mc 748 - 2*mc 428*mc 1708 - 2*mc 748*mc 1708 + 4*mc 428*mc 748*mc 1708) + 2 * KeccakfPermAir.extraction.inter_1939 c row := by
    simp only [KeccakfPermAir.extraction.inter_1941, KeccakfPermAir.extraction.inter_1940, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_1939 c row = (mc 429 + mc 749 + mc 1709 - 2*mc 429*mc 749 - 2*mc 429*mc 1709 - 2*mc 749*mc 1709 + 4*mc 429*mc 749*mc 1709) + 2 * KeccakfPermAir.extraction.inter_1937 c row := by
    simp only [KeccakfPermAir.extraction.inter_1939, KeccakfPermAir.extraction.inter_1938, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_1937 c row = (mc 430 + mc 750 + mc 1710 - 2*mc 430*mc 750 - 2*mc 430*mc 1710 - 2*mc 750*mc 1710 + 4*mc 430*mc 750*mc 1710) + 2 * KeccakfPermAir.extraction.inter_1935 c row := by
    simp only [KeccakfPermAir.extraction.inter_1937, KeccakfPermAir.extraction.inter_1936, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_1935 c row = (mc 431 + mc 751 + mc 1711 - 2*mc 431*mc 751 - 2*mc 431*mc 1711 - 2*mc 751*mc 1711 + 4*mc 431*mc 751*mc 1711) + 2 * KeccakfPermAir.extraction.inter_1933 c row := by
    simp only [KeccakfPermAir.extraction.inter_1935, KeccakfPermAir.extraction.inter_1934, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_1933 c row = (mc 432 + mc 752 + mc 1712 - 2*mc 432*mc 752 - 2*mc 432*mc 1712 - 2*mc 752*mc 1712 + 4*mc 432*mc 752*mc 1712) := by
    simp only [KeccakfPermAir.extraction.inter_1933, KeccakfPermAir.extraction.inter_1932, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1839 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 433 753 1713 178 row) :
    mc 178 = (mc 433 + mc 753 + mc 1713 - 2*mc 433*mc 753 - 2*mc 433*mc 1713 - 2*mc 753*mc 1713 + 4*mc 433*mc 753*mc 1713) + 2*(mc 434 + mc 754 + mc 1714 - 2*mc 434*mc 754 - 2*mc 434*mc 1714 - 2*mc 754*mc 1714 + 4*mc 434*mc 754*mc 1714) + 4*(mc 435 + mc 755 + mc 1715 - 2*mc 435*mc 755 - 2*mc 435*mc 1715 - 2*mc 755*mc 1715 + 4*mc 435*mc 755*mc 1715) + 8*(mc 436 + mc 756 + mc 1716 - 2*mc 436*mc 756 - 2*mc 436*mc 1716 - 2*mc 756*mc 1716 + 4*mc 436*mc 756*mc 1716) + 16*(mc 437 + mc 757 + mc 1717 - 2*mc 437*mc 757 - 2*mc 437*mc 1717 - 2*mc 757*mc 1717 + 4*mc 437*mc 757*mc 1717) + 32*(mc 438 + mc 758 + mc 1718 - 2*mc 438*mc 758 - 2*mc 438*mc 1718 - 2*mc 758*mc 1718 + 4*mc 438*mc 758*mc 1718) + 64*(mc 439 + mc 759 + mc 1719 - 2*mc 439*mc 759 - 2*mc 439*mc 1719 - 2*mc 759*mc 1719 + 4*mc 439*mc 759*mc 1719) + 128*(mc 440 + mc 760 + mc 1720 - 2*mc 440*mc 760 - 2*mc 440*mc 1720 - 2*mc 760*mc 1720 + 4*mc 440*mc 760*mc 1720) + 256*(mc 441 + mc 761 + mc 1721 - 2*mc 441*mc 761 - 2*mc 441*mc 1721 - 2*mc 761*mc 1721 + 4*mc 441*mc 761*mc 1721) + 512*(mc 442 + mc 762 + mc 1722 - 2*mc 442*mc 762 - 2*mc 442*mc 1722 - 2*mc 762*mc 1722 + 4*mc 442*mc 762*mc 1722) + 1024*(mc 443 + mc 763 + mc 1723 - 2*mc 443*mc 763 - 2*mc 443*mc 1723 - 2*mc 763*mc 1723 + 4*mc 443*mc 763*mc 1723) + 2048*(mc 444 + mc 764 + mc 1724 - 2*mc 444*mc 764 - 2*mc 444*mc 1724 - 2*mc 764*mc 1724 + 4*mc 444*mc 764*mc 1724) + 4096*(mc 445 + mc 765 + mc 1725 - 2*mc 445*mc 765 - 2*mc 445*mc 1725 - 2*mc 765*mc 1725 + 4*mc 445*mc 765*mc 1725) + 8192*(mc 446 + mc 766 + mc 1726 - 2*mc 446*mc 766 - 2*mc 446*mc 1726 - 2*mc 766*mc 1726 + 4*mc 446*mc 766*mc 1726) + 16384*(mc 447 + mc 767 + mc 1727 - 2*mc 447*mc 767 - 2*mc 447*mc 1727 - 2*mc 767*mc 1727 + 4*mc 447*mc 767*mc 1727) + 32768*(mc 448 + mc 768 + mc 1728 - 2*mc 448*mc 768 - 2*mc 448*mc 1728 - 2*mc 768*mc 1728 + 4*mc 448*mc 768*mc 1728) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1839, KeccakfPermAir.extraction.inter_1993, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_1992 c row = (mc 434 + mc 754 + mc 1714 - 2*mc 434*mc 754 - 2*mc 434*mc 1714 - 2*mc 754*mc 1714 + 4*mc 434*mc 754*mc 1714) + 2 * KeccakfPermAir.extraction.inter_1990 c row := by
    simp only [KeccakfPermAir.extraction.inter_1992, KeccakfPermAir.extraction.inter_1991, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_1990 c row = (mc 435 + mc 755 + mc 1715 - 2*mc 435*mc 755 - 2*mc 435*mc 1715 - 2*mc 755*mc 1715 + 4*mc 435*mc 755*mc 1715) + 2 * KeccakfPermAir.extraction.inter_1988 c row := by
    simp only [KeccakfPermAir.extraction.inter_1990, KeccakfPermAir.extraction.inter_1989, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_1988 c row = (mc 436 + mc 756 + mc 1716 - 2*mc 436*mc 756 - 2*mc 436*mc 1716 - 2*mc 756*mc 1716 + 4*mc 436*mc 756*mc 1716) + 2 * KeccakfPermAir.extraction.inter_1986 c row := by
    simp only [KeccakfPermAir.extraction.inter_1988, KeccakfPermAir.extraction.inter_1987, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_1986 c row = (mc 437 + mc 757 + mc 1717 - 2*mc 437*mc 757 - 2*mc 437*mc 1717 - 2*mc 757*mc 1717 + 4*mc 437*mc 757*mc 1717) + 2 * KeccakfPermAir.extraction.inter_1984 c row := by
    simp only [KeccakfPermAir.extraction.inter_1986, KeccakfPermAir.extraction.inter_1985, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_1984 c row = (mc 438 + mc 758 + mc 1718 - 2*mc 438*mc 758 - 2*mc 438*mc 1718 - 2*mc 758*mc 1718 + 4*mc 438*mc 758*mc 1718) + 2 * KeccakfPermAir.extraction.inter_1982 c row := by
    simp only [KeccakfPermAir.extraction.inter_1984, KeccakfPermAir.extraction.inter_1983, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_1982 c row = (mc 439 + mc 759 + mc 1719 - 2*mc 439*mc 759 - 2*mc 439*mc 1719 - 2*mc 759*mc 1719 + 4*mc 439*mc 759*mc 1719) + 2 * KeccakfPermAir.extraction.inter_1980 c row := by
    simp only [KeccakfPermAir.extraction.inter_1982, KeccakfPermAir.extraction.inter_1981, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_1980 c row = (mc 440 + mc 760 + mc 1720 - 2*mc 440*mc 760 - 2*mc 440*mc 1720 - 2*mc 760*mc 1720 + 4*mc 440*mc 760*mc 1720) + 2 * KeccakfPermAir.extraction.inter_1978 c row := by
    simp only [KeccakfPermAir.extraction.inter_1980, KeccakfPermAir.extraction.inter_1979, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_1978 c row = (mc 441 + mc 761 + mc 1721 - 2*mc 441*mc 761 - 2*mc 441*mc 1721 - 2*mc 761*mc 1721 + 4*mc 441*mc 761*mc 1721) + 2 * KeccakfPermAir.extraction.inter_1976 c row := by
    simp only [KeccakfPermAir.extraction.inter_1978, KeccakfPermAir.extraction.inter_1977, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_1976 c row = (mc 442 + mc 762 + mc 1722 - 2*mc 442*mc 762 - 2*mc 442*mc 1722 - 2*mc 762*mc 1722 + 4*mc 442*mc 762*mc 1722) + 2 * KeccakfPermAir.extraction.inter_1974 c row := by
    simp only [KeccakfPermAir.extraction.inter_1976, KeccakfPermAir.extraction.inter_1975, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_1974 c row = (mc 443 + mc 763 + mc 1723 - 2*mc 443*mc 763 - 2*mc 443*mc 1723 - 2*mc 763*mc 1723 + 4*mc 443*mc 763*mc 1723) + 2 * KeccakfPermAir.extraction.inter_1972 c row := by
    simp only [KeccakfPermAir.extraction.inter_1974, KeccakfPermAir.extraction.inter_1973, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_1972 c row = (mc 444 + mc 764 + mc 1724 - 2*mc 444*mc 764 - 2*mc 444*mc 1724 - 2*mc 764*mc 1724 + 4*mc 444*mc 764*mc 1724) + 2 * KeccakfPermAir.extraction.inter_1970 c row := by
    simp only [KeccakfPermAir.extraction.inter_1972, KeccakfPermAir.extraction.inter_1971, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_1970 c row = (mc 445 + mc 765 + mc 1725 - 2*mc 445*mc 765 - 2*mc 445*mc 1725 - 2*mc 765*mc 1725 + 4*mc 445*mc 765*mc 1725) + 2 * KeccakfPermAir.extraction.inter_1968 c row := by
    simp only [KeccakfPermAir.extraction.inter_1970, KeccakfPermAir.extraction.inter_1969, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_1968 c row = (mc 446 + mc 766 + mc 1726 - 2*mc 446*mc 766 - 2*mc 446*mc 1726 - 2*mc 766*mc 1726 + 4*mc 446*mc 766*mc 1726) + 2 * KeccakfPermAir.extraction.inter_1966 c row := by
    simp only [KeccakfPermAir.extraction.inter_1968, KeccakfPermAir.extraction.inter_1967, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_1966 c row = (mc 447 + mc 767 + mc 1727 - 2*mc 447*mc 767 - 2*mc 447*mc 1727 - 2*mc 767*mc 1727 + 4*mc 447*mc 767*mc 1727) + 2 * KeccakfPermAir.extraction.inter_1964 c row := by
    simp only [KeccakfPermAir.extraction.inter_1966, KeccakfPermAir.extraction.inter_1965, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_1964 c row = (mc 448 + mc 768 + mc 1728 - 2*mc 448*mc 768 - 2*mc 448*mc 1728 - 2*mc 768*mc 1728 + 4*mc 448*mc 768*mc 1728) := by
    simp only [KeccakfPermAir.extraction.inter_1964, KeccakfPermAir.extraction.inter_1963, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1840 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 449 769 1729 179 row) :
    mc 179 = (mc 449 + mc 769 + mc 1729 - 2*mc 449*mc 769 - 2*mc 449*mc 1729 - 2*mc 769*mc 1729 + 4*mc 449*mc 769*mc 1729) + 2*(mc 450 + mc 770 + mc 1730 - 2*mc 450*mc 770 - 2*mc 450*mc 1730 - 2*mc 770*mc 1730 + 4*mc 450*mc 770*mc 1730) + 4*(mc 451 + mc 771 + mc 1731 - 2*mc 451*mc 771 - 2*mc 451*mc 1731 - 2*mc 771*mc 1731 + 4*mc 451*mc 771*mc 1731) + 8*(mc 452 + mc 772 + mc 1732 - 2*mc 452*mc 772 - 2*mc 452*mc 1732 - 2*mc 772*mc 1732 + 4*mc 452*mc 772*mc 1732) + 16*(mc 453 + mc 773 + mc 1733 - 2*mc 453*mc 773 - 2*mc 453*mc 1733 - 2*mc 773*mc 1733 + 4*mc 453*mc 773*mc 1733) + 32*(mc 454 + mc 774 + mc 1734 - 2*mc 454*mc 774 - 2*mc 454*mc 1734 - 2*mc 774*mc 1734 + 4*mc 454*mc 774*mc 1734) + 64*(mc 455 + mc 775 + mc 1735 - 2*mc 455*mc 775 - 2*mc 455*mc 1735 - 2*mc 775*mc 1735 + 4*mc 455*mc 775*mc 1735) + 128*(mc 456 + mc 776 + mc 1736 - 2*mc 456*mc 776 - 2*mc 456*mc 1736 - 2*mc 776*mc 1736 + 4*mc 456*mc 776*mc 1736) + 256*(mc 457 + mc 777 + mc 1737 - 2*mc 457*mc 777 - 2*mc 457*mc 1737 - 2*mc 777*mc 1737 + 4*mc 457*mc 777*mc 1737) + 512*(mc 458 + mc 778 + mc 1738 - 2*mc 458*mc 778 - 2*mc 458*mc 1738 - 2*mc 778*mc 1738 + 4*mc 458*mc 778*mc 1738) + 1024*(mc 459 + mc 779 + mc 1739 - 2*mc 459*mc 779 - 2*mc 459*mc 1739 - 2*mc 779*mc 1739 + 4*mc 459*mc 779*mc 1739) + 2048*(mc 460 + mc 780 + mc 1740 - 2*mc 460*mc 780 - 2*mc 460*mc 1740 - 2*mc 780*mc 1740 + 4*mc 460*mc 780*mc 1740) + 4096*(mc 461 + mc 781 + mc 1741 - 2*mc 461*mc 781 - 2*mc 461*mc 1741 - 2*mc 781*mc 1741 + 4*mc 461*mc 781*mc 1741) + 8192*(mc 462 + mc 782 + mc 1742 - 2*mc 462*mc 782 - 2*mc 462*mc 1742 - 2*mc 782*mc 1742 + 4*mc 462*mc 782*mc 1742) + 16384*(mc 463 + mc 783 + mc 1743 - 2*mc 463*mc 783 - 2*mc 463*mc 1743 - 2*mc 783*mc 1743 + 4*mc 463*mc 783*mc 1743) + 32768*(mc 464 + mc 784 + mc 1744 - 2*mc 464*mc 784 - 2*mc 464*mc 1744 - 2*mc 784*mc 1744 + 4*mc 464*mc 784*mc 1744) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1840, KeccakfPermAir.extraction.inter_2024, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_2023 c row = (mc 450 + mc 770 + mc 1730 - 2*mc 450*mc 770 - 2*mc 450*mc 1730 - 2*mc 770*mc 1730 + 4*mc 450*mc 770*mc 1730) + 2 * KeccakfPermAir.extraction.inter_2021 c row := by
    simp only [KeccakfPermAir.extraction.inter_2023, KeccakfPermAir.extraction.inter_2022, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_2021 c row = (mc 451 + mc 771 + mc 1731 - 2*mc 451*mc 771 - 2*mc 451*mc 1731 - 2*mc 771*mc 1731 + 4*mc 451*mc 771*mc 1731) + 2 * KeccakfPermAir.extraction.inter_2019 c row := by
    simp only [KeccakfPermAir.extraction.inter_2021, KeccakfPermAir.extraction.inter_2020, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_2019 c row = (mc 452 + mc 772 + mc 1732 - 2*mc 452*mc 772 - 2*mc 452*mc 1732 - 2*mc 772*mc 1732 + 4*mc 452*mc 772*mc 1732) + 2 * KeccakfPermAir.extraction.inter_2017 c row := by
    simp only [KeccakfPermAir.extraction.inter_2019, KeccakfPermAir.extraction.inter_2018, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_2017 c row = (mc 453 + mc 773 + mc 1733 - 2*mc 453*mc 773 - 2*mc 453*mc 1733 - 2*mc 773*mc 1733 + 4*mc 453*mc 773*mc 1733) + 2 * KeccakfPermAir.extraction.inter_2015 c row := by
    simp only [KeccakfPermAir.extraction.inter_2017, KeccakfPermAir.extraction.inter_2016, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_2015 c row = (mc 454 + mc 774 + mc 1734 - 2*mc 454*mc 774 - 2*mc 454*mc 1734 - 2*mc 774*mc 1734 + 4*mc 454*mc 774*mc 1734) + 2 * KeccakfPermAir.extraction.inter_2013 c row := by
    simp only [KeccakfPermAir.extraction.inter_2015, KeccakfPermAir.extraction.inter_2014, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_2013 c row = (mc 455 + mc 775 + mc 1735 - 2*mc 455*mc 775 - 2*mc 455*mc 1735 - 2*mc 775*mc 1735 + 4*mc 455*mc 775*mc 1735) + 2 * KeccakfPermAir.extraction.inter_2011 c row := by
    simp only [KeccakfPermAir.extraction.inter_2013, KeccakfPermAir.extraction.inter_2012, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_2011 c row = (mc 456 + mc 776 + mc 1736 - 2*mc 456*mc 776 - 2*mc 456*mc 1736 - 2*mc 776*mc 1736 + 4*mc 456*mc 776*mc 1736) + 2 * KeccakfPermAir.extraction.inter_2009 c row := by
    simp only [KeccakfPermAir.extraction.inter_2011, KeccakfPermAir.extraction.inter_2010, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_2009 c row = (mc 457 + mc 777 + mc 1737 - 2*mc 457*mc 777 - 2*mc 457*mc 1737 - 2*mc 777*mc 1737 + 4*mc 457*mc 777*mc 1737) + 2 * KeccakfPermAir.extraction.inter_2007 c row := by
    simp only [KeccakfPermAir.extraction.inter_2009, KeccakfPermAir.extraction.inter_2008, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_2007 c row = (mc 458 + mc 778 + mc 1738 - 2*mc 458*mc 778 - 2*mc 458*mc 1738 - 2*mc 778*mc 1738 + 4*mc 458*mc 778*mc 1738) + 2 * KeccakfPermAir.extraction.inter_2005 c row := by
    simp only [KeccakfPermAir.extraction.inter_2007, KeccakfPermAir.extraction.inter_2006, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_2005 c row = (mc 459 + mc 779 + mc 1739 - 2*mc 459*mc 779 - 2*mc 459*mc 1739 - 2*mc 779*mc 1739 + 4*mc 459*mc 779*mc 1739) + 2 * KeccakfPermAir.extraction.inter_2003 c row := by
    simp only [KeccakfPermAir.extraction.inter_2005, KeccakfPermAir.extraction.inter_2004, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_2003 c row = (mc 460 + mc 780 + mc 1740 - 2*mc 460*mc 780 - 2*mc 460*mc 1740 - 2*mc 780*mc 1740 + 4*mc 460*mc 780*mc 1740) + 2 * KeccakfPermAir.extraction.inter_2001 c row := by
    simp only [KeccakfPermAir.extraction.inter_2003, KeccakfPermAir.extraction.inter_2002, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_2001 c row = (mc 461 + mc 781 + mc 1741 - 2*mc 461*mc 781 - 2*mc 461*mc 1741 - 2*mc 781*mc 1741 + 4*mc 461*mc 781*mc 1741) + 2 * KeccakfPermAir.extraction.inter_1999 c row := by
    simp only [KeccakfPermAir.extraction.inter_2001, KeccakfPermAir.extraction.inter_2000, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_1999 c row = (mc 462 + mc 782 + mc 1742 - 2*mc 462*mc 782 - 2*mc 462*mc 1742 - 2*mc 782*mc 1742 + 4*mc 462*mc 782*mc 1742) + 2 * KeccakfPermAir.extraction.inter_1997 c row := by
    simp only [KeccakfPermAir.extraction.inter_1999, KeccakfPermAir.extraction.inter_1998, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_1997 c row = (mc 463 + mc 783 + mc 1743 - 2*mc 463*mc 783 - 2*mc 463*mc 1743 - 2*mc 783*mc 1743 + 4*mc 463*mc 783*mc 1743) + 2 * KeccakfPermAir.extraction.inter_1995 c row := by
    simp only [KeccakfPermAir.extraction.inter_1997, KeccakfPermAir.extraction.inter_1996, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_1995 c row = (mc 464 + mc 784 + mc 1744 - 2*mc 464*mc 784 - 2*mc 464*mc 1744 - 2*mc 784*mc 1744 + 4*mc 464*mc 784*mc 1744) := by
    simp only [KeccakfPermAir.extraction.inter_1995, KeccakfPermAir.extraction.inter_1994, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1841 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 465 785 1745 180 row) :
    mc 180 = (mc 465 + mc 785 + mc 1745 - 2*mc 465*mc 785 - 2*mc 465*mc 1745 - 2*mc 785*mc 1745 + 4*mc 465*mc 785*mc 1745) + 2*(mc 466 + mc 786 + mc 1746 - 2*mc 466*mc 786 - 2*mc 466*mc 1746 - 2*mc 786*mc 1746 + 4*mc 466*mc 786*mc 1746) + 4*(mc 467 + mc 787 + mc 1747 - 2*mc 467*mc 787 - 2*mc 467*mc 1747 - 2*mc 787*mc 1747 + 4*mc 467*mc 787*mc 1747) + 8*(mc 468 + mc 788 + mc 1748 - 2*mc 468*mc 788 - 2*mc 468*mc 1748 - 2*mc 788*mc 1748 + 4*mc 468*mc 788*mc 1748) + 16*(mc 469 + mc 789 + mc 1749 - 2*mc 469*mc 789 - 2*mc 469*mc 1749 - 2*mc 789*mc 1749 + 4*mc 469*mc 789*mc 1749) + 32*(mc 470 + mc 790 + mc 1750 - 2*mc 470*mc 790 - 2*mc 470*mc 1750 - 2*mc 790*mc 1750 + 4*mc 470*mc 790*mc 1750) + 64*(mc 471 + mc 791 + mc 1751 - 2*mc 471*mc 791 - 2*mc 471*mc 1751 - 2*mc 791*mc 1751 + 4*mc 471*mc 791*mc 1751) + 128*(mc 472 + mc 792 + mc 1752 - 2*mc 472*mc 792 - 2*mc 472*mc 1752 - 2*mc 792*mc 1752 + 4*mc 472*mc 792*mc 1752) + 256*(mc 473 + mc 793 + mc 1753 - 2*mc 473*mc 793 - 2*mc 473*mc 1753 - 2*mc 793*mc 1753 + 4*mc 473*mc 793*mc 1753) + 512*(mc 474 + mc 794 + mc 1754 - 2*mc 474*mc 794 - 2*mc 474*mc 1754 - 2*mc 794*mc 1754 + 4*mc 474*mc 794*mc 1754) + 1024*(mc 475 + mc 795 + mc 1755 - 2*mc 475*mc 795 - 2*mc 475*mc 1755 - 2*mc 795*mc 1755 + 4*mc 475*mc 795*mc 1755) + 2048*(mc 476 + mc 796 + mc 1756 - 2*mc 476*mc 796 - 2*mc 476*mc 1756 - 2*mc 796*mc 1756 + 4*mc 476*mc 796*mc 1756) + 4096*(mc 477 + mc 797 + mc 1757 - 2*mc 477*mc 797 - 2*mc 477*mc 1757 - 2*mc 797*mc 1757 + 4*mc 477*mc 797*mc 1757) + 8192*(mc 478 + mc 798 + mc 1758 - 2*mc 478*mc 798 - 2*mc 478*mc 1758 - 2*mc 798*mc 1758 + 4*mc 478*mc 798*mc 1758) + 16384*(mc 479 + mc 799 + mc 1759 - 2*mc 479*mc 799 - 2*mc 479*mc 1759 - 2*mc 799*mc 1759 + 4*mc 479*mc 799*mc 1759) + 32768*(mc 480 + mc 800 + mc 1760 - 2*mc 480*mc 800 - 2*mc 480*mc 1760 - 2*mc 800*mc 1760 + 4*mc 480*mc 800*mc 1760) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1841, KeccakfPermAir.extraction.inter_2055, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_2054 c row = (mc 466 + mc 786 + mc 1746 - 2*mc 466*mc 786 - 2*mc 466*mc 1746 - 2*mc 786*mc 1746 + 4*mc 466*mc 786*mc 1746) + 2 * KeccakfPermAir.extraction.inter_2052 c row := by
    simp only [KeccakfPermAir.extraction.inter_2054, KeccakfPermAir.extraction.inter_2053, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_2052 c row = (mc 467 + mc 787 + mc 1747 - 2*mc 467*mc 787 - 2*mc 467*mc 1747 - 2*mc 787*mc 1747 + 4*mc 467*mc 787*mc 1747) + 2 * KeccakfPermAir.extraction.inter_2050 c row := by
    simp only [KeccakfPermAir.extraction.inter_2052, KeccakfPermAir.extraction.inter_2051, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_2050 c row = (mc 468 + mc 788 + mc 1748 - 2*mc 468*mc 788 - 2*mc 468*mc 1748 - 2*mc 788*mc 1748 + 4*mc 468*mc 788*mc 1748) + 2 * KeccakfPermAir.extraction.inter_2048 c row := by
    simp only [KeccakfPermAir.extraction.inter_2050, KeccakfPermAir.extraction.inter_2049, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_2048 c row = (mc 469 + mc 789 + mc 1749 - 2*mc 469*mc 789 - 2*mc 469*mc 1749 - 2*mc 789*mc 1749 + 4*mc 469*mc 789*mc 1749) + 2 * KeccakfPermAir.extraction.inter_2046 c row := by
    simp only [KeccakfPermAir.extraction.inter_2048, KeccakfPermAir.extraction.inter_2047, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_2046 c row = (mc 470 + mc 790 + mc 1750 - 2*mc 470*mc 790 - 2*mc 470*mc 1750 - 2*mc 790*mc 1750 + 4*mc 470*mc 790*mc 1750) + 2 * KeccakfPermAir.extraction.inter_2044 c row := by
    simp only [KeccakfPermAir.extraction.inter_2046, KeccakfPermAir.extraction.inter_2045, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_2044 c row = (mc 471 + mc 791 + mc 1751 - 2*mc 471*mc 791 - 2*mc 471*mc 1751 - 2*mc 791*mc 1751 + 4*mc 471*mc 791*mc 1751) + 2 * KeccakfPermAir.extraction.inter_2042 c row := by
    simp only [KeccakfPermAir.extraction.inter_2044, KeccakfPermAir.extraction.inter_2043, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_2042 c row = (mc 472 + mc 792 + mc 1752 - 2*mc 472*mc 792 - 2*mc 472*mc 1752 - 2*mc 792*mc 1752 + 4*mc 472*mc 792*mc 1752) + 2 * KeccakfPermAir.extraction.inter_2040 c row := by
    simp only [KeccakfPermAir.extraction.inter_2042, KeccakfPermAir.extraction.inter_2041, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_2040 c row = (mc 473 + mc 793 + mc 1753 - 2*mc 473*mc 793 - 2*mc 473*mc 1753 - 2*mc 793*mc 1753 + 4*mc 473*mc 793*mc 1753) + 2 * KeccakfPermAir.extraction.inter_2038 c row := by
    simp only [KeccakfPermAir.extraction.inter_2040, KeccakfPermAir.extraction.inter_2039, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_2038 c row = (mc 474 + mc 794 + mc 1754 - 2*mc 474*mc 794 - 2*mc 474*mc 1754 - 2*mc 794*mc 1754 + 4*mc 474*mc 794*mc 1754) + 2 * KeccakfPermAir.extraction.inter_2036 c row := by
    simp only [KeccakfPermAir.extraction.inter_2038, KeccakfPermAir.extraction.inter_2037, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_2036 c row = (mc 475 + mc 795 + mc 1755 - 2*mc 475*mc 795 - 2*mc 475*mc 1755 - 2*mc 795*mc 1755 + 4*mc 475*mc 795*mc 1755) + 2 * KeccakfPermAir.extraction.inter_2034 c row := by
    simp only [KeccakfPermAir.extraction.inter_2036, KeccakfPermAir.extraction.inter_2035, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_2034 c row = (mc 476 + mc 796 + mc 1756 - 2*mc 476*mc 796 - 2*mc 476*mc 1756 - 2*mc 796*mc 1756 + 4*mc 476*mc 796*mc 1756) + 2 * KeccakfPermAir.extraction.inter_2032 c row := by
    simp only [KeccakfPermAir.extraction.inter_2034, KeccakfPermAir.extraction.inter_2033, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_2032 c row = (mc 477 + mc 797 + mc 1757 - 2*mc 477*mc 797 - 2*mc 477*mc 1757 - 2*mc 797*mc 1757 + 4*mc 477*mc 797*mc 1757) + 2 * KeccakfPermAir.extraction.inter_2030 c row := by
    simp only [KeccakfPermAir.extraction.inter_2032, KeccakfPermAir.extraction.inter_2031, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_2030 c row = (mc 478 + mc 798 + mc 1758 - 2*mc 478*mc 798 - 2*mc 478*mc 1758 - 2*mc 798*mc 1758 + 4*mc 478*mc 798*mc 1758) + 2 * KeccakfPermAir.extraction.inter_2028 c row := by
    simp only [KeccakfPermAir.extraction.inter_2030, KeccakfPermAir.extraction.inter_2029, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_2028 c row = (mc 479 + mc 799 + mc 1759 - 2*mc 479*mc 799 - 2*mc 479*mc 1759 - 2*mc 799*mc 1759 + 4*mc 479*mc 799*mc 1759) + 2 * KeccakfPermAir.extraction.inter_2026 c row := by
    simp only [KeccakfPermAir.extraction.inter_2028, KeccakfPermAir.extraction.inter_2027, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_2026 c row = (mc 480 + mc 800 + mc 1760 - 2*mc 480*mc 800 - 2*mc 480*mc 1760 - 2*mc 800*mc 1760 + 4*mc 480*mc 800*mc 1760) := by
    simp only [KeccakfPermAir.extraction.inter_2026, KeccakfPermAir.extraction.inter_2025, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1906 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 481 801 1761 181 row) :
    mc 181 = (mc 481 + mc 801 + mc 1761 - 2*mc 481*mc 801 - 2*mc 481*mc 1761 - 2*mc 801*mc 1761 + 4*mc 481*mc 801*mc 1761) + 2*(mc 482 + mc 802 + mc 1762 - 2*mc 482*mc 802 - 2*mc 482*mc 1762 - 2*mc 802*mc 1762 + 4*mc 482*mc 802*mc 1762) + 4*(mc 483 + mc 803 + mc 1763 - 2*mc 483*mc 803 - 2*mc 483*mc 1763 - 2*mc 803*mc 1763 + 4*mc 483*mc 803*mc 1763) + 8*(mc 484 + mc 804 + mc 1764 - 2*mc 484*mc 804 - 2*mc 484*mc 1764 - 2*mc 804*mc 1764 + 4*mc 484*mc 804*mc 1764) + 16*(mc 485 + mc 805 + mc 1765 - 2*mc 485*mc 805 - 2*mc 485*mc 1765 - 2*mc 805*mc 1765 + 4*mc 485*mc 805*mc 1765) + 32*(mc 486 + mc 806 + mc 1766 - 2*mc 486*mc 806 - 2*mc 486*mc 1766 - 2*mc 806*mc 1766 + 4*mc 486*mc 806*mc 1766) + 64*(mc 487 + mc 807 + mc 1767 - 2*mc 487*mc 807 - 2*mc 487*mc 1767 - 2*mc 807*mc 1767 + 4*mc 487*mc 807*mc 1767) + 128*(mc 488 + mc 808 + mc 1768 - 2*mc 488*mc 808 - 2*mc 488*mc 1768 - 2*mc 808*mc 1768 + 4*mc 488*mc 808*mc 1768) + 256*(mc 489 + mc 809 + mc 1769 - 2*mc 489*mc 809 - 2*mc 489*mc 1769 - 2*mc 809*mc 1769 + 4*mc 489*mc 809*mc 1769) + 512*(mc 490 + mc 810 + mc 1770 - 2*mc 490*mc 810 - 2*mc 490*mc 1770 - 2*mc 810*mc 1770 + 4*mc 490*mc 810*mc 1770) + 1024*(mc 491 + mc 811 + mc 1771 - 2*mc 491*mc 811 - 2*mc 491*mc 1771 - 2*mc 811*mc 1771 + 4*mc 491*mc 811*mc 1771) + 2048*(mc 492 + mc 812 + mc 1772 - 2*mc 492*mc 812 - 2*mc 492*mc 1772 - 2*mc 812*mc 1772 + 4*mc 492*mc 812*mc 1772) + 4096*(mc 493 + mc 813 + mc 1773 - 2*mc 493*mc 813 - 2*mc 493*mc 1773 - 2*mc 813*mc 1773 + 4*mc 493*mc 813*mc 1773) + 8192*(mc 494 + mc 814 + mc 1774 - 2*mc 494*mc 814 - 2*mc 494*mc 1774 - 2*mc 814*mc 1774 + 4*mc 494*mc 814*mc 1774) + 16384*(mc 495 + mc 815 + mc 1775 - 2*mc 495*mc 815 - 2*mc 495*mc 1775 - 2*mc 815*mc 1775 + 4*mc 495*mc 815*mc 1775) + 32768*(mc 496 + mc 816 + mc 1776 - 2*mc 496*mc 816 - 2*mc 496*mc 1776 - 2*mc 816*mc 1776 + 4*mc 496*mc 816*mc 1776) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1906, KeccakfPermAir.extraction.inter_2086, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_2085 c row = (mc 482 + mc 802 + mc 1762 - 2*mc 482*mc 802 - 2*mc 482*mc 1762 - 2*mc 802*mc 1762 + 4*mc 482*mc 802*mc 1762) + 2 * KeccakfPermAir.extraction.inter_2083 c row := by
    simp only [KeccakfPermAir.extraction.inter_2085, KeccakfPermAir.extraction.inter_2084, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_2083 c row = (mc 483 + mc 803 + mc 1763 - 2*mc 483*mc 803 - 2*mc 483*mc 1763 - 2*mc 803*mc 1763 + 4*mc 483*mc 803*mc 1763) + 2 * KeccakfPermAir.extraction.inter_2081 c row := by
    simp only [KeccakfPermAir.extraction.inter_2083, KeccakfPermAir.extraction.inter_2082, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_2081 c row = (mc 484 + mc 804 + mc 1764 - 2*mc 484*mc 804 - 2*mc 484*mc 1764 - 2*mc 804*mc 1764 + 4*mc 484*mc 804*mc 1764) + 2 * KeccakfPermAir.extraction.inter_2079 c row := by
    simp only [KeccakfPermAir.extraction.inter_2081, KeccakfPermAir.extraction.inter_2080, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_2079 c row = (mc 485 + mc 805 + mc 1765 - 2*mc 485*mc 805 - 2*mc 485*mc 1765 - 2*mc 805*mc 1765 + 4*mc 485*mc 805*mc 1765) + 2 * KeccakfPermAir.extraction.inter_2077 c row := by
    simp only [KeccakfPermAir.extraction.inter_2079, KeccakfPermAir.extraction.inter_2078, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_2077 c row = (mc 486 + mc 806 + mc 1766 - 2*mc 486*mc 806 - 2*mc 486*mc 1766 - 2*mc 806*mc 1766 + 4*mc 486*mc 806*mc 1766) + 2 * KeccakfPermAir.extraction.inter_2075 c row := by
    simp only [KeccakfPermAir.extraction.inter_2077, KeccakfPermAir.extraction.inter_2076, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_2075 c row = (mc 487 + mc 807 + mc 1767 - 2*mc 487*mc 807 - 2*mc 487*mc 1767 - 2*mc 807*mc 1767 + 4*mc 487*mc 807*mc 1767) + 2 * KeccakfPermAir.extraction.inter_2073 c row := by
    simp only [KeccakfPermAir.extraction.inter_2075, KeccakfPermAir.extraction.inter_2074, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_2073 c row = (mc 488 + mc 808 + mc 1768 - 2*mc 488*mc 808 - 2*mc 488*mc 1768 - 2*mc 808*mc 1768 + 4*mc 488*mc 808*mc 1768) + 2 * KeccakfPermAir.extraction.inter_2071 c row := by
    simp only [KeccakfPermAir.extraction.inter_2073, KeccakfPermAir.extraction.inter_2072, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_2071 c row = (mc 489 + mc 809 + mc 1769 - 2*mc 489*mc 809 - 2*mc 489*mc 1769 - 2*mc 809*mc 1769 + 4*mc 489*mc 809*mc 1769) + 2 * KeccakfPermAir.extraction.inter_2069 c row := by
    simp only [KeccakfPermAir.extraction.inter_2071, KeccakfPermAir.extraction.inter_2070, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_2069 c row = (mc 490 + mc 810 + mc 1770 - 2*mc 490*mc 810 - 2*mc 490*mc 1770 - 2*mc 810*mc 1770 + 4*mc 490*mc 810*mc 1770) + 2 * KeccakfPermAir.extraction.inter_2067 c row := by
    simp only [KeccakfPermAir.extraction.inter_2069, KeccakfPermAir.extraction.inter_2068, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_2067 c row = (mc 491 + mc 811 + mc 1771 - 2*mc 491*mc 811 - 2*mc 491*mc 1771 - 2*mc 811*mc 1771 + 4*mc 491*mc 811*mc 1771) + 2 * KeccakfPermAir.extraction.inter_2065 c row := by
    simp only [KeccakfPermAir.extraction.inter_2067, KeccakfPermAir.extraction.inter_2066, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_2065 c row = (mc 492 + mc 812 + mc 1772 - 2*mc 492*mc 812 - 2*mc 492*mc 1772 - 2*mc 812*mc 1772 + 4*mc 492*mc 812*mc 1772) + 2 * KeccakfPermAir.extraction.inter_2063 c row := by
    simp only [KeccakfPermAir.extraction.inter_2065, KeccakfPermAir.extraction.inter_2064, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_2063 c row = (mc 493 + mc 813 + mc 1773 - 2*mc 493*mc 813 - 2*mc 493*mc 1773 - 2*mc 813*mc 1773 + 4*mc 493*mc 813*mc 1773) + 2 * KeccakfPermAir.extraction.inter_2061 c row := by
    simp only [KeccakfPermAir.extraction.inter_2063, KeccakfPermAir.extraction.inter_2062, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_2061 c row = (mc 494 + mc 814 + mc 1774 - 2*mc 494*mc 814 - 2*mc 494*mc 1774 - 2*mc 814*mc 1774 + 4*mc 494*mc 814*mc 1774) + 2 * KeccakfPermAir.extraction.inter_2059 c row := by
    simp only [KeccakfPermAir.extraction.inter_2061, KeccakfPermAir.extraction.inter_2060, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_2059 c row = (mc 495 + mc 815 + mc 1775 - 2*mc 495*mc 815 - 2*mc 495*mc 1775 - 2*mc 815*mc 1775 + 4*mc 495*mc 815*mc 1775) + 2 * KeccakfPermAir.extraction.inter_2057 c row := by
    simp only [KeccakfPermAir.extraction.inter_2059, KeccakfPermAir.extraction.inter_2058, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_2057 c row = (mc 496 + mc 816 + mc 1776 - 2*mc 496*mc 816 - 2*mc 496*mc 1776 - 2*mc 816*mc 1776 + 4*mc 496*mc 816*mc 1776) := by
    simp only [KeccakfPermAir.extraction.inter_2057, KeccakfPermAir.extraction.inter_2056, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1907 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 497 817 1777 182 row) :
    mc 182 = (mc 497 + mc 817 + mc 1777 - 2*mc 497*mc 817 - 2*mc 497*mc 1777 - 2*mc 817*mc 1777 + 4*mc 497*mc 817*mc 1777) + 2*(mc 498 + mc 818 + mc 1778 - 2*mc 498*mc 818 - 2*mc 498*mc 1778 - 2*mc 818*mc 1778 + 4*mc 498*mc 818*mc 1778) + 4*(mc 499 + mc 819 + mc 1779 - 2*mc 499*mc 819 - 2*mc 499*mc 1779 - 2*mc 819*mc 1779 + 4*mc 499*mc 819*mc 1779) + 8*(mc 500 + mc 820 + mc 1780 - 2*mc 500*mc 820 - 2*mc 500*mc 1780 - 2*mc 820*mc 1780 + 4*mc 500*mc 820*mc 1780) + 16*(mc 501 + mc 821 + mc 1781 - 2*mc 501*mc 821 - 2*mc 501*mc 1781 - 2*mc 821*mc 1781 + 4*mc 501*mc 821*mc 1781) + 32*(mc 502 + mc 822 + mc 1782 - 2*mc 502*mc 822 - 2*mc 502*mc 1782 - 2*mc 822*mc 1782 + 4*mc 502*mc 822*mc 1782) + 64*(mc 503 + mc 823 + mc 1783 - 2*mc 503*mc 823 - 2*mc 503*mc 1783 - 2*mc 823*mc 1783 + 4*mc 503*mc 823*mc 1783) + 128*(mc 504 + mc 824 + mc 1784 - 2*mc 504*mc 824 - 2*mc 504*mc 1784 - 2*mc 824*mc 1784 + 4*mc 504*mc 824*mc 1784) + 256*(mc 505 + mc 825 + mc 1785 - 2*mc 505*mc 825 - 2*mc 505*mc 1785 - 2*mc 825*mc 1785 + 4*mc 505*mc 825*mc 1785) + 512*(mc 506 + mc 826 + mc 1786 - 2*mc 506*mc 826 - 2*mc 506*mc 1786 - 2*mc 826*mc 1786 + 4*mc 506*mc 826*mc 1786) + 1024*(mc 507 + mc 827 + mc 1787 - 2*mc 507*mc 827 - 2*mc 507*mc 1787 - 2*mc 827*mc 1787 + 4*mc 507*mc 827*mc 1787) + 2048*(mc 508 + mc 828 + mc 1788 - 2*mc 508*mc 828 - 2*mc 508*mc 1788 - 2*mc 828*mc 1788 + 4*mc 508*mc 828*mc 1788) + 4096*(mc 509 + mc 829 + mc 1789 - 2*mc 509*mc 829 - 2*mc 509*mc 1789 - 2*mc 829*mc 1789 + 4*mc 509*mc 829*mc 1789) + 8192*(mc 510 + mc 830 + mc 1790 - 2*mc 510*mc 830 - 2*mc 510*mc 1790 - 2*mc 830*mc 1790 + 4*mc 510*mc 830*mc 1790) + 16384*(mc 511 + mc 831 + mc 1791 - 2*mc 511*mc 831 - 2*mc 511*mc 1791 - 2*mc 831*mc 1791 + 4*mc 511*mc 831*mc 1791) + 32768*(mc 512 + mc 832 + mc 1792 - 2*mc 512*mc 832 - 2*mc 512*mc 1792 - 2*mc 832*mc 1792 + 4*mc 512*mc 832*mc 1792) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1907, KeccakfPermAir.extraction.inter_2117, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_2116 c row = (mc 498 + mc 818 + mc 1778 - 2*mc 498*mc 818 - 2*mc 498*mc 1778 - 2*mc 818*mc 1778 + 4*mc 498*mc 818*mc 1778) + 2 * KeccakfPermAir.extraction.inter_2114 c row := by
    simp only [KeccakfPermAir.extraction.inter_2116, KeccakfPermAir.extraction.inter_2115, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_2114 c row = (mc 499 + mc 819 + mc 1779 - 2*mc 499*mc 819 - 2*mc 499*mc 1779 - 2*mc 819*mc 1779 + 4*mc 499*mc 819*mc 1779) + 2 * KeccakfPermAir.extraction.inter_2112 c row := by
    simp only [KeccakfPermAir.extraction.inter_2114, KeccakfPermAir.extraction.inter_2113, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_2112 c row = (mc 500 + mc 820 + mc 1780 - 2*mc 500*mc 820 - 2*mc 500*mc 1780 - 2*mc 820*mc 1780 + 4*mc 500*mc 820*mc 1780) + 2 * KeccakfPermAir.extraction.inter_2110 c row := by
    simp only [KeccakfPermAir.extraction.inter_2112, KeccakfPermAir.extraction.inter_2111, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_2110 c row = (mc 501 + mc 821 + mc 1781 - 2*mc 501*mc 821 - 2*mc 501*mc 1781 - 2*mc 821*mc 1781 + 4*mc 501*mc 821*mc 1781) + 2 * KeccakfPermAir.extraction.inter_2108 c row := by
    simp only [KeccakfPermAir.extraction.inter_2110, KeccakfPermAir.extraction.inter_2109, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_2108 c row = (mc 502 + mc 822 + mc 1782 - 2*mc 502*mc 822 - 2*mc 502*mc 1782 - 2*mc 822*mc 1782 + 4*mc 502*mc 822*mc 1782) + 2 * KeccakfPermAir.extraction.inter_2106 c row := by
    simp only [KeccakfPermAir.extraction.inter_2108, KeccakfPermAir.extraction.inter_2107, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_2106 c row = (mc 503 + mc 823 + mc 1783 - 2*mc 503*mc 823 - 2*mc 503*mc 1783 - 2*mc 823*mc 1783 + 4*mc 503*mc 823*mc 1783) + 2 * KeccakfPermAir.extraction.inter_2104 c row := by
    simp only [KeccakfPermAir.extraction.inter_2106, KeccakfPermAir.extraction.inter_2105, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_2104 c row = (mc 504 + mc 824 + mc 1784 - 2*mc 504*mc 824 - 2*mc 504*mc 1784 - 2*mc 824*mc 1784 + 4*mc 504*mc 824*mc 1784) + 2 * KeccakfPermAir.extraction.inter_2102 c row := by
    simp only [KeccakfPermAir.extraction.inter_2104, KeccakfPermAir.extraction.inter_2103, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_2102 c row = (mc 505 + mc 825 + mc 1785 - 2*mc 505*mc 825 - 2*mc 505*mc 1785 - 2*mc 825*mc 1785 + 4*mc 505*mc 825*mc 1785) + 2 * KeccakfPermAir.extraction.inter_2100 c row := by
    simp only [KeccakfPermAir.extraction.inter_2102, KeccakfPermAir.extraction.inter_2101, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_2100 c row = (mc 506 + mc 826 + mc 1786 - 2*mc 506*mc 826 - 2*mc 506*mc 1786 - 2*mc 826*mc 1786 + 4*mc 506*mc 826*mc 1786) + 2 * KeccakfPermAir.extraction.inter_2098 c row := by
    simp only [KeccakfPermAir.extraction.inter_2100, KeccakfPermAir.extraction.inter_2099, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_2098 c row = (mc 507 + mc 827 + mc 1787 - 2*mc 507*mc 827 - 2*mc 507*mc 1787 - 2*mc 827*mc 1787 + 4*mc 507*mc 827*mc 1787) + 2 * KeccakfPermAir.extraction.inter_2096 c row := by
    simp only [KeccakfPermAir.extraction.inter_2098, KeccakfPermAir.extraction.inter_2097, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_2096 c row = (mc 508 + mc 828 + mc 1788 - 2*mc 508*mc 828 - 2*mc 508*mc 1788 - 2*mc 828*mc 1788 + 4*mc 508*mc 828*mc 1788) + 2 * KeccakfPermAir.extraction.inter_2094 c row := by
    simp only [KeccakfPermAir.extraction.inter_2096, KeccakfPermAir.extraction.inter_2095, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_2094 c row = (mc 509 + mc 829 + mc 1789 - 2*mc 509*mc 829 - 2*mc 509*mc 1789 - 2*mc 829*mc 1789 + 4*mc 509*mc 829*mc 1789) + 2 * KeccakfPermAir.extraction.inter_2092 c row := by
    simp only [KeccakfPermAir.extraction.inter_2094, KeccakfPermAir.extraction.inter_2093, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_2092 c row = (mc 510 + mc 830 + mc 1790 - 2*mc 510*mc 830 - 2*mc 510*mc 1790 - 2*mc 830*mc 1790 + 4*mc 510*mc 830*mc 1790) + 2 * KeccakfPermAir.extraction.inter_2090 c row := by
    simp only [KeccakfPermAir.extraction.inter_2092, KeccakfPermAir.extraction.inter_2091, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_2090 c row = (mc 511 + mc 831 + mc 1791 - 2*mc 511*mc 831 - 2*mc 511*mc 1791 - 2*mc 831*mc 1791 + 4*mc 511*mc 831*mc 1791) + 2 * KeccakfPermAir.extraction.inter_2088 c row := by
    simp only [KeccakfPermAir.extraction.inter_2090, KeccakfPermAir.extraction.inter_2089, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_2088 c row = (mc 512 + mc 832 + mc 1792 - 2*mc 512*mc 832 - 2*mc 512*mc 1792 - 2*mc 832*mc 1792 + 4*mc 512*mc 832*mc 1792) := by
    simp only [KeccakfPermAir.extraction.inter_2088, KeccakfPermAir.extraction.inter_2087, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1908 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 513 833 1793 183 row) :
    mc 183 = (mc 513 + mc 833 + mc 1793 - 2*mc 513*mc 833 - 2*mc 513*mc 1793 - 2*mc 833*mc 1793 + 4*mc 513*mc 833*mc 1793) + 2*(mc 514 + mc 834 + mc 1794 - 2*mc 514*mc 834 - 2*mc 514*mc 1794 - 2*mc 834*mc 1794 + 4*mc 514*mc 834*mc 1794) + 4*(mc 515 + mc 835 + mc 1795 - 2*mc 515*mc 835 - 2*mc 515*mc 1795 - 2*mc 835*mc 1795 + 4*mc 515*mc 835*mc 1795) + 8*(mc 516 + mc 836 + mc 1796 - 2*mc 516*mc 836 - 2*mc 516*mc 1796 - 2*mc 836*mc 1796 + 4*mc 516*mc 836*mc 1796) + 16*(mc 517 + mc 837 + mc 1797 - 2*mc 517*mc 837 - 2*mc 517*mc 1797 - 2*mc 837*mc 1797 + 4*mc 517*mc 837*mc 1797) + 32*(mc 518 + mc 838 + mc 1798 - 2*mc 518*mc 838 - 2*mc 518*mc 1798 - 2*mc 838*mc 1798 + 4*mc 518*mc 838*mc 1798) + 64*(mc 519 + mc 839 + mc 1799 - 2*mc 519*mc 839 - 2*mc 519*mc 1799 - 2*mc 839*mc 1799 + 4*mc 519*mc 839*mc 1799) + 128*(mc 520 + mc 840 + mc 1800 - 2*mc 520*mc 840 - 2*mc 520*mc 1800 - 2*mc 840*mc 1800 + 4*mc 520*mc 840*mc 1800) + 256*(mc 521 + mc 841 + mc 1801 - 2*mc 521*mc 841 - 2*mc 521*mc 1801 - 2*mc 841*mc 1801 + 4*mc 521*mc 841*mc 1801) + 512*(mc 522 + mc 842 + mc 1802 - 2*mc 522*mc 842 - 2*mc 522*mc 1802 - 2*mc 842*mc 1802 + 4*mc 522*mc 842*mc 1802) + 1024*(mc 523 + mc 843 + mc 1803 - 2*mc 523*mc 843 - 2*mc 523*mc 1803 - 2*mc 843*mc 1803 + 4*mc 523*mc 843*mc 1803) + 2048*(mc 524 + mc 844 + mc 1804 - 2*mc 524*mc 844 - 2*mc 524*mc 1804 - 2*mc 844*mc 1804 + 4*mc 524*mc 844*mc 1804) + 4096*(mc 525 + mc 845 + mc 1805 - 2*mc 525*mc 845 - 2*mc 525*mc 1805 - 2*mc 845*mc 1805 + 4*mc 525*mc 845*mc 1805) + 8192*(mc 526 + mc 846 + mc 1806 - 2*mc 526*mc 846 - 2*mc 526*mc 1806 - 2*mc 846*mc 1806 + 4*mc 526*mc 846*mc 1806) + 16384*(mc 527 + mc 847 + mc 1807 - 2*mc 527*mc 847 - 2*mc 527*mc 1807 - 2*mc 847*mc 1807 + 4*mc 527*mc 847*mc 1807) + 32768*(mc 528 + mc 848 + mc 1808 - 2*mc 528*mc 848 - 2*mc 528*mc 1808 - 2*mc 848*mc 1808 + 4*mc 528*mc 848*mc 1808) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1908, KeccakfPermAir.extraction.inter_2148, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_2147 c row = (mc 514 + mc 834 + mc 1794 - 2*mc 514*mc 834 - 2*mc 514*mc 1794 - 2*mc 834*mc 1794 + 4*mc 514*mc 834*mc 1794) + 2 * KeccakfPermAir.extraction.inter_2145 c row := by
    simp only [KeccakfPermAir.extraction.inter_2147, KeccakfPermAir.extraction.inter_2146, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_2145 c row = (mc 515 + mc 835 + mc 1795 - 2*mc 515*mc 835 - 2*mc 515*mc 1795 - 2*mc 835*mc 1795 + 4*mc 515*mc 835*mc 1795) + 2 * KeccakfPermAir.extraction.inter_2143 c row := by
    simp only [KeccakfPermAir.extraction.inter_2145, KeccakfPermAir.extraction.inter_2144, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_2143 c row = (mc 516 + mc 836 + mc 1796 - 2*mc 516*mc 836 - 2*mc 516*mc 1796 - 2*mc 836*mc 1796 + 4*mc 516*mc 836*mc 1796) + 2 * KeccakfPermAir.extraction.inter_2141 c row := by
    simp only [KeccakfPermAir.extraction.inter_2143, KeccakfPermAir.extraction.inter_2142, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_2141 c row = (mc 517 + mc 837 + mc 1797 - 2*mc 517*mc 837 - 2*mc 517*mc 1797 - 2*mc 837*mc 1797 + 4*mc 517*mc 837*mc 1797) + 2 * KeccakfPermAir.extraction.inter_2139 c row := by
    simp only [KeccakfPermAir.extraction.inter_2141, KeccakfPermAir.extraction.inter_2140, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_2139 c row = (mc 518 + mc 838 + mc 1798 - 2*mc 518*mc 838 - 2*mc 518*mc 1798 - 2*mc 838*mc 1798 + 4*mc 518*mc 838*mc 1798) + 2 * KeccakfPermAir.extraction.inter_2137 c row := by
    simp only [KeccakfPermAir.extraction.inter_2139, KeccakfPermAir.extraction.inter_2138, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_2137 c row = (mc 519 + mc 839 + mc 1799 - 2*mc 519*mc 839 - 2*mc 519*mc 1799 - 2*mc 839*mc 1799 + 4*mc 519*mc 839*mc 1799) + 2 * KeccakfPermAir.extraction.inter_2135 c row := by
    simp only [KeccakfPermAir.extraction.inter_2137, KeccakfPermAir.extraction.inter_2136, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_2135 c row = (mc 520 + mc 840 + mc 1800 - 2*mc 520*mc 840 - 2*mc 520*mc 1800 - 2*mc 840*mc 1800 + 4*mc 520*mc 840*mc 1800) + 2 * KeccakfPermAir.extraction.inter_2133 c row := by
    simp only [KeccakfPermAir.extraction.inter_2135, KeccakfPermAir.extraction.inter_2134, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_2133 c row = (mc 521 + mc 841 + mc 1801 - 2*mc 521*mc 841 - 2*mc 521*mc 1801 - 2*mc 841*mc 1801 + 4*mc 521*mc 841*mc 1801) + 2 * KeccakfPermAir.extraction.inter_2131 c row := by
    simp only [KeccakfPermAir.extraction.inter_2133, KeccakfPermAir.extraction.inter_2132, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_2131 c row = (mc 522 + mc 842 + mc 1802 - 2*mc 522*mc 842 - 2*mc 522*mc 1802 - 2*mc 842*mc 1802 + 4*mc 522*mc 842*mc 1802) + 2 * KeccakfPermAir.extraction.inter_2129 c row := by
    simp only [KeccakfPermAir.extraction.inter_2131, KeccakfPermAir.extraction.inter_2130, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_2129 c row = (mc 523 + mc 843 + mc 1803 - 2*mc 523*mc 843 - 2*mc 523*mc 1803 - 2*mc 843*mc 1803 + 4*mc 523*mc 843*mc 1803) + 2 * KeccakfPermAir.extraction.inter_2127 c row := by
    simp only [KeccakfPermAir.extraction.inter_2129, KeccakfPermAir.extraction.inter_2128, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_2127 c row = (mc 524 + mc 844 + mc 1804 - 2*mc 524*mc 844 - 2*mc 524*mc 1804 - 2*mc 844*mc 1804 + 4*mc 524*mc 844*mc 1804) + 2 * KeccakfPermAir.extraction.inter_2125 c row := by
    simp only [KeccakfPermAir.extraction.inter_2127, KeccakfPermAir.extraction.inter_2126, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_2125 c row = (mc 525 + mc 845 + mc 1805 - 2*mc 525*mc 845 - 2*mc 525*mc 1805 - 2*mc 845*mc 1805 + 4*mc 525*mc 845*mc 1805) + 2 * KeccakfPermAir.extraction.inter_2123 c row := by
    simp only [KeccakfPermAir.extraction.inter_2125, KeccakfPermAir.extraction.inter_2124, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_2123 c row = (mc 526 + mc 846 + mc 1806 - 2*mc 526*mc 846 - 2*mc 526*mc 1806 - 2*mc 846*mc 1806 + 4*mc 526*mc 846*mc 1806) + 2 * KeccakfPermAir.extraction.inter_2121 c row := by
    simp only [KeccakfPermAir.extraction.inter_2123, KeccakfPermAir.extraction.inter_2122, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_2121 c row = (mc 527 + mc 847 + mc 1807 - 2*mc 527*mc 847 - 2*mc 527*mc 1807 - 2*mc 847*mc 1807 + 4*mc 527*mc 847*mc 1807) + 2 * KeccakfPermAir.extraction.inter_2119 c row := by
    simp only [KeccakfPermAir.extraction.inter_2121, KeccakfPermAir.extraction.inter_2120, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_2119 c row = (mc 528 + mc 848 + mc 1808 - 2*mc 528*mc 848 - 2*mc 528*mc 1808 - 2*mc 848*mc 1808 + 4*mc 528*mc 848*mc 1808) := by
    simp only [KeccakfPermAir.extraction.inter_2119, KeccakfPermAir.extraction.inter_2118, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1909 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 529 849 1809 184 row) :
    mc 184 = (mc 529 + mc 849 + mc 1809 - 2*mc 529*mc 849 - 2*mc 529*mc 1809 - 2*mc 849*mc 1809 + 4*mc 529*mc 849*mc 1809) + 2*(mc 530 + mc 850 + mc 1810 - 2*mc 530*mc 850 - 2*mc 530*mc 1810 - 2*mc 850*mc 1810 + 4*mc 530*mc 850*mc 1810) + 4*(mc 531 + mc 851 + mc 1811 - 2*mc 531*mc 851 - 2*mc 531*mc 1811 - 2*mc 851*mc 1811 + 4*mc 531*mc 851*mc 1811) + 8*(mc 532 + mc 852 + mc 1812 - 2*mc 532*mc 852 - 2*mc 532*mc 1812 - 2*mc 852*mc 1812 + 4*mc 532*mc 852*mc 1812) + 16*(mc 533 + mc 853 + mc 1813 - 2*mc 533*mc 853 - 2*mc 533*mc 1813 - 2*mc 853*mc 1813 + 4*mc 533*mc 853*mc 1813) + 32*(mc 534 + mc 854 + mc 1814 - 2*mc 534*mc 854 - 2*mc 534*mc 1814 - 2*mc 854*mc 1814 + 4*mc 534*mc 854*mc 1814) + 64*(mc 535 + mc 855 + mc 1815 - 2*mc 535*mc 855 - 2*mc 535*mc 1815 - 2*mc 855*mc 1815 + 4*mc 535*mc 855*mc 1815) + 128*(mc 536 + mc 856 + mc 1816 - 2*mc 536*mc 856 - 2*mc 536*mc 1816 - 2*mc 856*mc 1816 + 4*mc 536*mc 856*mc 1816) + 256*(mc 537 + mc 857 + mc 1817 - 2*mc 537*mc 857 - 2*mc 537*mc 1817 - 2*mc 857*mc 1817 + 4*mc 537*mc 857*mc 1817) + 512*(mc 538 + mc 858 + mc 1818 - 2*mc 538*mc 858 - 2*mc 538*mc 1818 - 2*mc 858*mc 1818 + 4*mc 538*mc 858*mc 1818) + 1024*(mc 539 + mc 859 + mc 1819 - 2*mc 539*mc 859 - 2*mc 539*mc 1819 - 2*mc 859*mc 1819 + 4*mc 539*mc 859*mc 1819) + 2048*(mc 540 + mc 860 + mc 1820 - 2*mc 540*mc 860 - 2*mc 540*mc 1820 - 2*mc 860*mc 1820 + 4*mc 540*mc 860*mc 1820) + 4096*(mc 541 + mc 861 + mc 1821 - 2*mc 541*mc 861 - 2*mc 541*mc 1821 - 2*mc 861*mc 1821 + 4*mc 541*mc 861*mc 1821) + 8192*(mc 542 + mc 862 + mc 1822 - 2*mc 542*mc 862 - 2*mc 542*mc 1822 - 2*mc 862*mc 1822 + 4*mc 542*mc 862*mc 1822) + 16384*(mc 543 + mc 863 + mc 1823 - 2*mc 543*mc 863 - 2*mc 543*mc 1823 - 2*mc 863*mc 1823 + 4*mc 543*mc 863*mc 1823) + 32768*(mc 544 + mc 864 + mc 1824 - 2*mc 544*mc 864 - 2*mc 544*mc 1824 - 2*mc 864*mc 1824 + 4*mc 544*mc 864*mc 1824) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1909, KeccakfPermAir.extraction.inter_2179, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_2178 c row = (mc 530 + mc 850 + mc 1810 - 2*mc 530*mc 850 - 2*mc 530*mc 1810 - 2*mc 850*mc 1810 + 4*mc 530*mc 850*mc 1810) + 2 * KeccakfPermAir.extraction.inter_2176 c row := by
    simp only [KeccakfPermAir.extraction.inter_2178, KeccakfPermAir.extraction.inter_2177, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_2176 c row = (mc 531 + mc 851 + mc 1811 - 2*mc 531*mc 851 - 2*mc 531*mc 1811 - 2*mc 851*mc 1811 + 4*mc 531*mc 851*mc 1811) + 2 * KeccakfPermAir.extraction.inter_2174 c row := by
    simp only [KeccakfPermAir.extraction.inter_2176, KeccakfPermAir.extraction.inter_2175, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_2174 c row = (mc 532 + mc 852 + mc 1812 - 2*mc 532*mc 852 - 2*mc 532*mc 1812 - 2*mc 852*mc 1812 + 4*mc 532*mc 852*mc 1812) + 2 * KeccakfPermAir.extraction.inter_2172 c row := by
    simp only [KeccakfPermAir.extraction.inter_2174, KeccakfPermAir.extraction.inter_2173, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_2172 c row = (mc 533 + mc 853 + mc 1813 - 2*mc 533*mc 853 - 2*mc 533*mc 1813 - 2*mc 853*mc 1813 + 4*mc 533*mc 853*mc 1813) + 2 * KeccakfPermAir.extraction.inter_2170 c row := by
    simp only [KeccakfPermAir.extraction.inter_2172, KeccakfPermAir.extraction.inter_2171, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_2170 c row = (mc 534 + mc 854 + mc 1814 - 2*mc 534*mc 854 - 2*mc 534*mc 1814 - 2*mc 854*mc 1814 + 4*mc 534*mc 854*mc 1814) + 2 * KeccakfPermAir.extraction.inter_2168 c row := by
    simp only [KeccakfPermAir.extraction.inter_2170, KeccakfPermAir.extraction.inter_2169, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_2168 c row = (mc 535 + mc 855 + mc 1815 - 2*mc 535*mc 855 - 2*mc 535*mc 1815 - 2*mc 855*mc 1815 + 4*mc 535*mc 855*mc 1815) + 2 * KeccakfPermAir.extraction.inter_2166 c row := by
    simp only [KeccakfPermAir.extraction.inter_2168, KeccakfPermAir.extraction.inter_2167, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_2166 c row = (mc 536 + mc 856 + mc 1816 - 2*mc 536*mc 856 - 2*mc 536*mc 1816 - 2*mc 856*mc 1816 + 4*mc 536*mc 856*mc 1816) + 2 * KeccakfPermAir.extraction.inter_2164 c row := by
    simp only [KeccakfPermAir.extraction.inter_2166, KeccakfPermAir.extraction.inter_2165, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_2164 c row = (mc 537 + mc 857 + mc 1817 - 2*mc 537*mc 857 - 2*mc 537*mc 1817 - 2*mc 857*mc 1817 + 4*mc 537*mc 857*mc 1817) + 2 * KeccakfPermAir.extraction.inter_2162 c row := by
    simp only [KeccakfPermAir.extraction.inter_2164, KeccakfPermAir.extraction.inter_2163, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_2162 c row = (mc 538 + mc 858 + mc 1818 - 2*mc 538*mc 858 - 2*mc 538*mc 1818 - 2*mc 858*mc 1818 + 4*mc 538*mc 858*mc 1818) + 2 * KeccakfPermAir.extraction.inter_2160 c row := by
    simp only [KeccakfPermAir.extraction.inter_2162, KeccakfPermAir.extraction.inter_2161, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_2160 c row = (mc 539 + mc 859 + mc 1819 - 2*mc 539*mc 859 - 2*mc 539*mc 1819 - 2*mc 859*mc 1819 + 4*mc 539*mc 859*mc 1819) + 2 * KeccakfPermAir.extraction.inter_2158 c row := by
    simp only [KeccakfPermAir.extraction.inter_2160, KeccakfPermAir.extraction.inter_2159, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_2158 c row = (mc 540 + mc 860 + mc 1820 - 2*mc 540*mc 860 - 2*mc 540*mc 1820 - 2*mc 860*mc 1820 + 4*mc 540*mc 860*mc 1820) + 2 * KeccakfPermAir.extraction.inter_2156 c row := by
    simp only [KeccakfPermAir.extraction.inter_2158, KeccakfPermAir.extraction.inter_2157, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_2156 c row = (mc 541 + mc 861 + mc 1821 - 2*mc 541*mc 861 - 2*mc 541*mc 1821 - 2*mc 861*mc 1821 + 4*mc 541*mc 861*mc 1821) + 2 * KeccakfPermAir.extraction.inter_2154 c row := by
    simp only [KeccakfPermAir.extraction.inter_2156, KeccakfPermAir.extraction.inter_2155, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_2154 c row = (mc 542 + mc 862 + mc 1822 - 2*mc 542*mc 862 - 2*mc 542*mc 1822 - 2*mc 862*mc 1822 + 4*mc 542*mc 862*mc 1822) + 2 * KeccakfPermAir.extraction.inter_2152 c row := by
    simp only [KeccakfPermAir.extraction.inter_2154, KeccakfPermAir.extraction.inter_2153, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_2152 c row = (mc 543 + mc 863 + mc 1823 - 2*mc 543*mc 863 - 2*mc 543*mc 1823 - 2*mc 863*mc 1823 + 4*mc 543*mc 863*mc 1823) + 2 * KeccakfPermAir.extraction.inter_2150 c row := by
    simp only [KeccakfPermAir.extraction.inter_2152, KeccakfPermAir.extraction.inter_2151, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_2150 c row = (mc 544 + mc 864 + mc 1824 - 2*mc 544*mc 864 - 2*mc 544*mc 1824 - 2*mc 864*mc 1824 + 4*mc 544*mc 864*mc 1824) := by
    simp only [KeccakfPermAir.extraction.inter_2150, KeccakfPermAir.extraction.inter_2149, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1974 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 225 545 1825 185 row) :
    mc 185 = (mc 225 + mc 545 + mc 1825 - 2*mc 225*mc 545 - 2*mc 225*mc 1825 - 2*mc 545*mc 1825 + 4*mc 225*mc 545*mc 1825) + 2*(mc 226 + mc 546 + mc 1826 - 2*mc 226*mc 546 - 2*mc 226*mc 1826 - 2*mc 546*mc 1826 + 4*mc 226*mc 546*mc 1826) + 4*(mc 227 + mc 547 + mc 1827 - 2*mc 227*mc 547 - 2*mc 227*mc 1827 - 2*mc 547*mc 1827 + 4*mc 227*mc 547*mc 1827) + 8*(mc 228 + mc 548 + mc 1828 - 2*mc 228*mc 548 - 2*mc 228*mc 1828 - 2*mc 548*mc 1828 + 4*mc 228*mc 548*mc 1828) + 16*(mc 229 + mc 549 + mc 1829 - 2*mc 229*mc 549 - 2*mc 229*mc 1829 - 2*mc 549*mc 1829 + 4*mc 229*mc 549*mc 1829) + 32*(mc 230 + mc 550 + mc 1830 - 2*mc 230*mc 550 - 2*mc 230*mc 1830 - 2*mc 550*mc 1830 + 4*mc 230*mc 550*mc 1830) + 64*(mc 231 + mc 551 + mc 1831 - 2*mc 231*mc 551 - 2*mc 231*mc 1831 - 2*mc 551*mc 1831 + 4*mc 231*mc 551*mc 1831) + 128*(mc 232 + mc 552 + mc 1832 - 2*mc 232*mc 552 - 2*mc 232*mc 1832 - 2*mc 552*mc 1832 + 4*mc 232*mc 552*mc 1832) + 256*(mc 233 + mc 553 + mc 1833 - 2*mc 233*mc 553 - 2*mc 233*mc 1833 - 2*mc 553*mc 1833 + 4*mc 233*mc 553*mc 1833) + 512*(mc 234 + mc 554 + mc 1834 - 2*mc 234*mc 554 - 2*mc 234*mc 1834 - 2*mc 554*mc 1834 + 4*mc 234*mc 554*mc 1834) + 1024*(mc 235 + mc 555 + mc 1835 - 2*mc 235*mc 555 - 2*mc 235*mc 1835 - 2*mc 555*mc 1835 + 4*mc 235*mc 555*mc 1835) + 2048*(mc 236 + mc 556 + mc 1836 - 2*mc 236*mc 556 - 2*mc 236*mc 1836 - 2*mc 556*mc 1836 + 4*mc 236*mc 556*mc 1836) + 4096*(mc 237 + mc 557 + mc 1837 - 2*mc 237*mc 557 - 2*mc 237*mc 1837 - 2*mc 557*mc 1837 + 4*mc 237*mc 557*mc 1837) + 8192*(mc 238 + mc 558 + mc 1838 - 2*mc 238*mc 558 - 2*mc 238*mc 1838 - 2*mc 558*mc 1838 + 4*mc 238*mc 558*mc 1838) + 16384*(mc 239 + mc 559 + mc 1839 - 2*mc 239*mc 559 - 2*mc 239*mc 1839 - 2*mc 559*mc 1839 + 4*mc 239*mc 559*mc 1839) + 32768*(mc 240 + mc 560 + mc 1840 - 2*mc 240*mc 560 - 2*mc 240*mc 1840 - 2*mc 560*mc 1840 + 4*mc 240*mc 560*mc 1840) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1974, KeccakfPermAir.extraction.inter_2210, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_2209 c row = (mc 226 + mc 546 + mc 1826 - 2*mc 226*mc 546 - 2*mc 226*mc 1826 - 2*mc 546*mc 1826 + 4*mc 226*mc 546*mc 1826) + 2 * KeccakfPermAir.extraction.inter_2207 c row := by
    simp only [KeccakfPermAir.extraction.inter_2209, KeccakfPermAir.extraction.inter_2208, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_2207 c row = (mc 227 + mc 547 + mc 1827 - 2*mc 227*mc 547 - 2*mc 227*mc 1827 - 2*mc 547*mc 1827 + 4*mc 227*mc 547*mc 1827) + 2 * KeccakfPermAir.extraction.inter_2205 c row := by
    simp only [KeccakfPermAir.extraction.inter_2207, KeccakfPermAir.extraction.inter_2206, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_2205 c row = (mc 228 + mc 548 + mc 1828 - 2*mc 228*mc 548 - 2*mc 228*mc 1828 - 2*mc 548*mc 1828 + 4*mc 228*mc 548*mc 1828) + 2 * KeccakfPermAir.extraction.inter_2203 c row := by
    simp only [KeccakfPermAir.extraction.inter_2205, KeccakfPermAir.extraction.inter_2204, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_2203 c row = (mc 229 + mc 549 + mc 1829 - 2*mc 229*mc 549 - 2*mc 229*mc 1829 - 2*mc 549*mc 1829 + 4*mc 229*mc 549*mc 1829) + 2 * KeccakfPermAir.extraction.inter_2201 c row := by
    simp only [KeccakfPermAir.extraction.inter_2203, KeccakfPermAir.extraction.inter_2202, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_2201 c row = (mc 230 + mc 550 + mc 1830 - 2*mc 230*mc 550 - 2*mc 230*mc 1830 - 2*mc 550*mc 1830 + 4*mc 230*mc 550*mc 1830) + 2 * KeccakfPermAir.extraction.inter_2199 c row := by
    simp only [KeccakfPermAir.extraction.inter_2201, KeccakfPermAir.extraction.inter_2200, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_2199 c row = (mc 231 + mc 551 + mc 1831 - 2*mc 231*mc 551 - 2*mc 231*mc 1831 - 2*mc 551*mc 1831 + 4*mc 231*mc 551*mc 1831) + 2 * KeccakfPermAir.extraction.inter_2197 c row := by
    simp only [KeccakfPermAir.extraction.inter_2199, KeccakfPermAir.extraction.inter_2198, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_2197 c row = (mc 232 + mc 552 + mc 1832 - 2*mc 232*mc 552 - 2*mc 232*mc 1832 - 2*mc 552*mc 1832 + 4*mc 232*mc 552*mc 1832) + 2 * KeccakfPermAir.extraction.inter_2195 c row := by
    simp only [KeccakfPermAir.extraction.inter_2197, KeccakfPermAir.extraction.inter_2196, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_2195 c row = (mc 233 + mc 553 + mc 1833 - 2*mc 233*mc 553 - 2*mc 233*mc 1833 - 2*mc 553*mc 1833 + 4*mc 233*mc 553*mc 1833) + 2 * KeccakfPermAir.extraction.inter_2193 c row := by
    simp only [KeccakfPermAir.extraction.inter_2195, KeccakfPermAir.extraction.inter_2194, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_2193 c row = (mc 234 + mc 554 + mc 1834 - 2*mc 234*mc 554 - 2*mc 234*mc 1834 - 2*mc 554*mc 1834 + 4*mc 234*mc 554*mc 1834) + 2 * KeccakfPermAir.extraction.inter_2191 c row := by
    simp only [KeccakfPermAir.extraction.inter_2193, KeccakfPermAir.extraction.inter_2192, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_2191 c row = (mc 235 + mc 555 + mc 1835 - 2*mc 235*mc 555 - 2*mc 235*mc 1835 - 2*mc 555*mc 1835 + 4*mc 235*mc 555*mc 1835) + 2 * KeccakfPermAir.extraction.inter_2189 c row := by
    simp only [KeccakfPermAir.extraction.inter_2191, KeccakfPermAir.extraction.inter_2190, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_2189 c row = (mc 236 + mc 556 + mc 1836 - 2*mc 236*mc 556 - 2*mc 236*mc 1836 - 2*mc 556*mc 1836 + 4*mc 236*mc 556*mc 1836) + 2 * KeccakfPermAir.extraction.inter_2187 c row := by
    simp only [KeccakfPermAir.extraction.inter_2189, KeccakfPermAir.extraction.inter_2188, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_2187 c row = (mc 237 + mc 557 + mc 1837 - 2*mc 237*mc 557 - 2*mc 237*mc 1837 - 2*mc 557*mc 1837 + 4*mc 237*mc 557*mc 1837) + 2 * KeccakfPermAir.extraction.inter_2185 c row := by
    simp only [KeccakfPermAir.extraction.inter_2187, KeccakfPermAir.extraction.inter_2186, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_2185 c row = (mc 238 + mc 558 + mc 1838 - 2*mc 238*mc 558 - 2*mc 238*mc 1838 - 2*mc 558*mc 1838 + 4*mc 238*mc 558*mc 1838) + 2 * KeccakfPermAir.extraction.inter_2183 c row := by
    simp only [KeccakfPermAir.extraction.inter_2185, KeccakfPermAir.extraction.inter_2184, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_2183 c row = (mc 239 + mc 559 + mc 1839 - 2*mc 239*mc 559 - 2*mc 239*mc 1839 - 2*mc 559*mc 1839 + 4*mc 239*mc 559*mc 1839) + 2 * KeccakfPermAir.extraction.inter_2181 c row := by
    simp only [KeccakfPermAir.extraction.inter_2183, KeccakfPermAir.extraction.inter_2182, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_2181 c row = (mc 240 + mc 560 + mc 1840 - 2*mc 240*mc 560 - 2*mc 240*mc 1840 - 2*mc 560*mc 1840 + 4*mc 240*mc 560*mc 1840) := by
    simp only [KeccakfPermAir.extraction.inter_2181, KeccakfPermAir.extraction.inter_2180, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1975 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 241 561 1841 186 row) :
    mc 186 = (mc 241 + mc 561 + mc 1841 - 2*mc 241*mc 561 - 2*mc 241*mc 1841 - 2*mc 561*mc 1841 + 4*mc 241*mc 561*mc 1841) + 2*(mc 242 + mc 562 + mc 1842 - 2*mc 242*mc 562 - 2*mc 242*mc 1842 - 2*mc 562*mc 1842 + 4*mc 242*mc 562*mc 1842) + 4*(mc 243 + mc 563 + mc 1843 - 2*mc 243*mc 563 - 2*mc 243*mc 1843 - 2*mc 563*mc 1843 + 4*mc 243*mc 563*mc 1843) + 8*(mc 244 + mc 564 + mc 1844 - 2*mc 244*mc 564 - 2*mc 244*mc 1844 - 2*mc 564*mc 1844 + 4*mc 244*mc 564*mc 1844) + 16*(mc 245 + mc 565 + mc 1845 - 2*mc 245*mc 565 - 2*mc 245*mc 1845 - 2*mc 565*mc 1845 + 4*mc 245*mc 565*mc 1845) + 32*(mc 246 + mc 566 + mc 1846 - 2*mc 246*mc 566 - 2*mc 246*mc 1846 - 2*mc 566*mc 1846 + 4*mc 246*mc 566*mc 1846) + 64*(mc 247 + mc 567 + mc 1847 - 2*mc 247*mc 567 - 2*mc 247*mc 1847 - 2*mc 567*mc 1847 + 4*mc 247*mc 567*mc 1847) + 128*(mc 248 + mc 568 + mc 1848 - 2*mc 248*mc 568 - 2*mc 248*mc 1848 - 2*mc 568*mc 1848 + 4*mc 248*mc 568*mc 1848) + 256*(mc 249 + mc 569 + mc 1849 - 2*mc 249*mc 569 - 2*mc 249*mc 1849 - 2*mc 569*mc 1849 + 4*mc 249*mc 569*mc 1849) + 512*(mc 250 + mc 570 + mc 1850 - 2*mc 250*mc 570 - 2*mc 250*mc 1850 - 2*mc 570*mc 1850 + 4*mc 250*mc 570*mc 1850) + 1024*(mc 251 + mc 571 + mc 1851 - 2*mc 251*mc 571 - 2*mc 251*mc 1851 - 2*mc 571*mc 1851 + 4*mc 251*mc 571*mc 1851) + 2048*(mc 252 + mc 572 + mc 1852 - 2*mc 252*mc 572 - 2*mc 252*mc 1852 - 2*mc 572*mc 1852 + 4*mc 252*mc 572*mc 1852) + 4096*(mc 253 + mc 573 + mc 1853 - 2*mc 253*mc 573 - 2*mc 253*mc 1853 - 2*mc 573*mc 1853 + 4*mc 253*mc 573*mc 1853) + 8192*(mc 254 + mc 574 + mc 1854 - 2*mc 254*mc 574 - 2*mc 254*mc 1854 - 2*mc 574*mc 1854 + 4*mc 254*mc 574*mc 1854) + 16384*(mc 255 + mc 575 + mc 1855 - 2*mc 255*mc 575 - 2*mc 255*mc 1855 - 2*mc 575*mc 1855 + 4*mc 255*mc 575*mc 1855) + 32768*(mc 256 + mc 576 + mc 1856 - 2*mc 256*mc 576 - 2*mc 256*mc 1856 - 2*mc 576*mc 1856 + 4*mc 256*mc 576*mc 1856) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1975, KeccakfPermAir.extraction.inter_2241, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_2240 c row = (mc 242 + mc 562 + mc 1842 - 2*mc 242*mc 562 - 2*mc 242*mc 1842 - 2*mc 562*mc 1842 + 4*mc 242*mc 562*mc 1842) + 2 * KeccakfPermAir.extraction.inter_2238 c row := by
    simp only [KeccakfPermAir.extraction.inter_2240, KeccakfPermAir.extraction.inter_2239, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_2238 c row = (mc 243 + mc 563 + mc 1843 - 2*mc 243*mc 563 - 2*mc 243*mc 1843 - 2*mc 563*mc 1843 + 4*mc 243*mc 563*mc 1843) + 2 * KeccakfPermAir.extraction.inter_2236 c row := by
    simp only [KeccakfPermAir.extraction.inter_2238, KeccakfPermAir.extraction.inter_2237, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_2236 c row = (mc 244 + mc 564 + mc 1844 - 2*mc 244*mc 564 - 2*mc 244*mc 1844 - 2*mc 564*mc 1844 + 4*mc 244*mc 564*mc 1844) + 2 * KeccakfPermAir.extraction.inter_2234 c row := by
    simp only [KeccakfPermAir.extraction.inter_2236, KeccakfPermAir.extraction.inter_2235, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_2234 c row = (mc 245 + mc 565 + mc 1845 - 2*mc 245*mc 565 - 2*mc 245*mc 1845 - 2*mc 565*mc 1845 + 4*mc 245*mc 565*mc 1845) + 2 * KeccakfPermAir.extraction.inter_2232 c row := by
    simp only [KeccakfPermAir.extraction.inter_2234, KeccakfPermAir.extraction.inter_2233, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_2232 c row = (mc 246 + mc 566 + mc 1846 - 2*mc 246*mc 566 - 2*mc 246*mc 1846 - 2*mc 566*mc 1846 + 4*mc 246*mc 566*mc 1846) + 2 * KeccakfPermAir.extraction.inter_2230 c row := by
    simp only [KeccakfPermAir.extraction.inter_2232, KeccakfPermAir.extraction.inter_2231, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_2230 c row = (mc 247 + mc 567 + mc 1847 - 2*mc 247*mc 567 - 2*mc 247*mc 1847 - 2*mc 567*mc 1847 + 4*mc 247*mc 567*mc 1847) + 2 * KeccakfPermAir.extraction.inter_2228 c row := by
    simp only [KeccakfPermAir.extraction.inter_2230, KeccakfPermAir.extraction.inter_2229, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_2228 c row = (mc 248 + mc 568 + mc 1848 - 2*mc 248*mc 568 - 2*mc 248*mc 1848 - 2*mc 568*mc 1848 + 4*mc 248*mc 568*mc 1848) + 2 * KeccakfPermAir.extraction.inter_2226 c row := by
    simp only [KeccakfPermAir.extraction.inter_2228, KeccakfPermAir.extraction.inter_2227, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_2226 c row = (mc 249 + mc 569 + mc 1849 - 2*mc 249*mc 569 - 2*mc 249*mc 1849 - 2*mc 569*mc 1849 + 4*mc 249*mc 569*mc 1849) + 2 * KeccakfPermAir.extraction.inter_2224 c row := by
    simp only [KeccakfPermAir.extraction.inter_2226, KeccakfPermAir.extraction.inter_2225, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_2224 c row = (mc 250 + mc 570 + mc 1850 - 2*mc 250*mc 570 - 2*mc 250*mc 1850 - 2*mc 570*mc 1850 + 4*mc 250*mc 570*mc 1850) + 2 * KeccakfPermAir.extraction.inter_2222 c row := by
    simp only [KeccakfPermAir.extraction.inter_2224, KeccakfPermAir.extraction.inter_2223, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_2222 c row = (mc 251 + mc 571 + mc 1851 - 2*mc 251*mc 571 - 2*mc 251*mc 1851 - 2*mc 571*mc 1851 + 4*mc 251*mc 571*mc 1851) + 2 * KeccakfPermAir.extraction.inter_2220 c row := by
    simp only [KeccakfPermAir.extraction.inter_2222, KeccakfPermAir.extraction.inter_2221, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_2220 c row = (mc 252 + mc 572 + mc 1852 - 2*mc 252*mc 572 - 2*mc 252*mc 1852 - 2*mc 572*mc 1852 + 4*mc 252*mc 572*mc 1852) + 2 * KeccakfPermAir.extraction.inter_2218 c row := by
    simp only [KeccakfPermAir.extraction.inter_2220, KeccakfPermAir.extraction.inter_2219, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_2218 c row = (mc 253 + mc 573 + mc 1853 - 2*mc 253*mc 573 - 2*mc 253*mc 1853 - 2*mc 573*mc 1853 + 4*mc 253*mc 573*mc 1853) + 2 * KeccakfPermAir.extraction.inter_2216 c row := by
    simp only [KeccakfPermAir.extraction.inter_2218, KeccakfPermAir.extraction.inter_2217, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_2216 c row = (mc 254 + mc 574 + mc 1854 - 2*mc 254*mc 574 - 2*mc 254*mc 1854 - 2*mc 574*mc 1854 + 4*mc 254*mc 574*mc 1854) + 2 * KeccakfPermAir.extraction.inter_2214 c row := by
    simp only [KeccakfPermAir.extraction.inter_2216, KeccakfPermAir.extraction.inter_2215, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_2214 c row = (mc 255 + mc 575 + mc 1855 - 2*mc 255*mc 575 - 2*mc 255*mc 1855 - 2*mc 575*mc 1855 + 4*mc 255*mc 575*mc 1855) + 2 * KeccakfPermAir.extraction.inter_2212 c row := by
    simp only [KeccakfPermAir.extraction.inter_2214, KeccakfPermAir.extraction.inter_2213, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_2212 c row = (mc 256 + mc 576 + mc 1856 - 2*mc 256*mc 576 - 2*mc 256*mc 1856 - 2*mc 576*mc 1856 + 4*mc 256*mc 576*mc 1856) := by
    simp only [KeccakfPermAir.extraction.inter_2212, KeccakfPermAir.extraction.inter_2211, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1976 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 257 577 1857 187 row) :
    mc 187 = (mc 257 + mc 577 + mc 1857 - 2*mc 257*mc 577 - 2*mc 257*mc 1857 - 2*mc 577*mc 1857 + 4*mc 257*mc 577*mc 1857) + 2*(mc 258 + mc 578 + mc 1858 - 2*mc 258*mc 578 - 2*mc 258*mc 1858 - 2*mc 578*mc 1858 + 4*mc 258*mc 578*mc 1858) + 4*(mc 259 + mc 579 + mc 1859 - 2*mc 259*mc 579 - 2*mc 259*mc 1859 - 2*mc 579*mc 1859 + 4*mc 259*mc 579*mc 1859) + 8*(mc 260 + mc 580 + mc 1860 - 2*mc 260*mc 580 - 2*mc 260*mc 1860 - 2*mc 580*mc 1860 + 4*mc 260*mc 580*mc 1860) + 16*(mc 261 + mc 581 + mc 1861 - 2*mc 261*mc 581 - 2*mc 261*mc 1861 - 2*mc 581*mc 1861 + 4*mc 261*mc 581*mc 1861) + 32*(mc 262 + mc 582 + mc 1862 - 2*mc 262*mc 582 - 2*mc 262*mc 1862 - 2*mc 582*mc 1862 + 4*mc 262*mc 582*mc 1862) + 64*(mc 263 + mc 583 + mc 1863 - 2*mc 263*mc 583 - 2*mc 263*mc 1863 - 2*mc 583*mc 1863 + 4*mc 263*mc 583*mc 1863) + 128*(mc 264 + mc 584 + mc 1864 - 2*mc 264*mc 584 - 2*mc 264*mc 1864 - 2*mc 584*mc 1864 + 4*mc 264*mc 584*mc 1864) + 256*(mc 265 + mc 585 + mc 1865 - 2*mc 265*mc 585 - 2*mc 265*mc 1865 - 2*mc 585*mc 1865 + 4*mc 265*mc 585*mc 1865) + 512*(mc 266 + mc 586 + mc 1866 - 2*mc 266*mc 586 - 2*mc 266*mc 1866 - 2*mc 586*mc 1866 + 4*mc 266*mc 586*mc 1866) + 1024*(mc 267 + mc 587 + mc 1867 - 2*mc 267*mc 587 - 2*mc 267*mc 1867 - 2*mc 587*mc 1867 + 4*mc 267*mc 587*mc 1867) + 2048*(mc 268 + mc 588 + mc 1868 - 2*mc 268*mc 588 - 2*mc 268*mc 1868 - 2*mc 588*mc 1868 + 4*mc 268*mc 588*mc 1868) + 4096*(mc 269 + mc 589 + mc 1869 - 2*mc 269*mc 589 - 2*mc 269*mc 1869 - 2*mc 589*mc 1869 + 4*mc 269*mc 589*mc 1869) + 8192*(mc 270 + mc 590 + mc 1870 - 2*mc 270*mc 590 - 2*mc 270*mc 1870 - 2*mc 590*mc 1870 + 4*mc 270*mc 590*mc 1870) + 16384*(mc 271 + mc 591 + mc 1871 - 2*mc 271*mc 591 - 2*mc 271*mc 1871 - 2*mc 591*mc 1871 + 4*mc 271*mc 591*mc 1871) + 32768*(mc 272 + mc 592 + mc 1872 - 2*mc 272*mc 592 - 2*mc 272*mc 1872 - 2*mc 592*mc 1872 + 4*mc 272*mc 592*mc 1872) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1976, KeccakfPermAir.extraction.inter_2272, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_2271 c row = (mc 258 + mc 578 + mc 1858 - 2*mc 258*mc 578 - 2*mc 258*mc 1858 - 2*mc 578*mc 1858 + 4*mc 258*mc 578*mc 1858) + 2 * KeccakfPermAir.extraction.inter_2269 c row := by
    simp only [KeccakfPermAir.extraction.inter_2271, KeccakfPermAir.extraction.inter_2270, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_2269 c row = (mc 259 + mc 579 + mc 1859 - 2*mc 259*mc 579 - 2*mc 259*mc 1859 - 2*mc 579*mc 1859 + 4*mc 259*mc 579*mc 1859) + 2 * KeccakfPermAir.extraction.inter_2267 c row := by
    simp only [KeccakfPermAir.extraction.inter_2269, KeccakfPermAir.extraction.inter_2268, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_2267 c row = (mc 260 + mc 580 + mc 1860 - 2*mc 260*mc 580 - 2*mc 260*mc 1860 - 2*mc 580*mc 1860 + 4*mc 260*mc 580*mc 1860) + 2 * KeccakfPermAir.extraction.inter_2265 c row := by
    simp only [KeccakfPermAir.extraction.inter_2267, KeccakfPermAir.extraction.inter_2266, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_2265 c row = (mc 261 + mc 581 + mc 1861 - 2*mc 261*mc 581 - 2*mc 261*mc 1861 - 2*mc 581*mc 1861 + 4*mc 261*mc 581*mc 1861) + 2 * KeccakfPermAir.extraction.inter_2263 c row := by
    simp only [KeccakfPermAir.extraction.inter_2265, KeccakfPermAir.extraction.inter_2264, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_2263 c row = (mc 262 + mc 582 + mc 1862 - 2*mc 262*mc 582 - 2*mc 262*mc 1862 - 2*mc 582*mc 1862 + 4*mc 262*mc 582*mc 1862) + 2 * KeccakfPermAir.extraction.inter_2261 c row := by
    simp only [KeccakfPermAir.extraction.inter_2263, KeccakfPermAir.extraction.inter_2262, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_2261 c row = (mc 263 + mc 583 + mc 1863 - 2*mc 263*mc 583 - 2*mc 263*mc 1863 - 2*mc 583*mc 1863 + 4*mc 263*mc 583*mc 1863) + 2 * KeccakfPermAir.extraction.inter_2259 c row := by
    simp only [KeccakfPermAir.extraction.inter_2261, KeccakfPermAir.extraction.inter_2260, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_2259 c row = (mc 264 + mc 584 + mc 1864 - 2*mc 264*mc 584 - 2*mc 264*mc 1864 - 2*mc 584*mc 1864 + 4*mc 264*mc 584*mc 1864) + 2 * KeccakfPermAir.extraction.inter_2257 c row := by
    simp only [KeccakfPermAir.extraction.inter_2259, KeccakfPermAir.extraction.inter_2258, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_2257 c row = (mc 265 + mc 585 + mc 1865 - 2*mc 265*mc 585 - 2*mc 265*mc 1865 - 2*mc 585*mc 1865 + 4*mc 265*mc 585*mc 1865) + 2 * KeccakfPermAir.extraction.inter_2255 c row := by
    simp only [KeccakfPermAir.extraction.inter_2257, KeccakfPermAir.extraction.inter_2256, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_2255 c row = (mc 266 + mc 586 + mc 1866 - 2*mc 266*mc 586 - 2*mc 266*mc 1866 - 2*mc 586*mc 1866 + 4*mc 266*mc 586*mc 1866) + 2 * KeccakfPermAir.extraction.inter_2253 c row := by
    simp only [KeccakfPermAir.extraction.inter_2255, KeccakfPermAir.extraction.inter_2254, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_2253 c row = (mc 267 + mc 587 + mc 1867 - 2*mc 267*mc 587 - 2*mc 267*mc 1867 - 2*mc 587*mc 1867 + 4*mc 267*mc 587*mc 1867) + 2 * KeccakfPermAir.extraction.inter_2251 c row := by
    simp only [KeccakfPermAir.extraction.inter_2253, KeccakfPermAir.extraction.inter_2252, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_2251 c row = (mc 268 + mc 588 + mc 1868 - 2*mc 268*mc 588 - 2*mc 268*mc 1868 - 2*mc 588*mc 1868 + 4*mc 268*mc 588*mc 1868) + 2 * KeccakfPermAir.extraction.inter_2249 c row := by
    simp only [KeccakfPermAir.extraction.inter_2251, KeccakfPermAir.extraction.inter_2250, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_2249 c row = (mc 269 + mc 589 + mc 1869 - 2*mc 269*mc 589 - 2*mc 269*mc 1869 - 2*mc 589*mc 1869 + 4*mc 269*mc 589*mc 1869) + 2 * KeccakfPermAir.extraction.inter_2247 c row := by
    simp only [KeccakfPermAir.extraction.inter_2249, KeccakfPermAir.extraction.inter_2248, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_2247 c row = (mc 270 + mc 590 + mc 1870 - 2*mc 270*mc 590 - 2*mc 270*mc 1870 - 2*mc 590*mc 1870 + 4*mc 270*mc 590*mc 1870) + 2 * KeccakfPermAir.extraction.inter_2245 c row := by
    simp only [KeccakfPermAir.extraction.inter_2247, KeccakfPermAir.extraction.inter_2246, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_2245 c row = (mc 271 + mc 591 + mc 1871 - 2*mc 271*mc 591 - 2*mc 271*mc 1871 - 2*mc 591*mc 1871 + 4*mc 271*mc 591*mc 1871) + 2 * KeccakfPermAir.extraction.inter_2243 c row := by
    simp only [KeccakfPermAir.extraction.inter_2245, KeccakfPermAir.extraction.inter_2244, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_2243 c row = (mc 272 + mc 592 + mc 1872 - 2*mc 272*mc 592 - 2*mc 272*mc 1872 - 2*mc 592*mc 1872 + 4*mc 272*mc 592*mc 1872) := by
    simp only [KeccakfPermAir.extraction.inter_2243, KeccakfPermAir.extraction.inter_2242, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_1977 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 273 593 1873 188 row) :
    mc 188 = (mc 273 + mc 593 + mc 1873 - 2*mc 273*mc 593 - 2*mc 273*mc 1873 - 2*mc 593*mc 1873 + 4*mc 273*mc 593*mc 1873) + 2*(mc 274 + mc 594 + mc 1874 - 2*mc 274*mc 594 - 2*mc 274*mc 1874 - 2*mc 594*mc 1874 + 4*mc 274*mc 594*mc 1874) + 4*(mc 275 + mc 595 + mc 1875 - 2*mc 275*mc 595 - 2*mc 275*mc 1875 - 2*mc 595*mc 1875 + 4*mc 275*mc 595*mc 1875) + 8*(mc 276 + mc 596 + mc 1876 - 2*mc 276*mc 596 - 2*mc 276*mc 1876 - 2*mc 596*mc 1876 + 4*mc 276*mc 596*mc 1876) + 16*(mc 277 + mc 597 + mc 1877 - 2*mc 277*mc 597 - 2*mc 277*mc 1877 - 2*mc 597*mc 1877 + 4*mc 277*mc 597*mc 1877) + 32*(mc 278 + mc 598 + mc 1878 - 2*mc 278*mc 598 - 2*mc 278*mc 1878 - 2*mc 598*mc 1878 + 4*mc 278*mc 598*mc 1878) + 64*(mc 279 + mc 599 + mc 1879 - 2*mc 279*mc 599 - 2*mc 279*mc 1879 - 2*mc 599*mc 1879 + 4*mc 279*mc 599*mc 1879) + 128*(mc 280 + mc 600 + mc 1880 - 2*mc 280*mc 600 - 2*mc 280*mc 1880 - 2*mc 600*mc 1880 + 4*mc 280*mc 600*mc 1880) + 256*(mc 281 + mc 601 + mc 1881 - 2*mc 281*mc 601 - 2*mc 281*mc 1881 - 2*mc 601*mc 1881 + 4*mc 281*mc 601*mc 1881) + 512*(mc 282 + mc 602 + mc 1882 - 2*mc 282*mc 602 - 2*mc 282*mc 1882 - 2*mc 602*mc 1882 + 4*mc 282*mc 602*mc 1882) + 1024*(mc 283 + mc 603 + mc 1883 - 2*mc 283*mc 603 - 2*mc 283*mc 1883 - 2*mc 603*mc 1883 + 4*mc 283*mc 603*mc 1883) + 2048*(mc 284 + mc 604 + mc 1884 - 2*mc 284*mc 604 - 2*mc 284*mc 1884 - 2*mc 604*mc 1884 + 4*mc 284*mc 604*mc 1884) + 4096*(mc 285 + mc 605 + mc 1885 - 2*mc 285*mc 605 - 2*mc 285*mc 1885 - 2*mc 605*mc 1885 + 4*mc 285*mc 605*mc 1885) + 8192*(mc 286 + mc 606 + mc 1886 - 2*mc 286*mc 606 - 2*mc 286*mc 1886 - 2*mc 606*mc 1886 + 4*mc 286*mc 606*mc 1886) + 16384*(mc 287 + mc 607 + mc 1887 - 2*mc 287*mc 607 - 2*mc 287*mc 1887 - 2*mc 607*mc 1887 + 4*mc 287*mc 607*mc 1887) + 32768*(mc 288 + mc 608 + mc 1888 - 2*mc 288*mc 608 - 2*mc 288*mc 1888 - 2*mc 608*mc 1888 + 4*mc 288*mc 608*mc 1888) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_1977, KeccakfPermAir.extraction.inter_2303, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_2302 c row = (mc 274 + mc 594 + mc 1874 - 2*mc 274*mc 594 - 2*mc 274*mc 1874 - 2*mc 594*mc 1874 + 4*mc 274*mc 594*mc 1874) + 2 * KeccakfPermAir.extraction.inter_2300 c row := by
    simp only [KeccakfPermAir.extraction.inter_2302, KeccakfPermAir.extraction.inter_2301, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_2300 c row = (mc 275 + mc 595 + mc 1875 - 2*mc 275*mc 595 - 2*mc 275*mc 1875 - 2*mc 595*mc 1875 + 4*mc 275*mc 595*mc 1875) + 2 * KeccakfPermAir.extraction.inter_2298 c row := by
    simp only [KeccakfPermAir.extraction.inter_2300, KeccakfPermAir.extraction.inter_2299, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_2298 c row = (mc 276 + mc 596 + mc 1876 - 2*mc 276*mc 596 - 2*mc 276*mc 1876 - 2*mc 596*mc 1876 + 4*mc 276*mc 596*mc 1876) + 2 * KeccakfPermAir.extraction.inter_2296 c row := by
    simp only [KeccakfPermAir.extraction.inter_2298, KeccakfPermAir.extraction.inter_2297, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_2296 c row = (mc 277 + mc 597 + mc 1877 - 2*mc 277*mc 597 - 2*mc 277*mc 1877 - 2*mc 597*mc 1877 + 4*mc 277*mc 597*mc 1877) + 2 * KeccakfPermAir.extraction.inter_2294 c row := by
    simp only [KeccakfPermAir.extraction.inter_2296, KeccakfPermAir.extraction.inter_2295, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_2294 c row = (mc 278 + mc 598 + mc 1878 - 2*mc 278*mc 598 - 2*mc 278*mc 1878 - 2*mc 598*mc 1878 + 4*mc 278*mc 598*mc 1878) + 2 * KeccakfPermAir.extraction.inter_2292 c row := by
    simp only [KeccakfPermAir.extraction.inter_2294, KeccakfPermAir.extraction.inter_2293, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_2292 c row = (mc 279 + mc 599 + mc 1879 - 2*mc 279*mc 599 - 2*mc 279*mc 1879 - 2*mc 599*mc 1879 + 4*mc 279*mc 599*mc 1879) + 2 * KeccakfPermAir.extraction.inter_2290 c row := by
    simp only [KeccakfPermAir.extraction.inter_2292, KeccakfPermAir.extraction.inter_2291, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_2290 c row = (mc 280 + mc 600 + mc 1880 - 2*mc 280*mc 600 - 2*mc 280*mc 1880 - 2*mc 600*mc 1880 + 4*mc 280*mc 600*mc 1880) + 2 * KeccakfPermAir.extraction.inter_2288 c row := by
    simp only [KeccakfPermAir.extraction.inter_2290, KeccakfPermAir.extraction.inter_2289, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_2288 c row = (mc 281 + mc 601 + mc 1881 - 2*mc 281*mc 601 - 2*mc 281*mc 1881 - 2*mc 601*mc 1881 + 4*mc 281*mc 601*mc 1881) + 2 * KeccakfPermAir.extraction.inter_2286 c row := by
    simp only [KeccakfPermAir.extraction.inter_2288, KeccakfPermAir.extraction.inter_2287, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_2286 c row = (mc 282 + mc 602 + mc 1882 - 2*mc 282*mc 602 - 2*mc 282*mc 1882 - 2*mc 602*mc 1882 + 4*mc 282*mc 602*mc 1882) + 2 * KeccakfPermAir.extraction.inter_2284 c row := by
    simp only [KeccakfPermAir.extraction.inter_2286, KeccakfPermAir.extraction.inter_2285, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_2284 c row = (mc 283 + mc 603 + mc 1883 - 2*mc 283*mc 603 - 2*mc 283*mc 1883 - 2*mc 603*mc 1883 + 4*mc 283*mc 603*mc 1883) + 2 * KeccakfPermAir.extraction.inter_2282 c row := by
    simp only [KeccakfPermAir.extraction.inter_2284, KeccakfPermAir.extraction.inter_2283, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_2282 c row = (mc 284 + mc 604 + mc 1884 - 2*mc 284*mc 604 - 2*mc 284*mc 1884 - 2*mc 604*mc 1884 + 4*mc 284*mc 604*mc 1884) + 2 * KeccakfPermAir.extraction.inter_2280 c row := by
    simp only [KeccakfPermAir.extraction.inter_2282, KeccakfPermAir.extraction.inter_2281, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_2280 c row = (mc 285 + mc 605 + mc 1885 - 2*mc 285*mc 605 - 2*mc 285*mc 1885 - 2*mc 605*mc 1885 + 4*mc 285*mc 605*mc 1885) + 2 * KeccakfPermAir.extraction.inter_2278 c row := by
    simp only [KeccakfPermAir.extraction.inter_2280, KeccakfPermAir.extraction.inter_2279, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_2278 c row = (mc 286 + mc 606 + mc 1886 - 2*mc 286*mc 606 - 2*mc 286*mc 1886 - 2*mc 606*mc 1886 + 4*mc 286*mc 606*mc 1886) + 2 * KeccakfPermAir.extraction.inter_2276 c row := by
    simp only [KeccakfPermAir.extraction.inter_2278, KeccakfPermAir.extraction.inter_2277, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_2276 c row = (mc 287 + mc 607 + mc 1887 - 2*mc 287*mc 607 - 2*mc 287*mc 1887 - 2*mc 607*mc 1887 + 4*mc 287*mc 607*mc 1887) + 2 * KeccakfPermAir.extraction.inter_2274 c row := by
    simp only [KeccakfPermAir.extraction.inter_2276, KeccakfPermAir.extraction.inter_2275, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_2274 c row = (mc 288 + mc 608 + mc 1888 - 2*mc 288*mc 608 - 2*mc 288*mc 1888 - 2*mc 608*mc 1888 + 4*mc 288*mc 608*mc 1888) := by
    simp only [KeccakfPermAir.extraction.inter_2274, KeccakfPermAir.extraction.inter_2273, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_2042 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 289 609 1889 189 row) :
    mc 189 = (mc 289 + mc 609 + mc 1889 - 2*mc 289*mc 609 - 2*mc 289*mc 1889 - 2*mc 609*mc 1889 + 4*mc 289*mc 609*mc 1889) + 2*(mc 290 + mc 610 + mc 1890 - 2*mc 290*mc 610 - 2*mc 290*mc 1890 - 2*mc 610*mc 1890 + 4*mc 290*mc 610*mc 1890) + 4*(mc 291 + mc 611 + mc 1891 - 2*mc 291*mc 611 - 2*mc 291*mc 1891 - 2*mc 611*mc 1891 + 4*mc 291*mc 611*mc 1891) + 8*(mc 292 + mc 612 + mc 1892 - 2*mc 292*mc 612 - 2*mc 292*mc 1892 - 2*mc 612*mc 1892 + 4*mc 292*mc 612*mc 1892) + 16*(mc 293 + mc 613 + mc 1893 - 2*mc 293*mc 613 - 2*mc 293*mc 1893 - 2*mc 613*mc 1893 + 4*mc 293*mc 613*mc 1893) + 32*(mc 294 + mc 614 + mc 1894 - 2*mc 294*mc 614 - 2*mc 294*mc 1894 - 2*mc 614*mc 1894 + 4*mc 294*mc 614*mc 1894) + 64*(mc 295 + mc 615 + mc 1895 - 2*mc 295*mc 615 - 2*mc 295*mc 1895 - 2*mc 615*mc 1895 + 4*mc 295*mc 615*mc 1895) + 128*(mc 296 + mc 616 + mc 1896 - 2*mc 296*mc 616 - 2*mc 296*mc 1896 - 2*mc 616*mc 1896 + 4*mc 296*mc 616*mc 1896) + 256*(mc 297 + mc 617 + mc 1897 - 2*mc 297*mc 617 - 2*mc 297*mc 1897 - 2*mc 617*mc 1897 + 4*mc 297*mc 617*mc 1897) + 512*(mc 298 + mc 618 + mc 1898 - 2*mc 298*mc 618 - 2*mc 298*mc 1898 - 2*mc 618*mc 1898 + 4*mc 298*mc 618*mc 1898) + 1024*(mc 299 + mc 619 + mc 1899 - 2*mc 299*mc 619 - 2*mc 299*mc 1899 - 2*mc 619*mc 1899 + 4*mc 299*mc 619*mc 1899) + 2048*(mc 300 + mc 620 + mc 1900 - 2*mc 300*mc 620 - 2*mc 300*mc 1900 - 2*mc 620*mc 1900 + 4*mc 300*mc 620*mc 1900) + 4096*(mc 301 + mc 621 + mc 1901 - 2*mc 301*mc 621 - 2*mc 301*mc 1901 - 2*mc 621*mc 1901 + 4*mc 301*mc 621*mc 1901) + 8192*(mc 302 + mc 622 + mc 1902 - 2*mc 302*mc 622 - 2*mc 302*mc 1902 - 2*mc 622*mc 1902 + 4*mc 302*mc 622*mc 1902) + 16384*(mc 303 + mc 623 + mc 1903 - 2*mc 303*mc 623 - 2*mc 303*mc 1903 - 2*mc 623*mc 1903 + 4*mc 303*mc 623*mc 1903) + 32768*(mc 304 + mc 624 + mc 1904 - 2*mc 304*mc 624 - 2*mc 304*mc 1904 - 2*mc 624*mc 1904 + 4*mc 304*mc 624*mc 1904) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_2042, KeccakfPermAir.extraction.inter_2334, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_2333 c row = (mc 290 + mc 610 + mc 1890 - 2*mc 290*mc 610 - 2*mc 290*mc 1890 - 2*mc 610*mc 1890 + 4*mc 290*mc 610*mc 1890) + 2 * KeccakfPermAir.extraction.inter_2331 c row := by
    simp only [KeccakfPermAir.extraction.inter_2333, KeccakfPermAir.extraction.inter_2332, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_2331 c row = (mc 291 + mc 611 + mc 1891 - 2*mc 291*mc 611 - 2*mc 291*mc 1891 - 2*mc 611*mc 1891 + 4*mc 291*mc 611*mc 1891) + 2 * KeccakfPermAir.extraction.inter_2329 c row := by
    simp only [KeccakfPermAir.extraction.inter_2331, KeccakfPermAir.extraction.inter_2330, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_2329 c row = (mc 292 + mc 612 + mc 1892 - 2*mc 292*mc 612 - 2*mc 292*mc 1892 - 2*mc 612*mc 1892 + 4*mc 292*mc 612*mc 1892) + 2 * KeccakfPermAir.extraction.inter_2327 c row := by
    simp only [KeccakfPermAir.extraction.inter_2329, KeccakfPermAir.extraction.inter_2328, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_2327 c row = (mc 293 + mc 613 + mc 1893 - 2*mc 293*mc 613 - 2*mc 293*mc 1893 - 2*mc 613*mc 1893 + 4*mc 293*mc 613*mc 1893) + 2 * KeccakfPermAir.extraction.inter_2325 c row := by
    simp only [KeccakfPermAir.extraction.inter_2327, KeccakfPermAir.extraction.inter_2326, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_2325 c row = (mc 294 + mc 614 + mc 1894 - 2*mc 294*mc 614 - 2*mc 294*mc 1894 - 2*mc 614*mc 1894 + 4*mc 294*mc 614*mc 1894) + 2 * KeccakfPermAir.extraction.inter_2323 c row := by
    simp only [KeccakfPermAir.extraction.inter_2325, KeccakfPermAir.extraction.inter_2324, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_2323 c row = (mc 295 + mc 615 + mc 1895 - 2*mc 295*mc 615 - 2*mc 295*mc 1895 - 2*mc 615*mc 1895 + 4*mc 295*mc 615*mc 1895) + 2 * KeccakfPermAir.extraction.inter_2321 c row := by
    simp only [KeccakfPermAir.extraction.inter_2323, KeccakfPermAir.extraction.inter_2322, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_2321 c row = (mc 296 + mc 616 + mc 1896 - 2*mc 296*mc 616 - 2*mc 296*mc 1896 - 2*mc 616*mc 1896 + 4*mc 296*mc 616*mc 1896) + 2 * KeccakfPermAir.extraction.inter_2319 c row := by
    simp only [KeccakfPermAir.extraction.inter_2321, KeccakfPermAir.extraction.inter_2320, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_2319 c row = (mc 297 + mc 617 + mc 1897 - 2*mc 297*mc 617 - 2*mc 297*mc 1897 - 2*mc 617*mc 1897 + 4*mc 297*mc 617*mc 1897) + 2 * KeccakfPermAir.extraction.inter_2317 c row := by
    simp only [KeccakfPermAir.extraction.inter_2319, KeccakfPermAir.extraction.inter_2318, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_2317 c row = (mc 298 + mc 618 + mc 1898 - 2*mc 298*mc 618 - 2*mc 298*mc 1898 - 2*mc 618*mc 1898 + 4*mc 298*mc 618*mc 1898) + 2 * KeccakfPermAir.extraction.inter_2315 c row := by
    simp only [KeccakfPermAir.extraction.inter_2317, KeccakfPermAir.extraction.inter_2316, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_2315 c row = (mc 299 + mc 619 + mc 1899 - 2*mc 299*mc 619 - 2*mc 299*mc 1899 - 2*mc 619*mc 1899 + 4*mc 299*mc 619*mc 1899) + 2 * KeccakfPermAir.extraction.inter_2313 c row := by
    simp only [KeccakfPermAir.extraction.inter_2315, KeccakfPermAir.extraction.inter_2314, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_2313 c row = (mc 300 + mc 620 + mc 1900 - 2*mc 300*mc 620 - 2*mc 300*mc 1900 - 2*mc 620*mc 1900 + 4*mc 300*mc 620*mc 1900) + 2 * KeccakfPermAir.extraction.inter_2311 c row := by
    simp only [KeccakfPermAir.extraction.inter_2313, KeccakfPermAir.extraction.inter_2312, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_2311 c row = (mc 301 + mc 621 + mc 1901 - 2*mc 301*mc 621 - 2*mc 301*mc 1901 - 2*mc 621*mc 1901 + 4*mc 301*mc 621*mc 1901) + 2 * KeccakfPermAir.extraction.inter_2309 c row := by
    simp only [KeccakfPermAir.extraction.inter_2311, KeccakfPermAir.extraction.inter_2310, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_2309 c row = (mc 302 + mc 622 + mc 1902 - 2*mc 302*mc 622 - 2*mc 302*mc 1902 - 2*mc 622*mc 1902 + 4*mc 302*mc 622*mc 1902) + 2 * KeccakfPermAir.extraction.inter_2307 c row := by
    simp only [KeccakfPermAir.extraction.inter_2309, KeccakfPermAir.extraction.inter_2308, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_2307 c row = (mc 303 + mc 623 + mc 1903 - 2*mc 303*mc 623 - 2*mc 303*mc 1903 - 2*mc 623*mc 1903 + 4*mc 303*mc 623*mc 1903) + 2 * KeccakfPermAir.extraction.inter_2305 c row := by
    simp only [KeccakfPermAir.extraction.inter_2307, KeccakfPermAir.extraction.inter_2306, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_2305 c row = (mc 304 + mc 624 + mc 1904 - 2*mc 304*mc 624 - 2*mc 304*mc 1904 - 2*mc 624*mc 1904 + 4*mc 304*mc 624*mc 1904) := by
    simp only [KeccakfPermAir.extraction.inter_2305, KeccakfPermAir.extraction.inter_2304, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_2043 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 305 625 1905 190 row) :
    mc 190 = (mc 305 + mc 625 + mc 1905 - 2*mc 305*mc 625 - 2*mc 305*mc 1905 - 2*mc 625*mc 1905 + 4*mc 305*mc 625*mc 1905) + 2*(mc 306 + mc 626 + mc 1906 - 2*mc 306*mc 626 - 2*mc 306*mc 1906 - 2*mc 626*mc 1906 + 4*mc 306*mc 626*mc 1906) + 4*(mc 307 + mc 627 + mc 1907 - 2*mc 307*mc 627 - 2*mc 307*mc 1907 - 2*mc 627*mc 1907 + 4*mc 307*mc 627*mc 1907) + 8*(mc 308 + mc 628 + mc 1908 - 2*mc 308*mc 628 - 2*mc 308*mc 1908 - 2*mc 628*mc 1908 + 4*mc 308*mc 628*mc 1908) + 16*(mc 309 + mc 629 + mc 1909 - 2*mc 309*mc 629 - 2*mc 309*mc 1909 - 2*mc 629*mc 1909 + 4*mc 309*mc 629*mc 1909) + 32*(mc 310 + mc 630 + mc 1910 - 2*mc 310*mc 630 - 2*mc 310*mc 1910 - 2*mc 630*mc 1910 + 4*mc 310*mc 630*mc 1910) + 64*(mc 311 + mc 631 + mc 1911 - 2*mc 311*mc 631 - 2*mc 311*mc 1911 - 2*mc 631*mc 1911 + 4*mc 311*mc 631*mc 1911) + 128*(mc 312 + mc 632 + mc 1912 - 2*mc 312*mc 632 - 2*mc 312*mc 1912 - 2*mc 632*mc 1912 + 4*mc 312*mc 632*mc 1912) + 256*(mc 313 + mc 633 + mc 1913 - 2*mc 313*mc 633 - 2*mc 313*mc 1913 - 2*mc 633*mc 1913 + 4*mc 313*mc 633*mc 1913) + 512*(mc 314 + mc 634 + mc 1914 - 2*mc 314*mc 634 - 2*mc 314*mc 1914 - 2*mc 634*mc 1914 + 4*mc 314*mc 634*mc 1914) + 1024*(mc 315 + mc 635 + mc 1915 - 2*mc 315*mc 635 - 2*mc 315*mc 1915 - 2*mc 635*mc 1915 + 4*mc 315*mc 635*mc 1915) + 2048*(mc 316 + mc 636 + mc 1916 - 2*mc 316*mc 636 - 2*mc 316*mc 1916 - 2*mc 636*mc 1916 + 4*mc 316*mc 636*mc 1916) + 4096*(mc 317 + mc 637 + mc 1917 - 2*mc 317*mc 637 - 2*mc 317*mc 1917 - 2*mc 637*mc 1917 + 4*mc 317*mc 637*mc 1917) + 8192*(mc 318 + mc 638 + mc 1918 - 2*mc 318*mc 638 - 2*mc 318*mc 1918 - 2*mc 638*mc 1918 + 4*mc 318*mc 638*mc 1918) + 16384*(mc 319 + mc 639 + mc 1919 - 2*mc 319*mc 639 - 2*mc 319*mc 1919 - 2*mc 639*mc 1919 + 4*mc 319*mc 639*mc 1919) + 32768*(mc 320 + mc 640 + mc 1920 - 2*mc 320*mc 640 - 2*mc 320*mc 1920 - 2*mc 640*mc 1920 + 4*mc 320*mc 640*mc 1920) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_2043, KeccakfPermAir.extraction.inter_2365, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_2364 c row = (mc 306 + mc 626 + mc 1906 - 2*mc 306*mc 626 - 2*mc 306*mc 1906 - 2*mc 626*mc 1906 + 4*mc 306*mc 626*mc 1906) + 2 * KeccakfPermAir.extraction.inter_2362 c row := by
    simp only [KeccakfPermAir.extraction.inter_2364, KeccakfPermAir.extraction.inter_2363, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_2362 c row = (mc 307 + mc 627 + mc 1907 - 2*mc 307*mc 627 - 2*mc 307*mc 1907 - 2*mc 627*mc 1907 + 4*mc 307*mc 627*mc 1907) + 2 * KeccakfPermAir.extraction.inter_2360 c row := by
    simp only [KeccakfPermAir.extraction.inter_2362, KeccakfPermAir.extraction.inter_2361, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_2360 c row = (mc 308 + mc 628 + mc 1908 - 2*mc 308*mc 628 - 2*mc 308*mc 1908 - 2*mc 628*mc 1908 + 4*mc 308*mc 628*mc 1908) + 2 * KeccakfPermAir.extraction.inter_2358 c row := by
    simp only [KeccakfPermAir.extraction.inter_2360, KeccakfPermAir.extraction.inter_2359, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_2358 c row = (mc 309 + mc 629 + mc 1909 - 2*mc 309*mc 629 - 2*mc 309*mc 1909 - 2*mc 629*mc 1909 + 4*mc 309*mc 629*mc 1909) + 2 * KeccakfPermAir.extraction.inter_2356 c row := by
    simp only [KeccakfPermAir.extraction.inter_2358, KeccakfPermAir.extraction.inter_2357, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_2356 c row = (mc 310 + mc 630 + mc 1910 - 2*mc 310*mc 630 - 2*mc 310*mc 1910 - 2*mc 630*mc 1910 + 4*mc 310*mc 630*mc 1910) + 2 * KeccakfPermAir.extraction.inter_2354 c row := by
    simp only [KeccakfPermAir.extraction.inter_2356, KeccakfPermAir.extraction.inter_2355, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_2354 c row = (mc 311 + mc 631 + mc 1911 - 2*mc 311*mc 631 - 2*mc 311*mc 1911 - 2*mc 631*mc 1911 + 4*mc 311*mc 631*mc 1911) + 2 * KeccakfPermAir.extraction.inter_2352 c row := by
    simp only [KeccakfPermAir.extraction.inter_2354, KeccakfPermAir.extraction.inter_2353, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_2352 c row = (mc 312 + mc 632 + mc 1912 - 2*mc 312*mc 632 - 2*mc 312*mc 1912 - 2*mc 632*mc 1912 + 4*mc 312*mc 632*mc 1912) + 2 * KeccakfPermAir.extraction.inter_2350 c row := by
    simp only [KeccakfPermAir.extraction.inter_2352, KeccakfPermAir.extraction.inter_2351, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_2350 c row = (mc 313 + mc 633 + mc 1913 - 2*mc 313*mc 633 - 2*mc 313*mc 1913 - 2*mc 633*mc 1913 + 4*mc 313*mc 633*mc 1913) + 2 * KeccakfPermAir.extraction.inter_2348 c row := by
    simp only [KeccakfPermAir.extraction.inter_2350, KeccakfPermAir.extraction.inter_2349, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_2348 c row = (mc 314 + mc 634 + mc 1914 - 2*mc 314*mc 634 - 2*mc 314*mc 1914 - 2*mc 634*mc 1914 + 4*mc 314*mc 634*mc 1914) + 2 * KeccakfPermAir.extraction.inter_2346 c row := by
    simp only [KeccakfPermAir.extraction.inter_2348, KeccakfPermAir.extraction.inter_2347, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_2346 c row = (mc 315 + mc 635 + mc 1915 - 2*mc 315*mc 635 - 2*mc 315*mc 1915 - 2*mc 635*mc 1915 + 4*mc 315*mc 635*mc 1915) + 2 * KeccakfPermAir.extraction.inter_2344 c row := by
    simp only [KeccakfPermAir.extraction.inter_2346, KeccakfPermAir.extraction.inter_2345, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_2344 c row = (mc 316 + mc 636 + mc 1916 - 2*mc 316*mc 636 - 2*mc 316*mc 1916 - 2*mc 636*mc 1916 + 4*mc 316*mc 636*mc 1916) + 2 * KeccakfPermAir.extraction.inter_2342 c row := by
    simp only [KeccakfPermAir.extraction.inter_2344, KeccakfPermAir.extraction.inter_2343, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_2342 c row = (mc 317 + mc 637 + mc 1917 - 2*mc 317*mc 637 - 2*mc 317*mc 1917 - 2*mc 637*mc 1917 + 4*mc 317*mc 637*mc 1917) + 2 * KeccakfPermAir.extraction.inter_2340 c row := by
    simp only [KeccakfPermAir.extraction.inter_2342, KeccakfPermAir.extraction.inter_2341, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_2340 c row = (mc 318 + mc 638 + mc 1918 - 2*mc 318*mc 638 - 2*mc 318*mc 1918 - 2*mc 638*mc 1918 + 4*mc 318*mc 638*mc 1918) + 2 * KeccakfPermAir.extraction.inter_2338 c row := by
    simp only [KeccakfPermAir.extraction.inter_2340, KeccakfPermAir.extraction.inter_2339, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_2338 c row = (mc 319 + mc 639 + mc 1919 - 2*mc 319*mc 639 - 2*mc 319*mc 1919 - 2*mc 639*mc 1919 + 4*mc 319*mc 639*mc 1919) + 2 * KeccakfPermAir.extraction.inter_2336 c row := by
    simp only [KeccakfPermAir.extraction.inter_2338, KeccakfPermAir.extraction.inter_2337, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_2336 c row = (mc 320 + mc 640 + mc 1920 - 2*mc 320*mc 640 - 2*mc 320*mc 1920 - 2*mc 640*mc 1920 + 4*mc 320*mc 640*mc 1920) := by
    simp only [KeccakfPermAir.extraction.inter_2336, KeccakfPermAir.extraction.inter_2335, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_2044 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 321 641 1921 191 row) :
    mc 191 = (mc 321 + mc 641 + mc 1921 - 2*mc 321*mc 641 - 2*mc 321*mc 1921 - 2*mc 641*mc 1921 + 4*mc 321*mc 641*mc 1921) + 2*(mc 322 + mc 642 + mc 1922 - 2*mc 322*mc 642 - 2*mc 322*mc 1922 - 2*mc 642*mc 1922 + 4*mc 322*mc 642*mc 1922) + 4*(mc 323 + mc 643 + mc 1923 - 2*mc 323*mc 643 - 2*mc 323*mc 1923 - 2*mc 643*mc 1923 + 4*mc 323*mc 643*mc 1923) + 8*(mc 324 + mc 644 + mc 1924 - 2*mc 324*mc 644 - 2*mc 324*mc 1924 - 2*mc 644*mc 1924 + 4*mc 324*mc 644*mc 1924) + 16*(mc 325 + mc 645 + mc 1925 - 2*mc 325*mc 645 - 2*mc 325*mc 1925 - 2*mc 645*mc 1925 + 4*mc 325*mc 645*mc 1925) + 32*(mc 326 + mc 646 + mc 1926 - 2*mc 326*mc 646 - 2*mc 326*mc 1926 - 2*mc 646*mc 1926 + 4*mc 326*mc 646*mc 1926) + 64*(mc 327 + mc 647 + mc 1927 - 2*mc 327*mc 647 - 2*mc 327*mc 1927 - 2*mc 647*mc 1927 + 4*mc 327*mc 647*mc 1927) + 128*(mc 328 + mc 648 + mc 1928 - 2*mc 328*mc 648 - 2*mc 328*mc 1928 - 2*mc 648*mc 1928 + 4*mc 328*mc 648*mc 1928) + 256*(mc 329 + mc 649 + mc 1929 - 2*mc 329*mc 649 - 2*mc 329*mc 1929 - 2*mc 649*mc 1929 + 4*mc 329*mc 649*mc 1929) + 512*(mc 330 + mc 650 + mc 1930 - 2*mc 330*mc 650 - 2*mc 330*mc 1930 - 2*mc 650*mc 1930 + 4*mc 330*mc 650*mc 1930) + 1024*(mc 331 + mc 651 + mc 1931 - 2*mc 331*mc 651 - 2*mc 331*mc 1931 - 2*mc 651*mc 1931 + 4*mc 331*mc 651*mc 1931) + 2048*(mc 332 + mc 652 + mc 1932 - 2*mc 332*mc 652 - 2*mc 332*mc 1932 - 2*mc 652*mc 1932 + 4*mc 332*mc 652*mc 1932) + 4096*(mc 333 + mc 653 + mc 1933 - 2*mc 333*mc 653 - 2*mc 333*mc 1933 - 2*mc 653*mc 1933 + 4*mc 333*mc 653*mc 1933) + 8192*(mc 334 + mc 654 + mc 1934 - 2*mc 334*mc 654 - 2*mc 334*mc 1934 - 2*mc 654*mc 1934 + 4*mc 334*mc 654*mc 1934) + 16384*(mc 335 + mc 655 + mc 1935 - 2*mc 335*mc 655 - 2*mc 335*mc 1935 - 2*mc 655*mc 1935 + 4*mc 335*mc 655*mc 1935) + 32768*(mc 336 + mc 656 + mc 1936 - 2*mc 336*mc 656 - 2*mc 336*mc 1936 - 2*mc 656*mc 1936 + 4*mc 336*mc 656*mc 1936) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_2044, KeccakfPermAir.extraction.inter_2396, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_2395 c row = (mc 322 + mc 642 + mc 1922 - 2*mc 322*mc 642 - 2*mc 322*mc 1922 - 2*mc 642*mc 1922 + 4*mc 322*mc 642*mc 1922) + 2 * KeccakfPermAir.extraction.inter_2393 c row := by
    simp only [KeccakfPermAir.extraction.inter_2395, KeccakfPermAir.extraction.inter_2394, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_2393 c row = (mc 323 + mc 643 + mc 1923 - 2*mc 323*mc 643 - 2*mc 323*mc 1923 - 2*mc 643*mc 1923 + 4*mc 323*mc 643*mc 1923) + 2 * KeccakfPermAir.extraction.inter_2391 c row := by
    simp only [KeccakfPermAir.extraction.inter_2393, KeccakfPermAir.extraction.inter_2392, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_2391 c row = (mc 324 + mc 644 + mc 1924 - 2*mc 324*mc 644 - 2*mc 324*mc 1924 - 2*mc 644*mc 1924 + 4*mc 324*mc 644*mc 1924) + 2 * KeccakfPermAir.extraction.inter_2389 c row := by
    simp only [KeccakfPermAir.extraction.inter_2391, KeccakfPermAir.extraction.inter_2390, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_2389 c row = (mc 325 + mc 645 + mc 1925 - 2*mc 325*mc 645 - 2*mc 325*mc 1925 - 2*mc 645*mc 1925 + 4*mc 325*mc 645*mc 1925) + 2 * KeccakfPermAir.extraction.inter_2387 c row := by
    simp only [KeccakfPermAir.extraction.inter_2389, KeccakfPermAir.extraction.inter_2388, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_2387 c row = (mc 326 + mc 646 + mc 1926 - 2*mc 326*mc 646 - 2*mc 326*mc 1926 - 2*mc 646*mc 1926 + 4*mc 326*mc 646*mc 1926) + 2 * KeccakfPermAir.extraction.inter_2385 c row := by
    simp only [KeccakfPermAir.extraction.inter_2387, KeccakfPermAir.extraction.inter_2386, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_2385 c row = (mc 327 + mc 647 + mc 1927 - 2*mc 327*mc 647 - 2*mc 327*mc 1927 - 2*mc 647*mc 1927 + 4*mc 327*mc 647*mc 1927) + 2 * KeccakfPermAir.extraction.inter_2383 c row := by
    simp only [KeccakfPermAir.extraction.inter_2385, KeccakfPermAir.extraction.inter_2384, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_2383 c row = (mc 328 + mc 648 + mc 1928 - 2*mc 328*mc 648 - 2*mc 328*mc 1928 - 2*mc 648*mc 1928 + 4*mc 328*mc 648*mc 1928) + 2 * KeccakfPermAir.extraction.inter_2381 c row := by
    simp only [KeccakfPermAir.extraction.inter_2383, KeccakfPermAir.extraction.inter_2382, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_2381 c row = (mc 329 + mc 649 + mc 1929 - 2*mc 329*mc 649 - 2*mc 329*mc 1929 - 2*mc 649*mc 1929 + 4*mc 329*mc 649*mc 1929) + 2 * KeccakfPermAir.extraction.inter_2379 c row := by
    simp only [KeccakfPermAir.extraction.inter_2381, KeccakfPermAir.extraction.inter_2380, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_2379 c row = (mc 330 + mc 650 + mc 1930 - 2*mc 330*mc 650 - 2*mc 330*mc 1930 - 2*mc 650*mc 1930 + 4*mc 330*mc 650*mc 1930) + 2 * KeccakfPermAir.extraction.inter_2377 c row := by
    simp only [KeccakfPermAir.extraction.inter_2379, KeccakfPermAir.extraction.inter_2378, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_2377 c row = (mc 331 + mc 651 + mc 1931 - 2*mc 331*mc 651 - 2*mc 331*mc 1931 - 2*mc 651*mc 1931 + 4*mc 331*mc 651*mc 1931) + 2 * KeccakfPermAir.extraction.inter_2375 c row := by
    simp only [KeccakfPermAir.extraction.inter_2377, KeccakfPermAir.extraction.inter_2376, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_2375 c row = (mc 332 + mc 652 + mc 1932 - 2*mc 332*mc 652 - 2*mc 332*mc 1932 - 2*mc 652*mc 1932 + 4*mc 332*mc 652*mc 1932) + 2 * KeccakfPermAir.extraction.inter_2373 c row := by
    simp only [KeccakfPermAir.extraction.inter_2375, KeccakfPermAir.extraction.inter_2374, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_2373 c row = (mc 333 + mc 653 + mc 1933 - 2*mc 333*mc 653 - 2*mc 333*mc 1933 - 2*mc 653*mc 1933 + 4*mc 333*mc 653*mc 1933) + 2 * KeccakfPermAir.extraction.inter_2371 c row := by
    simp only [KeccakfPermAir.extraction.inter_2373, KeccakfPermAir.extraction.inter_2372, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_2371 c row = (mc 334 + mc 654 + mc 1934 - 2*mc 334*mc 654 - 2*mc 334*mc 1934 - 2*mc 654*mc 1934 + 4*mc 334*mc 654*mc 1934) + 2 * KeccakfPermAir.extraction.inter_2369 c row := by
    simp only [KeccakfPermAir.extraction.inter_2371, KeccakfPermAir.extraction.inter_2370, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_2369 c row = (mc 335 + mc 655 + mc 1935 - 2*mc 335*mc 655 - 2*mc 335*mc 1935 - 2*mc 655*mc 1935 + 4*mc 335*mc 655*mc 1935) + 2 * KeccakfPermAir.extraction.inter_2367 c row := by
    simp only [KeccakfPermAir.extraction.inter_2369, KeccakfPermAir.extraction.inter_2368, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_2367 c row = (mc 336 + mc 656 + mc 1936 - 2*mc 336*mc 656 - 2*mc 336*mc 1936 - 2*mc 656*mc 1936 + 4*mc 336*mc 656*mc 1936) := by
    simp only [KeccakfPermAir.extraction.inter_2367, KeccakfPermAir.extraction.inter_2366, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_2045 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 337 657 1937 192 row) :
    mc 192 = (mc 337 + mc 657 + mc 1937 - 2*mc 337*mc 657 - 2*mc 337*mc 1937 - 2*mc 657*mc 1937 + 4*mc 337*mc 657*mc 1937) + 2*(mc 338 + mc 658 + mc 1938 - 2*mc 338*mc 658 - 2*mc 338*mc 1938 - 2*mc 658*mc 1938 + 4*mc 338*mc 658*mc 1938) + 4*(mc 339 + mc 659 + mc 1939 - 2*mc 339*mc 659 - 2*mc 339*mc 1939 - 2*mc 659*mc 1939 + 4*mc 339*mc 659*mc 1939) + 8*(mc 340 + mc 660 + mc 1940 - 2*mc 340*mc 660 - 2*mc 340*mc 1940 - 2*mc 660*mc 1940 + 4*mc 340*mc 660*mc 1940) + 16*(mc 341 + mc 661 + mc 1941 - 2*mc 341*mc 661 - 2*mc 341*mc 1941 - 2*mc 661*mc 1941 + 4*mc 341*mc 661*mc 1941) + 32*(mc 342 + mc 662 + mc 1942 - 2*mc 342*mc 662 - 2*mc 342*mc 1942 - 2*mc 662*mc 1942 + 4*mc 342*mc 662*mc 1942) + 64*(mc 343 + mc 663 + mc 1943 - 2*mc 343*mc 663 - 2*mc 343*mc 1943 - 2*mc 663*mc 1943 + 4*mc 343*mc 663*mc 1943) + 128*(mc 344 + mc 664 + mc 1944 - 2*mc 344*mc 664 - 2*mc 344*mc 1944 - 2*mc 664*mc 1944 + 4*mc 344*mc 664*mc 1944) + 256*(mc 345 + mc 665 + mc 1945 - 2*mc 345*mc 665 - 2*mc 345*mc 1945 - 2*mc 665*mc 1945 + 4*mc 345*mc 665*mc 1945) + 512*(mc 346 + mc 666 + mc 1946 - 2*mc 346*mc 666 - 2*mc 346*mc 1946 - 2*mc 666*mc 1946 + 4*mc 346*mc 666*mc 1946) + 1024*(mc 347 + mc 667 + mc 1947 - 2*mc 347*mc 667 - 2*mc 347*mc 1947 - 2*mc 667*mc 1947 + 4*mc 347*mc 667*mc 1947) + 2048*(mc 348 + mc 668 + mc 1948 - 2*mc 348*mc 668 - 2*mc 348*mc 1948 - 2*mc 668*mc 1948 + 4*mc 348*mc 668*mc 1948) + 4096*(mc 349 + mc 669 + mc 1949 - 2*mc 349*mc 669 - 2*mc 349*mc 1949 - 2*mc 669*mc 1949 + 4*mc 349*mc 669*mc 1949) + 8192*(mc 350 + mc 670 + mc 1950 - 2*mc 350*mc 670 - 2*mc 350*mc 1950 - 2*mc 670*mc 1950 + 4*mc 350*mc 670*mc 1950) + 16384*(mc 351 + mc 671 + mc 1951 - 2*mc 351*mc 671 - 2*mc 351*mc 1951 - 2*mc 671*mc 1951 + 4*mc 351*mc 671*mc 1951) + 32768*(mc 352 + mc 672 + mc 1952 - 2*mc 352*mc 672 - 2*mc 352*mc 1952 - 2*mc 672*mc 1952 + 4*mc 352*mc 672*mc 1952) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_2045, KeccakfPermAir.extraction.inter_2427, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_2426 c row = (mc 338 + mc 658 + mc 1938 - 2*mc 338*mc 658 - 2*mc 338*mc 1938 - 2*mc 658*mc 1938 + 4*mc 338*mc 658*mc 1938) + 2 * KeccakfPermAir.extraction.inter_2424 c row := by
    simp only [KeccakfPermAir.extraction.inter_2426, KeccakfPermAir.extraction.inter_2425, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_2424 c row = (mc 339 + mc 659 + mc 1939 - 2*mc 339*mc 659 - 2*mc 339*mc 1939 - 2*mc 659*mc 1939 + 4*mc 339*mc 659*mc 1939) + 2 * KeccakfPermAir.extraction.inter_2422 c row := by
    simp only [KeccakfPermAir.extraction.inter_2424, KeccakfPermAir.extraction.inter_2423, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_2422 c row = (mc 340 + mc 660 + mc 1940 - 2*mc 340*mc 660 - 2*mc 340*mc 1940 - 2*mc 660*mc 1940 + 4*mc 340*mc 660*mc 1940) + 2 * KeccakfPermAir.extraction.inter_2420 c row := by
    simp only [KeccakfPermAir.extraction.inter_2422, KeccakfPermAir.extraction.inter_2421, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_2420 c row = (mc 341 + mc 661 + mc 1941 - 2*mc 341*mc 661 - 2*mc 341*mc 1941 - 2*mc 661*mc 1941 + 4*mc 341*mc 661*mc 1941) + 2 * KeccakfPermAir.extraction.inter_2418 c row := by
    simp only [KeccakfPermAir.extraction.inter_2420, KeccakfPermAir.extraction.inter_2419, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_2418 c row = (mc 342 + mc 662 + mc 1942 - 2*mc 342*mc 662 - 2*mc 342*mc 1942 - 2*mc 662*mc 1942 + 4*mc 342*mc 662*mc 1942) + 2 * KeccakfPermAir.extraction.inter_2416 c row := by
    simp only [KeccakfPermAir.extraction.inter_2418, KeccakfPermAir.extraction.inter_2417, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_2416 c row = (mc 343 + mc 663 + mc 1943 - 2*mc 343*mc 663 - 2*mc 343*mc 1943 - 2*mc 663*mc 1943 + 4*mc 343*mc 663*mc 1943) + 2 * KeccakfPermAir.extraction.inter_2414 c row := by
    simp only [KeccakfPermAir.extraction.inter_2416, KeccakfPermAir.extraction.inter_2415, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_2414 c row = (mc 344 + mc 664 + mc 1944 - 2*mc 344*mc 664 - 2*mc 344*mc 1944 - 2*mc 664*mc 1944 + 4*mc 344*mc 664*mc 1944) + 2 * KeccakfPermAir.extraction.inter_2412 c row := by
    simp only [KeccakfPermAir.extraction.inter_2414, KeccakfPermAir.extraction.inter_2413, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_2412 c row = (mc 345 + mc 665 + mc 1945 - 2*mc 345*mc 665 - 2*mc 345*mc 1945 - 2*mc 665*mc 1945 + 4*mc 345*mc 665*mc 1945) + 2 * KeccakfPermAir.extraction.inter_2410 c row := by
    simp only [KeccakfPermAir.extraction.inter_2412, KeccakfPermAir.extraction.inter_2411, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_2410 c row = (mc 346 + mc 666 + mc 1946 - 2*mc 346*mc 666 - 2*mc 346*mc 1946 - 2*mc 666*mc 1946 + 4*mc 346*mc 666*mc 1946) + 2 * KeccakfPermAir.extraction.inter_2408 c row := by
    simp only [KeccakfPermAir.extraction.inter_2410, KeccakfPermAir.extraction.inter_2409, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_2408 c row = (mc 347 + mc 667 + mc 1947 - 2*mc 347*mc 667 - 2*mc 347*mc 1947 - 2*mc 667*mc 1947 + 4*mc 347*mc 667*mc 1947) + 2 * KeccakfPermAir.extraction.inter_2406 c row := by
    simp only [KeccakfPermAir.extraction.inter_2408, KeccakfPermAir.extraction.inter_2407, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_2406 c row = (mc 348 + mc 668 + mc 1948 - 2*mc 348*mc 668 - 2*mc 348*mc 1948 - 2*mc 668*mc 1948 + 4*mc 348*mc 668*mc 1948) + 2 * KeccakfPermAir.extraction.inter_2404 c row := by
    simp only [KeccakfPermAir.extraction.inter_2406, KeccakfPermAir.extraction.inter_2405, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_2404 c row = (mc 349 + mc 669 + mc 1949 - 2*mc 349*mc 669 - 2*mc 349*mc 1949 - 2*mc 669*mc 1949 + 4*mc 349*mc 669*mc 1949) + 2 * KeccakfPermAir.extraction.inter_2402 c row := by
    simp only [KeccakfPermAir.extraction.inter_2404, KeccakfPermAir.extraction.inter_2403, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_2402 c row = (mc 350 + mc 670 + mc 1950 - 2*mc 350*mc 670 - 2*mc 350*mc 1950 - 2*mc 670*mc 1950 + 4*mc 350*mc 670*mc 1950) + 2 * KeccakfPermAir.extraction.inter_2400 c row := by
    simp only [KeccakfPermAir.extraction.inter_2402, KeccakfPermAir.extraction.inter_2401, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_2400 c row = (mc 351 + mc 671 + mc 1951 - 2*mc 351*mc 671 - 2*mc 351*mc 1951 - 2*mc 671*mc 1951 + 4*mc 351*mc 671*mc 1951) + 2 * KeccakfPermAir.extraction.inter_2398 c row := by
    simp only [KeccakfPermAir.extraction.inter_2400, KeccakfPermAir.extraction.inter_2399, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_2398 c row = (mc 352 + mc 672 + mc 1952 - 2*mc 352*mc 672 - 2*mc 352*mc 1952 - 2*mc 672*mc 1952 + 4*mc 352*mc 672*mc 1952) := by
    simp only [KeccakfPermAir.extraction.inter_2398, KeccakfPermAir.extraction.inter_2397, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_2110 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 353 673 1953 193 row) :
    mc 193 = (mc 353 + mc 673 + mc 1953 - 2*mc 353*mc 673 - 2*mc 353*mc 1953 - 2*mc 673*mc 1953 + 4*mc 353*mc 673*mc 1953) + 2*(mc 354 + mc 674 + mc 1954 - 2*mc 354*mc 674 - 2*mc 354*mc 1954 - 2*mc 674*mc 1954 + 4*mc 354*mc 674*mc 1954) + 4*(mc 355 + mc 675 + mc 1955 - 2*mc 355*mc 675 - 2*mc 355*mc 1955 - 2*mc 675*mc 1955 + 4*mc 355*mc 675*mc 1955) + 8*(mc 356 + mc 676 + mc 1956 - 2*mc 356*mc 676 - 2*mc 356*mc 1956 - 2*mc 676*mc 1956 + 4*mc 356*mc 676*mc 1956) + 16*(mc 357 + mc 677 + mc 1957 - 2*mc 357*mc 677 - 2*mc 357*mc 1957 - 2*mc 677*mc 1957 + 4*mc 357*mc 677*mc 1957) + 32*(mc 358 + mc 678 + mc 1958 - 2*mc 358*mc 678 - 2*mc 358*mc 1958 - 2*mc 678*mc 1958 + 4*mc 358*mc 678*mc 1958) + 64*(mc 359 + mc 679 + mc 1959 - 2*mc 359*mc 679 - 2*mc 359*mc 1959 - 2*mc 679*mc 1959 + 4*mc 359*mc 679*mc 1959) + 128*(mc 360 + mc 680 + mc 1960 - 2*mc 360*mc 680 - 2*mc 360*mc 1960 - 2*mc 680*mc 1960 + 4*mc 360*mc 680*mc 1960) + 256*(mc 361 + mc 681 + mc 1961 - 2*mc 361*mc 681 - 2*mc 361*mc 1961 - 2*mc 681*mc 1961 + 4*mc 361*mc 681*mc 1961) + 512*(mc 362 + mc 682 + mc 1962 - 2*mc 362*mc 682 - 2*mc 362*mc 1962 - 2*mc 682*mc 1962 + 4*mc 362*mc 682*mc 1962) + 1024*(mc 363 + mc 683 + mc 1963 - 2*mc 363*mc 683 - 2*mc 363*mc 1963 - 2*mc 683*mc 1963 + 4*mc 363*mc 683*mc 1963) + 2048*(mc 364 + mc 684 + mc 1964 - 2*mc 364*mc 684 - 2*mc 364*mc 1964 - 2*mc 684*mc 1964 + 4*mc 364*mc 684*mc 1964) + 4096*(mc 365 + mc 685 + mc 1965 - 2*mc 365*mc 685 - 2*mc 365*mc 1965 - 2*mc 685*mc 1965 + 4*mc 365*mc 685*mc 1965) + 8192*(mc 366 + mc 686 + mc 1966 - 2*mc 366*mc 686 - 2*mc 366*mc 1966 - 2*mc 686*mc 1966 + 4*mc 366*mc 686*mc 1966) + 16384*(mc 367 + mc 687 + mc 1967 - 2*mc 367*mc 687 - 2*mc 367*mc 1967 - 2*mc 687*mc 1967 + 4*mc 367*mc 687*mc 1967) + 32768*(mc 368 + mc 688 + mc 1968 - 2*mc 368*mc 688 - 2*mc 368*mc 1968 - 2*mc 688*mc 1968 + 4*mc 368*mc 688*mc 1968) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_2110, KeccakfPermAir.extraction.inter_2458, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_2457 c row = (mc 354 + mc 674 + mc 1954 - 2*mc 354*mc 674 - 2*mc 354*mc 1954 - 2*mc 674*mc 1954 + 4*mc 354*mc 674*mc 1954) + 2 * KeccakfPermAir.extraction.inter_2455 c row := by
    simp only [KeccakfPermAir.extraction.inter_2457, KeccakfPermAir.extraction.inter_2456, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_2455 c row = (mc 355 + mc 675 + mc 1955 - 2*mc 355*mc 675 - 2*mc 355*mc 1955 - 2*mc 675*mc 1955 + 4*mc 355*mc 675*mc 1955) + 2 * KeccakfPermAir.extraction.inter_2453 c row := by
    simp only [KeccakfPermAir.extraction.inter_2455, KeccakfPermAir.extraction.inter_2454, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_2453 c row = (mc 356 + mc 676 + mc 1956 - 2*mc 356*mc 676 - 2*mc 356*mc 1956 - 2*mc 676*mc 1956 + 4*mc 356*mc 676*mc 1956) + 2 * KeccakfPermAir.extraction.inter_2451 c row := by
    simp only [KeccakfPermAir.extraction.inter_2453, KeccakfPermAir.extraction.inter_2452, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_2451 c row = (mc 357 + mc 677 + mc 1957 - 2*mc 357*mc 677 - 2*mc 357*mc 1957 - 2*mc 677*mc 1957 + 4*mc 357*mc 677*mc 1957) + 2 * KeccakfPermAir.extraction.inter_2449 c row := by
    simp only [KeccakfPermAir.extraction.inter_2451, KeccakfPermAir.extraction.inter_2450, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_2449 c row = (mc 358 + mc 678 + mc 1958 - 2*mc 358*mc 678 - 2*mc 358*mc 1958 - 2*mc 678*mc 1958 + 4*mc 358*mc 678*mc 1958) + 2 * KeccakfPermAir.extraction.inter_2447 c row := by
    simp only [KeccakfPermAir.extraction.inter_2449, KeccakfPermAir.extraction.inter_2448, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_2447 c row = (mc 359 + mc 679 + mc 1959 - 2*mc 359*mc 679 - 2*mc 359*mc 1959 - 2*mc 679*mc 1959 + 4*mc 359*mc 679*mc 1959) + 2 * KeccakfPermAir.extraction.inter_2445 c row := by
    simp only [KeccakfPermAir.extraction.inter_2447, KeccakfPermAir.extraction.inter_2446, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_2445 c row = (mc 360 + mc 680 + mc 1960 - 2*mc 360*mc 680 - 2*mc 360*mc 1960 - 2*mc 680*mc 1960 + 4*mc 360*mc 680*mc 1960) + 2 * KeccakfPermAir.extraction.inter_2443 c row := by
    simp only [KeccakfPermAir.extraction.inter_2445, KeccakfPermAir.extraction.inter_2444, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_2443 c row = (mc 361 + mc 681 + mc 1961 - 2*mc 361*mc 681 - 2*mc 361*mc 1961 - 2*mc 681*mc 1961 + 4*mc 361*mc 681*mc 1961) + 2 * KeccakfPermAir.extraction.inter_2441 c row := by
    simp only [KeccakfPermAir.extraction.inter_2443, KeccakfPermAir.extraction.inter_2442, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_2441 c row = (mc 362 + mc 682 + mc 1962 - 2*mc 362*mc 682 - 2*mc 362*mc 1962 - 2*mc 682*mc 1962 + 4*mc 362*mc 682*mc 1962) + 2 * KeccakfPermAir.extraction.inter_2439 c row := by
    simp only [KeccakfPermAir.extraction.inter_2441, KeccakfPermAir.extraction.inter_2440, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_2439 c row = (mc 363 + mc 683 + mc 1963 - 2*mc 363*mc 683 - 2*mc 363*mc 1963 - 2*mc 683*mc 1963 + 4*mc 363*mc 683*mc 1963) + 2 * KeccakfPermAir.extraction.inter_2437 c row := by
    simp only [KeccakfPermAir.extraction.inter_2439, KeccakfPermAir.extraction.inter_2438, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_2437 c row = (mc 364 + mc 684 + mc 1964 - 2*mc 364*mc 684 - 2*mc 364*mc 1964 - 2*mc 684*mc 1964 + 4*mc 364*mc 684*mc 1964) + 2 * KeccakfPermAir.extraction.inter_2435 c row := by
    simp only [KeccakfPermAir.extraction.inter_2437, KeccakfPermAir.extraction.inter_2436, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_2435 c row = (mc 365 + mc 685 + mc 1965 - 2*mc 365*mc 685 - 2*mc 365*mc 1965 - 2*mc 685*mc 1965 + 4*mc 365*mc 685*mc 1965) + 2 * KeccakfPermAir.extraction.inter_2433 c row := by
    simp only [KeccakfPermAir.extraction.inter_2435, KeccakfPermAir.extraction.inter_2434, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_2433 c row = (mc 366 + mc 686 + mc 1966 - 2*mc 366*mc 686 - 2*mc 366*mc 1966 - 2*mc 686*mc 1966 + 4*mc 366*mc 686*mc 1966) + 2 * KeccakfPermAir.extraction.inter_2431 c row := by
    simp only [KeccakfPermAir.extraction.inter_2433, KeccakfPermAir.extraction.inter_2432, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_2431 c row = (mc 367 + mc 687 + mc 1967 - 2*mc 367*mc 687 - 2*mc 367*mc 1967 - 2*mc 687*mc 1967 + 4*mc 367*mc 687*mc 1967) + 2 * KeccakfPermAir.extraction.inter_2429 c row := by
    simp only [KeccakfPermAir.extraction.inter_2431, KeccakfPermAir.extraction.inter_2430, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_2429 c row = (mc 368 + mc 688 + mc 1968 - 2*mc 368*mc 688 - 2*mc 368*mc 1968 - 2*mc 688*mc 1968 + 4*mc 368*mc 688*mc 1968) := by
    simp only [KeccakfPermAir.extraction.inter_2429, KeccakfPermAir.extraction.inter_2428, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_2111 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 369 689 1969 194 row) :
    mc 194 = (mc 369 + mc 689 + mc 1969 - 2*mc 369*mc 689 - 2*mc 369*mc 1969 - 2*mc 689*mc 1969 + 4*mc 369*mc 689*mc 1969) + 2*(mc 370 + mc 690 + mc 1970 - 2*mc 370*mc 690 - 2*mc 370*mc 1970 - 2*mc 690*mc 1970 + 4*mc 370*mc 690*mc 1970) + 4*(mc 371 + mc 691 + mc 1971 - 2*mc 371*mc 691 - 2*mc 371*mc 1971 - 2*mc 691*mc 1971 + 4*mc 371*mc 691*mc 1971) + 8*(mc 372 + mc 692 + mc 1972 - 2*mc 372*mc 692 - 2*mc 372*mc 1972 - 2*mc 692*mc 1972 + 4*mc 372*mc 692*mc 1972) + 16*(mc 373 + mc 693 + mc 1973 - 2*mc 373*mc 693 - 2*mc 373*mc 1973 - 2*mc 693*mc 1973 + 4*mc 373*mc 693*mc 1973) + 32*(mc 374 + mc 694 + mc 1974 - 2*mc 374*mc 694 - 2*mc 374*mc 1974 - 2*mc 694*mc 1974 + 4*mc 374*mc 694*mc 1974) + 64*(mc 375 + mc 695 + mc 1975 - 2*mc 375*mc 695 - 2*mc 375*mc 1975 - 2*mc 695*mc 1975 + 4*mc 375*mc 695*mc 1975) + 128*(mc 376 + mc 696 + mc 1976 - 2*mc 376*mc 696 - 2*mc 376*mc 1976 - 2*mc 696*mc 1976 + 4*mc 376*mc 696*mc 1976) + 256*(mc 377 + mc 697 + mc 1977 - 2*mc 377*mc 697 - 2*mc 377*mc 1977 - 2*mc 697*mc 1977 + 4*mc 377*mc 697*mc 1977) + 512*(mc 378 + mc 698 + mc 1978 - 2*mc 378*mc 698 - 2*mc 378*mc 1978 - 2*mc 698*mc 1978 + 4*mc 378*mc 698*mc 1978) + 1024*(mc 379 + mc 699 + mc 1979 - 2*mc 379*mc 699 - 2*mc 379*mc 1979 - 2*mc 699*mc 1979 + 4*mc 379*mc 699*mc 1979) + 2048*(mc 380 + mc 700 + mc 1980 - 2*mc 380*mc 700 - 2*mc 380*mc 1980 - 2*mc 700*mc 1980 + 4*mc 380*mc 700*mc 1980) + 4096*(mc 381 + mc 701 + mc 1981 - 2*mc 381*mc 701 - 2*mc 381*mc 1981 - 2*mc 701*mc 1981 + 4*mc 381*mc 701*mc 1981) + 8192*(mc 382 + mc 702 + mc 1982 - 2*mc 382*mc 702 - 2*mc 382*mc 1982 - 2*mc 702*mc 1982 + 4*mc 382*mc 702*mc 1982) + 16384*(mc 383 + mc 703 + mc 1983 - 2*mc 383*mc 703 - 2*mc 383*mc 1983 - 2*mc 703*mc 1983 + 4*mc 383*mc 703*mc 1983) + 32768*(mc 384 + mc 704 + mc 1984 - 2*mc 384*mc 704 - 2*mc 384*mc 1984 - 2*mc 704*mc 1984 + 4*mc 384*mc 704*mc 1984) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_2111, KeccakfPermAir.extraction.inter_2489, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_2488 c row = (mc 370 + mc 690 + mc 1970 - 2*mc 370*mc 690 - 2*mc 370*mc 1970 - 2*mc 690*mc 1970 + 4*mc 370*mc 690*mc 1970) + 2 * KeccakfPermAir.extraction.inter_2486 c row := by
    simp only [KeccakfPermAir.extraction.inter_2488, KeccakfPermAir.extraction.inter_2487, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_2486 c row = (mc 371 + mc 691 + mc 1971 - 2*mc 371*mc 691 - 2*mc 371*mc 1971 - 2*mc 691*mc 1971 + 4*mc 371*mc 691*mc 1971) + 2 * KeccakfPermAir.extraction.inter_2484 c row := by
    simp only [KeccakfPermAir.extraction.inter_2486, KeccakfPermAir.extraction.inter_2485, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_2484 c row = (mc 372 + mc 692 + mc 1972 - 2*mc 372*mc 692 - 2*mc 372*mc 1972 - 2*mc 692*mc 1972 + 4*mc 372*mc 692*mc 1972) + 2 * KeccakfPermAir.extraction.inter_2482 c row := by
    simp only [KeccakfPermAir.extraction.inter_2484, KeccakfPermAir.extraction.inter_2483, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_2482 c row = (mc 373 + mc 693 + mc 1973 - 2*mc 373*mc 693 - 2*mc 373*mc 1973 - 2*mc 693*mc 1973 + 4*mc 373*mc 693*mc 1973) + 2 * KeccakfPermAir.extraction.inter_2480 c row := by
    simp only [KeccakfPermAir.extraction.inter_2482, KeccakfPermAir.extraction.inter_2481, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_2480 c row = (mc 374 + mc 694 + mc 1974 - 2*mc 374*mc 694 - 2*mc 374*mc 1974 - 2*mc 694*mc 1974 + 4*mc 374*mc 694*mc 1974) + 2 * KeccakfPermAir.extraction.inter_2478 c row := by
    simp only [KeccakfPermAir.extraction.inter_2480, KeccakfPermAir.extraction.inter_2479, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_2478 c row = (mc 375 + mc 695 + mc 1975 - 2*mc 375*mc 695 - 2*mc 375*mc 1975 - 2*mc 695*mc 1975 + 4*mc 375*mc 695*mc 1975) + 2 * KeccakfPermAir.extraction.inter_2476 c row := by
    simp only [KeccakfPermAir.extraction.inter_2478, KeccakfPermAir.extraction.inter_2477, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_2476 c row = (mc 376 + mc 696 + mc 1976 - 2*mc 376*mc 696 - 2*mc 376*mc 1976 - 2*mc 696*mc 1976 + 4*mc 376*mc 696*mc 1976) + 2 * KeccakfPermAir.extraction.inter_2474 c row := by
    simp only [KeccakfPermAir.extraction.inter_2476, KeccakfPermAir.extraction.inter_2475, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_2474 c row = (mc 377 + mc 697 + mc 1977 - 2*mc 377*mc 697 - 2*mc 377*mc 1977 - 2*mc 697*mc 1977 + 4*mc 377*mc 697*mc 1977) + 2 * KeccakfPermAir.extraction.inter_2472 c row := by
    simp only [KeccakfPermAir.extraction.inter_2474, KeccakfPermAir.extraction.inter_2473, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_2472 c row = (mc 378 + mc 698 + mc 1978 - 2*mc 378*mc 698 - 2*mc 378*mc 1978 - 2*mc 698*mc 1978 + 4*mc 378*mc 698*mc 1978) + 2 * KeccakfPermAir.extraction.inter_2470 c row := by
    simp only [KeccakfPermAir.extraction.inter_2472, KeccakfPermAir.extraction.inter_2471, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_2470 c row = (mc 379 + mc 699 + mc 1979 - 2*mc 379*mc 699 - 2*mc 379*mc 1979 - 2*mc 699*mc 1979 + 4*mc 379*mc 699*mc 1979) + 2 * KeccakfPermAir.extraction.inter_2468 c row := by
    simp only [KeccakfPermAir.extraction.inter_2470, KeccakfPermAir.extraction.inter_2469, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_2468 c row = (mc 380 + mc 700 + mc 1980 - 2*mc 380*mc 700 - 2*mc 380*mc 1980 - 2*mc 700*mc 1980 + 4*mc 380*mc 700*mc 1980) + 2 * KeccakfPermAir.extraction.inter_2466 c row := by
    simp only [KeccakfPermAir.extraction.inter_2468, KeccakfPermAir.extraction.inter_2467, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_2466 c row = (mc 381 + mc 701 + mc 1981 - 2*mc 381*mc 701 - 2*mc 381*mc 1981 - 2*mc 701*mc 1981 + 4*mc 381*mc 701*mc 1981) + 2 * KeccakfPermAir.extraction.inter_2464 c row := by
    simp only [KeccakfPermAir.extraction.inter_2466, KeccakfPermAir.extraction.inter_2465, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_2464 c row = (mc 382 + mc 702 + mc 1982 - 2*mc 382*mc 702 - 2*mc 382*mc 1982 - 2*mc 702*mc 1982 + 4*mc 382*mc 702*mc 1982) + 2 * KeccakfPermAir.extraction.inter_2462 c row := by
    simp only [KeccakfPermAir.extraction.inter_2464, KeccakfPermAir.extraction.inter_2463, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_2462 c row = (mc 383 + mc 703 + mc 1983 - 2*mc 383*mc 703 - 2*mc 383*mc 1983 - 2*mc 703*mc 1983 + 4*mc 383*mc 703*mc 1983) + 2 * KeccakfPermAir.extraction.inter_2460 c row := by
    simp only [KeccakfPermAir.extraction.inter_2462, KeccakfPermAir.extraction.inter_2461, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_2460 c row = (mc 384 + mc 704 + mc 1984 - 2*mc 384*mc 704 - 2*mc 384*mc 1984 - 2*mc 704*mc 1984 + 4*mc 384*mc 704*mc 1984) := by
    simp only [KeccakfPermAir.extraction.inter_2460, KeccakfPermAir.extraction.inter_2459, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_2112 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 385 705 1985 195 row) :
    mc 195 = (mc 385 + mc 705 + mc 1985 - 2*mc 385*mc 705 - 2*mc 385*mc 1985 - 2*mc 705*mc 1985 + 4*mc 385*mc 705*mc 1985) + 2*(mc 386 + mc 706 + mc 1986 - 2*mc 386*mc 706 - 2*mc 386*mc 1986 - 2*mc 706*mc 1986 + 4*mc 386*mc 706*mc 1986) + 4*(mc 387 + mc 707 + mc 1987 - 2*mc 387*mc 707 - 2*mc 387*mc 1987 - 2*mc 707*mc 1987 + 4*mc 387*mc 707*mc 1987) + 8*(mc 388 + mc 708 + mc 1988 - 2*mc 388*mc 708 - 2*mc 388*mc 1988 - 2*mc 708*mc 1988 + 4*mc 388*mc 708*mc 1988) + 16*(mc 389 + mc 709 + mc 1989 - 2*mc 389*mc 709 - 2*mc 389*mc 1989 - 2*mc 709*mc 1989 + 4*mc 389*mc 709*mc 1989) + 32*(mc 390 + mc 710 + mc 1990 - 2*mc 390*mc 710 - 2*mc 390*mc 1990 - 2*mc 710*mc 1990 + 4*mc 390*mc 710*mc 1990) + 64*(mc 391 + mc 711 + mc 1991 - 2*mc 391*mc 711 - 2*mc 391*mc 1991 - 2*mc 711*mc 1991 + 4*mc 391*mc 711*mc 1991) + 128*(mc 392 + mc 712 + mc 1992 - 2*mc 392*mc 712 - 2*mc 392*mc 1992 - 2*mc 712*mc 1992 + 4*mc 392*mc 712*mc 1992) + 256*(mc 393 + mc 713 + mc 1993 - 2*mc 393*mc 713 - 2*mc 393*mc 1993 - 2*mc 713*mc 1993 + 4*mc 393*mc 713*mc 1993) + 512*(mc 394 + mc 714 + mc 1994 - 2*mc 394*mc 714 - 2*mc 394*mc 1994 - 2*mc 714*mc 1994 + 4*mc 394*mc 714*mc 1994) + 1024*(mc 395 + mc 715 + mc 1995 - 2*mc 395*mc 715 - 2*mc 395*mc 1995 - 2*mc 715*mc 1995 + 4*mc 395*mc 715*mc 1995) + 2048*(mc 396 + mc 716 + mc 1996 - 2*mc 396*mc 716 - 2*mc 396*mc 1996 - 2*mc 716*mc 1996 + 4*mc 396*mc 716*mc 1996) + 4096*(mc 397 + mc 717 + mc 1997 - 2*mc 397*mc 717 - 2*mc 397*mc 1997 - 2*mc 717*mc 1997 + 4*mc 397*mc 717*mc 1997) + 8192*(mc 398 + mc 718 + mc 1998 - 2*mc 398*mc 718 - 2*mc 398*mc 1998 - 2*mc 718*mc 1998 + 4*mc 398*mc 718*mc 1998) + 16384*(mc 399 + mc 719 + mc 1999 - 2*mc 399*mc 719 - 2*mc 399*mc 1999 - 2*mc 719*mc 1999 + 4*mc 399*mc 719*mc 1999) + 32768*(mc 400 + mc 720 + mc 2000 - 2*mc 400*mc 720 - 2*mc 400*mc 2000 - 2*mc 720*mc 2000 + 4*mc 400*mc 720*mc 2000) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_2112, KeccakfPermAir.extraction.inter_2520, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_2519 c row = (mc 386 + mc 706 + mc 1986 - 2*mc 386*mc 706 - 2*mc 386*mc 1986 - 2*mc 706*mc 1986 + 4*mc 386*mc 706*mc 1986) + 2 * KeccakfPermAir.extraction.inter_2517 c row := by
    simp only [KeccakfPermAir.extraction.inter_2519, KeccakfPermAir.extraction.inter_2518, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_2517 c row = (mc 387 + mc 707 + mc 1987 - 2*mc 387*mc 707 - 2*mc 387*mc 1987 - 2*mc 707*mc 1987 + 4*mc 387*mc 707*mc 1987) + 2 * KeccakfPermAir.extraction.inter_2515 c row := by
    simp only [KeccakfPermAir.extraction.inter_2517, KeccakfPermAir.extraction.inter_2516, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_2515 c row = (mc 388 + mc 708 + mc 1988 - 2*mc 388*mc 708 - 2*mc 388*mc 1988 - 2*mc 708*mc 1988 + 4*mc 388*mc 708*mc 1988) + 2 * KeccakfPermAir.extraction.inter_2513 c row := by
    simp only [KeccakfPermAir.extraction.inter_2515, KeccakfPermAir.extraction.inter_2514, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_2513 c row = (mc 389 + mc 709 + mc 1989 - 2*mc 389*mc 709 - 2*mc 389*mc 1989 - 2*mc 709*mc 1989 + 4*mc 389*mc 709*mc 1989) + 2 * KeccakfPermAir.extraction.inter_2511 c row := by
    simp only [KeccakfPermAir.extraction.inter_2513, KeccakfPermAir.extraction.inter_2512, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_2511 c row = (mc 390 + mc 710 + mc 1990 - 2*mc 390*mc 710 - 2*mc 390*mc 1990 - 2*mc 710*mc 1990 + 4*mc 390*mc 710*mc 1990) + 2 * KeccakfPermAir.extraction.inter_2509 c row := by
    simp only [KeccakfPermAir.extraction.inter_2511, KeccakfPermAir.extraction.inter_2510, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_2509 c row = (mc 391 + mc 711 + mc 1991 - 2*mc 391*mc 711 - 2*mc 391*mc 1991 - 2*mc 711*mc 1991 + 4*mc 391*mc 711*mc 1991) + 2 * KeccakfPermAir.extraction.inter_2507 c row := by
    simp only [KeccakfPermAir.extraction.inter_2509, KeccakfPermAir.extraction.inter_2508, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_2507 c row = (mc 392 + mc 712 + mc 1992 - 2*mc 392*mc 712 - 2*mc 392*mc 1992 - 2*mc 712*mc 1992 + 4*mc 392*mc 712*mc 1992) + 2 * KeccakfPermAir.extraction.inter_2505 c row := by
    simp only [KeccakfPermAir.extraction.inter_2507, KeccakfPermAir.extraction.inter_2506, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_2505 c row = (mc 393 + mc 713 + mc 1993 - 2*mc 393*mc 713 - 2*mc 393*mc 1993 - 2*mc 713*mc 1993 + 4*mc 393*mc 713*mc 1993) + 2 * KeccakfPermAir.extraction.inter_2503 c row := by
    simp only [KeccakfPermAir.extraction.inter_2505, KeccakfPermAir.extraction.inter_2504, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_2503 c row = (mc 394 + mc 714 + mc 1994 - 2*mc 394*mc 714 - 2*mc 394*mc 1994 - 2*mc 714*mc 1994 + 4*mc 394*mc 714*mc 1994) + 2 * KeccakfPermAir.extraction.inter_2501 c row := by
    simp only [KeccakfPermAir.extraction.inter_2503, KeccakfPermAir.extraction.inter_2502, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_2501 c row = (mc 395 + mc 715 + mc 1995 - 2*mc 395*mc 715 - 2*mc 395*mc 1995 - 2*mc 715*mc 1995 + 4*mc 395*mc 715*mc 1995) + 2 * KeccakfPermAir.extraction.inter_2499 c row := by
    simp only [KeccakfPermAir.extraction.inter_2501, KeccakfPermAir.extraction.inter_2500, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_2499 c row = (mc 396 + mc 716 + mc 1996 - 2*mc 396*mc 716 - 2*mc 396*mc 1996 - 2*mc 716*mc 1996 + 4*mc 396*mc 716*mc 1996) + 2 * KeccakfPermAir.extraction.inter_2497 c row := by
    simp only [KeccakfPermAir.extraction.inter_2499, KeccakfPermAir.extraction.inter_2498, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_2497 c row = (mc 397 + mc 717 + mc 1997 - 2*mc 397*mc 717 - 2*mc 397*mc 1997 - 2*mc 717*mc 1997 + 4*mc 397*mc 717*mc 1997) + 2 * KeccakfPermAir.extraction.inter_2495 c row := by
    simp only [KeccakfPermAir.extraction.inter_2497, KeccakfPermAir.extraction.inter_2496, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_2495 c row = (mc 398 + mc 718 + mc 1998 - 2*mc 398*mc 718 - 2*mc 398*mc 1998 - 2*mc 718*mc 1998 + 4*mc 398*mc 718*mc 1998) + 2 * KeccakfPermAir.extraction.inter_2493 c row := by
    simp only [KeccakfPermAir.extraction.inter_2495, KeccakfPermAir.extraction.inter_2494, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_2493 c row = (mc 399 + mc 719 + mc 1999 - 2*mc 399*mc 719 - 2*mc 399*mc 1999 - 2*mc 719*mc 1999 + 4*mc 399*mc 719*mc 1999) + 2 * KeccakfPermAir.extraction.inter_2491 c row := by
    simp only [KeccakfPermAir.extraction.inter_2493, KeccakfPermAir.extraction.inter_2492, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_2491 c row = (mc 400 + mc 720 + mc 2000 - 2*mc 400*mc 720 - 2*mc 400*mc 2000 - 2*mc 720*mc 2000 + 4*mc 400*mc 720*mc 2000) := by
    simp only [KeccakfPermAir.extraction.inter_2491, KeccakfPermAir.extraction.inter_2490, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_2113 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 401 721 2001 196 row) :
    mc 196 = (mc 401 + mc 721 + mc 2001 - 2*mc 401*mc 721 - 2*mc 401*mc 2001 - 2*mc 721*mc 2001 + 4*mc 401*mc 721*mc 2001) + 2*(mc 402 + mc 722 + mc 2002 - 2*mc 402*mc 722 - 2*mc 402*mc 2002 - 2*mc 722*mc 2002 + 4*mc 402*mc 722*mc 2002) + 4*(mc 403 + mc 723 + mc 2003 - 2*mc 403*mc 723 - 2*mc 403*mc 2003 - 2*mc 723*mc 2003 + 4*mc 403*mc 723*mc 2003) + 8*(mc 404 + mc 724 + mc 2004 - 2*mc 404*mc 724 - 2*mc 404*mc 2004 - 2*mc 724*mc 2004 + 4*mc 404*mc 724*mc 2004) + 16*(mc 405 + mc 725 + mc 2005 - 2*mc 405*mc 725 - 2*mc 405*mc 2005 - 2*mc 725*mc 2005 + 4*mc 405*mc 725*mc 2005) + 32*(mc 406 + mc 726 + mc 2006 - 2*mc 406*mc 726 - 2*mc 406*mc 2006 - 2*mc 726*mc 2006 + 4*mc 406*mc 726*mc 2006) + 64*(mc 407 + mc 727 + mc 2007 - 2*mc 407*mc 727 - 2*mc 407*mc 2007 - 2*mc 727*mc 2007 + 4*mc 407*mc 727*mc 2007) + 128*(mc 408 + mc 728 + mc 2008 - 2*mc 408*mc 728 - 2*mc 408*mc 2008 - 2*mc 728*mc 2008 + 4*mc 408*mc 728*mc 2008) + 256*(mc 409 + mc 729 + mc 2009 - 2*mc 409*mc 729 - 2*mc 409*mc 2009 - 2*mc 729*mc 2009 + 4*mc 409*mc 729*mc 2009) + 512*(mc 410 + mc 730 + mc 2010 - 2*mc 410*mc 730 - 2*mc 410*mc 2010 - 2*mc 730*mc 2010 + 4*mc 410*mc 730*mc 2010) + 1024*(mc 411 + mc 731 + mc 2011 - 2*mc 411*mc 731 - 2*mc 411*mc 2011 - 2*mc 731*mc 2011 + 4*mc 411*mc 731*mc 2011) + 2048*(mc 412 + mc 732 + mc 2012 - 2*mc 412*mc 732 - 2*mc 412*mc 2012 - 2*mc 732*mc 2012 + 4*mc 412*mc 732*mc 2012) + 4096*(mc 413 + mc 733 + mc 2013 - 2*mc 413*mc 733 - 2*mc 413*mc 2013 - 2*mc 733*mc 2013 + 4*mc 413*mc 733*mc 2013) + 8192*(mc 414 + mc 734 + mc 2014 - 2*mc 414*mc 734 - 2*mc 414*mc 2014 - 2*mc 734*mc 2014 + 4*mc 414*mc 734*mc 2014) + 16384*(mc 415 + mc 735 + mc 2015 - 2*mc 415*mc 735 - 2*mc 415*mc 2015 - 2*mc 735*mc 2015 + 4*mc 415*mc 735*mc 2015) + 32768*(mc 416 + mc 736 + mc 2016 - 2*mc 416*mc 736 - 2*mc 416*mc 2016 - 2*mc 736*mc 2016 + 4*mc 416*mc 736*mc 2016) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_2113, KeccakfPermAir.extraction.inter_2551, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_2550 c row = (mc 402 + mc 722 + mc 2002 - 2*mc 402*mc 722 - 2*mc 402*mc 2002 - 2*mc 722*mc 2002 + 4*mc 402*mc 722*mc 2002) + 2 * KeccakfPermAir.extraction.inter_2548 c row := by
    simp only [KeccakfPermAir.extraction.inter_2550, KeccakfPermAir.extraction.inter_2549, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_2548 c row = (mc 403 + mc 723 + mc 2003 - 2*mc 403*mc 723 - 2*mc 403*mc 2003 - 2*mc 723*mc 2003 + 4*mc 403*mc 723*mc 2003) + 2 * KeccakfPermAir.extraction.inter_2546 c row := by
    simp only [KeccakfPermAir.extraction.inter_2548, KeccakfPermAir.extraction.inter_2547, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_2546 c row = (mc 404 + mc 724 + mc 2004 - 2*mc 404*mc 724 - 2*mc 404*mc 2004 - 2*mc 724*mc 2004 + 4*mc 404*mc 724*mc 2004) + 2 * KeccakfPermAir.extraction.inter_2544 c row := by
    simp only [KeccakfPermAir.extraction.inter_2546, KeccakfPermAir.extraction.inter_2545, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_2544 c row = (mc 405 + mc 725 + mc 2005 - 2*mc 405*mc 725 - 2*mc 405*mc 2005 - 2*mc 725*mc 2005 + 4*mc 405*mc 725*mc 2005) + 2 * KeccakfPermAir.extraction.inter_2542 c row := by
    simp only [KeccakfPermAir.extraction.inter_2544, KeccakfPermAir.extraction.inter_2543, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_2542 c row = (mc 406 + mc 726 + mc 2006 - 2*mc 406*mc 726 - 2*mc 406*mc 2006 - 2*mc 726*mc 2006 + 4*mc 406*mc 726*mc 2006) + 2 * KeccakfPermAir.extraction.inter_2540 c row := by
    simp only [KeccakfPermAir.extraction.inter_2542, KeccakfPermAir.extraction.inter_2541, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_2540 c row = (mc 407 + mc 727 + mc 2007 - 2*mc 407*mc 727 - 2*mc 407*mc 2007 - 2*mc 727*mc 2007 + 4*mc 407*mc 727*mc 2007) + 2 * KeccakfPermAir.extraction.inter_2538 c row := by
    simp only [KeccakfPermAir.extraction.inter_2540, KeccakfPermAir.extraction.inter_2539, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_2538 c row = (mc 408 + mc 728 + mc 2008 - 2*mc 408*mc 728 - 2*mc 408*mc 2008 - 2*mc 728*mc 2008 + 4*mc 408*mc 728*mc 2008) + 2 * KeccakfPermAir.extraction.inter_2536 c row := by
    simp only [KeccakfPermAir.extraction.inter_2538, KeccakfPermAir.extraction.inter_2537, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_2536 c row = (mc 409 + mc 729 + mc 2009 - 2*mc 409*mc 729 - 2*mc 409*mc 2009 - 2*mc 729*mc 2009 + 4*mc 409*mc 729*mc 2009) + 2 * KeccakfPermAir.extraction.inter_2534 c row := by
    simp only [KeccakfPermAir.extraction.inter_2536, KeccakfPermAir.extraction.inter_2535, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_2534 c row = (mc 410 + mc 730 + mc 2010 - 2*mc 410*mc 730 - 2*mc 410*mc 2010 - 2*mc 730*mc 2010 + 4*mc 410*mc 730*mc 2010) + 2 * KeccakfPermAir.extraction.inter_2532 c row := by
    simp only [KeccakfPermAir.extraction.inter_2534, KeccakfPermAir.extraction.inter_2533, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_2532 c row = (mc 411 + mc 731 + mc 2011 - 2*mc 411*mc 731 - 2*mc 411*mc 2011 - 2*mc 731*mc 2011 + 4*mc 411*mc 731*mc 2011) + 2 * KeccakfPermAir.extraction.inter_2530 c row := by
    simp only [KeccakfPermAir.extraction.inter_2532, KeccakfPermAir.extraction.inter_2531, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_2530 c row = (mc 412 + mc 732 + mc 2012 - 2*mc 412*mc 732 - 2*mc 412*mc 2012 - 2*mc 732*mc 2012 + 4*mc 412*mc 732*mc 2012) + 2 * KeccakfPermAir.extraction.inter_2528 c row := by
    simp only [KeccakfPermAir.extraction.inter_2530, KeccakfPermAir.extraction.inter_2529, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_2528 c row = (mc 413 + mc 733 + mc 2013 - 2*mc 413*mc 733 - 2*mc 413*mc 2013 - 2*mc 733*mc 2013 + 4*mc 413*mc 733*mc 2013) + 2 * KeccakfPermAir.extraction.inter_2526 c row := by
    simp only [KeccakfPermAir.extraction.inter_2528, KeccakfPermAir.extraction.inter_2527, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_2526 c row = (mc 414 + mc 734 + mc 2014 - 2*mc 414*mc 734 - 2*mc 414*mc 2014 - 2*mc 734*mc 2014 + 4*mc 414*mc 734*mc 2014) + 2 * KeccakfPermAir.extraction.inter_2524 c row := by
    simp only [KeccakfPermAir.extraction.inter_2526, KeccakfPermAir.extraction.inter_2525, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_2524 c row = (mc 415 + mc 735 + mc 2015 - 2*mc 415*mc 735 - 2*mc 415*mc 2015 - 2*mc 735*mc 2015 + 4*mc 415*mc 735*mc 2015) + 2 * KeccakfPermAir.extraction.inter_2522 c row := by
    simp only [KeccakfPermAir.extraction.inter_2524, KeccakfPermAir.extraction.inter_2523, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_2522 c row = (mc 416 + mc 736 + mc 2016 - 2*mc 416*mc 736 - 2*mc 416*mc 2016 - 2*mc 736*mc 2016 + 4*mc 416*mc 736*mc 2016) := by
    simp only [KeccakfPermAir.extraction.inter_2522, KeccakfPermAir.extraction.inter_2521, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_2178 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 417 737 2017 197 row) :
    mc 197 = (mc 417 + mc 737 + mc 2017 - 2*mc 417*mc 737 - 2*mc 417*mc 2017 - 2*mc 737*mc 2017 + 4*mc 417*mc 737*mc 2017) + 2*(mc 418 + mc 738 + mc 2018 - 2*mc 418*mc 738 - 2*mc 418*mc 2018 - 2*mc 738*mc 2018 + 4*mc 418*mc 738*mc 2018) + 4*(mc 419 + mc 739 + mc 2019 - 2*mc 419*mc 739 - 2*mc 419*mc 2019 - 2*mc 739*mc 2019 + 4*mc 419*mc 739*mc 2019) + 8*(mc 420 + mc 740 + mc 2020 - 2*mc 420*mc 740 - 2*mc 420*mc 2020 - 2*mc 740*mc 2020 + 4*mc 420*mc 740*mc 2020) + 16*(mc 421 + mc 741 + mc 2021 - 2*mc 421*mc 741 - 2*mc 421*mc 2021 - 2*mc 741*mc 2021 + 4*mc 421*mc 741*mc 2021) + 32*(mc 422 + mc 742 + mc 2022 - 2*mc 422*mc 742 - 2*mc 422*mc 2022 - 2*mc 742*mc 2022 + 4*mc 422*mc 742*mc 2022) + 64*(mc 423 + mc 743 + mc 2023 - 2*mc 423*mc 743 - 2*mc 423*mc 2023 - 2*mc 743*mc 2023 + 4*mc 423*mc 743*mc 2023) + 128*(mc 424 + mc 744 + mc 2024 - 2*mc 424*mc 744 - 2*mc 424*mc 2024 - 2*mc 744*mc 2024 + 4*mc 424*mc 744*mc 2024) + 256*(mc 425 + mc 745 + mc 2025 - 2*mc 425*mc 745 - 2*mc 425*mc 2025 - 2*mc 745*mc 2025 + 4*mc 425*mc 745*mc 2025) + 512*(mc 426 + mc 746 + mc 2026 - 2*mc 426*mc 746 - 2*mc 426*mc 2026 - 2*mc 746*mc 2026 + 4*mc 426*mc 746*mc 2026) + 1024*(mc 427 + mc 747 + mc 2027 - 2*mc 427*mc 747 - 2*mc 427*mc 2027 - 2*mc 747*mc 2027 + 4*mc 427*mc 747*mc 2027) + 2048*(mc 428 + mc 748 + mc 2028 - 2*mc 428*mc 748 - 2*mc 428*mc 2028 - 2*mc 748*mc 2028 + 4*mc 428*mc 748*mc 2028) + 4096*(mc 429 + mc 749 + mc 2029 - 2*mc 429*mc 749 - 2*mc 429*mc 2029 - 2*mc 749*mc 2029 + 4*mc 429*mc 749*mc 2029) + 8192*(mc 430 + mc 750 + mc 2030 - 2*mc 430*mc 750 - 2*mc 430*mc 2030 - 2*mc 750*mc 2030 + 4*mc 430*mc 750*mc 2030) + 16384*(mc 431 + mc 751 + mc 2031 - 2*mc 431*mc 751 - 2*mc 431*mc 2031 - 2*mc 751*mc 2031 + 4*mc 431*mc 751*mc 2031) + 32768*(mc 432 + mc 752 + mc 2032 - 2*mc 432*mc 752 - 2*mc 432*mc 2032 - 2*mc 752*mc 2032 + 4*mc 432*mc 752*mc 2032) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_2178, KeccakfPermAir.extraction.inter_2582, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_2581 c row = (mc 418 + mc 738 + mc 2018 - 2*mc 418*mc 738 - 2*mc 418*mc 2018 - 2*mc 738*mc 2018 + 4*mc 418*mc 738*mc 2018) + 2 * KeccakfPermAir.extraction.inter_2579 c row := by
    simp only [KeccakfPermAir.extraction.inter_2581, KeccakfPermAir.extraction.inter_2580, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_2579 c row = (mc 419 + mc 739 + mc 2019 - 2*mc 419*mc 739 - 2*mc 419*mc 2019 - 2*mc 739*mc 2019 + 4*mc 419*mc 739*mc 2019) + 2 * KeccakfPermAir.extraction.inter_2577 c row := by
    simp only [KeccakfPermAir.extraction.inter_2579, KeccakfPermAir.extraction.inter_2578, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_2577 c row = (mc 420 + mc 740 + mc 2020 - 2*mc 420*mc 740 - 2*mc 420*mc 2020 - 2*mc 740*mc 2020 + 4*mc 420*mc 740*mc 2020) + 2 * KeccakfPermAir.extraction.inter_2575 c row := by
    simp only [KeccakfPermAir.extraction.inter_2577, KeccakfPermAir.extraction.inter_2576, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_2575 c row = (mc 421 + mc 741 + mc 2021 - 2*mc 421*mc 741 - 2*mc 421*mc 2021 - 2*mc 741*mc 2021 + 4*mc 421*mc 741*mc 2021) + 2 * KeccakfPermAir.extraction.inter_2573 c row := by
    simp only [KeccakfPermAir.extraction.inter_2575, KeccakfPermAir.extraction.inter_2574, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_2573 c row = (mc 422 + mc 742 + mc 2022 - 2*mc 422*mc 742 - 2*mc 422*mc 2022 - 2*mc 742*mc 2022 + 4*mc 422*mc 742*mc 2022) + 2 * KeccakfPermAir.extraction.inter_2571 c row := by
    simp only [KeccakfPermAir.extraction.inter_2573, KeccakfPermAir.extraction.inter_2572, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_2571 c row = (mc 423 + mc 743 + mc 2023 - 2*mc 423*mc 743 - 2*mc 423*mc 2023 - 2*mc 743*mc 2023 + 4*mc 423*mc 743*mc 2023) + 2 * KeccakfPermAir.extraction.inter_2569 c row := by
    simp only [KeccakfPermAir.extraction.inter_2571, KeccakfPermAir.extraction.inter_2570, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_2569 c row = (mc 424 + mc 744 + mc 2024 - 2*mc 424*mc 744 - 2*mc 424*mc 2024 - 2*mc 744*mc 2024 + 4*mc 424*mc 744*mc 2024) + 2 * KeccakfPermAir.extraction.inter_2567 c row := by
    simp only [KeccakfPermAir.extraction.inter_2569, KeccakfPermAir.extraction.inter_2568, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_2567 c row = (mc 425 + mc 745 + mc 2025 - 2*mc 425*mc 745 - 2*mc 425*mc 2025 - 2*mc 745*mc 2025 + 4*mc 425*mc 745*mc 2025) + 2 * KeccakfPermAir.extraction.inter_2565 c row := by
    simp only [KeccakfPermAir.extraction.inter_2567, KeccakfPermAir.extraction.inter_2566, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_2565 c row = (mc 426 + mc 746 + mc 2026 - 2*mc 426*mc 746 - 2*mc 426*mc 2026 - 2*mc 746*mc 2026 + 4*mc 426*mc 746*mc 2026) + 2 * KeccakfPermAir.extraction.inter_2563 c row := by
    simp only [KeccakfPermAir.extraction.inter_2565, KeccakfPermAir.extraction.inter_2564, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_2563 c row = (mc 427 + mc 747 + mc 2027 - 2*mc 427*mc 747 - 2*mc 427*mc 2027 - 2*mc 747*mc 2027 + 4*mc 427*mc 747*mc 2027) + 2 * KeccakfPermAir.extraction.inter_2561 c row := by
    simp only [KeccakfPermAir.extraction.inter_2563, KeccakfPermAir.extraction.inter_2562, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_2561 c row = (mc 428 + mc 748 + mc 2028 - 2*mc 428*mc 748 - 2*mc 428*mc 2028 - 2*mc 748*mc 2028 + 4*mc 428*mc 748*mc 2028) + 2 * KeccakfPermAir.extraction.inter_2559 c row := by
    simp only [KeccakfPermAir.extraction.inter_2561, KeccakfPermAir.extraction.inter_2560, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_2559 c row = (mc 429 + mc 749 + mc 2029 - 2*mc 429*mc 749 - 2*mc 429*mc 2029 - 2*mc 749*mc 2029 + 4*mc 429*mc 749*mc 2029) + 2 * KeccakfPermAir.extraction.inter_2557 c row := by
    simp only [KeccakfPermAir.extraction.inter_2559, KeccakfPermAir.extraction.inter_2558, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_2557 c row = (mc 430 + mc 750 + mc 2030 - 2*mc 430*mc 750 - 2*mc 430*mc 2030 - 2*mc 750*mc 2030 + 4*mc 430*mc 750*mc 2030) + 2 * KeccakfPermAir.extraction.inter_2555 c row := by
    simp only [KeccakfPermAir.extraction.inter_2557, KeccakfPermAir.extraction.inter_2556, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_2555 c row = (mc 431 + mc 751 + mc 2031 - 2*mc 431*mc 751 - 2*mc 431*mc 2031 - 2*mc 751*mc 2031 + 4*mc 431*mc 751*mc 2031) + 2 * KeccakfPermAir.extraction.inter_2553 c row := by
    simp only [KeccakfPermAir.extraction.inter_2555, KeccakfPermAir.extraction.inter_2554, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_2553 c row = (mc 432 + mc 752 + mc 2032 - 2*mc 432*mc 752 - 2*mc 432*mc 2032 - 2*mc 752*mc 2032 + 4*mc 432*mc 752*mc 2032) := by
    simp only [KeccakfPermAir.extraction.inter_2553, KeccakfPermAir.extraction.inter_2552, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_2179 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 433 753 2033 198 row) :
    mc 198 = (mc 433 + mc 753 + mc 2033 - 2*mc 433*mc 753 - 2*mc 433*mc 2033 - 2*mc 753*mc 2033 + 4*mc 433*mc 753*mc 2033) + 2*(mc 434 + mc 754 + mc 2034 - 2*mc 434*mc 754 - 2*mc 434*mc 2034 - 2*mc 754*mc 2034 + 4*mc 434*mc 754*mc 2034) + 4*(mc 435 + mc 755 + mc 2035 - 2*mc 435*mc 755 - 2*mc 435*mc 2035 - 2*mc 755*mc 2035 + 4*mc 435*mc 755*mc 2035) + 8*(mc 436 + mc 756 + mc 2036 - 2*mc 436*mc 756 - 2*mc 436*mc 2036 - 2*mc 756*mc 2036 + 4*mc 436*mc 756*mc 2036) + 16*(mc 437 + mc 757 + mc 2037 - 2*mc 437*mc 757 - 2*mc 437*mc 2037 - 2*mc 757*mc 2037 + 4*mc 437*mc 757*mc 2037) + 32*(mc 438 + mc 758 + mc 2038 - 2*mc 438*mc 758 - 2*mc 438*mc 2038 - 2*mc 758*mc 2038 + 4*mc 438*mc 758*mc 2038) + 64*(mc 439 + mc 759 + mc 2039 - 2*mc 439*mc 759 - 2*mc 439*mc 2039 - 2*mc 759*mc 2039 + 4*mc 439*mc 759*mc 2039) + 128*(mc 440 + mc 760 + mc 2040 - 2*mc 440*mc 760 - 2*mc 440*mc 2040 - 2*mc 760*mc 2040 + 4*mc 440*mc 760*mc 2040) + 256*(mc 441 + mc 761 + mc 2041 - 2*mc 441*mc 761 - 2*mc 441*mc 2041 - 2*mc 761*mc 2041 + 4*mc 441*mc 761*mc 2041) + 512*(mc 442 + mc 762 + mc 2042 - 2*mc 442*mc 762 - 2*mc 442*mc 2042 - 2*mc 762*mc 2042 + 4*mc 442*mc 762*mc 2042) + 1024*(mc 443 + mc 763 + mc 2043 - 2*mc 443*mc 763 - 2*mc 443*mc 2043 - 2*mc 763*mc 2043 + 4*mc 443*mc 763*mc 2043) + 2048*(mc 444 + mc 764 + mc 2044 - 2*mc 444*mc 764 - 2*mc 444*mc 2044 - 2*mc 764*mc 2044 + 4*mc 444*mc 764*mc 2044) + 4096*(mc 445 + mc 765 + mc 2045 - 2*mc 445*mc 765 - 2*mc 445*mc 2045 - 2*mc 765*mc 2045 + 4*mc 445*mc 765*mc 2045) + 8192*(mc 446 + mc 766 + mc 2046 - 2*mc 446*mc 766 - 2*mc 446*mc 2046 - 2*mc 766*mc 2046 + 4*mc 446*mc 766*mc 2046) + 16384*(mc 447 + mc 767 + mc 2047 - 2*mc 447*mc 767 - 2*mc 447*mc 2047 - 2*mc 767*mc 2047 + 4*mc 447*mc 767*mc 2047) + 32768*(mc 448 + mc 768 + mc 2048 - 2*mc 448*mc 768 - 2*mc 448*mc 2048 - 2*mc 768*mc 2048 + 4*mc 448*mc 768*mc 2048) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_2179, KeccakfPermAir.extraction.inter_2613, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_2612 c row = (mc 434 + mc 754 + mc 2034 - 2*mc 434*mc 754 - 2*mc 434*mc 2034 - 2*mc 754*mc 2034 + 4*mc 434*mc 754*mc 2034) + 2 * KeccakfPermAir.extraction.inter_2610 c row := by
    simp only [KeccakfPermAir.extraction.inter_2612, KeccakfPermAir.extraction.inter_2611, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_2610 c row = (mc 435 + mc 755 + mc 2035 - 2*mc 435*mc 755 - 2*mc 435*mc 2035 - 2*mc 755*mc 2035 + 4*mc 435*mc 755*mc 2035) + 2 * KeccakfPermAir.extraction.inter_2608 c row := by
    simp only [KeccakfPermAir.extraction.inter_2610, KeccakfPermAir.extraction.inter_2609, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_2608 c row = (mc 436 + mc 756 + mc 2036 - 2*mc 436*mc 756 - 2*mc 436*mc 2036 - 2*mc 756*mc 2036 + 4*mc 436*mc 756*mc 2036) + 2 * KeccakfPermAir.extraction.inter_2606 c row := by
    simp only [KeccakfPermAir.extraction.inter_2608, KeccakfPermAir.extraction.inter_2607, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_2606 c row = (mc 437 + mc 757 + mc 2037 - 2*mc 437*mc 757 - 2*mc 437*mc 2037 - 2*mc 757*mc 2037 + 4*mc 437*mc 757*mc 2037) + 2 * KeccakfPermAir.extraction.inter_2604 c row := by
    simp only [KeccakfPermAir.extraction.inter_2606, KeccakfPermAir.extraction.inter_2605, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_2604 c row = (mc 438 + mc 758 + mc 2038 - 2*mc 438*mc 758 - 2*mc 438*mc 2038 - 2*mc 758*mc 2038 + 4*mc 438*mc 758*mc 2038) + 2 * KeccakfPermAir.extraction.inter_2602 c row := by
    simp only [KeccakfPermAir.extraction.inter_2604, KeccakfPermAir.extraction.inter_2603, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_2602 c row = (mc 439 + mc 759 + mc 2039 - 2*mc 439*mc 759 - 2*mc 439*mc 2039 - 2*mc 759*mc 2039 + 4*mc 439*mc 759*mc 2039) + 2 * KeccakfPermAir.extraction.inter_2600 c row := by
    simp only [KeccakfPermAir.extraction.inter_2602, KeccakfPermAir.extraction.inter_2601, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_2600 c row = (mc 440 + mc 760 + mc 2040 - 2*mc 440*mc 760 - 2*mc 440*mc 2040 - 2*mc 760*mc 2040 + 4*mc 440*mc 760*mc 2040) + 2 * KeccakfPermAir.extraction.inter_2598 c row := by
    simp only [KeccakfPermAir.extraction.inter_2600, KeccakfPermAir.extraction.inter_2599, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_2598 c row = (mc 441 + mc 761 + mc 2041 - 2*mc 441*mc 761 - 2*mc 441*mc 2041 - 2*mc 761*mc 2041 + 4*mc 441*mc 761*mc 2041) + 2 * KeccakfPermAir.extraction.inter_2596 c row := by
    simp only [KeccakfPermAir.extraction.inter_2598, KeccakfPermAir.extraction.inter_2597, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_2596 c row = (mc 442 + mc 762 + mc 2042 - 2*mc 442*mc 762 - 2*mc 442*mc 2042 - 2*mc 762*mc 2042 + 4*mc 442*mc 762*mc 2042) + 2 * KeccakfPermAir.extraction.inter_2594 c row := by
    simp only [KeccakfPermAir.extraction.inter_2596, KeccakfPermAir.extraction.inter_2595, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_2594 c row = (mc 443 + mc 763 + mc 2043 - 2*mc 443*mc 763 - 2*mc 443*mc 2043 - 2*mc 763*mc 2043 + 4*mc 443*mc 763*mc 2043) + 2 * KeccakfPermAir.extraction.inter_2592 c row := by
    simp only [KeccakfPermAir.extraction.inter_2594, KeccakfPermAir.extraction.inter_2593, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_2592 c row = (mc 444 + mc 764 + mc 2044 - 2*mc 444*mc 764 - 2*mc 444*mc 2044 - 2*mc 764*mc 2044 + 4*mc 444*mc 764*mc 2044) + 2 * KeccakfPermAir.extraction.inter_2590 c row := by
    simp only [KeccakfPermAir.extraction.inter_2592, KeccakfPermAir.extraction.inter_2591, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_2590 c row = (mc 445 + mc 765 + mc 2045 - 2*mc 445*mc 765 - 2*mc 445*mc 2045 - 2*mc 765*mc 2045 + 4*mc 445*mc 765*mc 2045) + 2 * KeccakfPermAir.extraction.inter_2588 c row := by
    simp only [KeccakfPermAir.extraction.inter_2590, KeccakfPermAir.extraction.inter_2589, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_2588 c row = (mc 446 + mc 766 + mc 2046 - 2*mc 446*mc 766 - 2*mc 446*mc 2046 - 2*mc 766*mc 2046 + 4*mc 446*mc 766*mc 2046) + 2 * KeccakfPermAir.extraction.inter_2586 c row := by
    simp only [KeccakfPermAir.extraction.inter_2588, KeccakfPermAir.extraction.inter_2587, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_2586 c row = (mc 447 + mc 767 + mc 2047 - 2*mc 447*mc 767 - 2*mc 447*mc 2047 - 2*mc 767*mc 2047 + 4*mc 447*mc 767*mc 2047) + 2 * KeccakfPermAir.extraction.inter_2584 c row := by
    simp only [KeccakfPermAir.extraction.inter_2586, KeccakfPermAir.extraction.inter_2585, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_2584 c row = (mc 448 + mc 768 + mc 2048 - 2*mc 448*mc 768 - 2*mc 448*mc 2048 - 2*mc 768*mc 2048 + 4*mc 448*mc 768*mc 2048) := by
    simp only [KeccakfPermAir.extraction.inter_2584, KeccakfPermAir.extraction.inter_2583, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_2180 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 449 769 2049 199 row) :
    mc 199 = (mc 449 + mc 769 + mc 2049 - 2*mc 449*mc 769 - 2*mc 449*mc 2049 - 2*mc 769*mc 2049 + 4*mc 449*mc 769*mc 2049) + 2*(mc 450 + mc 770 + mc 2050 - 2*mc 450*mc 770 - 2*mc 450*mc 2050 - 2*mc 770*mc 2050 + 4*mc 450*mc 770*mc 2050) + 4*(mc 451 + mc 771 + mc 2051 - 2*mc 451*mc 771 - 2*mc 451*mc 2051 - 2*mc 771*mc 2051 + 4*mc 451*mc 771*mc 2051) + 8*(mc 452 + mc 772 + mc 2052 - 2*mc 452*mc 772 - 2*mc 452*mc 2052 - 2*mc 772*mc 2052 + 4*mc 452*mc 772*mc 2052) + 16*(mc 453 + mc 773 + mc 2053 - 2*mc 453*mc 773 - 2*mc 453*mc 2053 - 2*mc 773*mc 2053 + 4*mc 453*mc 773*mc 2053) + 32*(mc 454 + mc 774 + mc 2054 - 2*mc 454*mc 774 - 2*mc 454*mc 2054 - 2*mc 774*mc 2054 + 4*mc 454*mc 774*mc 2054) + 64*(mc 455 + mc 775 + mc 2055 - 2*mc 455*mc 775 - 2*mc 455*mc 2055 - 2*mc 775*mc 2055 + 4*mc 455*mc 775*mc 2055) + 128*(mc 456 + mc 776 + mc 2056 - 2*mc 456*mc 776 - 2*mc 456*mc 2056 - 2*mc 776*mc 2056 + 4*mc 456*mc 776*mc 2056) + 256*(mc 457 + mc 777 + mc 2057 - 2*mc 457*mc 777 - 2*mc 457*mc 2057 - 2*mc 777*mc 2057 + 4*mc 457*mc 777*mc 2057) + 512*(mc 458 + mc 778 + mc 2058 - 2*mc 458*mc 778 - 2*mc 458*mc 2058 - 2*mc 778*mc 2058 + 4*mc 458*mc 778*mc 2058) + 1024*(mc 459 + mc 779 + mc 2059 - 2*mc 459*mc 779 - 2*mc 459*mc 2059 - 2*mc 779*mc 2059 + 4*mc 459*mc 779*mc 2059) + 2048*(mc 460 + mc 780 + mc 2060 - 2*mc 460*mc 780 - 2*mc 460*mc 2060 - 2*mc 780*mc 2060 + 4*mc 460*mc 780*mc 2060) + 4096*(mc 461 + mc 781 + mc 2061 - 2*mc 461*mc 781 - 2*mc 461*mc 2061 - 2*mc 781*mc 2061 + 4*mc 461*mc 781*mc 2061) + 8192*(mc 462 + mc 782 + mc 2062 - 2*mc 462*mc 782 - 2*mc 462*mc 2062 - 2*mc 782*mc 2062 + 4*mc 462*mc 782*mc 2062) + 16384*(mc 463 + mc 783 + mc 2063 - 2*mc 463*mc 783 - 2*mc 463*mc 2063 - 2*mc 783*mc 2063 + 4*mc 463*mc 783*mc 2063) + 32768*(mc 464 + mc 784 + mc 2064 - 2*mc 464*mc 784 - 2*mc 464*mc 2064 - 2*mc 784*mc 2064 + 4*mc 464*mc 784*mc 2064) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_2180, KeccakfPermAir.extraction.inter_2644, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_2643 c row = (mc 450 + mc 770 + mc 2050 - 2*mc 450*mc 770 - 2*mc 450*mc 2050 - 2*mc 770*mc 2050 + 4*mc 450*mc 770*mc 2050) + 2 * KeccakfPermAir.extraction.inter_2641 c row := by
    simp only [KeccakfPermAir.extraction.inter_2643, KeccakfPermAir.extraction.inter_2642, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_2641 c row = (mc 451 + mc 771 + mc 2051 - 2*mc 451*mc 771 - 2*mc 451*mc 2051 - 2*mc 771*mc 2051 + 4*mc 451*mc 771*mc 2051) + 2 * KeccakfPermAir.extraction.inter_2639 c row := by
    simp only [KeccakfPermAir.extraction.inter_2641, KeccakfPermAir.extraction.inter_2640, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_2639 c row = (mc 452 + mc 772 + mc 2052 - 2*mc 452*mc 772 - 2*mc 452*mc 2052 - 2*mc 772*mc 2052 + 4*mc 452*mc 772*mc 2052) + 2 * KeccakfPermAir.extraction.inter_2637 c row := by
    simp only [KeccakfPermAir.extraction.inter_2639, KeccakfPermAir.extraction.inter_2638, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_2637 c row = (mc 453 + mc 773 + mc 2053 - 2*mc 453*mc 773 - 2*mc 453*mc 2053 - 2*mc 773*mc 2053 + 4*mc 453*mc 773*mc 2053) + 2 * KeccakfPermAir.extraction.inter_2635 c row := by
    simp only [KeccakfPermAir.extraction.inter_2637, KeccakfPermAir.extraction.inter_2636, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_2635 c row = (mc 454 + mc 774 + mc 2054 - 2*mc 454*mc 774 - 2*mc 454*mc 2054 - 2*mc 774*mc 2054 + 4*mc 454*mc 774*mc 2054) + 2 * KeccakfPermAir.extraction.inter_2633 c row := by
    simp only [KeccakfPermAir.extraction.inter_2635, KeccakfPermAir.extraction.inter_2634, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_2633 c row = (mc 455 + mc 775 + mc 2055 - 2*mc 455*mc 775 - 2*mc 455*mc 2055 - 2*mc 775*mc 2055 + 4*mc 455*mc 775*mc 2055) + 2 * KeccakfPermAir.extraction.inter_2631 c row := by
    simp only [KeccakfPermAir.extraction.inter_2633, KeccakfPermAir.extraction.inter_2632, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_2631 c row = (mc 456 + mc 776 + mc 2056 - 2*mc 456*mc 776 - 2*mc 456*mc 2056 - 2*mc 776*mc 2056 + 4*mc 456*mc 776*mc 2056) + 2 * KeccakfPermAir.extraction.inter_2629 c row := by
    simp only [KeccakfPermAir.extraction.inter_2631, KeccakfPermAir.extraction.inter_2630, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_2629 c row = (mc 457 + mc 777 + mc 2057 - 2*mc 457*mc 777 - 2*mc 457*mc 2057 - 2*mc 777*mc 2057 + 4*mc 457*mc 777*mc 2057) + 2 * KeccakfPermAir.extraction.inter_2627 c row := by
    simp only [KeccakfPermAir.extraction.inter_2629, KeccakfPermAir.extraction.inter_2628, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_2627 c row = (mc 458 + mc 778 + mc 2058 - 2*mc 458*mc 778 - 2*mc 458*mc 2058 - 2*mc 778*mc 2058 + 4*mc 458*mc 778*mc 2058) + 2 * KeccakfPermAir.extraction.inter_2625 c row := by
    simp only [KeccakfPermAir.extraction.inter_2627, KeccakfPermAir.extraction.inter_2626, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_2625 c row = (mc 459 + mc 779 + mc 2059 - 2*mc 459*mc 779 - 2*mc 459*mc 2059 - 2*mc 779*mc 2059 + 4*mc 459*mc 779*mc 2059) + 2 * KeccakfPermAir.extraction.inter_2623 c row := by
    simp only [KeccakfPermAir.extraction.inter_2625, KeccakfPermAir.extraction.inter_2624, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_2623 c row = (mc 460 + mc 780 + mc 2060 - 2*mc 460*mc 780 - 2*mc 460*mc 2060 - 2*mc 780*mc 2060 + 4*mc 460*mc 780*mc 2060) + 2 * KeccakfPermAir.extraction.inter_2621 c row := by
    simp only [KeccakfPermAir.extraction.inter_2623, KeccakfPermAir.extraction.inter_2622, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_2621 c row = (mc 461 + mc 781 + mc 2061 - 2*mc 461*mc 781 - 2*mc 461*mc 2061 - 2*mc 781*mc 2061 + 4*mc 461*mc 781*mc 2061) + 2 * KeccakfPermAir.extraction.inter_2619 c row := by
    simp only [KeccakfPermAir.extraction.inter_2621, KeccakfPermAir.extraction.inter_2620, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_2619 c row = (mc 462 + mc 782 + mc 2062 - 2*mc 462*mc 782 - 2*mc 462*mc 2062 - 2*mc 782*mc 2062 + 4*mc 462*mc 782*mc 2062) + 2 * KeccakfPermAir.extraction.inter_2617 c row := by
    simp only [KeccakfPermAir.extraction.inter_2619, KeccakfPermAir.extraction.inter_2618, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_2617 c row = (mc 463 + mc 783 + mc 2063 - 2*mc 463*mc 783 - 2*mc 463*mc 2063 - 2*mc 783*mc 2063 + 4*mc 463*mc 783*mc 2063) + 2 * KeccakfPermAir.extraction.inter_2615 c row := by
    simp only [KeccakfPermAir.extraction.inter_2617, KeccakfPermAir.extraction.inter_2616, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_2615 c row = (mc 464 + mc 784 + mc 2064 - 2*mc 464*mc 784 - 2*mc 464*mc 2064 - 2*mc 784*mc 2064 + 4*mc 464*mc 784*mc 2064) := by
    simp only [KeccakfPermAir.extraction.inter_2615, KeccakfPermAir.extraction.inter_2614, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_2181 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 465 785 2065 200 row) :
    mc 200 = (mc 465 + mc 785 + mc 2065 - 2*mc 465*mc 785 - 2*mc 465*mc 2065 - 2*mc 785*mc 2065 + 4*mc 465*mc 785*mc 2065) + 2*(mc 466 + mc 786 + mc 2066 - 2*mc 466*mc 786 - 2*mc 466*mc 2066 - 2*mc 786*mc 2066 + 4*mc 466*mc 786*mc 2066) + 4*(mc 467 + mc 787 + mc 2067 - 2*mc 467*mc 787 - 2*mc 467*mc 2067 - 2*mc 787*mc 2067 + 4*mc 467*mc 787*mc 2067) + 8*(mc 468 + mc 788 + mc 2068 - 2*mc 468*mc 788 - 2*mc 468*mc 2068 - 2*mc 788*mc 2068 + 4*mc 468*mc 788*mc 2068) + 16*(mc 469 + mc 789 + mc 2069 - 2*mc 469*mc 789 - 2*mc 469*mc 2069 - 2*mc 789*mc 2069 + 4*mc 469*mc 789*mc 2069) + 32*(mc 470 + mc 790 + mc 2070 - 2*mc 470*mc 790 - 2*mc 470*mc 2070 - 2*mc 790*mc 2070 + 4*mc 470*mc 790*mc 2070) + 64*(mc 471 + mc 791 + mc 2071 - 2*mc 471*mc 791 - 2*mc 471*mc 2071 - 2*mc 791*mc 2071 + 4*mc 471*mc 791*mc 2071) + 128*(mc 472 + mc 792 + mc 2072 - 2*mc 472*mc 792 - 2*mc 472*mc 2072 - 2*mc 792*mc 2072 + 4*mc 472*mc 792*mc 2072) + 256*(mc 473 + mc 793 + mc 2073 - 2*mc 473*mc 793 - 2*mc 473*mc 2073 - 2*mc 793*mc 2073 + 4*mc 473*mc 793*mc 2073) + 512*(mc 474 + mc 794 + mc 2074 - 2*mc 474*mc 794 - 2*mc 474*mc 2074 - 2*mc 794*mc 2074 + 4*mc 474*mc 794*mc 2074) + 1024*(mc 475 + mc 795 + mc 2075 - 2*mc 475*mc 795 - 2*mc 475*mc 2075 - 2*mc 795*mc 2075 + 4*mc 475*mc 795*mc 2075) + 2048*(mc 476 + mc 796 + mc 2076 - 2*mc 476*mc 796 - 2*mc 476*mc 2076 - 2*mc 796*mc 2076 + 4*mc 476*mc 796*mc 2076) + 4096*(mc 477 + mc 797 + mc 2077 - 2*mc 477*mc 797 - 2*mc 477*mc 2077 - 2*mc 797*mc 2077 + 4*mc 477*mc 797*mc 2077) + 8192*(mc 478 + mc 798 + mc 2078 - 2*mc 478*mc 798 - 2*mc 478*mc 2078 - 2*mc 798*mc 2078 + 4*mc 478*mc 798*mc 2078) + 16384*(mc 479 + mc 799 + mc 2079 - 2*mc 479*mc 799 - 2*mc 479*mc 2079 - 2*mc 799*mc 2079 + 4*mc 479*mc 799*mc 2079) + 32768*(mc 480 + mc 800 + mc 2080 - 2*mc 480*mc 800 - 2*mc 480*mc 2080 - 2*mc 800*mc 2080 + 4*mc 480*mc 800*mc 2080) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_2181, KeccakfPermAir.extraction.inter_2675, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_2674 c row = (mc 466 + mc 786 + mc 2066 - 2*mc 466*mc 786 - 2*mc 466*mc 2066 - 2*mc 786*mc 2066 + 4*mc 466*mc 786*mc 2066) + 2 * KeccakfPermAir.extraction.inter_2672 c row := by
    simp only [KeccakfPermAir.extraction.inter_2674, KeccakfPermAir.extraction.inter_2673, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_2672 c row = (mc 467 + mc 787 + mc 2067 - 2*mc 467*mc 787 - 2*mc 467*mc 2067 - 2*mc 787*mc 2067 + 4*mc 467*mc 787*mc 2067) + 2 * KeccakfPermAir.extraction.inter_2670 c row := by
    simp only [KeccakfPermAir.extraction.inter_2672, KeccakfPermAir.extraction.inter_2671, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_2670 c row = (mc 468 + mc 788 + mc 2068 - 2*mc 468*mc 788 - 2*mc 468*mc 2068 - 2*mc 788*mc 2068 + 4*mc 468*mc 788*mc 2068) + 2 * KeccakfPermAir.extraction.inter_2668 c row := by
    simp only [KeccakfPermAir.extraction.inter_2670, KeccakfPermAir.extraction.inter_2669, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_2668 c row = (mc 469 + mc 789 + mc 2069 - 2*mc 469*mc 789 - 2*mc 469*mc 2069 - 2*mc 789*mc 2069 + 4*mc 469*mc 789*mc 2069) + 2 * KeccakfPermAir.extraction.inter_2666 c row := by
    simp only [KeccakfPermAir.extraction.inter_2668, KeccakfPermAir.extraction.inter_2667, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_2666 c row = (mc 470 + mc 790 + mc 2070 - 2*mc 470*mc 790 - 2*mc 470*mc 2070 - 2*mc 790*mc 2070 + 4*mc 470*mc 790*mc 2070) + 2 * KeccakfPermAir.extraction.inter_2664 c row := by
    simp only [KeccakfPermAir.extraction.inter_2666, KeccakfPermAir.extraction.inter_2665, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_2664 c row = (mc 471 + mc 791 + mc 2071 - 2*mc 471*mc 791 - 2*mc 471*mc 2071 - 2*mc 791*mc 2071 + 4*mc 471*mc 791*mc 2071) + 2 * KeccakfPermAir.extraction.inter_2662 c row := by
    simp only [KeccakfPermAir.extraction.inter_2664, KeccakfPermAir.extraction.inter_2663, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_2662 c row = (mc 472 + mc 792 + mc 2072 - 2*mc 472*mc 792 - 2*mc 472*mc 2072 - 2*mc 792*mc 2072 + 4*mc 472*mc 792*mc 2072) + 2 * KeccakfPermAir.extraction.inter_2660 c row := by
    simp only [KeccakfPermAir.extraction.inter_2662, KeccakfPermAir.extraction.inter_2661, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_2660 c row = (mc 473 + mc 793 + mc 2073 - 2*mc 473*mc 793 - 2*mc 473*mc 2073 - 2*mc 793*mc 2073 + 4*mc 473*mc 793*mc 2073) + 2 * KeccakfPermAir.extraction.inter_2658 c row := by
    simp only [KeccakfPermAir.extraction.inter_2660, KeccakfPermAir.extraction.inter_2659, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_2658 c row = (mc 474 + mc 794 + mc 2074 - 2*mc 474*mc 794 - 2*mc 474*mc 2074 - 2*mc 794*mc 2074 + 4*mc 474*mc 794*mc 2074) + 2 * KeccakfPermAir.extraction.inter_2656 c row := by
    simp only [KeccakfPermAir.extraction.inter_2658, KeccakfPermAir.extraction.inter_2657, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_2656 c row = (mc 475 + mc 795 + mc 2075 - 2*mc 475*mc 795 - 2*mc 475*mc 2075 - 2*mc 795*mc 2075 + 4*mc 475*mc 795*mc 2075) + 2 * KeccakfPermAir.extraction.inter_2654 c row := by
    simp only [KeccakfPermAir.extraction.inter_2656, KeccakfPermAir.extraction.inter_2655, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_2654 c row = (mc 476 + mc 796 + mc 2076 - 2*mc 476*mc 796 - 2*mc 476*mc 2076 - 2*mc 796*mc 2076 + 4*mc 476*mc 796*mc 2076) + 2 * KeccakfPermAir.extraction.inter_2652 c row := by
    simp only [KeccakfPermAir.extraction.inter_2654, KeccakfPermAir.extraction.inter_2653, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_2652 c row = (mc 477 + mc 797 + mc 2077 - 2*mc 477*mc 797 - 2*mc 477*mc 2077 - 2*mc 797*mc 2077 + 4*mc 477*mc 797*mc 2077) + 2 * KeccakfPermAir.extraction.inter_2650 c row := by
    simp only [KeccakfPermAir.extraction.inter_2652, KeccakfPermAir.extraction.inter_2651, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_2650 c row = (mc 478 + mc 798 + mc 2078 - 2*mc 478*mc 798 - 2*mc 478*mc 2078 - 2*mc 798*mc 2078 + 4*mc 478*mc 798*mc 2078) + 2 * KeccakfPermAir.extraction.inter_2648 c row := by
    simp only [KeccakfPermAir.extraction.inter_2650, KeccakfPermAir.extraction.inter_2649, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_2648 c row = (mc 479 + mc 799 + mc 2079 - 2*mc 479*mc 799 - 2*mc 479*mc 2079 - 2*mc 799*mc 2079 + 4*mc 479*mc 799*mc 2079) + 2 * KeccakfPermAir.extraction.inter_2646 c row := by
    simp only [KeccakfPermAir.extraction.inter_2648, KeccakfPermAir.extraction.inter_2647, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_2646 c row = (mc 480 + mc 800 + mc 2080 - 2*mc 480*mc 800 - 2*mc 480*mc 2080 - 2*mc 800*mc 2080 + 4*mc 480*mc 800*mc 2080) := by
    simp only [KeccakfPermAir.extraction.inter_2646, KeccakfPermAir.extraction.inter_2645, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_2246 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 481 801 2081 201 row) :
    mc 201 = (mc 481 + mc 801 + mc 2081 - 2*mc 481*mc 801 - 2*mc 481*mc 2081 - 2*mc 801*mc 2081 + 4*mc 481*mc 801*mc 2081) + 2*(mc 482 + mc 802 + mc 2082 - 2*mc 482*mc 802 - 2*mc 482*mc 2082 - 2*mc 802*mc 2082 + 4*mc 482*mc 802*mc 2082) + 4*(mc 483 + mc 803 + mc 2083 - 2*mc 483*mc 803 - 2*mc 483*mc 2083 - 2*mc 803*mc 2083 + 4*mc 483*mc 803*mc 2083) + 8*(mc 484 + mc 804 + mc 2084 - 2*mc 484*mc 804 - 2*mc 484*mc 2084 - 2*mc 804*mc 2084 + 4*mc 484*mc 804*mc 2084) + 16*(mc 485 + mc 805 + mc 2085 - 2*mc 485*mc 805 - 2*mc 485*mc 2085 - 2*mc 805*mc 2085 + 4*mc 485*mc 805*mc 2085) + 32*(mc 486 + mc 806 + mc 2086 - 2*mc 486*mc 806 - 2*mc 486*mc 2086 - 2*mc 806*mc 2086 + 4*mc 486*mc 806*mc 2086) + 64*(mc 487 + mc 807 + mc 2087 - 2*mc 487*mc 807 - 2*mc 487*mc 2087 - 2*mc 807*mc 2087 + 4*mc 487*mc 807*mc 2087) + 128*(mc 488 + mc 808 + mc 2088 - 2*mc 488*mc 808 - 2*mc 488*mc 2088 - 2*mc 808*mc 2088 + 4*mc 488*mc 808*mc 2088) + 256*(mc 489 + mc 809 + mc 2089 - 2*mc 489*mc 809 - 2*mc 489*mc 2089 - 2*mc 809*mc 2089 + 4*mc 489*mc 809*mc 2089) + 512*(mc 490 + mc 810 + mc 2090 - 2*mc 490*mc 810 - 2*mc 490*mc 2090 - 2*mc 810*mc 2090 + 4*mc 490*mc 810*mc 2090) + 1024*(mc 491 + mc 811 + mc 2091 - 2*mc 491*mc 811 - 2*mc 491*mc 2091 - 2*mc 811*mc 2091 + 4*mc 491*mc 811*mc 2091) + 2048*(mc 492 + mc 812 + mc 2092 - 2*mc 492*mc 812 - 2*mc 492*mc 2092 - 2*mc 812*mc 2092 + 4*mc 492*mc 812*mc 2092) + 4096*(mc 493 + mc 813 + mc 2093 - 2*mc 493*mc 813 - 2*mc 493*mc 2093 - 2*mc 813*mc 2093 + 4*mc 493*mc 813*mc 2093) + 8192*(mc 494 + mc 814 + mc 2094 - 2*mc 494*mc 814 - 2*mc 494*mc 2094 - 2*mc 814*mc 2094 + 4*mc 494*mc 814*mc 2094) + 16384*(mc 495 + mc 815 + mc 2095 - 2*mc 495*mc 815 - 2*mc 495*mc 2095 - 2*mc 815*mc 2095 + 4*mc 495*mc 815*mc 2095) + 32768*(mc 496 + mc 816 + mc 2096 - 2*mc 496*mc 816 - 2*mc 496*mc 2096 - 2*mc 816*mc 2096 + 4*mc 496*mc 816*mc 2096) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_2246, KeccakfPermAir.extraction.inter_2706, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_2705 c row = (mc 482 + mc 802 + mc 2082 - 2*mc 482*mc 802 - 2*mc 482*mc 2082 - 2*mc 802*mc 2082 + 4*mc 482*mc 802*mc 2082) + 2 * KeccakfPermAir.extraction.inter_2703 c row := by
    simp only [KeccakfPermAir.extraction.inter_2705, KeccakfPermAir.extraction.inter_2704, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_2703 c row = (mc 483 + mc 803 + mc 2083 - 2*mc 483*mc 803 - 2*mc 483*mc 2083 - 2*mc 803*mc 2083 + 4*mc 483*mc 803*mc 2083) + 2 * KeccakfPermAir.extraction.inter_2701 c row := by
    simp only [KeccakfPermAir.extraction.inter_2703, KeccakfPermAir.extraction.inter_2702, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_2701 c row = (mc 484 + mc 804 + mc 2084 - 2*mc 484*mc 804 - 2*mc 484*mc 2084 - 2*mc 804*mc 2084 + 4*mc 484*mc 804*mc 2084) + 2 * KeccakfPermAir.extraction.inter_2699 c row := by
    simp only [KeccakfPermAir.extraction.inter_2701, KeccakfPermAir.extraction.inter_2700, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_2699 c row = (mc 485 + mc 805 + mc 2085 - 2*mc 485*mc 805 - 2*mc 485*mc 2085 - 2*mc 805*mc 2085 + 4*mc 485*mc 805*mc 2085) + 2 * KeccakfPermAir.extraction.inter_2697 c row := by
    simp only [KeccakfPermAir.extraction.inter_2699, KeccakfPermAir.extraction.inter_2698, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_2697 c row = (mc 486 + mc 806 + mc 2086 - 2*mc 486*mc 806 - 2*mc 486*mc 2086 - 2*mc 806*mc 2086 + 4*mc 486*mc 806*mc 2086) + 2 * KeccakfPermAir.extraction.inter_2695 c row := by
    simp only [KeccakfPermAir.extraction.inter_2697, KeccakfPermAir.extraction.inter_2696, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_2695 c row = (mc 487 + mc 807 + mc 2087 - 2*mc 487*mc 807 - 2*mc 487*mc 2087 - 2*mc 807*mc 2087 + 4*mc 487*mc 807*mc 2087) + 2 * KeccakfPermAir.extraction.inter_2693 c row := by
    simp only [KeccakfPermAir.extraction.inter_2695, KeccakfPermAir.extraction.inter_2694, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_2693 c row = (mc 488 + mc 808 + mc 2088 - 2*mc 488*mc 808 - 2*mc 488*mc 2088 - 2*mc 808*mc 2088 + 4*mc 488*mc 808*mc 2088) + 2 * KeccakfPermAir.extraction.inter_2691 c row := by
    simp only [KeccakfPermAir.extraction.inter_2693, KeccakfPermAir.extraction.inter_2692, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_2691 c row = (mc 489 + mc 809 + mc 2089 - 2*mc 489*mc 809 - 2*mc 489*mc 2089 - 2*mc 809*mc 2089 + 4*mc 489*mc 809*mc 2089) + 2 * KeccakfPermAir.extraction.inter_2689 c row := by
    simp only [KeccakfPermAir.extraction.inter_2691, KeccakfPermAir.extraction.inter_2690, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_2689 c row = (mc 490 + mc 810 + mc 2090 - 2*mc 490*mc 810 - 2*mc 490*mc 2090 - 2*mc 810*mc 2090 + 4*mc 490*mc 810*mc 2090) + 2 * KeccakfPermAir.extraction.inter_2687 c row := by
    simp only [KeccakfPermAir.extraction.inter_2689, KeccakfPermAir.extraction.inter_2688, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_2687 c row = (mc 491 + mc 811 + mc 2091 - 2*mc 491*mc 811 - 2*mc 491*mc 2091 - 2*mc 811*mc 2091 + 4*mc 491*mc 811*mc 2091) + 2 * KeccakfPermAir.extraction.inter_2685 c row := by
    simp only [KeccakfPermAir.extraction.inter_2687, KeccakfPermAir.extraction.inter_2686, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_2685 c row = (mc 492 + mc 812 + mc 2092 - 2*mc 492*mc 812 - 2*mc 492*mc 2092 - 2*mc 812*mc 2092 + 4*mc 492*mc 812*mc 2092) + 2 * KeccakfPermAir.extraction.inter_2683 c row := by
    simp only [KeccakfPermAir.extraction.inter_2685, KeccakfPermAir.extraction.inter_2684, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_2683 c row = (mc 493 + mc 813 + mc 2093 - 2*mc 493*mc 813 - 2*mc 493*mc 2093 - 2*mc 813*mc 2093 + 4*mc 493*mc 813*mc 2093) + 2 * KeccakfPermAir.extraction.inter_2681 c row := by
    simp only [KeccakfPermAir.extraction.inter_2683, KeccakfPermAir.extraction.inter_2682, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_2681 c row = (mc 494 + mc 814 + mc 2094 - 2*mc 494*mc 814 - 2*mc 494*mc 2094 - 2*mc 814*mc 2094 + 4*mc 494*mc 814*mc 2094) + 2 * KeccakfPermAir.extraction.inter_2679 c row := by
    simp only [KeccakfPermAir.extraction.inter_2681, KeccakfPermAir.extraction.inter_2680, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_2679 c row = (mc 495 + mc 815 + mc 2095 - 2*mc 495*mc 815 - 2*mc 495*mc 2095 - 2*mc 815*mc 2095 + 4*mc 495*mc 815*mc 2095) + 2 * KeccakfPermAir.extraction.inter_2677 c row := by
    simp only [KeccakfPermAir.extraction.inter_2679, KeccakfPermAir.extraction.inter_2678, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_2677 c row = (mc 496 + mc 816 + mc 2096 - 2*mc 496*mc 816 - 2*mc 496*mc 2096 - 2*mc 816*mc 2096 + 4*mc 496*mc 816*mc 2096) := by
    simp only [KeccakfPermAir.extraction.inter_2677, KeccakfPermAir.extraction.inter_2676, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_2247 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 497 817 2097 202 row) :
    mc 202 = (mc 497 + mc 817 + mc 2097 - 2*mc 497*mc 817 - 2*mc 497*mc 2097 - 2*mc 817*mc 2097 + 4*mc 497*mc 817*mc 2097) + 2*(mc 498 + mc 818 + mc 2098 - 2*mc 498*mc 818 - 2*mc 498*mc 2098 - 2*mc 818*mc 2098 + 4*mc 498*mc 818*mc 2098) + 4*(mc 499 + mc 819 + mc 2099 - 2*mc 499*mc 819 - 2*mc 499*mc 2099 - 2*mc 819*mc 2099 + 4*mc 499*mc 819*mc 2099) + 8*(mc 500 + mc 820 + mc 2100 - 2*mc 500*mc 820 - 2*mc 500*mc 2100 - 2*mc 820*mc 2100 + 4*mc 500*mc 820*mc 2100) + 16*(mc 501 + mc 821 + mc 2101 - 2*mc 501*mc 821 - 2*mc 501*mc 2101 - 2*mc 821*mc 2101 + 4*mc 501*mc 821*mc 2101) + 32*(mc 502 + mc 822 + mc 2102 - 2*mc 502*mc 822 - 2*mc 502*mc 2102 - 2*mc 822*mc 2102 + 4*mc 502*mc 822*mc 2102) + 64*(mc 503 + mc 823 + mc 2103 - 2*mc 503*mc 823 - 2*mc 503*mc 2103 - 2*mc 823*mc 2103 + 4*mc 503*mc 823*mc 2103) + 128*(mc 504 + mc 824 + mc 2104 - 2*mc 504*mc 824 - 2*mc 504*mc 2104 - 2*mc 824*mc 2104 + 4*mc 504*mc 824*mc 2104) + 256*(mc 505 + mc 825 + mc 2105 - 2*mc 505*mc 825 - 2*mc 505*mc 2105 - 2*mc 825*mc 2105 + 4*mc 505*mc 825*mc 2105) + 512*(mc 506 + mc 826 + mc 2106 - 2*mc 506*mc 826 - 2*mc 506*mc 2106 - 2*mc 826*mc 2106 + 4*mc 506*mc 826*mc 2106) + 1024*(mc 507 + mc 827 + mc 2107 - 2*mc 507*mc 827 - 2*mc 507*mc 2107 - 2*mc 827*mc 2107 + 4*mc 507*mc 827*mc 2107) + 2048*(mc 508 + mc 828 + mc 2108 - 2*mc 508*mc 828 - 2*mc 508*mc 2108 - 2*mc 828*mc 2108 + 4*mc 508*mc 828*mc 2108) + 4096*(mc 509 + mc 829 + mc 2109 - 2*mc 509*mc 829 - 2*mc 509*mc 2109 - 2*mc 829*mc 2109 + 4*mc 509*mc 829*mc 2109) + 8192*(mc 510 + mc 830 + mc 2110 - 2*mc 510*mc 830 - 2*mc 510*mc 2110 - 2*mc 830*mc 2110 + 4*mc 510*mc 830*mc 2110) + 16384*(mc 511 + mc 831 + mc 2111 - 2*mc 511*mc 831 - 2*mc 511*mc 2111 - 2*mc 831*mc 2111 + 4*mc 511*mc 831*mc 2111) + 32768*(mc 512 + mc 832 + mc 2112 - 2*mc 512*mc 832 - 2*mc 512*mc 2112 - 2*mc 832*mc 2112 + 4*mc 512*mc 832*mc 2112) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_2247, KeccakfPermAir.extraction.inter_2737, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_2736 c row = (mc 498 + mc 818 + mc 2098 - 2*mc 498*mc 818 - 2*mc 498*mc 2098 - 2*mc 818*mc 2098 + 4*mc 498*mc 818*mc 2098) + 2 * KeccakfPermAir.extraction.inter_2734 c row := by
    simp only [KeccakfPermAir.extraction.inter_2736, KeccakfPermAir.extraction.inter_2735, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_2734 c row = (mc 499 + mc 819 + mc 2099 - 2*mc 499*mc 819 - 2*mc 499*mc 2099 - 2*mc 819*mc 2099 + 4*mc 499*mc 819*mc 2099) + 2 * KeccakfPermAir.extraction.inter_2732 c row := by
    simp only [KeccakfPermAir.extraction.inter_2734, KeccakfPermAir.extraction.inter_2733, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_2732 c row = (mc 500 + mc 820 + mc 2100 - 2*mc 500*mc 820 - 2*mc 500*mc 2100 - 2*mc 820*mc 2100 + 4*mc 500*mc 820*mc 2100) + 2 * KeccakfPermAir.extraction.inter_2730 c row := by
    simp only [KeccakfPermAir.extraction.inter_2732, KeccakfPermAir.extraction.inter_2731, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_2730 c row = (mc 501 + mc 821 + mc 2101 - 2*mc 501*mc 821 - 2*mc 501*mc 2101 - 2*mc 821*mc 2101 + 4*mc 501*mc 821*mc 2101) + 2 * KeccakfPermAir.extraction.inter_2728 c row := by
    simp only [KeccakfPermAir.extraction.inter_2730, KeccakfPermAir.extraction.inter_2729, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_2728 c row = (mc 502 + mc 822 + mc 2102 - 2*mc 502*mc 822 - 2*mc 502*mc 2102 - 2*mc 822*mc 2102 + 4*mc 502*mc 822*mc 2102) + 2 * KeccakfPermAir.extraction.inter_2726 c row := by
    simp only [KeccakfPermAir.extraction.inter_2728, KeccakfPermAir.extraction.inter_2727, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_2726 c row = (mc 503 + mc 823 + mc 2103 - 2*mc 503*mc 823 - 2*mc 503*mc 2103 - 2*mc 823*mc 2103 + 4*mc 503*mc 823*mc 2103) + 2 * KeccakfPermAir.extraction.inter_2724 c row := by
    simp only [KeccakfPermAir.extraction.inter_2726, KeccakfPermAir.extraction.inter_2725, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_2724 c row = (mc 504 + mc 824 + mc 2104 - 2*mc 504*mc 824 - 2*mc 504*mc 2104 - 2*mc 824*mc 2104 + 4*mc 504*mc 824*mc 2104) + 2 * KeccakfPermAir.extraction.inter_2722 c row := by
    simp only [KeccakfPermAir.extraction.inter_2724, KeccakfPermAir.extraction.inter_2723, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_2722 c row = (mc 505 + mc 825 + mc 2105 - 2*mc 505*mc 825 - 2*mc 505*mc 2105 - 2*mc 825*mc 2105 + 4*mc 505*mc 825*mc 2105) + 2 * KeccakfPermAir.extraction.inter_2720 c row := by
    simp only [KeccakfPermAir.extraction.inter_2722, KeccakfPermAir.extraction.inter_2721, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_2720 c row = (mc 506 + mc 826 + mc 2106 - 2*mc 506*mc 826 - 2*mc 506*mc 2106 - 2*mc 826*mc 2106 + 4*mc 506*mc 826*mc 2106) + 2 * KeccakfPermAir.extraction.inter_2718 c row := by
    simp only [KeccakfPermAir.extraction.inter_2720, KeccakfPermAir.extraction.inter_2719, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_2718 c row = (mc 507 + mc 827 + mc 2107 - 2*mc 507*mc 827 - 2*mc 507*mc 2107 - 2*mc 827*mc 2107 + 4*mc 507*mc 827*mc 2107) + 2 * KeccakfPermAir.extraction.inter_2716 c row := by
    simp only [KeccakfPermAir.extraction.inter_2718, KeccakfPermAir.extraction.inter_2717, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_2716 c row = (mc 508 + mc 828 + mc 2108 - 2*mc 508*mc 828 - 2*mc 508*mc 2108 - 2*mc 828*mc 2108 + 4*mc 508*mc 828*mc 2108) + 2 * KeccakfPermAir.extraction.inter_2714 c row := by
    simp only [KeccakfPermAir.extraction.inter_2716, KeccakfPermAir.extraction.inter_2715, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_2714 c row = (mc 509 + mc 829 + mc 2109 - 2*mc 509*mc 829 - 2*mc 509*mc 2109 - 2*mc 829*mc 2109 + 4*mc 509*mc 829*mc 2109) + 2 * KeccakfPermAir.extraction.inter_2712 c row := by
    simp only [KeccakfPermAir.extraction.inter_2714, KeccakfPermAir.extraction.inter_2713, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_2712 c row = (mc 510 + mc 830 + mc 2110 - 2*mc 510*mc 830 - 2*mc 510*mc 2110 - 2*mc 830*mc 2110 + 4*mc 510*mc 830*mc 2110) + 2 * KeccakfPermAir.extraction.inter_2710 c row := by
    simp only [KeccakfPermAir.extraction.inter_2712, KeccakfPermAir.extraction.inter_2711, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_2710 c row = (mc 511 + mc 831 + mc 2111 - 2*mc 511*mc 831 - 2*mc 511*mc 2111 - 2*mc 831*mc 2111 + 4*mc 511*mc 831*mc 2111) + 2 * KeccakfPermAir.extraction.inter_2708 c row := by
    simp only [KeccakfPermAir.extraction.inter_2710, KeccakfPermAir.extraction.inter_2709, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_2708 c row = (mc 512 + mc 832 + mc 2112 - 2*mc 512*mc 832 - 2*mc 512*mc 2112 - 2*mc 832*mc 2112 + 4*mc 512*mc 832*mc 2112) := by
    simp only [KeccakfPermAir.extraction.inter_2708, KeccakfPermAir.extraction.inter_2707, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_2248 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 513 833 2113 203 row) :
    mc 203 = (mc 513 + mc 833 + mc 2113 - 2*mc 513*mc 833 - 2*mc 513*mc 2113 - 2*mc 833*mc 2113 + 4*mc 513*mc 833*mc 2113) + 2*(mc 514 + mc 834 + mc 2114 - 2*mc 514*mc 834 - 2*mc 514*mc 2114 - 2*mc 834*mc 2114 + 4*mc 514*mc 834*mc 2114) + 4*(mc 515 + mc 835 + mc 2115 - 2*mc 515*mc 835 - 2*mc 515*mc 2115 - 2*mc 835*mc 2115 + 4*mc 515*mc 835*mc 2115) + 8*(mc 516 + mc 836 + mc 2116 - 2*mc 516*mc 836 - 2*mc 516*mc 2116 - 2*mc 836*mc 2116 + 4*mc 516*mc 836*mc 2116) + 16*(mc 517 + mc 837 + mc 2117 - 2*mc 517*mc 837 - 2*mc 517*mc 2117 - 2*mc 837*mc 2117 + 4*mc 517*mc 837*mc 2117) + 32*(mc 518 + mc 838 + mc 2118 - 2*mc 518*mc 838 - 2*mc 518*mc 2118 - 2*mc 838*mc 2118 + 4*mc 518*mc 838*mc 2118) + 64*(mc 519 + mc 839 + mc 2119 - 2*mc 519*mc 839 - 2*mc 519*mc 2119 - 2*mc 839*mc 2119 + 4*mc 519*mc 839*mc 2119) + 128*(mc 520 + mc 840 + mc 2120 - 2*mc 520*mc 840 - 2*mc 520*mc 2120 - 2*mc 840*mc 2120 + 4*mc 520*mc 840*mc 2120) + 256*(mc 521 + mc 841 + mc 2121 - 2*mc 521*mc 841 - 2*mc 521*mc 2121 - 2*mc 841*mc 2121 + 4*mc 521*mc 841*mc 2121) + 512*(mc 522 + mc 842 + mc 2122 - 2*mc 522*mc 842 - 2*mc 522*mc 2122 - 2*mc 842*mc 2122 + 4*mc 522*mc 842*mc 2122) + 1024*(mc 523 + mc 843 + mc 2123 - 2*mc 523*mc 843 - 2*mc 523*mc 2123 - 2*mc 843*mc 2123 + 4*mc 523*mc 843*mc 2123) + 2048*(mc 524 + mc 844 + mc 2124 - 2*mc 524*mc 844 - 2*mc 524*mc 2124 - 2*mc 844*mc 2124 + 4*mc 524*mc 844*mc 2124) + 4096*(mc 525 + mc 845 + mc 2125 - 2*mc 525*mc 845 - 2*mc 525*mc 2125 - 2*mc 845*mc 2125 + 4*mc 525*mc 845*mc 2125) + 8192*(mc 526 + mc 846 + mc 2126 - 2*mc 526*mc 846 - 2*mc 526*mc 2126 - 2*mc 846*mc 2126 + 4*mc 526*mc 846*mc 2126) + 16384*(mc 527 + mc 847 + mc 2127 - 2*mc 527*mc 847 - 2*mc 527*mc 2127 - 2*mc 847*mc 2127 + 4*mc 527*mc 847*mc 2127) + 32768*(mc 528 + mc 848 + mc 2128 - 2*mc 528*mc 848 - 2*mc 528*mc 2128 - 2*mc 848*mc 2128 + 4*mc 528*mc 848*mc 2128) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_2248, KeccakfPermAir.extraction.inter_2768, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_2767 c row = (mc 514 + mc 834 + mc 2114 - 2*mc 514*mc 834 - 2*mc 514*mc 2114 - 2*mc 834*mc 2114 + 4*mc 514*mc 834*mc 2114) + 2 * KeccakfPermAir.extraction.inter_2765 c row := by
    simp only [KeccakfPermAir.extraction.inter_2767, KeccakfPermAir.extraction.inter_2766, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_2765 c row = (mc 515 + mc 835 + mc 2115 - 2*mc 515*mc 835 - 2*mc 515*mc 2115 - 2*mc 835*mc 2115 + 4*mc 515*mc 835*mc 2115) + 2 * KeccakfPermAir.extraction.inter_2763 c row := by
    simp only [KeccakfPermAir.extraction.inter_2765, KeccakfPermAir.extraction.inter_2764, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_2763 c row = (mc 516 + mc 836 + mc 2116 - 2*mc 516*mc 836 - 2*mc 516*mc 2116 - 2*mc 836*mc 2116 + 4*mc 516*mc 836*mc 2116) + 2 * KeccakfPermAir.extraction.inter_2761 c row := by
    simp only [KeccakfPermAir.extraction.inter_2763, KeccakfPermAir.extraction.inter_2762, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_2761 c row = (mc 517 + mc 837 + mc 2117 - 2*mc 517*mc 837 - 2*mc 517*mc 2117 - 2*mc 837*mc 2117 + 4*mc 517*mc 837*mc 2117) + 2 * KeccakfPermAir.extraction.inter_2759 c row := by
    simp only [KeccakfPermAir.extraction.inter_2761, KeccakfPermAir.extraction.inter_2760, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_2759 c row = (mc 518 + mc 838 + mc 2118 - 2*mc 518*mc 838 - 2*mc 518*mc 2118 - 2*mc 838*mc 2118 + 4*mc 518*mc 838*mc 2118) + 2 * KeccakfPermAir.extraction.inter_2757 c row := by
    simp only [KeccakfPermAir.extraction.inter_2759, KeccakfPermAir.extraction.inter_2758, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_2757 c row = (mc 519 + mc 839 + mc 2119 - 2*mc 519*mc 839 - 2*mc 519*mc 2119 - 2*mc 839*mc 2119 + 4*mc 519*mc 839*mc 2119) + 2 * KeccakfPermAir.extraction.inter_2755 c row := by
    simp only [KeccakfPermAir.extraction.inter_2757, KeccakfPermAir.extraction.inter_2756, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_2755 c row = (mc 520 + mc 840 + mc 2120 - 2*mc 520*mc 840 - 2*mc 520*mc 2120 - 2*mc 840*mc 2120 + 4*mc 520*mc 840*mc 2120) + 2 * KeccakfPermAir.extraction.inter_2753 c row := by
    simp only [KeccakfPermAir.extraction.inter_2755, KeccakfPermAir.extraction.inter_2754, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_2753 c row = (mc 521 + mc 841 + mc 2121 - 2*mc 521*mc 841 - 2*mc 521*mc 2121 - 2*mc 841*mc 2121 + 4*mc 521*mc 841*mc 2121) + 2 * KeccakfPermAir.extraction.inter_2751 c row := by
    simp only [KeccakfPermAir.extraction.inter_2753, KeccakfPermAir.extraction.inter_2752, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_2751 c row = (mc 522 + mc 842 + mc 2122 - 2*mc 522*mc 842 - 2*mc 522*mc 2122 - 2*mc 842*mc 2122 + 4*mc 522*mc 842*mc 2122) + 2 * KeccakfPermAir.extraction.inter_2749 c row := by
    simp only [KeccakfPermAir.extraction.inter_2751, KeccakfPermAir.extraction.inter_2750, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_2749 c row = (mc 523 + mc 843 + mc 2123 - 2*mc 523*mc 843 - 2*mc 523*mc 2123 - 2*mc 843*mc 2123 + 4*mc 523*mc 843*mc 2123) + 2 * KeccakfPermAir.extraction.inter_2747 c row := by
    simp only [KeccakfPermAir.extraction.inter_2749, KeccakfPermAir.extraction.inter_2748, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_2747 c row = (mc 524 + mc 844 + mc 2124 - 2*mc 524*mc 844 - 2*mc 524*mc 2124 - 2*mc 844*mc 2124 + 4*mc 524*mc 844*mc 2124) + 2 * KeccakfPermAir.extraction.inter_2745 c row := by
    simp only [KeccakfPermAir.extraction.inter_2747, KeccakfPermAir.extraction.inter_2746, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_2745 c row = (mc 525 + mc 845 + mc 2125 - 2*mc 525*mc 845 - 2*mc 525*mc 2125 - 2*mc 845*mc 2125 + 4*mc 525*mc 845*mc 2125) + 2 * KeccakfPermAir.extraction.inter_2743 c row := by
    simp only [KeccakfPermAir.extraction.inter_2745, KeccakfPermAir.extraction.inter_2744, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_2743 c row = (mc 526 + mc 846 + mc 2126 - 2*mc 526*mc 846 - 2*mc 526*mc 2126 - 2*mc 846*mc 2126 + 4*mc 526*mc 846*mc 2126) + 2 * KeccakfPermAir.extraction.inter_2741 c row := by
    simp only [KeccakfPermAir.extraction.inter_2743, KeccakfPermAir.extraction.inter_2742, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_2741 c row = (mc 527 + mc 847 + mc 2127 - 2*mc 527*mc 847 - 2*mc 527*mc 2127 - 2*mc 847*mc 2127 + 4*mc 527*mc 847*mc 2127) + 2 * KeccakfPermAir.extraction.inter_2739 c row := by
    simp only [KeccakfPermAir.extraction.inter_2741, KeccakfPermAir.extraction.inter_2740, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_2739 c row = (mc 528 + mc 848 + mc 2128 - 2*mc 528*mc 848 - 2*mc 528*mc 2128 - 2*mc 848*mc 2128 + 4*mc 528*mc 848*mc 2128) := by
    simp only [KeccakfPermAir.extraction.inter_2739, KeccakfPermAir.extraction.inter_2738, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_2249 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 529 849 2129 204 row) :
    mc 204 = (mc 529 + mc 849 + mc 2129 - 2*mc 529*mc 849 - 2*mc 529*mc 2129 - 2*mc 849*mc 2129 + 4*mc 529*mc 849*mc 2129) + 2*(mc 530 + mc 850 + mc 2130 - 2*mc 530*mc 850 - 2*mc 530*mc 2130 - 2*mc 850*mc 2130 + 4*mc 530*mc 850*mc 2130) + 4*(mc 531 + mc 851 + mc 2131 - 2*mc 531*mc 851 - 2*mc 531*mc 2131 - 2*mc 851*mc 2131 + 4*mc 531*mc 851*mc 2131) + 8*(mc 532 + mc 852 + mc 2132 - 2*mc 532*mc 852 - 2*mc 532*mc 2132 - 2*mc 852*mc 2132 + 4*mc 532*mc 852*mc 2132) + 16*(mc 533 + mc 853 + mc 2133 - 2*mc 533*mc 853 - 2*mc 533*mc 2133 - 2*mc 853*mc 2133 + 4*mc 533*mc 853*mc 2133) + 32*(mc 534 + mc 854 + mc 2134 - 2*mc 534*mc 854 - 2*mc 534*mc 2134 - 2*mc 854*mc 2134 + 4*mc 534*mc 854*mc 2134) + 64*(mc 535 + mc 855 + mc 2135 - 2*mc 535*mc 855 - 2*mc 535*mc 2135 - 2*mc 855*mc 2135 + 4*mc 535*mc 855*mc 2135) + 128*(mc 536 + mc 856 + mc 2136 - 2*mc 536*mc 856 - 2*mc 536*mc 2136 - 2*mc 856*mc 2136 + 4*mc 536*mc 856*mc 2136) + 256*(mc 537 + mc 857 + mc 2137 - 2*mc 537*mc 857 - 2*mc 537*mc 2137 - 2*mc 857*mc 2137 + 4*mc 537*mc 857*mc 2137) + 512*(mc 538 + mc 858 + mc 2138 - 2*mc 538*mc 858 - 2*mc 538*mc 2138 - 2*mc 858*mc 2138 + 4*mc 538*mc 858*mc 2138) + 1024*(mc 539 + mc 859 + mc 2139 - 2*mc 539*mc 859 - 2*mc 539*mc 2139 - 2*mc 859*mc 2139 + 4*mc 539*mc 859*mc 2139) + 2048*(mc 540 + mc 860 + mc 2140 - 2*mc 540*mc 860 - 2*mc 540*mc 2140 - 2*mc 860*mc 2140 + 4*mc 540*mc 860*mc 2140) + 4096*(mc 541 + mc 861 + mc 2141 - 2*mc 541*mc 861 - 2*mc 541*mc 2141 - 2*mc 861*mc 2141 + 4*mc 541*mc 861*mc 2141) + 8192*(mc 542 + mc 862 + mc 2142 - 2*mc 542*mc 862 - 2*mc 542*mc 2142 - 2*mc 862*mc 2142 + 4*mc 542*mc 862*mc 2142) + 16384*(mc 543 + mc 863 + mc 2143 - 2*mc 543*mc 863 - 2*mc 543*mc 2143 - 2*mc 863*mc 2143 + 4*mc 543*mc 863*mc 2143) + 32768*(mc 544 + mc 864 + mc 2144 - 2*mc 544*mc 864 - 2*mc 544*mc 2144 - 2*mc 864*mc 2144 + 4*mc 544*mc 864*mc 2144) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_2249, KeccakfPermAir.extraction.inter_2799, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_2798 c row = (mc 530 + mc 850 + mc 2130 - 2*mc 530*mc 850 - 2*mc 530*mc 2130 - 2*mc 850*mc 2130 + 4*mc 530*mc 850*mc 2130) + 2 * KeccakfPermAir.extraction.inter_2796 c row := by
    simp only [KeccakfPermAir.extraction.inter_2798, KeccakfPermAir.extraction.inter_2797, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_2796 c row = (mc 531 + mc 851 + mc 2131 - 2*mc 531*mc 851 - 2*mc 531*mc 2131 - 2*mc 851*mc 2131 + 4*mc 531*mc 851*mc 2131) + 2 * KeccakfPermAir.extraction.inter_2794 c row := by
    simp only [KeccakfPermAir.extraction.inter_2796, KeccakfPermAir.extraction.inter_2795, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_2794 c row = (mc 532 + mc 852 + mc 2132 - 2*mc 532*mc 852 - 2*mc 532*mc 2132 - 2*mc 852*mc 2132 + 4*mc 532*mc 852*mc 2132) + 2 * KeccakfPermAir.extraction.inter_2792 c row := by
    simp only [KeccakfPermAir.extraction.inter_2794, KeccakfPermAir.extraction.inter_2793, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_2792 c row = (mc 533 + mc 853 + mc 2133 - 2*mc 533*mc 853 - 2*mc 533*mc 2133 - 2*mc 853*mc 2133 + 4*mc 533*mc 853*mc 2133) + 2 * KeccakfPermAir.extraction.inter_2790 c row := by
    simp only [KeccakfPermAir.extraction.inter_2792, KeccakfPermAir.extraction.inter_2791, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_2790 c row = (mc 534 + mc 854 + mc 2134 - 2*mc 534*mc 854 - 2*mc 534*mc 2134 - 2*mc 854*mc 2134 + 4*mc 534*mc 854*mc 2134) + 2 * KeccakfPermAir.extraction.inter_2788 c row := by
    simp only [KeccakfPermAir.extraction.inter_2790, KeccakfPermAir.extraction.inter_2789, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_2788 c row = (mc 535 + mc 855 + mc 2135 - 2*mc 535*mc 855 - 2*mc 535*mc 2135 - 2*mc 855*mc 2135 + 4*mc 535*mc 855*mc 2135) + 2 * KeccakfPermAir.extraction.inter_2786 c row := by
    simp only [KeccakfPermAir.extraction.inter_2788, KeccakfPermAir.extraction.inter_2787, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_2786 c row = (mc 536 + mc 856 + mc 2136 - 2*mc 536*mc 856 - 2*mc 536*mc 2136 - 2*mc 856*mc 2136 + 4*mc 536*mc 856*mc 2136) + 2 * KeccakfPermAir.extraction.inter_2784 c row := by
    simp only [KeccakfPermAir.extraction.inter_2786, KeccakfPermAir.extraction.inter_2785, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_2784 c row = (mc 537 + mc 857 + mc 2137 - 2*mc 537*mc 857 - 2*mc 537*mc 2137 - 2*mc 857*mc 2137 + 4*mc 537*mc 857*mc 2137) + 2 * KeccakfPermAir.extraction.inter_2782 c row := by
    simp only [KeccakfPermAir.extraction.inter_2784, KeccakfPermAir.extraction.inter_2783, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_2782 c row = (mc 538 + mc 858 + mc 2138 - 2*mc 538*mc 858 - 2*mc 538*mc 2138 - 2*mc 858*mc 2138 + 4*mc 538*mc 858*mc 2138) + 2 * KeccakfPermAir.extraction.inter_2780 c row := by
    simp only [KeccakfPermAir.extraction.inter_2782, KeccakfPermAir.extraction.inter_2781, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_2780 c row = (mc 539 + mc 859 + mc 2139 - 2*mc 539*mc 859 - 2*mc 539*mc 2139 - 2*mc 859*mc 2139 + 4*mc 539*mc 859*mc 2139) + 2 * KeccakfPermAir.extraction.inter_2778 c row := by
    simp only [KeccakfPermAir.extraction.inter_2780, KeccakfPermAir.extraction.inter_2779, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_2778 c row = (mc 540 + mc 860 + mc 2140 - 2*mc 540*mc 860 - 2*mc 540*mc 2140 - 2*mc 860*mc 2140 + 4*mc 540*mc 860*mc 2140) + 2 * KeccakfPermAir.extraction.inter_2776 c row := by
    simp only [KeccakfPermAir.extraction.inter_2778, KeccakfPermAir.extraction.inter_2777, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_2776 c row = (mc 541 + mc 861 + mc 2141 - 2*mc 541*mc 861 - 2*mc 541*mc 2141 - 2*mc 861*mc 2141 + 4*mc 541*mc 861*mc 2141) + 2 * KeccakfPermAir.extraction.inter_2774 c row := by
    simp only [KeccakfPermAir.extraction.inter_2776, KeccakfPermAir.extraction.inter_2775, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_2774 c row = (mc 542 + mc 862 + mc 2142 - 2*mc 542*mc 862 - 2*mc 542*mc 2142 - 2*mc 862*mc 2142 + 4*mc 542*mc 862*mc 2142) + 2 * KeccakfPermAir.extraction.inter_2772 c row := by
    simp only [KeccakfPermAir.extraction.inter_2774, KeccakfPermAir.extraction.inter_2773, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_2772 c row = (mc 543 + mc 863 + mc 2143 - 2*mc 543*mc 863 - 2*mc 543*mc 2143 - 2*mc 863*mc 2143 + 4*mc 543*mc 863*mc 2143) + 2 * KeccakfPermAir.extraction.inter_2770 c row := by
    simp only [KeccakfPermAir.extraction.inter_2772, KeccakfPermAir.extraction.inter_2771, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_2770 c row = (mc 544 + mc 864 + mc 2144 - 2*mc 544*mc 864 - 2*mc 544*mc 2144 - 2*mc 864*mc 2144 + 4*mc 544*mc 864*mc 2144) := by
    simp only [KeccakfPermAir.extraction.inter_2770, KeccakfPermAir.extraction.inter_2769, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_2314 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 225 545 2145 205 row) :
    mc 205 = (mc 225 + mc 545 + mc 2145 - 2*mc 225*mc 545 - 2*mc 225*mc 2145 - 2*mc 545*mc 2145 + 4*mc 225*mc 545*mc 2145) + 2*(mc 226 + mc 546 + mc 2146 - 2*mc 226*mc 546 - 2*mc 226*mc 2146 - 2*mc 546*mc 2146 + 4*mc 226*mc 546*mc 2146) + 4*(mc 227 + mc 547 + mc 2147 - 2*mc 227*mc 547 - 2*mc 227*mc 2147 - 2*mc 547*mc 2147 + 4*mc 227*mc 547*mc 2147) + 8*(mc 228 + mc 548 + mc 2148 - 2*mc 228*mc 548 - 2*mc 228*mc 2148 - 2*mc 548*mc 2148 + 4*mc 228*mc 548*mc 2148) + 16*(mc 229 + mc 549 + mc 2149 - 2*mc 229*mc 549 - 2*mc 229*mc 2149 - 2*mc 549*mc 2149 + 4*mc 229*mc 549*mc 2149) + 32*(mc 230 + mc 550 + mc 2150 - 2*mc 230*mc 550 - 2*mc 230*mc 2150 - 2*mc 550*mc 2150 + 4*mc 230*mc 550*mc 2150) + 64*(mc 231 + mc 551 + mc 2151 - 2*mc 231*mc 551 - 2*mc 231*mc 2151 - 2*mc 551*mc 2151 + 4*mc 231*mc 551*mc 2151) + 128*(mc 232 + mc 552 + mc 2152 - 2*mc 232*mc 552 - 2*mc 232*mc 2152 - 2*mc 552*mc 2152 + 4*mc 232*mc 552*mc 2152) + 256*(mc 233 + mc 553 + mc 2153 - 2*mc 233*mc 553 - 2*mc 233*mc 2153 - 2*mc 553*mc 2153 + 4*mc 233*mc 553*mc 2153) + 512*(mc 234 + mc 554 + mc 2154 - 2*mc 234*mc 554 - 2*mc 234*mc 2154 - 2*mc 554*mc 2154 + 4*mc 234*mc 554*mc 2154) + 1024*(mc 235 + mc 555 + mc 2155 - 2*mc 235*mc 555 - 2*mc 235*mc 2155 - 2*mc 555*mc 2155 + 4*mc 235*mc 555*mc 2155) + 2048*(mc 236 + mc 556 + mc 2156 - 2*mc 236*mc 556 - 2*mc 236*mc 2156 - 2*mc 556*mc 2156 + 4*mc 236*mc 556*mc 2156) + 4096*(mc 237 + mc 557 + mc 2157 - 2*mc 237*mc 557 - 2*mc 237*mc 2157 - 2*mc 557*mc 2157 + 4*mc 237*mc 557*mc 2157) + 8192*(mc 238 + mc 558 + mc 2158 - 2*mc 238*mc 558 - 2*mc 238*mc 2158 - 2*mc 558*mc 2158 + 4*mc 238*mc 558*mc 2158) + 16384*(mc 239 + mc 559 + mc 2159 - 2*mc 239*mc 559 - 2*mc 239*mc 2159 - 2*mc 559*mc 2159 + 4*mc 239*mc 559*mc 2159) + 32768*(mc 240 + mc 560 + mc 2160 - 2*mc 240*mc 560 - 2*mc 240*mc 2160 - 2*mc 560*mc 2160 + 4*mc 240*mc 560*mc 2160) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_2314, KeccakfPermAir.extraction.inter_2830, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_2829 c row = (mc 226 + mc 546 + mc 2146 - 2*mc 226*mc 546 - 2*mc 226*mc 2146 - 2*mc 546*mc 2146 + 4*mc 226*mc 546*mc 2146) + 2 * KeccakfPermAir.extraction.inter_2827 c row := by
    simp only [KeccakfPermAir.extraction.inter_2829, KeccakfPermAir.extraction.inter_2828, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_2827 c row = (mc 227 + mc 547 + mc 2147 - 2*mc 227*mc 547 - 2*mc 227*mc 2147 - 2*mc 547*mc 2147 + 4*mc 227*mc 547*mc 2147) + 2 * KeccakfPermAir.extraction.inter_2825 c row := by
    simp only [KeccakfPermAir.extraction.inter_2827, KeccakfPermAir.extraction.inter_2826, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_2825 c row = (mc 228 + mc 548 + mc 2148 - 2*mc 228*mc 548 - 2*mc 228*mc 2148 - 2*mc 548*mc 2148 + 4*mc 228*mc 548*mc 2148) + 2 * KeccakfPermAir.extraction.inter_2823 c row := by
    simp only [KeccakfPermAir.extraction.inter_2825, KeccakfPermAir.extraction.inter_2824, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_2823 c row = (mc 229 + mc 549 + mc 2149 - 2*mc 229*mc 549 - 2*mc 229*mc 2149 - 2*mc 549*mc 2149 + 4*mc 229*mc 549*mc 2149) + 2 * KeccakfPermAir.extraction.inter_2821 c row := by
    simp only [KeccakfPermAir.extraction.inter_2823, KeccakfPermAir.extraction.inter_2822, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_2821 c row = (mc 230 + mc 550 + mc 2150 - 2*mc 230*mc 550 - 2*mc 230*mc 2150 - 2*mc 550*mc 2150 + 4*mc 230*mc 550*mc 2150) + 2 * KeccakfPermAir.extraction.inter_2819 c row := by
    simp only [KeccakfPermAir.extraction.inter_2821, KeccakfPermAir.extraction.inter_2820, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_2819 c row = (mc 231 + mc 551 + mc 2151 - 2*mc 231*mc 551 - 2*mc 231*mc 2151 - 2*mc 551*mc 2151 + 4*mc 231*mc 551*mc 2151) + 2 * KeccakfPermAir.extraction.inter_2817 c row := by
    simp only [KeccakfPermAir.extraction.inter_2819, KeccakfPermAir.extraction.inter_2818, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_2817 c row = (mc 232 + mc 552 + mc 2152 - 2*mc 232*mc 552 - 2*mc 232*mc 2152 - 2*mc 552*mc 2152 + 4*mc 232*mc 552*mc 2152) + 2 * KeccakfPermAir.extraction.inter_2815 c row := by
    simp only [KeccakfPermAir.extraction.inter_2817, KeccakfPermAir.extraction.inter_2816, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_2815 c row = (mc 233 + mc 553 + mc 2153 - 2*mc 233*mc 553 - 2*mc 233*mc 2153 - 2*mc 553*mc 2153 + 4*mc 233*mc 553*mc 2153) + 2 * KeccakfPermAir.extraction.inter_2813 c row := by
    simp only [KeccakfPermAir.extraction.inter_2815, KeccakfPermAir.extraction.inter_2814, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_2813 c row = (mc 234 + mc 554 + mc 2154 - 2*mc 234*mc 554 - 2*mc 234*mc 2154 - 2*mc 554*mc 2154 + 4*mc 234*mc 554*mc 2154) + 2 * KeccakfPermAir.extraction.inter_2811 c row := by
    simp only [KeccakfPermAir.extraction.inter_2813, KeccakfPermAir.extraction.inter_2812, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_2811 c row = (mc 235 + mc 555 + mc 2155 - 2*mc 235*mc 555 - 2*mc 235*mc 2155 - 2*mc 555*mc 2155 + 4*mc 235*mc 555*mc 2155) + 2 * KeccakfPermAir.extraction.inter_2809 c row := by
    simp only [KeccakfPermAir.extraction.inter_2811, KeccakfPermAir.extraction.inter_2810, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_2809 c row = (mc 236 + mc 556 + mc 2156 - 2*mc 236*mc 556 - 2*mc 236*mc 2156 - 2*mc 556*mc 2156 + 4*mc 236*mc 556*mc 2156) + 2 * KeccakfPermAir.extraction.inter_2807 c row := by
    simp only [KeccakfPermAir.extraction.inter_2809, KeccakfPermAir.extraction.inter_2808, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_2807 c row = (mc 237 + mc 557 + mc 2157 - 2*mc 237*mc 557 - 2*mc 237*mc 2157 - 2*mc 557*mc 2157 + 4*mc 237*mc 557*mc 2157) + 2 * KeccakfPermAir.extraction.inter_2805 c row := by
    simp only [KeccakfPermAir.extraction.inter_2807, KeccakfPermAir.extraction.inter_2806, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_2805 c row = (mc 238 + mc 558 + mc 2158 - 2*mc 238*mc 558 - 2*mc 238*mc 2158 - 2*mc 558*mc 2158 + 4*mc 238*mc 558*mc 2158) + 2 * KeccakfPermAir.extraction.inter_2803 c row := by
    simp only [KeccakfPermAir.extraction.inter_2805, KeccakfPermAir.extraction.inter_2804, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_2803 c row = (mc 239 + mc 559 + mc 2159 - 2*mc 239*mc 559 - 2*mc 239*mc 2159 - 2*mc 559*mc 2159 + 4*mc 239*mc 559*mc 2159) + 2 * KeccakfPermAir.extraction.inter_2801 c row := by
    simp only [KeccakfPermAir.extraction.inter_2803, KeccakfPermAir.extraction.inter_2802, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_2801 c row = (mc 240 + mc 560 + mc 2160 - 2*mc 240*mc 560 - 2*mc 240*mc 2160 - 2*mc 560*mc 2160 + 4*mc 240*mc 560*mc 2160) := by
    simp only [KeccakfPermAir.extraction.inter_2801, KeccakfPermAir.extraction.inter_2800, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_2315 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 241 561 2161 206 row) :
    mc 206 = (mc 241 + mc 561 + mc 2161 - 2*mc 241*mc 561 - 2*mc 241*mc 2161 - 2*mc 561*mc 2161 + 4*mc 241*mc 561*mc 2161) + 2*(mc 242 + mc 562 + mc 2162 - 2*mc 242*mc 562 - 2*mc 242*mc 2162 - 2*mc 562*mc 2162 + 4*mc 242*mc 562*mc 2162) + 4*(mc 243 + mc 563 + mc 2163 - 2*mc 243*mc 563 - 2*mc 243*mc 2163 - 2*mc 563*mc 2163 + 4*mc 243*mc 563*mc 2163) + 8*(mc 244 + mc 564 + mc 2164 - 2*mc 244*mc 564 - 2*mc 244*mc 2164 - 2*mc 564*mc 2164 + 4*mc 244*mc 564*mc 2164) + 16*(mc 245 + mc 565 + mc 2165 - 2*mc 245*mc 565 - 2*mc 245*mc 2165 - 2*mc 565*mc 2165 + 4*mc 245*mc 565*mc 2165) + 32*(mc 246 + mc 566 + mc 2166 - 2*mc 246*mc 566 - 2*mc 246*mc 2166 - 2*mc 566*mc 2166 + 4*mc 246*mc 566*mc 2166) + 64*(mc 247 + mc 567 + mc 2167 - 2*mc 247*mc 567 - 2*mc 247*mc 2167 - 2*mc 567*mc 2167 + 4*mc 247*mc 567*mc 2167) + 128*(mc 248 + mc 568 + mc 2168 - 2*mc 248*mc 568 - 2*mc 248*mc 2168 - 2*mc 568*mc 2168 + 4*mc 248*mc 568*mc 2168) + 256*(mc 249 + mc 569 + mc 2169 - 2*mc 249*mc 569 - 2*mc 249*mc 2169 - 2*mc 569*mc 2169 + 4*mc 249*mc 569*mc 2169) + 512*(mc 250 + mc 570 + mc 2170 - 2*mc 250*mc 570 - 2*mc 250*mc 2170 - 2*mc 570*mc 2170 + 4*mc 250*mc 570*mc 2170) + 1024*(mc 251 + mc 571 + mc 2171 - 2*mc 251*mc 571 - 2*mc 251*mc 2171 - 2*mc 571*mc 2171 + 4*mc 251*mc 571*mc 2171) + 2048*(mc 252 + mc 572 + mc 2172 - 2*mc 252*mc 572 - 2*mc 252*mc 2172 - 2*mc 572*mc 2172 + 4*mc 252*mc 572*mc 2172) + 4096*(mc 253 + mc 573 + mc 2173 - 2*mc 253*mc 573 - 2*mc 253*mc 2173 - 2*mc 573*mc 2173 + 4*mc 253*mc 573*mc 2173) + 8192*(mc 254 + mc 574 + mc 2174 - 2*mc 254*mc 574 - 2*mc 254*mc 2174 - 2*mc 574*mc 2174 + 4*mc 254*mc 574*mc 2174) + 16384*(mc 255 + mc 575 + mc 2175 - 2*mc 255*mc 575 - 2*mc 255*mc 2175 - 2*mc 575*mc 2175 + 4*mc 255*mc 575*mc 2175) + 32768*(mc 256 + mc 576 + mc 2176 - 2*mc 256*mc 576 - 2*mc 256*mc 2176 - 2*mc 576*mc 2176 + 4*mc 256*mc 576*mc 2176) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_2315, KeccakfPermAir.extraction.inter_2861, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_2860 c row = (mc 242 + mc 562 + mc 2162 - 2*mc 242*mc 562 - 2*mc 242*mc 2162 - 2*mc 562*mc 2162 + 4*mc 242*mc 562*mc 2162) + 2 * KeccakfPermAir.extraction.inter_2858 c row := by
    simp only [KeccakfPermAir.extraction.inter_2860, KeccakfPermAir.extraction.inter_2859, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_2858 c row = (mc 243 + mc 563 + mc 2163 - 2*mc 243*mc 563 - 2*mc 243*mc 2163 - 2*mc 563*mc 2163 + 4*mc 243*mc 563*mc 2163) + 2 * KeccakfPermAir.extraction.inter_2856 c row := by
    simp only [KeccakfPermAir.extraction.inter_2858, KeccakfPermAir.extraction.inter_2857, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_2856 c row = (mc 244 + mc 564 + mc 2164 - 2*mc 244*mc 564 - 2*mc 244*mc 2164 - 2*mc 564*mc 2164 + 4*mc 244*mc 564*mc 2164) + 2 * KeccakfPermAir.extraction.inter_2854 c row := by
    simp only [KeccakfPermAir.extraction.inter_2856, KeccakfPermAir.extraction.inter_2855, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_2854 c row = (mc 245 + mc 565 + mc 2165 - 2*mc 245*mc 565 - 2*mc 245*mc 2165 - 2*mc 565*mc 2165 + 4*mc 245*mc 565*mc 2165) + 2 * KeccakfPermAir.extraction.inter_2852 c row := by
    simp only [KeccakfPermAir.extraction.inter_2854, KeccakfPermAir.extraction.inter_2853, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_2852 c row = (mc 246 + mc 566 + mc 2166 - 2*mc 246*mc 566 - 2*mc 246*mc 2166 - 2*mc 566*mc 2166 + 4*mc 246*mc 566*mc 2166) + 2 * KeccakfPermAir.extraction.inter_2850 c row := by
    simp only [KeccakfPermAir.extraction.inter_2852, KeccakfPermAir.extraction.inter_2851, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_2850 c row = (mc 247 + mc 567 + mc 2167 - 2*mc 247*mc 567 - 2*mc 247*mc 2167 - 2*mc 567*mc 2167 + 4*mc 247*mc 567*mc 2167) + 2 * KeccakfPermAir.extraction.inter_2848 c row := by
    simp only [KeccakfPermAir.extraction.inter_2850, KeccakfPermAir.extraction.inter_2849, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_2848 c row = (mc 248 + mc 568 + mc 2168 - 2*mc 248*mc 568 - 2*mc 248*mc 2168 - 2*mc 568*mc 2168 + 4*mc 248*mc 568*mc 2168) + 2 * KeccakfPermAir.extraction.inter_2846 c row := by
    simp only [KeccakfPermAir.extraction.inter_2848, KeccakfPermAir.extraction.inter_2847, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_2846 c row = (mc 249 + mc 569 + mc 2169 - 2*mc 249*mc 569 - 2*mc 249*mc 2169 - 2*mc 569*mc 2169 + 4*mc 249*mc 569*mc 2169) + 2 * KeccakfPermAir.extraction.inter_2844 c row := by
    simp only [KeccakfPermAir.extraction.inter_2846, KeccakfPermAir.extraction.inter_2845, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_2844 c row = (mc 250 + mc 570 + mc 2170 - 2*mc 250*mc 570 - 2*mc 250*mc 2170 - 2*mc 570*mc 2170 + 4*mc 250*mc 570*mc 2170) + 2 * KeccakfPermAir.extraction.inter_2842 c row := by
    simp only [KeccakfPermAir.extraction.inter_2844, KeccakfPermAir.extraction.inter_2843, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_2842 c row = (mc 251 + mc 571 + mc 2171 - 2*mc 251*mc 571 - 2*mc 251*mc 2171 - 2*mc 571*mc 2171 + 4*mc 251*mc 571*mc 2171) + 2 * KeccakfPermAir.extraction.inter_2840 c row := by
    simp only [KeccakfPermAir.extraction.inter_2842, KeccakfPermAir.extraction.inter_2841, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_2840 c row = (mc 252 + mc 572 + mc 2172 - 2*mc 252*mc 572 - 2*mc 252*mc 2172 - 2*mc 572*mc 2172 + 4*mc 252*mc 572*mc 2172) + 2 * KeccakfPermAir.extraction.inter_2838 c row := by
    simp only [KeccakfPermAir.extraction.inter_2840, KeccakfPermAir.extraction.inter_2839, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_2838 c row = (mc 253 + mc 573 + mc 2173 - 2*mc 253*mc 573 - 2*mc 253*mc 2173 - 2*mc 573*mc 2173 + 4*mc 253*mc 573*mc 2173) + 2 * KeccakfPermAir.extraction.inter_2836 c row := by
    simp only [KeccakfPermAir.extraction.inter_2838, KeccakfPermAir.extraction.inter_2837, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_2836 c row = (mc 254 + mc 574 + mc 2174 - 2*mc 254*mc 574 - 2*mc 254*mc 2174 - 2*mc 574*mc 2174 + 4*mc 254*mc 574*mc 2174) + 2 * KeccakfPermAir.extraction.inter_2834 c row := by
    simp only [KeccakfPermAir.extraction.inter_2836, KeccakfPermAir.extraction.inter_2835, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_2834 c row = (mc 255 + mc 575 + mc 2175 - 2*mc 255*mc 575 - 2*mc 255*mc 2175 - 2*mc 575*mc 2175 + 4*mc 255*mc 575*mc 2175) + 2 * KeccakfPermAir.extraction.inter_2832 c row := by
    simp only [KeccakfPermAir.extraction.inter_2834, KeccakfPermAir.extraction.inter_2833, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_2832 c row = (mc 256 + mc 576 + mc 2176 - 2*mc 256*mc 576 - 2*mc 256*mc 2176 - 2*mc 576*mc 2176 + 4*mc 256*mc 576*mc 2176) := by
    simp only [KeccakfPermAir.extraction.inter_2832, KeccakfPermAir.extraction.inter_2831, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_2316 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 257 577 2177 207 row) :
    mc 207 = (mc 257 + mc 577 + mc 2177 - 2*mc 257*mc 577 - 2*mc 257*mc 2177 - 2*mc 577*mc 2177 + 4*mc 257*mc 577*mc 2177) + 2*(mc 258 + mc 578 + mc 2178 - 2*mc 258*mc 578 - 2*mc 258*mc 2178 - 2*mc 578*mc 2178 + 4*mc 258*mc 578*mc 2178) + 4*(mc 259 + mc 579 + mc 2179 - 2*mc 259*mc 579 - 2*mc 259*mc 2179 - 2*mc 579*mc 2179 + 4*mc 259*mc 579*mc 2179) + 8*(mc 260 + mc 580 + mc 2180 - 2*mc 260*mc 580 - 2*mc 260*mc 2180 - 2*mc 580*mc 2180 + 4*mc 260*mc 580*mc 2180) + 16*(mc 261 + mc 581 + mc 2181 - 2*mc 261*mc 581 - 2*mc 261*mc 2181 - 2*mc 581*mc 2181 + 4*mc 261*mc 581*mc 2181) + 32*(mc 262 + mc 582 + mc 2182 - 2*mc 262*mc 582 - 2*mc 262*mc 2182 - 2*mc 582*mc 2182 + 4*mc 262*mc 582*mc 2182) + 64*(mc 263 + mc 583 + mc 2183 - 2*mc 263*mc 583 - 2*mc 263*mc 2183 - 2*mc 583*mc 2183 + 4*mc 263*mc 583*mc 2183) + 128*(mc 264 + mc 584 + mc 2184 - 2*mc 264*mc 584 - 2*mc 264*mc 2184 - 2*mc 584*mc 2184 + 4*mc 264*mc 584*mc 2184) + 256*(mc 265 + mc 585 + mc 2185 - 2*mc 265*mc 585 - 2*mc 265*mc 2185 - 2*mc 585*mc 2185 + 4*mc 265*mc 585*mc 2185) + 512*(mc 266 + mc 586 + mc 2186 - 2*mc 266*mc 586 - 2*mc 266*mc 2186 - 2*mc 586*mc 2186 + 4*mc 266*mc 586*mc 2186) + 1024*(mc 267 + mc 587 + mc 2187 - 2*mc 267*mc 587 - 2*mc 267*mc 2187 - 2*mc 587*mc 2187 + 4*mc 267*mc 587*mc 2187) + 2048*(mc 268 + mc 588 + mc 2188 - 2*mc 268*mc 588 - 2*mc 268*mc 2188 - 2*mc 588*mc 2188 + 4*mc 268*mc 588*mc 2188) + 4096*(mc 269 + mc 589 + mc 2189 - 2*mc 269*mc 589 - 2*mc 269*mc 2189 - 2*mc 589*mc 2189 + 4*mc 269*mc 589*mc 2189) + 8192*(mc 270 + mc 590 + mc 2190 - 2*mc 270*mc 590 - 2*mc 270*mc 2190 - 2*mc 590*mc 2190 + 4*mc 270*mc 590*mc 2190) + 16384*(mc 271 + mc 591 + mc 2191 - 2*mc 271*mc 591 - 2*mc 271*mc 2191 - 2*mc 591*mc 2191 + 4*mc 271*mc 591*mc 2191) + 32768*(mc 272 + mc 592 + mc 2192 - 2*mc 272*mc 592 - 2*mc 272*mc 2192 - 2*mc 592*mc 2192 + 4*mc 272*mc 592*mc 2192) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_2316, KeccakfPermAir.extraction.inter_2892, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_2891 c row = (mc 258 + mc 578 + mc 2178 - 2*mc 258*mc 578 - 2*mc 258*mc 2178 - 2*mc 578*mc 2178 + 4*mc 258*mc 578*mc 2178) + 2 * KeccakfPermAir.extraction.inter_2889 c row := by
    simp only [KeccakfPermAir.extraction.inter_2891, KeccakfPermAir.extraction.inter_2890, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_2889 c row = (mc 259 + mc 579 + mc 2179 - 2*mc 259*mc 579 - 2*mc 259*mc 2179 - 2*mc 579*mc 2179 + 4*mc 259*mc 579*mc 2179) + 2 * KeccakfPermAir.extraction.inter_2887 c row := by
    simp only [KeccakfPermAir.extraction.inter_2889, KeccakfPermAir.extraction.inter_2888, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_2887 c row = (mc 260 + mc 580 + mc 2180 - 2*mc 260*mc 580 - 2*mc 260*mc 2180 - 2*mc 580*mc 2180 + 4*mc 260*mc 580*mc 2180) + 2 * KeccakfPermAir.extraction.inter_2885 c row := by
    simp only [KeccakfPermAir.extraction.inter_2887, KeccakfPermAir.extraction.inter_2886, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_2885 c row = (mc 261 + mc 581 + mc 2181 - 2*mc 261*mc 581 - 2*mc 261*mc 2181 - 2*mc 581*mc 2181 + 4*mc 261*mc 581*mc 2181) + 2 * KeccakfPermAir.extraction.inter_2883 c row := by
    simp only [KeccakfPermAir.extraction.inter_2885, KeccakfPermAir.extraction.inter_2884, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_2883 c row = (mc 262 + mc 582 + mc 2182 - 2*mc 262*mc 582 - 2*mc 262*mc 2182 - 2*mc 582*mc 2182 + 4*mc 262*mc 582*mc 2182) + 2 * KeccakfPermAir.extraction.inter_2881 c row := by
    simp only [KeccakfPermAir.extraction.inter_2883, KeccakfPermAir.extraction.inter_2882, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_2881 c row = (mc 263 + mc 583 + mc 2183 - 2*mc 263*mc 583 - 2*mc 263*mc 2183 - 2*mc 583*mc 2183 + 4*mc 263*mc 583*mc 2183) + 2 * KeccakfPermAir.extraction.inter_2879 c row := by
    simp only [KeccakfPermAir.extraction.inter_2881, KeccakfPermAir.extraction.inter_2880, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_2879 c row = (mc 264 + mc 584 + mc 2184 - 2*mc 264*mc 584 - 2*mc 264*mc 2184 - 2*mc 584*mc 2184 + 4*mc 264*mc 584*mc 2184) + 2 * KeccakfPermAir.extraction.inter_2877 c row := by
    simp only [KeccakfPermAir.extraction.inter_2879, KeccakfPermAir.extraction.inter_2878, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_2877 c row = (mc 265 + mc 585 + mc 2185 - 2*mc 265*mc 585 - 2*mc 265*mc 2185 - 2*mc 585*mc 2185 + 4*mc 265*mc 585*mc 2185) + 2 * KeccakfPermAir.extraction.inter_2875 c row := by
    simp only [KeccakfPermAir.extraction.inter_2877, KeccakfPermAir.extraction.inter_2876, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_2875 c row = (mc 266 + mc 586 + mc 2186 - 2*mc 266*mc 586 - 2*mc 266*mc 2186 - 2*mc 586*mc 2186 + 4*mc 266*mc 586*mc 2186) + 2 * KeccakfPermAir.extraction.inter_2873 c row := by
    simp only [KeccakfPermAir.extraction.inter_2875, KeccakfPermAir.extraction.inter_2874, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_2873 c row = (mc 267 + mc 587 + mc 2187 - 2*mc 267*mc 587 - 2*mc 267*mc 2187 - 2*mc 587*mc 2187 + 4*mc 267*mc 587*mc 2187) + 2 * KeccakfPermAir.extraction.inter_2871 c row := by
    simp only [KeccakfPermAir.extraction.inter_2873, KeccakfPermAir.extraction.inter_2872, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_2871 c row = (mc 268 + mc 588 + mc 2188 - 2*mc 268*mc 588 - 2*mc 268*mc 2188 - 2*mc 588*mc 2188 + 4*mc 268*mc 588*mc 2188) + 2 * KeccakfPermAir.extraction.inter_2869 c row := by
    simp only [KeccakfPermAir.extraction.inter_2871, KeccakfPermAir.extraction.inter_2870, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_2869 c row = (mc 269 + mc 589 + mc 2189 - 2*mc 269*mc 589 - 2*mc 269*mc 2189 - 2*mc 589*mc 2189 + 4*mc 269*mc 589*mc 2189) + 2 * KeccakfPermAir.extraction.inter_2867 c row := by
    simp only [KeccakfPermAir.extraction.inter_2869, KeccakfPermAir.extraction.inter_2868, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_2867 c row = (mc 270 + mc 590 + mc 2190 - 2*mc 270*mc 590 - 2*mc 270*mc 2190 - 2*mc 590*mc 2190 + 4*mc 270*mc 590*mc 2190) + 2 * KeccakfPermAir.extraction.inter_2865 c row := by
    simp only [KeccakfPermAir.extraction.inter_2867, KeccakfPermAir.extraction.inter_2866, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_2865 c row = (mc 271 + mc 591 + mc 2191 - 2*mc 271*mc 591 - 2*mc 271*mc 2191 - 2*mc 591*mc 2191 + 4*mc 271*mc 591*mc 2191) + 2 * KeccakfPermAir.extraction.inter_2863 c row := by
    simp only [KeccakfPermAir.extraction.inter_2865, KeccakfPermAir.extraction.inter_2864, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_2863 c row = (mc 272 + mc 592 + mc 2192 - 2*mc 272*mc 592 - 2*mc 272*mc 2192 - 2*mc 592*mc 2192 + 4*mc 272*mc 592*mc 2192) := by
    simp only [KeccakfPermAir.extraction.inter_2863, KeccakfPermAir.extraction.inter_2862, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_2317 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 273 593 2193 208 row) :
    mc 208 = (mc 273 + mc 593 + mc 2193 - 2*mc 273*mc 593 - 2*mc 273*mc 2193 - 2*mc 593*mc 2193 + 4*mc 273*mc 593*mc 2193) + 2*(mc 274 + mc 594 + mc 2194 - 2*mc 274*mc 594 - 2*mc 274*mc 2194 - 2*mc 594*mc 2194 + 4*mc 274*mc 594*mc 2194) + 4*(mc 275 + mc 595 + mc 2195 - 2*mc 275*mc 595 - 2*mc 275*mc 2195 - 2*mc 595*mc 2195 + 4*mc 275*mc 595*mc 2195) + 8*(mc 276 + mc 596 + mc 2196 - 2*mc 276*mc 596 - 2*mc 276*mc 2196 - 2*mc 596*mc 2196 + 4*mc 276*mc 596*mc 2196) + 16*(mc 277 + mc 597 + mc 2197 - 2*mc 277*mc 597 - 2*mc 277*mc 2197 - 2*mc 597*mc 2197 + 4*mc 277*mc 597*mc 2197) + 32*(mc 278 + mc 598 + mc 2198 - 2*mc 278*mc 598 - 2*mc 278*mc 2198 - 2*mc 598*mc 2198 + 4*mc 278*mc 598*mc 2198) + 64*(mc 279 + mc 599 + mc 2199 - 2*mc 279*mc 599 - 2*mc 279*mc 2199 - 2*mc 599*mc 2199 + 4*mc 279*mc 599*mc 2199) + 128*(mc 280 + mc 600 + mc 2200 - 2*mc 280*mc 600 - 2*mc 280*mc 2200 - 2*mc 600*mc 2200 + 4*mc 280*mc 600*mc 2200) + 256*(mc 281 + mc 601 + mc 2201 - 2*mc 281*mc 601 - 2*mc 281*mc 2201 - 2*mc 601*mc 2201 + 4*mc 281*mc 601*mc 2201) + 512*(mc 282 + mc 602 + mc 2202 - 2*mc 282*mc 602 - 2*mc 282*mc 2202 - 2*mc 602*mc 2202 + 4*mc 282*mc 602*mc 2202) + 1024*(mc 283 + mc 603 + mc 2203 - 2*mc 283*mc 603 - 2*mc 283*mc 2203 - 2*mc 603*mc 2203 + 4*mc 283*mc 603*mc 2203) + 2048*(mc 284 + mc 604 + mc 2204 - 2*mc 284*mc 604 - 2*mc 284*mc 2204 - 2*mc 604*mc 2204 + 4*mc 284*mc 604*mc 2204) + 4096*(mc 285 + mc 605 + mc 2205 - 2*mc 285*mc 605 - 2*mc 285*mc 2205 - 2*mc 605*mc 2205 + 4*mc 285*mc 605*mc 2205) + 8192*(mc 286 + mc 606 + mc 2206 - 2*mc 286*mc 606 - 2*mc 286*mc 2206 - 2*mc 606*mc 2206 + 4*mc 286*mc 606*mc 2206) + 16384*(mc 287 + mc 607 + mc 2207 - 2*mc 287*mc 607 - 2*mc 287*mc 2207 - 2*mc 607*mc 2207 + 4*mc 287*mc 607*mc 2207) + 32768*(mc 288 + mc 608 + mc 2208 - 2*mc 288*mc 608 - 2*mc 288*mc 2208 - 2*mc 608*mc 2208 + 4*mc 288*mc 608*mc 2208) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_2317, KeccakfPermAir.extraction.inter_2923, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_2922 c row = (mc 274 + mc 594 + mc 2194 - 2*mc 274*mc 594 - 2*mc 274*mc 2194 - 2*mc 594*mc 2194 + 4*mc 274*mc 594*mc 2194) + 2 * KeccakfPermAir.extraction.inter_2920 c row := by
    simp only [KeccakfPermAir.extraction.inter_2922, KeccakfPermAir.extraction.inter_2921, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_2920 c row = (mc 275 + mc 595 + mc 2195 - 2*mc 275*mc 595 - 2*mc 275*mc 2195 - 2*mc 595*mc 2195 + 4*mc 275*mc 595*mc 2195) + 2 * KeccakfPermAir.extraction.inter_2918 c row := by
    simp only [KeccakfPermAir.extraction.inter_2920, KeccakfPermAir.extraction.inter_2919, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_2918 c row = (mc 276 + mc 596 + mc 2196 - 2*mc 276*mc 596 - 2*mc 276*mc 2196 - 2*mc 596*mc 2196 + 4*mc 276*mc 596*mc 2196) + 2 * KeccakfPermAir.extraction.inter_2916 c row := by
    simp only [KeccakfPermAir.extraction.inter_2918, KeccakfPermAir.extraction.inter_2917, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_2916 c row = (mc 277 + mc 597 + mc 2197 - 2*mc 277*mc 597 - 2*mc 277*mc 2197 - 2*mc 597*mc 2197 + 4*mc 277*mc 597*mc 2197) + 2 * KeccakfPermAir.extraction.inter_2914 c row := by
    simp only [KeccakfPermAir.extraction.inter_2916, KeccakfPermAir.extraction.inter_2915, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_2914 c row = (mc 278 + mc 598 + mc 2198 - 2*mc 278*mc 598 - 2*mc 278*mc 2198 - 2*mc 598*mc 2198 + 4*mc 278*mc 598*mc 2198) + 2 * KeccakfPermAir.extraction.inter_2912 c row := by
    simp only [KeccakfPermAir.extraction.inter_2914, KeccakfPermAir.extraction.inter_2913, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_2912 c row = (mc 279 + mc 599 + mc 2199 - 2*mc 279*mc 599 - 2*mc 279*mc 2199 - 2*mc 599*mc 2199 + 4*mc 279*mc 599*mc 2199) + 2 * KeccakfPermAir.extraction.inter_2910 c row := by
    simp only [KeccakfPermAir.extraction.inter_2912, KeccakfPermAir.extraction.inter_2911, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_2910 c row = (mc 280 + mc 600 + mc 2200 - 2*mc 280*mc 600 - 2*mc 280*mc 2200 - 2*mc 600*mc 2200 + 4*mc 280*mc 600*mc 2200) + 2 * KeccakfPermAir.extraction.inter_2908 c row := by
    simp only [KeccakfPermAir.extraction.inter_2910, KeccakfPermAir.extraction.inter_2909, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_2908 c row = (mc 281 + mc 601 + mc 2201 - 2*mc 281*mc 601 - 2*mc 281*mc 2201 - 2*mc 601*mc 2201 + 4*mc 281*mc 601*mc 2201) + 2 * KeccakfPermAir.extraction.inter_2906 c row := by
    simp only [KeccakfPermAir.extraction.inter_2908, KeccakfPermAir.extraction.inter_2907, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_2906 c row = (mc 282 + mc 602 + mc 2202 - 2*mc 282*mc 602 - 2*mc 282*mc 2202 - 2*mc 602*mc 2202 + 4*mc 282*mc 602*mc 2202) + 2 * KeccakfPermAir.extraction.inter_2904 c row := by
    simp only [KeccakfPermAir.extraction.inter_2906, KeccakfPermAir.extraction.inter_2905, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_2904 c row = (mc 283 + mc 603 + mc 2203 - 2*mc 283*mc 603 - 2*mc 283*mc 2203 - 2*mc 603*mc 2203 + 4*mc 283*mc 603*mc 2203) + 2 * KeccakfPermAir.extraction.inter_2902 c row := by
    simp only [KeccakfPermAir.extraction.inter_2904, KeccakfPermAir.extraction.inter_2903, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_2902 c row = (mc 284 + mc 604 + mc 2204 - 2*mc 284*mc 604 - 2*mc 284*mc 2204 - 2*mc 604*mc 2204 + 4*mc 284*mc 604*mc 2204) + 2 * KeccakfPermAir.extraction.inter_2900 c row := by
    simp only [KeccakfPermAir.extraction.inter_2902, KeccakfPermAir.extraction.inter_2901, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_2900 c row = (mc 285 + mc 605 + mc 2205 - 2*mc 285*mc 605 - 2*mc 285*mc 2205 - 2*mc 605*mc 2205 + 4*mc 285*mc 605*mc 2205) + 2 * KeccakfPermAir.extraction.inter_2898 c row := by
    simp only [KeccakfPermAir.extraction.inter_2900, KeccakfPermAir.extraction.inter_2899, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_2898 c row = (mc 286 + mc 606 + mc 2206 - 2*mc 286*mc 606 - 2*mc 286*mc 2206 - 2*mc 606*mc 2206 + 4*mc 286*mc 606*mc 2206) + 2 * KeccakfPermAir.extraction.inter_2896 c row := by
    simp only [KeccakfPermAir.extraction.inter_2898, KeccakfPermAir.extraction.inter_2897, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_2896 c row = (mc 287 + mc 607 + mc 2207 - 2*mc 287*mc 607 - 2*mc 287*mc 2207 - 2*mc 607*mc 2207 + 4*mc 287*mc 607*mc 2207) + 2 * KeccakfPermAir.extraction.inter_2894 c row := by
    simp only [KeccakfPermAir.extraction.inter_2896, KeccakfPermAir.extraction.inter_2895, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_2894 c row = (mc 288 + mc 608 + mc 2208 - 2*mc 288*mc 608 - 2*mc 288*mc 2208 - 2*mc 608*mc 2208 + 4*mc 288*mc 608*mc 2208) := by
    simp only [KeccakfPermAir.extraction.inter_2894, KeccakfPermAir.extraction.inter_2893, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_2382 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 289 609 2209 209 row) :
    mc 209 = (mc 289 + mc 609 + mc 2209 - 2*mc 289*mc 609 - 2*mc 289*mc 2209 - 2*mc 609*mc 2209 + 4*mc 289*mc 609*mc 2209) + 2*(mc 290 + mc 610 + mc 2210 - 2*mc 290*mc 610 - 2*mc 290*mc 2210 - 2*mc 610*mc 2210 + 4*mc 290*mc 610*mc 2210) + 4*(mc 291 + mc 611 + mc 2211 - 2*mc 291*mc 611 - 2*mc 291*mc 2211 - 2*mc 611*mc 2211 + 4*mc 291*mc 611*mc 2211) + 8*(mc 292 + mc 612 + mc 2212 - 2*mc 292*mc 612 - 2*mc 292*mc 2212 - 2*mc 612*mc 2212 + 4*mc 292*mc 612*mc 2212) + 16*(mc 293 + mc 613 + mc 2213 - 2*mc 293*mc 613 - 2*mc 293*mc 2213 - 2*mc 613*mc 2213 + 4*mc 293*mc 613*mc 2213) + 32*(mc 294 + mc 614 + mc 2214 - 2*mc 294*mc 614 - 2*mc 294*mc 2214 - 2*mc 614*mc 2214 + 4*mc 294*mc 614*mc 2214) + 64*(mc 295 + mc 615 + mc 2215 - 2*mc 295*mc 615 - 2*mc 295*mc 2215 - 2*mc 615*mc 2215 + 4*mc 295*mc 615*mc 2215) + 128*(mc 296 + mc 616 + mc 2216 - 2*mc 296*mc 616 - 2*mc 296*mc 2216 - 2*mc 616*mc 2216 + 4*mc 296*mc 616*mc 2216) + 256*(mc 297 + mc 617 + mc 2217 - 2*mc 297*mc 617 - 2*mc 297*mc 2217 - 2*mc 617*mc 2217 + 4*mc 297*mc 617*mc 2217) + 512*(mc 298 + mc 618 + mc 2218 - 2*mc 298*mc 618 - 2*mc 298*mc 2218 - 2*mc 618*mc 2218 + 4*mc 298*mc 618*mc 2218) + 1024*(mc 299 + mc 619 + mc 2219 - 2*mc 299*mc 619 - 2*mc 299*mc 2219 - 2*mc 619*mc 2219 + 4*mc 299*mc 619*mc 2219) + 2048*(mc 300 + mc 620 + mc 2220 - 2*mc 300*mc 620 - 2*mc 300*mc 2220 - 2*mc 620*mc 2220 + 4*mc 300*mc 620*mc 2220) + 4096*(mc 301 + mc 621 + mc 2221 - 2*mc 301*mc 621 - 2*mc 301*mc 2221 - 2*mc 621*mc 2221 + 4*mc 301*mc 621*mc 2221) + 8192*(mc 302 + mc 622 + mc 2222 - 2*mc 302*mc 622 - 2*mc 302*mc 2222 - 2*mc 622*mc 2222 + 4*mc 302*mc 622*mc 2222) + 16384*(mc 303 + mc 623 + mc 2223 - 2*mc 303*mc 623 - 2*mc 303*mc 2223 - 2*mc 623*mc 2223 + 4*mc 303*mc 623*mc 2223) + 32768*(mc 304 + mc 624 + mc 2224 - 2*mc 304*mc 624 - 2*mc 304*mc 2224 - 2*mc 624*mc 2224 + 4*mc 304*mc 624*mc 2224) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_2382, KeccakfPermAir.extraction.inter_2954, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_2953 c row = (mc 290 + mc 610 + mc 2210 - 2*mc 290*mc 610 - 2*mc 290*mc 2210 - 2*mc 610*mc 2210 + 4*mc 290*mc 610*mc 2210) + 2 * KeccakfPermAir.extraction.inter_2951 c row := by
    simp only [KeccakfPermAir.extraction.inter_2953, KeccakfPermAir.extraction.inter_2952, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_2951 c row = (mc 291 + mc 611 + mc 2211 - 2*mc 291*mc 611 - 2*mc 291*mc 2211 - 2*mc 611*mc 2211 + 4*mc 291*mc 611*mc 2211) + 2 * KeccakfPermAir.extraction.inter_2949 c row := by
    simp only [KeccakfPermAir.extraction.inter_2951, KeccakfPermAir.extraction.inter_2950, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_2949 c row = (mc 292 + mc 612 + mc 2212 - 2*mc 292*mc 612 - 2*mc 292*mc 2212 - 2*mc 612*mc 2212 + 4*mc 292*mc 612*mc 2212) + 2 * KeccakfPermAir.extraction.inter_2947 c row := by
    simp only [KeccakfPermAir.extraction.inter_2949, KeccakfPermAir.extraction.inter_2948, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_2947 c row = (mc 293 + mc 613 + mc 2213 - 2*mc 293*mc 613 - 2*mc 293*mc 2213 - 2*mc 613*mc 2213 + 4*mc 293*mc 613*mc 2213) + 2 * KeccakfPermAir.extraction.inter_2945 c row := by
    simp only [KeccakfPermAir.extraction.inter_2947, KeccakfPermAir.extraction.inter_2946, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_2945 c row = (mc 294 + mc 614 + mc 2214 - 2*mc 294*mc 614 - 2*mc 294*mc 2214 - 2*mc 614*mc 2214 + 4*mc 294*mc 614*mc 2214) + 2 * KeccakfPermAir.extraction.inter_2943 c row := by
    simp only [KeccakfPermAir.extraction.inter_2945, KeccakfPermAir.extraction.inter_2944, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_2943 c row = (mc 295 + mc 615 + mc 2215 - 2*mc 295*mc 615 - 2*mc 295*mc 2215 - 2*mc 615*mc 2215 + 4*mc 295*mc 615*mc 2215) + 2 * KeccakfPermAir.extraction.inter_2941 c row := by
    simp only [KeccakfPermAir.extraction.inter_2943, KeccakfPermAir.extraction.inter_2942, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_2941 c row = (mc 296 + mc 616 + mc 2216 - 2*mc 296*mc 616 - 2*mc 296*mc 2216 - 2*mc 616*mc 2216 + 4*mc 296*mc 616*mc 2216) + 2 * KeccakfPermAir.extraction.inter_2939 c row := by
    simp only [KeccakfPermAir.extraction.inter_2941, KeccakfPermAir.extraction.inter_2940, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_2939 c row = (mc 297 + mc 617 + mc 2217 - 2*mc 297*mc 617 - 2*mc 297*mc 2217 - 2*mc 617*mc 2217 + 4*mc 297*mc 617*mc 2217) + 2 * KeccakfPermAir.extraction.inter_2937 c row := by
    simp only [KeccakfPermAir.extraction.inter_2939, KeccakfPermAir.extraction.inter_2938, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_2937 c row = (mc 298 + mc 618 + mc 2218 - 2*mc 298*mc 618 - 2*mc 298*mc 2218 - 2*mc 618*mc 2218 + 4*mc 298*mc 618*mc 2218) + 2 * KeccakfPermAir.extraction.inter_2935 c row := by
    simp only [KeccakfPermAir.extraction.inter_2937, KeccakfPermAir.extraction.inter_2936, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_2935 c row = (mc 299 + mc 619 + mc 2219 - 2*mc 299*mc 619 - 2*mc 299*mc 2219 - 2*mc 619*mc 2219 + 4*mc 299*mc 619*mc 2219) + 2 * KeccakfPermAir.extraction.inter_2933 c row := by
    simp only [KeccakfPermAir.extraction.inter_2935, KeccakfPermAir.extraction.inter_2934, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_2933 c row = (mc 300 + mc 620 + mc 2220 - 2*mc 300*mc 620 - 2*mc 300*mc 2220 - 2*mc 620*mc 2220 + 4*mc 300*mc 620*mc 2220) + 2 * KeccakfPermAir.extraction.inter_2931 c row := by
    simp only [KeccakfPermAir.extraction.inter_2933, KeccakfPermAir.extraction.inter_2932, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_2931 c row = (mc 301 + mc 621 + mc 2221 - 2*mc 301*mc 621 - 2*mc 301*mc 2221 - 2*mc 621*mc 2221 + 4*mc 301*mc 621*mc 2221) + 2 * KeccakfPermAir.extraction.inter_2929 c row := by
    simp only [KeccakfPermAir.extraction.inter_2931, KeccakfPermAir.extraction.inter_2930, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_2929 c row = (mc 302 + mc 622 + mc 2222 - 2*mc 302*mc 622 - 2*mc 302*mc 2222 - 2*mc 622*mc 2222 + 4*mc 302*mc 622*mc 2222) + 2 * KeccakfPermAir.extraction.inter_2927 c row := by
    simp only [KeccakfPermAir.extraction.inter_2929, KeccakfPermAir.extraction.inter_2928, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_2927 c row = (mc 303 + mc 623 + mc 2223 - 2*mc 303*mc 623 - 2*mc 303*mc 2223 - 2*mc 623*mc 2223 + 4*mc 303*mc 623*mc 2223) + 2 * KeccakfPermAir.extraction.inter_2925 c row := by
    simp only [KeccakfPermAir.extraction.inter_2927, KeccakfPermAir.extraction.inter_2926, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_2925 c row = (mc 304 + mc 624 + mc 2224 - 2*mc 304*mc 624 - 2*mc 304*mc 2224 - 2*mc 624*mc 2224 + 4*mc 304*mc 624*mc 2224) := by
    simp only [KeccakfPermAir.extraction.inter_2925, KeccakfPermAir.extraction.inter_2924, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_2383 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 305 625 2225 210 row) :
    mc 210 = (mc 305 + mc 625 + mc 2225 - 2*mc 305*mc 625 - 2*mc 305*mc 2225 - 2*mc 625*mc 2225 + 4*mc 305*mc 625*mc 2225) + 2*(mc 306 + mc 626 + mc 2226 - 2*mc 306*mc 626 - 2*mc 306*mc 2226 - 2*mc 626*mc 2226 + 4*mc 306*mc 626*mc 2226) + 4*(mc 307 + mc 627 + mc 2227 - 2*mc 307*mc 627 - 2*mc 307*mc 2227 - 2*mc 627*mc 2227 + 4*mc 307*mc 627*mc 2227) + 8*(mc 308 + mc 628 + mc 2228 - 2*mc 308*mc 628 - 2*mc 308*mc 2228 - 2*mc 628*mc 2228 + 4*mc 308*mc 628*mc 2228) + 16*(mc 309 + mc 629 + mc 2229 - 2*mc 309*mc 629 - 2*mc 309*mc 2229 - 2*mc 629*mc 2229 + 4*mc 309*mc 629*mc 2229) + 32*(mc 310 + mc 630 + mc 2230 - 2*mc 310*mc 630 - 2*mc 310*mc 2230 - 2*mc 630*mc 2230 + 4*mc 310*mc 630*mc 2230) + 64*(mc 311 + mc 631 + mc 2231 - 2*mc 311*mc 631 - 2*mc 311*mc 2231 - 2*mc 631*mc 2231 + 4*mc 311*mc 631*mc 2231) + 128*(mc 312 + mc 632 + mc 2232 - 2*mc 312*mc 632 - 2*mc 312*mc 2232 - 2*mc 632*mc 2232 + 4*mc 312*mc 632*mc 2232) + 256*(mc 313 + mc 633 + mc 2233 - 2*mc 313*mc 633 - 2*mc 313*mc 2233 - 2*mc 633*mc 2233 + 4*mc 313*mc 633*mc 2233) + 512*(mc 314 + mc 634 + mc 2234 - 2*mc 314*mc 634 - 2*mc 314*mc 2234 - 2*mc 634*mc 2234 + 4*mc 314*mc 634*mc 2234) + 1024*(mc 315 + mc 635 + mc 2235 - 2*mc 315*mc 635 - 2*mc 315*mc 2235 - 2*mc 635*mc 2235 + 4*mc 315*mc 635*mc 2235) + 2048*(mc 316 + mc 636 + mc 2236 - 2*mc 316*mc 636 - 2*mc 316*mc 2236 - 2*mc 636*mc 2236 + 4*mc 316*mc 636*mc 2236) + 4096*(mc 317 + mc 637 + mc 2237 - 2*mc 317*mc 637 - 2*mc 317*mc 2237 - 2*mc 637*mc 2237 + 4*mc 317*mc 637*mc 2237) + 8192*(mc 318 + mc 638 + mc 2238 - 2*mc 318*mc 638 - 2*mc 318*mc 2238 - 2*mc 638*mc 2238 + 4*mc 318*mc 638*mc 2238) + 16384*(mc 319 + mc 639 + mc 2239 - 2*mc 319*mc 639 - 2*mc 319*mc 2239 - 2*mc 639*mc 2239 + 4*mc 319*mc 639*mc 2239) + 32768*(mc 320 + mc 640 + mc 2240 - 2*mc 320*mc 640 - 2*mc 320*mc 2240 - 2*mc 640*mc 2240 + 4*mc 320*mc 640*mc 2240) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_2383, KeccakfPermAir.extraction.inter_2985, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_2984 c row = (mc 306 + mc 626 + mc 2226 - 2*mc 306*mc 626 - 2*mc 306*mc 2226 - 2*mc 626*mc 2226 + 4*mc 306*mc 626*mc 2226) + 2 * KeccakfPermAir.extraction.inter_2982 c row := by
    simp only [KeccakfPermAir.extraction.inter_2984, KeccakfPermAir.extraction.inter_2983, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_2982 c row = (mc 307 + mc 627 + mc 2227 - 2*mc 307*mc 627 - 2*mc 307*mc 2227 - 2*mc 627*mc 2227 + 4*mc 307*mc 627*mc 2227) + 2 * KeccakfPermAir.extraction.inter_2980 c row := by
    simp only [KeccakfPermAir.extraction.inter_2982, KeccakfPermAir.extraction.inter_2981, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_2980 c row = (mc 308 + mc 628 + mc 2228 - 2*mc 308*mc 628 - 2*mc 308*mc 2228 - 2*mc 628*mc 2228 + 4*mc 308*mc 628*mc 2228) + 2 * KeccakfPermAir.extraction.inter_2978 c row := by
    simp only [KeccakfPermAir.extraction.inter_2980, KeccakfPermAir.extraction.inter_2979, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_2978 c row = (mc 309 + mc 629 + mc 2229 - 2*mc 309*mc 629 - 2*mc 309*mc 2229 - 2*mc 629*mc 2229 + 4*mc 309*mc 629*mc 2229) + 2 * KeccakfPermAir.extraction.inter_2976 c row := by
    simp only [KeccakfPermAir.extraction.inter_2978, KeccakfPermAir.extraction.inter_2977, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_2976 c row = (mc 310 + mc 630 + mc 2230 - 2*mc 310*mc 630 - 2*mc 310*mc 2230 - 2*mc 630*mc 2230 + 4*mc 310*mc 630*mc 2230) + 2 * KeccakfPermAir.extraction.inter_2974 c row := by
    simp only [KeccakfPermAir.extraction.inter_2976, KeccakfPermAir.extraction.inter_2975, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_2974 c row = (mc 311 + mc 631 + mc 2231 - 2*mc 311*mc 631 - 2*mc 311*mc 2231 - 2*mc 631*mc 2231 + 4*mc 311*mc 631*mc 2231) + 2 * KeccakfPermAir.extraction.inter_2972 c row := by
    simp only [KeccakfPermAir.extraction.inter_2974, KeccakfPermAir.extraction.inter_2973, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_2972 c row = (mc 312 + mc 632 + mc 2232 - 2*mc 312*mc 632 - 2*mc 312*mc 2232 - 2*mc 632*mc 2232 + 4*mc 312*mc 632*mc 2232) + 2 * KeccakfPermAir.extraction.inter_2970 c row := by
    simp only [KeccakfPermAir.extraction.inter_2972, KeccakfPermAir.extraction.inter_2971, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_2970 c row = (mc 313 + mc 633 + mc 2233 - 2*mc 313*mc 633 - 2*mc 313*mc 2233 - 2*mc 633*mc 2233 + 4*mc 313*mc 633*mc 2233) + 2 * KeccakfPermAir.extraction.inter_2968 c row := by
    simp only [KeccakfPermAir.extraction.inter_2970, KeccakfPermAir.extraction.inter_2969, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_2968 c row = (mc 314 + mc 634 + mc 2234 - 2*mc 314*mc 634 - 2*mc 314*mc 2234 - 2*mc 634*mc 2234 + 4*mc 314*mc 634*mc 2234) + 2 * KeccakfPermAir.extraction.inter_2966 c row := by
    simp only [KeccakfPermAir.extraction.inter_2968, KeccakfPermAir.extraction.inter_2967, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_2966 c row = (mc 315 + mc 635 + mc 2235 - 2*mc 315*mc 635 - 2*mc 315*mc 2235 - 2*mc 635*mc 2235 + 4*mc 315*mc 635*mc 2235) + 2 * KeccakfPermAir.extraction.inter_2964 c row := by
    simp only [KeccakfPermAir.extraction.inter_2966, KeccakfPermAir.extraction.inter_2965, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_2964 c row = (mc 316 + mc 636 + mc 2236 - 2*mc 316*mc 636 - 2*mc 316*mc 2236 - 2*mc 636*mc 2236 + 4*mc 316*mc 636*mc 2236) + 2 * KeccakfPermAir.extraction.inter_2962 c row := by
    simp only [KeccakfPermAir.extraction.inter_2964, KeccakfPermAir.extraction.inter_2963, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_2962 c row = (mc 317 + mc 637 + mc 2237 - 2*mc 317*mc 637 - 2*mc 317*mc 2237 - 2*mc 637*mc 2237 + 4*mc 317*mc 637*mc 2237) + 2 * KeccakfPermAir.extraction.inter_2960 c row := by
    simp only [KeccakfPermAir.extraction.inter_2962, KeccakfPermAir.extraction.inter_2961, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_2960 c row = (mc 318 + mc 638 + mc 2238 - 2*mc 318*mc 638 - 2*mc 318*mc 2238 - 2*mc 638*mc 2238 + 4*mc 318*mc 638*mc 2238) + 2 * KeccakfPermAir.extraction.inter_2958 c row := by
    simp only [KeccakfPermAir.extraction.inter_2960, KeccakfPermAir.extraction.inter_2959, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_2958 c row = (mc 319 + mc 639 + mc 2239 - 2*mc 319*mc 639 - 2*mc 319*mc 2239 - 2*mc 639*mc 2239 + 4*mc 319*mc 639*mc 2239) + 2 * KeccakfPermAir.extraction.inter_2956 c row := by
    simp only [KeccakfPermAir.extraction.inter_2958, KeccakfPermAir.extraction.inter_2957, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_2956 c row = (mc 320 + mc 640 + mc 2240 - 2*mc 320*mc 640 - 2*mc 320*mc 2240 - 2*mc 640*mc 2240 + 4*mc 320*mc 640*mc 2240) := by
    simp only [KeccakfPermAir.extraction.inter_2956, KeccakfPermAir.extraction.inter_2955, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_2384 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 321 641 2241 211 row) :
    mc 211 = (mc 321 + mc 641 + mc 2241 - 2*mc 321*mc 641 - 2*mc 321*mc 2241 - 2*mc 641*mc 2241 + 4*mc 321*mc 641*mc 2241) + 2*(mc 322 + mc 642 + mc 2242 - 2*mc 322*mc 642 - 2*mc 322*mc 2242 - 2*mc 642*mc 2242 + 4*mc 322*mc 642*mc 2242) + 4*(mc 323 + mc 643 + mc 2243 - 2*mc 323*mc 643 - 2*mc 323*mc 2243 - 2*mc 643*mc 2243 + 4*mc 323*mc 643*mc 2243) + 8*(mc 324 + mc 644 + mc 2244 - 2*mc 324*mc 644 - 2*mc 324*mc 2244 - 2*mc 644*mc 2244 + 4*mc 324*mc 644*mc 2244) + 16*(mc 325 + mc 645 + mc 2245 - 2*mc 325*mc 645 - 2*mc 325*mc 2245 - 2*mc 645*mc 2245 + 4*mc 325*mc 645*mc 2245) + 32*(mc 326 + mc 646 + mc 2246 - 2*mc 326*mc 646 - 2*mc 326*mc 2246 - 2*mc 646*mc 2246 + 4*mc 326*mc 646*mc 2246) + 64*(mc 327 + mc 647 + mc 2247 - 2*mc 327*mc 647 - 2*mc 327*mc 2247 - 2*mc 647*mc 2247 + 4*mc 327*mc 647*mc 2247) + 128*(mc 328 + mc 648 + mc 2248 - 2*mc 328*mc 648 - 2*mc 328*mc 2248 - 2*mc 648*mc 2248 + 4*mc 328*mc 648*mc 2248) + 256*(mc 329 + mc 649 + mc 2249 - 2*mc 329*mc 649 - 2*mc 329*mc 2249 - 2*mc 649*mc 2249 + 4*mc 329*mc 649*mc 2249) + 512*(mc 330 + mc 650 + mc 2250 - 2*mc 330*mc 650 - 2*mc 330*mc 2250 - 2*mc 650*mc 2250 + 4*mc 330*mc 650*mc 2250) + 1024*(mc 331 + mc 651 + mc 2251 - 2*mc 331*mc 651 - 2*mc 331*mc 2251 - 2*mc 651*mc 2251 + 4*mc 331*mc 651*mc 2251) + 2048*(mc 332 + mc 652 + mc 2252 - 2*mc 332*mc 652 - 2*mc 332*mc 2252 - 2*mc 652*mc 2252 + 4*mc 332*mc 652*mc 2252) + 4096*(mc 333 + mc 653 + mc 2253 - 2*mc 333*mc 653 - 2*mc 333*mc 2253 - 2*mc 653*mc 2253 + 4*mc 333*mc 653*mc 2253) + 8192*(mc 334 + mc 654 + mc 2254 - 2*mc 334*mc 654 - 2*mc 334*mc 2254 - 2*mc 654*mc 2254 + 4*mc 334*mc 654*mc 2254) + 16384*(mc 335 + mc 655 + mc 2255 - 2*mc 335*mc 655 - 2*mc 335*mc 2255 - 2*mc 655*mc 2255 + 4*mc 335*mc 655*mc 2255) + 32768*(mc 336 + mc 656 + mc 2256 - 2*mc 336*mc 656 - 2*mc 336*mc 2256 - 2*mc 656*mc 2256 + 4*mc 336*mc 656*mc 2256) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_2384, KeccakfPermAir.extraction.inter_3016, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_3015 c row = (mc 322 + mc 642 + mc 2242 - 2*mc 322*mc 642 - 2*mc 322*mc 2242 - 2*mc 642*mc 2242 + 4*mc 322*mc 642*mc 2242) + 2 * KeccakfPermAir.extraction.inter_3013 c row := by
    simp only [KeccakfPermAir.extraction.inter_3015, KeccakfPermAir.extraction.inter_3014, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_3013 c row = (mc 323 + mc 643 + mc 2243 - 2*mc 323*mc 643 - 2*mc 323*mc 2243 - 2*mc 643*mc 2243 + 4*mc 323*mc 643*mc 2243) + 2 * KeccakfPermAir.extraction.inter_3011 c row := by
    simp only [KeccakfPermAir.extraction.inter_3013, KeccakfPermAir.extraction.inter_3012, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_3011 c row = (mc 324 + mc 644 + mc 2244 - 2*mc 324*mc 644 - 2*mc 324*mc 2244 - 2*mc 644*mc 2244 + 4*mc 324*mc 644*mc 2244) + 2 * KeccakfPermAir.extraction.inter_3009 c row := by
    simp only [KeccakfPermAir.extraction.inter_3011, KeccakfPermAir.extraction.inter_3010, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_3009 c row = (mc 325 + mc 645 + mc 2245 - 2*mc 325*mc 645 - 2*mc 325*mc 2245 - 2*mc 645*mc 2245 + 4*mc 325*mc 645*mc 2245) + 2 * KeccakfPermAir.extraction.inter_3007 c row := by
    simp only [KeccakfPermAir.extraction.inter_3009, KeccakfPermAir.extraction.inter_3008, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_3007 c row = (mc 326 + mc 646 + mc 2246 - 2*mc 326*mc 646 - 2*mc 326*mc 2246 - 2*mc 646*mc 2246 + 4*mc 326*mc 646*mc 2246) + 2 * KeccakfPermAir.extraction.inter_3005 c row := by
    simp only [KeccakfPermAir.extraction.inter_3007, KeccakfPermAir.extraction.inter_3006, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_3005 c row = (mc 327 + mc 647 + mc 2247 - 2*mc 327*mc 647 - 2*mc 327*mc 2247 - 2*mc 647*mc 2247 + 4*mc 327*mc 647*mc 2247) + 2 * KeccakfPermAir.extraction.inter_3003 c row := by
    simp only [KeccakfPermAir.extraction.inter_3005, KeccakfPermAir.extraction.inter_3004, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_3003 c row = (mc 328 + mc 648 + mc 2248 - 2*mc 328*mc 648 - 2*mc 328*mc 2248 - 2*mc 648*mc 2248 + 4*mc 328*mc 648*mc 2248) + 2 * KeccakfPermAir.extraction.inter_3001 c row := by
    simp only [KeccakfPermAir.extraction.inter_3003, KeccakfPermAir.extraction.inter_3002, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_3001 c row = (mc 329 + mc 649 + mc 2249 - 2*mc 329*mc 649 - 2*mc 329*mc 2249 - 2*mc 649*mc 2249 + 4*mc 329*mc 649*mc 2249) + 2 * KeccakfPermAir.extraction.inter_2999 c row := by
    simp only [KeccakfPermAir.extraction.inter_3001, KeccakfPermAir.extraction.inter_3000, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_2999 c row = (mc 330 + mc 650 + mc 2250 - 2*mc 330*mc 650 - 2*mc 330*mc 2250 - 2*mc 650*mc 2250 + 4*mc 330*mc 650*mc 2250) + 2 * KeccakfPermAir.extraction.inter_2997 c row := by
    simp only [KeccakfPermAir.extraction.inter_2999, KeccakfPermAir.extraction.inter_2998, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_2997 c row = (mc 331 + mc 651 + mc 2251 - 2*mc 331*mc 651 - 2*mc 331*mc 2251 - 2*mc 651*mc 2251 + 4*mc 331*mc 651*mc 2251) + 2 * KeccakfPermAir.extraction.inter_2995 c row := by
    simp only [KeccakfPermAir.extraction.inter_2997, KeccakfPermAir.extraction.inter_2996, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_2995 c row = (mc 332 + mc 652 + mc 2252 - 2*mc 332*mc 652 - 2*mc 332*mc 2252 - 2*mc 652*mc 2252 + 4*mc 332*mc 652*mc 2252) + 2 * KeccakfPermAir.extraction.inter_2993 c row := by
    simp only [KeccakfPermAir.extraction.inter_2995, KeccakfPermAir.extraction.inter_2994, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_2993 c row = (mc 333 + mc 653 + mc 2253 - 2*mc 333*mc 653 - 2*mc 333*mc 2253 - 2*mc 653*mc 2253 + 4*mc 333*mc 653*mc 2253) + 2 * KeccakfPermAir.extraction.inter_2991 c row := by
    simp only [KeccakfPermAir.extraction.inter_2993, KeccakfPermAir.extraction.inter_2992, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_2991 c row = (mc 334 + mc 654 + mc 2254 - 2*mc 334*mc 654 - 2*mc 334*mc 2254 - 2*mc 654*mc 2254 + 4*mc 334*mc 654*mc 2254) + 2 * KeccakfPermAir.extraction.inter_2989 c row := by
    simp only [KeccakfPermAir.extraction.inter_2991, KeccakfPermAir.extraction.inter_2990, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_2989 c row = (mc 335 + mc 655 + mc 2255 - 2*mc 335*mc 655 - 2*mc 335*mc 2255 - 2*mc 655*mc 2255 + 4*mc 335*mc 655*mc 2255) + 2 * KeccakfPermAir.extraction.inter_2987 c row := by
    simp only [KeccakfPermAir.extraction.inter_2989, KeccakfPermAir.extraction.inter_2988, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_2987 c row = (mc 336 + mc 656 + mc 2256 - 2*mc 336*mc 656 - 2*mc 336*mc 2256 - 2*mc 656*mc 2256 + 4*mc 336*mc 656*mc 2256) := by
    simp only [KeccakfPermAir.extraction.inter_2987, KeccakfPermAir.extraction.inter_2986, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_2385 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 337 657 2257 212 row) :
    mc 212 = (mc 337 + mc 657 + mc 2257 - 2*mc 337*mc 657 - 2*mc 337*mc 2257 - 2*mc 657*mc 2257 + 4*mc 337*mc 657*mc 2257) + 2*(mc 338 + mc 658 + mc 2258 - 2*mc 338*mc 658 - 2*mc 338*mc 2258 - 2*mc 658*mc 2258 + 4*mc 338*mc 658*mc 2258) + 4*(mc 339 + mc 659 + mc 2259 - 2*mc 339*mc 659 - 2*mc 339*mc 2259 - 2*mc 659*mc 2259 + 4*mc 339*mc 659*mc 2259) + 8*(mc 340 + mc 660 + mc 2260 - 2*mc 340*mc 660 - 2*mc 340*mc 2260 - 2*mc 660*mc 2260 + 4*mc 340*mc 660*mc 2260) + 16*(mc 341 + mc 661 + mc 2261 - 2*mc 341*mc 661 - 2*mc 341*mc 2261 - 2*mc 661*mc 2261 + 4*mc 341*mc 661*mc 2261) + 32*(mc 342 + mc 662 + mc 2262 - 2*mc 342*mc 662 - 2*mc 342*mc 2262 - 2*mc 662*mc 2262 + 4*mc 342*mc 662*mc 2262) + 64*(mc 343 + mc 663 + mc 2263 - 2*mc 343*mc 663 - 2*mc 343*mc 2263 - 2*mc 663*mc 2263 + 4*mc 343*mc 663*mc 2263) + 128*(mc 344 + mc 664 + mc 2264 - 2*mc 344*mc 664 - 2*mc 344*mc 2264 - 2*mc 664*mc 2264 + 4*mc 344*mc 664*mc 2264) + 256*(mc 345 + mc 665 + mc 2265 - 2*mc 345*mc 665 - 2*mc 345*mc 2265 - 2*mc 665*mc 2265 + 4*mc 345*mc 665*mc 2265) + 512*(mc 346 + mc 666 + mc 2266 - 2*mc 346*mc 666 - 2*mc 346*mc 2266 - 2*mc 666*mc 2266 + 4*mc 346*mc 666*mc 2266) + 1024*(mc 347 + mc 667 + mc 2267 - 2*mc 347*mc 667 - 2*mc 347*mc 2267 - 2*mc 667*mc 2267 + 4*mc 347*mc 667*mc 2267) + 2048*(mc 348 + mc 668 + mc 2268 - 2*mc 348*mc 668 - 2*mc 348*mc 2268 - 2*mc 668*mc 2268 + 4*mc 348*mc 668*mc 2268) + 4096*(mc 349 + mc 669 + mc 2269 - 2*mc 349*mc 669 - 2*mc 349*mc 2269 - 2*mc 669*mc 2269 + 4*mc 349*mc 669*mc 2269) + 8192*(mc 350 + mc 670 + mc 2270 - 2*mc 350*mc 670 - 2*mc 350*mc 2270 - 2*mc 670*mc 2270 + 4*mc 350*mc 670*mc 2270) + 16384*(mc 351 + mc 671 + mc 2271 - 2*mc 351*mc 671 - 2*mc 351*mc 2271 - 2*mc 671*mc 2271 + 4*mc 351*mc 671*mc 2271) + 32768*(mc 352 + mc 672 + mc 2272 - 2*mc 352*mc 672 - 2*mc 352*mc 2272 - 2*mc 672*mc 2272 + 4*mc 352*mc 672*mc 2272) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_2385, KeccakfPermAir.extraction.inter_3047, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_3046 c row = (mc 338 + mc 658 + mc 2258 - 2*mc 338*mc 658 - 2*mc 338*mc 2258 - 2*mc 658*mc 2258 + 4*mc 338*mc 658*mc 2258) + 2 * KeccakfPermAir.extraction.inter_3044 c row := by
    simp only [KeccakfPermAir.extraction.inter_3046, KeccakfPermAir.extraction.inter_3045, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_3044 c row = (mc 339 + mc 659 + mc 2259 - 2*mc 339*mc 659 - 2*mc 339*mc 2259 - 2*mc 659*mc 2259 + 4*mc 339*mc 659*mc 2259) + 2 * KeccakfPermAir.extraction.inter_3042 c row := by
    simp only [KeccakfPermAir.extraction.inter_3044, KeccakfPermAir.extraction.inter_3043, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_3042 c row = (mc 340 + mc 660 + mc 2260 - 2*mc 340*mc 660 - 2*mc 340*mc 2260 - 2*mc 660*mc 2260 + 4*mc 340*mc 660*mc 2260) + 2 * KeccakfPermAir.extraction.inter_3040 c row := by
    simp only [KeccakfPermAir.extraction.inter_3042, KeccakfPermAir.extraction.inter_3041, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_3040 c row = (mc 341 + mc 661 + mc 2261 - 2*mc 341*mc 661 - 2*mc 341*mc 2261 - 2*mc 661*mc 2261 + 4*mc 341*mc 661*mc 2261) + 2 * KeccakfPermAir.extraction.inter_3038 c row := by
    simp only [KeccakfPermAir.extraction.inter_3040, KeccakfPermAir.extraction.inter_3039, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_3038 c row = (mc 342 + mc 662 + mc 2262 - 2*mc 342*mc 662 - 2*mc 342*mc 2262 - 2*mc 662*mc 2262 + 4*mc 342*mc 662*mc 2262) + 2 * KeccakfPermAir.extraction.inter_3036 c row := by
    simp only [KeccakfPermAir.extraction.inter_3038, KeccakfPermAir.extraction.inter_3037, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_3036 c row = (mc 343 + mc 663 + mc 2263 - 2*mc 343*mc 663 - 2*mc 343*mc 2263 - 2*mc 663*mc 2263 + 4*mc 343*mc 663*mc 2263) + 2 * KeccakfPermAir.extraction.inter_3034 c row := by
    simp only [KeccakfPermAir.extraction.inter_3036, KeccakfPermAir.extraction.inter_3035, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_3034 c row = (mc 344 + mc 664 + mc 2264 - 2*mc 344*mc 664 - 2*mc 344*mc 2264 - 2*mc 664*mc 2264 + 4*mc 344*mc 664*mc 2264) + 2 * KeccakfPermAir.extraction.inter_3032 c row := by
    simp only [KeccakfPermAir.extraction.inter_3034, KeccakfPermAir.extraction.inter_3033, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_3032 c row = (mc 345 + mc 665 + mc 2265 - 2*mc 345*mc 665 - 2*mc 345*mc 2265 - 2*mc 665*mc 2265 + 4*mc 345*mc 665*mc 2265) + 2 * KeccakfPermAir.extraction.inter_3030 c row := by
    simp only [KeccakfPermAir.extraction.inter_3032, KeccakfPermAir.extraction.inter_3031, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_3030 c row = (mc 346 + mc 666 + mc 2266 - 2*mc 346*mc 666 - 2*mc 346*mc 2266 - 2*mc 666*mc 2266 + 4*mc 346*mc 666*mc 2266) + 2 * KeccakfPermAir.extraction.inter_3028 c row := by
    simp only [KeccakfPermAir.extraction.inter_3030, KeccakfPermAir.extraction.inter_3029, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_3028 c row = (mc 347 + mc 667 + mc 2267 - 2*mc 347*mc 667 - 2*mc 347*mc 2267 - 2*mc 667*mc 2267 + 4*mc 347*mc 667*mc 2267) + 2 * KeccakfPermAir.extraction.inter_3026 c row := by
    simp only [KeccakfPermAir.extraction.inter_3028, KeccakfPermAir.extraction.inter_3027, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_3026 c row = (mc 348 + mc 668 + mc 2268 - 2*mc 348*mc 668 - 2*mc 348*mc 2268 - 2*mc 668*mc 2268 + 4*mc 348*mc 668*mc 2268) + 2 * KeccakfPermAir.extraction.inter_3024 c row := by
    simp only [KeccakfPermAir.extraction.inter_3026, KeccakfPermAir.extraction.inter_3025, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_3024 c row = (mc 349 + mc 669 + mc 2269 - 2*mc 349*mc 669 - 2*mc 349*mc 2269 - 2*mc 669*mc 2269 + 4*mc 349*mc 669*mc 2269) + 2 * KeccakfPermAir.extraction.inter_3022 c row := by
    simp only [KeccakfPermAir.extraction.inter_3024, KeccakfPermAir.extraction.inter_3023, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_3022 c row = (mc 350 + mc 670 + mc 2270 - 2*mc 350*mc 670 - 2*mc 350*mc 2270 - 2*mc 670*mc 2270 + 4*mc 350*mc 670*mc 2270) + 2 * KeccakfPermAir.extraction.inter_3020 c row := by
    simp only [KeccakfPermAir.extraction.inter_3022, KeccakfPermAir.extraction.inter_3021, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_3020 c row = (mc 351 + mc 671 + mc 2271 - 2*mc 351*mc 671 - 2*mc 351*mc 2271 - 2*mc 671*mc 2271 + 4*mc 351*mc 671*mc 2271) + 2 * KeccakfPermAir.extraction.inter_3018 c row := by
    simp only [KeccakfPermAir.extraction.inter_3020, KeccakfPermAir.extraction.inter_3019, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_3018 c row = (mc 352 + mc 672 + mc 2272 - 2*mc 352*mc 672 - 2*mc 352*mc 2272 - 2*mc 672*mc 2272 + 4*mc 352*mc 672*mc 2272) := by
    simp only [KeccakfPermAir.extraction.inter_3018, KeccakfPermAir.extraction.inter_3017, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_2450 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 353 673 2273 213 row) :
    mc 213 = (mc 353 + mc 673 + mc 2273 - 2*mc 353*mc 673 - 2*mc 353*mc 2273 - 2*mc 673*mc 2273 + 4*mc 353*mc 673*mc 2273) + 2*(mc 354 + mc 674 + mc 2274 - 2*mc 354*mc 674 - 2*mc 354*mc 2274 - 2*mc 674*mc 2274 + 4*mc 354*mc 674*mc 2274) + 4*(mc 355 + mc 675 + mc 2275 - 2*mc 355*mc 675 - 2*mc 355*mc 2275 - 2*mc 675*mc 2275 + 4*mc 355*mc 675*mc 2275) + 8*(mc 356 + mc 676 + mc 2276 - 2*mc 356*mc 676 - 2*mc 356*mc 2276 - 2*mc 676*mc 2276 + 4*mc 356*mc 676*mc 2276) + 16*(mc 357 + mc 677 + mc 2277 - 2*mc 357*mc 677 - 2*mc 357*mc 2277 - 2*mc 677*mc 2277 + 4*mc 357*mc 677*mc 2277) + 32*(mc 358 + mc 678 + mc 2278 - 2*mc 358*mc 678 - 2*mc 358*mc 2278 - 2*mc 678*mc 2278 + 4*mc 358*mc 678*mc 2278) + 64*(mc 359 + mc 679 + mc 2279 - 2*mc 359*mc 679 - 2*mc 359*mc 2279 - 2*mc 679*mc 2279 + 4*mc 359*mc 679*mc 2279) + 128*(mc 360 + mc 680 + mc 2280 - 2*mc 360*mc 680 - 2*mc 360*mc 2280 - 2*mc 680*mc 2280 + 4*mc 360*mc 680*mc 2280) + 256*(mc 361 + mc 681 + mc 2281 - 2*mc 361*mc 681 - 2*mc 361*mc 2281 - 2*mc 681*mc 2281 + 4*mc 361*mc 681*mc 2281) + 512*(mc 362 + mc 682 + mc 2282 - 2*mc 362*mc 682 - 2*mc 362*mc 2282 - 2*mc 682*mc 2282 + 4*mc 362*mc 682*mc 2282) + 1024*(mc 363 + mc 683 + mc 2283 - 2*mc 363*mc 683 - 2*mc 363*mc 2283 - 2*mc 683*mc 2283 + 4*mc 363*mc 683*mc 2283) + 2048*(mc 364 + mc 684 + mc 2284 - 2*mc 364*mc 684 - 2*mc 364*mc 2284 - 2*mc 684*mc 2284 + 4*mc 364*mc 684*mc 2284) + 4096*(mc 365 + mc 685 + mc 2285 - 2*mc 365*mc 685 - 2*mc 365*mc 2285 - 2*mc 685*mc 2285 + 4*mc 365*mc 685*mc 2285) + 8192*(mc 366 + mc 686 + mc 2286 - 2*mc 366*mc 686 - 2*mc 366*mc 2286 - 2*mc 686*mc 2286 + 4*mc 366*mc 686*mc 2286) + 16384*(mc 367 + mc 687 + mc 2287 - 2*mc 367*mc 687 - 2*mc 367*mc 2287 - 2*mc 687*mc 2287 + 4*mc 367*mc 687*mc 2287) + 32768*(mc 368 + mc 688 + mc 2288 - 2*mc 368*mc 688 - 2*mc 368*mc 2288 - 2*mc 688*mc 2288 + 4*mc 368*mc 688*mc 2288) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_2450, KeccakfPermAir.extraction.inter_3078, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_3077 c row = (mc 354 + mc 674 + mc 2274 - 2*mc 354*mc 674 - 2*mc 354*mc 2274 - 2*mc 674*mc 2274 + 4*mc 354*mc 674*mc 2274) + 2 * KeccakfPermAir.extraction.inter_3075 c row := by
    simp only [KeccakfPermAir.extraction.inter_3077, KeccakfPermAir.extraction.inter_3076, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_3075 c row = (mc 355 + mc 675 + mc 2275 - 2*mc 355*mc 675 - 2*mc 355*mc 2275 - 2*mc 675*mc 2275 + 4*mc 355*mc 675*mc 2275) + 2 * KeccakfPermAir.extraction.inter_3073 c row := by
    simp only [KeccakfPermAir.extraction.inter_3075, KeccakfPermAir.extraction.inter_3074, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_3073 c row = (mc 356 + mc 676 + mc 2276 - 2*mc 356*mc 676 - 2*mc 356*mc 2276 - 2*mc 676*mc 2276 + 4*mc 356*mc 676*mc 2276) + 2 * KeccakfPermAir.extraction.inter_3071 c row := by
    simp only [KeccakfPermAir.extraction.inter_3073, KeccakfPermAir.extraction.inter_3072, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_3071 c row = (mc 357 + mc 677 + mc 2277 - 2*mc 357*mc 677 - 2*mc 357*mc 2277 - 2*mc 677*mc 2277 + 4*mc 357*mc 677*mc 2277) + 2 * KeccakfPermAir.extraction.inter_3069 c row := by
    simp only [KeccakfPermAir.extraction.inter_3071, KeccakfPermAir.extraction.inter_3070, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_3069 c row = (mc 358 + mc 678 + mc 2278 - 2*mc 358*mc 678 - 2*mc 358*mc 2278 - 2*mc 678*mc 2278 + 4*mc 358*mc 678*mc 2278) + 2 * KeccakfPermAir.extraction.inter_3067 c row := by
    simp only [KeccakfPermAir.extraction.inter_3069, KeccakfPermAir.extraction.inter_3068, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_3067 c row = (mc 359 + mc 679 + mc 2279 - 2*mc 359*mc 679 - 2*mc 359*mc 2279 - 2*mc 679*mc 2279 + 4*mc 359*mc 679*mc 2279) + 2 * KeccakfPermAir.extraction.inter_3065 c row := by
    simp only [KeccakfPermAir.extraction.inter_3067, KeccakfPermAir.extraction.inter_3066, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_3065 c row = (mc 360 + mc 680 + mc 2280 - 2*mc 360*mc 680 - 2*mc 360*mc 2280 - 2*mc 680*mc 2280 + 4*mc 360*mc 680*mc 2280) + 2 * KeccakfPermAir.extraction.inter_3063 c row := by
    simp only [KeccakfPermAir.extraction.inter_3065, KeccakfPermAir.extraction.inter_3064, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_3063 c row = (mc 361 + mc 681 + mc 2281 - 2*mc 361*mc 681 - 2*mc 361*mc 2281 - 2*mc 681*mc 2281 + 4*mc 361*mc 681*mc 2281) + 2 * KeccakfPermAir.extraction.inter_3061 c row := by
    simp only [KeccakfPermAir.extraction.inter_3063, KeccakfPermAir.extraction.inter_3062, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_3061 c row = (mc 362 + mc 682 + mc 2282 - 2*mc 362*mc 682 - 2*mc 362*mc 2282 - 2*mc 682*mc 2282 + 4*mc 362*mc 682*mc 2282) + 2 * KeccakfPermAir.extraction.inter_3059 c row := by
    simp only [KeccakfPermAir.extraction.inter_3061, KeccakfPermAir.extraction.inter_3060, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_3059 c row = (mc 363 + mc 683 + mc 2283 - 2*mc 363*mc 683 - 2*mc 363*mc 2283 - 2*mc 683*mc 2283 + 4*mc 363*mc 683*mc 2283) + 2 * KeccakfPermAir.extraction.inter_3057 c row := by
    simp only [KeccakfPermAir.extraction.inter_3059, KeccakfPermAir.extraction.inter_3058, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_3057 c row = (mc 364 + mc 684 + mc 2284 - 2*mc 364*mc 684 - 2*mc 364*mc 2284 - 2*mc 684*mc 2284 + 4*mc 364*mc 684*mc 2284) + 2 * KeccakfPermAir.extraction.inter_3055 c row := by
    simp only [KeccakfPermAir.extraction.inter_3057, KeccakfPermAir.extraction.inter_3056, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_3055 c row = (mc 365 + mc 685 + mc 2285 - 2*mc 365*mc 685 - 2*mc 365*mc 2285 - 2*mc 685*mc 2285 + 4*mc 365*mc 685*mc 2285) + 2 * KeccakfPermAir.extraction.inter_3053 c row := by
    simp only [KeccakfPermAir.extraction.inter_3055, KeccakfPermAir.extraction.inter_3054, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_3053 c row = (mc 366 + mc 686 + mc 2286 - 2*mc 366*mc 686 - 2*mc 366*mc 2286 - 2*mc 686*mc 2286 + 4*mc 366*mc 686*mc 2286) + 2 * KeccakfPermAir.extraction.inter_3051 c row := by
    simp only [KeccakfPermAir.extraction.inter_3053, KeccakfPermAir.extraction.inter_3052, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_3051 c row = (mc 367 + mc 687 + mc 2287 - 2*mc 367*mc 687 - 2*mc 367*mc 2287 - 2*mc 687*mc 2287 + 4*mc 367*mc 687*mc 2287) + 2 * KeccakfPermAir.extraction.inter_3049 c row := by
    simp only [KeccakfPermAir.extraction.inter_3051, KeccakfPermAir.extraction.inter_3050, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_3049 c row = (mc 368 + mc 688 + mc 2288 - 2*mc 368*mc 688 - 2*mc 368*mc 2288 - 2*mc 688*mc 2288 + 4*mc 368*mc 688*mc 2288) := by
    simp only [KeccakfPermAir.extraction.inter_3049, KeccakfPermAir.extraction.inter_3048, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_2451 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 369 689 2289 214 row) :
    mc 214 = (mc 369 + mc 689 + mc 2289 - 2*mc 369*mc 689 - 2*mc 369*mc 2289 - 2*mc 689*mc 2289 + 4*mc 369*mc 689*mc 2289) + 2*(mc 370 + mc 690 + mc 2290 - 2*mc 370*mc 690 - 2*mc 370*mc 2290 - 2*mc 690*mc 2290 + 4*mc 370*mc 690*mc 2290) + 4*(mc 371 + mc 691 + mc 2291 - 2*mc 371*mc 691 - 2*mc 371*mc 2291 - 2*mc 691*mc 2291 + 4*mc 371*mc 691*mc 2291) + 8*(mc 372 + mc 692 + mc 2292 - 2*mc 372*mc 692 - 2*mc 372*mc 2292 - 2*mc 692*mc 2292 + 4*mc 372*mc 692*mc 2292) + 16*(mc 373 + mc 693 + mc 2293 - 2*mc 373*mc 693 - 2*mc 373*mc 2293 - 2*mc 693*mc 2293 + 4*mc 373*mc 693*mc 2293) + 32*(mc 374 + mc 694 + mc 2294 - 2*mc 374*mc 694 - 2*mc 374*mc 2294 - 2*mc 694*mc 2294 + 4*mc 374*mc 694*mc 2294) + 64*(mc 375 + mc 695 + mc 2295 - 2*mc 375*mc 695 - 2*mc 375*mc 2295 - 2*mc 695*mc 2295 + 4*mc 375*mc 695*mc 2295) + 128*(mc 376 + mc 696 + mc 2296 - 2*mc 376*mc 696 - 2*mc 376*mc 2296 - 2*mc 696*mc 2296 + 4*mc 376*mc 696*mc 2296) + 256*(mc 377 + mc 697 + mc 2297 - 2*mc 377*mc 697 - 2*mc 377*mc 2297 - 2*mc 697*mc 2297 + 4*mc 377*mc 697*mc 2297) + 512*(mc 378 + mc 698 + mc 2298 - 2*mc 378*mc 698 - 2*mc 378*mc 2298 - 2*mc 698*mc 2298 + 4*mc 378*mc 698*mc 2298) + 1024*(mc 379 + mc 699 + mc 2299 - 2*mc 379*mc 699 - 2*mc 379*mc 2299 - 2*mc 699*mc 2299 + 4*mc 379*mc 699*mc 2299) + 2048*(mc 380 + mc 700 + mc 2300 - 2*mc 380*mc 700 - 2*mc 380*mc 2300 - 2*mc 700*mc 2300 + 4*mc 380*mc 700*mc 2300) + 4096*(mc 381 + mc 701 + mc 2301 - 2*mc 381*mc 701 - 2*mc 381*mc 2301 - 2*mc 701*mc 2301 + 4*mc 381*mc 701*mc 2301) + 8192*(mc 382 + mc 702 + mc 2302 - 2*mc 382*mc 702 - 2*mc 382*mc 2302 - 2*mc 702*mc 2302 + 4*mc 382*mc 702*mc 2302) + 16384*(mc 383 + mc 703 + mc 2303 - 2*mc 383*mc 703 - 2*mc 383*mc 2303 - 2*mc 703*mc 2303 + 4*mc 383*mc 703*mc 2303) + 32768*(mc 384 + mc 704 + mc 2304 - 2*mc 384*mc 704 - 2*mc 384*mc 2304 - 2*mc 704*mc 2304 + 4*mc 384*mc 704*mc 2304) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_2451, KeccakfPermAir.extraction.inter_3109, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_3108 c row = (mc 370 + mc 690 + mc 2290 - 2*mc 370*mc 690 - 2*mc 370*mc 2290 - 2*mc 690*mc 2290 + 4*mc 370*mc 690*mc 2290) + 2 * KeccakfPermAir.extraction.inter_3106 c row := by
    simp only [KeccakfPermAir.extraction.inter_3108, KeccakfPermAir.extraction.inter_3107, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_3106 c row = (mc 371 + mc 691 + mc 2291 - 2*mc 371*mc 691 - 2*mc 371*mc 2291 - 2*mc 691*mc 2291 + 4*mc 371*mc 691*mc 2291) + 2 * KeccakfPermAir.extraction.inter_3104 c row := by
    simp only [KeccakfPermAir.extraction.inter_3106, KeccakfPermAir.extraction.inter_3105, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_3104 c row = (mc 372 + mc 692 + mc 2292 - 2*mc 372*mc 692 - 2*mc 372*mc 2292 - 2*mc 692*mc 2292 + 4*mc 372*mc 692*mc 2292) + 2 * KeccakfPermAir.extraction.inter_3102 c row := by
    simp only [KeccakfPermAir.extraction.inter_3104, KeccakfPermAir.extraction.inter_3103, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_3102 c row = (mc 373 + mc 693 + mc 2293 - 2*mc 373*mc 693 - 2*mc 373*mc 2293 - 2*mc 693*mc 2293 + 4*mc 373*mc 693*mc 2293) + 2 * KeccakfPermAir.extraction.inter_3100 c row := by
    simp only [KeccakfPermAir.extraction.inter_3102, KeccakfPermAir.extraction.inter_3101, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_3100 c row = (mc 374 + mc 694 + mc 2294 - 2*mc 374*mc 694 - 2*mc 374*mc 2294 - 2*mc 694*mc 2294 + 4*mc 374*mc 694*mc 2294) + 2 * KeccakfPermAir.extraction.inter_3098 c row := by
    simp only [KeccakfPermAir.extraction.inter_3100, KeccakfPermAir.extraction.inter_3099, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_3098 c row = (mc 375 + mc 695 + mc 2295 - 2*mc 375*mc 695 - 2*mc 375*mc 2295 - 2*mc 695*mc 2295 + 4*mc 375*mc 695*mc 2295) + 2 * KeccakfPermAir.extraction.inter_3096 c row := by
    simp only [KeccakfPermAir.extraction.inter_3098, KeccakfPermAir.extraction.inter_3097, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_3096 c row = (mc 376 + mc 696 + mc 2296 - 2*mc 376*mc 696 - 2*mc 376*mc 2296 - 2*mc 696*mc 2296 + 4*mc 376*mc 696*mc 2296) + 2 * KeccakfPermAir.extraction.inter_3094 c row := by
    simp only [KeccakfPermAir.extraction.inter_3096, KeccakfPermAir.extraction.inter_3095, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_3094 c row = (mc 377 + mc 697 + mc 2297 - 2*mc 377*mc 697 - 2*mc 377*mc 2297 - 2*mc 697*mc 2297 + 4*mc 377*mc 697*mc 2297) + 2 * KeccakfPermAir.extraction.inter_3092 c row := by
    simp only [KeccakfPermAir.extraction.inter_3094, KeccakfPermAir.extraction.inter_3093, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_3092 c row = (mc 378 + mc 698 + mc 2298 - 2*mc 378*mc 698 - 2*mc 378*mc 2298 - 2*mc 698*mc 2298 + 4*mc 378*mc 698*mc 2298) + 2 * KeccakfPermAir.extraction.inter_3090 c row := by
    simp only [KeccakfPermAir.extraction.inter_3092, KeccakfPermAir.extraction.inter_3091, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_3090 c row = (mc 379 + mc 699 + mc 2299 - 2*mc 379*mc 699 - 2*mc 379*mc 2299 - 2*mc 699*mc 2299 + 4*mc 379*mc 699*mc 2299) + 2 * KeccakfPermAir.extraction.inter_3088 c row := by
    simp only [KeccakfPermAir.extraction.inter_3090, KeccakfPermAir.extraction.inter_3089, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_3088 c row = (mc 380 + mc 700 + mc 2300 - 2*mc 380*mc 700 - 2*mc 380*mc 2300 - 2*mc 700*mc 2300 + 4*mc 380*mc 700*mc 2300) + 2 * KeccakfPermAir.extraction.inter_3086 c row := by
    simp only [KeccakfPermAir.extraction.inter_3088, KeccakfPermAir.extraction.inter_3087, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_3086 c row = (mc 381 + mc 701 + mc 2301 - 2*mc 381*mc 701 - 2*mc 381*mc 2301 - 2*mc 701*mc 2301 + 4*mc 381*mc 701*mc 2301) + 2 * KeccakfPermAir.extraction.inter_3084 c row := by
    simp only [KeccakfPermAir.extraction.inter_3086, KeccakfPermAir.extraction.inter_3085, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_3084 c row = (mc 382 + mc 702 + mc 2302 - 2*mc 382*mc 702 - 2*mc 382*mc 2302 - 2*mc 702*mc 2302 + 4*mc 382*mc 702*mc 2302) + 2 * KeccakfPermAir.extraction.inter_3082 c row := by
    simp only [KeccakfPermAir.extraction.inter_3084, KeccakfPermAir.extraction.inter_3083, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_3082 c row = (mc 383 + mc 703 + mc 2303 - 2*mc 383*mc 703 - 2*mc 383*mc 2303 - 2*mc 703*mc 2303 + 4*mc 383*mc 703*mc 2303) + 2 * KeccakfPermAir.extraction.inter_3080 c row := by
    simp only [KeccakfPermAir.extraction.inter_3082, KeccakfPermAir.extraction.inter_3081, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_3080 c row = (mc 384 + mc 704 + mc 2304 - 2*mc 384*mc 704 - 2*mc 384*mc 2304 - 2*mc 704*mc 2304 + 4*mc 384*mc 704*mc 2304) := by
    simp only [KeccakfPermAir.extraction.inter_3080, KeccakfPermAir.extraction.inter_3079, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_2452 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 385 705 2305 215 row) :
    mc 215 = (mc 385 + mc 705 + mc 2305 - 2*mc 385*mc 705 - 2*mc 385*mc 2305 - 2*mc 705*mc 2305 + 4*mc 385*mc 705*mc 2305) + 2*(mc 386 + mc 706 + mc 2306 - 2*mc 386*mc 706 - 2*mc 386*mc 2306 - 2*mc 706*mc 2306 + 4*mc 386*mc 706*mc 2306) + 4*(mc 387 + mc 707 + mc 2307 - 2*mc 387*mc 707 - 2*mc 387*mc 2307 - 2*mc 707*mc 2307 + 4*mc 387*mc 707*mc 2307) + 8*(mc 388 + mc 708 + mc 2308 - 2*mc 388*mc 708 - 2*mc 388*mc 2308 - 2*mc 708*mc 2308 + 4*mc 388*mc 708*mc 2308) + 16*(mc 389 + mc 709 + mc 2309 - 2*mc 389*mc 709 - 2*mc 389*mc 2309 - 2*mc 709*mc 2309 + 4*mc 389*mc 709*mc 2309) + 32*(mc 390 + mc 710 + mc 2310 - 2*mc 390*mc 710 - 2*mc 390*mc 2310 - 2*mc 710*mc 2310 + 4*mc 390*mc 710*mc 2310) + 64*(mc 391 + mc 711 + mc 2311 - 2*mc 391*mc 711 - 2*mc 391*mc 2311 - 2*mc 711*mc 2311 + 4*mc 391*mc 711*mc 2311) + 128*(mc 392 + mc 712 + mc 2312 - 2*mc 392*mc 712 - 2*mc 392*mc 2312 - 2*mc 712*mc 2312 + 4*mc 392*mc 712*mc 2312) + 256*(mc 393 + mc 713 + mc 2313 - 2*mc 393*mc 713 - 2*mc 393*mc 2313 - 2*mc 713*mc 2313 + 4*mc 393*mc 713*mc 2313) + 512*(mc 394 + mc 714 + mc 2314 - 2*mc 394*mc 714 - 2*mc 394*mc 2314 - 2*mc 714*mc 2314 + 4*mc 394*mc 714*mc 2314) + 1024*(mc 395 + mc 715 + mc 2315 - 2*mc 395*mc 715 - 2*mc 395*mc 2315 - 2*mc 715*mc 2315 + 4*mc 395*mc 715*mc 2315) + 2048*(mc 396 + mc 716 + mc 2316 - 2*mc 396*mc 716 - 2*mc 396*mc 2316 - 2*mc 716*mc 2316 + 4*mc 396*mc 716*mc 2316) + 4096*(mc 397 + mc 717 + mc 2317 - 2*mc 397*mc 717 - 2*mc 397*mc 2317 - 2*mc 717*mc 2317 + 4*mc 397*mc 717*mc 2317) + 8192*(mc 398 + mc 718 + mc 2318 - 2*mc 398*mc 718 - 2*mc 398*mc 2318 - 2*mc 718*mc 2318 + 4*mc 398*mc 718*mc 2318) + 16384*(mc 399 + mc 719 + mc 2319 - 2*mc 399*mc 719 - 2*mc 399*mc 2319 - 2*mc 719*mc 2319 + 4*mc 399*mc 719*mc 2319) + 32768*(mc 400 + mc 720 + mc 2320 - 2*mc 400*mc 720 - 2*mc 400*mc 2320 - 2*mc 720*mc 2320 + 4*mc 400*mc 720*mc 2320) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_2452, KeccakfPermAir.extraction.inter_3140, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_3139 c row = (mc 386 + mc 706 + mc 2306 - 2*mc 386*mc 706 - 2*mc 386*mc 2306 - 2*mc 706*mc 2306 + 4*mc 386*mc 706*mc 2306) + 2 * KeccakfPermAir.extraction.inter_3137 c row := by
    simp only [KeccakfPermAir.extraction.inter_3139, KeccakfPermAir.extraction.inter_3138, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_3137 c row = (mc 387 + mc 707 + mc 2307 - 2*mc 387*mc 707 - 2*mc 387*mc 2307 - 2*mc 707*mc 2307 + 4*mc 387*mc 707*mc 2307) + 2 * KeccakfPermAir.extraction.inter_3135 c row := by
    simp only [KeccakfPermAir.extraction.inter_3137, KeccakfPermAir.extraction.inter_3136, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_3135 c row = (mc 388 + mc 708 + mc 2308 - 2*mc 388*mc 708 - 2*mc 388*mc 2308 - 2*mc 708*mc 2308 + 4*mc 388*mc 708*mc 2308) + 2 * KeccakfPermAir.extraction.inter_3133 c row := by
    simp only [KeccakfPermAir.extraction.inter_3135, KeccakfPermAir.extraction.inter_3134, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_3133 c row = (mc 389 + mc 709 + mc 2309 - 2*mc 389*mc 709 - 2*mc 389*mc 2309 - 2*mc 709*mc 2309 + 4*mc 389*mc 709*mc 2309) + 2 * KeccakfPermAir.extraction.inter_3131 c row := by
    simp only [KeccakfPermAir.extraction.inter_3133, KeccakfPermAir.extraction.inter_3132, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_3131 c row = (mc 390 + mc 710 + mc 2310 - 2*mc 390*mc 710 - 2*mc 390*mc 2310 - 2*mc 710*mc 2310 + 4*mc 390*mc 710*mc 2310) + 2 * KeccakfPermAir.extraction.inter_3129 c row := by
    simp only [KeccakfPermAir.extraction.inter_3131, KeccakfPermAir.extraction.inter_3130, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_3129 c row = (mc 391 + mc 711 + mc 2311 - 2*mc 391*mc 711 - 2*mc 391*mc 2311 - 2*mc 711*mc 2311 + 4*mc 391*mc 711*mc 2311) + 2 * KeccakfPermAir.extraction.inter_3127 c row := by
    simp only [KeccakfPermAir.extraction.inter_3129, KeccakfPermAir.extraction.inter_3128, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_3127 c row = (mc 392 + mc 712 + mc 2312 - 2*mc 392*mc 712 - 2*mc 392*mc 2312 - 2*mc 712*mc 2312 + 4*mc 392*mc 712*mc 2312) + 2 * KeccakfPermAir.extraction.inter_3125 c row := by
    simp only [KeccakfPermAir.extraction.inter_3127, KeccakfPermAir.extraction.inter_3126, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_3125 c row = (mc 393 + mc 713 + mc 2313 - 2*mc 393*mc 713 - 2*mc 393*mc 2313 - 2*mc 713*mc 2313 + 4*mc 393*mc 713*mc 2313) + 2 * KeccakfPermAir.extraction.inter_3123 c row := by
    simp only [KeccakfPermAir.extraction.inter_3125, KeccakfPermAir.extraction.inter_3124, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_3123 c row = (mc 394 + mc 714 + mc 2314 - 2*mc 394*mc 714 - 2*mc 394*mc 2314 - 2*mc 714*mc 2314 + 4*mc 394*mc 714*mc 2314) + 2 * KeccakfPermAir.extraction.inter_3121 c row := by
    simp only [KeccakfPermAir.extraction.inter_3123, KeccakfPermAir.extraction.inter_3122, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_3121 c row = (mc 395 + mc 715 + mc 2315 - 2*mc 395*mc 715 - 2*mc 395*mc 2315 - 2*mc 715*mc 2315 + 4*mc 395*mc 715*mc 2315) + 2 * KeccakfPermAir.extraction.inter_3119 c row := by
    simp only [KeccakfPermAir.extraction.inter_3121, KeccakfPermAir.extraction.inter_3120, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_3119 c row = (mc 396 + mc 716 + mc 2316 - 2*mc 396*mc 716 - 2*mc 396*mc 2316 - 2*mc 716*mc 2316 + 4*mc 396*mc 716*mc 2316) + 2 * KeccakfPermAir.extraction.inter_3117 c row := by
    simp only [KeccakfPermAir.extraction.inter_3119, KeccakfPermAir.extraction.inter_3118, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_3117 c row = (mc 397 + mc 717 + mc 2317 - 2*mc 397*mc 717 - 2*mc 397*mc 2317 - 2*mc 717*mc 2317 + 4*mc 397*mc 717*mc 2317) + 2 * KeccakfPermAir.extraction.inter_3115 c row := by
    simp only [KeccakfPermAir.extraction.inter_3117, KeccakfPermAir.extraction.inter_3116, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_3115 c row = (mc 398 + mc 718 + mc 2318 - 2*mc 398*mc 718 - 2*mc 398*mc 2318 - 2*mc 718*mc 2318 + 4*mc 398*mc 718*mc 2318) + 2 * KeccakfPermAir.extraction.inter_3113 c row := by
    simp only [KeccakfPermAir.extraction.inter_3115, KeccakfPermAir.extraction.inter_3114, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_3113 c row = (mc 399 + mc 719 + mc 2319 - 2*mc 399*mc 719 - 2*mc 399*mc 2319 - 2*mc 719*mc 2319 + 4*mc 399*mc 719*mc 2319) + 2 * KeccakfPermAir.extraction.inter_3111 c row := by
    simp only [KeccakfPermAir.extraction.inter_3113, KeccakfPermAir.extraction.inter_3112, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_3111 c row = (mc 400 + mc 720 + mc 2320 - 2*mc 400*mc 720 - 2*mc 400*mc 2320 - 2*mc 720*mc 2320 + 4*mc 400*mc 720*mc 2320) := by
    simp only [KeccakfPermAir.extraction.inter_3111, KeccakfPermAir.extraction.inter_3110, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_2453 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 401 721 2321 216 row) :
    mc 216 = (mc 401 + mc 721 + mc 2321 - 2*mc 401*mc 721 - 2*mc 401*mc 2321 - 2*mc 721*mc 2321 + 4*mc 401*mc 721*mc 2321) + 2*(mc 402 + mc 722 + mc 2322 - 2*mc 402*mc 722 - 2*mc 402*mc 2322 - 2*mc 722*mc 2322 + 4*mc 402*mc 722*mc 2322) + 4*(mc 403 + mc 723 + mc 2323 - 2*mc 403*mc 723 - 2*mc 403*mc 2323 - 2*mc 723*mc 2323 + 4*mc 403*mc 723*mc 2323) + 8*(mc 404 + mc 724 + mc 2324 - 2*mc 404*mc 724 - 2*mc 404*mc 2324 - 2*mc 724*mc 2324 + 4*mc 404*mc 724*mc 2324) + 16*(mc 405 + mc 725 + mc 2325 - 2*mc 405*mc 725 - 2*mc 405*mc 2325 - 2*mc 725*mc 2325 + 4*mc 405*mc 725*mc 2325) + 32*(mc 406 + mc 726 + mc 2326 - 2*mc 406*mc 726 - 2*mc 406*mc 2326 - 2*mc 726*mc 2326 + 4*mc 406*mc 726*mc 2326) + 64*(mc 407 + mc 727 + mc 2327 - 2*mc 407*mc 727 - 2*mc 407*mc 2327 - 2*mc 727*mc 2327 + 4*mc 407*mc 727*mc 2327) + 128*(mc 408 + mc 728 + mc 2328 - 2*mc 408*mc 728 - 2*mc 408*mc 2328 - 2*mc 728*mc 2328 + 4*mc 408*mc 728*mc 2328) + 256*(mc 409 + mc 729 + mc 2329 - 2*mc 409*mc 729 - 2*mc 409*mc 2329 - 2*mc 729*mc 2329 + 4*mc 409*mc 729*mc 2329) + 512*(mc 410 + mc 730 + mc 2330 - 2*mc 410*mc 730 - 2*mc 410*mc 2330 - 2*mc 730*mc 2330 + 4*mc 410*mc 730*mc 2330) + 1024*(mc 411 + mc 731 + mc 2331 - 2*mc 411*mc 731 - 2*mc 411*mc 2331 - 2*mc 731*mc 2331 + 4*mc 411*mc 731*mc 2331) + 2048*(mc 412 + mc 732 + mc 2332 - 2*mc 412*mc 732 - 2*mc 412*mc 2332 - 2*mc 732*mc 2332 + 4*mc 412*mc 732*mc 2332) + 4096*(mc 413 + mc 733 + mc 2333 - 2*mc 413*mc 733 - 2*mc 413*mc 2333 - 2*mc 733*mc 2333 + 4*mc 413*mc 733*mc 2333) + 8192*(mc 414 + mc 734 + mc 2334 - 2*mc 414*mc 734 - 2*mc 414*mc 2334 - 2*mc 734*mc 2334 + 4*mc 414*mc 734*mc 2334) + 16384*(mc 415 + mc 735 + mc 2335 - 2*mc 415*mc 735 - 2*mc 415*mc 2335 - 2*mc 735*mc 2335 + 4*mc 415*mc 735*mc 2335) + 32768*(mc 416 + mc 736 + mc 2336 - 2*mc 416*mc 736 - 2*mc 416*mc 2336 - 2*mc 736*mc 2336 + 4*mc 416*mc 736*mc 2336) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_2453, KeccakfPermAir.extraction.inter_3171, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_3170 c row = (mc 402 + mc 722 + mc 2322 - 2*mc 402*mc 722 - 2*mc 402*mc 2322 - 2*mc 722*mc 2322 + 4*mc 402*mc 722*mc 2322) + 2 * KeccakfPermAir.extraction.inter_3168 c row := by
    simp only [KeccakfPermAir.extraction.inter_3170, KeccakfPermAir.extraction.inter_3169, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_3168 c row = (mc 403 + mc 723 + mc 2323 - 2*mc 403*mc 723 - 2*mc 403*mc 2323 - 2*mc 723*mc 2323 + 4*mc 403*mc 723*mc 2323) + 2 * KeccakfPermAir.extraction.inter_3166 c row := by
    simp only [KeccakfPermAir.extraction.inter_3168, KeccakfPermAir.extraction.inter_3167, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_3166 c row = (mc 404 + mc 724 + mc 2324 - 2*mc 404*mc 724 - 2*mc 404*mc 2324 - 2*mc 724*mc 2324 + 4*mc 404*mc 724*mc 2324) + 2 * KeccakfPermAir.extraction.inter_3164 c row := by
    simp only [KeccakfPermAir.extraction.inter_3166, KeccakfPermAir.extraction.inter_3165, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_3164 c row = (mc 405 + mc 725 + mc 2325 - 2*mc 405*mc 725 - 2*mc 405*mc 2325 - 2*mc 725*mc 2325 + 4*mc 405*mc 725*mc 2325) + 2 * KeccakfPermAir.extraction.inter_3162 c row := by
    simp only [KeccakfPermAir.extraction.inter_3164, KeccakfPermAir.extraction.inter_3163, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_3162 c row = (mc 406 + mc 726 + mc 2326 - 2*mc 406*mc 726 - 2*mc 406*mc 2326 - 2*mc 726*mc 2326 + 4*mc 406*mc 726*mc 2326) + 2 * KeccakfPermAir.extraction.inter_3160 c row := by
    simp only [KeccakfPermAir.extraction.inter_3162, KeccakfPermAir.extraction.inter_3161, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_3160 c row = (mc 407 + mc 727 + mc 2327 - 2*mc 407*mc 727 - 2*mc 407*mc 2327 - 2*mc 727*mc 2327 + 4*mc 407*mc 727*mc 2327) + 2 * KeccakfPermAir.extraction.inter_3158 c row := by
    simp only [KeccakfPermAir.extraction.inter_3160, KeccakfPermAir.extraction.inter_3159, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_3158 c row = (mc 408 + mc 728 + mc 2328 - 2*mc 408*mc 728 - 2*mc 408*mc 2328 - 2*mc 728*mc 2328 + 4*mc 408*mc 728*mc 2328) + 2 * KeccakfPermAir.extraction.inter_3156 c row := by
    simp only [KeccakfPermAir.extraction.inter_3158, KeccakfPermAir.extraction.inter_3157, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_3156 c row = (mc 409 + mc 729 + mc 2329 - 2*mc 409*mc 729 - 2*mc 409*mc 2329 - 2*mc 729*mc 2329 + 4*mc 409*mc 729*mc 2329) + 2 * KeccakfPermAir.extraction.inter_3154 c row := by
    simp only [KeccakfPermAir.extraction.inter_3156, KeccakfPermAir.extraction.inter_3155, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_3154 c row = (mc 410 + mc 730 + mc 2330 - 2*mc 410*mc 730 - 2*mc 410*mc 2330 - 2*mc 730*mc 2330 + 4*mc 410*mc 730*mc 2330) + 2 * KeccakfPermAir.extraction.inter_3152 c row := by
    simp only [KeccakfPermAir.extraction.inter_3154, KeccakfPermAir.extraction.inter_3153, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_3152 c row = (mc 411 + mc 731 + mc 2331 - 2*mc 411*mc 731 - 2*mc 411*mc 2331 - 2*mc 731*mc 2331 + 4*mc 411*mc 731*mc 2331) + 2 * KeccakfPermAir.extraction.inter_3150 c row := by
    simp only [KeccakfPermAir.extraction.inter_3152, KeccakfPermAir.extraction.inter_3151, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_3150 c row = (mc 412 + mc 732 + mc 2332 - 2*mc 412*mc 732 - 2*mc 412*mc 2332 - 2*mc 732*mc 2332 + 4*mc 412*mc 732*mc 2332) + 2 * KeccakfPermAir.extraction.inter_3148 c row := by
    simp only [KeccakfPermAir.extraction.inter_3150, KeccakfPermAir.extraction.inter_3149, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_3148 c row = (mc 413 + mc 733 + mc 2333 - 2*mc 413*mc 733 - 2*mc 413*mc 2333 - 2*mc 733*mc 2333 + 4*mc 413*mc 733*mc 2333) + 2 * KeccakfPermAir.extraction.inter_3146 c row := by
    simp only [KeccakfPermAir.extraction.inter_3148, KeccakfPermAir.extraction.inter_3147, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_3146 c row = (mc 414 + mc 734 + mc 2334 - 2*mc 414*mc 734 - 2*mc 414*mc 2334 - 2*mc 734*mc 2334 + 4*mc 414*mc 734*mc 2334) + 2 * KeccakfPermAir.extraction.inter_3144 c row := by
    simp only [KeccakfPermAir.extraction.inter_3146, KeccakfPermAir.extraction.inter_3145, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_3144 c row = (mc 415 + mc 735 + mc 2335 - 2*mc 415*mc 735 - 2*mc 415*mc 2335 - 2*mc 735*mc 2335 + 4*mc 415*mc 735*mc 2335) + 2 * KeccakfPermAir.extraction.inter_3142 c row := by
    simp only [KeccakfPermAir.extraction.inter_3144, KeccakfPermAir.extraction.inter_3143, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_3142 c row = (mc 416 + mc 736 + mc 2336 - 2*mc 416*mc 736 - 2*mc 416*mc 2336 - 2*mc 736*mc 2336 + 4*mc 416*mc 736*mc 2336) := by
    simp only [KeccakfPermAir.extraction.inter_3142, KeccakfPermAir.extraction.inter_3141, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_2518 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 417 737 2337 217 row) :
    mc 217 = (mc 417 + mc 737 + mc 2337 - 2*mc 417*mc 737 - 2*mc 417*mc 2337 - 2*mc 737*mc 2337 + 4*mc 417*mc 737*mc 2337) + 2*(mc 418 + mc 738 + mc 2338 - 2*mc 418*mc 738 - 2*mc 418*mc 2338 - 2*mc 738*mc 2338 + 4*mc 418*mc 738*mc 2338) + 4*(mc 419 + mc 739 + mc 2339 - 2*mc 419*mc 739 - 2*mc 419*mc 2339 - 2*mc 739*mc 2339 + 4*mc 419*mc 739*mc 2339) + 8*(mc 420 + mc 740 + mc 2340 - 2*mc 420*mc 740 - 2*mc 420*mc 2340 - 2*mc 740*mc 2340 + 4*mc 420*mc 740*mc 2340) + 16*(mc 421 + mc 741 + mc 2341 - 2*mc 421*mc 741 - 2*mc 421*mc 2341 - 2*mc 741*mc 2341 + 4*mc 421*mc 741*mc 2341) + 32*(mc 422 + mc 742 + mc 2342 - 2*mc 422*mc 742 - 2*mc 422*mc 2342 - 2*mc 742*mc 2342 + 4*mc 422*mc 742*mc 2342) + 64*(mc 423 + mc 743 + mc 2343 - 2*mc 423*mc 743 - 2*mc 423*mc 2343 - 2*mc 743*mc 2343 + 4*mc 423*mc 743*mc 2343) + 128*(mc 424 + mc 744 + mc 2344 - 2*mc 424*mc 744 - 2*mc 424*mc 2344 - 2*mc 744*mc 2344 + 4*mc 424*mc 744*mc 2344) + 256*(mc 425 + mc 745 + mc 2345 - 2*mc 425*mc 745 - 2*mc 425*mc 2345 - 2*mc 745*mc 2345 + 4*mc 425*mc 745*mc 2345) + 512*(mc 426 + mc 746 + mc 2346 - 2*mc 426*mc 746 - 2*mc 426*mc 2346 - 2*mc 746*mc 2346 + 4*mc 426*mc 746*mc 2346) + 1024*(mc 427 + mc 747 + mc 2347 - 2*mc 427*mc 747 - 2*mc 427*mc 2347 - 2*mc 747*mc 2347 + 4*mc 427*mc 747*mc 2347) + 2048*(mc 428 + mc 748 + mc 2348 - 2*mc 428*mc 748 - 2*mc 428*mc 2348 - 2*mc 748*mc 2348 + 4*mc 428*mc 748*mc 2348) + 4096*(mc 429 + mc 749 + mc 2349 - 2*mc 429*mc 749 - 2*mc 429*mc 2349 - 2*mc 749*mc 2349 + 4*mc 429*mc 749*mc 2349) + 8192*(mc 430 + mc 750 + mc 2350 - 2*mc 430*mc 750 - 2*mc 430*mc 2350 - 2*mc 750*mc 2350 + 4*mc 430*mc 750*mc 2350) + 16384*(mc 431 + mc 751 + mc 2351 - 2*mc 431*mc 751 - 2*mc 431*mc 2351 - 2*mc 751*mc 2351 + 4*mc 431*mc 751*mc 2351) + 32768*(mc 432 + mc 752 + mc 2352 - 2*mc 432*mc 752 - 2*mc 432*mc 2352 - 2*mc 752*mc 2352 + 4*mc 432*mc 752*mc 2352) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_2518, KeccakfPermAir.extraction.inter_3202, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_3201 c row = (mc 418 + mc 738 + mc 2338 - 2*mc 418*mc 738 - 2*mc 418*mc 2338 - 2*mc 738*mc 2338 + 4*mc 418*mc 738*mc 2338) + 2 * KeccakfPermAir.extraction.inter_3199 c row := by
    simp only [KeccakfPermAir.extraction.inter_3201, KeccakfPermAir.extraction.inter_3200, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_3199 c row = (mc 419 + mc 739 + mc 2339 - 2*mc 419*mc 739 - 2*mc 419*mc 2339 - 2*mc 739*mc 2339 + 4*mc 419*mc 739*mc 2339) + 2 * KeccakfPermAir.extraction.inter_3197 c row := by
    simp only [KeccakfPermAir.extraction.inter_3199, KeccakfPermAir.extraction.inter_3198, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_3197 c row = (mc 420 + mc 740 + mc 2340 - 2*mc 420*mc 740 - 2*mc 420*mc 2340 - 2*mc 740*mc 2340 + 4*mc 420*mc 740*mc 2340) + 2 * KeccakfPermAir.extraction.inter_3195 c row := by
    simp only [KeccakfPermAir.extraction.inter_3197, KeccakfPermAir.extraction.inter_3196, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_3195 c row = (mc 421 + mc 741 + mc 2341 - 2*mc 421*mc 741 - 2*mc 421*mc 2341 - 2*mc 741*mc 2341 + 4*mc 421*mc 741*mc 2341) + 2 * KeccakfPermAir.extraction.inter_3193 c row := by
    simp only [KeccakfPermAir.extraction.inter_3195, KeccakfPermAir.extraction.inter_3194, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_3193 c row = (mc 422 + mc 742 + mc 2342 - 2*mc 422*mc 742 - 2*mc 422*mc 2342 - 2*mc 742*mc 2342 + 4*mc 422*mc 742*mc 2342) + 2 * KeccakfPermAir.extraction.inter_3191 c row := by
    simp only [KeccakfPermAir.extraction.inter_3193, KeccakfPermAir.extraction.inter_3192, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_3191 c row = (mc 423 + mc 743 + mc 2343 - 2*mc 423*mc 743 - 2*mc 423*mc 2343 - 2*mc 743*mc 2343 + 4*mc 423*mc 743*mc 2343) + 2 * KeccakfPermAir.extraction.inter_3189 c row := by
    simp only [KeccakfPermAir.extraction.inter_3191, KeccakfPermAir.extraction.inter_3190, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_3189 c row = (mc 424 + mc 744 + mc 2344 - 2*mc 424*mc 744 - 2*mc 424*mc 2344 - 2*mc 744*mc 2344 + 4*mc 424*mc 744*mc 2344) + 2 * KeccakfPermAir.extraction.inter_3187 c row := by
    simp only [KeccakfPermAir.extraction.inter_3189, KeccakfPermAir.extraction.inter_3188, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_3187 c row = (mc 425 + mc 745 + mc 2345 - 2*mc 425*mc 745 - 2*mc 425*mc 2345 - 2*mc 745*mc 2345 + 4*mc 425*mc 745*mc 2345) + 2 * KeccakfPermAir.extraction.inter_3185 c row := by
    simp only [KeccakfPermAir.extraction.inter_3187, KeccakfPermAir.extraction.inter_3186, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_3185 c row = (mc 426 + mc 746 + mc 2346 - 2*mc 426*mc 746 - 2*mc 426*mc 2346 - 2*mc 746*mc 2346 + 4*mc 426*mc 746*mc 2346) + 2 * KeccakfPermAir.extraction.inter_3183 c row := by
    simp only [KeccakfPermAir.extraction.inter_3185, KeccakfPermAir.extraction.inter_3184, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_3183 c row = (mc 427 + mc 747 + mc 2347 - 2*mc 427*mc 747 - 2*mc 427*mc 2347 - 2*mc 747*mc 2347 + 4*mc 427*mc 747*mc 2347) + 2 * KeccakfPermAir.extraction.inter_3181 c row := by
    simp only [KeccakfPermAir.extraction.inter_3183, KeccakfPermAir.extraction.inter_3182, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_3181 c row = (mc 428 + mc 748 + mc 2348 - 2*mc 428*mc 748 - 2*mc 428*mc 2348 - 2*mc 748*mc 2348 + 4*mc 428*mc 748*mc 2348) + 2 * KeccakfPermAir.extraction.inter_3179 c row := by
    simp only [KeccakfPermAir.extraction.inter_3181, KeccakfPermAir.extraction.inter_3180, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_3179 c row = (mc 429 + mc 749 + mc 2349 - 2*mc 429*mc 749 - 2*mc 429*mc 2349 - 2*mc 749*mc 2349 + 4*mc 429*mc 749*mc 2349) + 2 * KeccakfPermAir.extraction.inter_3177 c row := by
    simp only [KeccakfPermAir.extraction.inter_3179, KeccakfPermAir.extraction.inter_3178, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_3177 c row = (mc 430 + mc 750 + mc 2350 - 2*mc 430*mc 750 - 2*mc 430*mc 2350 - 2*mc 750*mc 2350 + 4*mc 430*mc 750*mc 2350) + 2 * KeccakfPermAir.extraction.inter_3175 c row := by
    simp only [KeccakfPermAir.extraction.inter_3177, KeccakfPermAir.extraction.inter_3176, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_3175 c row = (mc 431 + mc 751 + mc 2351 - 2*mc 431*mc 751 - 2*mc 431*mc 2351 - 2*mc 751*mc 2351 + 4*mc 431*mc 751*mc 2351) + 2 * KeccakfPermAir.extraction.inter_3173 c row := by
    simp only [KeccakfPermAir.extraction.inter_3175, KeccakfPermAir.extraction.inter_3174, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_3173 c row = (mc 432 + mc 752 + mc 2352 - 2*mc 432*mc 752 - 2*mc 432*mc 2352 - 2*mc 752*mc 2352 + 4*mc 432*mc 752*mc 2352) := by
    simp only [KeccakfPermAir.extraction.inter_3173, KeccakfPermAir.extraction.inter_3172, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_2519 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 433 753 2353 218 row) :
    mc 218 = (mc 433 + mc 753 + mc 2353 - 2*mc 433*mc 753 - 2*mc 433*mc 2353 - 2*mc 753*mc 2353 + 4*mc 433*mc 753*mc 2353) + 2*(mc 434 + mc 754 + mc 2354 - 2*mc 434*mc 754 - 2*mc 434*mc 2354 - 2*mc 754*mc 2354 + 4*mc 434*mc 754*mc 2354) + 4*(mc 435 + mc 755 + mc 2355 - 2*mc 435*mc 755 - 2*mc 435*mc 2355 - 2*mc 755*mc 2355 + 4*mc 435*mc 755*mc 2355) + 8*(mc 436 + mc 756 + mc 2356 - 2*mc 436*mc 756 - 2*mc 436*mc 2356 - 2*mc 756*mc 2356 + 4*mc 436*mc 756*mc 2356) + 16*(mc 437 + mc 757 + mc 2357 - 2*mc 437*mc 757 - 2*mc 437*mc 2357 - 2*mc 757*mc 2357 + 4*mc 437*mc 757*mc 2357) + 32*(mc 438 + mc 758 + mc 2358 - 2*mc 438*mc 758 - 2*mc 438*mc 2358 - 2*mc 758*mc 2358 + 4*mc 438*mc 758*mc 2358) + 64*(mc 439 + mc 759 + mc 2359 - 2*mc 439*mc 759 - 2*mc 439*mc 2359 - 2*mc 759*mc 2359 + 4*mc 439*mc 759*mc 2359) + 128*(mc 440 + mc 760 + mc 2360 - 2*mc 440*mc 760 - 2*mc 440*mc 2360 - 2*mc 760*mc 2360 + 4*mc 440*mc 760*mc 2360) + 256*(mc 441 + mc 761 + mc 2361 - 2*mc 441*mc 761 - 2*mc 441*mc 2361 - 2*mc 761*mc 2361 + 4*mc 441*mc 761*mc 2361) + 512*(mc 442 + mc 762 + mc 2362 - 2*mc 442*mc 762 - 2*mc 442*mc 2362 - 2*mc 762*mc 2362 + 4*mc 442*mc 762*mc 2362) + 1024*(mc 443 + mc 763 + mc 2363 - 2*mc 443*mc 763 - 2*mc 443*mc 2363 - 2*mc 763*mc 2363 + 4*mc 443*mc 763*mc 2363) + 2048*(mc 444 + mc 764 + mc 2364 - 2*mc 444*mc 764 - 2*mc 444*mc 2364 - 2*mc 764*mc 2364 + 4*mc 444*mc 764*mc 2364) + 4096*(mc 445 + mc 765 + mc 2365 - 2*mc 445*mc 765 - 2*mc 445*mc 2365 - 2*mc 765*mc 2365 + 4*mc 445*mc 765*mc 2365) + 8192*(mc 446 + mc 766 + mc 2366 - 2*mc 446*mc 766 - 2*mc 446*mc 2366 - 2*mc 766*mc 2366 + 4*mc 446*mc 766*mc 2366) + 16384*(mc 447 + mc 767 + mc 2367 - 2*mc 447*mc 767 - 2*mc 447*mc 2367 - 2*mc 767*mc 2367 + 4*mc 447*mc 767*mc 2367) + 32768*(mc 448 + mc 768 + mc 2368 - 2*mc 448*mc 768 - 2*mc 448*mc 2368 - 2*mc 768*mc 2368 + 4*mc 448*mc 768*mc 2368) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_2519, KeccakfPermAir.extraction.inter_3233, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_3232 c row = (mc 434 + mc 754 + mc 2354 - 2*mc 434*mc 754 - 2*mc 434*mc 2354 - 2*mc 754*mc 2354 + 4*mc 434*mc 754*mc 2354) + 2 * KeccakfPermAir.extraction.inter_3230 c row := by
    simp only [KeccakfPermAir.extraction.inter_3232, KeccakfPermAir.extraction.inter_3231, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_3230 c row = (mc 435 + mc 755 + mc 2355 - 2*mc 435*mc 755 - 2*mc 435*mc 2355 - 2*mc 755*mc 2355 + 4*mc 435*mc 755*mc 2355) + 2 * KeccakfPermAir.extraction.inter_3228 c row := by
    simp only [KeccakfPermAir.extraction.inter_3230, KeccakfPermAir.extraction.inter_3229, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_3228 c row = (mc 436 + mc 756 + mc 2356 - 2*mc 436*mc 756 - 2*mc 436*mc 2356 - 2*mc 756*mc 2356 + 4*mc 436*mc 756*mc 2356) + 2 * KeccakfPermAir.extraction.inter_3226 c row := by
    simp only [KeccakfPermAir.extraction.inter_3228, KeccakfPermAir.extraction.inter_3227, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_3226 c row = (mc 437 + mc 757 + mc 2357 - 2*mc 437*mc 757 - 2*mc 437*mc 2357 - 2*mc 757*mc 2357 + 4*mc 437*mc 757*mc 2357) + 2 * KeccakfPermAir.extraction.inter_3224 c row := by
    simp only [KeccakfPermAir.extraction.inter_3226, KeccakfPermAir.extraction.inter_3225, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_3224 c row = (mc 438 + mc 758 + mc 2358 - 2*mc 438*mc 758 - 2*mc 438*mc 2358 - 2*mc 758*mc 2358 + 4*mc 438*mc 758*mc 2358) + 2 * KeccakfPermAir.extraction.inter_3222 c row := by
    simp only [KeccakfPermAir.extraction.inter_3224, KeccakfPermAir.extraction.inter_3223, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_3222 c row = (mc 439 + mc 759 + mc 2359 - 2*mc 439*mc 759 - 2*mc 439*mc 2359 - 2*mc 759*mc 2359 + 4*mc 439*mc 759*mc 2359) + 2 * KeccakfPermAir.extraction.inter_3220 c row := by
    simp only [KeccakfPermAir.extraction.inter_3222, KeccakfPermAir.extraction.inter_3221, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_3220 c row = (mc 440 + mc 760 + mc 2360 - 2*mc 440*mc 760 - 2*mc 440*mc 2360 - 2*mc 760*mc 2360 + 4*mc 440*mc 760*mc 2360) + 2 * KeccakfPermAir.extraction.inter_3218 c row := by
    simp only [KeccakfPermAir.extraction.inter_3220, KeccakfPermAir.extraction.inter_3219, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_3218 c row = (mc 441 + mc 761 + mc 2361 - 2*mc 441*mc 761 - 2*mc 441*mc 2361 - 2*mc 761*mc 2361 + 4*mc 441*mc 761*mc 2361) + 2 * KeccakfPermAir.extraction.inter_3216 c row := by
    simp only [KeccakfPermAir.extraction.inter_3218, KeccakfPermAir.extraction.inter_3217, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_3216 c row = (mc 442 + mc 762 + mc 2362 - 2*mc 442*mc 762 - 2*mc 442*mc 2362 - 2*mc 762*mc 2362 + 4*mc 442*mc 762*mc 2362) + 2 * KeccakfPermAir.extraction.inter_3214 c row := by
    simp only [KeccakfPermAir.extraction.inter_3216, KeccakfPermAir.extraction.inter_3215, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_3214 c row = (mc 443 + mc 763 + mc 2363 - 2*mc 443*mc 763 - 2*mc 443*mc 2363 - 2*mc 763*mc 2363 + 4*mc 443*mc 763*mc 2363) + 2 * KeccakfPermAir.extraction.inter_3212 c row := by
    simp only [KeccakfPermAir.extraction.inter_3214, KeccakfPermAir.extraction.inter_3213, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_3212 c row = (mc 444 + mc 764 + mc 2364 - 2*mc 444*mc 764 - 2*mc 444*mc 2364 - 2*mc 764*mc 2364 + 4*mc 444*mc 764*mc 2364) + 2 * KeccakfPermAir.extraction.inter_3210 c row := by
    simp only [KeccakfPermAir.extraction.inter_3212, KeccakfPermAir.extraction.inter_3211, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_3210 c row = (mc 445 + mc 765 + mc 2365 - 2*mc 445*mc 765 - 2*mc 445*mc 2365 - 2*mc 765*mc 2365 + 4*mc 445*mc 765*mc 2365) + 2 * KeccakfPermAir.extraction.inter_3208 c row := by
    simp only [KeccakfPermAir.extraction.inter_3210, KeccakfPermAir.extraction.inter_3209, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_3208 c row = (mc 446 + mc 766 + mc 2366 - 2*mc 446*mc 766 - 2*mc 446*mc 2366 - 2*mc 766*mc 2366 + 4*mc 446*mc 766*mc 2366) + 2 * KeccakfPermAir.extraction.inter_3206 c row := by
    simp only [KeccakfPermAir.extraction.inter_3208, KeccakfPermAir.extraction.inter_3207, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_3206 c row = (mc 447 + mc 767 + mc 2367 - 2*mc 447*mc 767 - 2*mc 447*mc 2367 - 2*mc 767*mc 2367 + 4*mc 447*mc 767*mc 2367) + 2 * KeccakfPermAir.extraction.inter_3204 c row := by
    simp only [KeccakfPermAir.extraction.inter_3206, KeccakfPermAir.extraction.inter_3205, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_3204 c row = (mc 448 + mc 768 + mc 2368 - 2*mc 448*mc 768 - 2*mc 448*mc 2368 - 2*mc 768*mc 2368 + 4*mc 448*mc 768*mc 2368) := by
    simp only [KeccakfPermAir.extraction.inter_3204, KeccakfPermAir.extraction.inter_3203, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_2520 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 449 769 2369 219 row) :
    mc 219 = (mc 449 + mc 769 + mc 2369 - 2*mc 449*mc 769 - 2*mc 449*mc 2369 - 2*mc 769*mc 2369 + 4*mc 449*mc 769*mc 2369) + 2*(mc 450 + mc 770 + mc 2370 - 2*mc 450*mc 770 - 2*mc 450*mc 2370 - 2*mc 770*mc 2370 + 4*mc 450*mc 770*mc 2370) + 4*(mc 451 + mc 771 + mc 2371 - 2*mc 451*mc 771 - 2*mc 451*mc 2371 - 2*mc 771*mc 2371 + 4*mc 451*mc 771*mc 2371) + 8*(mc 452 + mc 772 + mc 2372 - 2*mc 452*mc 772 - 2*mc 452*mc 2372 - 2*mc 772*mc 2372 + 4*mc 452*mc 772*mc 2372) + 16*(mc 453 + mc 773 + mc 2373 - 2*mc 453*mc 773 - 2*mc 453*mc 2373 - 2*mc 773*mc 2373 + 4*mc 453*mc 773*mc 2373) + 32*(mc 454 + mc 774 + mc 2374 - 2*mc 454*mc 774 - 2*mc 454*mc 2374 - 2*mc 774*mc 2374 + 4*mc 454*mc 774*mc 2374) + 64*(mc 455 + mc 775 + mc 2375 - 2*mc 455*mc 775 - 2*mc 455*mc 2375 - 2*mc 775*mc 2375 + 4*mc 455*mc 775*mc 2375) + 128*(mc 456 + mc 776 + mc 2376 - 2*mc 456*mc 776 - 2*mc 456*mc 2376 - 2*mc 776*mc 2376 + 4*mc 456*mc 776*mc 2376) + 256*(mc 457 + mc 777 + mc 2377 - 2*mc 457*mc 777 - 2*mc 457*mc 2377 - 2*mc 777*mc 2377 + 4*mc 457*mc 777*mc 2377) + 512*(mc 458 + mc 778 + mc 2378 - 2*mc 458*mc 778 - 2*mc 458*mc 2378 - 2*mc 778*mc 2378 + 4*mc 458*mc 778*mc 2378) + 1024*(mc 459 + mc 779 + mc 2379 - 2*mc 459*mc 779 - 2*mc 459*mc 2379 - 2*mc 779*mc 2379 + 4*mc 459*mc 779*mc 2379) + 2048*(mc 460 + mc 780 + mc 2380 - 2*mc 460*mc 780 - 2*mc 460*mc 2380 - 2*mc 780*mc 2380 + 4*mc 460*mc 780*mc 2380) + 4096*(mc 461 + mc 781 + mc 2381 - 2*mc 461*mc 781 - 2*mc 461*mc 2381 - 2*mc 781*mc 2381 + 4*mc 461*mc 781*mc 2381) + 8192*(mc 462 + mc 782 + mc 2382 - 2*mc 462*mc 782 - 2*mc 462*mc 2382 - 2*mc 782*mc 2382 + 4*mc 462*mc 782*mc 2382) + 16384*(mc 463 + mc 783 + mc 2383 - 2*mc 463*mc 783 - 2*mc 463*mc 2383 - 2*mc 783*mc 2383 + 4*mc 463*mc 783*mc 2383) + 32768*(mc 464 + mc 784 + mc 2384 - 2*mc 464*mc 784 - 2*mc 464*mc 2384 - 2*mc 784*mc 2384 + 4*mc 464*mc 784*mc 2384) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_2520, KeccakfPermAir.extraction.inter_3264, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_3263 c row = (mc 450 + mc 770 + mc 2370 - 2*mc 450*mc 770 - 2*mc 450*mc 2370 - 2*mc 770*mc 2370 + 4*mc 450*mc 770*mc 2370) + 2 * KeccakfPermAir.extraction.inter_3261 c row := by
    simp only [KeccakfPermAir.extraction.inter_3263, KeccakfPermAir.extraction.inter_3262, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_3261 c row = (mc 451 + mc 771 + mc 2371 - 2*mc 451*mc 771 - 2*mc 451*mc 2371 - 2*mc 771*mc 2371 + 4*mc 451*mc 771*mc 2371) + 2 * KeccakfPermAir.extraction.inter_3259 c row := by
    simp only [KeccakfPermAir.extraction.inter_3261, KeccakfPermAir.extraction.inter_3260, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_3259 c row = (mc 452 + mc 772 + mc 2372 - 2*mc 452*mc 772 - 2*mc 452*mc 2372 - 2*mc 772*mc 2372 + 4*mc 452*mc 772*mc 2372) + 2 * KeccakfPermAir.extraction.inter_3257 c row := by
    simp only [KeccakfPermAir.extraction.inter_3259, KeccakfPermAir.extraction.inter_3258, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_3257 c row = (mc 453 + mc 773 + mc 2373 - 2*mc 453*mc 773 - 2*mc 453*mc 2373 - 2*mc 773*mc 2373 + 4*mc 453*mc 773*mc 2373) + 2 * KeccakfPermAir.extraction.inter_3255 c row := by
    simp only [KeccakfPermAir.extraction.inter_3257, KeccakfPermAir.extraction.inter_3256, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_3255 c row = (mc 454 + mc 774 + mc 2374 - 2*mc 454*mc 774 - 2*mc 454*mc 2374 - 2*mc 774*mc 2374 + 4*mc 454*mc 774*mc 2374) + 2 * KeccakfPermAir.extraction.inter_3253 c row := by
    simp only [KeccakfPermAir.extraction.inter_3255, KeccakfPermAir.extraction.inter_3254, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_3253 c row = (mc 455 + mc 775 + mc 2375 - 2*mc 455*mc 775 - 2*mc 455*mc 2375 - 2*mc 775*mc 2375 + 4*mc 455*mc 775*mc 2375) + 2 * KeccakfPermAir.extraction.inter_3251 c row := by
    simp only [KeccakfPermAir.extraction.inter_3253, KeccakfPermAir.extraction.inter_3252, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_3251 c row = (mc 456 + mc 776 + mc 2376 - 2*mc 456*mc 776 - 2*mc 456*mc 2376 - 2*mc 776*mc 2376 + 4*mc 456*mc 776*mc 2376) + 2 * KeccakfPermAir.extraction.inter_3249 c row := by
    simp only [KeccakfPermAir.extraction.inter_3251, KeccakfPermAir.extraction.inter_3250, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_3249 c row = (mc 457 + mc 777 + mc 2377 - 2*mc 457*mc 777 - 2*mc 457*mc 2377 - 2*mc 777*mc 2377 + 4*mc 457*mc 777*mc 2377) + 2 * KeccakfPermAir.extraction.inter_3247 c row := by
    simp only [KeccakfPermAir.extraction.inter_3249, KeccakfPermAir.extraction.inter_3248, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_3247 c row = (mc 458 + mc 778 + mc 2378 - 2*mc 458*mc 778 - 2*mc 458*mc 2378 - 2*mc 778*mc 2378 + 4*mc 458*mc 778*mc 2378) + 2 * KeccakfPermAir.extraction.inter_3245 c row := by
    simp only [KeccakfPermAir.extraction.inter_3247, KeccakfPermAir.extraction.inter_3246, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_3245 c row = (mc 459 + mc 779 + mc 2379 - 2*mc 459*mc 779 - 2*mc 459*mc 2379 - 2*mc 779*mc 2379 + 4*mc 459*mc 779*mc 2379) + 2 * KeccakfPermAir.extraction.inter_3243 c row := by
    simp only [KeccakfPermAir.extraction.inter_3245, KeccakfPermAir.extraction.inter_3244, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_3243 c row = (mc 460 + mc 780 + mc 2380 - 2*mc 460*mc 780 - 2*mc 460*mc 2380 - 2*mc 780*mc 2380 + 4*mc 460*mc 780*mc 2380) + 2 * KeccakfPermAir.extraction.inter_3241 c row := by
    simp only [KeccakfPermAir.extraction.inter_3243, KeccakfPermAir.extraction.inter_3242, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_3241 c row = (mc 461 + mc 781 + mc 2381 - 2*mc 461*mc 781 - 2*mc 461*mc 2381 - 2*mc 781*mc 2381 + 4*mc 461*mc 781*mc 2381) + 2 * KeccakfPermAir.extraction.inter_3239 c row := by
    simp only [KeccakfPermAir.extraction.inter_3241, KeccakfPermAir.extraction.inter_3240, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_3239 c row = (mc 462 + mc 782 + mc 2382 - 2*mc 462*mc 782 - 2*mc 462*mc 2382 - 2*mc 782*mc 2382 + 4*mc 462*mc 782*mc 2382) + 2 * KeccakfPermAir.extraction.inter_3237 c row := by
    simp only [KeccakfPermAir.extraction.inter_3239, KeccakfPermAir.extraction.inter_3238, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_3237 c row = (mc 463 + mc 783 + mc 2383 - 2*mc 463*mc 783 - 2*mc 463*mc 2383 - 2*mc 783*mc 2383 + 4*mc 463*mc 783*mc 2383) + 2 * KeccakfPermAir.extraction.inter_3235 c row := by
    simp only [KeccakfPermAir.extraction.inter_3237, KeccakfPermAir.extraction.inter_3236, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_3235 c row = (mc 464 + mc 784 + mc 2384 - 2*mc 464*mc 784 - 2*mc 464*mc 2384 - 2*mc 784*mc 2384 + 4*mc 464*mc 784*mc 2384) := by
    simp only [KeccakfPermAir.extraction.inter_3235, KeccakfPermAir.extraction.inter_3234, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_2521 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 465 785 2385 220 row) :
    mc 220 = (mc 465 + mc 785 + mc 2385 - 2*mc 465*mc 785 - 2*mc 465*mc 2385 - 2*mc 785*mc 2385 + 4*mc 465*mc 785*mc 2385) + 2*(mc 466 + mc 786 + mc 2386 - 2*mc 466*mc 786 - 2*mc 466*mc 2386 - 2*mc 786*mc 2386 + 4*mc 466*mc 786*mc 2386) + 4*(mc 467 + mc 787 + mc 2387 - 2*mc 467*mc 787 - 2*mc 467*mc 2387 - 2*mc 787*mc 2387 + 4*mc 467*mc 787*mc 2387) + 8*(mc 468 + mc 788 + mc 2388 - 2*mc 468*mc 788 - 2*mc 468*mc 2388 - 2*mc 788*mc 2388 + 4*mc 468*mc 788*mc 2388) + 16*(mc 469 + mc 789 + mc 2389 - 2*mc 469*mc 789 - 2*mc 469*mc 2389 - 2*mc 789*mc 2389 + 4*mc 469*mc 789*mc 2389) + 32*(mc 470 + mc 790 + mc 2390 - 2*mc 470*mc 790 - 2*mc 470*mc 2390 - 2*mc 790*mc 2390 + 4*mc 470*mc 790*mc 2390) + 64*(mc 471 + mc 791 + mc 2391 - 2*mc 471*mc 791 - 2*mc 471*mc 2391 - 2*mc 791*mc 2391 + 4*mc 471*mc 791*mc 2391) + 128*(mc 472 + mc 792 + mc 2392 - 2*mc 472*mc 792 - 2*mc 472*mc 2392 - 2*mc 792*mc 2392 + 4*mc 472*mc 792*mc 2392) + 256*(mc 473 + mc 793 + mc 2393 - 2*mc 473*mc 793 - 2*mc 473*mc 2393 - 2*mc 793*mc 2393 + 4*mc 473*mc 793*mc 2393) + 512*(mc 474 + mc 794 + mc 2394 - 2*mc 474*mc 794 - 2*mc 474*mc 2394 - 2*mc 794*mc 2394 + 4*mc 474*mc 794*mc 2394) + 1024*(mc 475 + mc 795 + mc 2395 - 2*mc 475*mc 795 - 2*mc 475*mc 2395 - 2*mc 795*mc 2395 + 4*mc 475*mc 795*mc 2395) + 2048*(mc 476 + mc 796 + mc 2396 - 2*mc 476*mc 796 - 2*mc 476*mc 2396 - 2*mc 796*mc 2396 + 4*mc 476*mc 796*mc 2396) + 4096*(mc 477 + mc 797 + mc 2397 - 2*mc 477*mc 797 - 2*mc 477*mc 2397 - 2*mc 797*mc 2397 + 4*mc 477*mc 797*mc 2397) + 8192*(mc 478 + mc 798 + mc 2398 - 2*mc 478*mc 798 - 2*mc 478*mc 2398 - 2*mc 798*mc 2398 + 4*mc 478*mc 798*mc 2398) + 16384*(mc 479 + mc 799 + mc 2399 - 2*mc 479*mc 799 - 2*mc 479*mc 2399 - 2*mc 799*mc 2399 + 4*mc 479*mc 799*mc 2399) + 32768*(mc 480 + mc 800 + mc 2400 - 2*mc 480*mc 800 - 2*mc 480*mc 2400 - 2*mc 800*mc 2400 + 4*mc 480*mc 800*mc 2400) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_2521, KeccakfPermAir.extraction.inter_3295, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_3294 c row = (mc 466 + mc 786 + mc 2386 - 2*mc 466*mc 786 - 2*mc 466*mc 2386 - 2*mc 786*mc 2386 + 4*mc 466*mc 786*mc 2386) + 2 * KeccakfPermAir.extraction.inter_3292 c row := by
    simp only [KeccakfPermAir.extraction.inter_3294, KeccakfPermAir.extraction.inter_3293, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_3292 c row = (mc 467 + mc 787 + mc 2387 - 2*mc 467*mc 787 - 2*mc 467*mc 2387 - 2*mc 787*mc 2387 + 4*mc 467*mc 787*mc 2387) + 2 * KeccakfPermAir.extraction.inter_3290 c row := by
    simp only [KeccakfPermAir.extraction.inter_3292, KeccakfPermAir.extraction.inter_3291, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_3290 c row = (mc 468 + mc 788 + mc 2388 - 2*mc 468*mc 788 - 2*mc 468*mc 2388 - 2*mc 788*mc 2388 + 4*mc 468*mc 788*mc 2388) + 2 * KeccakfPermAir.extraction.inter_3288 c row := by
    simp only [KeccakfPermAir.extraction.inter_3290, KeccakfPermAir.extraction.inter_3289, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_3288 c row = (mc 469 + mc 789 + mc 2389 - 2*mc 469*mc 789 - 2*mc 469*mc 2389 - 2*mc 789*mc 2389 + 4*mc 469*mc 789*mc 2389) + 2 * KeccakfPermAir.extraction.inter_3286 c row := by
    simp only [KeccakfPermAir.extraction.inter_3288, KeccakfPermAir.extraction.inter_3287, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_3286 c row = (mc 470 + mc 790 + mc 2390 - 2*mc 470*mc 790 - 2*mc 470*mc 2390 - 2*mc 790*mc 2390 + 4*mc 470*mc 790*mc 2390) + 2 * KeccakfPermAir.extraction.inter_3284 c row := by
    simp only [KeccakfPermAir.extraction.inter_3286, KeccakfPermAir.extraction.inter_3285, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_3284 c row = (mc 471 + mc 791 + mc 2391 - 2*mc 471*mc 791 - 2*mc 471*mc 2391 - 2*mc 791*mc 2391 + 4*mc 471*mc 791*mc 2391) + 2 * KeccakfPermAir.extraction.inter_3282 c row := by
    simp only [KeccakfPermAir.extraction.inter_3284, KeccakfPermAir.extraction.inter_3283, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_3282 c row = (mc 472 + mc 792 + mc 2392 - 2*mc 472*mc 792 - 2*mc 472*mc 2392 - 2*mc 792*mc 2392 + 4*mc 472*mc 792*mc 2392) + 2 * KeccakfPermAir.extraction.inter_3280 c row := by
    simp only [KeccakfPermAir.extraction.inter_3282, KeccakfPermAir.extraction.inter_3281, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_3280 c row = (mc 473 + mc 793 + mc 2393 - 2*mc 473*mc 793 - 2*mc 473*mc 2393 - 2*mc 793*mc 2393 + 4*mc 473*mc 793*mc 2393) + 2 * KeccakfPermAir.extraction.inter_3278 c row := by
    simp only [KeccakfPermAir.extraction.inter_3280, KeccakfPermAir.extraction.inter_3279, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_3278 c row = (mc 474 + mc 794 + mc 2394 - 2*mc 474*mc 794 - 2*mc 474*mc 2394 - 2*mc 794*mc 2394 + 4*mc 474*mc 794*mc 2394) + 2 * KeccakfPermAir.extraction.inter_3276 c row := by
    simp only [KeccakfPermAir.extraction.inter_3278, KeccakfPermAir.extraction.inter_3277, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_3276 c row = (mc 475 + mc 795 + mc 2395 - 2*mc 475*mc 795 - 2*mc 475*mc 2395 - 2*mc 795*mc 2395 + 4*mc 475*mc 795*mc 2395) + 2 * KeccakfPermAir.extraction.inter_3274 c row := by
    simp only [KeccakfPermAir.extraction.inter_3276, KeccakfPermAir.extraction.inter_3275, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_3274 c row = (mc 476 + mc 796 + mc 2396 - 2*mc 476*mc 796 - 2*mc 476*mc 2396 - 2*mc 796*mc 2396 + 4*mc 476*mc 796*mc 2396) + 2 * KeccakfPermAir.extraction.inter_3272 c row := by
    simp only [KeccakfPermAir.extraction.inter_3274, KeccakfPermAir.extraction.inter_3273, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_3272 c row = (mc 477 + mc 797 + mc 2397 - 2*mc 477*mc 797 - 2*mc 477*mc 2397 - 2*mc 797*mc 2397 + 4*mc 477*mc 797*mc 2397) + 2 * KeccakfPermAir.extraction.inter_3270 c row := by
    simp only [KeccakfPermAir.extraction.inter_3272, KeccakfPermAir.extraction.inter_3271, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_3270 c row = (mc 478 + mc 798 + mc 2398 - 2*mc 478*mc 798 - 2*mc 478*mc 2398 - 2*mc 798*mc 2398 + 4*mc 478*mc 798*mc 2398) + 2 * KeccakfPermAir.extraction.inter_3268 c row := by
    simp only [KeccakfPermAir.extraction.inter_3270, KeccakfPermAir.extraction.inter_3269, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_3268 c row = (mc 479 + mc 799 + mc 2399 - 2*mc 479*mc 799 - 2*mc 479*mc 2399 - 2*mc 799*mc 2399 + 4*mc 479*mc 799*mc 2399) + 2 * KeccakfPermAir.extraction.inter_3266 c row := by
    simp only [KeccakfPermAir.extraction.inter_3268, KeccakfPermAir.extraction.inter_3267, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_3266 c row = (mc 480 + mc 800 + mc 2400 - 2*mc 480*mc 800 - 2*mc 480*mc 2400 - 2*mc 800*mc 2400 + 4*mc 480*mc 800*mc 2400) := by
    simp only [KeccakfPermAir.extraction.inter_3266, KeccakfPermAir.extraction.inter_3265, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_2586 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 481 801 2401 221 row) :
    mc 221 = (mc 481 + mc 801 + mc 2401 - 2*mc 481*mc 801 - 2*mc 481*mc 2401 - 2*mc 801*mc 2401 + 4*mc 481*mc 801*mc 2401) + 2*(mc 482 + mc 802 + mc 2402 - 2*mc 482*mc 802 - 2*mc 482*mc 2402 - 2*mc 802*mc 2402 + 4*mc 482*mc 802*mc 2402) + 4*(mc 483 + mc 803 + mc 2403 - 2*mc 483*mc 803 - 2*mc 483*mc 2403 - 2*mc 803*mc 2403 + 4*mc 483*mc 803*mc 2403) + 8*(mc 484 + mc 804 + mc 2404 - 2*mc 484*mc 804 - 2*mc 484*mc 2404 - 2*mc 804*mc 2404 + 4*mc 484*mc 804*mc 2404) + 16*(mc 485 + mc 805 + mc 2405 - 2*mc 485*mc 805 - 2*mc 485*mc 2405 - 2*mc 805*mc 2405 + 4*mc 485*mc 805*mc 2405) + 32*(mc 486 + mc 806 + mc 2406 - 2*mc 486*mc 806 - 2*mc 486*mc 2406 - 2*mc 806*mc 2406 + 4*mc 486*mc 806*mc 2406) + 64*(mc 487 + mc 807 + mc 2407 - 2*mc 487*mc 807 - 2*mc 487*mc 2407 - 2*mc 807*mc 2407 + 4*mc 487*mc 807*mc 2407) + 128*(mc 488 + mc 808 + mc 2408 - 2*mc 488*mc 808 - 2*mc 488*mc 2408 - 2*mc 808*mc 2408 + 4*mc 488*mc 808*mc 2408) + 256*(mc 489 + mc 809 + mc 2409 - 2*mc 489*mc 809 - 2*mc 489*mc 2409 - 2*mc 809*mc 2409 + 4*mc 489*mc 809*mc 2409) + 512*(mc 490 + mc 810 + mc 2410 - 2*mc 490*mc 810 - 2*mc 490*mc 2410 - 2*mc 810*mc 2410 + 4*mc 490*mc 810*mc 2410) + 1024*(mc 491 + mc 811 + mc 2411 - 2*mc 491*mc 811 - 2*mc 491*mc 2411 - 2*mc 811*mc 2411 + 4*mc 491*mc 811*mc 2411) + 2048*(mc 492 + mc 812 + mc 2412 - 2*mc 492*mc 812 - 2*mc 492*mc 2412 - 2*mc 812*mc 2412 + 4*mc 492*mc 812*mc 2412) + 4096*(mc 493 + mc 813 + mc 2413 - 2*mc 493*mc 813 - 2*mc 493*mc 2413 - 2*mc 813*mc 2413 + 4*mc 493*mc 813*mc 2413) + 8192*(mc 494 + mc 814 + mc 2414 - 2*mc 494*mc 814 - 2*mc 494*mc 2414 - 2*mc 814*mc 2414 + 4*mc 494*mc 814*mc 2414) + 16384*(mc 495 + mc 815 + mc 2415 - 2*mc 495*mc 815 - 2*mc 495*mc 2415 - 2*mc 815*mc 2415 + 4*mc 495*mc 815*mc 2415) + 32768*(mc 496 + mc 816 + mc 2416 - 2*mc 496*mc 816 - 2*mc 496*mc 2416 - 2*mc 816*mc 2416 + 4*mc 496*mc 816*mc 2416) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_2586, KeccakfPermAir.extraction.inter_3326, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_3325 c row = (mc 482 + mc 802 + mc 2402 - 2*mc 482*mc 802 - 2*mc 482*mc 2402 - 2*mc 802*mc 2402 + 4*mc 482*mc 802*mc 2402) + 2 * KeccakfPermAir.extraction.inter_3323 c row := by
    simp only [KeccakfPermAir.extraction.inter_3325, KeccakfPermAir.extraction.inter_3324, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_3323 c row = (mc 483 + mc 803 + mc 2403 - 2*mc 483*mc 803 - 2*mc 483*mc 2403 - 2*mc 803*mc 2403 + 4*mc 483*mc 803*mc 2403) + 2 * KeccakfPermAir.extraction.inter_3321 c row := by
    simp only [KeccakfPermAir.extraction.inter_3323, KeccakfPermAir.extraction.inter_3322, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_3321 c row = (mc 484 + mc 804 + mc 2404 - 2*mc 484*mc 804 - 2*mc 484*mc 2404 - 2*mc 804*mc 2404 + 4*mc 484*mc 804*mc 2404) + 2 * KeccakfPermAir.extraction.inter_3319 c row := by
    simp only [KeccakfPermAir.extraction.inter_3321, KeccakfPermAir.extraction.inter_3320, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_3319 c row = (mc 485 + mc 805 + mc 2405 - 2*mc 485*mc 805 - 2*mc 485*mc 2405 - 2*mc 805*mc 2405 + 4*mc 485*mc 805*mc 2405) + 2 * KeccakfPermAir.extraction.inter_3317 c row := by
    simp only [KeccakfPermAir.extraction.inter_3319, KeccakfPermAir.extraction.inter_3318, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_3317 c row = (mc 486 + mc 806 + mc 2406 - 2*mc 486*mc 806 - 2*mc 486*mc 2406 - 2*mc 806*mc 2406 + 4*mc 486*mc 806*mc 2406) + 2 * KeccakfPermAir.extraction.inter_3315 c row := by
    simp only [KeccakfPermAir.extraction.inter_3317, KeccakfPermAir.extraction.inter_3316, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_3315 c row = (mc 487 + mc 807 + mc 2407 - 2*mc 487*mc 807 - 2*mc 487*mc 2407 - 2*mc 807*mc 2407 + 4*mc 487*mc 807*mc 2407) + 2 * KeccakfPermAir.extraction.inter_3313 c row := by
    simp only [KeccakfPermAir.extraction.inter_3315, KeccakfPermAir.extraction.inter_3314, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_3313 c row = (mc 488 + mc 808 + mc 2408 - 2*mc 488*mc 808 - 2*mc 488*mc 2408 - 2*mc 808*mc 2408 + 4*mc 488*mc 808*mc 2408) + 2 * KeccakfPermAir.extraction.inter_3311 c row := by
    simp only [KeccakfPermAir.extraction.inter_3313, KeccakfPermAir.extraction.inter_3312, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_3311 c row = (mc 489 + mc 809 + mc 2409 - 2*mc 489*mc 809 - 2*mc 489*mc 2409 - 2*mc 809*mc 2409 + 4*mc 489*mc 809*mc 2409) + 2 * KeccakfPermAir.extraction.inter_3309 c row := by
    simp only [KeccakfPermAir.extraction.inter_3311, KeccakfPermAir.extraction.inter_3310, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_3309 c row = (mc 490 + mc 810 + mc 2410 - 2*mc 490*mc 810 - 2*mc 490*mc 2410 - 2*mc 810*mc 2410 + 4*mc 490*mc 810*mc 2410) + 2 * KeccakfPermAir.extraction.inter_3307 c row := by
    simp only [KeccakfPermAir.extraction.inter_3309, KeccakfPermAir.extraction.inter_3308, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_3307 c row = (mc 491 + mc 811 + mc 2411 - 2*mc 491*mc 811 - 2*mc 491*mc 2411 - 2*mc 811*mc 2411 + 4*mc 491*mc 811*mc 2411) + 2 * KeccakfPermAir.extraction.inter_3305 c row := by
    simp only [KeccakfPermAir.extraction.inter_3307, KeccakfPermAir.extraction.inter_3306, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_3305 c row = (mc 492 + mc 812 + mc 2412 - 2*mc 492*mc 812 - 2*mc 492*mc 2412 - 2*mc 812*mc 2412 + 4*mc 492*mc 812*mc 2412) + 2 * KeccakfPermAir.extraction.inter_3303 c row := by
    simp only [KeccakfPermAir.extraction.inter_3305, KeccakfPermAir.extraction.inter_3304, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_3303 c row = (mc 493 + mc 813 + mc 2413 - 2*mc 493*mc 813 - 2*mc 493*mc 2413 - 2*mc 813*mc 2413 + 4*mc 493*mc 813*mc 2413) + 2 * KeccakfPermAir.extraction.inter_3301 c row := by
    simp only [KeccakfPermAir.extraction.inter_3303, KeccakfPermAir.extraction.inter_3302, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_3301 c row = (mc 494 + mc 814 + mc 2414 - 2*mc 494*mc 814 - 2*mc 494*mc 2414 - 2*mc 814*mc 2414 + 4*mc 494*mc 814*mc 2414) + 2 * KeccakfPermAir.extraction.inter_3299 c row := by
    simp only [KeccakfPermAir.extraction.inter_3301, KeccakfPermAir.extraction.inter_3300, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_3299 c row = (mc 495 + mc 815 + mc 2415 - 2*mc 495*mc 815 - 2*mc 495*mc 2415 - 2*mc 815*mc 2415 + 4*mc 495*mc 815*mc 2415) + 2 * KeccakfPermAir.extraction.inter_3297 c row := by
    simp only [KeccakfPermAir.extraction.inter_3299, KeccakfPermAir.extraction.inter_3298, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_3297 c row = (mc 496 + mc 816 + mc 2416 - 2*mc 496*mc 816 - 2*mc 496*mc 2416 - 2*mc 816*mc 2416 + 4*mc 496*mc 816*mc 2416) := by
    simp only [KeccakfPermAir.extraction.inter_3297, KeccakfPermAir.extraction.inter_3296, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_2587 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 497 817 2417 222 row) :
    mc 222 = (mc 497 + mc 817 + mc 2417 - 2*mc 497*mc 817 - 2*mc 497*mc 2417 - 2*mc 817*mc 2417 + 4*mc 497*mc 817*mc 2417) + 2*(mc 498 + mc 818 + mc 2418 - 2*mc 498*mc 818 - 2*mc 498*mc 2418 - 2*mc 818*mc 2418 + 4*mc 498*mc 818*mc 2418) + 4*(mc 499 + mc 819 + mc 2419 - 2*mc 499*mc 819 - 2*mc 499*mc 2419 - 2*mc 819*mc 2419 + 4*mc 499*mc 819*mc 2419) + 8*(mc 500 + mc 820 + mc 2420 - 2*mc 500*mc 820 - 2*mc 500*mc 2420 - 2*mc 820*mc 2420 + 4*mc 500*mc 820*mc 2420) + 16*(mc 501 + mc 821 + mc 2421 - 2*mc 501*mc 821 - 2*mc 501*mc 2421 - 2*mc 821*mc 2421 + 4*mc 501*mc 821*mc 2421) + 32*(mc 502 + mc 822 + mc 2422 - 2*mc 502*mc 822 - 2*mc 502*mc 2422 - 2*mc 822*mc 2422 + 4*mc 502*mc 822*mc 2422) + 64*(mc 503 + mc 823 + mc 2423 - 2*mc 503*mc 823 - 2*mc 503*mc 2423 - 2*mc 823*mc 2423 + 4*mc 503*mc 823*mc 2423) + 128*(mc 504 + mc 824 + mc 2424 - 2*mc 504*mc 824 - 2*mc 504*mc 2424 - 2*mc 824*mc 2424 + 4*mc 504*mc 824*mc 2424) + 256*(mc 505 + mc 825 + mc 2425 - 2*mc 505*mc 825 - 2*mc 505*mc 2425 - 2*mc 825*mc 2425 + 4*mc 505*mc 825*mc 2425) + 512*(mc 506 + mc 826 + mc 2426 - 2*mc 506*mc 826 - 2*mc 506*mc 2426 - 2*mc 826*mc 2426 + 4*mc 506*mc 826*mc 2426) + 1024*(mc 507 + mc 827 + mc 2427 - 2*mc 507*mc 827 - 2*mc 507*mc 2427 - 2*mc 827*mc 2427 + 4*mc 507*mc 827*mc 2427) + 2048*(mc 508 + mc 828 + mc 2428 - 2*mc 508*mc 828 - 2*mc 508*mc 2428 - 2*mc 828*mc 2428 + 4*mc 508*mc 828*mc 2428) + 4096*(mc 509 + mc 829 + mc 2429 - 2*mc 509*mc 829 - 2*mc 509*mc 2429 - 2*mc 829*mc 2429 + 4*mc 509*mc 829*mc 2429) + 8192*(mc 510 + mc 830 + mc 2430 - 2*mc 510*mc 830 - 2*mc 510*mc 2430 - 2*mc 830*mc 2430 + 4*mc 510*mc 830*mc 2430) + 16384*(mc 511 + mc 831 + mc 2431 - 2*mc 511*mc 831 - 2*mc 511*mc 2431 - 2*mc 831*mc 2431 + 4*mc 511*mc 831*mc 2431) + 32768*(mc 512 + mc 832 + mc 2432 - 2*mc 512*mc 832 - 2*mc 512*mc 2432 - 2*mc 832*mc 2432 + 4*mc 512*mc 832*mc 2432) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_2587, KeccakfPermAir.extraction.inter_3357, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_3356 c row = (mc 498 + mc 818 + mc 2418 - 2*mc 498*mc 818 - 2*mc 498*mc 2418 - 2*mc 818*mc 2418 + 4*mc 498*mc 818*mc 2418) + 2 * KeccakfPermAir.extraction.inter_3354 c row := by
    simp only [KeccakfPermAir.extraction.inter_3356, KeccakfPermAir.extraction.inter_3355, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_3354 c row = (mc 499 + mc 819 + mc 2419 - 2*mc 499*mc 819 - 2*mc 499*mc 2419 - 2*mc 819*mc 2419 + 4*mc 499*mc 819*mc 2419) + 2 * KeccakfPermAir.extraction.inter_3352 c row := by
    simp only [KeccakfPermAir.extraction.inter_3354, KeccakfPermAir.extraction.inter_3353, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_3352 c row = (mc 500 + mc 820 + mc 2420 - 2*mc 500*mc 820 - 2*mc 500*mc 2420 - 2*mc 820*mc 2420 + 4*mc 500*mc 820*mc 2420) + 2 * KeccakfPermAir.extraction.inter_3350 c row := by
    simp only [KeccakfPermAir.extraction.inter_3352, KeccakfPermAir.extraction.inter_3351, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_3350 c row = (mc 501 + mc 821 + mc 2421 - 2*mc 501*mc 821 - 2*mc 501*mc 2421 - 2*mc 821*mc 2421 + 4*mc 501*mc 821*mc 2421) + 2 * KeccakfPermAir.extraction.inter_3348 c row := by
    simp only [KeccakfPermAir.extraction.inter_3350, KeccakfPermAir.extraction.inter_3349, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_3348 c row = (mc 502 + mc 822 + mc 2422 - 2*mc 502*mc 822 - 2*mc 502*mc 2422 - 2*mc 822*mc 2422 + 4*mc 502*mc 822*mc 2422) + 2 * KeccakfPermAir.extraction.inter_3346 c row := by
    simp only [KeccakfPermAir.extraction.inter_3348, KeccakfPermAir.extraction.inter_3347, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_3346 c row = (mc 503 + mc 823 + mc 2423 - 2*mc 503*mc 823 - 2*mc 503*mc 2423 - 2*mc 823*mc 2423 + 4*mc 503*mc 823*mc 2423) + 2 * KeccakfPermAir.extraction.inter_3344 c row := by
    simp only [KeccakfPermAir.extraction.inter_3346, KeccakfPermAir.extraction.inter_3345, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_3344 c row = (mc 504 + mc 824 + mc 2424 - 2*mc 504*mc 824 - 2*mc 504*mc 2424 - 2*mc 824*mc 2424 + 4*mc 504*mc 824*mc 2424) + 2 * KeccakfPermAir.extraction.inter_3342 c row := by
    simp only [KeccakfPermAir.extraction.inter_3344, KeccakfPermAir.extraction.inter_3343, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_3342 c row = (mc 505 + mc 825 + mc 2425 - 2*mc 505*mc 825 - 2*mc 505*mc 2425 - 2*mc 825*mc 2425 + 4*mc 505*mc 825*mc 2425) + 2 * KeccakfPermAir.extraction.inter_3340 c row := by
    simp only [KeccakfPermAir.extraction.inter_3342, KeccakfPermAir.extraction.inter_3341, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_3340 c row = (mc 506 + mc 826 + mc 2426 - 2*mc 506*mc 826 - 2*mc 506*mc 2426 - 2*mc 826*mc 2426 + 4*mc 506*mc 826*mc 2426) + 2 * KeccakfPermAir.extraction.inter_3338 c row := by
    simp only [KeccakfPermAir.extraction.inter_3340, KeccakfPermAir.extraction.inter_3339, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_3338 c row = (mc 507 + mc 827 + mc 2427 - 2*mc 507*mc 827 - 2*mc 507*mc 2427 - 2*mc 827*mc 2427 + 4*mc 507*mc 827*mc 2427) + 2 * KeccakfPermAir.extraction.inter_3336 c row := by
    simp only [KeccakfPermAir.extraction.inter_3338, KeccakfPermAir.extraction.inter_3337, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_3336 c row = (mc 508 + mc 828 + mc 2428 - 2*mc 508*mc 828 - 2*mc 508*mc 2428 - 2*mc 828*mc 2428 + 4*mc 508*mc 828*mc 2428) + 2 * KeccakfPermAir.extraction.inter_3334 c row := by
    simp only [KeccakfPermAir.extraction.inter_3336, KeccakfPermAir.extraction.inter_3335, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_3334 c row = (mc 509 + mc 829 + mc 2429 - 2*mc 509*mc 829 - 2*mc 509*mc 2429 - 2*mc 829*mc 2429 + 4*mc 509*mc 829*mc 2429) + 2 * KeccakfPermAir.extraction.inter_3332 c row := by
    simp only [KeccakfPermAir.extraction.inter_3334, KeccakfPermAir.extraction.inter_3333, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_3332 c row = (mc 510 + mc 830 + mc 2430 - 2*mc 510*mc 830 - 2*mc 510*mc 2430 - 2*mc 830*mc 2430 + 4*mc 510*mc 830*mc 2430) + 2 * KeccakfPermAir.extraction.inter_3330 c row := by
    simp only [KeccakfPermAir.extraction.inter_3332, KeccakfPermAir.extraction.inter_3331, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_3330 c row = (mc 511 + mc 831 + mc 2431 - 2*mc 511*mc 831 - 2*mc 511*mc 2431 - 2*mc 831*mc 2431 + 4*mc 511*mc 831*mc 2431) + 2 * KeccakfPermAir.extraction.inter_3328 c row := by
    simp only [KeccakfPermAir.extraction.inter_3330, KeccakfPermAir.extraction.inter_3329, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_3328 c row = (mc 512 + mc 832 + mc 2432 - 2*mc 512*mc 832 - 2*mc 512*mc 2432 - 2*mc 832*mc 2432 + 4*mc 512*mc 832*mc 2432) := by
    simp only [KeccakfPermAir.extraction.inter_3328, KeccakfPermAir.extraction.inter_3327, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_2588 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 513 833 2433 223 row) :
    mc 223 = (mc 513 + mc 833 + mc 2433 - 2*mc 513*mc 833 - 2*mc 513*mc 2433 - 2*mc 833*mc 2433 + 4*mc 513*mc 833*mc 2433) + 2*(mc 514 + mc 834 + mc 2434 - 2*mc 514*mc 834 - 2*mc 514*mc 2434 - 2*mc 834*mc 2434 + 4*mc 514*mc 834*mc 2434) + 4*(mc 515 + mc 835 + mc 2435 - 2*mc 515*mc 835 - 2*mc 515*mc 2435 - 2*mc 835*mc 2435 + 4*mc 515*mc 835*mc 2435) + 8*(mc 516 + mc 836 + mc 2436 - 2*mc 516*mc 836 - 2*mc 516*mc 2436 - 2*mc 836*mc 2436 + 4*mc 516*mc 836*mc 2436) + 16*(mc 517 + mc 837 + mc 2437 - 2*mc 517*mc 837 - 2*mc 517*mc 2437 - 2*mc 837*mc 2437 + 4*mc 517*mc 837*mc 2437) + 32*(mc 518 + mc 838 + mc 2438 - 2*mc 518*mc 838 - 2*mc 518*mc 2438 - 2*mc 838*mc 2438 + 4*mc 518*mc 838*mc 2438) + 64*(mc 519 + mc 839 + mc 2439 - 2*mc 519*mc 839 - 2*mc 519*mc 2439 - 2*mc 839*mc 2439 + 4*mc 519*mc 839*mc 2439) + 128*(mc 520 + mc 840 + mc 2440 - 2*mc 520*mc 840 - 2*mc 520*mc 2440 - 2*mc 840*mc 2440 + 4*mc 520*mc 840*mc 2440) + 256*(mc 521 + mc 841 + mc 2441 - 2*mc 521*mc 841 - 2*mc 521*mc 2441 - 2*mc 841*mc 2441 + 4*mc 521*mc 841*mc 2441) + 512*(mc 522 + mc 842 + mc 2442 - 2*mc 522*mc 842 - 2*mc 522*mc 2442 - 2*mc 842*mc 2442 + 4*mc 522*mc 842*mc 2442) + 1024*(mc 523 + mc 843 + mc 2443 - 2*mc 523*mc 843 - 2*mc 523*mc 2443 - 2*mc 843*mc 2443 + 4*mc 523*mc 843*mc 2443) + 2048*(mc 524 + mc 844 + mc 2444 - 2*mc 524*mc 844 - 2*mc 524*mc 2444 - 2*mc 844*mc 2444 + 4*mc 524*mc 844*mc 2444) + 4096*(mc 525 + mc 845 + mc 2445 - 2*mc 525*mc 845 - 2*mc 525*mc 2445 - 2*mc 845*mc 2445 + 4*mc 525*mc 845*mc 2445) + 8192*(mc 526 + mc 846 + mc 2446 - 2*mc 526*mc 846 - 2*mc 526*mc 2446 - 2*mc 846*mc 2446 + 4*mc 526*mc 846*mc 2446) + 16384*(mc 527 + mc 847 + mc 2447 - 2*mc 527*mc 847 - 2*mc 527*mc 2447 - 2*mc 847*mc 2447 + 4*mc 527*mc 847*mc 2447) + 32768*(mc 528 + mc 848 + mc 2448 - 2*mc 528*mc 848 - 2*mc 528*mc 2448 - 2*mc 848*mc 2448 + 4*mc 528*mc 848*mc 2448) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_2588, KeccakfPermAir.extraction.inter_3388, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_3387 c row = (mc 514 + mc 834 + mc 2434 - 2*mc 514*mc 834 - 2*mc 514*mc 2434 - 2*mc 834*mc 2434 + 4*mc 514*mc 834*mc 2434) + 2 * KeccakfPermAir.extraction.inter_3385 c row := by
    simp only [KeccakfPermAir.extraction.inter_3387, KeccakfPermAir.extraction.inter_3386, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_3385 c row = (mc 515 + mc 835 + mc 2435 - 2*mc 515*mc 835 - 2*mc 515*mc 2435 - 2*mc 835*mc 2435 + 4*mc 515*mc 835*mc 2435) + 2 * KeccakfPermAir.extraction.inter_3383 c row := by
    simp only [KeccakfPermAir.extraction.inter_3385, KeccakfPermAir.extraction.inter_3384, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_3383 c row = (mc 516 + mc 836 + mc 2436 - 2*mc 516*mc 836 - 2*mc 516*mc 2436 - 2*mc 836*mc 2436 + 4*mc 516*mc 836*mc 2436) + 2 * KeccakfPermAir.extraction.inter_3381 c row := by
    simp only [KeccakfPermAir.extraction.inter_3383, KeccakfPermAir.extraction.inter_3382, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_3381 c row = (mc 517 + mc 837 + mc 2437 - 2*mc 517*mc 837 - 2*mc 517*mc 2437 - 2*mc 837*mc 2437 + 4*mc 517*mc 837*mc 2437) + 2 * KeccakfPermAir.extraction.inter_3379 c row := by
    simp only [KeccakfPermAir.extraction.inter_3381, KeccakfPermAir.extraction.inter_3380, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_3379 c row = (mc 518 + mc 838 + mc 2438 - 2*mc 518*mc 838 - 2*mc 518*mc 2438 - 2*mc 838*mc 2438 + 4*mc 518*mc 838*mc 2438) + 2 * KeccakfPermAir.extraction.inter_3377 c row := by
    simp only [KeccakfPermAir.extraction.inter_3379, KeccakfPermAir.extraction.inter_3378, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_3377 c row = (mc 519 + mc 839 + mc 2439 - 2*mc 519*mc 839 - 2*mc 519*mc 2439 - 2*mc 839*mc 2439 + 4*mc 519*mc 839*mc 2439) + 2 * KeccakfPermAir.extraction.inter_3375 c row := by
    simp only [KeccakfPermAir.extraction.inter_3377, KeccakfPermAir.extraction.inter_3376, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_3375 c row = (mc 520 + mc 840 + mc 2440 - 2*mc 520*mc 840 - 2*mc 520*mc 2440 - 2*mc 840*mc 2440 + 4*mc 520*mc 840*mc 2440) + 2 * KeccakfPermAir.extraction.inter_3373 c row := by
    simp only [KeccakfPermAir.extraction.inter_3375, KeccakfPermAir.extraction.inter_3374, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_3373 c row = (mc 521 + mc 841 + mc 2441 - 2*mc 521*mc 841 - 2*mc 521*mc 2441 - 2*mc 841*mc 2441 + 4*mc 521*mc 841*mc 2441) + 2 * KeccakfPermAir.extraction.inter_3371 c row := by
    simp only [KeccakfPermAir.extraction.inter_3373, KeccakfPermAir.extraction.inter_3372, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_3371 c row = (mc 522 + mc 842 + mc 2442 - 2*mc 522*mc 842 - 2*mc 522*mc 2442 - 2*mc 842*mc 2442 + 4*mc 522*mc 842*mc 2442) + 2 * KeccakfPermAir.extraction.inter_3369 c row := by
    simp only [KeccakfPermAir.extraction.inter_3371, KeccakfPermAir.extraction.inter_3370, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_3369 c row = (mc 523 + mc 843 + mc 2443 - 2*mc 523*mc 843 - 2*mc 523*mc 2443 - 2*mc 843*mc 2443 + 4*mc 523*mc 843*mc 2443) + 2 * KeccakfPermAir.extraction.inter_3367 c row := by
    simp only [KeccakfPermAir.extraction.inter_3369, KeccakfPermAir.extraction.inter_3368, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_3367 c row = (mc 524 + mc 844 + mc 2444 - 2*mc 524*mc 844 - 2*mc 524*mc 2444 - 2*mc 844*mc 2444 + 4*mc 524*mc 844*mc 2444) + 2 * KeccakfPermAir.extraction.inter_3365 c row := by
    simp only [KeccakfPermAir.extraction.inter_3367, KeccakfPermAir.extraction.inter_3366, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_3365 c row = (mc 525 + mc 845 + mc 2445 - 2*mc 525*mc 845 - 2*mc 525*mc 2445 - 2*mc 845*mc 2445 + 4*mc 525*mc 845*mc 2445) + 2 * KeccakfPermAir.extraction.inter_3363 c row := by
    simp only [KeccakfPermAir.extraction.inter_3365, KeccakfPermAir.extraction.inter_3364, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_3363 c row = (mc 526 + mc 846 + mc 2446 - 2*mc 526*mc 846 - 2*mc 526*mc 2446 - 2*mc 846*mc 2446 + 4*mc 526*mc 846*mc 2446) + 2 * KeccakfPermAir.extraction.inter_3361 c row := by
    simp only [KeccakfPermAir.extraction.inter_3363, KeccakfPermAir.extraction.inter_3362, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_3361 c row = (mc 527 + mc 847 + mc 2447 - 2*mc 527*mc 847 - 2*mc 527*mc 2447 - 2*mc 847*mc 2447 + 4*mc 527*mc 847*mc 2447) + 2 * KeccakfPermAir.extraction.inter_3359 c row := by
    simp only [KeccakfPermAir.extraction.inter_3361, KeccakfPermAir.extraction.inter_3360, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_3359 c row = (mc 528 + mc 848 + mc 2448 - 2*mc 528*mc 848 - 2*mc 528*mc 2448 - 2*mc 848*mc 2448 + 4*mc 528*mc 848*mc 2448) := by
    simp only [KeccakfPermAir.extraction.inter_3359, KeccakfPermAir.extraction.inter_3358, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_g_2589 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.xor3_recompose16_eq c 529 849 2449 224 row) :
    mc 224 = (mc 529 + mc 849 + mc 2449 - 2*mc 529*mc 849 - 2*mc 529*mc 2449 - 2*mc 849*mc 2449 + 4*mc 529*mc 849*mc 2449) + 2*(mc 530 + mc 850 + mc 2450 - 2*mc 530*mc 850 - 2*mc 530*mc 2450 - 2*mc 850*mc 2450 + 4*mc 530*mc 850*mc 2450) + 4*(mc 531 + mc 851 + mc 2451 - 2*mc 531*mc 851 - 2*mc 531*mc 2451 - 2*mc 851*mc 2451 + 4*mc 531*mc 851*mc 2451) + 8*(mc 532 + mc 852 + mc 2452 - 2*mc 532*mc 852 - 2*mc 532*mc 2452 - 2*mc 852*mc 2452 + 4*mc 532*mc 852*mc 2452) + 16*(mc 533 + mc 853 + mc 2453 - 2*mc 533*mc 853 - 2*mc 533*mc 2453 - 2*mc 853*mc 2453 + 4*mc 533*mc 853*mc 2453) + 32*(mc 534 + mc 854 + mc 2454 - 2*mc 534*mc 854 - 2*mc 534*mc 2454 - 2*mc 854*mc 2454 + 4*mc 534*mc 854*mc 2454) + 64*(mc 535 + mc 855 + mc 2455 - 2*mc 535*mc 855 - 2*mc 535*mc 2455 - 2*mc 855*mc 2455 + 4*mc 535*mc 855*mc 2455) + 128*(mc 536 + mc 856 + mc 2456 - 2*mc 536*mc 856 - 2*mc 536*mc 2456 - 2*mc 856*mc 2456 + 4*mc 536*mc 856*mc 2456) + 256*(mc 537 + mc 857 + mc 2457 - 2*mc 537*mc 857 - 2*mc 537*mc 2457 - 2*mc 857*mc 2457 + 4*mc 537*mc 857*mc 2457) + 512*(mc 538 + mc 858 + mc 2458 - 2*mc 538*mc 858 - 2*mc 538*mc 2458 - 2*mc 858*mc 2458 + 4*mc 538*mc 858*mc 2458) + 1024*(mc 539 + mc 859 + mc 2459 - 2*mc 539*mc 859 - 2*mc 539*mc 2459 - 2*mc 859*mc 2459 + 4*mc 539*mc 859*mc 2459) + 2048*(mc 540 + mc 860 + mc 2460 - 2*mc 540*mc 860 - 2*mc 540*mc 2460 - 2*mc 860*mc 2460 + 4*mc 540*mc 860*mc 2460) + 4096*(mc 541 + mc 861 + mc 2461 - 2*mc 541*mc 861 - 2*mc 541*mc 2461 - 2*mc 861*mc 2461 + 4*mc 541*mc 861*mc 2461) + 8192*(mc 542 + mc 862 + mc 2462 - 2*mc 542*mc 862 - 2*mc 542*mc 2462 - 2*mc 862*mc 2462 + 4*mc 542*mc 862*mc 2462) + 16384*(mc 543 + mc 863 + mc 2463 - 2*mc 543*mc 863 - 2*mc 543*mc 2463 - 2*mc 863*mc 2463 + 4*mc 543*mc 863*mc 2463) + 32768*(mc 544 + mc 864 + mc 2464 - 2*mc 544*mc 864 - 2*mc 544*mc 2464 - 2*mc 864*mc 2464 + 4*mc 544*mc 864*mc 2464) := by
  dsimp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at hx
  simp only [KeccakfPermAir.extraction.constraint_2589, KeccakfPermAir.extraction.inter_3419, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_3418 c row = (mc 530 + mc 850 + mc 2450 - 2*mc 530*mc 850 - 2*mc 530*mc 2450 - 2*mc 850*mc 2450 + 4*mc 530*mc 850*mc 2450) + 2 * KeccakfPermAir.extraction.inter_3416 c row := by
    simp only [KeccakfPermAir.extraction.inter_3418, KeccakfPermAir.extraction.inter_3417, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_3416 c row = (mc 531 + mc 851 + mc 2451 - 2*mc 531*mc 851 - 2*mc 531*mc 2451 - 2*mc 851*mc 2451 + 4*mc 531*mc 851*mc 2451) + 2 * KeccakfPermAir.extraction.inter_3414 c row := by
    simp only [KeccakfPermAir.extraction.inter_3416, KeccakfPermAir.extraction.inter_3415, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_3414 c row = (mc 532 + mc 852 + mc 2452 - 2*mc 532*mc 852 - 2*mc 532*mc 2452 - 2*mc 852*mc 2452 + 4*mc 532*mc 852*mc 2452) + 2 * KeccakfPermAir.extraction.inter_3412 c row := by
    simp only [KeccakfPermAir.extraction.inter_3414, KeccakfPermAir.extraction.inter_3413, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_3412 c row = (mc 533 + mc 853 + mc 2453 - 2*mc 533*mc 853 - 2*mc 533*mc 2453 - 2*mc 853*mc 2453 + 4*mc 533*mc 853*mc 2453) + 2 * KeccakfPermAir.extraction.inter_3410 c row := by
    simp only [KeccakfPermAir.extraction.inter_3412, KeccakfPermAir.extraction.inter_3411, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_3410 c row = (mc 534 + mc 854 + mc 2454 - 2*mc 534*mc 854 - 2*mc 534*mc 2454 - 2*mc 854*mc 2454 + 4*mc 534*mc 854*mc 2454) + 2 * KeccakfPermAir.extraction.inter_3408 c row := by
    simp only [KeccakfPermAir.extraction.inter_3410, KeccakfPermAir.extraction.inter_3409, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_3408 c row = (mc 535 + mc 855 + mc 2455 - 2*mc 535*mc 855 - 2*mc 535*mc 2455 - 2*mc 855*mc 2455 + 4*mc 535*mc 855*mc 2455) + 2 * KeccakfPermAir.extraction.inter_3406 c row := by
    simp only [KeccakfPermAir.extraction.inter_3408, KeccakfPermAir.extraction.inter_3407, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_3406 c row = (mc 536 + mc 856 + mc 2456 - 2*mc 536*mc 856 - 2*mc 536*mc 2456 - 2*mc 856*mc 2456 + 4*mc 536*mc 856*mc 2456) + 2 * KeccakfPermAir.extraction.inter_3404 c row := by
    simp only [KeccakfPermAir.extraction.inter_3406, KeccakfPermAir.extraction.inter_3405, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_3404 c row = (mc 537 + mc 857 + mc 2457 - 2*mc 537*mc 857 - 2*mc 537*mc 2457 - 2*mc 857*mc 2457 + 4*mc 537*mc 857*mc 2457) + 2 * KeccakfPermAir.extraction.inter_3402 c row := by
    simp only [KeccakfPermAir.extraction.inter_3404, KeccakfPermAir.extraction.inter_3403, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_3402 c row = (mc 538 + mc 858 + mc 2458 - 2*mc 538*mc 858 - 2*mc 538*mc 2458 - 2*mc 858*mc 2458 + 4*mc 538*mc 858*mc 2458) + 2 * KeccakfPermAir.extraction.inter_3400 c row := by
    simp only [KeccakfPermAir.extraction.inter_3402, KeccakfPermAir.extraction.inter_3401, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_3400 c row = (mc 539 + mc 859 + mc 2459 - 2*mc 539*mc 859 - 2*mc 539*mc 2459 - 2*mc 859*mc 2459 + 4*mc 539*mc 859*mc 2459) + 2 * KeccakfPermAir.extraction.inter_3398 c row := by
    simp only [KeccakfPermAir.extraction.inter_3400, KeccakfPermAir.extraction.inter_3399, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_3398 c row = (mc 540 + mc 860 + mc 2460 - 2*mc 540*mc 860 - 2*mc 540*mc 2460 - 2*mc 860*mc 2460 + 4*mc 540*mc 860*mc 2460) + 2 * KeccakfPermAir.extraction.inter_3396 c row := by
    simp only [KeccakfPermAir.extraction.inter_3398, KeccakfPermAir.extraction.inter_3397, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_3396 c row = (mc 541 + mc 861 + mc 2461 - 2*mc 541*mc 861 - 2*mc 541*mc 2461 - 2*mc 861*mc 2461 + 4*mc 541*mc 861*mc 2461) + 2 * KeccakfPermAir.extraction.inter_3394 c row := by
    simp only [KeccakfPermAir.extraction.inter_3396, KeccakfPermAir.extraction.inter_3395, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_3394 c row = (mc 542 + mc 862 + mc 2462 - 2*mc 542*mc 862 - 2*mc 542*mc 2462 - 2*mc 862*mc 2462 + 4*mc 542*mc 862*mc 2462) + 2 * KeccakfPermAir.extraction.inter_3392 c row := by
    simp only [KeccakfPermAir.extraction.inter_3394, KeccakfPermAir.extraction.inter_3393, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_3392 c row = (mc 543 + mc 863 + mc 2463 - 2*mc 543*mc 863 - 2*mc 543*mc 2463 - 2*mc 863*mc 2463 + 4*mc 543*mc 863*mc 2463) + 2 * KeccakfPermAir.extraction.inter_3390 c row := by
    simp only [KeccakfPermAir.extraction.inter_3392, KeccakfPermAir.extraction.inter_3391, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_3390 c row = (mc 544 + mc 864 + mc 2464 - 2*mc 544*mc 864 - 2*mc 544*mc 2464 - 2*mc 864*mc 2464 + 4*mc 544*mc 864*mc 2464) := by
    simp only [KeccakfPermAir.extraction.inter_3390, KeccakfPermAir.extraction.inter_3389, hmc]; ring
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

/-! ## `theta_a_eq_xor3_recompose`: value-level linking over the full range

For each limb j ∈ [0, 100) the `a` column at flat index j equals the
16-bit xor3 recomposition of corresponding chunks from three bit-column
families (using column abbreviations from `Columns.lean`):
- `c_bit` at offset `64 * x + 16 * limb + i`
- `c_prime_bit` at offset `64 * x + 16 * limb + i`
- `a_prime_bit` at offset `16 * j + i`

where `x = (j / 4) % 5` and `limb = j % 4`.

This covers the full `a`-column range 125..224 with no gap at the
216/217 boundary. -/

/-- For each limb j < 100, the `a` column at index j equals the 16-bit
    xor3 recomposition of corresponding c_bit, c_prime_bit, and a_prime_bit
    chunks.  This is the raw chunkwise relation `a = c ⊕ c' ⊕ a'` at the
    limb level.

    Proof: extract `theta_xor3_recompose` from `RoundLocalConstraints`, then
    case-split `j` and dispatch each concrete limb to its `peel_g_<cnum>`
    Horner-peeling lemma (instantiating the opaque `mc` with the actual
    `Circuit.main` column accessor).  Each case closes by definitional
    equality. -/
theorem theta_a_eq_xor3_recompose
    {ExtF : Type} [Field ExtF]
    {air : KeccakfPermAir.Valid_KeccakfPermAir FBB ExtF} {row : ℕ}
    (h_round : RoundLocalConstraints air row) (j : ℕ) (hj : j < 100) :
    let x := (j / 4) % 5
    let limb := j % 4
    let cbi (i : ℕ) := c_bit air (64 * x + 16 * limb + i) row
    let cpbi (i : ℕ) := c_prime_bit air (64 * x + 16 * limb + i) row
    let apbi (i : ℕ) := a_prime_bit air (16 * j + i) row
    let x3 (i : ℕ) :=
      cbi i + cpbi i + apbi i -
      2 * cbi i * cpbi i - 2 * cbi i * apbi i - 2 * cpbi i * apbi i +
      4 * cbi i * cpbi i * apbi i
    a air j row =
    x3 0 + 2 * x3 1 + 4 * x3 2 + 8 * x3 3 + 16 * x3 4 + 32 * x3 5 + 64 * x3 6 + 128 * x3 7 +
    256 * x3 8 + 512 * x3 9 + 1024 * x3 10 + 2048 * x3 11 + 4096 * x3 12 + 8192 * x3 13 +
    16384 * x3 14 + 32768 * x3 15 := by
  have hx := h_round.theta_xor3_recompose j hj
  simp only at hx
  interval_cases j
  · exact peel_g_954 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_955 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_956 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_957 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1022 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1023 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1024 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1025 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1090 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1091 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1092 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1093 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1158 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1159 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1160 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1161 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1226 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1227 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1228 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1229 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1294 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1295 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1296 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1297 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1362 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1363 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1364 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1365 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1430 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1431 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1432 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1433 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1498 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1499 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1500 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1501 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1566 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1567 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1568 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1569 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1634 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1635 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1636 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1637 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1702 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1703 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1704 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1705 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1770 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1771 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1772 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1773 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1838 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1839 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1840 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1841 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1906 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1907 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1908 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1909 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1974 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1975 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1976 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_1977 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_2042 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_2043 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_2044 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_2045 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_2110 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_2111 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_2112 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_2113 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_2178 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_2179 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_2180 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_2181 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_2246 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_2247 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_2248 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_2249 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_2314 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_2315 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_2316 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_2317 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_2382 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_2383 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_2384 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_2385 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_2450 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_2451 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_2452 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_2453 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_2518 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_2519 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_2520 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_2521 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_2586 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_2587 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_2588 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx
  · exact peel_g_2589 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) hx

/-! ## Raw linking theorem

For each limb j ∈ [0, 100) the xor3 recomposition constraint holds between the
c_bit, c_prime_bit, a_prime_bit bit-column chunks and the `a` limb column at
index 125 + j, as a direct projection from `RoundLocalConstraints`. -/

/-- For each limb j < 100, the `xor3_recompose16_eq` constraint holds
    between the c_bit, c_prime_bit, and a_prime_bit bit-column chunks
    and the `a` limb column at index 125 + j. -/
theorem theta_xor3_raw
    {ExtF : Type} [Field ExtF]
    {air : KeccakfPermAir.Valid_KeccakfPermAir FBB ExtF} {row : ℕ}
    (h_round : RoundLocalConstraints air row) (j : ℕ) (hj : j < 100) :
    let x := (j / 4) % 5
    let limb := j % 4
    KeccakfPermAir.extraction.xor3_recompose16_eq air
      (225 + 64 * x + 16 * limb)
      (545 + 64 * x + 16 * limb)
      (865 + 16 * j)
      (125 + j)
      row := by
  have hx := h_round.theta_xor3_recompose j hj
  simp only at hx
  exact hx

end KeccakfPermAir.Soundness
