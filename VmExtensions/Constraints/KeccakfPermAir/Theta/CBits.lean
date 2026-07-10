import VmExtensions.Constraints.KeccakfPermAir.Columns
import VmExtensions.Extraction.KeccakfPermAir

set_option linter.all false
set_option maxHeartbeats 1_000_000_000

namespace KeccakfPermAir.constraints

/-! ## θ column-parity boolean constraints: c_bit[x][z] * (c_bit[x][z] - 1) = 0 -/

section constraint_simplification
  variable {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_250 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 0 row) * ((c_bit c 0 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_250_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_250 c row ↔ constraint_250 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_251 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 1 row) * ((c_bit c 1 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_251_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_251 c row ↔ constraint_251 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_252 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 2 row) * ((c_bit c 2 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_252_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_252 c row ↔ constraint_252 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_253 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 3 row) * ((c_bit c 3 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_253_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_253 c row ↔ constraint_253 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_254 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 4 row) * ((c_bit c 4 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_254_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_254 c row ↔ constraint_254 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_255 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 5 row) * ((c_bit c 5 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_255_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_255 c row ↔ constraint_255 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_256 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 6 row) * ((c_bit c 6 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_256_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_256 c row ↔ constraint_256 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_257 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 7 row) * ((c_bit c 7 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_257_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_257 c row ↔ constraint_257 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_258 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 8 row) * ((c_bit c 8 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_258_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_258 c row ↔ constraint_258 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_259 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 9 row) * ((c_bit c 9 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_259_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_259 c row ↔ constraint_259 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_260 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 10 row) * ((c_bit c 10 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_260_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_260 c row ↔ constraint_260 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_261 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 11 row) * ((c_bit c 11 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_261_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_261 c row ↔ constraint_261 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_262 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 12 row) * ((c_bit c 12 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_262_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_262 c row ↔ constraint_262 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_263 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 13 row) * ((c_bit c 13 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_263_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_263 c row ↔ constraint_263 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_264 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 14 row) * ((c_bit c 14 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_264_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_264 c row ↔ constraint_264 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_265 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 15 row) * ((c_bit c 15 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_265_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_265 c row ↔ constraint_265 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_266 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 16 row) * ((c_bit c 16 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_266_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_266 c row ↔ constraint_266 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_267 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 17 row) * ((c_bit c 17 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_267_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_267 c row ↔ constraint_267 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_268 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 18 row) * ((c_bit c 18 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_268_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_268 c row ↔ constraint_268 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_269 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 19 row) * ((c_bit c 19 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_269_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_269 c row ↔ constraint_269 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_270 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 20 row) * ((c_bit c 20 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_270_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_270 c row ↔ constraint_270 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_271 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 21 row) * ((c_bit c 21 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_271_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_271 c row ↔ constraint_271 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_272 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 22 row) * ((c_bit c 22 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_272_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_272 c row ↔ constraint_272 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_273 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 23 row) * ((c_bit c 23 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_273_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_273 c row ↔ constraint_273 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_274 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 24 row) * ((c_bit c 24 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_274_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_274 c row ↔ constraint_274 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_275 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 25 row) * ((c_bit c 25 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_275_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_275 c row ↔ constraint_275 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_276 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 26 row) * ((c_bit c 26 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_276_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_276 c row ↔ constraint_276 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_277 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 27 row) * ((c_bit c 27 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_277_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_277 c row ↔ constraint_277 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_278 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 28 row) * ((c_bit c 28 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_278_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_278 c row ↔ constraint_278 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_279 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 29 row) * ((c_bit c 29 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_279_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_279 c row ↔ constraint_279 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_280 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 30 row) * ((c_bit c 30 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_280_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_280 c row ↔ constraint_280 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_281 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 31 row) * ((c_bit c 31 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_281_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_281 c row ↔ constraint_281 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_282 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 32 row) * ((c_bit c 32 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_282_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_282 c row ↔ constraint_282 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_283 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 33 row) * ((c_bit c 33 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_283_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_283 c row ↔ constraint_283 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_284 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 34 row) * ((c_bit c 34 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_284_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_284 c row ↔ constraint_284 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_285 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 35 row) * ((c_bit c 35 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_285_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_285 c row ↔ constraint_285 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_286 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 36 row) * ((c_bit c 36 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_286_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_286 c row ↔ constraint_286 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_287 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 37 row) * ((c_bit c 37 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_287_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_287 c row ↔ constraint_287 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_288 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 38 row) * ((c_bit c 38 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_288_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_288 c row ↔ constraint_288 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_289 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 39 row) * ((c_bit c 39 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_289_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_289 c row ↔ constraint_289 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_290 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 40 row) * ((c_bit c 40 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_290_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_290 c row ↔ constraint_290 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_291 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 41 row) * ((c_bit c 41 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_291_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_291 c row ↔ constraint_291 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_292 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 42 row) * ((c_bit c 42 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_292_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_292 c row ↔ constraint_292 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_293 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 43 row) * ((c_bit c 43 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_293_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_293 c row ↔ constraint_293 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_294 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 44 row) * ((c_bit c 44 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_294_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_294 c row ↔ constraint_294 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_295 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 45 row) * ((c_bit c 45 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_295_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_295 c row ↔ constraint_295 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_296 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 46 row) * ((c_bit c 46 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_296_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_296 c row ↔ constraint_296 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_297 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 47 row) * ((c_bit c 47 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_297_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_297 c row ↔ constraint_297 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_298 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 48 row) * ((c_bit c 48 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_298_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_298 c row ↔ constraint_298 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_299 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 49 row) * ((c_bit c 49 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_299_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_299 c row ↔ constraint_299 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_300 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 50 row) * ((c_bit c 50 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_300_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_300 c row ↔ constraint_300 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_301 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 51 row) * ((c_bit c 51 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_301_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_301 c row ↔ constraint_301 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_302 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 52 row) * ((c_bit c 52 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_302_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_302 c row ↔ constraint_302 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_303 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 53 row) * ((c_bit c 53 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_303_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_303 c row ↔ constraint_303 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_304 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 54 row) * ((c_bit c 54 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_304_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_304 c row ↔ constraint_304 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_305 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 55 row) * ((c_bit c 55 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_305_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_305 c row ↔ constraint_305 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_306 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 56 row) * ((c_bit c 56 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_306_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_306 c row ↔ constraint_306 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_307 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 57 row) * ((c_bit c 57 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_307_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_307 c row ↔ constraint_307 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_308 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 58 row) * ((c_bit c 58 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_308_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_308 c row ↔ constraint_308 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_309 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 59 row) * ((c_bit c 59 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_309_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_309 c row ↔ constraint_309 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_310 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 60 row) * ((c_bit c 60 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_310_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_310 c row ↔ constraint_310 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_311 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 61 row) * ((c_bit c 61 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_311_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_311 c row ↔ constraint_311 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_312 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 62 row) * ((c_bit c 62 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_312_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_312 c row ↔ constraint_312 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_313 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 63 row) * ((c_bit c 63 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_313_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_313 c row ↔ constraint_313 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_314 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 0 row) - (((((c_bit c 0 row) + (c_bit c 256 row)) - ((c_bit c 0 row) * ((c_bit c 256 row) + (c_bit c 256 row)))) + (c_bit c 127 row)) - ((((c_bit c 0 row) + (c_bit c 256 row)) - ((c_bit c 0 row) * ((c_bit c 256 row) + (c_bit c 256 row)))) * ((c_bit c 127 row) + (c_bit c 127 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_314_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_314 c row ↔ constraint_314 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_315 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 1 row) - (((((c_bit c 1 row) + (c_bit c 257 row)) - ((c_bit c 1 row) * ((c_bit c 257 row) + (c_bit c 257 row)))) + (c_bit c 64 row)) - ((((c_bit c 1 row) + (c_bit c 257 row)) - ((c_bit c 1 row) * ((c_bit c 257 row) + (c_bit c 257 row)))) * ((c_bit c 64 row) + (c_bit c 64 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_315_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_315 c row ↔ constraint_315 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_316 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 2 row) - (((((c_bit c 2 row) + (c_bit c 258 row)) - ((c_bit c 2 row) * ((c_bit c 258 row) + (c_bit c 258 row)))) + (c_bit c 65 row)) - ((((c_bit c 2 row) + (c_bit c 258 row)) - ((c_bit c 2 row) * ((c_bit c 258 row) + (c_bit c 258 row)))) * ((c_bit c 65 row) + (c_bit c 65 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_316_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_316 c row ↔ constraint_316 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_317 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 3 row) - (((((c_bit c 3 row) + (c_bit c 259 row)) - ((c_bit c 3 row) * ((c_bit c 259 row) + (c_bit c 259 row)))) + (c_bit c 66 row)) - ((((c_bit c 3 row) + (c_bit c 259 row)) - ((c_bit c 3 row) * ((c_bit c 259 row) + (c_bit c 259 row)))) * ((c_bit c 66 row) + (c_bit c 66 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_317_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_317 c row ↔ constraint_317 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_318 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 4 row) - (((((c_bit c 4 row) + (c_bit c 260 row)) - ((c_bit c 4 row) * ((c_bit c 260 row) + (c_bit c 260 row)))) + (c_bit c 67 row)) - ((((c_bit c 4 row) + (c_bit c 260 row)) - ((c_bit c 4 row) * ((c_bit c 260 row) + (c_bit c 260 row)))) * ((c_bit c 67 row) + (c_bit c 67 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_318_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_318 c row ↔ constraint_318 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_319 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 5 row) - (((((c_bit c 5 row) + (c_bit c 261 row)) - ((c_bit c 5 row) * ((c_bit c 261 row) + (c_bit c 261 row)))) + (c_bit c 68 row)) - ((((c_bit c 5 row) + (c_bit c 261 row)) - ((c_bit c 5 row) * ((c_bit c 261 row) + (c_bit c 261 row)))) * ((c_bit c 68 row) + (c_bit c 68 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_319_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_319 c row ↔ constraint_319 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_320 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 6 row) - (((((c_bit c 6 row) + (c_bit c 262 row)) - ((c_bit c 6 row) * ((c_bit c 262 row) + (c_bit c 262 row)))) + (c_bit c 69 row)) - ((((c_bit c 6 row) + (c_bit c 262 row)) - ((c_bit c 6 row) * ((c_bit c 262 row) + (c_bit c 262 row)))) * ((c_bit c 69 row) + (c_bit c 69 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_320_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_320 c row ↔ constraint_320 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_321 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 7 row) - (((((c_bit c 7 row) + (c_bit c 263 row)) - ((c_bit c 7 row) * ((c_bit c 263 row) + (c_bit c 263 row)))) + (c_bit c 70 row)) - ((((c_bit c 7 row) + (c_bit c 263 row)) - ((c_bit c 7 row) * ((c_bit c 263 row) + (c_bit c 263 row)))) * ((c_bit c 70 row) + (c_bit c 70 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_321_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_321 c row ↔ constraint_321 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_322 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 8 row) - (((((c_bit c 8 row) + (c_bit c 264 row)) - ((c_bit c 8 row) * ((c_bit c 264 row) + (c_bit c 264 row)))) + (c_bit c 71 row)) - ((((c_bit c 8 row) + (c_bit c 264 row)) - ((c_bit c 8 row) * ((c_bit c 264 row) + (c_bit c 264 row)))) * ((c_bit c 71 row) + (c_bit c 71 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_322_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_322 c row ↔ constraint_322 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_323 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 9 row) - (((((c_bit c 9 row) + (c_bit c 265 row)) - ((c_bit c 9 row) * ((c_bit c 265 row) + (c_bit c 265 row)))) + (c_bit c 72 row)) - ((((c_bit c 9 row) + (c_bit c 265 row)) - ((c_bit c 9 row) * ((c_bit c 265 row) + (c_bit c 265 row)))) * ((c_bit c 72 row) + (c_bit c 72 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_323_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_323 c row ↔ constraint_323 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_324 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 10 row) - (((((c_bit c 10 row) + (c_bit c 266 row)) - ((c_bit c 10 row) * ((c_bit c 266 row) + (c_bit c 266 row)))) + (c_bit c 73 row)) - ((((c_bit c 10 row) + (c_bit c 266 row)) - ((c_bit c 10 row) * ((c_bit c 266 row) + (c_bit c 266 row)))) * ((c_bit c 73 row) + (c_bit c 73 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_324_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_324 c row ↔ constraint_324 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_325 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 11 row) - (((((c_bit c 11 row) + (c_bit c 267 row)) - ((c_bit c 11 row) * ((c_bit c 267 row) + (c_bit c 267 row)))) + (c_bit c 74 row)) - ((((c_bit c 11 row) + (c_bit c 267 row)) - ((c_bit c 11 row) * ((c_bit c 267 row) + (c_bit c 267 row)))) * ((c_bit c 74 row) + (c_bit c 74 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_325_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_325 c row ↔ constraint_325 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_326 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 12 row) - (((((c_bit c 12 row) + (c_bit c 268 row)) - ((c_bit c 12 row) * ((c_bit c 268 row) + (c_bit c 268 row)))) + (c_bit c 75 row)) - ((((c_bit c 12 row) + (c_bit c 268 row)) - ((c_bit c 12 row) * ((c_bit c 268 row) + (c_bit c 268 row)))) * ((c_bit c 75 row) + (c_bit c 75 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_326_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_326 c row ↔ constraint_326 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_327 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 13 row) - (((((c_bit c 13 row) + (c_bit c 269 row)) - ((c_bit c 13 row) * ((c_bit c 269 row) + (c_bit c 269 row)))) + (c_bit c 76 row)) - ((((c_bit c 13 row) + (c_bit c 269 row)) - ((c_bit c 13 row) * ((c_bit c 269 row) + (c_bit c 269 row)))) * ((c_bit c 76 row) + (c_bit c 76 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_327_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_327 c row ↔ constraint_327 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_328 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 14 row) - (((((c_bit c 14 row) + (c_bit c 270 row)) - ((c_bit c 14 row) * ((c_bit c 270 row) + (c_bit c 270 row)))) + (c_bit c 77 row)) - ((((c_bit c 14 row) + (c_bit c 270 row)) - ((c_bit c 14 row) * ((c_bit c 270 row) + (c_bit c 270 row)))) * ((c_bit c 77 row) + (c_bit c 77 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_328_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_328 c row ↔ constraint_328 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_329 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 15 row) - (((((c_bit c 15 row) + (c_bit c 271 row)) - ((c_bit c 15 row) * ((c_bit c 271 row) + (c_bit c 271 row)))) + (c_bit c 78 row)) - ((((c_bit c 15 row) + (c_bit c 271 row)) - ((c_bit c 15 row) * ((c_bit c 271 row) + (c_bit c 271 row)))) * ((c_bit c 78 row) + (c_bit c 78 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_329_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_329 c row ↔ constraint_329 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_330 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 16 row) - (((((c_bit c 16 row) + (c_bit c 272 row)) - ((c_bit c 16 row) * ((c_bit c 272 row) + (c_bit c 272 row)))) + (c_bit c 79 row)) - ((((c_bit c 16 row) + (c_bit c 272 row)) - ((c_bit c 16 row) * ((c_bit c 272 row) + (c_bit c 272 row)))) * ((c_bit c 79 row) + (c_bit c 79 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_330_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_330 c row ↔ constraint_330 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_331 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 17 row) - (((((c_bit c 17 row) + (c_bit c 273 row)) - ((c_bit c 17 row) * ((c_bit c 273 row) + (c_bit c 273 row)))) + (c_bit c 80 row)) - ((((c_bit c 17 row) + (c_bit c 273 row)) - ((c_bit c 17 row) * ((c_bit c 273 row) + (c_bit c 273 row)))) * ((c_bit c 80 row) + (c_bit c 80 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_331_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_331 c row ↔ constraint_331 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_332 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 18 row) - (((((c_bit c 18 row) + (c_bit c 274 row)) - ((c_bit c 18 row) * ((c_bit c 274 row) + (c_bit c 274 row)))) + (c_bit c 81 row)) - ((((c_bit c 18 row) + (c_bit c 274 row)) - ((c_bit c 18 row) * ((c_bit c 274 row) + (c_bit c 274 row)))) * ((c_bit c 81 row) + (c_bit c 81 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_332_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_332 c row ↔ constraint_332 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_333 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 19 row) - (((((c_bit c 19 row) + (c_bit c 275 row)) - ((c_bit c 19 row) * ((c_bit c 275 row) + (c_bit c 275 row)))) + (c_bit c 82 row)) - ((((c_bit c 19 row) + (c_bit c 275 row)) - ((c_bit c 19 row) * ((c_bit c 275 row) + (c_bit c 275 row)))) * ((c_bit c 82 row) + (c_bit c 82 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_333_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_333 c row ↔ constraint_333 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_334 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 20 row) - (((((c_bit c 20 row) + (c_bit c 276 row)) - ((c_bit c 20 row) * ((c_bit c 276 row) + (c_bit c 276 row)))) + (c_bit c 83 row)) - ((((c_bit c 20 row) + (c_bit c 276 row)) - ((c_bit c 20 row) * ((c_bit c 276 row) + (c_bit c 276 row)))) * ((c_bit c 83 row) + (c_bit c 83 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_334_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_334 c row ↔ constraint_334 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_335 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 21 row) - (((((c_bit c 21 row) + (c_bit c 277 row)) - ((c_bit c 21 row) * ((c_bit c 277 row) + (c_bit c 277 row)))) + (c_bit c 84 row)) - ((((c_bit c 21 row) + (c_bit c 277 row)) - ((c_bit c 21 row) * ((c_bit c 277 row) + (c_bit c 277 row)))) * ((c_bit c 84 row) + (c_bit c 84 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_335_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_335 c row ↔ constraint_335 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_336 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 22 row) - (((((c_bit c 22 row) + (c_bit c 278 row)) - ((c_bit c 22 row) * ((c_bit c 278 row) + (c_bit c 278 row)))) + (c_bit c 85 row)) - ((((c_bit c 22 row) + (c_bit c 278 row)) - ((c_bit c 22 row) * ((c_bit c 278 row) + (c_bit c 278 row)))) * ((c_bit c 85 row) + (c_bit c 85 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_336_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_336 c row ↔ constraint_336 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_337 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 23 row) - (((((c_bit c 23 row) + (c_bit c 279 row)) - ((c_bit c 23 row) * ((c_bit c 279 row) + (c_bit c 279 row)))) + (c_bit c 86 row)) - ((((c_bit c 23 row) + (c_bit c 279 row)) - ((c_bit c 23 row) * ((c_bit c 279 row) + (c_bit c 279 row)))) * ((c_bit c 86 row) + (c_bit c 86 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_337_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_337 c row ↔ constraint_337 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_338 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 24 row) - (((((c_bit c 24 row) + (c_bit c 280 row)) - ((c_bit c 24 row) * ((c_bit c 280 row) + (c_bit c 280 row)))) + (c_bit c 87 row)) - ((((c_bit c 24 row) + (c_bit c 280 row)) - ((c_bit c 24 row) * ((c_bit c 280 row) + (c_bit c 280 row)))) * ((c_bit c 87 row) + (c_bit c 87 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_338_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_338 c row ↔ constraint_338 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_339 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 25 row) - (((((c_bit c 25 row) + (c_bit c 281 row)) - ((c_bit c 25 row) * ((c_bit c 281 row) + (c_bit c 281 row)))) + (c_bit c 88 row)) - ((((c_bit c 25 row) + (c_bit c 281 row)) - ((c_bit c 25 row) * ((c_bit c 281 row) + (c_bit c 281 row)))) * ((c_bit c 88 row) + (c_bit c 88 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_339_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_339 c row ↔ constraint_339 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_340 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 26 row) - (((((c_bit c 26 row) + (c_bit c 282 row)) - ((c_bit c 26 row) * ((c_bit c 282 row) + (c_bit c 282 row)))) + (c_bit c 89 row)) - ((((c_bit c 26 row) + (c_bit c 282 row)) - ((c_bit c 26 row) * ((c_bit c 282 row) + (c_bit c 282 row)))) * ((c_bit c 89 row) + (c_bit c 89 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_340_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_340 c row ↔ constraint_340 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_341 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 27 row) - (((((c_bit c 27 row) + (c_bit c 283 row)) - ((c_bit c 27 row) * ((c_bit c 283 row) + (c_bit c 283 row)))) + (c_bit c 90 row)) - ((((c_bit c 27 row) + (c_bit c 283 row)) - ((c_bit c 27 row) * ((c_bit c 283 row) + (c_bit c 283 row)))) * ((c_bit c 90 row) + (c_bit c 90 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_341_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_341 c row ↔ constraint_341 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_342 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 28 row) - (((((c_bit c 28 row) + (c_bit c 284 row)) - ((c_bit c 28 row) * ((c_bit c 284 row) + (c_bit c 284 row)))) + (c_bit c 91 row)) - ((((c_bit c 28 row) + (c_bit c 284 row)) - ((c_bit c 28 row) * ((c_bit c 284 row) + (c_bit c 284 row)))) * ((c_bit c 91 row) + (c_bit c 91 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_342_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_342 c row ↔ constraint_342 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_343 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 29 row) - (((((c_bit c 29 row) + (c_bit c 285 row)) - ((c_bit c 29 row) * ((c_bit c 285 row) + (c_bit c 285 row)))) + (c_bit c 92 row)) - ((((c_bit c 29 row) + (c_bit c 285 row)) - ((c_bit c 29 row) * ((c_bit c 285 row) + (c_bit c 285 row)))) * ((c_bit c 92 row) + (c_bit c 92 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_343_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_343 c row ↔ constraint_343 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_344 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 30 row) - (((((c_bit c 30 row) + (c_bit c 286 row)) - ((c_bit c 30 row) * ((c_bit c 286 row) + (c_bit c 286 row)))) + (c_bit c 93 row)) - ((((c_bit c 30 row) + (c_bit c 286 row)) - ((c_bit c 30 row) * ((c_bit c 286 row) + (c_bit c 286 row)))) * ((c_bit c 93 row) + (c_bit c 93 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_344_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_344 c row ↔ constraint_344 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_345 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 31 row) - (((((c_bit c 31 row) + (c_bit c 287 row)) - ((c_bit c 31 row) * ((c_bit c 287 row) + (c_bit c 287 row)))) + (c_bit c 94 row)) - ((((c_bit c 31 row) + (c_bit c 287 row)) - ((c_bit c 31 row) * ((c_bit c 287 row) + (c_bit c 287 row)))) * ((c_bit c 94 row) + (c_bit c 94 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_345_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_345 c row ↔ constraint_345 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_346 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 32 row) - (((((c_bit c 32 row) + (c_bit c 288 row)) - ((c_bit c 32 row) * ((c_bit c 288 row) + (c_bit c 288 row)))) + (c_bit c 95 row)) - ((((c_bit c 32 row) + (c_bit c 288 row)) - ((c_bit c 32 row) * ((c_bit c 288 row) + (c_bit c 288 row)))) * ((c_bit c 95 row) + (c_bit c 95 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_346_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_346 c row ↔ constraint_346 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_347 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 33 row) - (((((c_bit c 33 row) + (c_bit c 289 row)) - ((c_bit c 33 row) * ((c_bit c 289 row) + (c_bit c 289 row)))) + (c_bit c 96 row)) - ((((c_bit c 33 row) + (c_bit c 289 row)) - ((c_bit c 33 row) * ((c_bit c 289 row) + (c_bit c 289 row)))) * ((c_bit c 96 row) + (c_bit c 96 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_347_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_347 c row ↔ constraint_347 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_348 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 34 row) - (((((c_bit c 34 row) + (c_bit c 290 row)) - ((c_bit c 34 row) * ((c_bit c 290 row) + (c_bit c 290 row)))) + (c_bit c 97 row)) - ((((c_bit c 34 row) + (c_bit c 290 row)) - ((c_bit c 34 row) * ((c_bit c 290 row) + (c_bit c 290 row)))) * ((c_bit c 97 row) + (c_bit c 97 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_348_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_348 c row ↔ constraint_348 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_349 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 35 row) - (((((c_bit c 35 row) + (c_bit c 291 row)) - ((c_bit c 35 row) * ((c_bit c 291 row) + (c_bit c 291 row)))) + (c_bit c 98 row)) - ((((c_bit c 35 row) + (c_bit c 291 row)) - ((c_bit c 35 row) * ((c_bit c 291 row) + (c_bit c 291 row)))) * ((c_bit c 98 row) + (c_bit c 98 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_349_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_349 c row ↔ constraint_349 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_350 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 36 row) - (((((c_bit c 36 row) + (c_bit c 292 row)) - ((c_bit c 36 row) * ((c_bit c 292 row) + (c_bit c 292 row)))) + (c_bit c 99 row)) - ((((c_bit c 36 row) + (c_bit c 292 row)) - ((c_bit c 36 row) * ((c_bit c 292 row) + (c_bit c 292 row)))) * ((c_bit c 99 row) + (c_bit c 99 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_350_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_350 c row ↔ constraint_350 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_351 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 37 row) - (((((c_bit c 37 row) + (c_bit c 293 row)) - ((c_bit c 37 row) * ((c_bit c 293 row) + (c_bit c 293 row)))) + (c_bit c 100 row)) - ((((c_bit c 37 row) + (c_bit c 293 row)) - ((c_bit c 37 row) * ((c_bit c 293 row) + (c_bit c 293 row)))) * ((c_bit c 100 row) + (c_bit c 100 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_351_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_351 c row ↔ constraint_351 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_352 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 38 row) - (((((c_bit c 38 row) + (c_bit c 294 row)) - ((c_bit c 38 row) * ((c_bit c 294 row) + (c_bit c 294 row)))) + (c_bit c 101 row)) - ((((c_bit c 38 row) + (c_bit c 294 row)) - ((c_bit c 38 row) * ((c_bit c 294 row) + (c_bit c 294 row)))) * ((c_bit c 101 row) + (c_bit c 101 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_352_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_352 c row ↔ constraint_352 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_353 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 39 row) - (((((c_bit c 39 row) + (c_bit c 295 row)) - ((c_bit c 39 row) * ((c_bit c 295 row) + (c_bit c 295 row)))) + (c_bit c 102 row)) - ((((c_bit c 39 row) + (c_bit c 295 row)) - ((c_bit c 39 row) * ((c_bit c 295 row) + (c_bit c 295 row)))) * ((c_bit c 102 row) + (c_bit c 102 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_353_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_353 c row ↔ constraint_353 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_354 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 40 row) - (((((c_bit c 40 row) + (c_bit c 296 row)) - ((c_bit c 40 row) * ((c_bit c 296 row) + (c_bit c 296 row)))) + (c_bit c 103 row)) - ((((c_bit c 40 row) + (c_bit c 296 row)) - ((c_bit c 40 row) * ((c_bit c 296 row) + (c_bit c 296 row)))) * ((c_bit c 103 row) + (c_bit c 103 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_354_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_354 c row ↔ constraint_354 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_355 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 41 row) - (((((c_bit c 41 row) + (c_bit c 297 row)) - ((c_bit c 41 row) * ((c_bit c 297 row) + (c_bit c 297 row)))) + (c_bit c 104 row)) - ((((c_bit c 41 row) + (c_bit c 297 row)) - ((c_bit c 41 row) * ((c_bit c 297 row) + (c_bit c 297 row)))) * ((c_bit c 104 row) + (c_bit c 104 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_355_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_355 c row ↔ constraint_355 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_356 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 42 row) - (((((c_bit c 42 row) + (c_bit c 298 row)) - ((c_bit c 42 row) * ((c_bit c 298 row) + (c_bit c 298 row)))) + (c_bit c 105 row)) - ((((c_bit c 42 row) + (c_bit c 298 row)) - ((c_bit c 42 row) * ((c_bit c 298 row) + (c_bit c 298 row)))) * ((c_bit c 105 row) + (c_bit c 105 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_356_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_356 c row ↔ constraint_356 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_357 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 43 row) - (((((c_bit c 43 row) + (c_bit c 299 row)) - ((c_bit c 43 row) * ((c_bit c 299 row) + (c_bit c 299 row)))) + (c_bit c 106 row)) - ((((c_bit c 43 row) + (c_bit c 299 row)) - ((c_bit c 43 row) * ((c_bit c 299 row) + (c_bit c 299 row)))) * ((c_bit c 106 row) + (c_bit c 106 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_357_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_357 c row ↔ constraint_357 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_358 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 44 row) - (((((c_bit c 44 row) + (c_bit c 300 row)) - ((c_bit c 44 row) * ((c_bit c 300 row) + (c_bit c 300 row)))) + (c_bit c 107 row)) - ((((c_bit c 44 row) + (c_bit c 300 row)) - ((c_bit c 44 row) * ((c_bit c 300 row) + (c_bit c 300 row)))) * ((c_bit c 107 row) + (c_bit c 107 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_358_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_358 c row ↔ constraint_358 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_359 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 45 row) - (((((c_bit c 45 row) + (c_bit c 301 row)) - ((c_bit c 45 row) * ((c_bit c 301 row) + (c_bit c 301 row)))) + (c_bit c 108 row)) - ((((c_bit c 45 row) + (c_bit c 301 row)) - ((c_bit c 45 row) * ((c_bit c 301 row) + (c_bit c 301 row)))) * ((c_bit c 108 row) + (c_bit c 108 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_359_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_359 c row ↔ constraint_359 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_360 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 46 row) - (((((c_bit c 46 row) + (c_bit c 302 row)) - ((c_bit c 46 row) * ((c_bit c 302 row) + (c_bit c 302 row)))) + (c_bit c 109 row)) - ((((c_bit c 46 row) + (c_bit c 302 row)) - ((c_bit c 46 row) * ((c_bit c 302 row) + (c_bit c 302 row)))) * ((c_bit c 109 row) + (c_bit c 109 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_360_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_360 c row ↔ constraint_360 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_361 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 47 row) - (((((c_bit c 47 row) + (c_bit c 303 row)) - ((c_bit c 47 row) * ((c_bit c 303 row) + (c_bit c 303 row)))) + (c_bit c 110 row)) - ((((c_bit c 47 row) + (c_bit c 303 row)) - ((c_bit c 47 row) * ((c_bit c 303 row) + (c_bit c 303 row)))) * ((c_bit c 110 row) + (c_bit c 110 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_361_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_361 c row ↔ constraint_361 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_362 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 48 row) - (((((c_bit c 48 row) + (c_bit c 304 row)) - ((c_bit c 48 row) * ((c_bit c 304 row) + (c_bit c 304 row)))) + (c_bit c 111 row)) - ((((c_bit c 48 row) + (c_bit c 304 row)) - ((c_bit c 48 row) * ((c_bit c 304 row) + (c_bit c 304 row)))) * ((c_bit c 111 row) + (c_bit c 111 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_362_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_362 c row ↔ constraint_362 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_363 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 49 row) - (((((c_bit c 49 row) + (c_bit c 305 row)) - ((c_bit c 49 row) * ((c_bit c 305 row) + (c_bit c 305 row)))) + (c_bit c 112 row)) - ((((c_bit c 49 row) + (c_bit c 305 row)) - ((c_bit c 49 row) * ((c_bit c 305 row) + (c_bit c 305 row)))) * ((c_bit c 112 row) + (c_bit c 112 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_363_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_363 c row ↔ constraint_363 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_364 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 50 row) - (((((c_bit c 50 row) + (c_bit c 306 row)) - ((c_bit c 50 row) * ((c_bit c 306 row) + (c_bit c 306 row)))) + (c_bit c 113 row)) - ((((c_bit c 50 row) + (c_bit c 306 row)) - ((c_bit c 50 row) * ((c_bit c 306 row) + (c_bit c 306 row)))) * ((c_bit c 113 row) + (c_bit c 113 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_364_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_364 c row ↔ constraint_364 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_365 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 51 row) - (((((c_bit c 51 row) + (c_bit c 307 row)) - ((c_bit c 51 row) * ((c_bit c 307 row) + (c_bit c 307 row)))) + (c_bit c 114 row)) - ((((c_bit c 51 row) + (c_bit c 307 row)) - ((c_bit c 51 row) * ((c_bit c 307 row) + (c_bit c 307 row)))) * ((c_bit c 114 row) + (c_bit c 114 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_365_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_365 c row ↔ constraint_365 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_366 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 52 row) - (((((c_bit c 52 row) + (c_bit c 308 row)) - ((c_bit c 52 row) * ((c_bit c 308 row) + (c_bit c 308 row)))) + (c_bit c 115 row)) - ((((c_bit c 52 row) + (c_bit c 308 row)) - ((c_bit c 52 row) * ((c_bit c 308 row) + (c_bit c 308 row)))) * ((c_bit c 115 row) + (c_bit c 115 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_366_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_366 c row ↔ constraint_366 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_367 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 53 row) - (((((c_bit c 53 row) + (c_bit c 309 row)) - ((c_bit c 53 row) * ((c_bit c 309 row) + (c_bit c 309 row)))) + (c_bit c 116 row)) - ((((c_bit c 53 row) + (c_bit c 309 row)) - ((c_bit c 53 row) * ((c_bit c 309 row) + (c_bit c 309 row)))) * ((c_bit c 116 row) + (c_bit c 116 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_367_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_367 c row ↔ constraint_367 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_368 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 54 row) - (((((c_bit c 54 row) + (c_bit c 310 row)) - ((c_bit c 54 row) * ((c_bit c 310 row) + (c_bit c 310 row)))) + (c_bit c 117 row)) - ((((c_bit c 54 row) + (c_bit c 310 row)) - ((c_bit c 54 row) * ((c_bit c 310 row) + (c_bit c 310 row)))) * ((c_bit c 117 row) + (c_bit c 117 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_368_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_368 c row ↔ constraint_368 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_369 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 55 row) - (((((c_bit c 55 row) + (c_bit c 311 row)) - ((c_bit c 55 row) * ((c_bit c 311 row) + (c_bit c 311 row)))) + (c_bit c 118 row)) - ((((c_bit c 55 row) + (c_bit c 311 row)) - ((c_bit c 55 row) * ((c_bit c 311 row) + (c_bit c 311 row)))) * ((c_bit c 118 row) + (c_bit c 118 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_369_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_369 c row ↔ constraint_369 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_370 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 56 row) - (((((c_bit c 56 row) + (c_bit c 312 row)) - ((c_bit c 56 row) * ((c_bit c 312 row) + (c_bit c 312 row)))) + (c_bit c 119 row)) - ((((c_bit c 56 row) + (c_bit c 312 row)) - ((c_bit c 56 row) * ((c_bit c 312 row) + (c_bit c 312 row)))) * ((c_bit c 119 row) + (c_bit c 119 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_370_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_370 c row ↔ constraint_370 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_371 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 57 row) - (((((c_bit c 57 row) + (c_bit c 313 row)) - ((c_bit c 57 row) * ((c_bit c 313 row) + (c_bit c 313 row)))) + (c_bit c 120 row)) - ((((c_bit c 57 row) + (c_bit c 313 row)) - ((c_bit c 57 row) * ((c_bit c 313 row) + (c_bit c 313 row)))) * ((c_bit c 120 row) + (c_bit c 120 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_371_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_371 c row ↔ constraint_371 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_372 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 58 row) - (((((c_bit c 58 row) + (c_bit c 314 row)) - ((c_bit c 58 row) * ((c_bit c 314 row) + (c_bit c 314 row)))) + (c_bit c 121 row)) - ((((c_bit c 58 row) + (c_bit c 314 row)) - ((c_bit c 58 row) * ((c_bit c 314 row) + (c_bit c 314 row)))) * ((c_bit c 121 row) + (c_bit c 121 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_372_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_372 c row ↔ constraint_372 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_373 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 59 row) - (((((c_bit c 59 row) + (c_bit c 315 row)) - ((c_bit c 59 row) * ((c_bit c 315 row) + (c_bit c 315 row)))) + (c_bit c 122 row)) - ((((c_bit c 59 row) + (c_bit c 315 row)) - ((c_bit c 59 row) * ((c_bit c 315 row) + (c_bit c 315 row)))) * ((c_bit c 122 row) + (c_bit c 122 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_373_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_373 c row ↔ constraint_373 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_374 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 60 row) - (((((c_bit c 60 row) + (c_bit c 316 row)) - ((c_bit c 60 row) * ((c_bit c 316 row) + (c_bit c 316 row)))) + (c_bit c 123 row)) - ((((c_bit c 60 row) + (c_bit c 316 row)) - ((c_bit c 60 row) * ((c_bit c 316 row) + (c_bit c 316 row)))) * ((c_bit c 123 row) + (c_bit c 123 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_374_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_374 c row ↔ constraint_374 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_375 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 61 row) - (((((c_bit c 61 row) + (c_bit c 317 row)) - ((c_bit c 61 row) * ((c_bit c 317 row) + (c_bit c 317 row)))) + (c_bit c 124 row)) - ((((c_bit c 61 row) + (c_bit c 317 row)) - ((c_bit c 61 row) * ((c_bit c 317 row) + (c_bit c 317 row)))) * ((c_bit c 124 row) + (c_bit c 124 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_375_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_375 c row ↔ constraint_375 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_376 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 62 row) - (((((c_bit c 62 row) + (c_bit c 318 row)) - ((c_bit c 62 row) * ((c_bit c 318 row) + (c_bit c 318 row)))) + (c_bit c 125 row)) - ((((c_bit c 62 row) + (c_bit c 318 row)) - ((c_bit c 62 row) * ((c_bit c 318 row) + (c_bit c 318 row)))) * ((c_bit c 125 row) + (c_bit c 125 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_376_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_376 c row ↔ constraint_376 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_377 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 63 row) - (((((c_bit c 63 row) + (c_bit c 319 row)) - ((c_bit c 63 row) * ((c_bit c 319 row) + (c_bit c 319 row)))) + (c_bit c 126 row)) - ((((c_bit c 63 row) + (c_bit c 319 row)) - ((c_bit c 63 row) * ((c_bit c 319 row) + (c_bit c 319 row)))) * ((c_bit c 126 row) + (c_bit c 126 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_377_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_377 c row ↔ constraint_377 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_378 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 64 row) * ((c_bit c 64 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_378_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_378 c row ↔ constraint_378 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_379 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 65 row) * ((c_bit c 65 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_379_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_379 c row ↔ constraint_379 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_380 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 66 row) * ((c_bit c 66 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_380_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_380 c row ↔ constraint_380 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_381 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 67 row) * ((c_bit c 67 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_381_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_381 c row ↔ constraint_381 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_382 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 68 row) * ((c_bit c 68 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_382_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_382 c row ↔ constraint_382 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_383 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 69 row) * ((c_bit c 69 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_383_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_383 c row ↔ constraint_383 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_384 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 70 row) * ((c_bit c 70 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_384_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_384 c row ↔ constraint_384 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_385 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 71 row) * ((c_bit c 71 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_385_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_385 c row ↔ constraint_385 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_386 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 72 row) * ((c_bit c 72 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_386_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_386 c row ↔ constraint_386 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_387 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 73 row) * ((c_bit c 73 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_387_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_387 c row ↔ constraint_387 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_388 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 74 row) * ((c_bit c 74 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_388_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_388 c row ↔ constraint_388 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_389 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 75 row) * ((c_bit c 75 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_389_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_389 c row ↔ constraint_389 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_390 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 76 row) * ((c_bit c 76 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_390_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_390 c row ↔ constraint_390 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_391 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 77 row) * ((c_bit c 77 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_391_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_391 c row ↔ constraint_391 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_392 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 78 row) * ((c_bit c 78 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_392_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_392 c row ↔ constraint_392 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_393 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 79 row) * ((c_bit c 79 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_393_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_393 c row ↔ constraint_393 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_394 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 80 row) * ((c_bit c 80 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_394_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_394 c row ↔ constraint_394 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_395 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 81 row) * ((c_bit c 81 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_395_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_395 c row ↔ constraint_395 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_396 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 82 row) * ((c_bit c 82 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_396_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_396 c row ↔ constraint_396 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_397 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 83 row) * ((c_bit c 83 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_397_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_397 c row ↔ constraint_397 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_398 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 84 row) * ((c_bit c 84 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_398_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_398 c row ↔ constraint_398 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_399 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 85 row) * ((c_bit c 85 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_399_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_399 c row ↔ constraint_399 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_400 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 86 row) * ((c_bit c 86 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_400_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_400 c row ↔ constraint_400 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_401 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 87 row) * ((c_bit c 87 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_401_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_401 c row ↔ constraint_401 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_402 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 88 row) * ((c_bit c 88 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_402_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_402 c row ↔ constraint_402 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_403 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 89 row) * ((c_bit c 89 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_403_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_403 c row ↔ constraint_403 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_404 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 90 row) * ((c_bit c 90 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_404_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_404 c row ↔ constraint_404 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_405 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 91 row) * ((c_bit c 91 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_405_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_405 c row ↔ constraint_405 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_406 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 92 row) * ((c_bit c 92 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_406_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_406 c row ↔ constraint_406 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_407 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 93 row) * ((c_bit c 93 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_407_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_407 c row ↔ constraint_407 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_408 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 94 row) * ((c_bit c 94 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_408_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_408 c row ↔ constraint_408 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_409 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 95 row) * ((c_bit c 95 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_409_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_409 c row ↔ constraint_409 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_410 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 96 row) * ((c_bit c 96 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_410_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_410 c row ↔ constraint_410 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_411 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 97 row) * ((c_bit c 97 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_411_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_411 c row ↔ constraint_411 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_412 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 98 row) * ((c_bit c 98 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_412_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_412 c row ↔ constraint_412 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_413 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 99 row) * ((c_bit c 99 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_413_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_413 c row ↔ constraint_413 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_414 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 100 row) * ((c_bit c 100 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_414_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_414 c row ↔ constraint_414 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_415 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 101 row) * ((c_bit c 101 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_415_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_415 c row ↔ constraint_415 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_416 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 102 row) * ((c_bit c 102 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_416_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_416 c row ↔ constraint_416 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_417 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 103 row) * ((c_bit c 103 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_417_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_417 c row ↔ constraint_417 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_418 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 104 row) * ((c_bit c 104 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_418_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_418 c row ↔ constraint_418 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_419 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 105 row) * ((c_bit c 105 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_419_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_419 c row ↔ constraint_419 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_420 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 106 row) * ((c_bit c 106 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_420_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_420 c row ↔ constraint_420 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_421 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 107 row) * ((c_bit c 107 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_421_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_421 c row ↔ constraint_421 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_422 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 108 row) * ((c_bit c 108 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_422_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_422 c row ↔ constraint_422 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_423 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 109 row) * ((c_bit c 109 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_423_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_423 c row ↔ constraint_423 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_424 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 110 row) * ((c_bit c 110 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_424_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_424 c row ↔ constraint_424 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_425 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 111 row) * ((c_bit c 111 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_425_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_425 c row ↔ constraint_425 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_426 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 112 row) * ((c_bit c 112 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_426_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_426 c row ↔ constraint_426 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_427 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 113 row) * ((c_bit c 113 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_427_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_427 c row ↔ constraint_427 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_428 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 114 row) * ((c_bit c 114 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_428_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_428 c row ↔ constraint_428 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_429 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 115 row) * ((c_bit c 115 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_429_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_429 c row ↔ constraint_429 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_430 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 116 row) * ((c_bit c 116 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_430_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_430 c row ↔ constraint_430 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_431 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 117 row) * ((c_bit c 117 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_431_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_431 c row ↔ constraint_431 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_432 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 118 row) * ((c_bit c 118 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_432_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_432 c row ↔ constraint_432 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_433 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 119 row) * ((c_bit c 119 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_433_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_433 c row ↔ constraint_433 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_434 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 120 row) * ((c_bit c 120 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_434_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_434 c row ↔ constraint_434 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_435 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 121 row) * ((c_bit c 121 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_435_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_435 c row ↔ constraint_435 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_436 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 122 row) * ((c_bit c 122 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_436_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_436 c row ↔ constraint_436 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_437 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 123 row) * ((c_bit c 123 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_437_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_437 c row ↔ constraint_437 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_438 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 124 row) * ((c_bit c 124 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_438_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_438 c row ↔ constraint_438 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_439 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 125 row) * ((c_bit c 125 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_439_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_439 c row ↔ constraint_439 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_440 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 126 row) * ((c_bit c 126 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_440_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_440 c row ↔ constraint_440 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_441 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 127 row) * ((c_bit c 127 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_441_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_441 c row ↔ constraint_441 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_442 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 64 row) - (((((c_bit c 64 row) + (c_bit c 0 row)) - ((c_bit c 64 row) * ((c_bit c 0 row) + (c_bit c 0 row)))) + (c_bit c 191 row)) - ((((c_bit c 64 row) + (c_bit c 0 row)) - ((c_bit c 64 row) * ((c_bit c 0 row) + (c_bit c 0 row)))) * ((c_bit c 191 row) + (c_bit c 191 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_442_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_442 c row ↔ constraint_442 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_443 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 65 row) - (((((c_bit c 65 row) + (c_bit c 1 row)) - ((c_bit c 65 row) * ((c_bit c 1 row) + (c_bit c 1 row)))) + (c_bit c 128 row)) - ((((c_bit c 65 row) + (c_bit c 1 row)) - ((c_bit c 65 row) * ((c_bit c 1 row) + (c_bit c 1 row)))) * ((c_bit c 128 row) + (c_bit c 128 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_443_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_443 c row ↔ constraint_443 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_444 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 66 row) - (((((c_bit c 66 row) + (c_bit c 2 row)) - ((c_bit c 66 row) * ((c_bit c 2 row) + (c_bit c 2 row)))) + (c_bit c 129 row)) - ((((c_bit c 66 row) + (c_bit c 2 row)) - ((c_bit c 66 row) * ((c_bit c 2 row) + (c_bit c 2 row)))) * ((c_bit c 129 row) + (c_bit c 129 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_444_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_444 c row ↔ constraint_444 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_445 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 67 row) - (((((c_bit c 67 row) + (c_bit c 3 row)) - ((c_bit c 67 row) * ((c_bit c 3 row) + (c_bit c 3 row)))) + (c_bit c 130 row)) - ((((c_bit c 67 row) + (c_bit c 3 row)) - ((c_bit c 67 row) * ((c_bit c 3 row) + (c_bit c 3 row)))) * ((c_bit c 130 row) + (c_bit c 130 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_445_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_445 c row ↔ constraint_445 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_446 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 68 row) - (((((c_bit c 68 row) + (c_bit c 4 row)) - ((c_bit c 68 row) * ((c_bit c 4 row) + (c_bit c 4 row)))) + (c_bit c 131 row)) - ((((c_bit c 68 row) + (c_bit c 4 row)) - ((c_bit c 68 row) * ((c_bit c 4 row) + (c_bit c 4 row)))) * ((c_bit c 131 row) + (c_bit c 131 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_446_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_446 c row ↔ constraint_446 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_447 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 69 row) - (((((c_bit c 69 row) + (c_bit c 5 row)) - ((c_bit c 69 row) * ((c_bit c 5 row) + (c_bit c 5 row)))) + (c_bit c 132 row)) - ((((c_bit c 69 row) + (c_bit c 5 row)) - ((c_bit c 69 row) * ((c_bit c 5 row) + (c_bit c 5 row)))) * ((c_bit c 132 row) + (c_bit c 132 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_447_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_447 c row ↔ constraint_447 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_448 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 70 row) - (((((c_bit c 70 row) + (c_bit c 6 row)) - ((c_bit c 70 row) * ((c_bit c 6 row) + (c_bit c 6 row)))) + (c_bit c 133 row)) - ((((c_bit c 70 row) + (c_bit c 6 row)) - ((c_bit c 70 row) * ((c_bit c 6 row) + (c_bit c 6 row)))) * ((c_bit c 133 row) + (c_bit c 133 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_448_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_448 c row ↔ constraint_448 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_449 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 71 row) - (((((c_bit c 71 row) + (c_bit c 7 row)) - ((c_bit c 71 row) * ((c_bit c 7 row) + (c_bit c 7 row)))) + (c_bit c 134 row)) - ((((c_bit c 71 row) + (c_bit c 7 row)) - ((c_bit c 71 row) * ((c_bit c 7 row) + (c_bit c 7 row)))) * ((c_bit c 134 row) + (c_bit c 134 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_449_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_449 c row ↔ constraint_449 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_450 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 72 row) - (((((c_bit c 72 row) + (c_bit c 8 row)) - ((c_bit c 72 row) * ((c_bit c 8 row) + (c_bit c 8 row)))) + (c_bit c 135 row)) - ((((c_bit c 72 row) + (c_bit c 8 row)) - ((c_bit c 72 row) * ((c_bit c 8 row) + (c_bit c 8 row)))) * ((c_bit c 135 row) + (c_bit c 135 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_450_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_450 c row ↔ constraint_450 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_451 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 73 row) - (((((c_bit c 73 row) + (c_bit c 9 row)) - ((c_bit c 73 row) * ((c_bit c 9 row) + (c_bit c 9 row)))) + (c_bit c 136 row)) - ((((c_bit c 73 row) + (c_bit c 9 row)) - ((c_bit c 73 row) * ((c_bit c 9 row) + (c_bit c 9 row)))) * ((c_bit c 136 row) + (c_bit c 136 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_451_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_451 c row ↔ constraint_451 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_452 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 74 row) - (((((c_bit c 74 row) + (c_bit c 10 row)) - ((c_bit c 74 row) * ((c_bit c 10 row) + (c_bit c 10 row)))) + (c_bit c 137 row)) - ((((c_bit c 74 row) + (c_bit c 10 row)) - ((c_bit c 74 row) * ((c_bit c 10 row) + (c_bit c 10 row)))) * ((c_bit c 137 row) + (c_bit c 137 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_452_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_452 c row ↔ constraint_452 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_453 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 75 row) - (((((c_bit c 75 row) + (c_bit c 11 row)) - ((c_bit c 75 row) * ((c_bit c 11 row) + (c_bit c 11 row)))) + (c_bit c 138 row)) - ((((c_bit c 75 row) + (c_bit c 11 row)) - ((c_bit c 75 row) * ((c_bit c 11 row) + (c_bit c 11 row)))) * ((c_bit c 138 row) + (c_bit c 138 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_453_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_453 c row ↔ constraint_453 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_454 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 76 row) - (((((c_bit c 76 row) + (c_bit c 12 row)) - ((c_bit c 76 row) * ((c_bit c 12 row) + (c_bit c 12 row)))) + (c_bit c 139 row)) - ((((c_bit c 76 row) + (c_bit c 12 row)) - ((c_bit c 76 row) * ((c_bit c 12 row) + (c_bit c 12 row)))) * ((c_bit c 139 row) + (c_bit c 139 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_454_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_454 c row ↔ constraint_454 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_455 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 77 row) - (((((c_bit c 77 row) + (c_bit c 13 row)) - ((c_bit c 77 row) * ((c_bit c 13 row) + (c_bit c 13 row)))) + (c_bit c 140 row)) - ((((c_bit c 77 row) + (c_bit c 13 row)) - ((c_bit c 77 row) * ((c_bit c 13 row) + (c_bit c 13 row)))) * ((c_bit c 140 row) + (c_bit c 140 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_455_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_455 c row ↔ constraint_455 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_456 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 78 row) - (((((c_bit c 78 row) + (c_bit c 14 row)) - ((c_bit c 78 row) * ((c_bit c 14 row) + (c_bit c 14 row)))) + (c_bit c 141 row)) - ((((c_bit c 78 row) + (c_bit c 14 row)) - ((c_bit c 78 row) * ((c_bit c 14 row) + (c_bit c 14 row)))) * ((c_bit c 141 row) + (c_bit c 141 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_456_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_456 c row ↔ constraint_456 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_457 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 79 row) - (((((c_bit c 79 row) + (c_bit c 15 row)) - ((c_bit c 79 row) * ((c_bit c 15 row) + (c_bit c 15 row)))) + (c_bit c 142 row)) - ((((c_bit c 79 row) + (c_bit c 15 row)) - ((c_bit c 79 row) * ((c_bit c 15 row) + (c_bit c 15 row)))) * ((c_bit c 142 row) + (c_bit c 142 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_457_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_457 c row ↔ constraint_457 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_458 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 80 row) - (((((c_bit c 80 row) + (c_bit c 16 row)) - ((c_bit c 80 row) * ((c_bit c 16 row) + (c_bit c 16 row)))) + (c_bit c 143 row)) - ((((c_bit c 80 row) + (c_bit c 16 row)) - ((c_bit c 80 row) * ((c_bit c 16 row) + (c_bit c 16 row)))) * ((c_bit c 143 row) + (c_bit c 143 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_458_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_458 c row ↔ constraint_458 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_459 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 81 row) - (((((c_bit c 81 row) + (c_bit c 17 row)) - ((c_bit c 81 row) * ((c_bit c 17 row) + (c_bit c 17 row)))) + (c_bit c 144 row)) - ((((c_bit c 81 row) + (c_bit c 17 row)) - ((c_bit c 81 row) * ((c_bit c 17 row) + (c_bit c 17 row)))) * ((c_bit c 144 row) + (c_bit c 144 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_459_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_459 c row ↔ constraint_459 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_460 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 82 row) - (((((c_bit c 82 row) + (c_bit c 18 row)) - ((c_bit c 82 row) * ((c_bit c 18 row) + (c_bit c 18 row)))) + (c_bit c 145 row)) - ((((c_bit c 82 row) + (c_bit c 18 row)) - ((c_bit c 82 row) * ((c_bit c 18 row) + (c_bit c 18 row)))) * ((c_bit c 145 row) + (c_bit c 145 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_460_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_460 c row ↔ constraint_460 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_461 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 83 row) - (((((c_bit c 83 row) + (c_bit c 19 row)) - ((c_bit c 83 row) * ((c_bit c 19 row) + (c_bit c 19 row)))) + (c_bit c 146 row)) - ((((c_bit c 83 row) + (c_bit c 19 row)) - ((c_bit c 83 row) * ((c_bit c 19 row) + (c_bit c 19 row)))) * ((c_bit c 146 row) + (c_bit c 146 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_461_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_461 c row ↔ constraint_461 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_462 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 84 row) - (((((c_bit c 84 row) + (c_bit c 20 row)) - ((c_bit c 84 row) * ((c_bit c 20 row) + (c_bit c 20 row)))) + (c_bit c 147 row)) - ((((c_bit c 84 row) + (c_bit c 20 row)) - ((c_bit c 84 row) * ((c_bit c 20 row) + (c_bit c 20 row)))) * ((c_bit c 147 row) + (c_bit c 147 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_462_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_462 c row ↔ constraint_462 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_463 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 85 row) - (((((c_bit c 85 row) + (c_bit c 21 row)) - ((c_bit c 85 row) * ((c_bit c 21 row) + (c_bit c 21 row)))) + (c_bit c 148 row)) - ((((c_bit c 85 row) + (c_bit c 21 row)) - ((c_bit c 85 row) * ((c_bit c 21 row) + (c_bit c 21 row)))) * ((c_bit c 148 row) + (c_bit c 148 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_463_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_463 c row ↔ constraint_463 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_464 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 86 row) - (((((c_bit c 86 row) + (c_bit c 22 row)) - ((c_bit c 86 row) * ((c_bit c 22 row) + (c_bit c 22 row)))) + (c_bit c 149 row)) - ((((c_bit c 86 row) + (c_bit c 22 row)) - ((c_bit c 86 row) * ((c_bit c 22 row) + (c_bit c 22 row)))) * ((c_bit c 149 row) + (c_bit c 149 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_464_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_464 c row ↔ constraint_464 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_465 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 87 row) - (((((c_bit c 87 row) + (c_bit c 23 row)) - ((c_bit c 87 row) * ((c_bit c 23 row) + (c_bit c 23 row)))) + (c_bit c 150 row)) - ((((c_bit c 87 row) + (c_bit c 23 row)) - ((c_bit c 87 row) * ((c_bit c 23 row) + (c_bit c 23 row)))) * ((c_bit c 150 row) + (c_bit c 150 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_465_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_465 c row ↔ constraint_465 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_466 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 88 row) - (((((c_bit c 88 row) + (c_bit c 24 row)) - ((c_bit c 88 row) * ((c_bit c 24 row) + (c_bit c 24 row)))) + (c_bit c 151 row)) - ((((c_bit c 88 row) + (c_bit c 24 row)) - ((c_bit c 88 row) * ((c_bit c 24 row) + (c_bit c 24 row)))) * ((c_bit c 151 row) + (c_bit c 151 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_466_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_466 c row ↔ constraint_466 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_467 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 89 row) - (((((c_bit c 89 row) + (c_bit c 25 row)) - ((c_bit c 89 row) * ((c_bit c 25 row) + (c_bit c 25 row)))) + (c_bit c 152 row)) - ((((c_bit c 89 row) + (c_bit c 25 row)) - ((c_bit c 89 row) * ((c_bit c 25 row) + (c_bit c 25 row)))) * ((c_bit c 152 row) + (c_bit c 152 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_467_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_467 c row ↔ constraint_467 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_468 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 90 row) - (((((c_bit c 90 row) + (c_bit c 26 row)) - ((c_bit c 90 row) * ((c_bit c 26 row) + (c_bit c 26 row)))) + (c_bit c 153 row)) - ((((c_bit c 90 row) + (c_bit c 26 row)) - ((c_bit c 90 row) * ((c_bit c 26 row) + (c_bit c 26 row)))) * ((c_bit c 153 row) + (c_bit c 153 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_468_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_468 c row ↔ constraint_468 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_469 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 91 row) - (((((c_bit c 91 row) + (c_bit c 27 row)) - ((c_bit c 91 row) * ((c_bit c 27 row) + (c_bit c 27 row)))) + (c_bit c 154 row)) - ((((c_bit c 91 row) + (c_bit c 27 row)) - ((c_bit c 91 row) * ((c_bit c 27 row) + (c_bit c 27 row)))) * ((c_bit c 154 row) + (c_bit c 154 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_469_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_469 c row ↔ constraint_469 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_470 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 92 row) - (((((c_bit c 92 row) + (c_bit c 28 row)) - ((c_bit c 92 row) * ((c_bit c 28 row) + (c_bit c 28 row)))) + (c_bit c 155 row)) - ((((c_bit c 92 row) + (c_bit c 28 row)) - ((c_bit c 92 row) * ((c_bit c 28 row) + (c_bit c 28 row)))) * ((c_bit c 155 row) + (c_bit c 155 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_470_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_470 c row ↔ constraint_470 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_471 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 93 row) - (((((c_bit c 93 row) + (c_bit c 29 row)) - ((c_bit c 93 row) * ((c_bit c 29 row) + (c_bit c 29 row)))) + (c_bit c 156 row)) - ((((c_bit c 93 row) + (c_bit c 29 row)) - ((c_bit c 93 row) * ((c_bit c 29 row) + (c_bit c 29 row)))) * ((c_bit c 156 row) + (c_bit c 156 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_471_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_471 c row ↔ constraint_471 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_472 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 94 row) - (((((c_bit c 94 row) + (c_bit c 30 row)) - ((c_bit c 94 row) * ((c_bit c 30 row) + (c_bit c 30 row)))) + (c_bit c 157 row)) - ((((c_bit c 94 row) + (c_bit c 30 row)) - ((c_bit c 94 row) * ((c_bit c 30 row) + (c_bit c 30 row)))) * ((c_bit c 157 row) + (c_bit c 157 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_472_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_472 c row ↔ constraint_472 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_473 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 95 row) - (((((c_bit c 95 row) + (c_bit c 31 row)) - ((c_bit c 95 row) * ((c_bit c 31 row) + (c_bit c 31 row)))) + (c_bit c 158 row)) - ((((c_bit c 95 row) + (c_bit c 31 row)) - ((c_bit c 95 row) * ((c_bit c 31 row) + (c_bit c 31 row)))) * ((c_bit c 158 row) + (c_bit c 158 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_473_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_473 c row ↔ constraint_473 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_474 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 96 row) - (((((c_bit c 96 row) + (c_bit c 32 row)) - ((c_bit c 96 row) * ((c_bit c 32 row) + (c_bit c 32 row)))) + (c_bit c 159 row)) - ((((c_bit c 96 row) + (c_bit c 32 row)) - ((c_bit c 96 row) * ((c_bit c 32 row) + (c_bit c 32 row)))) * ((c_bit c 159 row) + (c_bit c 159 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_474_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_474 c row ↔ constraint_474 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_475 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 97 row) - (((((c_bit c 97 row) + (c_bit c 33 row)) - ((c_bit c 97 row) * ((c_bit c 33 row) + (c_bit c 33 row)))) + (c_bit c 160 row)) - ((((c_bit c 97 row) + (c_bit c 33 row)) - ((c_bit c 97 row) * ((c_bit c 33 row) + (c_bit c 33 row)))) * ((c_bit c 160 row) + (c_bit c 160 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_475_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_475 c row ↔ constraint_475 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_476 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 98 row) - (((((c_bit c 98 row) + (c_bit c 34 row)) - ((c_bit c 98 row) * ((c_bit c 34 row) + (c_bit c 34 row)))) + (c_bit c 161 row)) - ((((c_bit c 98 row) + (c_bit c 34 row)) - ((c_bit c 98 row) * ((c_bit c 34 row) + (c_bit c 34 row)))) * ((c_bit c 161 row) + (c_bit c 161 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_476_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_476 c row ↔ constraint_476 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_477 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 99 row) - (((((c_bit c 99 row) + (c_bit c 35 row)) - ((c_bit c 99 row) * ((c_bit c 35 row) + (c_bit c 35 row)))) + (c_bit c 162 row)) - ((((c_bit c 99 row) + (c_bit c 35 row)) - ((c_bit c 99 row) * ((c_bit c 35 row) + (c_bit c 35 row)))) * ((c_bit c 162 row) + (c_bit c 162 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_477_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_477 c row ↔ constraint_477 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_478 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 100 row) - (((((c_bit c 100 row) + (c_bit c 36 row)) - ((c_bit c 100 row) * ((c_bit c 36 row) + (c_bit c 36 row)))) + (c_bit c 163 row)) - ((((c_bit c 100 row) + (c_bit c 36 row)) - ((c_bit c 100 row) * ((c_bit c 36 row) + (c_bit c 36 row)))) * ((c_bit c 163 row) + (c_bit c 163 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_478_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_478 c row ↔ constraint_478 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_479 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 101 row) - (((((c_bit c 101 row) + (c_bit c 37 row)) - ((c_bit c 101 row) * ((c_bit c 37 row) + (c_bit c 37 row)))) + (c_bit c 164 row)) - ((((c_bit c 101 row) + (c_bit c 37 row)) - ((c_bit c 101 row) * ((c_bit c 37 row) + (c_bit c 37 row)))) * ((c_bit c 164 row) + (c_bit c 164 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_479_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_479 c row ↔ constraint_479 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_480 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 102 row) - (((((c_bit c 102 row) + (c_bit c 38 row)) - ((c_bit c 102 row) * ((c_bit c 38 row) + (c_bit c 38 row)))) + (c_bit c 165 row)) - ((((c_bit c 102 row) + (c_bit c 38 row)) - ((c_bit c 102 row) * ((c_bit c 38 row) + (c_bit c 38 row)))) * ((c_bit c 165 row) + (c_bit c 165 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_480_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_480 c row ↔ constraint_480 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_481 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 103 row) - (((((c_bit c 103 row) + (c_bit c 39 row)) - ((c_bit c 103 row) * ((c_bit c 39 row) + (c_bit c 39 row)))) + (c_bit c 166 row)) - ((((c_bit c 103 row) + (c_bit c 39 row)) - ((c_bit c 103 row) * ((c_bit c 39 row) + (c_bit c 39 row)))) * ((c_bit c 166 row) + (c_bit c 166 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_481_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_481 c row ↔ constraint_481 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_482 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 104 row) - (((((c_bit c 104 row) + (c_bit c 40 row)) - ((c_bit c 104 row) * ((c_bit c 40 row) + (c_bit c 40 row)))) + (c_bit c 167 row)) - ((((c_bit c 104 row) + (c_bit c 40 row)) - ((c_bit c 104 row) * ((c_bit c 40 row) + (c_bit c 40 row)))) * ((c_bit c 167 row) + (c_bit c 167 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_482_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_482 c row ↔ constraint_482 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_483 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 105 row) - (((((c_bit c 105 row) + (c_bit c 41 row)) - ((c_bit c 105 row) * ((c_bit c 41 row) + (c_bit c 41 row)))) + (c_bit c 168 row)) - ((((c_bit c 105 row) + (c_bit c 41 row)) - ((c_bit c 105 row) * ((c_bit c 41 row) + (c_bit c 41 row)))) * ((c_bit c 168 row) + (c_bit c 168 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_483_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_483 c row ↔ constraint_483 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_484 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 106 row) - (((((c_bit c 106 row) + (c_bit c 42 row)) - ((c_bit c 106 row) * ((c_bit c 42 row) + (c_bit c 42 row)))) + (c_bit c 169 row)) - ((((c_bit c 106 row) + (c_bit c 42 row)) - ((c_bit c 106 row) * ((c_bit c 42 row) + (c_bit c 42 row)))) * ((c_bit c 169 row) + (c_bit c 169 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_484_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_484 c row ↔ constraint_484 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_485 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 107 row) - (((((c_bit c 107 row) + (c_bit c 43 row)) - ((c_bit c 107 row) * ((c_bit c 43 row) + (c_bit c 43 row)))) + (c_bit c 170 row)) - ((((c_bit c 107 row) + (c_bit c 43 row)) - ((c_bit c 107 row) * ((c_bit c 43 row) + (c_bit c 43 row)))) * ((c_bit c 170 row) + (c_bit c 170 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_485_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_485 c row ↔ constraint_485 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_486 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 108 row) - (((((c_bit c 108 row) + (c_bit c 44 row)) - ((c_bit c 108 row) * ((c_bit c 44 row) + (c_bit c 44 row)))) + (c_bit c 171 row)) - ((((c_bit c 108 row) + (c_bit c 44 row)) - ((c_bit c 108 row) * ((c_bit c 44 row) + (c_bit c 44 row)))) * ((c_bit c 171 row) + (c_bit c 171 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_486_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_486 c row ↔ constraint_486 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_487 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 109 row) - (((((c_bit c 109 row) + (c_bit c 45 row)) - ((c_bit c 109 row) * ((c_bit c 45 row) + (c_bit c 45 row)))) + (c_bit c 172 row)) - ((((c_bit c 109 row) + (c_bit c 45 row)) - ((c_bit c 109 row) * ((c_bit c 45 row) + (c_bit c 45 row)))) * ((c_bit c 172 row) + (c_bit c 172 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_487_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_487 c row ↔ constraint_487 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_488 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 110 row) - (((((c_bit c 110 row) + (c_bit c 46 row)) - ((c_bit c 110 row) * ((c_bit c 46 row) + (c_bit c 46 row)))) + (c_bit c 173 row)) - ((((c_bit c 110 row) + (c_bit c 46 row)) - ((c_bit c 110 row) * ((c_bit c 46 row) + (c_bit c 46 row)))) * ((c_bit c 173 row) + (c_bit c 173 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_488_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_488 c row ↔ constraint_488 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_489 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 111 row) - (((((c_bit c 111 row) + (c_bit c 47 row)) - ((c_bit c 111 row) * ((c_bit c 47 row) + (c_bit c 47 row)))) + (c_bit c 174 row)) - ((((c_bit c 111 row) + (c_bit c 47 row)) - ((c_bit c 111 row) * ((c_bit c 47 row) + (c_bit c 47 row)))) * ((c_bit c 174 row) + (c_bit c 174 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_489_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_489 c row ↔ constraint_489 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_490 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 112 row) - (((((c_bit c 112 row) + (c_bit c 48 row)) - ((c_bit c 112 row) * ((c_bit c 48 row) + (c_bit c 48 row)))) + (c_bit c 175 row)) - ((((c_bit c 112 row) + (c_bit c 48 row)) - ((c_bit c 112 row) * ((c_bit c 48 row) + (c_bit c 48 row)))) * ((c_bit c 175 row) + (c_bit c 175 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_490_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_490 c row ↔ constraint_490 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_491 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 113 row) - (((((c_bit c 113 row) + (c_bit c 49 row)) - ((c_bit c 113 row) * ((c_bit c 49 row) + (c_bit c 49 row)))) + (c_bit c 176 row)) - ((((c_bit c 113 row) + (c_bit c 49 row)) - ((c_bit c 113 row) * ((c_bit c 49 row) + (c_bit c 49 row)))) * ((c_bit c 176 row) + (c_bit c 176 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_491_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_491 c row ↔ constraint_491 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_492 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 114 row) - (((((c_bit c 114 row) + (c_bit c 50 row)) - ((c_bit c 114 row) * ((c_bit c 50 row) + (c_bit c 50 row)))) + (c_bit c 177 row)) - ((((c_bit c 114 row) + (c_bit c 50 row)) - ((c_bit c 114 row) * ((c_bit c 50 row) + (c_bit c 50 row)))) * ((c_bit c 177 row) + (c_bit c 177 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_492_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_492 c row ↔ constraint_492 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_493 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 115 row) - (((((c_bit c 115 row) + (c_bit c 51 row)) - ((c_bit c 115 row) * ((c_bit c 51 row) + (c_bit c 51 row)))) + (c_bit c 178 row)) - ((((c_bit c 115 row) + (c_bit c 51 row)) - ((c_bit c 115 row) * ((c_bit c 51 row) + (c_bit c 51 row)))) * ((c_bit c 178 row) + (c_bit c 178 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_493_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_493 c row ↔ constraint_493 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_494 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 116 row) - (((((c_bit c 116 row) + (c_bit c 52 row)) - ((c_bit c 116 row) * ((c_bit c 52 row) + (c_bit c 52 row)))) + (c_bit c 179 row)) - ((((c_bit c 116 row) + (c_bit c 52 row)) - ((c_bit c 116 row) * ((c_bit c 52 row) + (c_bit c 52 row)))) * ((c_bit c 179 row) + (c_bit c 179 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_494_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_494 c row ↔ constraint_494 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_495 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 117 row) - (((((c_bit c 117 row) + (c_bit c 53 row)) - ((c_bit c 117 row) * ((c_bit c 53 row) + (c_bit c 53 row)))) + (c_bit c 180 row)) - ((((c_bit c 117 row) + (c_bit c 53 row)) - ((c_bit c 117 row) * ((c_bit c 53 row) + (c_bit c 53 row)))) * ((c_bit c 180 row) + (c_bit c 180 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_495_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_495 c row ↔ constraint_495 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_496 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 118 row) - (((((c_bit c 118 row) + (c_bit c 54 row)) - ((c_bit c 118 row) * ((c_bit c 54 row) + (c_bit c 54 row)))) + (c_bit c 181 row)) - ((((c_bit c 118 row) + (c_bit c 54 row)) - ((c_bit c 118 row) * ((c_bit c 54 row) + (c_bit c 54 row)))) * ((c_bit c 181 row) + (c_bit c 181 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_496_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_496 c row ↔ constraint_496 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_497 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 119 row) - (((((c_bit c 119 row) + (c_bit c 55 row)) - ((c_bit c 119 row) * ((c_bit c 55 row) + (c_bit c 55 row)))) + (c_bit c 182 row)) - ((((c_bit c 119 row) + (c_bit c 55 row)) - ((c_bit c 119 row) * ((c_bit c 55 row) + (c_bit c 55 row)))) * ((c_bit c 182 row) + (c_bit c 182 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_497_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_497 c row ↔ constraint_497 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_498 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 120 row) - (((((c_bit c 120 row) + (c_bit c 56 row)) - ((c_bit c 120 row) * ((c_bit c 56 row) + (c_bit c 56 row)))) + (c_bit c 183 row)) - ((((c_bit c 120 row) + (c_bit c 56 row)) - ((c_bit c 120 row) * ((c_bit c 56 row) + (c_bit c 56 row)))) * ((c_bit c 183 row) + (c_bit c 183 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_498_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_498 c row ↔ constraint_498 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_499 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 121 row) - (((((c_bit c 121 row) + (c_bit c 57 row)) - ((c_bit c 121 row) * ((c_bit c 57 row) + (c_bit c 57 row)))) + (c_bit c 184 row)) - ((((c_bit c 121 row) + (c_bit c 57 row)) - ((c_bit c 121 row) * ((c_bit c 57 row) + (c_bit c 57 row)))) * ((c_bit c 184 row) + (c_bit c 184 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_499_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_499 c row ↔ constraint_499 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_500 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 122 row) - (((((c_bit c 122 row) + (c_bit c 58 row)) - ((c_bit c 122 row) * ((c_bit c 58 row) + (c_bit c 58 row)))) + (c_bit c 185 row)) - ((((c_bit c 122 row) + (c_bit c 58 row)) - ((c_bit c 122 row) * ((c_bit c 58 row) + (c_bit c 58 row)))) * ((c_bit c 185 row) + (c_bit c 185 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_500_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_500 c row ↔ constraint_500 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_501 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 123 row) - (((((c_bit c 123 row) + (c_bit c 59 row)) - ((c_bit c 123 row) * ((c_bit c 59 row) + (c_bit c 59 row)))) + (c_bit c 186 row)) - ((((c_bit c 123 row) + (c_bit c 59 row)) - ((c_bit c 123 row) * ((c_bit c 59 row) + (c_bit c 59 row)))) * ((c_bit c 186 row) + (c_bit c 186 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_501_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_501 c row ↔ constraint_501 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_502 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 124 row) - (((((c_bit c 124 row) + (c_bit c 60 row)) - ((c_bit c 124 row) * ((c_bit c 60 row) + (c_bit c 60 row)))) + (c_bit c 187 row)) - ((((c_bit c 124 row) + (c_bit c 60 row)) - ((c_bit c 124 row) * ((c_bit c 60 row) + (c_bit c 60 row)))) * ((c_bit c 187 row) + (c_bit c 187 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_502_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_502 c row ↔ constraint_502 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_503 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 125 row) - (((((c_bit c 125 row) + (c_bit c 61 row)) - ((c_bit c 125 row) * ((c_bit c 61 row) + (c_bit c 61 row)))) + (c_bit c 188 row)) - ((((c_bit c 125 row) + (c_bit c 61 row)) - ((c_bit c 125 row) * ((c_bit c 61 row) + (c_bit c 61 row)))) * ((c_bit c 188 row) + (c_bit c 188 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_503_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_503 c row ↔ constraint_503 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_504 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 126 row) - (((((c_bit c 126 row) + (c_bit c 62 row)) - ((c_bit c 126 row) * ((c_bit c 62 row) + (c_bit c 62 row)))) + (c_bit c 189 row)) - ((((c_bit c 126 row) + (c_bit c 62 row)) - ((c_bit c 126 row) * ((c_bit c 62 row) + (c_bit c 62 row)))) * ((c_bit c 189 row) + (c_bit c 189 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_504_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_504 c row ↔ constraint_504 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_505 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 127 row) - (((((c_bit c 127 row) + (c_bit c 63 row)) - ((c_bit c 127 row) * ((c_bit c 63 row) + (c_bit c 63 row)))) + (c_bit c 190 row)) - ((((c_bit c 127 row) + (c_bit c 63 row)) - ((c_bit c 127 row) * ((c_bit c 63 row) + (c_bit c 63 row)))) * ((c_bit c 190 row) + (c_bit c 190 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_505_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_505 c row ↔ constraint_505 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_506 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 128 row) * ((c_bit c 128 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_506_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_506 c row ↔ constraint_506 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_507 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 129 row) * ((c_bit c 129 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_507_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_507 c row ↔ constraint_507 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_508 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 130 row) * ((c_bit c 130 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_508_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_508 c row ↔ constraint_508 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_509 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 131 row) * ((c_bit c 131 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_509_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_509 c row ↔ constraint_509 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_510 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 132 row) * ((c_bit c 132 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_510_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_510 c row ↔ constraint_510 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_511 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 133 row) * ((c_bit c 133 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_511_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_511 c row ↔ constraint_511 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_512 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 134 row) * ((c_bit c 134 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_512_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_512 c row ↔ constraint_512 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_513 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 135 row) * ((c_bit c 135 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_513_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_513 c row ↔ constraint_513 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_514 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 136 row) * ((c_bit c 136 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_514_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_514 c row ↔ constraint_514 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_515 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 137 row) * ((c_bit c 137 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_515_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_515 c row ↔ constraint_515 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_516 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 138 row) * ((c_bit c 138 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_516_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_516 c row ↔ constraint_516 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_517 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 139 row) * ((c_bit c 139 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_517_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_517 c row ↔ constraint_517 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_518 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 140 row) * ((c_bit c 140 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_518_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_518 c row ↔ constraint_518 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_519 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 141 row) * ((c_bit c 141 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_519_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_519 c row ↔ constraint_519 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_520 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 142 row) * ((c_bit c 142 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_520_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_520 c row ↔ constraint_520 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_521 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 143 row) * ((c_bit c 143 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_521_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_521 c row ↔ constraint_521 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_522 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 144 row) * ((c_bit c 144 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_522_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_522 c row ↔ constraint_522 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_523 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 145 row) * ((c_bit c 145 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_523_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_523 c row ↔ constraint_523 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_524 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 146 row) * ((c_bit c 146 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_524_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_524 c row ↔ constraint_524 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_525 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 147 row) * ((c_bit c 147 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_525_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_525 c row ↔ constraint_525 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_526 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 148 row) * ((c_bit c 148 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_526_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_526 c row ↔ constraint_526 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_527 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 149 row) * ((c_bit c 149 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_527_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_527 c row ↔ constraint_527 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_528 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 150 row) * ((c_bit c 150 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_528_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_528 c row ↔ constraint_528 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_529 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 151 row) * ((c_bit c 151 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_529_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_529 c row ↔ constraint_529 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_530 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 152 row) * ((c_bit c 152 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_530_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_530 c row ↔ constraint_530 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_531 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 153 row) * ((c_bit c 153 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_531_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_531 c row ↔ constraint_531 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_532 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 154 row) * ((c_bit c 154 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_532_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_532 c row ↔ constraint_532 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_533 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 155 row) * ((c_bit c 155 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_533_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_533 c row ↔ constraint_533 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_534 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 156 row) * ((c_bit c 156 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_534_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_534 c row ↔ constraint_534 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_535 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 157 row) * ((c_bit c 157 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_535_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_535 c row ↔ constraint_535 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_536 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 158 row) * ((c_bit c 158 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_536_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_536 c row ↔ constraint_536 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_537 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 159 row) * ((c_bit c 159 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_537_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_537 c row ↔ constraint_537 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_538 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 160 row) * ((c_bit c 160 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_538_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_538 c row ↔ constraint_538 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_539 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 161 row) * ((c_bit c 161 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_539_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_539 c row ↔ constraint_539 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_540 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 162 row) * ((c_bit c 162 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_540_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_540 c row ↔ constraint_540 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_541 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 163 row) * ((c_bit c 163 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_541_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_541 c row ↔ constraint_541 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_542 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 164 row) * ((c_bit c 164 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_542_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_542 c row ↔ constraint_542 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_543 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 165 row) * ((c_bit c 165 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_543_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_543 c row ↔ constraint_543 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_544 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 166 row) * ((c_bit c 166 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_544_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_544 c row ↔ constraint_544 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_545 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 167 row) * ((c_bit c 167 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_545_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_545 c row ↔ constraint_545 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_546 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 168 row) * ((c_bit c 168 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_546_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_546 c row ↔ constraint_546 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_547 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 169 row) * ((c_bit c 169 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_547_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_547 c row ↔ constraint_547 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_548 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 170 row) * ((c_bit c 170 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_548_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_548 c row ↔ constraint_548 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_549 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 171 row) * ((c_bit c 171 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_549_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_549 c row ↔ constraint_549 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_550 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 172 row) * ((c_bit c 172 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_550_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_550 c row ↔ constraint_550 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_551 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 173 row) * ((c_bit c 173 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_551_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_551 c row ↔ constraint_551 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_552 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 174 row) * ((c_bit c 174 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_552_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_552 c row ↔ constraint_552 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_553 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 175 row) * ((c_bit c 175 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_553_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_553 c row ↔ constraint_553 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_554 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 176 row) * ((c_bit c 176 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_554_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_554 c row ↔ constraint_554 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_555 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 177 row) * ((c_bit c 177 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_555_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_555 c row ↔ constraint_555 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_556 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 178 row) * ((c_bit c 178 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_556_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_556 c row ↔ constraint_556 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_557 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 179 row) * ((c_bit c 179 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_557_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_557 c row ↔ constraint_557 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_558 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 180 row) * ((c_bit c 180 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_558_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_558 c row ↔ constraint_558 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_559 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 181 row) * ((c_bit c 181 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_559_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_559 c row ↔ constraint_559 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_560 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 182 row) * ((c_bit c 182 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_560_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_560 c row ↔ constraint_560 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_561 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 183 row) * ((c_bit c 183 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_561_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_561 c row ↔ constraint_561 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_562 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 184 row) * ((c_bit c 184 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_562_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_562 c row ↔ constraint_562 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_563 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 185 row) * ((c_bit c 185 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_563_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_563 c row ↔ constraint_563 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_564 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 186 row) * ((c_bit c 186 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_564_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_564 c row ↔ constraint_564 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_565 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 187 row) * ((c_bit c 187 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_565_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_565 c row ↔ constraint_565 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_566 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 188 row) * ((c_bit c 188 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_566_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_566 c row ↔ constraint_566 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_567 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 189 row) * ((c_bit c 189 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_567_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_567 c row ↔ constraint_567 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_568 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 190 row) * ((c_bit c 190 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_568_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_568 c row ↔ constraint_568 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_569 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 191 row) * ((c_bit c 191 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_569_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_569 c row ↔ constraint_569 c row := by
    rfl

end constraint_simplification

end KeccakfPermAir.constraints
