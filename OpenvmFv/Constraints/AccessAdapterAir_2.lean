import OpenvmFv.Airs.AccessAdapterAir
import OpenvmFv.Extraction.AccessAdapterAir_2

namespace AccessAdapterAir_2.constraints

lemma constraint_0 [Field F] [Field ExtF]
  (c: Valid_AccessAdapterAir_2 F ExtF) (row: ℕ)
  (h: AccessAdapterAir_2.extraction.constraint_0 c row)
: c.is_split row 0 = 0 ∨ c.is_split row 0 - 1 = 0 := by
  unfold AccessAdapterAir_2.extraction.constraint_0 at h
  simp [openvm_encapsulation, *] at h
  exact h

lemma constraint_1 [Field F] [Field ExtF]
  (c: Valid_AccessAdapterAir_2 F ExtF) (row: ℕ)
  (h: AccessAdapterAir_2.extraction.constraint_1 c row)
: c.is_valid row 0 = 0 ∨ c.is_valid row 0 - 1 = 0 := by
  unfold AccessAdapterAir_2.extraction.constraint_1 at h
  simp [openvm_encapsulation, *] at h
  exact h

lemma constraint_2 [Field F] [Field ExtF]
  (c: Valid_AccessAdapterAir_2 F ExtF) (row: ℕ)
  (h: AccessAdapterAir_2.extraction.constraint_2 c row)
: c.is_right_larger row 0 = 0 ∨ c.is_right_larger row 0 - 1 = 0 := by
  unfold AccessAdapterAir_2.extraction.constraint_2 at h
  simp [openvm_encapsulation, *] at h
  exact h

lemma constraint_3 [Field F] [Field ExtF]
  (c: Valid_AccessAdapterAir_2 F ExtF) (row: ℕ)
  (h: AccessAdapterAir_2.extraction.constraint_3 c row)
: c.is_split row 0 = 0 ∨ c.left_timestamp row 0 - c.right_timestamp row 0 = 0 := by
  unfold AccessAdapterAir_2.extraction.constraint_3 at h
  simp [openvm_encapsulation, *] at h
  exact h

lemma constraint_4 [Field F] [Field ExtF]
  (c: Valid_AccessAdapterAir_2 F ExtF) (row: ℕ)
  (h: AccessAdapterAir_2.extraction.constraint_4 c row)
: c.is_valid row 0 = 0 ∨
  c.right_timestamp row 0 - c.left_timestamp row 0 + 536870911 -
      (c.lt_aux_0 row 0 + c.lt_aux_1 row 0 * 131072 + c.is_right_larger row 0 * 536870912) =
    0 := by
  unfold AccessAdapterAir_2.extraction.constraint_4 at h
  simp [openvm_encapsulation, *] at h
  exact h

lemma constraint_5 [Field F] [Field ExtF]
  (c: Valid_AccessAdapterAir_2 F ExtF) (row: ℕ)
  (h: AccessAdapterAir_2.extraction.constraint_5 c row)
: c.is_right_larger row 0 = 0 ∨ c.is_right_larger row 0 - 1 = 0 := by
  unfold AccessAdapterAir_2.extraction.constraint_5 at h
  simp [openvm_encapsulation, *] at h
  exact h

lemma constrain_interactions [Field F] [Field ExtF]
  (c: Valid_AccessAdapterAir_2 F ExtF)
  (h: AccessAdapterAir_2.extraction.constrain_interactions c)
: c.buses = fun index ↦
  if index = 1 then
    List.map
        (fun row ↦
          (2013265920 * (c.is_valid row 0 * (2 * c.is_split row 0 - 1)),
            [c.address.address_space row 0, c.address.pointer row 0, c.values_0 row 0, c.values_1 row 0,
              c.is_right_larger row 0 * c.right_timestamp row 0 +
                (1 - c.is_right_larger row 0) * c.left_timestamp row 0]))
        (List.range (c.last_row + 1)) ++
      (List.map
          (fun row ↦
            (c.is_valid row 0 * (2 * c.is_split row 0 - 1),
              [c.address.address_space row 0, c.address.pointer row 0, c.values_0 row 0, c.left_timestamp row 0]))
          (List.range (c.last_row + 1)) ++
        List.map
          (fun row ↦
            (c.is_valid row 0 * (2 * c.is_split row 0 - 1),
              [c.address.address_space row 0, c.address.pointer row 0 + 1, c.values_1 row 0, c.right_timestamp row 0]))
          (List.range (c.last_row + 1)))
  else
    if index = 4 then
      List.map (fun row ↦ (c.is_valid row 0, [c.lt_aux_0 row 0, 17])) (List.range (c.last_row + 1)) ++
        List.map (fun row ↦ (c.is_valid row 0, [c.lt_aux_1 row 0, 12])) (List.range (c.last_row + 1))
    else [] := by
  unfold AccessAdapterAir_2.extraction.constrain_interactions at h
  simp [openvm_encapsulation] at h
  exact h

end AccessAdapterAir_2.constraints
