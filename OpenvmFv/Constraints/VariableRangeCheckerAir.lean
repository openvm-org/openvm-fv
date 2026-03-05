import OpenvmFv.Airs.VariableRangeCheckerAir
import OpenvmFv.Extraction.VariableRangeCheckerAir
import OpenvmFv.Fundamentals.Interaction
import OpenvmFv.Util

import LeanZKCircuit.Interactions

namespace VariableRangeCheckerAir.constraints

  section constraint_simplification

    variable [Field F] [Field ExtF]

    section row_constraints

      @[VariableRangeCheckerAir_constraint_and_interaction_simplification]
      def constraint_0 (air : Valid_VariableRangeCheckerAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isFirstRow air row = 0 ∨ air.main_cols.value row 0 = 0

      @[VariableRangeCheckerAir_air_simplification]
      lemma constraint_0_of_extraction
          (air : Valid_VariableRangeCheckerAir F ExtF) (row : ℕ)
      : VariableRangeCheckerAir.extraction.constraint_0 air row ↔ constraint_0 air row := by
        simp_all [openvm_encapsulation,
                  VariableRangeCheckerAir_constraint_and_interaction_simplification]

      @[VariableRangeCheckerAir_constraint_and_interaction_simplification]
      def constraint_1 (air : Valid_VariableRangeCheckerAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isFirstRow air row = 0 ∨ air.main_cols.max_bits row 0 = 0

      @[VariableRangeCheckerAir_air_simplification]
      lemma constraint_1_of_extraction
          (air : Valid_VariableRangeCheckerAir F ExtF) (row : ℕ)
      : VariableRangeCheckerAir.extraction.constraint_1 air row ↔ constraint_1 air row := by
        simp_all [openvm_encapsulation,
                  VariableRangeCheckerAir_constraint_and_interaction_simplification]

      @[VariableRangeCheckerAir_constraint_and_interaction_simplification]
      def constraint_2 (air : Valid_VariableRangeCheckerAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isFirstRow air row = 0 ∨ air.main_cols.two_to_max_bits row 0 = 1

      @[VariableRangeCheckerAir_air_simplification]
      lemma constraint_2_of_extraction
          (air : Valid_VariableRangeCheckerAir F ExtF) (row : ℕ)
      : VariableRangeCheckerAir.extraction.constraint_2 air row ↔ constraint_2 air row := by
        simp_all [openvm_encapsulation,
                  VariableRangeCheckerAir_constraint_and_interaction_simplification]

      @[VariableRangeCheckerAir_constraint_and_interaction_simplification]
      def constraint_3 (air : Valid_VariableRangeCheckerAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isTransitionRow air row = 0 ∨
          air.main_cols.max_bits row 1 = air.main_cols.max_bits row 0 ∨
            air.main_cols.max_bits row 1 - air.main_cols.max_bits row 0 = 1

      @[VariableRangeCheckerAir_air_simplification]
      lemma constraint_3_of_extraction
          (air : Valid_VariableRangeCheckerAir F ExtF) (row : ℕ)
      : VariableRangeCheckerAir.extraction.constraint_3 air row ↔ constraint_3 air row := by
        simp_all [openvm_encapsulation,
                  VariableRangeCheckerAir_constraint_and_interaction_simplification]

      @[VariableRangeCheckerAir_constraint_and_interaction_simplification]
      def constraint_4 (air : Valid_VariableRangeCheckerAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isTransitionRow air row = 0 ∨
          air.main_cols.value row 1 = 0 ∨ air.main_cols.value row 1 = air.main_cols.value row 0 + 1

      @[VariableRangeCheckerAir_air_simplification]
      lemma constraint_4_of_extraction
          (air : Valid_VariableRangeCheckerAir F ExtF) (row : ℕ)
      : VariableRangeCheckerAir.extraction.constraint_4 air row ↔ constraint_4 air row := by
        simp_all [openvm_encapsulation,
                  VariableRangeCheckerAir_constraint_and_interaction_simplification]

      @[VariableRangeCheckerAir_constraint_and_interaction_simplification]
      def constraint_5 (air : Valid_VariableRangeCheckerAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isTransitionRow air row = 0 ∨
          air.main_cols.two_to_max_bits row 1 =
            air.main_cols.two_to_max_bits row 0 * (1 + (air.main_cols.max_bits row 1 - air.main_cols.max_bits row 0))

      @[VariableRangeCheckerAir_air_simplification]
      lemma constraint_5_of_extraction
          (air : Valid_VariableRangeCheckerAir F ExtF) (row : ℕ)
      : VariableRangeCheckerAir.extraction.constraint_5 air row ↔ constraint_5 air row := by
        simp_all [openvm_encapsulation,
                  VariableRangeCheckerAir_constraint_and_interaction_simplification]

      @[VariableRangeCheckerAir_constraint_and_interaction_simplification]
      def constraint_6 (air : Valid_VariableRangeCheckerAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isTransitionRow air row = 0 ∨
          air.main_cols.value row 0 + air.main_cols.two_to_max_bits row 0 + 1 =
            air.main_cols.value row 1 + air.main_cols.two_to_max_bits row 1

      @[VariableRangeCheckerAir_air_simplification]
      lemma constraint_6_of_extraction
          (air : Valid_VariableRangeCheckerAir F ExtF) (row : ℕ)
      : VariableRangeCheckerAir.extraction.constraint_6 air row ↔ constraint_6 air row := by
        simp_all [openvm_encapsulation,
                  VariableRangeCheckerAir_constraint_and_interaction_simplification]

      @[VariableRangeCheckerAir_constraint_and_interaction_simplification]
      def constraint_7 (air : Valid_VariableRangeCheckerAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isLastRow air row = 0 ∨ air.main_cols.value row 0 = 0

      @[VariableRangeCheckerAir_air_simplification]
      lemma constraint_7_of_extraction
          (air : Valid_VariableRangeCheckerAir F ExtF) (row : ℕ)
      : VariableRangeCheckerAir.extraction.constraint_7 air row ↔ constraint_7 air row := by
        simp_all [openvm_encapsulation,
                  VariableRangeCheckerAir_constraint_and_interaction_simplification]

      @[VariableRangeCheckerAir_constraint_and_interaction_simplification]
      def constraint_8 (air : Valid_VariableRangeCheckerAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isLastRow air row = 0 ∨ air.main_cols.max_bits row 0 = 18

      @[VariableRangeCheckerAir_air_simplification]
      lemma constraint_8_of_extraction
          (air : Valid_VariableRangeCheckerAir F ExtF) (row : ℕ)
      : VariableRangeCheckerAir.extraction.constraint_8 air row ↔ constraint_8 air row := by
        simp_all [openvm_encapsulation,
                  VariableRangeCheckerAir_constraint_and_interaction_simplification]

      @[VariableRangeCheckerAir_constraint_and_interaction_simplification]
      def constraint_9 (air : Valid_VariableRangeCheckerAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isLastRow air row = 0 ∨ air.main_cols.mult row 0 = 0

      @[VariableRangeCheckerAir_air_simplification]
      lemma constraint_9_of_extraction
          (air : Valid_VariableRangeCheckerAir F ExtF) (row : ℕ)
      : VariableRangeCheckerAir.extraction.constraint_9 air row ↔ constraint_9 air row := by
        simp_all [openvm_encapsulation,
                  VariableRangeCheckerAir_constraint_and_interaction_simplification]

    end row_constraints

    section interactions

      @[VariableRangeCheckerAir_constraint_and_interaction_simplification]
      def bus_3Bus_row (air : Valid_VariableRangeCheckerAir F ExtF) (row : ℕ) : List (F × List F) :=
        [(-air.main_cols.mult row 0, [air.main_cols.value row 0, air.main_cols.max_bits row 0])]

      lemma constrain_bus_3_interactions
        (air : Valid_VariableRangeCheckerAir F ExtF)
        (h : VariableRangeCheckerAir.extraction.constrain_interactions air)
      :
        air.buses 3 = (List.range (air.last_row + 1)).flatMap (λ row => bus_3Bus_row air row)
      := by
        unfold VariableRangeCheckerAir.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        simp [h]; clear h
        rfl

      def constrain_interactions (air : Valid_VariableRangeCheckerAir F ExtF) : Prop :=
        air.buses = fun index ↦
        if index = 3 then (List.range (air.last_row + 1)).flatMap (bus_3Bus_row air)
        else []

      @[VariableRangeCheckerAir_air_simplification]
      lemma constrain_interactions_of_extraction
        (air : Valid_VariableRangeCheckerAir F ExtF)
        (h : VariableRangeCheckerAir.extraction.constrain_interactions air)
      : constrain_interactions air := by
        unfold constrain_interactions
        unfold VariableRangeCheckerAir.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        simp [h]
        rfl

    end interactions

  end constraint_simplification

  section allHold

    variable [Field F] [Field ExtF]

    @[simp]
    def extracted_row_constraint_list
      [Field ExtF]
      (air : Valid_VariableRangeCheckerAir F ExtF)
      (row : ℕ)
    : List Prop :=
      [
        VariableRangeCheckerAir.extraction.constraint_0 air row,
        VariableRangeCheckerAir.extraction.constraint_1 air row,
        VariableRangeCheckerAir.extraction.constraint_2 air row,
        VariableRangeCheckerAir.extraction.constraint_3 air row,
        VariableRangeCheckerAir.extraction.constraint_4 air row,
        VariableRangeCheckerAir.extraction.constraint_5 air row,
        VariableRangeCheckerAir.extraction.constraint_6 air row,
        VariableRangeCheckerAir.extraction.constraint_7 air row,
        VariableRangeCheckerAir.extraction.constraint_8 air row,
        VariableRangeCheckerAir.extraction.constraint_9 air row
      ]

    @[simp]
    def allHold
      [Field ExtF]
      (air : Valid_VariableRangeCheckerAir F ExtF)
      (row : ℕ)
      (_ : row ≤ air.last_row)
    : Prop :=
      VariableRangeCheckerAir.extraction.constrain_interactions air ∧
      List.Forall (·) (extracted_row_constraint_list air row)

    @[simp]
    def row_constraint_list
      [Field ExtF]
      (air : Valid_VariableRangeCheckerAir F ExtF)
      (row : ℕ)
    : List Prop :=
      [
        constraint_0 air row,
        constraint_1 air row,
        constraint_2 air row,
        constraint_3 air row,
        constraint_4 air row,
        constraint_5 air row,
        constraint_6 air row,
        constraint_7 air row,
        constraint_8 air row,
        constraint_9 air row
      ]

    @[simp]
    def allHold_simplified
      [Field ExtF]
      (air : Valid_VariableRangeCheckerAir F ExtF)
      (row : ℕ)
      (_ : row ≤ air.last_row)
    : Prop :=
      constrain_interactions air ∧
      List.Forall (·) (row_constraint_list air row)

    omit [Field ExtF] in
    lemma allHold_simplified_of_allHold
      [Field ExtF]
      (air : Valid_VariableRangeCheckerAir F ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
    : allHold air row h_row ↔ allHold_simplified air row h_row := by
      unfold allHold allHold_simplified
      apply Iff.and
      . unfold VariableRangeCheckerAir.extraction.constrain_interactions
        simp [openvm_encapsulation]
        rfl
      . simp only [extracted_row_constraint_list,
                  row_constraint_list,
                  VariableRangeCheckerAir_air_simplification]

  end allHold

  section properties

    variable [Field ExtF]

    open BabyBear in
    /-- Rotation consistency: rotation 1 at row k equals rotation 0 at row k+1 -/
    def rotation_consistent (air : Valid_VariableRangeCheckerAir FBB ExtF) : Prop :=
      ∀ row,
        air.main_cols.value row 1 = air.main_cols.value (row + 1) 0 ∧
        air.main_cols.max_bits row 1 = air.main_cols.max_bits (row + 1) 0 ∧
        air.main_cols.two_to_max_bits row 1 = air.main_cols.two_to_max_bits (row + 1) 0

    /-- All constraints hold at every valid row -/
    def all_constraints_hold (air : Valid_VariableRangeCheckerAir FBB ExtF) : Prop :=
      ∀ row (h_row : row ≤ air.last_row), allHold_simplified air row h_row

    open BabyBear in
    -- Abbreviations
    private abbrev v_ (air : Valid_VariableRangeCheckerAir FBB ExtF) (row : ℕ) : FBB :=
      air.main_cols.value row 0
    private abbrev mb_ (air : Valid_VariableRangeCheckerAir FBB ExtF) (row : ℕ) : FBB :=
      air.main_cols.max_bits row 0
    private abbrev tmb_ (air : Valid_VariableRangeCheckerAir FBB ExtF) (row : ℕ) : FBB :=
      air.main_cols.two_to_max_bits row 0

    open BabyBear in
    private lemma first_row_values
        (air : Valid_VariableRangeCheckerAir FBB ExtF)
        (h_row : 0 ≤ air.last_row)
        (cstrs : allHold_simplified air 0 h_row)
    : v_ air 0 = 0 ∧ mb_ air 0 = 0 ∧ tmb_ air 0 = 1 := by
      obtain ⟨_, h0, h1, h2, _⟩ := cstrs
      simp [VariableRangeCheckerAir_constraint_and_interaction_simplification,
            Circuit.isFirstRow] at h0 h1 h2
      exact ⟨h0, h1, h2⟩

    open BabyBear in
    private lemma last_row_values
        (air : Valid_VariableRangeCheckerAir FBB ExtF)
        (cstrs : allHold_simplified air air.last_row (le_refl _))
    : v_ air air.last_row = 0 ∧ mb_ air air.last_row = 18 := by
      obtain ⟨_, _, _, _, _, _, _, _, h7, h8, _⟩ := cstrs
      simp [VariableRangeCheckerAir_constraint_and_interaction_simplification,
            Circuit.isLastRow,
            Valid_VariableRangeCheckerAir_last_row_project] at h7 h8
      exact ⟨h7, h8⟩

    open BabyBear in
    private lemma transition_facts
        (air : Valid_VariableRangeCheckerAir FBB ExtF)
        (row : ℕ) (h_row : row ≤ air.last_row) (h_trans : row < air.last_row)
        (cstrs : allHold_simplified air row h_row)
        (h_rot : rotation_consistent air)
    : (mb_ air (row+1) = mb_ air row ∨ mb_ air (row+1) - mb_ air row = 1) ∧
      (v_ air (row+1) = 0 ∨ v_ air (row+1) = v_ air row + 1) ∧
      (tmb_ air (row+1) = tmb_ air row * (1 + (mb_ air (row+1) - mb_ air row))) ∧
      (v_ air row + tmb_ air row + 1 = v_ air (row+1) + tmb_ air (row+1)) := by
      obtain ⟨_, _, _, _, h3, h4, h5, h6, _⟩ := cstrs
      simp [VariableRangeCheckerAir_constraint_and_interaction_simplification] at h3 h4 h5 h6
      have hrot := h_rot row
      rw [hrot.1] at h4 h6
      rw [hrot.2.1] at h3 h5
      rw [hrot.2.2] at h5 h6
      have h_not : row ≠ air.last_row := by omega
      simp [Circuit.isTransitionRow, Valid_VariableRangeCheckerAir_last_row_project, h_not] at h3 h4 h5 h6
      exact ⟨h3, h4, h5, h6⟩

    open BabyBear in
    /-- mb.val ≤ row for all rows (mb starts at 0, increments by at most 1) -/
    private lemma mb_bound_by_row
        (air : Valid_VariableRangeCheckerAir FBB ExtF)
        (h_all : all_constraints_hold air)
        (h_rot : rotation_consistent air)
        (h_lr : air.last_row + 1 < BB_prime)
        (row : ℕ) (h_row : row ≤ air.last_row)
    : (mb_ air row).val ≤ row := by
      induction row with
      | zero =>
        have ⟨_, hm, _⟩ := first_row_values air (by omega) (h_all 0 (by omega))
        have hm_val : (mb_ air 0).val = 0 := by
          have := congr_arg Fin.val hm
          simpa using this
        simp [hm_val]
      | succ k ih =>
        have hk : k ≤ air.last_row := by omega
        have h_trans : k < air.last_row := by omega
        have ⟨h3, _, _, _⟩ := transition_facts air k hk h_trans (h_all k hk) h_rot
        rcases h3 with h_eq | h_diff
        · have h_eq_val : (mb_ air (k + 1)).val = (mb_ air k).val := by
            have := congr_arg Fin.val h_eq
            simpa using this
          omega
        · have hmb_eq : mb_ air (k + 1) = 1 + mb_ air k := by
            exact eq_add_of_sub_eq h_diff
          have hmb_val : (mb_ air (k + 1)).val = (mb_ air k).val + 1 := by
            have hsmall : (mb_ air k).val + 1 < BB_prime := by
              have hmbk := ih hk
              omega
            have hsmall' : 1 + (mb_ air k).val < BB_prime := by simpa [add_comm] using hsmall
            have := congr_arg Fin.val hmb_eq
            simpa [Fin.val_add, Nat.mod_eq_of_lt hsmall', add_comm] using this
          omega

    open BabyBear in
    /-- mb does not decrease across transition rows -/
    private lemma mb_step_nondec
        (air : Valid_VariableRangeCheckerAir FBB ExtF)
        (h_all : all_constraints_hold air)
        (h_rot : rotation_consistent air)
        (h_lr : air.last_row + 1 < BB_prime)
        (k : ℕ) (hk : k < air.last_row)
    : (mb_ air k).val ≤ (mb_ air (k + 1)).val := by
      have hk' : k ≤ air.last_row := by omega
      have ⟨h3, _, _, _⟩ := transition_facts air k hk' hk (h_all k hk') h_rot
      rcases h3 with h_eq | h_diff
      · have := congr_arg Fin.val h_eq
        simpa using this.ge
      · have hmb_eq : mb_ air (k + 1) = 1 + mb_ air k := by
          exact eq_add_of_sub_eq h_diff
        have hmb_val : (mb_ air (k + 1)).val = (mb_ air k).val + 1 := by
          have hsmall : (mb_ air k).val + 1 < BB_prime := by
            have hmbk := mb_bound_by_row air h_all h_rot h_lr k hk'
            omega
          have hsmall' : 1 + (mb_ air k).val < BB_prime := by simpa [add_comm] using hsmall
          have := congr_arg Fin.val hmb_eq
          simpa [Fin.val_add, Nat.mod_eq_of_lt hsmall', add_comm] using this
        omega

    open BabyBear in
    /-- mb is monotone up to last_row -/
    private lemma mb_monotone
        (air : Valid_VariableRangeCheckerAir FBB ExtF)
        (h_all : all_constraints_hold air)
        (h_rot : rotation_consistent air)
        (h_lr : air.last_row + 1 < BB_prime)
        (i j : ℕ) (hij : i ≤ j) (hj : j ≤ air.last_row)
    : (mb_ air i).val ≤ (mb_ air j).val := by
      induction j with
      | zero =>
        have hi0 : i = 0 := by omega
        subst hi0
        omega
      | succ k ih =>
        by_cases hik : i ≤ k
        · have hk : k ≤ air.last_row := by omega
          have h1 := ih hik hk
          have h2 := mb_step_nondec air h_all h_rot h_lr k (by omega)
          omega
        · have hi : i = k + 1 := by omega
          subst hi
          omega

    open BabyBear in
    /-- Provable bound: mb.val ≤ 18 on all rows -/
    private lemma mb_le_18
        (air : Valid_VariableRangeCheckerAir FBB ExtF)
        (h_all : all_constraints_hold air)
        (h_rot : rotation_consistent air)
        (h_lr : air.last_row + 1 < BB_prime)
        (row : ℕ) (h_row : row ≤ air.last_row)
    : (mb_ air row).val ≤ 18 := by
      have hmono := mb_monotone air h_all h_rot h_lr row air.last_row h_row (le_refl _)
      have ⟨_, hlast⟩ := last_row_values air (h_all air.last_row (le_refl _))
      have hlast_val : (mb_ air air.last_row).val = 18 := by
        have := congr_arg Fin.val hlast
        norm_num at this
        simpa using this
      omega

    open BabyBear in
    /-- v.val ≤ row for all rows (v starts at 0, increments by at most 1 or resets) -/
    private lemma val_bound
        (air : Valid_VariableRangeCheckerAir FBB ExtF)
        (h_all : all_constraints_hold air)
        (h_rot : rotation_consistent air)
        (h_lr : air.last_row + 1 < BB_prime)
        (row : ℕ) (h_row : row ≤ air.last_row)
    : (v_ air row).val ≤ row := by
      induction row with
      | zero =>
        have ⟨hv, _, _⟩ := first_row_values air (by omega) (h_all 0 (by omega))
        simp [v_] at hv ⊢; rw [hv]
      | succ k ih =>
        have hk : k ≤ air.last_row := by omega
        have h_trans : k < air.last_row := by omega
        have ⟨_, h4, _, _⟩ := transition_facts air k hk h_trans (h_all k hk) h_rot
        rcases h4 with hv0 | hv1
        · -- v' = 0
          have : (v_ air (k+1)).val = 0 := by
            have := congr_arg Fin.val hv0; simpa using this
          omega
        · -- v' = v + 1
          have hih := ih hk
          have hv_small : (v_ air k).val < BB_prime - 1 := by omega
          have : (v_ air (k+1)).val = (v_ air k).val + 1 := by
            have := congr_arg Fin.val hv1
            simp [Fin.val_add] at this
            omega
          omega

    open BabyBear in
    /-- Counter identity in the field: v + tmb = ↑(row + 1) -/
    private lemma counter_field
        (air : Valid_VariableRangeCheckerAir FBB ExtF)
        (h_all : all_constraints_hold air)
        (h_rot : rotation_consistent air)
        (row : ℕ) (h_row : row ≤ air.last_row)
    : v_ air row + tmb_ air row = (↑(row + 1) : FBB) := by
      induction row with
      | zero =>
        have ⟨hv, _, ht⟩ := first_row_values air (by omega) (h_all 0 (by omega))
        simp [v_, tmb_] at hv ht ⊢; rw [hv, ht]; ring
      | succ k ih =>
        have hk : k ≤ air.last_row := by omega
        have ⟨_, _, _, h6⟩ := transition_facts air k hk (by omega) (h_all k hk) h_rot
        rw [← h6, ih hk]; push_cast; ring

    open BabyBear in
    /-- Counter identity in ℕ (using val_bound to eliminate wraparound) -/
    private lemma counter_nat
        (air : Valid_VariableRangeCheckerAir FBB ExtF)
        (h_all : all_constraints_hold air)
        (h_rot : rotation_consistent air)
        (h_lr : air.last_row + 1 < BB_prime)
        (row : ℕ) (h_row : row ≤ air.last_row)
    : (v_ air row).val + (tmb_ air row).val = row + 1 := by
      have hcf := counter_field air h_all h_rot row h_row
      have hcf_val := congr_arg Fin.val hcf
      have hvb := val_bound air h_all h_rot h_lr row h_row
      have hrow1_lt : row + 1 < BB_prime := by omega
      have hmod : ((v_ air row).val + (tmb_ air row).val) % BB_prime = row + 1 := by
        simpa [Fin.val_add, Fin.val_natCast, Nat.mod_eq_of_lt hrow1_lt] using hcf_val
      have hsum_lt_2p : (v_ air row).val + (tmb_ air row).val < 2 * BB_prime := by
        have hv_lt : (v_ air row).val < BB_prime := (v_ air row).isLt
        have ht_lt : (tmb_ air row).val < BB_prime := (tmb_ air row).isLt
        omega
      have hdiv_lt_two : (((v_ air row).val + (tmb_ air row).val) / BB_prime) < 2 := by
        have hp : 0 < BB_prime := by native_decide
        exact (Nat.div_lt_iff_lt_mul hp).2 (by simpa [two_mul] using hsum_lt_2p)
      have hdiv_cases : (((v_ air row).val + (tmb_ air row).val) / BB_prime) = 0 ∨
          (((v_ air row).val + (tmb_ air row).val) / BB_prime) = 1 := by
        omega
      have hdecomp :
          (v_ air row).val + (tmb_ air row).val =
            ((v_ air row).val + (tmb_ air row).val) % BB_prime +
              BB_prime * (((v_ air row).val + (tmb_ air row).val) / BB_prime) := by
        simpa [Nat.mul_comm] using (Nat.mod_add_div ((v_ air row).val + (tmb_ air row).val) BB_prime).symm
      rw [hmod] at hdecomp
      rcases hdiv_cases with hq | hq
      · rw [hq, mul_zero, add_zero] at hdecomp
        exact hdecomp
      · exfalso
        rw [hq, mul_one] at hdecomp
        have ht_le : (tmb_ air row).val ≤ BB_prime - 1 := Nat.le_pred_of_lt (tmb_ air row).isLt
        omega

    open BabyBear in
    /-- tmb.val = 2^(mb.val) -/
    private lemma tmb_eq_pow2
        (air : Valid_VariableRangeCheckerAir FBB ExtF)
        (h_all : all_constraints_hold air)
        (h_rot : rotation_consistent air)
        (row : ℕ) (h_row : row ≤ air.last_row)
        (h_mb_bound : ∀ r ≤ row, (mb_ air r).val ≤ 18)
    : (tmb_ air row).val = 2 ^ (mb_ air row).val := by
      induction row with
      | zero =>
        have ⟨_, hm, ht⟩ := first_row_values air (by omega) (h_all 0 (by omega))
        simp [mb_, tmb_] at hm ht ⊢
        rw [hm, ht]
        norm_num
      | succ k ih =>
        have hk : k ≤ air.last_row := by omega
        have ⟨h3, _, h5, _⟩ := transition_facts air k hk (by omega) (h_all k hk) h_rot
        have ih_eq := ih hk (fun r hr => h_mb_bound r (by omega))
        have hmb_k := h_mb_bound k (by omega)
        rcases h3 with hmb_eq | hmb_diff
        · -- mb stays
          rw [h5, hmb_eq, sub_self, add_zero, mul_one, ih_eq]
        · -- mb increments by 1
          have hmb_inc : (mb_ air (k+1)).val = (mb_ air k).val + 1 := by
            have := congr_arg Fin.val hmb_diff
            simp [Fin.val_sub] at this; omega
          have h_pow_small : 2 ^ (mb_ air k).val * 2 < BB_prime := by
            calc 2 ^ (mb_ air k).val * 2 = 2 ^ ((mb_ air k).val + 1) := by ring
              _ ≤ 2 ^ 19 := Nat.pow_le_pow_right (by omega) (by omega)
              _ < BB_prime := by norm_num
          rw [h5, hmb_diff, add_comm (1 : FBB) 1]
          simp [Fin.val_mul]
          rw [ih_eq, Nat.mod_eq_of_lt h_pow_small, hmb_inc]; ring

    open BabyBear in
    /-- mb cannot increment when v.val ≥ tmb.val -/
    private lemma mb_stays_when_v_ge_t
        (air : Valid_VariableRangeCheckerAir FBB ExtF)
        (h_all : all_constraints_hold air)
        (h_rot : rotation_consistent air)
        (h_mb_bound : ∀ r ≤ air.last_row, (mb_ air r).val ≤ 18)
        (j : ℕ) (hj : j ≤ air.last_row) (h_trans : j < air.last_row)
        (h_bad : (v_ air j).val ≥ (tmb_ air j).val)
    : mb_ air (j+1) = mb_ air j := by
      have ⟨h3, h4, h5, h6⟩ := transition_facts air j hj h_trans (h_all j hj) h_rot
      have h_tmb_j := tmb_eq_pow2 air h_all h_rot j hj (fun r hr => h_mb_bound r (by omega))
      have h_tmb_pos : (tmb_ air j).val > 0 := by rw [h_tmb_j]; positivity
      have h_tmb_small : (tmb_ air j).val * 2 < BB_prime := by
        rw [h_tmb_j]
        calc 2 ^ (mb_ air j).val * 2 ≤ 2 ^ 18 * 2 := by
              apply Nat.mul_le_mul_right; exact Nat.pow_le_pow_right (by omega) (h_mb_bound j hj)
          _ < BB_prime := by norm_num
      rcases h3 with h_eq | h_diff
      · exact h_eq
      · exfalso
        -- If mb increments: tmb' = 2*tmb, and from h6 + h4:
        rw [h_diff, add_comm (1 : FBB) 1] at h5
        rcases h4 with hv0 | hv1
        · -- v' = 0: h6 gives v + t + 1 = 2t, so v = t - 1
          rw [hv0, h5] at h6
          -- v + t + 1 = 0 + t * 2
          have h_eq : (v_ air j).val + (tmb_ air j).val + 1 = (tmb_ air j).val * 2 := by
            have := congr_arg Fin.val h6
            simp [Fin.val_add, Fin.val_mul] at this; omega
          -- v.val = t.val - 1 < t.val, contradicting h_bad
          omega
        · -- v' = v + 1: h6 gives v + t + 1 = (v+1) + 2t, so t = 2t, so t = 0
          rw [hv1, h5] at h6
          have : (tmb_ air j).val = 0 := by
            have := congr_arg Fin.val h6
            simp [Fin.val_add, Fin.val_mul] at this; omega
          omega

    open BabyBear in
    /-- Propagation: if v ≥ t at row j, then v(last_row) > 0 -/
    private lemma propagation
        (air : Valid_VariableRangeCheckerAir FBB ExtF)
        (h_all : all_constraints_hold air)
        (h_rot : rotation_consistent air)
        (h_lr : air.last_row + 1 < BB_prime)
        (h_mb_bound : ∀ r ≤ air.last_row, (mb_ air r).val ≤ 18)
        (j : ℕ) (hj : j ≤ air.last_row)
        (h_bad : (v_ air j).val ≥ (tmb_ air j).val)
    : False := by
      -- From counter_nat: v.val + t.val = row + 1 for all rows
      -- h_bad: v(j).val ≥ t(j).val, so j + 1 ≥ 2 * t(j).val
      have hcn_j := counter_nat air h_all h_rot h_lr j hj
      -- v(j).val = j + 1 - t(j).val, and v(j).val ≥ t(j).val means j + 1 ≥ 2*t(j).val
      have h_j_big : j + 1 ≥ 2 * (tmb_ air j).val := by omega
      -- mb stays from j to last_row (since at each intermediate row, v ≥ t still holds)
      -- t stays from j to last_row
      -- v increases by 1 each step
      -- So v(last_row).val = v(j).val + (last_row - j) = j + 1 - t + last_row - j = last_row + 1 - t
      -- But v(last_row) = 0 means last_row + 1 = t(j).val
      -- Combined with j + 1 ≥ 2*t(j).val: j + 1 ≥ 2*(last_row + 1), so j ≥ 2*last_row + 1
      -- But j ≤ last_row. Contradiction.
      -- To formalize, prove that from j to last_row: mb and tmb don't change, v increments by 1 each step
      suffices h_val_last : (v_ air air.last_row).val = (v_ air j).val + (air.last_row - j) by
        have ⟨hv_last, _⟩ := last_row_values air (h_all air.last_row (le_refl _))
        have hv_last_val : (v_ air air.last_row).val = 0 := by
          have := congr_arg Fin.val hv_last; simpa using this
        have hcn_last := counter_nat air h_all h_rot h_lr air.last_row (le_refl _)
        -- v(last).val = 0, so last_row + 1 = tmb(last).val
        -- v(j).val + (last_row - j) = 0, but v(j).val ≥ t(j).val ≥ 1, contradiction
        -- unless last_row = j and the difference is 0
        -- More carefully: v(last) = v(j) + (last_row - j)
        -- v(last) = 0, v(j) = j + 1 - t(j)
        -- So 0 = j + 1 - t(j) + last_row - j = last_row + 1 - t(j)
        -- So t(j) = last_row + 1
        -- But j + 1 ≥ 2 * t(j) = 2*(last_row + 1), so j ≥ 2*last_row + 1 > last_row
        -- Contradicts j ≤ last_row
        rw [hv_last_val] at h_val_last
        omega
      -- Prove v(last_row).val = v(j).val + (last_row - j) by induction on last_row - j
      -- At each step: mb stays (from mb_stays_when_v_ge_t), tmb stays, v' = v + 1
      -- Also (v+1).val = v.val + 1 (since v.val ≤ row < p - 1)
      suffices h_step : ∀ k, j ≤ k → k ≤ air.last_row →
          (v_ air k).val = (v_ air j).val + (k - j) ∧
          (tmb_ air k).val = (tmb_ air j).val by
        exact (h_step air.last_row hj (le_refl _)).1
      intro k hjk hk_row
      induction k with
      | zero =>
        have hj0 : j = 0 := by omega
        subst hj0; simp
      | succ n ihn =>
        by_cases hjn : j ≤ n
        · have hn_le : n ≤ air.last_row := by omega
          have ⟨ih_v, ih_t⟩ := ihn hjn hn_le
          have h_trans_n : n < air.last_row := by omega
          have h_bad_n : (v_ air n).val ≥ (tmb_ air n).val := by
            rw [ih_v, ih_t]; omega
          have hmb_n := mb_stays_when_v_ge_t air h_all h_rot h_mb_bound n hn_le h_trans_n h_bad_n
          have ⟨_, h4_n, h5_n, _⟩ := transition_facts air n hn_le h_trans_n (h_all n hn_le) h_rot
          have h_tmb_stays : tmb_ air (n+1) = tmb_ air n := by
            rw [h5_n, hmb_n, sub_self, add_zero, mul_one]
          have hv_inc : v_ air (n+1) = v_ air n + 1 := by
            rcases h4_n with hv0 | hv1
            · exfalso
              have hcn_n := counter_nat air h_all h_rot h_lr n hn_le
              have hcn_n1 := counter_nat air h_all h_rot h_lr (n+1) hk_row
              have hv0_val : (v_ air (n+1)).val = 0 := by
                have := congr_arg Fin.val hv0; simpa using this
              have h_tmb_eq : (tmb_ air (n+1)).val = (tmb_ air n).val := by
                have := congr_arg Fin.val h_tmb_stays; simpa using this
              rw [hv0_val, h_tmb_eq] at hcn_n1; omega
            · exact hv1
          constructor
          · have hv_val : (v_ air (n+1)).val = (v_ air n).val + 1 := by
              have := congr_arg Fin.val hv_inc
              simp [Fin.val_add] at this
              have hvb := val_bound air h_all h_rot h_lr n hn_le
              omega
            rw [hv_val, ih_v]; omega
          · have := congr_arg Fin.val h_tmb_stays
            simp at this; rw [this, ih_t]
        · have : j = n + 1 := by omega
          subst this; simp

    open BabyBear in
    /-- The main theorem: wf_properties hold for every row -/
    theorem wf_properties
        (air : Valid_VariableRangeCheckerAir FBB ExtF)
        (h_all : all_constraints_hold air)
        (h_rot : rotation_consistent air)
        (h_lr : air.last_row + 1 < BB_prime)
        (row : ℕ) (h_row : row ≤ air.last_row)
    : (mb_ air row).val < 31 ∧ (v_ air row).val < 2 ^ (mb_ air row).val := by
      have h_mb_bound : ∀ r ≤ air.last_row, (mb_ air r).val ≤ 18 := by
        intro r hr
        exact mb_le_18 air h_all h_rot h_lr r hr
      constructor
      · have := h_mb_bound row h_row; omega
      · by_contra h_not_lt
        push_neg at h_not_lt
        have h_tmb := tmb_eq_pow2 air h_all h_rot row h_row (fun r hr => h_mb_bound r (by omega))
        have h_bad : (v_ air row).val ≥ (tmb_ air row).val := by rw [h_tmb]; exact h_not_lt
        exact propagation air h_all h_rot h_lr h_mb_bound row h_row h_bad

  end properties

end VariableRangeCheckerAir.constraints
