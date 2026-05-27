import OpenvmFv.Airs.RangeTupleCheckerAir
import OpenvmFv.Extraction.RangeTupleCheckerAir
import OpenvmFv.Fundamentals.Interaction
import OpenvmFv.Util

import LeanZKCircuit.Interactions

namespace RangeTupleCheckerAir.constraints

  section constraint_simplification

    variable [Field F] [Field ExtF]

    section row_constraints

      @[RangeTupleCheckerAir_2_constraint_and_interaction_simplification]
      def constraint_0 (air : Valid_RangeTupleCheckerAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isFirstRow air row = 0 ∨ air.main_cols.tuple_0 row 0 = 0

      @[RangeTupleCheckerAir_2_air_simplification]
      lemma constraint_0_of_extraction
          (air : Valid_RangeTupleCheckerAir F ExtF) (row : ℕ)
      : RangeTupleCheckerAir_2.extraction.constraint_0 air row ↔ constraint_0 air row := by
        simp_all [openvm_encapsulation,
                  RangeTupleCheckerAir_2_constraint_and_interaction_simplification]

      @[RangeTupleCheckerAir_2_constraint_and_interaction_simplification]
      def constraint_1 (air : Valid_RangeTupleCheckerAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isLastRow air row = 0 ∨ air.main_cols.tuple_0 row 0 = 255

      @[RangeTupleCheckerAir_2_air_simplification]
      lemma constraint_1_of_extraction
          (air : Valid_RangeTupleCheckerAir F ExtF) (row : ℕ)
      : RangeTupleCheckerAir_2.extraction.constraint_1 air row ↔ constraint_1 air row := by
        simp_all [openvm_encapsulation,
                  RangeTupleCheckerAir_2_constraint_and_interaction_simplification]

      @[RangeTupleCheckerAir_2_constraint_and_interaction_simplification]
      def constraint_2 (air : Valid_RangeTupleCheckerAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isFirstRow air row = 0 ∨ air.main_cols.tuple_1 row 0 = 0

      @[RangeTupleCheckerAir_2_air_simplification]
      lemma constraint_2_of_extraction
          (air : Valid_RangeTupleCheckerAir F ExtF) (row : ℕ)
      : RangeTupleCheckerAir_2.extraction.constraint_2 air row ↔ constraint_2 air row := by
        simp_all [openvm_encapsulation,
                  RangeTupleCheckerAir_2_constraint_and_interaction_simplification]

      @[RangeTupleCheckerAir_2_constraint_and_interaction_simplification]
      def constraint_3 (air : Valid_RangeTupleCheckerAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isLastRow air row = 0 ∨ air.main_cols.tuple_1 row 0 = 8191

      @[RangeTupleCheckerAir_2_air_simplification]
      lemma constraint_3_of_extraction
          (air : Valid_RangeTupleCheckerAir F ExtF) (row : ℕ)
      : RangeTupleCheckerAir_2.extraction.constraint_3 air row ↔ constraint_3 air row := by
        simp_all [openvm_encapsulation,
                  RangeTupleCheckerAir_2_constraint_and_interaction_simplification]

      @[RangeTupleCheckerAir_2_constraint_and_interaction_simplification]
      def constraint_4 (air : Valid_RangeTupleCheckerAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isTransitionRow air row = 0 ∨
          air.main_cols.tuple_0 row 1 = air.main_cols.tuple_0 row 0 ∨
            air.main_cols.tuple_0 row 1 - air.main_cols.tuple_0 row 0 = 1

      @[RangeTupleCheckerAir_2_air_simplification]
      lemma constraint_4_of_extraction
          (air : Valid_RangeTupleCheckerAir F ExtF) (row : ℕ)
      : RangeTupleCheckerAir_2.extraction.constraint_4 air row ↔ constraint_4 air row := by
        simp_all [openvm_encapsulation,
                  RangeTupleCheckerAir_2_constraint_and_interaction_simplification]

      @[RangeTupleCheckerAir_2_constraint_and_interaction_simplification]
      def constraint_5 (air : Valid_RangeTupleCheckerAir F ExtF) (row : ℕ) : Prop :=
        air.main_cols.tuple_1 row 1 - air.main_cols.tuple_1 row 0 = 1 ∨ air.main_cols.tuple_1 row 0 = 8191

      @[RangeTupleCheckerAir_2_air_simplification]
      lemma constraint_5_of_extraction
          (air : Valid_RangeTupleCheckerAir F ExtF) (row : ℕ)
      : RangeTupleCheckerAir_2.extraction.constraint_5 air row ↔ constraint_5 air row := by
        simp_all [openvm_encapsulation,
                  RangeTupleCheckerAir_2_constraint_and_interaction_simplification]

      @[RangeTupleCheckerAir_2_constraint_and_interaction_simplification]
      def constraint_6 (air : Valid_RangeTupleCheckerAir F ExtF) (row : ℕ) : Prop :=
        air.main_cols.tuple_1 row 1 - air.main_cols.tuple_1 row 0 = 1 ∨ air.main_cols.tuple_1 row 1 = 0

      @[RangeTupleCheckerAir_2_air_simplification]
      lemma constraint_6_of_extraction
          (air : Valid_RangeTupleCheckerAir F ExtF) (row : ℕ)
      : RangeTupleCheckerAir_2.extraction.constraint_6 air row ↔ constraint_6 air row := by
        simp_all [openvm_encapsulation,
                  RangeTupleCheckerAir_2_constraint_and_interaction_simplification]

      @[RangeTupleCheckerAir_2_constraint_and_interaction_simplification]
      def constraint_7 (air : Valid_RangeTupleCheckerAir F ExtF) (row : ℕ) : Prop :=
        (air.main_cols.tuple_1 row 1 - air.main_cols.tuple_1 row 0) *
            (air.main_cols.tuple_1 row 1 - air.main_cols.tuple_1 row 0 - 1) *
          ((air.main_cols.tuple_0 row 0 - air.main_cols.tuple_0 row 1) * 2013265667 + 2013265666) +
        (air.main_cols.tuple_0 row 1 - air.main_cols.tuple_0 row 0) *
            (air.main_cols.tuple_0 row 1 - air.main_cols.tuple_0 row 0) *
          ((air.main_cols.tuple_1 row 1 - air.main_cols.tuple_1 row 0) * 2013249538 - 67092481) =
      0

      @[RangeTupleCheckerAir_2_air_simplification]
      lemma constraint_7_of_extraction
          (air : Valid_RangeTupleCheckerAir F ExtF) (row : ℕ)
      : RangeTupleCheckerAir_2.extraction.constraint_7 air row ↔ constraint_7 air row := by
        simp_all [openvm_encapsulation,
                  RangeTupleCheckerAir_2_constraint_and_interaction_simplification]

    end row_constraints

    section interactions

      @[RangeTupleCheckerAir_2_constraint_and_interaction_simplification]
      def bus_10Bus_row (air : Valid_RangeTupleCheckerAir F ExtF) (row : ℕ) : List (F × List F) :=
        [(-air.main_cols.mult row 0, [air.main_cols.tuple_0 row 0, air.main_cols.tuple_1 row 0])]

      lemma constrain_bus_10_interactions
        (air : Valid_RangeTupleCheckerAir F ExtF)
        (h : RangeTupleCheckerAir_2.extraction.constrain_interactions air)
      :
        air.buses 10 = (List.range (air.last_row + 1)).flatMap (λ row => bus_10Bus_row air row)
      := by
        unfold RangeTupleCheckerAir_2.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        simp [h]; clear h
        rfl

      def constrain_interactions (air : Valid_RangeTupleCheckerAir F ExtF) : Prop :=
        air.buses = fun index ↦
        if index = RangeTupleCheckerBus then (List.range (air.last_row + 1)).flatMap (bus_10Bus_row air)
        else []

      @[RangeTupleCheckerAir_2_air_simplification]
      lemma constrain_interactions_of_extraction
        (air : Valid_RangeTupleCheckerAir F ExtF)
        (h : RangeTupleCheckerAir_2.extraction.constrain_interactions air)
      : constrain_interactions air := by
        unfold constrain_interactions
        unfold RangeTupleCheckerAir_2.extraction.constrain_interactions at h
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
      (air : Valid_RangeTupleCheckerAir F ExtF)
      (row : ℕ)
    : List Prop :=
      [
        RangeTupleCheckerAir_2.extraction.constraint_0 air row,
        RangeTupleCheckerAir_2.extraction.constraint_1 air row,
        RangeTupleCheckerAir_2.extraction.constraint_2 air row,
        RangeTupleCheckerAir_2.extraction.constraint_3 air row,
        RangeTupleCheckerAir_2.extraction.constraint_4 air row,
        RangeTupleCheckerAir_2.extraction.constraint_5 air row,
        RangeTupleCheckerAir_2.extraction.constraint_6 air row,
        RangeTupleCheckerAir_2.extraction.constraint_7 air row
      ]

    @[simp]
    def allHold
      [Field ExtF]
      (air : Valid_RangeTupleCheckerAir F ExtF)
      (row : ℕ)
      (_ : row ≤ air.last_row)
    : Prop :=
      RangeTupleCheckerAir_2.extraction.constrain_interactions air ∧
      List.Forall (·) (extracted_row_constraint_list air row)

    @[simp]
    def row_constraint_list
      [Field ExtF]
      (air : Valid_RangeTupleCheckerAir F ExtF)
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
        constraint_7 air row
      ]

    @[simp]
    def allHold_simplified
      [Field ExtF]
      (air : Valid_RangeTupleCheckerAir F ExtF)
      (row : ℕ)
      (_ : row ≤ air.last_row)
    : Prop :=
      constrain_interactions air ∧
      List.Forall (·) (row_constraint_list air row)

    omit [Field ExtF] in
    lemma allHold_simplified_of_allHold
      [Field ExtF]
      (air : Valid_RangeTupleCheckerAir F ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
    : allHold air row h_row ↔ allHold_simplified air row h_row := by
      unfold allHold allHold_simplified
      apply Iff.and
      . unfold RangeTupleCheckerAir_2.extraction.constrain_interactions
        simp [openvm_encapsulation]
        rfl
      . simp only [extracted_row_constraint_list,
                  row_constraint_list,
                  RangeTupleCheckerAir_2_air_simplification]

  end allHold

  section properties

    variable [Field ExtF]

    abbrev t0_ (air : Valid_RangeTupleCheckerAir FBB ExtF) (row : ℕ) : FBB :=
      air.main_cols.tuple_0 row 0

    abbrev t1_ (air : Valid_RangeTupleCheckerAir FBB ExtF) (row : ℕ) : FBB :=
      air.main_cols.tuple_1 row 0

    def all_constraints_hold (air : Valid_RangeTupleCheckerAir FBB ExtF) : Prop :=
      ∀ row (h_row : row ≤ air.last_row), allHold air row h_row

    -- Rotation 1 is modeled abstractly, so the link to `row + 1` is external.
    def rotation_consistent (air : Valid_RangeTupleCheckerAir FBB ExtF) : Prop :=
      ∀ row, row < air.last_row →
        air.main_cols.tuple_0 row 1 = t0_ air (row + 1) ∧
        air.main_cols.tuple_1 row 1 = t1_ air (row + 1)

    private theorem val_eq_add_one_of_sub_eq_one
        {a b : FBB}
        (h_lt : b.val + 1 < BB_prime)
        (h : a - b = 1)
    : a.val = b.val + 1 := by
      have h_eq : a = b + 1 := (sub_eq_iff_eq_add').mp h
      rw [h_eq, Fin.val_add]
      simpa [Fin.val_natCast] using Nat.mod_eq_of_lt h_lt

    theorem first_row_values
        (air : Valid_RangeTupleCheckerAir FBB ExtF)
        (h_all : all_constraints_hold air)
    : t0_ air 0 = 0 ∧ t1_ air 0 = 0 := by
      have h := (allHold_simplified_of_allHold air 0 (by simp)).mp (h_all 0 (by simp))
      simp [allHold_simplified, row_constraint_list, constraint_0, constraint_2,
        Circuit.isFirstRow] at h
      exact ⟨h.2.1, h.2.2.2.1⟩

    theorem last_row_values
        (air : Valid_RangeTupleCheckerAir FBB ExtF)
        (h_all : all_constraints_hold air)
    : t0_ air air.last_row = 255 ∧ t1_ air air.last_row = 8191 := by
      have h := (allHold_simplified_of_allHold air air.last_row (by simp)).mp
        (h_all air.last_row (by simp))
      simp [allHold_simplified, row_constraint_list, constraint_1, constraint_3,
        Circuit.isLastRow, Valid_RangeTupleCheckerAir_last_row_project] at h
      exact ⟨h.2.2.1, h.2.2.2.2.1⟩

    theorem transition_facts
        (air : Valid_RangeTupleCheckerAir FBB ExtF)
        (h_all : all_constraints_hold air)
        (h_rot : rotation_consistent air)
        (row : ℕ)
        (h_row : row < air.last_row)
    : (t0_ air (row + 1) = t0_ air row ∨ t0_ air (row + 1) - t0_ air row = 1) ∧
      (t1_ air (row + 1) - t1_ air row = 1 ∨ t1_ air row = 8191) ∧
      (t1_ air (row + 1) - t1_ air row = 1 ∨ t1_ air (row + 1) = 0) := by
      have h := (allHold_simplified_of_allHold air row (by omega)).mp (h_all row (by omega))
      have hrot_row := h_rot row h_row
      simp [allHold_simplified, row_constraint_list, constraint_4, constraint_5, constraint_6,
        Circuit.isTransitionRow, Valid_RangeTupleCheckerAir_last_row_project,
        hrot_row.1, hrot_row.2, h_row.ne] at h
      exact ⟨h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1⟩

    private theorem t0_val_le_row
        (air : Valid_RangeTupleCheckerAir FBB ExtF)
        (h_all : all_constraints_hold air)
        (h_rot : rotation_consistent air)
        (h_lr : air.last_row + 1 < BB_prime)
        (row : ℕ)
        (h_row : row ≤ air.last_row)
    : (t0_ air row).val ≤ row := by
      induction row with
      | zero =>
          have h0 := first_row_values air h_all
          simp [h0.1]
      | succ k ih =>
          have hk_row : k < air.last_row := by omega
          have hk_le : k ≤ air.last_row := by omega
          have hk_val_le := ih hk_le
          have hstep := transition_facts air h_all h_rot k hk_row
          cases hstep.1 with
          | inl hsame =>
              have hval : (t0_ air (k + 1)).val = (t0_ air k).val := by
                simpa using congrArg Fin.val hsame
              omega
          | inr hdiff =>
              have hk1_lt : (t0_ air k).val + 1 < BB_prime := by
                have : k + 1 < BB_prime := by omega
                omega
              have hval := val_eq_add_one_of_sub_eq_one hk1_lt hdiff
              omega

    private theorem t1_val_le_row
        (air : Valid_RangeTupleCheckerAir FBB ExtF)
        (h_all : all_constraints_hold air)
        (h_rot : rotation_consistent air)
        (h_lr : air.last_row + 1 < BB_prime)
        (row : ℕ)
        (h_row : row ≤ air.last_row)
    : (t1_ air row).val ≤ row := by
      induction row with
      | zero =>
          have h0 := first_row_values air h_all
          simp [h0.2]
      | succ k ih =>
          have hk_row : k < air.last_row := by omega
          have hk_le : k ≤ air.last_row := by omega
          have hk_val_le := ih hk_le
          have hstep := transition_facts air h_all h_rot k hk_row
          cases hstep.2.2 with
          | inl hdiff =>
              have hk1_lt : (t1_ air k).val + 1 < BB_prime := by
                have : k + 1 < BB_prime := by omega
                omega
              have hval := val_eq_add_one_of_sub_eq_one hk1_lt hdiff
              omega
          | inr hzero =>
              have hval : (t1_ air (k + 1)).val = 0 := by
                simpa using congrArg Fin.val hzero
              omega

    private theorem t0_step_le
        (air : Valid_RangeTupleCheckerAir FBB ExtF)
        (h_all : all_constraints_hold air)
        (h_rot : rotation_consistent air)
        (h_lr : air.last_row + 1 < BB_prime)
        (row : ℕ)
        (h_row : row < air.last_row)
    : (t0_ air row).val ≤ (t0_ air (row + 1)).val := by
      have hstep := transition_facts air h_all h_rot row h_row
      cases hstep.1 with
      | inl hsame =>
          have hval : (t0_ air (row + 1)).val = (t0_ air row).val := by
            simpa using congrArg Fin.val hsame
          omega
      | inr hdiff =>
          have hrow_val := t0_val_le_row air h_all h_rot h_lr row (by omega)
          have hlt : (t0_ air row).val + 1 < BB_prime := by
            have : row + 1 < BB_prime := by omega
            omega
          have hval := val_eq_add_one_of_sub_eq_one hlt hdiff
          omega

    private theorem t0_monotone
        (air : Valid_RangeTupleCheckerAir FBB ExtF)
        (h_all : all_constraints_hold air)
        (h_rot : rotation_consistent air)
        (h_lr : air.last_row + 1 < BB_prime)
        {i j : ℕ}
        (hij : i ≤ j)
        (hj : j ≤ air.last_row)
    : (t0_ air i).val ≤ (t0_ air j).val := by
      induction j generalizing i with
      | zero =>
          have : i = 0 := by omega
          subst this
          omega
      | succ j ih =>
          by_cases h_eq : i = j + 1
          · subst h_eq
            omega
          · have hij' : i ≤ j := by omega
            have hj' : j ≤ air.last_row := by omega
            have hprev := ih hij' hj'
            have hstep := t0_step_le air h_all h_rot h_lr j (by omega)
            omega

    private theorem t1_bad_propagates
        (air : Valid_RangeTupleCheckerAir FBB ExtF)
        (h_all : all_constraints_hold air)
        (h_rot : rotation_consistent air)
        (h_lr : air.last_row + 1 < BB_prime)
        {j k : ℕ}
        (hjk : j ≤ k)
        (hk : k ≤ air.last_row)
        (hbad : 8192 ≤ (t1_ air j).val)
    : 8192 ≤ (t1_ air k).val := by
      induction k generalizing j with
      | zero =>
          have : j = 0 := by omega
          subst this
          have h0 := first_row_values air h_all
          have h0_val : (t1_ air 0).val = 0 := by
            simpa using congrArg Fin.val h0.2
          omega
      | succ k ih =>
          by_cases hjk' : j ≤ k
          · have hk_le : k ≤ air.last_row := by omega
            have hk_row : k < air.last_row := by omega
            have hk_bad := ih hjk' hk_le hbad
            have hstep := transition_facts air h_all h_rot k hk_row
            have hdiff : t1_ air (k + 1) - t1_ air k = 1 := by
              cases hstep.2.1 with
              | inl h => exact h
              | inr h8191 =>
                  have hval8191 : (t1_ air k).val = 8191 := by
                    simpa using congrArg Fin.val h8191
                  omega
            have hk_val_le := t1_val_le_row air h_all h_rot h_lr k hk_le
            have hk1_lt : (t1_ air k).val + 1 < BB_prime := by
              have : k + 1 < BB_prime := by omega
              omega
            have hval := val_eq_add_one_of_sub_eq_one hk1_lt hdiff
            omega
          · have h_eq : j = k + 1 := by omega
            subst h_eq
            exact hbad

    theorem t1_range
        (air : Valid_RangeTupleCheckerAir FBB ExtF)
        (h_all : all_constraints_hold air)
        (h_rot : rotation_consistent air)
        (h_lr : air.last_row + 1 < BB_prime)
        (row : ℕ)
        (h_row : row ≤ air.last_row)
    : (t1_ air row).val < 8192 := by
      by_contra h_bad
      have h_last_bad := t1_bad_propagates air h_all h_rot h_lr h_row (by simp) (by omega)
      have h_last := last_row_values air h_all
      have h_last_val : (t1_ air air.last_row).val = 8191 := by
        simpa using congrArg Fin.val h_last.2
      omega

    theorem t0_range
        (air : Valid_RangeTupleCheckerAir FBB ExtF)
        (h_all : all_constraints_hold air)
        (h_rot : rotation_consistent air)
        (h_lr : air.last_row + 1 < BB_prime)
        (row : ℕ)
        (h_row : row ≤ air.last_row)
    : (t0_ air row).val < 256 := by
      have hmono := t0_monotone air h_all h_rot h_lr h_row (by simp)
      have h_last := last_row_values air h_all
      have h_last_val : (t0_ air air.last_row).val = 255 := by
        simpa using congrArg Fin.val h_last.1
      omega

    theorem wf_properties
        (air : Valid_RangeTupleCheckerAir FBB ExtF)
        (h_all : all_constraints_hold air)
        (h_rot : rotation_consistent air)
        (h_lr : air.last_row + 1 < BB_prime)
        (row : ℕ)
        (h_row : row ≤ air.last_row)
    : (t0_ air row).val < 256 ∧ (t1_ air row).val < 8192 := by
      exact ⟨
        t0_range air h_all h_rot h_lr row h_row,
        t1_range air h_all h_rot h_lr row h_row
      ⟩

    omit [Field ExtF] in
    theorem wf_properties_iff_bus_wf_properties
        (air : Valid_RangeTupleCheckerAir FBB ExtF)
        (row : ℕ)
    : ((t0_ air row).val < 256 ∧ (t1_ air row).val < 8192) ↔
        Interaction.RangeTupleCheckerBusEntryInstance.wf_properties
          ⟨-air.main_cols.mult row 0, t0_ air row, t1_ air row⟩ := by
      rfl

  end properties

end RangeTupleCheckerAir.constraints
