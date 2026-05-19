import VmExtensions.Soundness.Sha2MainAir_sha512.CompressionBridge

set_option autoImplicit false
set_option linter.all false
set_option maxHeartbeats 1_000_000_000

namespace Sha2CompressionBridge_sha512

open BabyBear
open Sha2MainAir_sha512.Soundness
open Sha2BlockHasherVmAir_sha512.BlockSpec

section SharedBridge

open Sha2BlockHasherVmAir_sha512.constraints

variable {CMain CBlock : Type → Type → Type} {ExtF : Type}
  [Field ExtF] [Circuit FBB ExtF CMain] [Circuit FBB ExtF CBlock]

private theorem mappedEntries_getMultiplicity_zero_of_head_mismatch
    {f : ℕ → FBB × List FBB}
    (rows : List ℕ) (data : List FBB)
    (expected actual : FBB)
    (hkind : List.head? data = some expected)
    (hhead : ∀ r, List.head? (f r).2 = some actual)
    (hne : actual ≠ expected) :
    InteractionList.get_multiplicity (rows.map f) data = 0 := by
  induction rows with
  | nil =>
      simp [InteractionList.get_multiplicity]
  | cons r rows ih =>
      have hneq : (f r).2 ≠ data := by
        intro hEq
        have : some expected = some actual := by
          calc
            some expected = List.head? data := by simpa using hkind.symm
            _ = List.head? (f r).2 := by simpa [hEq]
            _ = some actual := hhead r
        exact hne (Option.some.inj this).symm
      simpa [InteractionList.get_multiplicity, hneq] using ih

private theorem blockMsg1_mult_zero_or_neg_one
    (blockAir : CBlock FBB ExtF) (row : ℕ)
    (hc : blockHasherConstraints blockAir) :
    (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg1Entry blockAir row).multiplicity = 0 ∨
      (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg1Entry blockAir row).multiplicity = -1 := by
  have hf : flag_constraints blockAir row := (hc row).1
  have hsum := round_plus_digest_boolean blockAir row hf
  have hpad := wrapperBus_padding_choose2_is_bit blockAir row hf
  rcases hpad with hpad0 | hpad1
  · simp [Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg1Entry, hpad0]
  · rcases hsum with hsum0 | hsum1
    · simp [Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg1Entry, hpad1, hsum0]
    · simp [Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg1Entry, hpad1, hsum1]

private theorem blockMsg2_mult_zero_or_neg_one
    (blockAir : CBlock FBB ExtF) (row : ℕ)
    (hc : blockHasherConstraints blockAir) :
    (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir row).multiplicity = 0 ∨
      (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir row).multiplicity = -1 := by
  have hf : flag_constraints blockAir row := (hc row).1
  have hsum := round_plus_digest_boolean blockAir row hf
  have hchoose := wrapperBus_choose2_encoder5_is_bit blockAir row hf
  rcases hchoose with hchoose0 | hchoose1
  · simp [Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry, hchoose0]
  · rcases hsum with hsum0 | hsum1
    · simp [Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry, hchoose1, hsum0]
    · simp [Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry, hchoose1, hsum1]

private theorem get_multiplicity_singleton
    (entry : FBB × List FBB) (data : List FBB) :
    InteractionList.get_multiplicity [entry] data =
      if entry.2 = data then entry.1 else 0 := by
  unfold InteractionList.get_multiplicity
  by_cases h : entry.2 = data <;> simp [h]

private theorem mainMsg1Entry_getMultiplicity_eq_countP
    (mainAir : CMain FBB ExtF)
    (r : ℕ)
    (hmainc : Sha2MainAir_sha512.Soundness.mainTraceConstraints mainAir)
    (data : List FBB) :
    InteractionList.get_multiplicity
        ([(Sha2MainAir_sha512.constraints.wrapperMsg1Entry mainAir r).toRaw]) data =
      (([r].countP
        (fun r =>
          (Sha2MainAir_sha512.constraints.wrapperMsg1Entry mainAir r).toRaw.2 == data ∧
            Sha2MainAir_sha512.constraints.is_enabled mainAir r = 1) : ℕ) : FBB) := by
  rw [get_multiplicity_singleton]
  have hen := hmainc.enabled_boolean r
  rcases hen with hen0 | hen1
  · by_cases hpayload :
        (Sha2MainAir_sha512.constraints.wrapperMsg1Entry mainAir r).message_type ::
            (Sha2MainAir_sha512.constraints.wrapperMsg1Entry mainAir r).request_id ::
              ((Sha2MainAir_sha512.constraints.wrapperMsg1Entry mainAir r).local_msg_bytes.toList ++
                (Sha2MainAir_sha512.constraints.wrapperMsg1Entry mainAir r).next_msg_bytes.toList) =
          data
    · simp [Sha2MainAir_sha512.constraints.wrapperMsg1Entry, List.countP_cons, hpayload, hen0]
    · simp [Sha2MainAir_sha512.constraints.wrapperMsg1Entry, List.countP_cons, hpayload, hen0]
  · by_cases hpayload :
        (Sha2MainAir_sha512.constraints.wrapperMsg1Entry mainAir r).message_type ::
            (Sha2MainAir_sha512.constraints.wrapperMsg1Entry mainAir r).request_id ::
              ((Sha2MainAir_sha512.constraints.wrapperMsg1Entry mainAir r).local_msg_bytes.toList ++
                (Sha2MainAir_sha512.constraints.wrapperMsg1Entry mainAir r).next_msg_bytes.toList) =
          data
    · simp [Sha2MainAir_sha512.constraints.wrapperMsg1Entry, List.countP_cons, hpayload, hen1]
    · simp [Sha2MainAir_sha512.constraints.wrapperMsg1Entry, List.countP_cons, hpayload, hen1]

private theorem mainMsg1Entries_getMultiplicity_eq_countP
    (mainAir : CMain FBB ExtF)
    (rows : List ℕ)
    (hmainc : Sha2MainAir_sha512.Soundness.mainTraceConstraints mainAir)
    (data : List FBB) :
    InteractionList.get_multiplicity
        (rows.map (fun r => (Sha2MainAir_sha512.constraints.wrapperMsg1Entry mainAir r).toRaw)) data =
      ((rows.countP
        (fun r =>
          (Sha2MainAir_sha512.constraints.wrapperMsg1Entry mainAir r).toRaw.2 == data ∧
            Sha2MainAir_sha512.constraints.is_enabled mainAir r = 1) : ℕ) : FBB) := by
  induction rows with
  | nil =>
      simp [InteractionList.get_multiplicity]
  | cons r rows ih =>
      rw [List.map_cons, ← List.singleton_append, InteractionList.get_multiplicity_append, ih,
        mainMsg1Entry_getMultiplicity_eq_countP mainAir r hmainc data]
      by_cases hP :
          (Sha2MainAir_sha512.constraints.wrapperMsg1Entry mainAir r).toRaw.2 == data ∧
            Sha2MainAir_sha512.constraints.is_enabled mainAir r = 1
      · simp [List.countP_cons, hP, Nat.cast_add, add_assoc, add_left_comm, add_comm]
      · simp [List.countP_cons, hP, Nat.cast_add, add_assoc, add_left_comm, add_comm]

private theorem blockStateEntry_getMultiplicity_eq_neg_countP
    (blockAir : CBlock FBB ExtF)
    (r : ℕ)
    (hc : blockHasherConstraints blockAir)
    (data : List FBB) :
    InteractionList.get_multiplicity
        ([(Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir r).toRaw]) data =
      -((([r].countP
        (fun r =>
          (Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir r).toRaw.2 == data ∧
            Sha2BlockHasherVmAir_sha512.constraints.is_digest_row blockAir r = 1) : ℕ) : FBB)) := by
  let payload : List FBB :=
    (Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir r).toRaw.2
  rw [get_multiplicity_singleton]
  change (if payload = data then -(Sha2BlockHasherVmAir_sha512.constraints.is_digest_row blockAir r) else 0) =
    -((([r].countP
      (fun r =>
        (Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir r).toRaw.2 == data ∧
          Sha2BlockHasherVmAir_sha512.constraints.is_digest_row blockAir r = 1) : ℕ) : FBB))
  have hdig := is_digest_row_boolean blockAir r ((hc r).1)
  rcases hdig with hdig0 | hdig1
  · have hneq : Sha2BlockHasherVmAir_sha512.constraints.is_digest_row blockAir r ≠ 1 := by
      intro h
      rw [hdig0] at h
      norm_num at h
    by_cases hpayload : payload = data
    · simp [payload, List.countP_cons, hpayload, hdig0, hneq]
    · simp [payload, List.countP_cons, hpayload, hdig0, hneq]
  · by_cases hpayload : payload = data
    · have hpayload' :
          (Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir r).message_type ::
              (Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir r).request_id ::
                ((Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir r).prev_state_u16.toList ++
                  (Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir r).new_state_bytes.toList) =
            data := by
        simpa [payload] using hpayload
      simp [payload, List.countP_cons, hpayload', hdig1]
    · have hpayload' :
          ¬((Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir r).message_type ::
              (Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir r).request_id ::
                ((Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir r).prev_state_u16.toList ++
                  (Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir r).new_state_bytes.toList) =
            data) := by
        simpa [payload] using hpayload
      simp [payload, List.countP_cons, hpayload', hdig1]

private theorem blockStateEntries_getMultiplicity_eq_neg_countP
    (blockAir : CBlock FBB ExtF)
    (rows : List ℕ)
    (hc : blockHasherConstraints blockAir)
    (data : List FBB) :
    InteractionList.get_multiplicity
        (rows.map (fun r => (Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir r).toRaw)) data =
      -(((rows.countP
        (fun r =>
          (Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir r).toRaw.2 == data ∧
            Sha2BlockHasherVmAir_sha512.constraints.is_digest_row blockAir r = 1) : ℕ) : FBB)) := by
  induction rows with
  | nil =>
      simp [InteractionList.get_multiplicity]
  | cons r rows ih =>
      rw [List.map_cons, ← List.singleton_append, InteractionList.get_multiplicity_append, ih,
        blockStateEntry_getMultiplicity_eq_neg_countP blockAir r hc data]
      by_cases hP :
          (Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir r).toRaw.2 == data ∧
            Sha2BlockHasherVmAir_sha512.constraints.is_digest_row blockAir r = 1
      · simp [List.countP_cons, hP, Nat.cast_add, add_assoc, add_left_comm, add_comm]
      · simp [List.countP_cons, hP, Nat.cast_add, add_assoc, add_left_comm, add_comm]

private theorem blockMsg2Entry_getMultiplicity_eq_neg_countP
    (blockAir : CBlock FBB ExtF)
    (r : ℕ)
    (hc : blockHasherConstraints blockAir)
    (data : List FBB) :
    InteractionList.get_multiplicity
        ([(Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir r).toRaw]) data =
      -((([r].countP
        (fun r =>
          (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir r).toRaw.2 == data ∧
            (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir r).multiplicity = -1) : ℕ) : FBB)) := by
  let payload : List FBB :=
    (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir r).toRaw.2
  let factor : FBB :=
    Sha2BlockHasherVmAir_sha512.constraints.wrapperBus_choose2
        (Sha2BlockHasherVmAir_sha512.constraints.encoder_idx blockAir 5 r) *
      (Sha2BlockHasherVmAir_sha512.constraints.is_round_row blockAir r +
        Sha2BlockHasherVmAir_sha512.constraints.is_digest_row blockAir r)
  rcases blockMsg2_mult_zero_or_neg_one blockAir r hc with hmult0 | hmult1
  · rw [get_multiplicity_singleton]
    change (if payload = data then -factor else 0) =
      -((([r].countP
        (fun r =>
          (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir r).toRaw.2 == data ∧
            (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir r).multiplicity = -1) : ℕ) : FBB))
    have hfactor0 : factor = 0 := by
      simpa [factor, Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry] using
        congrArg Neg.neg hmult0
    have hneq : factor ≠ 1 := by
      intro h
      rw [hfactor0] at h
      norm_num at h
    by_cases hpayload : payload = data
    · have hpayload' :
          (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir r).toRaw.2 = data := by
        simpa [payload] using hpayload
      simp [Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry, factor, List.countP_cons,
        hpayload', hfactor0, hneq]
    · have hpayload' :
          ¬((Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir r).toRaw.2 = data) := by
        simpa [payload] using hpayload
      simp [Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry, factor, List.countP_cons,
        hpayload', hfactor0, hneq]
  · rw [get_multiplicity_singleton]
    change (if payload = data then -factor else 0) =
      -((([r].countP
        (fun r =>
          (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir r).toRaw.2 == data ∧
            (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir r).multiplicity = -1) : ℕ) : FBB))
    have hfactor1 : factor = 1 := by
      simpa [factor, Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry] using
        congrArg Neg.neg hmult1
    by_cases hpayload : payload = data
    · have hpayload' :
          (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir r).message_type ::
              (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir r).request_id ::
                ((Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir r).local_msg_bytes.toList ++
                  (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir r).next_msg_bytes.toList) =
            data := by
        simpa [payload] using hpayload
      simp [payload, factor, List.countP_cons, hpayload', hfactor1, hmult1]
    · have hpayload' :
          ¬((Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir r).message_type ::
              (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir r).request_id ::
                ((Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir r).local_msg_bytes.toList ++
                  (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir r).next_msg_bytes.toList) =
            data) := by
        simpa [payload] using hpayload
      simp [payload, factor, List.countP_cons, hpayload', hfactor1]

private theorem blockMsg2Entries_getMultiplicity_eq_neg_countP
    (blockAir : CBlock FBB ExtF)
    (rows : List ℕ)
    (hc : blockHasherConstraints blockAir)
    (data : List FBB) :
    InteractionList.get_multiplicity
        (rows.map (fun r => (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir r).toRaw)) data =
      -(((rows.countP
        (fun r =>
          (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir r).toRaw.2 == data ∧
            (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir r).multiplicity = -1) : ℕ) : FBB)) := by
  induction rows with
  | nil =>
      simp [InteractionList.get_multiplicity]
  | cons r rows ih =>
      rw [List.map_cons, ← List.singleton_append, InteractionList.get_multiplicity_append, ih,
        blockMsg2Entry_getMultiplicity_eq_neg_countP blockAir r hc data]
      by_cases hP :
          (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir r).toRaw.2 == data ∧
            (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir r).multiplicity = -1
      · simp [List.countP_cons, hP, Nat.cast_add, add_assoc, add_left_comm, add_comm]
      · simp [List.countP_cons, hP, Nat.cast_add, add_assoc, add_left_comm, add_comm]

private theorem nodup_eq_singleton_of_mem_unique
    {α : Type} {xs : List α} {x : α}
    (hnodup : xs.Nodup)
    (hx : x ∈ xs)
    (hall : ∀ y ∈ xs, y = x) :
    xs = [x] := by
  cases xs with
  | nil =>
      cases hx
  | cons y ys =>
      have hy : y = x := hall y (by simp)
      subst y
      cases ys with
      | nil =>
          rfl
      | cons z zs =>
          have hz : z = x := hall z (by simp)
          have hnot : x ∉ z :: zs := by
            simpa using hnodup.not_mem
          exact False.elim (hnot (by simpa [hz]))

private theorem mainMsg1_filter_eq_singleton
    (mainAir : CMain FBB ExtF) (row : ℕ)
    (hmainc : Sha2MainAir_sha512.Soundness.mainTraceConstraints mainAir)
    (hmain_rot : rotation_consistent mainAir)
    (hmain_trace_fit : traceLengthFitsField mainAir)
    (hrow : row ≤ Circuit.last_row mainAir)
    (h_enabled : Sha2MainAir_sha512.constraints.is_enabled mainAir row = 1) :
    let rows := List.range (Circuit.last_row mainAir + 1)
    let data := (Sha2MainAir_sha512.constraints.wrapperMsg1Entry mainAir row).toRaw.2
    let P : ℕ → Bool := fun r =>
      (Sha2MainAir_sha512.constraints.wrapperMsg1Entry mainAir r).toRaw.2 == data ∧
        Sha2MainAir_sha512.constraints.is_enabled mainAir r = 1
    rows.filter P = [row] := by
  let rows := List.range (Circuit.last_row mainAir + 1)
  let data := (Sha2MainAir_sha512.constraints.wrapperMsg1Entry mainAir row).toRaw.2
  let P : ℕ → Bool := fun r =>
    (Sha2MainAir_sha512.constraints.wrapperMsg1Entry mainAir r).toRaw.2 == data ∧
      Sha2MainAir_sha512.constraints.is_enabled mainAir r = 1
  show rows.filter P = [row]
  have hrow_mem_filter : row ∈ rows.filter P := by
    apply List.mem_filter.mpr
    constructor
    · dsimp [rows]
      exact List.mem_range.mpr (Nat.lt_succ_of_le hrow)
    · simp [P, data, h_enabled]
  have hall_filter : ∀ r ∈ rows.filter P, r = row := by
    intro r hr
    have hr_mem_rows : r ∈ rows := (List.mem_filter.mp hr).1
    have hr_valid : r ≤ Circuit.last_row mainAir := Nat.lt_succ_iff.mp (List.mem_range.mp hr_mem_rows)
    have hrP :
        (Sha2MainAir_sha512.constraints.wrapperMsg1Entry mainAir r).toRaw.2 = data ∧
          Sha2MainAir_sha512.constraints.is_enabled mainAir r = 1 := by
      simpa [P] using (List.mem_filter.mp hr).2
    have h_enabled_r : Sha2MainAir_sha512.constraints.is_enabled mainAir r = 1 := hrP.2
    have hpayload_eq :
        (Sha2MainAir_sha512.constraints.wrapperMsg1Entry mainAir r).toRaw.2 = data := hrP.1
    have hreq_opt :
        some (Sha2MainAir_sha512.constraints.request_id mainAir r) =
          some (Sha2MainAir_sha512.constraints.request_id mainAir row) := by
      simpa [data, mainWrapperMsg1_raw_request] using
        congrArg (fun payload => List.head? (List.tail payload)) hpayload_eq
    have hreq :
        Sha2MainAir_sha512.constraints.request_id mainAir r =
          Sha2MainAir_sha512.constraints.request_id mainAir row :=
      Option.some.inj hreq_opt
    exact mainTraceConstraints.enabled_request_id_injective hmainc
      hmain_rot hmain_trace_fit r row hr_valid hrow h_enabled_r h_enabled hreq
  have hfilter_nodup : (rows.filter P).Nodup := by
    simpa [rows] using (List.nodup_range.filter P : (List.range (Circuit.last_row mainAir + 1)).filter P |>.Nodup)
  exact nodup_eq_singleton_of_mem_unique hfilter_nodup hrow_mem_filter hall_filter

private theorem mainMsg1_trace_getMultiplicity_eq_count
    (mainAir : CMain FBB ExtF) (row : ℕ)
    (hmainc : Sha2MainAir_sha512.Soundness.mainTraceConstraints mainAir)
    (h_enabled : Sha2MainAir_sha512.constraints.is_enabled mainAir row = 1) :
    let rows := List.range (Circuit.last_row mainAir + 1)
    let data := (Sha2MainAir_sha512.constraints.wrapperMsg1Entry mainAir row).toRaw.2
    let P : ℕ → Bool := fun r =>
      (Sha2MainAir_sha512.constraints.wrapperMsg1Entry mainAir r).toRaw.2 == data ∧
        Sha2MainAir_sha512.constraints.is_enabled mainAir r = 1
    InteractionList.get_multiplicity
      (Sha2MainAir_sha512.constraints.wrapperBus_trace mainAir) data =
      (((rows.countP P : ℕ) : FBB) : FBB) := by
  let rows := List.range (Circuit.last_row mainAir + 1)
  let data := (Sha2MainAir_sha512.constraints.wrapperMsg1Entry mainAir row).toRaw.2
  let P : ℕ → Bool := fun r =>
    (Sha2MainAir_sha512.constraints.wrapperMsg1Entry mainAir r).toRaw.2 == data ∧
      Sha2MainAir_sha512.constraints.is_enabled mainAir r = 1
  show
    InteractionList.get_multiplicity
      (Sha2MainAir_sha512.constraints.wrapperBus_trace mainAir) data =
      (((rows.countP P : ℕ) : FBB) : FBB)
  have htrace_perm := mainWrapperTrace_perm_components mainAir rows
  have hkind : List.head? data = some 1 := by
    simpa [data] using mainWrapperMsg1_raw_head mainAir row
  have hstate_zero :
      InteractionList.get_multiplicity
        (rows.map (fun r => (Sha2MainAir_sha512.constraints.wrapperStateEntry mainAir r).toRaw)) data = 0 :=
    mappedEntries_getMultiplicity_zero_of_head_mismatch
      (rows := rows) (data := data) (expected := 1) (actual := 0)
      hkind (fun r => mainWrapperState_raw_head mainAir r) (by decide)
  have hmsg2_zero :
      InteractionList.get_multiplicity
        (rows.map (fun r => (Sha2MainAir_sha512.constraints.wrapperMsg2Entry mainAir r).toRaw)) data = 0 :=
    mappedEntries_getMultiplicity_zero_of_head_mismatch
      (rows := rows) (data := data) (expected := 1) (actual := 2)
      hkind (fun r => mainWrapperMsg2_raw_head mainAir r) (by decide)
  have hmsg1_count :
      InteractionList.get_multiplicity
        (rows.map (fun r => (Sha2MainAir_sha512.constraints.wrapperMsg1Entry mainAir r).toRaw)) data =
      (((rows.countP P : ℕ) : FBB) : FBB) := by
    simpa [rows, data, P] using mainMsg1Entries_getMultiplicity_eq_countP mainAir rows hmainc data
  have hstate_zero' :
      InteractionList.get_multiplicity
        (rows.map (fun r =>
          ((Sha2MainAir_sha512.constraints.wrapperStateEntry mainAir r).multiplicity,
            (Sha2MainAir_sha512.constraints.wrapperStateEntry mainAir r).message_type ::
              (Sha2MainAir_sha512.constraints.wrapperStateEntry mainAir r).request_id ::
                ((Sha2MainAir_sha512.constraints.wrapperStateEntry mainAir r).prev_state_u16.toList ++
                  (Sha2MainAir_sha512.constraints.wrapperStateEntry mainAir r).new_state_bytes.toList)))) data = 0 := by
    simpa using hstate_zero
  have hmsg1_count' :
      InteractionList.get_multiplicity
        (rows.map (fun r =>
          ((Sha2MainAir_sha512.constraints.wrapperMsg1Entry mainAir r).multiplicity,
            (Sha2MainAir_sha512.constraints.wrapperMsg1Entry mainAir r).message_type ::
              (Sha2MainAir_sha512.constraints.wrapperMsg1Entry mainAir r).request_id ::
                ((Sha2MainAir_sha512.constraints.wrapperMsg1Entry mainAir r).local_msg_bytes.toList ++
                  (Sha2MainAir_sha512.constraints.wrapperMsg1Entry mainAir r).next_msg_bytes.toList)))) data =
      (((rows.countP P : ℕ) : FBB) : FBB) := by
    simpa using hmsg1_count
  have hmsg2_zero' :
      InteractionList.get_multiplicity
        (rows.map (fun r =>
          ((Sha2MainAir_sha512.constraints.wrapperMsg2Entry mainAir r).multiplicity,
            (Sha2MainAir_sha512.constraints.wrapperMsg2Entry mainAir r).message_type ::
              (Sha2MainAir_sha512.constraints.wrapperMsg2Entry mainAir r).request_id ::
                ((Sha2MainAir_sha512.constraints.wrapperMsg2Entry mainAir r).local_msg_bytes.toList ++
                  (Sha2MainAir_sha512.constraints.wrapperMsg2Entry mainAir r).next_msg_bytes.toList)))) data = 0 := by
    simpa using hmsg2_zero
  have hstate_zero'' :
      InteractionList.get_multiplicity
        (rows.map (fun r =>
          (Sha2MainAir_sha512.constraints.is_enabled mainAir r,
            0 :: Sha2MainAir_sha512.constraints.request_id mainAir r ::
              ((Sha2MainAir_sha512.constraints.wrapperStateEntry mainAir r).prev_state_u16.toList ++
                (Sha2MainAir_sha512.constraints.wrapperStateEntry mainAir r).new_state_bytes.toList)))) data = 0 := by
    simpa using hstate_zero'
  have hmsg1_count'' :
      InteractionList.get_multiplicity
        (rows.map (fun r =>
          (Sha2MainAir_sha512.constraints.is_enabled mainAir r,
            1 :: Sha2MainAir_sha512.constraints.request_id mainAir r ::
              ((Sha2MainAir_sha512.constraints.wrapperMsg1Entry mainAir r).local_msg_bytes.toList ++
                (Sha2MainAir_sha512.constraints.wrapperMsg1Entry mainAir r).next_msg_bytes.toList)))) data =
      (((rows.countP P : ℕ) : FBB) : FBB) := by
    simpa using hmsg1_count'
  have hmsg2_zero'' :
      InteractionList.get_multiplicity
        (rows.map (fun r =>
          (Sha2MainAir_sha512.constraints.is_enabled mainAir r,
            2 :: Sha2MainAir_sha512.constraints.request_id mainAir r ::
              ((Sha2MainAir_sha512.constraints.wrapperMsg2Entry mainAir r).local_msg_bytes.toList ++
                (Sha2MainAir_sha512.constraints.wrapperMsg2Entry mainAir r).next_msg_bytes.toList)))) data = 0 := by
    simpa using hmsg2_zero'
  calc
    InteractionList.get_multiplicity
        (Sha2MainAir_sha512.constraints.wrapperBus_trace mainAir) data =
      InteractionList.get_multiplicity
        (rows.map (fun r => (Sha2MainAir_sha512.constraints.wrapperStateEntry mainAir r).toRaw) ++
          rows.map (fun r => (Sha2MainAir_sha512.constraints.wrapperMsg1Entry mainAir r).toRaw) ++
          rows.map (fun r => (Sha2MainAir_sha512.constraints.wrapperMsg2Entry mainAir r).toRaw)) data := by
        simpa [rows, Sha2MainAir_sha512.constraints.wrapperBus_trace] using
          get_multiplicity_inv_perm htrace_perm data
    _ =
      InteractionList.get_multiplicity
        (rows.map (fun r => (Sha2MainAir_sha512.constraints.wrapperStateEntry mainAir r).toRaw)) data +
      (InteractionList.get_multiplicity
        (rows.map (fun r => (Sha2MainAir_sha512.constraints.wrapperMsg1Entry mainAir r).toRaw)) data +
        InteractionList.get_multiplicity
          (rows.map (fun r => (Sha2MainAir_sha512.constraints.wrapperMsg2Entry mainAir r).toRaw)) data) := by
        rw [InteractionList.get_multiplicity_append, InteractionList.get_multiplicity_append]
        simp [add_assoc]
    _ = (((rows.countP P : ℕ) : FBB) : FBB) := by
        simp [hstate_zero'', hmsg1_count'', hmsg2_zero'']

theorem mainMsg1_trace_getMultiplicity_eq_one
    (mainAir : CMain FBB ExtF) (row : ℕ)
    (hmainc : Sha2MainAir_sha512.Soundness.mainTraceConstraints mainAir)
    (hmain_rot : rotation_consistent mainAir)
    (hmain_trace_fit : traceLengthFitsField mainAir)
    (hrow : row ≤ Circuit.last_row mainAir)
    (h_enabled : Sha2MainAir_sha512.constraints.is_enabled mainAir row = 1) :
    InteractionList.get_multiplicity
      (Sha2MainAir_sha512.constraints.wrapperBus_trace mainAir)
      ((Sha2MainAir_sha512.constraints.wrapperMsg1Entry mainAir row).toRaw.2) = 1 := by
  let rows := List.range (Circuit.last_row mainAir + 1)
  let data := (Sha2MainAir_sha512.constraints.wrapperMsg1Entry mainAir row).toRaw.2
  let P : ℕ → Bool := fun r =>
    (Sha2MainAir_sha512.constraints.wrapperMsg1Entry mainAir r).toRaw.2 == data ∧
      Sha2MainAir_sha512.constraints.is_enabled mainAir r = 1
  have hcount :
      InteractionList.get_multiplicity
        (Sha2MainAir_sha512.constraints.wrapperBus_trace mainAir) data =
      (((rows.countP P : ℕ) : FBB) : FBB) := by
    simpa [rows, data, P] using
      mainMsg1_trace_getMultiplicity_eq_count mainAir row hmainc h_enabled
  have hfilter : rows.filter P = [row] := by
    simpa [rows, data, P] using
      mainMsg1_filter_eq_singleton mainAir row hmainc hmain_rot hmain_trace_fit hrow h_enabled
  rw [List.countP_eq_length_filter, hfilter] at hcount
  norm_num at hcount
  simpa [rows, data, P] using hcount

theorem mainState_trace_getMultiplicity_zero_of_no_sender
    (mainAir : CMain FBB ExtF)
    (hmainc : Sha2MainAir_sha512.Soundness.mainTraceConstraints mainAir)
    (data : List FBB)
    (hkind : List.head? data = some 0)
    (hno : ∀ r, r ≤ Circuit.last_row mainAir →
      Sha2MainAir_sha512.constraints.is_enabled mainAir r = 1 →
      (Sha2MainAir_sha512.constraints.wrapperStateEntry mainAir r).toRaw.2 ≠ data) :
    InteractionList.get_multiplicity
      (Sha2MainAir_sha512.constraints.wrapperBus_trace mainAir) data = 0 := by
  unfold InteractionList.get_multiplicity
  apply List.sum_eq_zero
  intro m hm
  rcases List.mem_map.mp hm with ⟨entry, hentry_filter, hm_eq⟩
  rcases entry with ⟨mult, payload⟩
  have hentry_trace :
      (mult, payload) ∈ Sha2MainAir_sha512.constraints.wrapperBus_trace mainAir :=
    (List.mem_filter.mp hentry_filter).1
  have hpayload : payload = data := by
    simpa using (List.mem_filter.mp hentry_filter).2
  rcases (mem_mainWrapperTrace_iff mainAir (mult, payload)).mp hentry_trace with
    ⟨r, hr_valid, hrow_entry⟩
  have hen := hmainc.enabled_boolean r
  simp [Sha2MainAir_sha512.constraints.wrapperBus_row] at hrow_entry
  rcases hrow_entry with hstate | hmsg1 | hmsg2
  · rcases hstate with ⟨hmult, hpayload_entry⟩
    rcases hen with hen0 | hen1
    · have hm : m = (Sha2MainAir_sha512.constraints.wrapperStateEntry mainAir r).multiplicity := by
        exact hm_eq.symm.trans hmult
      calc
        m = (Sha2MainAir_sha512.constraints.wrapperStateEntry mainAir r).multiplicity := hm
        _ = 0 := by simp [Sha2MainAir_sha512.constraints.wrapperStateEntry, hen0]
    · have hEq :
          (Sha2MainAir_sha512.constraints.wrapperStateEntry mainAir r).toRaw.2 = data := by
        calc
          (Sha2MainAir_sha512.constraints.wrapperStateEntry mainAir r).toRaw.2 = payload := by
            simpa using hpayload_entry.symm
          _ = data := hpayload
      exact False.elim (hno r hr_valid hen1 hEq)
  · rcases hmsg1 with ⟨_, hpayload_entry⟩
    have hhead1 : List.head? payload = some 1 := by
      calc
        List.head? payload = List.head? ((Sha2MainAir_sha512.constraints.wrapperMsg1Entry mainAir r).toRaw.2) := by
          simpa using congrArg List.head? hpayload_entry
        _ = some 1 := mainWrapperMsg1_raw_head mainAir r
    have : some (1 : FBB) = some 0 := by
      calc
        some (1 : FBB) = List.head? payload := hhead1.symm
        _ = List.head? data := by simpa [hpayload]
        _ = some 0 := hkind
    exact False.elim ((by decide : (some (1 : FBB)) ≠ some 0) this)
  · rcases hmsg2 with ⟨_, hpayload_entry⟩
    have hhead2 : List.head? payload = some 2 := by
      calc
        List.head? payload = List.head? ((Sha2MainAir_sha512.constraints.wrapperMsg2Entry mainAir r).toRaw.2) := by
          simpa using congrArg List.head? hpayload_entry
        _ = some 2 := mainWrapperMsg2_raw_head mainAir r
    have : some (2 : FBB) = some 0 := by
      calc
        some (2 : FBB) = List.head? payload := hhead2.symm
        _ = List.head? data := by simpa [hpayload]
        _ = some 0 := hkind
    exact False.elim ((by decide : (some (2 : FBB)) ≠ some 0) this)

theorem mainMsg2_trace_getMultiplicity_zero_of_no_sender
    (mainAir : CMain FBB ExtF)
    (hmainc : Sha2MainAir_sha512.Soundness.mainTraceConstraints mainAir)
    (data : List FBB)
    (hkind : List.head? data = some 2)
    (hno : ∀ r, r ≤ Circuit.last_row mainAir →
      Sha2MainAir_sha512.constraints.is_enabled mainAir r = 1 →
      (Sha2MainAir_sha512.constraints.wrapperMsg2Entry mainAir r).toRaw.2 ≠ data) :
    InteractionList.get_multiplicity
      (Sha2MainAir_sha512.constraints.wrapperBus_trace mainAir) data = 0 := by
  unfold InteractionList.get_multiplicity
  apply List.sum_eq_zero
  intro m hm
  rcases List.mem_map.mp hm with ⟨entry, hentry_filter, hm_eq⟩
  rcases entry with ⟨mult, payload⟩
  have hentry_trace :
      (mult, payload) ∈ Sha2MainAir_sha512.constraints.wrapperBus_trace mainAir :=
    (List.mem_filter.mp hentry_filter).1
  have hpayload : payload = data := by
    simpa using (List.mem_filter.mp hentry_filter).2
  rcases (mem_mainWrapperTrace_iff mainAir (mult, payload)).mp hentry_trace with
    ⟨r, hr_valid, hrow_entry⟩
  have hen := hmainc.enabled_boolean r
  simp [Sha2MainAir_sha512.constraints.wrapperBus_row] at hrow_entry
  rcases hrow_entry with hstate | hmsg1 | hmsg2
  · rcases hstate with ⟨_, hpayload_entry⟩
    have hhead0 : List.head? payload = some 0 := by
      calc
        List.head? payload = List.head? ((Sha2MainAir_sha512.constraints.wrapperStateEntry mainAir r).toRaw.2) := by
          simpa using congrArg List.head? hpayload_entry
        _ = some 0 := mainWrapperState_raw_head mainAir r
    have : some (0 : FBB) = some 2 := by
      calc
        some (0 : FBB) = List.head? payload := hhead0.symm
        _ = List.head? data := by simpa [hpayload]
        _ = some 2 := hkind
    exact False.elim ((by decide : (some (0 : FBB)) ≠ some 2) this)
  · rcases hmsg1 with ⟨_, hpayload_entry⟩
    have hhead1 : List.head? payload = some 1 := by
      calc
        List.head? payload = List.head? ((Sha2MainAir_sha512.constraints.wrapperMsg1Entry mainAir r).toRaw.2) := by
          simpa using congrArg List.head? hpayload_entry
        _ = some 1 := mainWrapperMsg1_raw_head mainAir r
    have : some (1 : FBB) = some 2 := by
      calc
        some (1 : FBB) = List.head? payload := hhead1.symm
        _ = List.head? data := by simpa [hpayload]
        _ = some 2 := hkind
    exact False.elim ((by decide : (some (1 : FBB)) ≠ some 2) this)
  · rcases hmsg2 with ⟨hmult, hpayload_entry⟩
    rcases hen with hen0 | hen1
    · have hm : m = (Sha2MainAir_sha512.constraints.wrapperMsg2Entry mainAir r).multiplicity := by
        exact hm_eq.symm.trans hmult
      calc
        m = (Sha2MainAir_sha512.constraints.wrapperMsg2Entry mainAir r).multiplicity := hm
        _ = 0 := by simp [Sha2MainAir_sha512.constraints.wrapperMsg2Entry, hen0]
    · have hEq :
          (Sha2MainAir_sha512.constraints.wrapperMsg2Entry mainAir r).toRaw.2 = data := by
        calc
          (Sha2MainAir_sha512.constraints.wrapperMsg2Entry mainAir r).toRaw.2 = payload := by
            simpa using hpayload_entry.symm
          _ = data := hpayload
      exact False.elim (hno r hr_valid hen1 hEq)

theorem blockMsg1_trace_getMultiplicity_zero_of_no_active_match
    (blockAir : CBlock FBB ExtF)
    (hc : blockHasherConstraints blockAir)
    (data : List FBB)
    (hkind : List.head? data = some 1)
    (hno : ∀ r, r ≤ Circuit.last_row blockAir →
      (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg1Entry blockAir r).toRaw.2 = data →
      (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg1Entry blockAir r).multiplicity ≠ -1) :
    InteractionList.get_multiplicity
      (Sha2BlockHasherVmAir_sha512.constraints.wrapperBus_trace blockAir) data = 0 := by
  unfold InteractionList.get_multiplicity
  apply List.sum_eq_zero
  intro m hm
  rcases List.mem_map.mp hm with ⟨entry, hentry_filter, hm_eq⟩
  rcases entry with ⟨mult, payload⟩
  have hentry_trace :
      (mult, payload) ∈ Sha2BlockHasherVmAir_sha512.constraints.wrapperBus_trace blockAir :=
    (List.mem_filter.mp hentry_filter).1
  have hpayload : payload = data := by
    simpa using (List.mem_filter.mp hentry_filter).2
  rcases (mem_blockWrapperTrace_iff blockAir (mult, payload)).mp hentry_trace with
    ⟨r, hr_valid, hrow_entry⟩
  simp [Sha2BlockHasherVmAir_sha512.constraints.wrapperBus_row] at hrow_entry
  rcases hrow_entry with hstate | hmsg1 | hmsg2
  · rcases hstate with ⟨_, hpayload_entry⟩
    have hhead0 : List.head? payload = some 0 := by
      calc
        List.head? payload = List.head? ((Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir r).toRaw.2) := by
          simpa using congrArg List.head? hpayload_entry
        _ = some 0 := blockWrapperState_raw_head blockAir r
    have : some (0 : FBB) = some 1 := by
      calc
        some (0 : FBB) = List.head? payload := hhead0.symm
        _ = List.head? data := by simpa [hpayload]
        _ = some 1 := hkind
    exact False.elim ((by decide : (some (0 : FBB)) ≠ some 1) this)
  · rcases hmsg1 with ⟨hmult, hpayload_entry⟩
    rcases blockMsg1_mult_zero_or_neg_one blockAir r hc with hmult0 | hmult1
    · have hm : m = (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg1Entry blockAir r).multiplicity := by
        exact hm_eq.symm.trans hmult
      calc
        m = (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg1Entry blockAir r).multiplicity := hm
        _ = 0 := hmult0
    · have hEq :
          (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg1Entry blockAir r).toRaw.2 = data := by
        calc
          (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg1Entry blockAir r).toRaw.2 = payload := by
            simpa using hpayload_entry.symm
          _ = data := hpayload
      exact False.elim (hno r hr_valid hEq hmult1)
  · rcases hmsg2 with ⟨_, hpayload_entry⟩
    have hhead2 : List.head? payload = some 2 := by
      calc
        List.head? payload = List.head? ((Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir r).toRaw.2) := by
          simpa using congrArg List.head? hpayload_entry
        _ = some 2 := blockWrapperMsg2_raw_head blockAir r
    have : some (2 : FBB) = some 1 := by
      calc
        some (2 : FBB) = List.head? payload := hhead2.symm
        _ = List.head? data := by simpa [hpayload]
        _ = some 1 := hkind
    exact False.elim ((by decide : (some (2 : FBB)) ≠ some 1) this)

theorem blockState_trace_getMultiplicity_ne_zero_of_start
    (blockAir : CBlock FBB ExtF) (start : ℕ)
    (hstart : start ≤ Circuit.last_row blockAir)
    (hsel : encoder_selector_idx blockAir start = 0)
    (hrot : rotation_consistent blockAir)
    (hc : blockHasherConstraints blockAir)
    (htrace_fit : traceLengthFitsField blockAir) :
    InteractionList.get_multiplicity
      (Sha2BlockHasherVmAir_sha512.constraints.wrapperBus_trace blockAir)
      ((Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir (start + 20)).toRaw.2) ≠ 0 := by
  let rows := List.range (Circuit.last_row blockAir + 1)
  let data := (Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir (start + 20)).toRaw.2
  let P : ℕ → Bool := fun r =>
    (Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir r).toRaw.2 == data ∧
      Sha2BlockHasherVmAir_sha512.constraints.is_digest_row blockAir r = 1
  have htrace_perm := blockWrapperTrace_perm_components blockAir rows
  have hkind : List.head? data = some 0 := by
    simpa [data] using blockWrapperState_raw_head blockAir (start + 20)
  have hmsg1_zero :
      InteractionList.get_multiplicity
        (rows.map (fun r => (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg1Entry blockAir r).toRaw)) data = 0 :=
    mappedEntries_getMultiplicity_zero_of_head_mismatch
      (rows := rows) (data := data) (expected := 0) (actual := 1)
      hkind (fun r => blockWrapperMsg1_raw_head blockAir r) (by decide)
  have hmsg2_zero :
      InteractionList.get_multiplicity
        (rows.map (fun r => (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir r).toRaw)) data = 0 :=
    mappedEntries_getMultiplicity_zero_of_head_mismatch
      (rows := rows) (data := data) (expected := 0) (actual := 2)
      hkind (fun r => blockWrapperMsg2_raw_head blockAir r) (by decide)
  have hstate_count :
      InteractionList.get_multiplicity
        (rows.map (fun r => (Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir r).toRaw)) data =
      -(((rows.countP P : ℕ) : FBB) : FBB) := by
    simpa [rows, data, P] using blockStateEntries_getMultiplicity_eq_neg_countP blockAir rows hc data
  have hwindow := blockWindowSupported_of_start_le blockAir start hstart hsel hrot hc
  have hshape := blockWindowHasShape_of_constraints blockAir start hwindow hsel hrot hc
  have hdigest16 : is_digest_row blockAir (start + 20) = 1 := hshape.2.2.2.2
  have hcount_lt : rows.countP P < BB_prime := by
    have hcount_le : rows.countP P ≤ rows.length := by
      rw [List.countP_eq_length_filter]
      have hlen :
          rows.length = (rows.filter P).length + (rows.filter (!P ·)).length := by
        simpa using List.length_eq_length_filter_add (l := rows) P
      omega
    have hrows_len : rows.length < BB_prime := by
      simpa [rows] using htrace_fit
    exact lt_of_le_of_lt hcount_le hrows_len
  have hcount_ne : rows.countP P ≠ 0 := by
    intro hzero
    have hfilter_nil : rows.filter P = [] := by
      apply List.length_eq_zero_iff.mp
      simpa [List.countP_eq_length_filter] using hzero
    have hmem_filter : start + 20 ∈ rows.filter P := by
      apply List.mem_filter.mpr
      constructor
      · dsimp [rows]
        dsimp [blockWindowSupported] at hwindow
        exact List.mem_range.mpr (by omega)
      · simp [P, data, hdigest16]
    have : False := by simpa [hfilter_nil] using hmem_filter
    exact False.elim this
  have hstate_nonzero :
      InteractionList.get_multiplicity
        (rows.map (fun r => (Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir r).toRaw)) data ≠ 0 := by
    rw [hstate_count]
    apply neg_ne_zero.mpr
    exact natCast_ne_zero_of_lt_BB_prime hcount_lt hcount_ne
  intro hzero
  have hsum_components :
      InteractionList.get_multiplicity
        (Sha2BlockHasherVmAir_sha512.constraints.wrapperBus_trace blockAir) data =
      InteractionList.get_multiplicity
        (rows.map (fun r => (Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir r).toRaw) ++
          rows.map (fun r => (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg1Entry blockAir r).toRaw) ++
          rows.map (fun r => (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir r).toRaw)) data := by
        simpa [rows, Sha2BlockHasherVmAir_sha512.constraints.wrapperBus_trace] using
          get_multiplicity_inv_perm htrace_perm data
  have hstate_zero' :
      InteractionList.get_multiplicity
        (rows.map (fun r => (Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir r).toRaw)) data = 0 := by
    rw [hsum_components, InteractionList.get_multiplicity_append, InteractionList.get_multiplicity_append] at hzero
    have hmsg1_zero' :
        InteractionList.get_multiplicity
          (rows.map (fun r =>
            ((Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg1Entry blockAir r).multiplicity,
              (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg1Entry blockAir r).message_type ::
                (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg1Entry blockAir r).request_id ::
                  ((Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg1Entry blockAir r).local_msg_bytes.toList ++
                    (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg1Entry blockAir r).next_msg_bytes.toList)))) data = 0 := by
      simpa using hmsg1_zero
    have hmsg2_zero'' :
        InteractionList.get_multiplicity
          (rows.map (fun r =>
            ((Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir r).multiplicity,
              (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir r).message_type ::
                (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir r).request_id ::
                  ((Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir r).local_msg_bytes.toList ++
                    (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir r).next_msg_bytes.toList)))) data = 0 := by
      simpa using hmsg2_zero
    simpa [hmsg1_zero', hmsg2_zero'', add_assoc] using hzero
  exact hstate_nonzero hstate_zero'

theorem blockMsg2_trace_getMultiplicity_ne_zero_of_start
    (blockAir : CBlock FBB ExtF) (start : ℕ)
    (hstart : start ≤ Circuit.last_row blockAir)
    (hsel : encoder_selector_idx blockAir start = 0)
    (hrot : rotation_consistent blockAir)
    (hc : blockHasherConstraints blockAir)
    (htrace_fit : traceLengthFitsField blockAir) :
    InteractionList.get_multiplicity
      (Sha2BlockHasherVmAir_sha512.constraints.wrapperBus_trace blockAir)
      ((Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir (start + 2)).toRaw.2) ≠ 0 := by
  let rows := List.range (Circuit.last_row blockAir + 1)
  let data := (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir (start + 2)).toRaw.2
  let P : ℕ → Bool := fun r =>
    (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir r).toRaw.2 == data ∧
      (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir r).multiplicity = -1
  have htrace_perm := blockWrapperTrace_perm_components blockAir rows
  have hkind : List.head? data = some 2 := by
    simpa [data] using blockWrapperMsg2_raw_head blockAir (start + 2)
  have hstate_zero :
      InteractionList.get_multiplicity
        (rows.map (fun r => (Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir r).toRaw)) data = 0 :=
    mappedEntries_getMultiplicity_zero_of_head_mismatch
      (rows := rows) (data := data) (expected := 2) (actual := 0)
      hkind (fun r => blockWrapperState_raw_head blockAir r) (by decide)
  have hmsg1_zero :
      InteractionList.get_multiplicity
        (rows.map (fun r => (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg1Entry blockAir r).toRaw)) data = 0 :=
    mappedEntries_getMultiplicity_zero_of_head_mismatch
      (rows := rows) (data := data) (expected := 2) (actual := 1)
      hkind (fun r => blockWrapperMsg1_raw_head blockAir r) (by decide)
  have hmsg2_count :
      InteractionList.get_multiplicity
        (rows.map (fun r => (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir r).toRaw)) data =
      -(((rows.countP P : ℕ) : FBB) : FBB) := by
    simpa [rows, data, P] using blockMsg2Entries_getMultiplicity_eq_neg_countP blockAir rows hc data
  have hwindow := blockWindowSupported_of_start_le blockAir start hstart hsel hrot hc
  have hshape := blockWindowHasShape_of_constraints blockAir start hwindow hsel hrot hc
  have hsel2 : encoder_selector_idx blockAir (start + 2) = 2 := by
    simpa using (hshape.2.1 2 (by omega)).1
  have hround2 : is_round_row blockAir (start + 2) = 1 := (hshape.2.1 2 (by omega)).2.1
  have hdigest2 : is_digest_row blockAir (start + 2) = 0 := (hshape.2.1 2 (by omega)).2.2
  have hreal2 : is_round_row blockAir (start + 2) + is_digest_row blockAir (start + 2) = 1 := by
    simpa [hround2, hdigest2]
  have hf2 : flag_constraints blockAir (start + 2) := (hc (start + 2)).1
  have hactive2 :
      (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir (start + 2)).multiplicity = -1 :=
    blockWrapperMsg2_active_of_selector_two blockAir (start + 2) hf2 hreal2 hsel2
  have hcount_lt : rows.countP P < BB_prime := by
    have hcount_le : rows.countP P ≤ rows.length := by
      rw [List.countP_eq_length_filter]
      have hlen :
          rows.length = (rows.filter P).length + (rows.filter (!P ·)).length := by
        simpa using List.length_eq_length_filter_add (l := rows) P
      omega
    have hrows_len : rows.length < BB_prime := by
      simpa [rows] using htrace_fit
    exact lt_of_le_of_lt hcount_le hrows_len
  have hcount_ne : rows.countP P ≠ 0 := by
    intro hzero
    have hfilter_nil : rows.filter P = [] := by
      apply List.length_eq_zero_iff.mp
      simpa [List.countP_eq_length_filter] using hzero
    have hmem_filter : start + 2 ∈ rows.filter P := by
      apply List.mem_filter.mpr
      constructor
      · dsimp [rows]
        dsimp [blockWindowSupported] at hwindow
        exact List.mem_range.mpr (by omega)
      · simp [P, data, hactive2]
    have : False := by simpa [hfilter_nil] using hmem_filter
    exact False.elim this
  have hmsg2_nonzero :
      InteractionList.get_multiplicity
        (rows.map (fun r => (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir r).toRaw)) data ≠ 0 := by
    rw [hmsg2_count]
    apply neg_ne_zero.mpr
    exact natCast_ne_zero_of_lt_BB_prime hcount_lt hcount_ne
  intro hzero
  have hsum_components :
      InteractionList.get_multiplicity
        (Sha2BlockHasherVmAir_sha512.constraints.wrapperBus_trace blockAir) data =
      InteractionList.get_multiplicity
        (rows.map (fun r => (Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir r).toRaw) ++
          rows.map (fun r => (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg1Entry blockAir r).toRaw) ++
          rows.map (fun r => (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir r).toRaw)) data := by
        simpa [rows, Sha2BlockHasherVmAir_sha512.constraints.wrapperBus_trace] using
          get_multiplicity_inv_perm htrace_perm data
  have hmsg2_zero' :
      InteractionList.get_multiplicity
        (rows.map (fun r => (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir r).toRaw)) data = 0 := by
    rw [hsum_components, InteractionList.get_multiplicity_append, InteractionList.get_multiplicity_append] at hzero
    have hstate_zero'' :
        InteractionList.get_multiplicity
          (rows.map (fun r =>
            ((Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir r).multiplicity,
              (Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir r).message_type ::
                (Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir r).request_id ::
                  ((Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir r).prev_state_u16.toList ++
                    (Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir r).new_state_bytes.toList)))) data = 0 := by
      simpa using hstate_zero
    have hmsg1_zero' :
        InteractionList.get_multiplicity
          (rows.map (fun r =>
            ((Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg1Entry blockAir r).multiplicity,
              (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg1Entry blockAir r).message_type ::
                (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg1Entry blockAir r).request_id ::
                  ((Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg1Entry blockAir r).local_msg_bytes.toList ++
                    (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg1Entry blockAir r).next_msg_bytes.toList)))) data = 0 := by
      simpa using hmsg1_zero
    simpa [hstate_zero'', hmsg1_zero', add_assoc] using hzero
  exact hmsg2_nonzero hmsg2_zero'

end SharedBridge

end Sha2CompressionBridge_sha512
