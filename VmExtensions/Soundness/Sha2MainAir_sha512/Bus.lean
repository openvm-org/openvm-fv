import VmExtensions.Constraints.Sha2MainAirBus_sha512
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.Core.FieldArithmetic

set_option autoImplicit false
set_option linter.all false
set_option maxHeartbeats 1_000_000_000

namespace Sha2MainAir_sha512.Soundness

open BabyBear
open Sha2BlockHasherVmAir_sha512.BlockSpec
open Sha2MainAir_sha512.constraints

section WrapperPayload

variable {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]

/-- Proof-side wrapper payload contract for one `Sha2MainAir` row. -/
def wrapperPayloadSpec (air : C F ExtF) (row : ℕ) : Prop :=
  let state := wrapperStateEntry air row
  let msg1 := wrapperMsg1Entry air row
  let msg2 := wrapperMsg2Entry air row
  state.multiplicity = is_enabled air row ∧
  state.message_type = 0 ∧
  state.request_id = request_id air row ∧
  msg1.multiplicity = is_enabled air row ∧
  msg1.message_type = 1 ∧
  msg1.request_id = request_id air row ∧
  msg2.multiplicity = is_enabled air row ∧
  msg2.message_type = 2 ∧
  msg2.request_id = request_id air row ∧
  (∀ i : Fin 32, state.prev_state_u16.get i = prev_state_u16 air i.1 row) ∧
  (∀ i : Fin 64, state.new_state_bytes.get i = new_state_byte air i.1 row) ∧
  (∀ i : Fin 32, msg1.local_msg_bytes.get i = message_byte air i.1 row) ∧
  (∀ i : Fin 32, msg1.next_msg_bytes.get i = message_byte air (32 + i.1) row) ∧
  (∀ i : Fin 32, msg2.local_msg_bytes.get i = message_byte air (64 + i.1) row) ∧
  (∀ i : Fin 32, msg2.next_msg_bytes.get i = message_byte air (96 + i.1) row)

@[simp] theorem wrapperStateEntry_multiplicity
    (air : C F ExtF) (row : ℕ) :
    (wrapperStateEntry air row).multiplicity = is_enabled air row := by
  rfl

@[simp] theorem wrapperStateEntry_message_type
    (air : C F ExtF) (row : ℕ) :
    (wrapperStateEntry air row).message_type = 0 := by
  rfl

@[simp] theorem wrapperStateEntry_request_id
    (air : C F ExtF) (row : ℕ) :
    (wrapperStateEntry air row).request_id = request_id air row := by
  rfl

@[simp] theorem wrapperMsg1Entry_multiplicity
    (air : C F ExtF) (row : ℕ) :
    (wrapperMsg1Entry air row).multiplicity = is_enabled air row := by
  rfl

@[simp] theorem wrapperMsg1Entry_message_type
    (air : C F ExtF) (row : ℕ) :
    (wrapperMsg1Entry air row).message_type = 1 := by
  rfl

@[simp] theorem wrapperMsg1Entry_request_id
    (air : C F ExtF) (row : ℕ) :
    (wrapperMsg1Entry air row).request_id = request_id air row := by
  rfl

@[simp] theorem wrapperMsg2Entry_multiplicity
    (air : C F ExtF) (row : ℕ) :
    (wrapperMsg2Entry air row).multiplicity = is_enabled air row := by
  rfl

@[simp] theorem wrapperMsg2Entry_message_type
    (air : C F ExtF) (row : ℕ) :
    (wrapperMsg2Entry air row).message_type = 2 := by
  rfl

@[simp] theorem wrapperMsg2Entry_request_id
    (air : C F ExtF) (row : ℕ) :
    (wrapperMsg2Entry air row).request_id = request_id air row := by
  rfl

/-- The typed wrapper entries already expose the exact request-id and byte
payload interface needed by the row-level opcode theorem. -/
theorem wrapperPayload_of_row
    (air : C F ExtF) (row : ℕ) :
    wrapperPayloadSpec air row := by
  simpa [wrapperPayloadSpec]

end WrapperPayload

section TraceConstraints

variable {C : Type → Type → Type} {ExtF : Type} [Field ExtF] [Circuit FBB ExtF C]

/-- The theorem-facing SHA-512 main-trace package: extracted interactions
plus the extracted row constraints needed by the wrapper-bus permutation
bridge. -/
structure mainTraceConstraints (air : C FBB ExtF) : Prop where
  constrain_interactions :
    Sha2MainAir_Sha512Config.extraction.constrain_interactions air
  rows :
    ∀ row, Sha2MainAir_Sha512Config.extraction.constrain_row air row

instance (air : C FBB ExtF) : CoeFun (mainTraceConstraints air) (fun _ => ∀ row,
    Sha2MainAir_Sha512Config.extraction.constrain_row air row) where
  coe hc := hc.rows

namespace mainTraceConstraints

theorem constraint_0
    {air : C FBB ExtF}
    (hc : mainTraceConstraints air) (row : ℕ) :
    Sha2MainAir_sha512.constraints.constraint_0 air row := by
  -- human.0 ≡ ext.2 (extractor reorders 0..3); feed the ext.2 conjunct.
  exact (Sha2MainAir_sha512.constraints.constraint_2_of_extraction air row).mp (hc row).2.2.1

theorem constraint_1
    {air : C FBB ExtF}
    (hc : mainTraceConstraints air) (row : ℕ) :
    Sha2MainAir_sha512.constraints.constraint_1 air row := by
  -- human.1 ≡ ext.3; feed the ext.3 conjunct.
  exact (Sha2MainAir_sha512.constraints.constraint_3_of_extraction air row).mp (hc row).2.2.2.1

theorem constraint_2
    {air : C FBB ExtF}
    (hc : mainTraceConstraints air) (row : ℕ) :
    Sha2MainAir_sha512.constraints.constraint_2 air row := by
  -- human.2 ≡ ext.0; feed the ext.0 conjunct.
  exact (Sha2MainAir_sha512.constraints.constraint_0_of_extraction air row).mp (hc row).1

theorem constraint_3
    {air : C FBB ExtF}
    (hc : mainTraceConstraints air) (row : ℕ) :
    Sha2MainAir_sha512.constraints.constraint_3 air row := by
  -- human.3 ≡ ext.1; feed the ext.1 conjunct.
  exact (Sha2MainAir_sha512.constraints.constraint_1_of_extraction air row).mp (hc row).2.1

/-- The extracted boolean gate implies `is_enabled ∈ {0,1}`. -/
theorem enabled_boolean
    {air : C FBB ExtF}
    (hc : mainTraceConstraints air) (row : ℕ) :
    is_enabled air row = 0 ∨ is_enabled air row = 1 := by
  exact bit_boolean_of_sq_eq_zero _ (hc.constraint_2 row)

/-- On the valid trace, enabled rows carry request ids equal to their row
index. This is derived from the extracted first-row / transition constraints
and the explicit rotation-consistency hypothesis. -/
theorem request_id_eq_row
    {air : C FBB ExtF}
    (hc : mainTraceConstraints air)
    (hrot : rotation_consistent air) :
    ∀ {row : ℕ}, row ≤ Circuit.last_row air →
      is_enabled air row = 1 →
      request_id air row = (row : FBB)
  | 0, _, h_enabled => by
      have h0 := hc.constraint_0 0
      have hreq0 : request_id air 0 = 0 := by
        simp [Sha2MainAir_sha512.constraints.constraint_0, Circuit.isFirstRow, h_enabled] at h0
        exact h0
      simpa using hreq0
  | row + 1, hvalid, h_enabled => by
      have hrow_lt : row < Circuit.last_row air := by omega
      have hnext_enabled_eq :
          next_is_enabled air row = is_enabled air (row + 1) := by
        simpa [next_is_enabled, is_enabled] using
          next_main_eq_main_succ air hrot 257 row hrow_lt
      have hnext_enabled : next_is_enabled air row = 1 := by
        rw [hnext_enabled_eq]
        exact h_enabled
      have h3 := hc.constraint_3 row
      have hprev_enabled_sub :
          is_enabled air row - 1 = 0 := by
        have htransition : Circuit.isTransitionRow air row = 1 := by
          simp [Circuit.isTransitionRow, Nat.ne_of_lt hrow_lt]
        simpa [Sha2MainAir_sha512.constraints.constraint_3, htransition, hnext_enabled] using h3
      have hprev_enabled : is_enabled air row = 1 := sub_eq_zero.mp hprev_enabled_sub
      have h1 := hc.constraint_1 row
      have htransition : Circuit.isTransitionRow air row = 1 := by
        simp [Circuit.isTransitionRow, Nat.ne_of_lt hrow_lt]
      have hnext_request_step :
          next_request_id air row = request_id air row + 1 := by
        have hnext_request_sub :
            next_request_id air row - (request_id air row + 1) = 0 := by
          simpa [Sha2MainAir_sha512.constraints.constraint_1, htransition, hnext_enabled] using h1
        exact sub_eq_zero.mp hnext_request_sub
      have hnext_request_eq :
          next_request_id air row = request_id air (row + 1) := by
        simpa [next_request_id, request_id] using
          next_main_eq_main_succ air hrot 0 row hrow_lt
      have hprev_request :
          request_id air row = (row : FBB) :=
        request_id_eq_row hc hrot (show row ≤ Circuit.last_row air by omega) hprev_enabled
      calc
        request_id air (row + 1) = next_request_id air row := hnext_request_eq.symm
        _ = request_id air row + 1 := hnext_request_step
        _ = ((row : ℕ) : FBB) + 1 := by rw [hprev_request]
        _ = ((row + 1 : ℕ) : FBB) := by simpa [Nat.cast_add]

/-- Equality of request ids on enabled, valid rows collapses to row equality.
This follows from raw row constraints, trace-length fit, and rotation
consistency. -/
theorem enabled_request_id_injective
    {air : C FBB ExtF}
    (hc : mainTraceConstraints air)
    (hrot : rotation_consistent air)
    (htrace_fit : traceLengthFitsField air)
    (r1 r2 : ℕ)
    (hr1 : r1 ≤ Circuit.last_row air)
    (hr2 : r2 ≤ Circuit.last_row air)
    (h_enabled1 : is_enabled air r1 = 1)
    (h_enabled2 : is_enabled air r2 = 1)
    (hreq : request_id air r1 = request_id air r2) :
    r1 = r2 := by
  have hreq1 :
      request_id air r1 = (r1 : FBB) :=
    request_id_eq_row hc hrot hr1 h_enabled1
  have hreq2 :
      request_id air r2 = (r2 : FBB) :=
    request_id_eq_row hc hrot hr2 h_enabled2
  have hcast : ((r1 : ℕ) : FBB) = (r2 : FBB) := by
    calc
      ((r1 : ℕ) : FBB) = request_id air r1 := hreq1.symm
      _ = request_id air r2 := hreq
      _ = (r2 : FBB) := hreq2
  have hlast_lt : Circuit.last_row air < BB_prime := by
    have htrace_fit' : Circuit.last_row air + 1 < BB_prime := htrace_fit
    omega
  have hr1_lt : r1 < BB_prime := lt_of_le_of_lt hr1 hlast_lt
  have hr2_lt : r2 < BB_prime := lt_of_le_of_lt hr2 hlast_lt
  have hval := congrArg Fin.val hcast
  simp [Nat.mod_eq_of_lt hr1_lt, Nat.mod_eq_of_lt hr2_lt] at hval
  exact hval

end mainTraceConstraints

end TraceConstraints

end Sha2MainAir_sha512.Soundness
