import OpenvmFv.Fundamentals.BabyBear
import OpenvmFv.Fundamentals.Transpiler

import LeanZKCircuit.Interactions

set_option maxHeartbeats 1_000_000_000

attribute [simp]
  List.filter_cons
  List.map_flatMap

attribute [-simp]
  Fin.val_fin_le
  exists_and_left
  exists_and_right
  List.minimum_of_length_pos_le_iff
  List.le_maximum_of_length_pos_iff

attribute [local grind]
  Fin.add_def
  Fin.neg_def
  Fin.val_natCast

namespace Interaction

  section buses

    variable
      (F : Type)
      [Field F]

    instance : Inhabited F := by exact Inhabited.mk 0

    /-- Type class for generic bus entries -/
    class BusEntry (α : Type*) where
      multiplicity : α → F

      data_length : ℕ
      data : α → Vector F data_length

      -- Unconditional assumptions on bus entries
      assumptions : α → Prop

      -- Well-formedness properties of bus entries
      wf_properties : α → Prop
      -- Condition under which well-formedness properties are assumed
      wf_assume_cond : α → Prop
      -- Condition under which well-formedness properties need to be asserted
      wf_assert_cond : α → Prop
      -- Assuming and proving of well-formedness properties
      assume (a : α) := wf_assume_cond a → wf_properties a
      assert (a : α) := wf_assert_cond a → wf_properties a

      -- Serialization, deserialization, inverses
      serialise (x : α) := (multiplicity x, data x)
      serialiseToList (x : α) := (multiplicity x, (data x).toList)
      deserialise : F × Vector F data_length → α

      inv_ser_deser (x : F × Vector F data_length) : serialise (deserialise x) = x
      inv_deser_ser {x : α} : deserialise (serialise x) = x

    section ExecutionBus

      /-- Execution bus entry -/
      structure ExecutionBusEntry where
        multiplicity : F
        pc : F
        timestamp : F

      @[simp, grind]
      def ExecutionBusEntry.deserialise
        (entry : F × Vector F 2)
      : ExecutionBusEntry F :=
        {
            multiplicity := entry.1,
            pc := entry.2[0],
            timestamp := entry.2[1]
        }

      /-- Execution bus entry instance -/
      @[simp, grind]
      instance ExecutionBusEntryInstance
      : BusEntry FBB (ExecutionBusEntry FBB) :=
      {
          multiplicity := fun entry => entry.1,

          data_length := 2,
          data := fun ⟨_, pc, timestamp⟩ => #v[pc, timestamp],

          -- `pc`s are always less than `2^30`,
          -- timestamps are always less than `2^29`.
          assumptions :=
            fun ⟨multiplicity, pc, timestamp⟩ =>
              ¬ multiplicity = 0 →
                pc < 2^30 ∧ pc % 4 = 0

          -- An execution bus entry has no assume/prove properties
          wf_properties := fun ⟨_, pc, _⟩ => True

          wf_assume_cond := fun entry => entry.1 = -1,
          wf_assert_cond := fun entry => entry.1 = 1,

          deserialise := ExecutionBusEntry.deserialise FBB

          inv_deser_ser := by simp
          inv_ser_deser := by
            simp_all
            intro b; cases b
            simp_all; grind
      }

    end ExecutionBus

    section MemoryBus

      /-- Memory bus entry -/
      structure MemoryBusEntry where
        multiplicity : F
        as : F
        ptr : F
        x0 : F
        x1 : F
        x2 : F
        x3 : F
        timestamp : F

      @[simp, grind]
      def MemoryBusEntry.deserialise
        (entry : FBB × Vector FBB 7)
      : MemoryBusEntry F :=
        {
          multiplicity := entry.1,
          as := entry.2[0],
          ptr := entry.2[1],
          x0 := entry.2[2],
          x1 := entry.2[3],
          x2 := entry.2[4],
          x3 := entry.2[5],
          timestamp := entry.2[6]
        }

      /-- Memory bus entry instance -/
      @[simp, grind]
      instance MemoryBusEntryInstance
      : BusEntry FBB (MemoryBusEntry FBB) :=
      {
          multiplicity := fun entry => entry.1,

          data_length := 7,
          data := fun ⟨_, as, ptr, x0, x1, x2, x3, timestamp⟩ =>
                    #v[as, ptr, x0, x1, x2, x3, timestamp],

          -- Timestamps are always less than `2^29`
          assumptions := fun ⟨multiplicity, _, _, _, _, _, _, timestamp⟩ =>
                           ¬ multiplicity = 0 → timestamp < 2 ^ 29

          -- Values already in memory are constrained in range
          wf_properties :=
            fun ⟨_, as, ptr, x0, x1, x2, x3, _⟩ =>
              as.val < 3 ∧
              ptr.val < 2 ^ 29 ∧
              x0.val < 256 ∧ x1.val < 256 ∧
              x2.val < 256 ∧ x3.val < 256

          wf_assume_cond := fun entry => entry.1 = -1,
          wf_assert_cond := fun entry => entry.1 = 1,

          deserialise := MemoryBusEntry.deserialise FBB

          inv_deser_ser := by simp
          inv_ser_deser := by
            simp_all
            intro b; cases b
            simp_all; grind (splits := 15) (gen := 10)
      }

    end MemoryBus

    section RangeCheckerBus

      /-- Range-checking bus entry -/
      structure RangeCheckerBusEntry where
        multiplicity : F
        val : F
        deg : F

      @[simp, grind]
      def RangeCheckerBusEntry.deserialise
        (entry : F × Vector F 2)
      : RangeCheckerBusEntry F :=
        {
            multiplicity := entry.1,
            val := entry.2[0],
            deg := entry.2[1],
        }

      /-- Range-checking bus entry -/
      @[simp, grind]
      instance RangeCheckerBusEntryInstance
      : BusEntry FBB (RangeCheckerBusEntry FBB) :=
      {
          multiplicity := fun entry => entry.1,

          data_length := 2,
          data := fun ⟨_, val, deg⟩ => #v[val, deg],

          -- No assumptions
          assumptions := fun _ => True

          -- The range checking bus checks that the
          -- value is less than 2 to the degree
          wf_properties :=
            fun ⟨_, val, deg⟩ =>
              -- `deg` range
              deg.val < 31 ∧
              -- `val` range
              val.val < 2 ^ deg.val

          wf_assume_cond := fun entry => entry.1 = 1,
          wf_assert_cond := fun entry => entry.1 = -1,

          deserialise := RangeCheckerBusEntry.deserialise FBB

          inv_deser_ser := by simp
          inv_ser_deser := by
            simp_all
            intro b; cases b
            simp_all; grind
      }

    end RangeCheckerBus

    section ReadInstructionBus

      /-- Read-instruction bus entry -/
      structure ReadInstructionBusEntry where
        multiplicity : F
        pc : F
        opcode : F
        xa : F
        xb : F
        xc : F
        xd : F
        xe : F
        xf : F
        xg : F

      @[simp, grind]
      def ReadInstructionBusEntry.deserialise
        (entry : FBB × Vector FBB 9)
      : ReadInstructionBusEntry F :=
        {
          multiplicity := entry.1,
          pc := entry.2[0],
          opcode := entry.2[1],
          xa := entry.2[2],
          xb := entry.2[3],
          xc := entry.2[4],
          xd := entry.2[5],
          xe := entry.2[6],
          xf := entry.2[7],
          xg := entry.2[8]
        }

      def ReadInstructionBusEntry.operand_properties (entry : ReadInstructionBusEntry FBB) : Prop :=
        ∃ instruction data,
          (Transpiler.transpile_op instruction entry.multiplicity entry.pc = .some data) ∧
          (ReadInstructionBusEntry.deserialise FBB data = entry)

      /-- Read-instruction bus entry instance -/
      @[simp, grind]
      instance ReadInstructionBusEntryInstance
      : BusEntry FBB (ReadInstructionBusEntry FBB) :=
      {
          multiplicity := fun entry => entry.1,

          data_length := 9,
          data := fun ⟨_, pc, opcode, xa, xb, xc, xd, xe, xf, xg⟩ =>
                    #v[pc, opcode, xa, xb, xc, xd, xe, xf, xg],

          -- No assumptions
          assumptions := fun _ => True

          -- No well-formedness properties imposed right now
          wf_properties := ReadInstructionBusEntry.operand_properties
          wf_assume_cond := fun entry => entry.1 = 1,
          wf_assert_cond := fun entry => entry.1 = -1,

          deserialise := ReadInstructionBusEntry.deserialise FBB

          inv_deser_ser := by simp
          inv_ser_deser := by
            simp_all
            intro b; cases b
            simp_all; grind (splits := 18) (gen := 12) (ematch := 11)
      }

    end ReadInstructionBus

    section BitwiseBus

      /-- Bitwise bus entry -/
      structure BitwiseBusEntry where
        multiplicity : F
        a : F
        b : F
        c : F
        op : F

      @[simp, grind]
      def BitwiseBusEntry.deserialise
        (entry : F × Vector F 4)
      : BitwiseBusEntry F :=
        {
            multiplicity := entry.1,
            a := entry.2[0],
            b := entry.2[1],
            c := entry.2[2],
            op := entry.2[3]
        }

      /-- Bitwise bus entry instance -/
      @[simp, grind]
      instance BitwiseBusEntryInstance
      : BusEntry FBB (BitwiseBusEntry FBB) :=
      {
          multiplicity := fun entry => entry.1,

          data_length := 4,
          data := fun ⟨_, a, b, c, op⟩ => #v[a, b, c, op],

          -- No assumptions
          assumptions := fun _ => True

          -- The bitwise bus range checks operands and
          -- possibly performs a `xor`
          wf_properties :=
            fun ⟨_, a, b, c, op⟩ =>
              -- operand range
              a.val < 256 ∧ b.val < 256 ∧
              -- xor indicator range
              (op = 0 ∨ op = 1) ∧
              -- xor or nothing
              c.val = if op = 0 then 0 else a.val ^^^ b.val

          wf_assume_cond := fun entry => entry.1 = 1,
          wf_assert_cond := fun entry => entry.1 = -1,

          deserialise := BitwiseBusEntry.deserialise FBB

          inv_deser_ser := by simp
          inv_ser_deser := by
            simp_all
            intro b; cases b
            simp_all; grind
      }

    end BitwiseBus

    section RangeTupleCheckerBus

      /-- Execution bus entry -/
      structure RangeTupleCheckerBusEntry where
        multiplicity : F
        x1 : F
        x2 : F

      @[simp, grind]
      def RangeTupleCheckerBusEntry.deserialise
        (entry : F × Vector F 2)
      : RangeTupleCheckerBusEntry F :=
        {
            multiplicity := entry.1,
            x1 := entry.2[0],
            x2 := entry.2[1]
        }

      /-- Execution bus entry instance -/
      @[simp, grind]
      instance RangeTupleCheckerBusEntryInstance
      : BusEntry FBB (RangeTupleCheckerBusEntry FBB) :=
      {
          multiplicity := fun entry => entry.1,

          data_length := 2,
          data := fun ⟨_, x1, x2⟩ => #v[x1, x2],

          -- No assumptions
          assumptions := fun _ => True

          -- The tuple range checker checks the appropriate ranges
          wf_properties := fun ⟨_, x1, x2⟩ => x1.val < 256 ∧ x2.val < 2048

          wf_assume_cond := fun entry => entry.1 = 1,
          wf_assert_cond := fun entry => entry.1 = -1,

          deserialise := RangeTupleCheckerBusEntry.deserialise FBB

          inv_deser_ser := by simp
          inv_ser_deser := by
            simp_all
            intro b; cases b
            simp_all; grind
      }

    end RangeTupleCheckerBus

  end buses

end Interaction

namespace List

/-- Strong induction on lists -/
@[elab_as_elim]
def strongInductionOn
  {P : List T → Prop}
  (l : List T)
  (ih : ∀ (l : List T), (∀ (l' : List T), l'.length < l.length → P l') → P l)
:
  P l
:=
  (ih l) fun l' _ => strongInductionOn l' ih
  termination_by (List.length l)

/-- Take is idempotent if it is of at least equal length -/
lemma take_eq_self
  {l : List T}
  {n : ℕ}
  (h_len : l.length ≤ n)
:
  l.take n = l
:= by
  simpa [List.take_eq_self_iff]

/-- `Forall` of `True` with `id` always holds -/
@[simp, grind]
lemma forall_id_true {len : ℕ}
:
  List.Forall id (List.replicate len True)
:= by
  induction len <;> simp_all [List.replicate_add]

end List

namespace BabyBear

  /-- Only zero equals its negation in BabyBear -/
  @[simp, grind]
  lemma eq_neg_eq_zero (m : FBB) : -m = m ↔ m = 0 := by grind

end BabyBear

namespace InteractionList

  open InteractionList

  /-- Invariance of `is_balanced` under permutation -/
  lemma is_balanced_inv_perm
    [BEq F]
    [Field F]
    {bus bus' : List (F × List F)}
    (h_bal_bus : is_balanced bus)
    (h_perm : bus.Perm bus')
  :
    is_balanced bus'
  := by
    simp [is_balanced, get_multiplicity] at *
    intro data; specialize h_bal_bus data
    rw [← h_bal_bus, List.Perm.sum_eq]
    rw [List.perm_comm] at h_perm
    grind

  /-- Invariance of `is_balanced` under bijective mapping. -/
  lemma is_balanced_inv_bijection
    [BEq F]
    [LawfulBEq F]
    [Field F]
    {bus : List (F × List F)}
    (f : List F → List F)
    {f_bi : Function.Bijective f}
  :
    is_balanced bus ↔ is_balanced (bus.map (fun (m, data) ↦ (m, f data)))
  := by
    simp [is_balanced, get_multiplicity,
          Function.Bijective, Function.Injective, Function.Surjective] at *
    obtain ⟨ f_inj, f_sur ⟩ := f_bi
    constructor
    . intro hyp data
      obtain ⟨ d', eq_d' ⟩ := f_sur data
      specialize hyp d'
      rw [← hyp]; clear hyp
      induction bus
      case nil => simp
      case cons hd tl ih =>
        obtain ⟨ m, d ⟩ := hd; simp
        split_ifs with h h' <;> simp_all
        absurd h'; apply f_inj; grind
    . intro hyp data
      specialize hyp (f data)
      rw [← hyp]; clear hyp
      induction bus
      case nil => simp
      case cons hd tl ih =>
        obtain ⟨ m, d ⟩ := hd; simp
        split_ifs with h h' <;> simp_all
        absurd h; apply f_inj; assumption

  -- Non-zero-multiplicity bus filtering and its properties
  section non_zero

    /-- Non-zero multiplicity filter -/
    def non_zero
      [BEq F]
      [Field F]
      (bus : List (F × List F))
    : List (F × List F) :=
      List.filter (fun (a, _) ↦ !(a == 0)) bus

    /-- Invariance of `get_multiplicity` under `non_zero` -/
    lemma non_zero_inv_sum
      [BEq F]
      [LawfulBEq F]
      [Field F]
      (bus : List (F × List F))
      (data : List F)
    :
      get_multiplicity bus data = get_multiplicity (non_zero bus) data
    := by
      simp [get_multiplicity, non_zero]
      induction bus <;> grind

    /-- Invariance of non-zero multiplicity under permutation -/
    lemma non_zero_inv_is_balanced
      [BEq F]
      [LawfulBEq F]
      [Field F]
      (bus : List (F × List F))
    :
      is_balanced bus ↔ is_balanced (non_zero bus)
    := by
      simp [is_balanced]
      have := non_zero_inv_sum bus
      grind

  end non_zero

  section unitary_buses

    /-- Unitary-with-zero buses: buses with only -1, 0, 1 multiplicities -/
    def unitary_with_zero
      [Field F]
      (bus : List (F × List F))
    : Prop :=
      forall entry, entry ∈ bus → entry.1 = -1 ∨ entry.1 = 0 ∨ entry.1 = 1

    /-- Unitary buses: buses with only -1, 1 multiplicities -/
    def unitary
      [Field F]
      (bus : List (F × List F))
    : Prop :=
      forall entry, entry ∈ bus → entry.1 = -1 ∨ entry.1 = 1

    /-- A unitary-with-zero bus under non-zero filtering becomes a unitary bus -/
    lemma unitary_zero_mult_non_zero_is_unitary
      [BEq F]
      [LawfulBEq F]
      [Field F]
      (bus : List (F × List F))
    :
      unitary_with_zero bus → unitary (non_zero bus)
    := by
      simp [unitary_with_zero, unitary, non_zero]
      grind

    /-- Invariance of unitary buses under permutation -/
    lemma unitary_inv_perm
      [Field F]
      {bus bus' : List (F × List F)}
      (h_perm : bus.Perm bus')
    :
      unitary bus ↔ unitary bus'
    := by
      unfold unitary
      grind

    /-- Compatibility of unitary buses under concatenation -/
    lemma unitary_append_iff
      [Field F]
      {bus bus' : List (F × List F)}
    :
      unitary (bus ++ bus') ↔ unitary bus ∧ unitary bus'
    := by
      unfold unitary
      simp; grind

    /-- Balanced arbitrary-multiplicity bus entry pair -/
    @[simp]
    def balanced_pair
      [Field F]
      (m : F)
      (data : List F)
    : List (F × List F) :=
      [
        ( m, data),
        (-m, data),
      ]

    /-- If a unitary bus is balanced and is not longer than `BB_prime`,
        and if we know an entry is on the bus, then we also know that
        its balancer is on the bus. -/
    lemma unitary_extract_balancer
      {bus : List (FBB × List FBB)}
      {m : FBB} {data : List FBB}
      (h_unitary : unitary bus)
      (h_balance : is_balanced bus)
      (h_len_bus : bus.length < BB_prime)
      (h_in_neg : (m, data) ∈ bus)
    :
      ∃ bus', bus.Perm (balanced_pair m data ++ bus')
    := by
      have m_neq_z : ¬ m = 0 := by apply h_unitary at h_in_neg; grind
      rw [← List.singleton_sublist] at h_in_neg
      apply List.Sublist.exists_perm_append at h_in_neg
      obtain ⟨ bus'', h_eq ⟩ := h_in_neg
      suffices h_in_pos : (-m, data) ∈ bus
      . rw [List.Perm.mem_iff h_eq] at h_in_pos
        simp_all
        rw [← List.singleton_sublist] at h_in_pos
        apply List.Sublist.exists_perm_append at h_in_pos
        grind
      . simp [List.Perm.mem_iff h_eq]; right
        apply is_balanced_inv_perm (h_perm := h_eq) at h_balance
        specialize h_balance data
        simp [get_multiplicity] at h_balance
        have h_len_bus'' : bus''.length < 2013265920
          := by simp [List.Perm.length_eq h_eq] at h_len_bus; omega
        rw [unitary_inv_perm h_eq] at h_unitary
        simp [unitary] at h_unitary
        obtain ⟨ split_m, split_bus'' ⟩ := h_unitary
        simp_all
        clear h_len_bus h_eq bus m_neq_z
        by_contra h_not_in
        replace h_balance : (List.map Prod.fst (List.filter (fun x ↦ x.2 == data) bus'')).sum = -m := by grind
        rcases split_m with eq_m | eq_m <;> simp_all <;> clear eq_m
        . suffices : ((0 : FBB) - bus''.length).val ≤ ((List.map Prod.fst (List.filter (fun x ↦ x.2 == data) bus'')).sum).val ∨
                    ((List.map Prod.fst (List.filter (fun x ↦ x.2 == data) bus'')).sum).val = 0
          . simp [Fin.neg_def] at this
            by_cases h_len : bus''.length = 0
            . simp_all
            . grind
          . clear h_balance
            induction bus''
            case this.nil => simp_all
            case this.cons hd tl ih =>
              obtain ⟨ m', data' ⟩ := hd
              simp_all
              specialize ih (by omega) (by grind)
              specialize split_bus'' m' data'; simp at split_bus''
              by_cases h_tl_len : tl.length = 0
              . split_ifs with h_data <;> simp_all
              . rcases ih with ihl | ihr
                . left; split_ifs <;>
                  (try simp_all [-List.length_eq_zero_iff, Fin.neg_def, Fin.add_def]) <;>
                  grind
                . split_ifs <;> simp_all [-List.length_eq_zero_iff]; grind
        . suffices : ((List.map Prod.fst (List.filter (fun x ↦ x.2 == data) bus'')).sum).val ≤ bus''.length ∨
                    ((List.map Prod.fst (List.filter (fun x ↦ x.2 == data) bus'')).sum).val = 0
          . grind
          . clear h_balance
            induction bus'' <;> grind

    /-- On a balanced unitary bus, there has to be an equal
        amount of sends and receives whose data abides by
        an *arbitrary predicate* `P`. -/
    lemma unitary_balanced_equal_predicate_count
      {bus : List (FBB × List FBB)}
      (P : List FBB → Bool)
      (μ : List FBB → FBB)
      (h_unitary : unitary bus)
      (h_balance : is_balanced bus)
      (h_len_bus : bus.length < BB_prime)
    :
      let s : List (FBB × List FBB) := bus.filter (fun (m, d) => m = -1 ∧ P d)
      let r : List (FBB × List FBB) := bus.filter (fun (m, d) => m =  1 ∧ P d)
      s.length = r.length
    := by
      revert P h_len_bus h_balance h_unitary μ
      refine List.strongInductionOn bus (fun bus ih => ?_)
      by_cases h_non_empty : 0 < bus.length
      . obtain ⟨ ⟨ m, data ⟩, h_in ⟩ := List.exists_mem_of_length_pos h_non_empty
        intro P μ h_unitary h_balanced h_length
        obtain ⟨ bus'', h_perm ⟩ := unitary_extract_balancer h_unitary h_balanced h_length h_in
        set bus' := balanced_pair m data ++ bus''
        let s' : List (FBB × List FBB) := bus'.filter (fun (m, d) => m = -1 ∧ P d)
        let r' : List (FBB × List FBB) := bus'.filter (fun (m, d) => m =  1 ∧ P d)
        extract_lets s r
        trans s'.length
        . apply List.Perm.length_eq; grind
        . trans r'.length
          . subst bus' s' r'
            simp_all [balanced_pair]
            have h_lt : bus''.length < bus.length := by
              apply List.Perm.length_eq at h_perm
              grind
            have h_unitary'' : unitary bus'' := by
              rw [unitary_inv_perm h_perm] at h_unitary
              simp [unitary] at h_unitary ⊢
              grind
            have h_balanced'' : is_balanced bus'' := by
              have : is_balanced (bus'' ++ [(m, data), (-m, data)]) := by
                grind [is_balanced_inv_perm]
              apply is_balanced_of_append_is_balanced _ _ _ this
              . simp [is_balanced, get_multiplicity]; grind
            have h_length'' : bus''.length < BB_prime := by grind [List.Perm.length_eq]
            specialize ih bus'' h_lt P h_unitary'' h_balanced'' h_length''
            grind
          . apply List.Perm.length_eq; grind
      . simp_all

  end unitary_buses

  section rising_buses

    variable
      -- Measure on bus data
      (μ : List FBB → ℕ)

    /-- Rising pairs are pairs whose send data
        is greater than their receive data
        according to some measure `mu` -/
    def rising_pair
      [Field F]
      (dr ds : List FBB)
      (_ : μ dr < μ ds)
    : List (F × List F) :=
      [
        (-1, dr),
        ( 1, ds)
      ]

    /-- Get receive data from bus data -/
    def recv_data
      (bus_data : List (List FBB × List FBB))
    : List (List FBB) :=
      List.map (fun x ↦ x.1) bus_data

    /-- Get send data from bus data -/
    def send_data
      (bus_data : List (List FBB × List FBB))
    : List (List FBB) :=
      List.map (fun x ↦ x.2) bus_data

    /-- All receives are in the bus data -/
    lemma recv_data_in_bus_data
      {dr : List FBB}
      {bus_data : List (List FBB × List FBB)}
      (dr_in_recv : dr ∈ recv_data bus_data)
    :
      ∃ (ds : List FBB), (dr, ds) ∈ bus_data
    := by
      induction bus_data
      case nil => simp_all [recv_data]
      case cons hd tl ih =>
        obtain ⟨ dr', ds' ⟩ := hd
        simp [recv_data] at *
        grind

    /-- All sends are in the bus data -/
    lemma send_data_in_bus_data
      {ds : List FBB}
      {bus_data : List (List FBB × List FBB)}
      (dr_in_recv : ds ∈ send_data bus_data)
    :
      ∃ (dr : List FBB), (dr, ds) ∈ bus_data
    := by
      induction bus_data
      case nil => simp_all [send_data]
      case cons hd tl ih =>
        obtain ⟨ dr', ds' ⟩ := hd
        simp [send_data] at *
        grind

    /-- Receive data can be split across an append modulo permutations -/
    lemma recv_data_perm_append_split
      (bus_data b1 b2 : List (List FBB × List FBB))
      (rd : List (List FBB))
      (h_perm_bus : bus_data.Perm (b1 ++ b2))
      (h_perm_recv : (recv_data bus_data).Perm (rd ++ recv_data b2))
    :
      rd.Perm (recv_data b1)
    := by
      revert bus_data
      refine List.strongInductionOn b2 (fun b2 ih => ?_)
      by_cases b2_not_empty : b2 = []
      . grind [recv_data]
      . obtain ⟨ b2', b2_last, b2_split ⟩ : ∃ b2' b2_last, b2 = b2' ++ [b2_last]
        := by
          exists b2.reverse.tail.reverse, b2.reverse.head (by simp_all)
          simp_all [List.dropLast_append_getLast]
        subst b2; clear b2_not_empty
        intro bus_data h_perm_bus h_perm_recv
        have : recv_data (b2' ++ [b2_last]) = recv_data b2' ++ recv_data [b2_last]
          := by simp [recv_data]
        rw [this, ← List.append_assoc] at h_perm_recv; clear this
        rw [← List.append_assoc] at h_perm_bus
        have ⟨ bus_data', bus_data_split ⟩ : ∃ bus_data', bus_data.Perm (bus_data' ++ [b2_last])
        := by
          have ⟨ bus_data', bus_data_split ⟩ := @List.Sublist.exists_perm_append _ [b2_last] bus_data (by grind)
          exists bus_data'; grind
        apply ih b2' (by simp) bus_data'
        . rw [← List.perm_append_right_iff [b2_last]]
          grind
        . rw [← List.perm_append_right_iff (recv_data [b2_last])]
          grind [recv_data]

    /-- Send data can be split across an append modulo permutations -/
    lemma send_data_perm_append_split
      (bus_data b1 b2 : List (List FBB × List FBB))
      (rd : List (List FBB))
      (h_perm_bus : bus_data.Perm (b1 ++ b2))
      (h_perm_recv : (send_data bus_data).Perm (rd ++ send_data b2))
    :
      rd.Perm (send_data b1)
    := by
      revert bus_data
      refine List.strongInductionOn b2 (fun b2 ih => ?_)
      by_cases b2_not_empty : b2 = []
      . grind [send_data]
      . obtain ⟨ b2', b2_last, b2_split ⟩ : ∃ b2' b2_last, b2 = b2' ++ [b2_last]
        := by
          exists b2.reverse.tail.reverse, b2.reverse.head (by simp_all)
          simp_all [List.dropLast_append_getLast]
        subst b2; clear b2_not_empty
        intro bus_data h_perm_bus h_perm_send
        have : send_data (b2' ++ [b2_last]) = send_data b2' ++ send_data [b2_last]
          := by simp [send_data]
        rw [this, ← List.append_assoc] at h_perm_send; clear this
        rw [← List.append_assoc] at h_perm_bus
        have ⟨ bus_data', bus_data_split ⟩ : ∃ bus_data', bus_data.Perm (bus_data' ++ [b2_last])
        := by
          have ⟨ bus_data', bus_data_split ⟩ := @List.Sublist.exists_perm_append _ [b2_last] bus_data (by grind)
          exists bus_data'; grind
        apply ih b2' (by simp) bus_data'
        . rw [← List.perm_append_right_iff [b2_last]]
          grind
        . rw [← List.perm_append_right_iff (send_data [b2_last])]
          grind [send_data]

    /-- Bus data entry can be deconstructed
        into receive and send data -/
    lemma bus_data_in_recv_send_lists
      {dr ds : List FBB}
      {bus_data : List (List FBB × List FBB)}
      (h_in : (dr, ds) ∈ bus_data)
    :
      dr ∈ recv_data bus_data ∧
      ds ∈ send_data bus_data
    := by
      induction bus_data
      case nil => simp_all
      case cons hd tl ih =>
        simp_all [recv_data, send_data]
        grind

    /-- Bus data is a direct `zip` of receive and send data -/
    lemma bus_data_is_zip
      (bus_data : List (List FBB × List FBB))
    :
      bus_data = List.zip (recv_data bus_data) (send_data bus_data)
    := by
      induction bus_data <;> simp [recv_data, send_data] at *; grind

    /-- A `rising_bus` is a bus consisting of rising pairs -/
    @[grind]
    def rising_bus
      (bus_data : List (List FBB × List FBB))
      (lt_proofs : ∀ entry ∈ bus_data, μ entry.1 < μ entry.2)
    : List (FBB × List FBB) :=
      List.flatten
        (List.map
          (fun (x : { y // y ∈ bus_data }) ↦
            let ⟨ ⟨ dr, ds ⟩ , pf ⟩ := x
            rising_pair μ dr ds (lt_proofs (dr, ds) pf )) bus_data.attach)

    /-- A rising bus has `2 * |bus_data|` entries -/
    lemma rising_bus_length
      {bus_data : List (List FBB × List FBB)}
      (lt_proofs : ∀ entry ∈ bus_data, μ entry.1 < μ entry.2)
    :
      (rising_bus μ bus_data lt_proofs).length = 2 * bus_data.length
    := by
      induction bus_data
      case nil => simp [rising_bus]
      case cons hd tl ih =>
        specialize ih (by grind)
        simp only [rising_bus,
                   List.attach_cons, List.map_cons, List.flatten_cons, List.length_cons,
                   List.length_append] at *
        conv => lhs; arg 1; simp [rising_pair]
        simp +arith at *
        rw [← ih]; congr

    /-- Receives and sends of rising bus data are on the rising bus -/
    lemma bus_data_in_rising_bus
      {dr ds : List FBB}
      {bus_data : List (List FBB × List FBB)}
      (lt_proofs : ∀ entry ∈ bus_data, μ entry.1 < μ entry.2)
      (h_in : (dr, ds) ∈ bus_data)
    :
      (-1, dr) ∈ rising_bus μ bus_data lt_proofs ∧
      ( 1, ds) ∈ rising_bus μ bus_data lt_proofs
    := by
      induction bus_data
      case nil => simp_all
      case cons hd tl ih =>
        simp_all [rising_bus, rising_pair]
        grind

    /-- A rising bus is a unitary bus -/
    lemma rising_bus_unitary
      (bus_data : List (List FBB × List FBB))
      (lt_proofs : ∀ entry ∈ bus_data, μ entry.1 < μ entry.2)
    :
      unitary (rising_bus μ bus_data lt_proofs)
    := by
      induction bus_data
      case nil => simp [unitary, rising_bus]
      case cons hd tl ih =>
        obtain ⟨ dr, ds ⟩ := hd
        simp_all [unitary, rising_bus, rising_pair]
        exact ih

    /-- All negative entries in a rising bus come from the receives -/
    lemma neg_ones_in_recv_data
      {dr : List FBB}
      {bus_data : List (List FBB × List FBB)}
      (lt_proofs : ∀ entry ∈ bus_data, μ entry.1 < μ entry.2)
      (h_in : (-1, dr) ∈ rising_bus μ bus_data lt_proofs)
    :
      dr ∈ recv_data bus_data
    := by
      induction bus_data
      case nil => grind
      case cons hd tl ihs =>
        obtain ⟨ dr', ds' ⟩ := hd
        simp_all [recv_data, rising_bus, rising_pair]
        rcases h_in with _ | h_tl <;> [ simp_all; right ]
        obtain ⟨ l, ⟨ ⟨ dr'', ds'', h_in'', eq_l ⟩, h_in ⟩ ⟩ := h_tl
        specialize ihs l dr'' ds'' h_in'' eq_l
        grind

    /-- All positive entries in a timestamp bus come from the sends -/
    lemma pos_ones_in_send_data
      {ds : List FBB}
      {bus_data : List (List FBB × List FBB)}
      (lt_proofs : ∀ entry ∈ bus_data, μ entry.1 < μ entry.2)
      (h_in : (1, ds) ∈ rising_bus μ bus_data lt_proofs)
    :
      ds ∈ send_data bus_data
    := by
      induction bus_data
      case nil => grind
      case cons hd tl ihs =>
        obtain ⟨ dr', ds' ⟩ := hd
        simp_all [send_data, rising_bus, rising_pair]
        rcases h_in with _ | h_tl <;> [ simp_all; right ]
        obtain ⟨ l, ⟨ ⟨ dr'', ds'', h_in'', eq_l ⟩, h_in ⟩ ⟩ := h_tl
        specialize ihs l dr'' ds'' h_in'' eq_l
        grind

    /-- Reconstructing receive data from a rising bus -/
    lemma recv_data_from_rising_bus
      {bus_data : List (List FBB × List FBB)}
      (lt_proofs : ∀ entry ∈ bus_data, μ entry.1 < μ entry.2)
    :
      (recv_data bus_data).Perm
        (List.filterMap (fun x ↦ if x.1 = -1 then some x.2 else none)
          (rising_bus μ bus_data lt_proofs))
    := by
      induction bus_data
      case nil => simp_all [rising_bus, recv_data]
      case cons hd tl ih =>
        obtain ⟨ m, d ⟩ := hd
        simp_all [rising_bus, rising_pair]
        simp [recv_data] at *
        exact ih

    /-- Reconstructing send data from a rising bus -/
    lemma send_data_from_rising_bus
      {bus_data : List (List FBB × List FBB)}
      (lt_proofs : ∀ entry ∈ bus_data, μ entry.1 < μ entry.2)
    :
      (send_data bus_data).Perm
        (List.filterMap (fun x ↦ if x.1 = 1 then some x.2 else none)
          (rising_bus μ bus_data lt_proofs))
    := by
      induction bus_data
      case nil => simp_all [rising_bus, send_data]
      case cons hd tl ih =>
        obtain ⟨ m, d ⟩ := hd
        simp_all [rising_bus, rising_pair]
        simp [send_data] at *
        exact ih

    /-- Splitting of a rising bus on its `n`th data pair -/
    lemma rising_bus_split
      {bus_data : List (List FBB × List FBB)}
      (lt_proofs : ∀ entry ∈ bus_data, μ entry.1 < μ entry.2)
      (n : ℕ)
    :
      ∃ lt_proofs₁ lt_proofs₂,
        rising_bus μ bus_data lt_proofs =
        rising_bus μ (bus_data.take n) lt_proofs₁ ++ rising_bus μ (bus_data.drop n) lt_proofs₂
    := by
      have lt₁ : ∀ entry ∈ List.take n bus_data, μ entry.1 < μ entry.2
      := by
        intro entry h_in; apply lt_proofs
        rw [List.mem_take_iff_getElem] at h_in
        grind
      have lt₂ : ∀ entry ∈ List.drop n bus_data, μ entry.1 < μ entry.2
      := by
        intro entry h_in; apply lt_proofs
        rw [List.mem_drop_iff_getElem] at h_in
        grind
      exists lt₁, lt₂
      trans rising_bus μ (List.take n bus_data ++ List.drop n bus_data) (by grind)
      . simp
      . simp [rising_bus]
        congr

    /-- A sublist of receive data can be found on its rising bus -/
    lemma recv_sublist_in_rising_bus
      {bus_data : List (List FBB × List FBB)}
      (lt_proofs : ∀ entry ∈ bus_data, μ entry.1 < μ entry.2)
      (h_sub : l.Sublist (recv_data bus_data))
    :
      (List.map (fun data ↦ (-1, data)) l).Sublist (rising_bus μ bus_data lt_proofs)
    := by
      induction l generalizing bus_data
      case nil => simp
      case cons d tl ih =>
        simp_all
        rw [List.cons_sublist_iff] at h_sub ⊢
        obtain ⟨ rd₁, rd₂, h_eq_rd, h_d_in, h_sub_tl ⟩ := h_sub
        have h_bus_len : bus_data.length = rd₁.length + rd₂.length := by
          have : (recv_data bus_data).length = (rd₁ ++ rd₂).length := by grind
          simp [recv_data] at *; assumption
        exists (List.take (2 * rd₁.length) (rising_bus μ bus_data lt_proofs))
        exists (List.drop (2 * rd₁.length) (rising_bus μ bus_data lt_proofs))
        have : ∃ sd₁ sd₂, sd₁.length = rd₁.length ∧ send_data bus_data = sd₁ ++ sd₂
        := by
          exists (List.take rd₁.length (send_data bus_data))
          exists (List.drop rd₁.length (send_data bus_data))
          simp_all [recv_data, send_data]
        obtain ⟨ sd₁, sd₂, h_eq_len, h_eq_sd ⟩ := this
        obtain ⟨ lt₁, lt₂, split ⟩ := rising_bus_split μ lt_proofs rd₁.length
        have len₁ := rising_bus_length μ lt₁
        have len₂ := rising_bus_length μ lt₂
        simp [h_bus_len] at len₁ len₂
        simp [split]
        rw [List.take_append, len₁]; simp
        rw [List.drop_append, len₁, List.drop_eq_nil_of_le (by omega)]; simp
        constructor
        . rw [List.take_eq_self (by omega)]
          have eq_rd₁ : rd₁ = recv_data (List.take rd₁.length bus_data) := by
            have := bus_data_is_zip bus_data
            rw [this, h_eq_rd, h_eq_sd]
            rw [List.zip_append (by omega)]
            simp [List.length_zip, h_eq_len]
            simp [recv_data]
            rw [List.map_fst_zip (by omega)]
          rw [eq_rd₁] at h_d_in
          obtain ⟨ ds, in_bus ⟩ := recv_data_in_bus_data h_d_in
          have := bus_data_in_rising_bus μ lt₁ in_bus
          tauto
        . apply ih (by grind)
          simp [recv_data] at *
          grind

    /-- Witness for minimal bus data -/
    lemma minimum_witness
      (data : List (List FBB))
      (h_not_empty : 0 < data.length)
    :
      ∃ d_min ∈ data,
      List.minimum_of_length_pos (l := List.map μ data) (by simpa) = μ d_min ∧
      ∀ d ∈ data, μ d_min ≤ μ d
    := by
      let μ_min := List.minimum_of_length_pos (l := List.map μ data) (by simpa)
      suffices : ∃ d_min ∈ data, μ d_min = μ_min
      . obtain ⟨ d_min, in_d_min, eq_d_min ⟩ := this
        exists d_min; simp_all [μ_min]
        intro d in_d
        have : μ d ∈ List.map μ data := by simp; tauto
        apply List.minimum_of_length_pos_le_of_mem this (by simpa)
      . have : μ_min ∈ List.map μ data := by apply List.minimum_of_length_pos_mem (by simpa)
        grind

    /-- Witness for maximal bus data -/
    lemma maximum_witness
      (data : List (List FBB))
      (h_not_empty : 0 < data.length)
    :
      ∃ d_max ∈ data,
        List.maximum_of_length_pos (l := List.map μ data) (by simpa) = μ d_max ∧
        ∀ d ∈ data, μ d ≤ μ d_max
    := by
      let μ_max := List.maximum_of_length_pos (l := List.map μ data) (by simpa)
      suffices : ∃ d_max ∈ data, μ d_max = μ_max
      . obtain ⟨ d_max, in_d_max, eq_d_max ⟩ := this
        exists d_max; simp_all [μ_max]
        intro d in_d
        have : μ d ∈ List.map μ data := by simp; tauto
        apply List.le_maximum_of_length_pos_of_mem this (by simpa)
      . have : μ_max ∈ List.map μ data := by apply List.maximum_of_length_pos_mem (by simpa)
        grind

    /-- The minimal receive data on a rising bus
        is strictly smaller in measure than all of the send data -/
    lemma recv_min_lt_sends
      (bus_data : List (List FBB × List FBB))
      (lt_proofs : ∀ entry ∈ bus_data, μ entry.1 < μ entry.2)
      (h_not_empty : 0 < bus_data.length)
    :
      List.minimum_of_length_pos (l := List.map μ (recv_data bus_data)) (by simp [recv_data]; omega)
        <
      List.minimum_of_length_pos (l := List.map μ (send_data bus_data)) (by simp [send_data]; omega)
    := by
      obtain ⟨ dr_min, in_dr_min, eq_dr_min, min_dr_min ⟩ := minimum_witness μ (recv_data bus_data) (by simp [recv_data]; omega)
      obtain ⟨ ds_min, in_ds_min, eq_ds_min, min_ds_min ⟩ := minimum_witness μ (send_data bus_data) (by simp [send_data]; omega)
      set r_min := List.minimum_of_length_pos (l := List.map μ (recv_data bus_data)) (by simp [recv_data]; omega)
      set s_min := List.minimum_of_length_pos (l := List.map μ (send_data bus_data)) (by simp [send_data]; omega)
      obtain ⟨ dr', h_in ⟩ := send_data_in_bus_data in_ds_min
      specialize lt_proofs _ h_in; simp at lt_proofs
      have ⟨ h_in_dr, h_in_ds ⟩ := bus_data_in_recv_send_lists h_in
      grind

    /-- The maximal send data on a rising bus
        is strictly larger in measure than all the receive data -/
    lemma send_max_gt_recvs
      (bus_data : List (List FBB × List FBB))
      (lt_proofs : ∀ entry ∈ bus_data, μ entry.1 < μ entry.2)
      (h_not_empty : 0 < bus_data.length)
    :
      List.maximum_of_length_pos (l := List.map μ (recv_data bus_data)) (by simp [recv_data]; omega)
        <
      List.maximum_of_length_pos (l := List.map μ (send_data bus_data)) (by simp [send_data]; omega)
    := by
      obtain ⟨ dr_max, in_dr_max, eq_dr_max, max_dr_max ⟩ := maximum_witness μ (recv_data bus_data) (by simp [recv_data]; omega)
      obtain ⟨ ds_max, in_ds_max, eq_ds_max, max_ds_max ⟩ := maximum_witness μ (send_data bus_data) (by simp [send_data]; omega)
      set r_max := List.maximum_of_length_pos (l := recv_data bus_data) (by simp [recv_data]; omega)
      set s_max := List.maximum_of_length_pos (l := send_data bus_data) (by simp [send_data]; omega)
      obtain ⟨ ds', h_in ⟩ := recv_data_in_bus_data in_dr_max
      specialize lt_proofs _ h_in; simp at lt_proofs
      have ⟨ h_in_dr, h_in_ds ⟩ := bus_data_in_recv_send_lists h_in
      grind

  end rising_buses

  section bus_balancing

    /-- On a balanced unitary bus, the sends and receives
        are permutations of each other -/
    lemma unitary_balanced_recvs_perm_sends
      {bus : List (FBB × List FBB)}
      (h_unitary : unitary bus)
      (h_balance : is_balanced bus)
      (h_len_bus : bus.length < BB_prime)
    :
      let recvs := List.filterMap (fun x ↦ if x.1 = -1 then some x.2 else none) bus
      let sends := List.filterMap (fun x ↦ if x.1 =  1 then some x.2 else none) bus
      recvs.Perm sends
    := by
      revert h_len_bus h_balance h_unitary
      refine List.strongInductionOn bus (fun bus ih => ?_)
      intro h_unitary h_balance h_len_bus
      simp_all
      by_cases bus_not_empty : bus = []
      . simp_all
      . obtain ⟨ ⟨ m, d ⟩, h_in ⟩ : ∃ entry, entry ∈ bus := by cases bus <;> aesop
        obtain ⟨ bus', h_perm ⟩  := unitary_extract_balancer h_unitary h_balance h_len_bus h_in
        simp [balanced_pair] at h_perm
        have h_unitary' : unitary bus'
        := by
          rw [unitary_inv_perm h_perm] at h_unitary
          grind [unitary]
        have h_balanced' : is_balanced bus'
        := by
          apply is_balanced_inv_perm (h_perm := h_perm) at h_balance
          clear *- h_balance
          simp [is_balanced, get_multiplicity] at *
          intro data; specialize h_balance data
          grind
        have h_length : bus'.length < bus.length := by grind [List.Perm.length_eq]
        specialize ih bus' h_length h_unitary' h_balanced' (by omega)
        set recv_extractor := List.filterMap (fun (x : FBB × List FBB) ↦ if x.1 = -1 then some x.2 else none)
        set send_extractor := List.filterMap (fun (x : FBB × List FBB) ↦ if x.1 =  1 then some x.2 else none)
        trans (recv_extractor ((m, d) :: (-m, d) :: bus'))
        . grind
        . trans (send_extractor ((m, d) :: (-m, d) :: bus'))
          . subst recv_extractor send_extractor
            have : m = -1 ∨ m = 1
            := by
              rw [unitary_inv_perm h_perm] at h_unitary
              grind [unitary]
            grind
          . grind

    /-- If a unitary bus of length less than `BB_prime` is balanced
        by a single send and a single receive, then it can be
        deconstructed into the corresponding balancers and the rest -/
    lemma single_balancer_decomposition
      {ldata rdata : List FBB}
      {bus : List (FBB × List FBB)}
      (h_unitary : unitary bus)
      (h_len_bus : ([(1, ldata)] ++ bus ++ [(-1, rdata)]).length < BB_prime)
      (h_balance : InteractionList.is_balanced ([((1 : FBB), ldata)] ++ bus ++ [((-1 : FBB), rdata)]))
    :
      (ldata = rdata → is_balanced bus) ∧
      (¬ ldata = rdata →
        exists bus',
          bus.Perm ([((-1 : FBB), ldata)] ++ bus' ++ [((1 : FBB), rdata)]) ∧
          is_balanced bus')
    := by
      constructor
      . intro heq; simp_all
        apply is_balanced_of_append_is_balanced (l₂ := [(1, rdata), (-1, rdata)])
        . intro data
          simp [get_multiplicity]
          split_ifs <;> simp_all
        . apply is_balanced_inv_perm h_balance
          grind
      . intro hneq
        suffices h_in : (-1, ldata) ∈ bus ∧ (1, rdata) ∈ bus
        . obtain ⟨ h_ld, h_rd ⟩ := h_in
          rw [← List.singleton_sublist] at h_ld
          apply List.Sublist.exists_perm_append at h_ld
          obtain ⟨ bus'', h_perm'' ⟩ := h_ld
          have h_rd' : (1, rdata) ∈ bus'' := by grind
          rw [← List.singleton_sublist] at h_rd'
          apply List.Sublist.exists_perm_append at h_rd'
          obtain ⟨ bus', h_perm' ⟩ := h_rd'
          have h_perm : bus.Perm ([(-1, ldata)] ++ bus' ++ [(1, rdata)]) := by grind
          exists bus'; simp_all
          have : List.Perm
                    ((1, ldata) :: (bus ++ [(-1, rdata)]))
                    ([(1, ldata), (-1, ldata)] ++ bus' ++ [(1, rdata), (-1, rdata)])
            := by grind
          apply is_balanced_of_append_is_balanced (l₂ := [(1, rdata), (-1, rdata)])
          . intro data
            simp [get_multiplicity]
            split_ifs <;> simp_all
          . apply is_balanced_of_append_is_balanced (l₂ := [(-1, ldata), (1, ldata)])
            . intro data
              simp [get_multiplicity]
              split_ifs <;> simp_all
            . apply is_balanced_inv_perm h_balance (by grind)
        . have : unitary ([(1, ldata)] ++ bus ++ [(-1, rdata)]) := by
            repeat rw [unitary_append_iff]
            simp_all; simp [unitary]
          have ⟨ bus_l, h_perm_l ⟩ := unitary_extract_balancer (m := 1) (data := ldata) this h_balance h_len_bus (by grind)
          have ⟨ bus_r, h_perm_r ⟩ := unitary_extract_balancer (m := -1) (data := rdata) this h_balance h_len_bus (by grind)
          simp [balanced_pair] at *
          suffices : (-1, ldata) ∈ bus ++ [(-1, rdata)] ∧ (1, rdata) ∈ (1, ldata) :: (bus ++ [(-1, rdata)])
          . grind
          . grind

    /-- A non-empty rising bus is never balanced -/
    lemma rising_bus_nonempty_not_balanced
      (bus_data : List (List FBB × List FBB))
      (lt_proofs : ∀ entry ∈ bus_data, μ entry.1 < μ entry.2)
      (h_not_empty : 0 < bus_data.length)
      (h_not_too_long : (rising_bus μ bus_data lt_proofs).length < BB_prime)
    :
      ¬ is_balanced (rising_bus μ bus_data lt_proofs)
    := by
      intro h_balanced
      have := recv_min_lt_sends μ bus_data lt_proofs h_not_empty
      obtain ⟨ dr_min, in_dr_min, eq_dr_min, min_dr_min ⟩ := minimum_witness μ (recv_data bus_data) (by simp [recv_data]; omega)
      obtain ⟨ ds_min, in_ds_min, eq_ds_min, min_ds_min ⟩ := minimum_witness μ (send_data bus_data) (by simp [send_data]; omega)
      set r_min := List.minimum_of_length_pos (l := List.map μ (recv_data bus_data)) (by simp [recv_data]; omega)
      set s_min := List.minimum_of_length_pos (l := List.map μ (send_data bus_data)) (by simp [send_data]; omega)
      obtain ⟨ ds', h_in ⟩ := recv_data_in_bus_data in_dr_min
      (have ⟨ dr_min_in, hb ⟩  := bus_data_in_rising_bus μ lt_proofs h_in); clear hb
      have h_unitary := rising_bus_unitary μ bus_data lt_proofs
      obtain ⟨ bus', h_perm ⟩ := unitary_extract_balancer h_unitary h_balanced h_not_too_long dr_min_in
      simp [balanced_pair] at h_perm
      obtain dr_min_in_send : dr_min ∈ send_data bus_data := by
        apply pos_ones_in_send_data (lt_proofs := lt_proofs)
        simp [List.Perm.mem_iff h_perm]
      grind

    /-- If a unitary non-empty bus of length less than `BB_prime`
        is balanced by a single send and a single receive, then
        these balancers are the minimal receive and the maximal send -/
    lemma single_boundary_balancers_of_rising_bus_are_min_and_max
      {ldata rdata : List FBB}
      (bus_data : List (List FBB × List FBB))
      (lt_proofs : ∀ entry ∈ bus_data, μ entry.1 < μ entry.2)
      (h_not_empty : 0 < bus_data.length)
      (h_len_bus : ([(1, ldata)] ++ (rising_bus μ bus_data lt_proofs) ++ [(-1, rdata)]).length < BB_prime)
      (h_balance : InteractionList.is_balanced ([((1 : FBB), ldata)] ++ (rising_bus μ bus_data lt_proofs) ++ [((-1 : FBB), rdata)]))
    :
      μ ldata < μ rdata ∧
      μ ldata = List.minimum_of_length_pos (l := List.map μ (recv_data bus_data)) (by simp [recv_data]; omega)
        ∧
      μ rdata = List.maximum_of_length_pos (l := List.map μ (send_data bus_data)) (by simp [send_data]; omega)
    := by
      have bus_not_balanced := rising_bus_nonempty_not_balanced bus_data lt_proofs h_not_empty (by simp_all; omega)
      have ⟨ h_data_neq, h_decomposition ⟩ := single_balancer_decomposition (rising_bus_unitary μ bus_data lt_proofs) h_len_bus h_balance
      have min_rel := recv_min_lt_sends μ bus_data lt_proofs h_not_empty
      have max_rel := send_max_gt_recvs μ bus_data lt_proofs h_not_empty
      simp_all
      obtain ⟨ bus', h_perm, h_balance' ⟩ := h_decomposition
      obtain ⟨ dr_min, in_dr_min, eq_dr_min, min_dr_min ⟩ := minimum_witness μ (recv_data bus_data) (by simp [recv_data]; omega)
      obtain ⟨ ds_max, in_ds_max, eq_ds_max, max_ds_max ⟩ := maximum_witness μ (send_data bus_data) (by simp [send_data]; omega)
      have min_recv_mem := @List.minimum_of_length_pos_le_of_mem (l := List.map μ (recv_data bus_data))
      have max_recv_mem := @List.le_maximum_of_length_pos_of_mem (l := List.map μ (recv_data bus_data))
      have min_send_mem := @List.minimum_of_length_pos_le_of_mem (l := List.map μ (send_data bus_data))
      have max_send_mem := @List.le_maximum_of_length_pos_of_mem (l := List.map μ (send_data bus_data))
      set r_min := List.minimum_of_length_pos (l := List.map μ (recv_data bus_data)) (by simp [recv_data]; omega)
      set r_max := List.maximum_of_length_pos (l := List.map μ (recv_data bus_data)) (by simp [recv_data]; omega)
      set s_min := List.minimum_of_length_pos (l := List.map μ (send_data bus_data)) (by simp [send_data]; omega)
      set s_max := List.maximum_of_length_pos (l := List.map μ (send_data bus_data)) (by simp [send_data]; omega)
      suffices : μ ldata = r_min ∧ μ rdata = s_max
      . simp_all; grind
      . simp_all
        have h_unitary : unitary ((1, ldata) :: (rising_bus μ bus_data lt_proofs ++ [(-1, rdata)]))
        := by
          have := rising_bus_unitary μ bus_data lt_proofs
          grind [unitary]
        have h_pos_in : (1, dr_min) ∈ (1, ldata) :: (rising_bus μ bus_data lt_proofs ++ [(-1, rdata)])
        := by
          obtain ⟨ ds', h_in ⟩ := recv_data_in_bus_data in_dr_min
          (have ⟨ dr_min_in, hb ⟩ := bus_data_in_rising_bus μ lt_proofs h_in); clear hb
          have dr_min_in' : (-1, dr_min) ∈ (1, ldata) :: (rising_bus μ bus_data lt_proofs ++ [(-1, rdata)]) := by grind
          obtain ⟨ bus'', h_perm'' ⟩ := unitary_extract_balancer h_unitary h_balance (by simp; exact h_len_bus) dr_min_in'
          simp [balanced_pair] at h_perm''
          grind
        have h_pos_not_in : ¬ (1, dr_min) ∈ rising_bus μ bus_data lt_proofs
        := by
          intro h_pos_in'
          have := pos_ones_in_send_data μ lt_proofs h_pos_in'
          grind
        have h_neg_in : (-1, ds_max) ∈ (1, ldata) :: (rising_bus μ bus_data lt_proofs ++ [(-1, rdata)])
        := by
          obtain ⟨ dr', h_in ⟩ := send_data_in_bus_data in_ds_max
          (have ⟨ hb, ds_max_in ⟩ := bus_data_in_rising_bus μ lt_proofs h_in); clear hb
          have ds_max_in' : (1, ds_max) ∈ (1, ldata) :: (rising_bus μ bus_data lt_proofs ++ [(-1, rdata)]) := by grind
          obtain ⟨ bus'', h_perm'' ⟩ := unitary_extract_balancer h_unitary h_balance (by simp; exact h_len_bus) ds_max_in'
          simp [balanced_pair] at h_perm''
          grind
        have h_neg_not_in : ¬ (-1, ds_max) ∈ rising_bus μ bus_data lt_proofs
        := by
          intro h_neg_in'
          have := neg_ones_in_recv_data μ lt_proofs h_neg_in'
          grind
        simp_all

    /-- If the sorted send and receive data of a rising bus
        match up except for the minimal receive and the maximal send,
        then the actual rising pairs match up monotonically -/
    lemma rising_bus_with_matching_sorted_data_is_monotonic
      (xs : List (List FBB))
      (d_min d_max : List FBB)
      (μ : List FBB → ℕ)
      (sorted_xs : List.Sorted (fun x₁ x₂ ↦ decide (μ x₁ ≤ μ x₂)) xs)
      (bus_data : List (List FBB × List FBB))
      (lt_proofs : ∀ entry ∈ bus_data, μ entry.1 < μ entry.2)
      (data_min : ∀ x ∈ xs, μ d_min < μ x)
      (data_max : ∀ x ∈ xs, μ x ≤ μ d_max)
      (h_recvs : (recv_data bus_data).Perm (d_min :: xs))
      (h_sends : (send_data bus_data).Perm (xs ++ [d_max]))
    :
      bus_data.Perm (List.zip (d_min :: xs) (xs ++ [d_max]))
    := by
      revert bus_data μ d_max d_min
      refine List.strongInductionOn xs (fun xs ih => ?_)
      intro d_min d_max μ sorted_xs bus_data lt_proofs
            data_min data_max h_recvs h_sends
      by_cases xs_not_empty : xs = []
      . simp_all [recv_data, send_data]
        grind
      . set recvs := d_min :: xs
        set sends := xs ++ [ d_max ]
        -- Get `x_max`, the last element of `xs`, which has to exist given `xs` is non-empty
        obtain ⟨ xs', x_max, xs_split ⟩ : ∃ xs' x_max , xs = xs' ++ [x_max]
          := by exists xs.reverse.tail.reverse, xs.reverse.head (by grind); grind
        subst xs; clear xs_not_empty
        -- `x_max` is in the receives
        have x_max_in_recvs : x_max ∈ recv_data bus_data := by grind
        -- This means there is a corresponding `y` in the sends
        -- that is strictly larger than `x_max`
        have ⟨ y, x_max_y_in_bus ⟩ := recv_data_in_bus_data x_max_in_recvs
        have y_in_sends : y ∈ sends := by grind [bus_data_in_recv_send_lists]
        have x_max_lt_y : μ x_max < μ y := lt_proofs _ x_max_y_in_bus
        -- This means that `y` has to equal `d_max`
        have : y = d_max := by
          subst sends; clear *- sorted_xs data_max y_in_sends x_max_lt_y
          simp_all
          rcases y_in_sends with y_in_xs' | y_is_xmax | y_is_dmax
          . unfold List.Sorted at sorted_xs
            simp_all [List.pairwise_append]
            grind
          . grind
          . assumption
        subst y
        -- Split `bus_data` into the max pair and the rest
        have ⟨ bus_data', bus_data_split ⟩ : ∃ bus_data', bus_data.Perm (bus_data' ++ [(x_max, d_max)])
        := by
          have ⟨ bus_data', bus_data_split ⟩ := @List.Sublist.exists_perm_append _ [(x_max, d_max)] bus_data (by grind)
          exists bus_data'; grind
        -- Reorganise goal
        subst recvs sends
        rw [← List.cons_append, List.zip_append]
        trans (bus_data' ++ [(x_max, d_max)]) <;> [ assumption; skip ]
        simp [List.perm_append_right_iff]
        unfold List.Sorted at *
        -- Fire the IH
        apply ih xs' (by simp) (μ := μ) <;> (try grind) <;> clear ih
        . simp_all; grind
        . rw [← List.cons_append] at h_recvs
          have := recv_data_perm_append_split _ _ _ _ bus_data_split h_recvs
          grind
        . have := send_data_perm_append_split _ _ _ _ bus_data_split h_sends
          grind
        . simp

    /-- If the sorted send and receive data of a rising bus
        match up except for the minimal receive and the maximal send,
        then there associated measure is strictly increasing  -/
    lemma rising_bus_with_matching_sorted_data_has_no_duplicates
      (xs : List (List FBB))
      (d_min d_max : List FBB)
      (μ : List FBB → ℕ)
      (sorted_xs : List.Sorted (fun x₁ x₂ ↦ decide (μ x₁ ≤ μ x₂)) xs)
      (bus_data : List (List FBB × List FBB))
      (lt_proofs : ∀ entry ∈ bus_data, μ entry.1 < μ entry.2)
      (data_min : ∀ x ∈ xs, μ d_min < μ x)
      (data_max : ∀ x ∈ xs, μ x ≤ μ d_max)
      (h_recvs : (recv_data bus_data).Perm (d_min :: xs))
      (h_sends : (send_data bus_data).Perm (xs ++ [d_max]))
    :
      List.Sorted (fun x₁ x₂ ↦ μ x₁ < μ x₂) (d_min :: xs ++ [d_max])
    := by
      have bus_data_perm_ordered :=
        rising_bus_with_matching_sorted_data_is_monotonic
          xs d_min d_max μ sorted_xs bus_data lt_proofs
          data_min data_max h_recvs h_sends
      unfold List.Sorted at *
      rw [List.pairwise_append, List.pairwise_cons]
      rcases xs with _ | ⟨ hd, tl ⟩
      . simp_all
      . split_ands
        . grind
        . have : IsTrans (List FBB) fun x₁ x₂ ↦ μ x₁ < μ x₂
            := by grind [IsTrans.mk]
          rw [← List.chain_iff_pairwise, List.chain_iff_get]
          . split_ands
            . intro h
              apply lt_proofs (hd, tl.get ⟨ 0, by omega⟩)
              rw [List.Perm.mem_iff bus_data_perm_ordered]
              rcases tl <;> simp_all
              grind
            . intro i hlen
              apply lt_proofs (tl.get ⟨ i, by omega⟩, tl.get ⟨ i + 1, by omega⟩)
              rw [List.Perm.mem_iff bus_data_perm_ordered]
              simp; right
              suffices : tl[i] = (hd :: tl)[i+1]'(by simp; omega) ∧ tl[i+1] = (tl ++ [d_max])[i+1]'(by simp; omega)
              . obtain ⟨ eq_i, eq_i_plus_one ⟩ := this
                rw [eq_i, eq_i_plus_one]
                suffices : ((hd :: tl)[i + 1]'(by simp; omega), (tl ++ [d_max])[i + 1]'(by simp; omega))
                             =
                           ((hd :: tl).zip (tl ++ [d_max]))[i+1]'(by simp; omega)
                . grind
                . grind
              . simp_all; grind
        . grind
        . simp_all
          by_cases tl_not_empty : tl = []
          . simp_all; grind
          . obtain ⟨ tl', tl_max, tl_split ⟩ : ∃ tl' tl_max , tl = tl' ++ [tl_max]
            := by exists tl.reverse.tail.reverse, tl.reverse.head (by grind)
                  simp_all [List.dropLast_append_getLast]
            subst tl; clear tl_not_empty
            suffices : μ tl_max < μ d_max
            . simp_all; grind
            . apply lt_proofs tl_max d_max
              rw [← List.cons_append, List.zip_append (by simp)] at bus_data_perm_ordered
              simp_all; grind

    /-- If a non-empty rising bus is balanced with single balancers,
        then the measure of the associated data is strictly increasing,
        and the receive-send pairs are such that there is no entry
        whose measure is between that of the receive and of the send. -/
    lemma rising_bus_with_single_balancer_characterisation
      {ldata rdata : List FBB}
      (bus_data : List (List FBB × List FBB))
      (lt_proofs : ∀ entry ∈ bus_data, μ entry.1 < μ entry.2)
      (h_not_empty : 0 < bus_data.length)
      (h_len_bus : ([(1, ldata)] ++ (rising_bus μ bus_data lt_proofs) ++ [(-1, rdata)]).length < BB_prime)
      (h_balance : InteractionList.is_balanced ([((1 : FBB), ldata)] ++ (rising_bus μ bus_data lt_proofs) ++ [((-1 : FBB), rdata)]))
    :
      ∃ xs, bus_data.Perm (List.zip (ldata :: xs) (xs ++ [rdata])) ∧
            List.Sorted (fun x₁ x₂ ↦ μ x₁ < μ x₂) (ldata :: xs ++ [rdata])
    := by
      have bus_not_balanced := rising_bus_nonempty_not_balanced bus_data lt_proofs h_not_empty (by simp_all; omega)
      have ⟨ h_data_neq, h_decomposition ⟩ := single_balancer_decomposition (rising_bus_unitary μ bus_data lt_proofs) h_len_bus h_balance
      have min_rel := recv_min_lt_sends μ bus_data lt_proofs h_not_empty
      have max_rel := send_max_gt_recvs μ bus_data lt_proofs h_not_empty
      simp_all +arith only [Fin.isValue, List.length_cons, List.length_append, List.length_nil,
                            zero_add, imp_false, not_false_eq_true, forall_const]
      obtain ⟨ bus', h_perm, h_balance' ⟩ := h_decomposition
      have ⟨ ldata_lt_rdata, ldata_is_min, rdata_is_max ⟩ :=
        @single_boundary_balancers_of_rising_bus_are_min_and_max
          μ ldata rdata bus_data lt_proofs h_not_empty (by simp_all; omega) h_balance
      have min_recv_mem := @List.minimum_of_length_pos_le_of_mem (l := List.map μ (recv_data bus_data))
      have max_recv_mem := @List.le_maximum_of_length_pos_of_mem (l := List.map μ (recv_data bus_data))
      have min_send_mem := @List.minimum_of_length_pos_le_of_mem (l := List.map μ (send_data bus_data))
      have max_send_mem := @List.le_maximum_of_length_pos_of_mem (l := List.map μ (send_data bus_data))
      set r_min := List.minimum_of_length_pos (l := List.map μ (recv_data bus_data)) (by simp [recv_data]; omega)
      set r_max := List.maximum_of_length_pos (l := List.map μ (recv_data bus_data)) (by simp [recv_data]; omega)
      set s_min := List.minimum_of_length_pos (l := List.map μ (send_data bus_data)) (by simp [send_data]; omega)
      set s_max := List.maximum_of_length_pos (l := List.map μ (send_data bus_data)) (by simp [send_data]; omega)
      have h_recv_data := recv_data_from_rising_bus μ lt_proofs
      have h_send_data := send_data_from_rising_bus μ lt_proofs

      set recv_extractor := List.filterMap (fun (x : FBB × List FBB) ↦ if x.1 = -1 then some x.2 else none)
      set send_extractor := List.filterMap (fun (x : FBB × List FBB) ↦ if x.1 =  1 then some x.2 else none)

      have h_recv_data_eq : (recv_data bus_data).Perm (recv_extractor ([(-1, ldata)] ++ bus' ++ [(1, rdata)]))
      := by
        trans; assumption
        apply List.Perm.filterMap; assumption

      have h_send_data_eq : (send_data bus_data).Perm (send_extractor ([(-1, ldata)] ++ bus' ++ [(1, rdata)]))
      := by
        trans; assumption
        apply List.Perm.filterMap; assumption

      simp [recv_extractor] at h_recv_data_eq
      simp [send_extractor] at h_send_data_eq

      have h_unitary' : unitary bus'
      := by
        have := rising_bus_unitary μ bus_data lt_proofs
        grind [unitary, unitary_inv_perm]
      have h_length' : bus'.length < BB_prime := by have := List.Perm.length_eq h_perm; grind
      have := @unitary_balanced_recvs_perm_sends bus' h_unitary' h_balance' h_length'
      simp_all [-List.sorted_cons, -List.cons_append]
      let xs := List.mergeSort (List.filterMap (fun x ↦ if x.1 = 1 then some x.2 else none) bus') (fun x₁ x₂ ↦ μ x₁ ≤ μ x₂)

      have all_xs_in_send : ∀ x, x ∈ xs → x ∈ send_data bus_data := by grind [List.mem_mergeSort]

      have sorted_xs : List.Sorted (fun x₁ x₂ ↦ decide (μ x₁ ≤ μ x₂)) xs
      := by
        subst xs
        unfold List.Sorted
        set l := List.filterMap (fun x ↦ if x.1 = 1 then some x.2 else none) bus'
        apply List.sorted_mergeSort <;> grind

      have data_min : ∀ x ∈ xs, μ ldata < μ x := by grind
      have data_max : ∀ x ∈ xs, μ x ≤ μ rdata := by grind

      have h_recvs : (recv_data bus_data).Perm (ldata :: xs)
      := by
        trans (ldata :: List.filterMap (fun x ↦ if x.1 = -1 then some x.2 else none) bus')
        . assumption
        . simp
          trans ((List.filterMap (fun x ↦ if x.1 = 1 then some x.2 else none) bus'))
          . grind
          . rw [List.perm_comm]
            apply List.mergeSort_perm

      have h_sends : (send_data bus_data).Perm (xs ++ [rdata])
      := by
        trans
        . exact h_send_data_eq
        . rw [List.perm_append_right_iff]
          rw [List.perm_comm]
          apply List.mergeSort_perm

      exists xs
      split_ands
      . apply rising_bus_with_matching_sorted_data_is_monotonic <;> assumption
      . apply rising_bus_with_matching_sorted_data_has_no_duplicates <;> try assumption

  end bus_balancing

  section consistency

    /-- A well formed chip with respect to a measure μ provides:
      - the entries on the execution bus, in -1, 1 order
      - the entries on the memory bus, in -1, 1 order
      - the proof that the execution bus consists of a single entry
      - a proof that the execution bus entries are rising
      - a proof that the memory bus entries are rising -/
    class WFConstraints (α : Type) (μ : List FBB → ℕ) where
      execution_bus_entries : List (List FBB × List FBB)
      memory_bus_entries : List (List FBB × List FBB)
      single_pair_on_execution_bus : execution_bus_entries.length = 1
      rising_pairs_on_execution_bus : List.Forall (fun (recv, send) ↦ μ recv < μ send) execution_bus_entries
      rising_pairs_on_memory_bus : List.Forall (fun (recv, send) ↦ μ recv < μ send) memory_bus_entries
      execution_envelops_memory :
        List.Forall
          (fun (_, send) ↦ μ execution_bus_entries[0].1 ≤ μ send ∧
                           μ send < μ execution_bus_entries[0].2
          ) memory_bus_entries

    /-- A general well-formed chip -/
    structure WFChip (μ : List FBB → ℕ) where
      ChipType : Type
      chip : ChipType
      [inst_wf : WFConstraints ChipType μ]

    instance {μ : List FBB → ℕ} (c : WFChip μ) : WFConstraints c.ChipType μ := c.inst_wf

    /-- The execution bus of a well-formed chip:
      - `chips` denotes a collection of chips that can be called
      - `next` is a function that selects what chip is next based on what is sent to the execution bus
      - `n` is the length of the bus
      - `i` is the chip to be run for this iteration -/
    def execution_bus (chips : List (WFChip μ)) (next : List FBB → Fin (chips.length)) (n : Fin 2013265919) (i : Fin (chips.length))
    :
      List (List FBB × List FBB)
    :=
      let execution_entry := ((chips[i]).inst_wf.execution_bus_entries)[0]'(by have := chips[i].inst_wf.single_pair_on_execution_bus; grind)
      if n = 0
        then []
        else execution_entry :: (execution_bus chips next (n - 1) (next execution_entry.1))

    /-- The execution bus is a rising bus -/
    lemma execution_bus_is_rising_bus
      (chips : List (WFChip μ))
      (next : List FBB → Fin (chips.length))
      (n : Fin 2013265919)
      (i : Fin (chips.length))
    :
      ∀ entry ∈ (execution_bus chips next n i), μ entry.1 < μ entry.2
    := by
      cases n
      case mk n lt =>
        induction n generalizing i
        case zero => simp_all [execution_bus]
        case succ n ih =>
          . intro entry h_in
            unfold execution_bus at h_in
            rw [if_neg (by simp [Fin.ext_iff])] at h_in
            simp at h_in
            rcases h_in with main | with_ih
            . have is_rising_pair := @WFConstraints.rising_pairs_on_execution_bus chips[i.val].ChipType μ (by exact chips[i.val].inst_wf)
              rw [List.forall_iff_forall_mem] at is_rising_pair
              grind
            . have : (⟨ n + 1, lt ⟩ : Fin 2013265919) - 1 = ⟨ n, by omega ⟩
                := by simp [Fin.ext_iff, Fin.sub_def]; omega
              rw [this] at with_ih
              grind

  end consistency



end InteractionList
