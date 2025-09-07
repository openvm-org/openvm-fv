import OpenvmFv.Fundamentals.BabyBear

import LeanZKCircuit.Interactions

set_option maxHeartbeats 1_000_000_000

attribute [local grind]
  Fin.add_def
  Fin.neg_def
  Fin.val_natCast

namespace Interaction

  section buses

  /-- ExecutionBus entry -/
  @[simp]
  def executionBus_entry
    (mul pc timestamp : F)
  : (F × List F) :=
    (mul, [ pc, timestamp ])

  /-- Assumptions from execution bus entries -/
  def executionBus_assumptions
    (mul _ timestamp : FBB)
  : Prop :=
    ¬ mul = 0 →
      -- appropriate ranges
      timestamp < 2 ^ 29

  /-- MemoryBus entry -/
  @[simp]
  def memoryBus_entry
    (mul as ptr x0 x1 x2 x3 timestamp : FBB)
  : (FBB × List FBB) :=
    (mul, [as, ptr, x0, x1, x2, x3, timestamp])

  /-- Assumptions from memory bus entries -/
  def memoryBus_assumptions
    (mul as ptr x0 x1 x2 x3 _ : FBB)
  : Prop :=
    ¬ mul = 0 →
      -- appropriate ranges
      as.val < 3 ∧
      ptr.val < 2 ^ 29 ∧
      x0.val < 256 ∧
      x1.val < 256 ∧
      x2.val < 256 ∧
      x3.val < 256

  /-- RangeBus entry -/
  @[simp]
  def rangeCheckerBus_entry
    (mul val deg : FBB)
  : (FBB × List FBB) :=
    (mul, [ val, deg ])

  /-- Assumptions from range-checker bus entries -/
  def rangeCheckerBus_assumptions
    (mul val deg : FBB)
  : Prop :=
    ¬ mul = 0 →
      -- `deg` range
      deg.val < 32 ∧
      -- `val` range
      val.val < 2 ^ deg.val

  /-- ReadInstructionBus entry, with parameter
      naming as per OpenVM documentation -/
  @[simp]
  def readInstructionBus_entry
    (mul pc opcode xa xb xc xd xe xf xg : FBB)
  : (FBB × List FBB) :=
    (mul, [ pc, opcode, xa, xb, xc, xd, xe, xf, xg ])

  /-- ReadInstructionBus entry -/
  def readInstructionBus_assumptions
    (mul _ _ _ _ _ _ _ _ _ : FBB)
  : Prop :=
    ¬ mul = 0 →
      True


  /-- BitwiseBus entry -/
  @[simp]
  def bitwiseBus_entry
    (mul a b c is_xor : FBB)
  : (FBB × List FBB) :=
    (mul, [ a, b, c, is_xor ])

  /-- Assumptions from bitwise bus entries -/
  def bitwiseBus_assumptions
    (mul a b c is_xor : FBB)
  : Prop :=
    ¬ mul = 0 →
      -- operand range
      a.val < 256 ∧ b.val < 256 ∧
      -- xor indicator range
      (is_xor = 0 ∨ is_xor = 1) ∧
      -- xor or nothing
      c.val = if is_xor = 0 then 0 else a.val ^^^ b.val

  end buses

end Interaction

namespace List

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

end List

namespace InteractionList

  open InteractionList

    /-- Balanced execution-bus pair -/
    @[simp]
    def balanced_pair
      [Field F]
      (m : F)
      (data : List F)
    : List (F × List F) :=
      [
        (m, data),
        (-m, data),
      ]

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

  /-- Prop variant of `non_zero` -/
  def is_non_zero
    [BEq F]
    [Field F]
    (bus : List (F × List F))
  : Prop :=
    ∀ entry ∈ bus, ¬ entry.1 = 0

  /-- Relationship between `non_zero` and `is_non_zero` -/
  lemma is_non_zero_as_non_zero
    [BEq F]
    [LawfulBEq F]
    [Field F]
    (bus : List (F × List F))
  :
    is_non_zero bus ↔ bus = non_zero bus
  := by
    induction bus <;> simp [is_non_zero, non_zero] at *
    case cons hd tl ih =>
      obtain ⟨ m, d ⟩ := hd
      by_cases hm : m = 0 <;> simp_all
      . intro hyp
        have := List.length_filter_le (fun x ↦ !x.1 == 0) tl
        grind

  /-- Buses with only -1, 0, 1 multiplicities -/
  def mult_max_one
    [Field F]
    (bus : List (F × List F))
  : Prop :=
    forall entry, entry ∈ bus → entry.1 = -1 ∨ entry.1 = 0 ∨ entry.1 = 1

  /-- Invariance of only -1, 0, 1 under permutation -/
  lemma mult_max_one_inv_perm
    [Field F]
    {bus bus' : List (F × List F)}
    (h_perm : bus.Perm bus')
  :
    mult_max_one bus ↔ mult_max_one bus'
  := by
    unfold mult_max_one
    grind

  /-- Invariance of only -1, 0, 1 under non-zero filtering -/
  lemma mult_max_one_inv_non_zero
    [BEq F]
    [LawfulBEq F]
    [Field F]
    (bus : List (F × List F))
  :
    mult_max_one bus ↔ mult_max_one (non_zero bus)
  := by
    simp [mult_max_one, non_zero]
    grind

  /-- Only zero equals its negation in BabyBear -/
  @[simp]
  lemma eq_neg_eq_zero (m : FBB) : -m = m ↔ m = 0 := by grind

  /-- Extraction of a balanced pair from a balanced -1/0/1 bus -/
  lemma mult_max_one_extract
    (bus : List (FBB × List FBB))
    (h_balance : is_balanced bus)
    (h_mult_max_one : mult_max_one bus)
    (h_len_bus : bus.length < BB_prime)
    (data : List FBB)
    (h_in_neg : (m, data) ∈ bus)
    (h_m_neq_zero : ¬m = 0)
  :
    ∃ bus', List.Perm bus (balanced_pair m data ++ bus')
  := by
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
      rw [mult_max_one_inv_perm h_eq] at h_mult_max_one
      simp [mult_max_one] at h_mult_max_one
      obtain ⟨ split_m, split_bus'' ⟩ := h_mult_max_one
      simp_all
      clear h_len_bus h_eq bus h_m_neq_zero
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
            simp_all [List.filter_cons]
            specialize ih (by omega) (by grind)
            specialize split_bus'' m' data'; simp at split_bus''
            by_cases h_tl_len : tl.length = 0
            . split_ifs with h_data <;> simp_all
              grind
            . rcases ih with ihl | ihr
              . left; split_ifs <;>
                (try simp_all [-List.length_eq_zero_iff]) <;>
                grind
              . split_ifs <;> simp_all [-List.length_eq_zero_iff]; grind
      . suffices : ((List.map Prod.fst (List.filter (fun x ↦ x.2 == data) bus'')).sum).val ≤ bus''.length ∨
                   ((List.map Prod.fst (List.filter (fun x ↦ x.2 == data) bus'')).sum).val = 0
        . grind
        . clear h_balance
          induction bus'' <;> grind

  section executionBus

    /-- Pairs emitted by the execution bus -/
    def executionBus_entry_pair
      (pcs pce ts te : FBB)
      (_ : ts < te)
    : List (FBB × List FBB):=
      [
        Interaction.executionBus_entry (-1) pcs ts,
        Interaction.executionBus_entry 1 pce te
      ]

    /-- List of execution-bus pairs -/
    def executionBus_entry_pair_list
      (bus : List (FBB × List FBB))
    : Prop :=
      match bus with
      | [] => True
      | (-1, [_, ts]) :: (1, [_, te]) :: bus =>
          ts < te ∧
          executionBus_entry_pair_list bus
      | _ => False

    /-- Timestamps of execution-bus pairs -/
    def executionBus_entry_pair_list_timestamps
      (bus : List (FBB × List FBB))
      (h_ep : executionBus_entry_pair_list bus)
    : List FBB := by
      unfold executionBus_entry_pair_list at h_ep
      split at h_ep
      case h_1 => exact []
      case h_2 bus _ ts _ _ bus' =>
        exact ts :: executionBus_entry_pair_list_timestamps bus' h_ep.2
      nomatch h_ep

  end executionBus

end InteractionList
