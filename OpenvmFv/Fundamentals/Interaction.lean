import OpenvmFv.Fundamentals.BabyBear

import LeanZKCircuit.Interactions

set_option maxHeartbeats 1_000_000_000

attribute [local simp]
  List.filter_cons

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

  /-- Buses with reversed data -/
  def reverse
    (bus : List (F × List F))
  : List (F × List F) :=
    List.map (fun (a, b) ↦ (a, b.reverse )) bus

  /-- Invariance of `is_balanced` under permutation -/
  lemma is_balanced_inv_reverse
    [BEq F]
    [LawfulBEq F]
    [Field F]
    {bus : List (F × List F)}
  :
    is_balanced bus ↔ is_balanced (reverse bus)
  := by
    simp [is_balanced, get_multiplicity, reverse] at *
    constructor
    all_goals
      intro hyp data
      specialize hyp data.reverse
      rw [← hyp]; clear hyp
      induction bus
      case nil => simp
      case cons hd tl ih =>
        obtain ⟨ m, d ⟩ := hd; simp
        split_ifs with h h' <;> simp_all
        try simp [← h, List.reverse_reverse] at h'

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
            simp_all
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

  section timestamps

    /-- Timestamped pairs -/
    def timestamped_pair
      (ts te : FBB) (pcs pce : List FBB)
      (_ : ts < te)
    : List (FBB × List FBB) :=
      [
        (-1, ts :: pcs),
        ( 1, te :: pce)
      ]

    /-- Start timestamps -/
    def start_timestamps
      (bus_data : List (FBB × FBB × List FBB × List FBB))
    : List FBB :=
      List.map (fun x ↦ x.1) bus_data

    /-- End timestamps -/
    def end_timestamps
      (bus_data : List (FBB × FBB × List FBB × List FBB))
    : List FBB :=
      List.map (fun x ↦ x.2.1) bus_data

    /-- A bus consisting of timestamped pairs -/
    def timestamped_pair_bus
      (bus_data : List (FBB × FBB × List FBB × List FBB))
      (lt_proofs : ∀ entry ∈ bus_data, entry.1 < entry.2.1)
    : List (FBB × List FBB) :=
      List.flatten
        (List.map
          (fun (x : { y // y ∈ bus_data }) ↦
            let ⟨ ⟨ ts, te, pcs, pce ⟩ , pf ⟩ := x
            timestamped_pair ts te pcs pce (lt_proofs (ts, te, pcs, pce) pf)) bus_data.attach)

    def sorted_timestamped_data
      (bus_data : List (FBB × FBB × List FBB × List FBB))
    : List (FBB × FBB × List FBB × List FBB) :=
      List.mergeSort bus_data (fun a b ↦ a.1 ≤ b.1)

    instance : IsTotal (Fin 2013265921 × Fin 2013265921 × List (Fin 2013265921) × List (Fin 2013265921)) fun a b ↦ a.1 ≤ b.1
    := by
      apply IsTotal.mk
      omega

    instance : IsTrans (Fin 2013265921 × Fin 2013265921 × List (Fin 2013265921) × List (Fin 2013265921)) fun a b ↦ a.1 ≤ b.1
    := by
      apply IsTrans.mk
      intro a b c hab hbc
      trans b.1 <;> assumption

    lemma sorted_timestamped_data_is_sorted
      (bus_data : List (FBB × FBB × List FBB × List FBB))
    :
      List.Sorted (fun a b ↦ a.1 ≤ b.1) (sorted_timestamped_data bus_data)
    := by
      apply List.sorted_mergeSort'

    @[grind]
    lemma sorted_timestamp_data_is_perm
      (bus_data : List (FBB × FBB × List FBB × List FBB))
    :
      bus_data.Perm (sorted_timestamped_data bus_data)
    := by
      unfold sorted_timestamped_data
      rw [List.perm_comm]
      apply List.mergeSort_perm

    def lt_proofs_of_sorted
      (bus_data : List (FBB × FBB × List FBB × List FBB))
      (lt_proofs : ∀ entry ∈ bus_data, entry.1 < entry.2.1)
    :
      ∀ entry ∈ sorted_timestamped_data bus_data, entry.1 < entry.2.1
    := by grind

    lemma sorted_timestamp_bus_is_perm
      (bus_data : List (FBB × FBB × List FBB × List FBB))
      (lt_proofs : ∀ entry ∈ bus_data, entry.1 < entry.2.1)
    :
      List.Perm
        (timestamped_pair_bus bus_data lt_proofs)
        (timestamped_pair_bus (sorted_timestamped_data bus_data) (lt_proofs_of_sorted bus_data lt_proofs))
    := by
      have sorted_data_is_perm := sorted_timestamp_data_is_perm bus_data
      unfold timestamped_pair_bus
      apply List.Perm.flatten
      iterate 2 rw [List.map_subtype
                     (g := (fun (ts, te, pcs, pce) ↦ [ (-1, ts :: pcs), ( 1, te :: pce) ]))
                     (by simp [timestamped_pair])]
      . simp
        rw [List.map_perm_map_iff (by unfold Function.Injective; grind)]
        assumption



    /- Pathway:
       - if a list of BTPs is balanced by adding boundary conditions, then"
         - starting timestamps are unique
         -  1-balancer balances the minimum
         - -1-balancer balances the maximum
         - everything is one big timestamp-ordered sequence
       -/

    lemma oh_lord
      (bus_data : List (FBB × FBB × List FBB × List FBB))
      (lt_proofs : ∀ entry ∈ bus_data, entry.1 < entry.2.1)
      (lbal_data rbal_data : List FBB)
      (h_balance : InteractionList.is_balanced ([((1 : FBB), lbal_data)] ++ (timestamped_pair_bus bus_data lt_proofs) ++ [((-1 : FBB), rbal_data)]))
    :
      List.Nodup (start_timestamps bus_data lt_proofs)
    := by sorry


  end timestamps

end InteractionList
