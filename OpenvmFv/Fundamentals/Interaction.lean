import OpenvmFv.Fundamentals.BabyBear

import LeanZKCircuit.Interactions

set_option maxHeartbeats 1_000_000_000

attribute [local simp]
  List.filter_cons

attribute [-simp]
  Fin.val_fin_le
  exists_and_left
  exists_and_right

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

end List

namespace BabyBear

  /-- Only zero equals its negation in BabyBear -/
  @[simp]
  lemma eq_neg_eq_zero (m : FBB) : -m = m ↔ m = 0 := by grind

end BabyBear

namespace InteractionList

  open InteractionList

    /-- Balanced arbitrary-multiplicity bus entry pair -/
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

  /-- Invariance of `is_balanced` under bijective mapping.
      Intended to be used with list reverse. -/
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

  /-- Buses with only -1, 0, 1 multiplicities -/
  def mult_n1_0_p1
    [Field F]
    (bus : List (F × List F))
  : Prop :=
    forall entry, entry ∈ bus → entry.1 = -1 ∨ entry.1 = 0 ∨ entry.1 = 1

  /-- Buses with only -1, 1 multiplicities -/
  def mult_n1_p1
    [Field F]
    (bus : List (F × List F))
  : Prop :=
    forall entry, entry ∈ bus → entry.1 = -1 ∨ entry.1 = 1

  /-- -1, 0, 1 under non-zero filtering becomes -1, 1 -/
  lemma mult_n1_0_p1_non_zero_is_n1_p1
    [BEq F]
    [LawfulBEq F]
    [Field F]
    (bus : List (F × List F))
  :
    mult_n1_0_p1 bus → mult_n1_p1 (non_zero bus)
  := by
    simp [mult_n1_0_p1, mult_n1_p1, non_zero]
    grind

  /-- Invariance of only -1, 1 under permutation -/
  lemma mult_n1_p1_inv_perm
    [Field F]
    {bus bus' : List (F × List F)}
    (h_perm : bus.Perm bus')
  :
    mult_n1_p1 bus ↔ mult_n1_p1 bus'
  := by
    unfold mult_n1_p1
    grind

  /-- Compatibility of only -1, 1 under concatenation -/
  lemma mult_n1_p1_append_iff
    [Field F]
    {bus bus' : List (F × List F)}
  :
    mult_n1_p1 (bus ++ bus') ↔ mult_n1_p1 bus ∧ mult_n1_p1 bus'
  := by
    unfold mult_n1_p1
    simp; grind

  /-- If a -1, 1 bus is balanced and does not exceed `BB_prime` in length,
      and if we know an entry is on the bus, then we also know that
      its individual balancer is on the bus. -/
  lemma mult_n1_p1_extract
    {bus : List (FBB × List FBB)}
    (h_mult_n1_p1 : mult_n1_p1 bus)
    (h_balance : is_balanced bus)
    (h_len_bus : bus.length < BB_prime)
    (data : List FBB)
    (h_in_neg : (m, data) ∈ bus)
  :
    ∃ bus', List.Perm bus (balanced_pair m data ++ bus')
  := by
    have m_neq_z : ¬ m = 0 := by apply h_mult_n1_p1 at h_in_neg; grind
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
      rw [mult_n1_p1_inv_perm h_eq] at h_mult_n1_p1
      simp [mult_n1_p1] at h_mult_n1_p1
      obtain ⟨ split_m, split_bus'' ⟩ := h_mult_n1_p1
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

  /- The idea is to now consider -1, 1 pairs whose
     send data (the leading component of the `1`-entry) is
     larger than their receive data (the leading comonent of
     the `-1` entry). Because those will be used in this work
     to represent timestamp-leading data, we refer to them
     as `timestamp_pair`s.
  -/
  section timestamp_pairs

    /-- Timestamped pairs -/
    def timestamp_pair
      (ts te : FBB) (pcs pce : List FBB)
      (_ : ts < te)
    : List (FBB × List FBB) :=
      [
        (-1, ts :: pcs),
        ( 1, te :: pce)
      ]

    /-- Receive timestamps -/
    def recv_timestamps
      (bus_data : List (FBB × FBB × List FBB × List FBB))
    : List FBB :=
      List.map (fun x ↦ x.1) bus_data

    /-- Receive entries -/
    def recv_entries
      (bus_data : List (FBB × FBB × List FBB × List FBB))
    : List (FBB × List FBB) :=
      List.map (fun x ↦ (x.1, x.2.2.1)) bus_data

    /-- Send timestamps -/
    def send_timestamps
      (bus_data : List (FBB × FBB × List FBB × List FBB))
    : List FBB :=
      List.map (fun x ↦ x.2.1) bus_data

    /-- Send entries -/
    def send_entries
      (bus_data : List (FBB × FBB × List FBB × List FBB))
    : List (FBB × List FBB) :=
      List.map (fun x ↦ (x.2.1, x.2.2.2)) bus_data

    /-- All receives are in the data -/
    lemma recv_timestamps_in_bus_data
      {ts : FBB}
      {bus_data : List (FBB × FBB × List FBB × List FBB)}
      (ts_in_recv : ts ∈ recv_timestamps bus_data)
    :
      ∃ (te : FBB) (pcs pce: List FBB), (ts, te, pcs, pce) ∈ bus_data
    := by
      induction bus_data
      case nil => simp_all [recv_timestamps]
      case cons hd tl ih =>
        obtain ⟨ ts', te', pcs', pce' ⟩ := hd
        simp [recv_timestamps] at *
        grind

    /-- All sends are in the data -/
    lemma send_timestamps_in_bus_data
      {te : FBB}
      {bus_data : List (FBB × FBB × List FBB × List FBB)}
      (te_in_send : te ∈ send_timestamps bus_data)
    :
      ∃ (ts : FBB) (pcs pce: List FBB), (ts, te, pcs, pce) ∈ bus_data
    := by
      induction bus_data
      case nil => simp_all [send_timestamps]
      case cons hd tl ih =>
        obtain ⟨ ts', te', pcs', pce' ⟩ := hd
        simp [send_timestamps] at *
        grind

    /-- Timestamps are in appropriate lists -/
    lemma bus_data_in_timestamp_lists
      {ts te : FBB} {pcs pce : List FBB}
      {bus_data : List (FBB × FBB × List FBB × List FBB)}
      (h_in : (ts, te, pcs, pce) ∈ bus_data)
    :
      ts ∈ recv_timestamps bus_data ∧
      te ∈ send_timestamps bus_data
    := by
      induction bus_data
      case nil => simp_all
      case cons hd tl ih =>
        simp_all [recv_timestamps, send_timestamps]
        grind

    /-- A `timestamp_bus` is a bus consisting of timestamp pairs -/
    @[grind]
    def timestamp_bus
      (bus_data : List (FBB × FBB × List FBB × List FBB))
      (lt_proofs : ∀ entry ∈ bus_data, entry.1 < entry.2.1)
    : List (FBB × List FBB) :=
      List.flatten
        (List.map
          (fun (x : { y // y ∈ bus_data }) ↦
            let ⟨ ⟨ ts, te, pcs, pce ⟩ , pf ⟩ := x
            timestamp_pair ts te pcs pce (lt_proofs (ts, te, pcs, pce) pf)) bus_data.attach)

    /-- Receives and sends of timestamp bus data are on the timestamp bus -/
    lemma bus_data_in_timestamp_bus
      {ts te : FBB} {pcs pce : List FBB}
      {bus_data : List (FBB × FBB × List FBB × List FBB)}
      (lt_proofs : ∀ entry ∈ bus_data, entry.1 < entry.2.1)
      (h_in : (ts, te, pcs, pce) ∈ bus_data)
    :
      (-1, ts :: pcs) ∈ timestamp_bus bus_data lt_proofs ∧
      ( 1, te :: pce) ∈ timestamp_bus bus_data lt_proofs
    := by
      induction bus_data
      case nil => simp_all
      case cons hd tl ih =>
        simp_all [timestamp_bus, timestamp_pair]
        grind

    /-- A timestamp bus is a -1, 1, bus -/
    lemma timestamp_bus_mult_n1_p1
      (bus_data : List (FBB × FBB × List FBB × List FBB))
      (lt_proofs : ∀ entry ∈ bus_data, entry.1 < entry.2.1)
    :
      mult_n1_p1 (timestamp_bus bus_data lt_proofs)
    := by
      induction bus_data
      case nil => simp [mult_n1_p1, timestamp_bus]
      case cons hd tl ih =>
        obtain ⟨ ts', te', pcs', pce' ⟩ := hd
        simp_all [mult_n1_p1, timestamp_bus, timestamp_pair]
        exact ih

    /-- All negative entries in a timestamp bus are from the receives -/
    lemma neg_ones_in_recv_timestamps
      (ts : FBB) (pcs : List FBB)
      (bus_data : List (FBB × FBB × List FBB × List FBB))
      (lt_proofs : ∀ entry ∈ bus_data, entry.1 < entry.2.1)
      (h_in : (-1, ts :: pcs) ∈ timestamp_bus bus_data lt_proofs)
    :
      ts ∈ recv_timestamps bus_data
    := by
      induction bus_data
      case nil => grind
      case cons hd tl ihs =>
        obtain ⟨ ts', te', pcs', pce' ⟩ := hd
        simp_all [recv_timestamps, timestamp_bus, timestamp_pair]
        rcases h_in with _ | h_tl <;> [ simp_all; right ]
        obtain ⟨ l, ⟨ ⟨ ts'', te'', pcs'', pce'', h_in'', eq_l ⟩, h_in ⟩ ⟩ := h_tl
        specialize ihs l ts'' te'' pcs'' pce'' h_in'' eq_l
        grind

    /-- All positive entries in a timestamp bus are from the sends -/
    lemma pos_ones_in_send_timestamps
      {ts : FBB} {pcs : List FBB}
      {bus_data : List (FBB × FBB × List FBB × List FBB)}
      (lt_proofs : ∀ entry ∈ bus_data, entry.1 < entry.2.1)
      (h_in : (1, ts :: pcs) ∈ timestamp_bus bus_data lt_proofs)
    :
      ts ∈ send_timestamps bus_data
    := by
      induction bus_data
      case nil => grind
      case cons hd tl ihs =>
        obtain ⟨ ts', te', pcs', pce' ⟩ := hd
        simp_all [send_timestamps, timestamp_bus, timestamp_pair]
        rcases h_in with _ | h_tl <;> [ simp_all; right ]
        obtain ⟨ l, ⟨ ⟨ ts'', te'', pcs'', pce'', h_in'', eq_l ⟩, h_in ⟩ ⟩ := h_tl
        specialize ihs l ts'' te'' pcs'' pce'' h_in'' eq_l
        grind

    /-- The minimal receive timestamp is smaller than all the send timestamps -/
    lemma recv_min_lt_sends
      (bus_data : List (FBB × FBB × List FBB × List FBB))
      (lt_proofs : ∀ entry ∈ bus_data, entry.1 < entry.2.1)
      (h_not_empty : ¬ bus_data = [])
    :
      List.minimum_of_length_pos (l := recv_timestamps bus_data) (by simp [recv_timestamps]; rw [← List.length_eq_zero_iff] at h_not_empty; omega)
        <
      List.minimum_of_length_pos (l := send_timestamps bus_data) (by simp [send_timestamps]; rw [← List.length_eq_zero_iff] at h_not_empty; omega)
    := by
      set ts_min := List.minimum_of_length_pos (l := recv_timestamps bus_data) (by simp [recv_timestamps]; rw [← List.length_eq_zero_iff] at h_not_empty; omega)
      set te_min := List.minimum_of_length_pos (l := send_timestamps bus_data) (by simp [send_timestamps]; rw [← List.length_eq_zero_iff] at h_not_empty; omega)
      have ts_in_recv : ts_min ∈ recv_timestamps bus_data := by apply List.minimum_of_length_pos_mem
      have te_in_send : te_min ∈ send_timestamps bus_data := by apply List.minimum_of_length_pos_mem
      obtain ⟨ ts', pcs', pce', h_in ⟩ := send_timestamps_in_bus_data te_in_send
      specialize lt_proofs _ h_in; simp at lt_proofs
      have ⟨ h_in_ts, h_in_te ⟩ := bus_data_in_timestamp_lists h_in
      apply List.minimum_of_length_pos_le_of_mem at h_in_ts
      grind

    /-- The maximal send timestamp is larger than all the receive timestamps -/
    lemma send_max_gt_recvs
      (bus_data : List (FBB × FBB × List FBB × List FBB))
      (lt_proofs : ∀ entry ∈ bus_data, entry.1 < entry.2.1)
      (h_not_empty : ¬ bus_data = [])
    :
      List.maximum_of_length_pos (l := recv_timestamps bus_data) (by simp [recv_timestamps]; rw [← List.length_eq_zero_iff] at h_not_empty; omega)
        <
      List.maximum_of_length_pos (l := send_timestamps bus_data) (by simp [send_timestamps]; rw [← List.length_eq_zero_iff] at h_not_empty; omega)
    := by
      set ts_max := List.maximum_of_length_pos (l := recv_timestamps bus_data) (by simp [recv_timestamps]; rw [← List.length_eq_zero_iff] at h_not_empty; omega)
      set te_max := List.maximum_of_length_pos (l := send_timestamps bus_data) (by simp [send_timestamps]; rw [← List.length_eq_zero_iff] at h_not_empty; omega)
      have ts_in_recv : ts_max ∈ recv_timestamps bus_data := by apply List.maximum_of_length_pos_mem
      have te_in_send : te_max ∈ send_timestamps bus_data := by apply List.maximum_of_length_pos_mem
      obtain ⟨ te', pcs', pce', h_in ⟩ := recv_timestamps_in_bus_data ts_in_recv
      specialize lt_proofs _ h_in; simp at lt_proofs
      have ⟨ h_in_ts, h_in_te ⟩ := bus_data_in_timestamp_lists h_in
      apply List.le_maximum_of_length_pos_of_mem at h_in_te
      grind

  end timestamp_pairs

  section balancing

    /-- A non-empty timestamp bus is never balanced -/
    lemma nonempty_timestamp_bus_not_balanced
      (bus_data : List (FBB × FBB × List FBB × List FBB))
      (lt_proofs : ∀ entry ∈ bus_data, entry.1 < entry.2.1)
      (h_not_empty : ¬ bus_data = [])
      (h_not_too_long : (timestamp_bus bus_data lt_proofs).length < BB_prime)
    :
      ¬ is_balanced (timestamp_bus bus_data lt_proofs)
    := by
      intro h_balanced
      have := recv_min_lt_sends bus_data lt_proofs h_not_empty
      set ts_min := List.minimum_of_length_pos (l := recv_timestamps bus_data) (by simp [recv_timestamps]; rw [← List.length_eq_zero_iff] at h_not_empty; omega)
      set te_min := List.minimum_of_length_pos (l := send_timestamps bus_data) (by simp [send_timestamps]; rw [← List.length_eq_zero_iff] at h_not_empty; omega)
      have ts_in_recv : ts_min ∈ recv_timestamps bus_data := by apply List.minimum_of_length_pos_mem
      obtain ⟨ te', pcs', pce', h_in ⟩ := recv_timestamps_in_bus_data ts_in_recv
      (have ⟨ ts_min_in, hb ⟩  := bus_data_in_timestamp_bus lt_proofs h_in); clear hb
      have h_mult_n1_p1 := timestamp_bus_mult_n1_p1 bus_data lt_proofs
      obtain ⟨ bus', h_perm ⟩  := @mult_n1_p1_extract (-1) _ h_mult_n1_p1 h_balanced h_not_too_long _ ts_min_in
      simp [balanced_pair] at h_perm
      obtain ts_min_in_send : ts_min ∈ send_timestamps bus_data := by
        apply pos_ones_in_send_timestamps (pcs := pcs') (lt_proofs := lt_proofs)
        simp [List.Perm.mem_iff h_perm]
      obtain : te_min ≤ ts_min := by apply List.minimum_of_length_pos_le_of_mem ts_min_in_send
      grind

    /-- If a -1, 1 bus of length less than `BB_prime` is balanced
        by a single send and a single receive, then it can be deconstructed
        into the corresponding balancers and the rest -/
    lemma single_balancer_decomposition
      {ldata rdata : List FBB}
      {bus : List (FBB × List FBB)}
      (h_mult_n1_p1 : mult_n1_p1 bus)
      (h_len_bus : ([(1, ldata)] ++ bus ++ [(-1, rdata)]).length < BB_prime)
      (h_balance : InteractionList.is_balanced ([((1 : FBB), ldata)] ++ bus ++ [((-1 : FBB), rdata)]))
    :
      (ldata = rdata → is_balanced bus) ∧
      (¬ ldata = rdata →
        exists bus',
          bus.Perm ([((1 : FBB), rdata)] ++ bus' ++ [((-1 : FBB), ldata)]) ∧
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
          have h_perm : bus.Perm ([(1, rdata)] ++ bus' ++ [(-1, ldata)]) := by grind
          exists bus'; simp_all
          have : List.Perm
                    ((1, ldata) :: (bus ++ [(-1, rdata)]))
                    ([(1, ldata), (-1, ldata)] ++ bus' ++ [(1, rdata), (-1, rdata)])
            := by grind
          have : List.Perm
                    ([(1, ldata), (-1, ldata)] ++ bus' ++ [(1, rdata), (-1, rdata)])
                    ([(1, ldata), (1, rdata)] ++ bus' ++ [(-1, ldata), (-1, rdata)])
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
        . have : mult_n1_p1 ([(1, ldata)] ++ bus ++ [(-1, rdata)]) := by
            repeat rw [mult_n1_p1_append_iff]
            simp_all; simp [mult_n1_p1]
          have ⟨ bus_l, h_perm_l ⟩ := mult_n1_p1_extract (m := 1) (data := ldata) this h_balance h_len_bus (by grind)
          have ⟨ bus_r, h_perm_r ⟩ := mult_n1_p1_extract (m := -1) (data := rdata) this h_balance h_len_bus (by grind)
          simp [balanced_pair] at *
          suffices : (-1, ldata) ∈ bus ++ [(-1, rdata)] ∧ (1, rdata) ∈ (1, ldata) :: (bus ++ [(-1, rdata)])
          . grind
          . grind

  end balancing

#exit

    lemma balanced_bus_balancer_characterisation
      (bus_data : List (FBB × FBB × List FBB × List FBB))
      (lt_proofs : ∀ entry ∈ bus_data, entry.1 < entry.2.1)
      (lbal_data rbal_data : List FBB)
      (bus : List (FBB × List FBB))
      (h_perm : (timestamp_bus bus_data lt_proofs).Perm bus)
      (h_balance : InteractionList.is_balanced ([((1 : FBB), lbal_data)] ++ bus ++ [((-1 : FBB), rbal_data)]))
      (h_not_empty : ¬ bus_data = [])
    :
      let ts_min := List.minimum_of_length_pos (l := recv_timestamps bus_data) (by simp [recv_timestamps]; rw [← List.length_eq_zero_iff] at h_not_empty; omega)
      let te_max := List.maximum_of_length_pos (l := send_timestamps bus_data) (by simp [send_timestamps]; rw [← List.length_eq_zero_iff] at h_not_empty; omega)
      (∃ (pcs' pce' : List FBB),
         lbal_data = (ts_min :: pcs') ∧
         rbal_data = (te_max :: pce'))
    := by


      extract_lets ts_min te_max
      obtain h_neq : ¬ lbal_data = rbal_data := by
        have h_perm' := List.perm_append_comm_assoc [(1, lbal_data)] bus [(-1, rbal_data)]
        intro h_eq <;> simp_all
        have h_balance' := is_balanced_inv_perm h_balance h_perm'
        obtain h_not_balanced : ¬ is_balanced bus := by
          suffices : ¬ is_balanced (timestamp_bus bus_data lt_proofs)
          . intro hyp; apply this
            rw [List.perm_comm] at h_perm
            exact is_balanced_inv_perm hyp h_perm
        apply h_not_balanced
        apply is_balanced_of_append_is_balanced (l₂ := [(1, rbal_data), (-1, rbal_data)])
        . intro data
          simp [get_multiplicity]
          split_ifs <;> simp_all
        . assumption
      obtain ⟨ t', pcs', pce'', in_bus_data' ⟩ := @recv_timestamps_in_bus_data ts_min bus_data (by apply List.minimum_of_length_pos_mem)
      obtain ⟨ t'', pcs'', pce', in_bus_data'' ⟩ := @send_timestamps_in_bus_data te_max bus_data (by apply List.maximum_of_length_pos_mem)
      exists pcs', pce'


  end timestamps

end InteractionList
