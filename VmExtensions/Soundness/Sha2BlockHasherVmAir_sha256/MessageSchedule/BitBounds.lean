/- 
  Layer B: Message Schedule Correctness (Bit Bounds)

  Isolates the `next.message_schedule.w[slot][bit]` booleanity proof so the
  main schedule file stays smaller and the proof remains purely local to the
  per-bit constraints.
-/
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.TraceSpec
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.Core.SpecFacts
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.Core.FieldArithmetic

set_option autoImplicit false

set_option maxHeartbeats 1200000

namespace Sha2BlockHasherVmAir_sha256.BlockSpec

open BabyBear
open Sha2BlockHasherVmAir_sha256.constraints

section MatrixProjection

variable {C : Type → Type → Type} {ExtF : Type} [Field ExtF] [Circuit FBB ExtF C]

theorem schedule_bit_boolean_raw_slot0 (air : C FBB ExtF) (row bit : ℕ)
    (hbit : bit < 32)
    (hs : schedule_constraints air row)
    (hround_next : next_is_round_row air row = 1) :
    next_msg_schedule_w air 0 bit row = 0 ∨
      next_msg_schedule_w air 0 bit row = 1 := by
  have h550_599 := constraints_550_599_of_schedule_constraints air row hs
  have h600_649 := constraints_600_649_of_schedule_constraints air row hs
  unfold constraints_550_599 at h550_599
  unfold constraints_600_649 at h600_649
  interval_cases bit
  · have h575 : constraint_575 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_575, hround_next] using h575)
  · have h576 : constraint_576 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_576, hround_next] using h576)
  · have h577 : constraint_577 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_577, hround_next] using h577)
  · have h578 : constraint_578 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_578, hround_next] using h578)
  · have h579 : constraint_579 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_579, hround_next] using h579)
  · have h580 : constraint_580 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_580, hround_next] using h580)
  · have h581 : constraint_581 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_581, hround_next] using h581)
  · have h582 : constraint_582 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_582, hround_next] using h582)
  · have h583 : constraint_583 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_583, hround_next] using h583)
  · have h584 : constraint_584 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_584, hround_next] using h584)
  · have h585 : constraint_585 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_585, hround_next] using h585)
  · have h586 : constraint_586 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_586, hround_next] using h586)
  · have h587 : constraint_587 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_587, hround_next] using h587)
  · have h588 : constraint_588 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_588, hround_next] using h588)
  · have h589 : constraint_589 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_589, hround_next] using h589)
  · have h590 : constraint_590 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_590, hround_next] using h590)
  · have h591 : constraint_591 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_591, hround_next] using h591)
  · have h592 : constraint_592 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_592, hround_next] using h592)
  · have h593 : constraint_593 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_593, hround_next] using h593)
  · have h594 : constraint_594 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_594, hround_next] using h594)
  · have h595 : constraint_595 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_595, hround_next] using h595)
  · have h596 : constraint_596 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_596, hround_next] using h596)
  · have h597 : constraint_597 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_597, hround_next] using h597)
  · have h598 : constraint_598 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_598, hround_next] using h598)
  · have h599 : constraint_599 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_599, hround_next] using h599)
  · have h600 : constraint_600 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_600, hround_next] using h600)
  · have h601 : constraint_601 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_601, hround_next] using h601)
  · have h602 : constraint_602 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_602, hround_next] using h602)
  · have h603 : constraint_603 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_603, hround_next] using h603)
  · have h604 : constraint_604 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_604, hround_next] using h604)
  · have h605 : constraint_605 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_605, hround_next] using h605)
  · have h606 : constraint_606 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_606, hround_next] using h606)

theorem schedule_bit_boolean_raw_slot1 (air : C FBB ExtF) (row bit : ℕ)
    (hbit : bit < 32)
    (hs : schedule_constraints air row)
    (hround_next : next_is_round_row air row = 1) :
    next_msg_schedule_w air 1 bit row = 0 ∨
      next_msg_schedule_w air 1 bit row = 1 := by
  have h600_649 := constraints_600_649_of_schedule_constraints air row hs
  unfold constraints_600_649 at h600_649
  interval_cases bit
  · have h613 : constraint_613 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_613, hround_next] using h613)
  · have h614 : constraint_614 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_614, hround_next] using h614)
  · have h615 : constraint_615 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_615, hround_next] using h615)
  · have h616 : constraint_616 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_616, hround_next] using h616)
  · have h617 : constraint_617 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_617, hround_next] using h617)
  · have h618 : constraint_618 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_618, hround_next] using h618)
  · have h619 : constraint_619 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_619, hround_next] using h619)
  · have h620 : constraint_620 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_620, hround_next] using h620)
  · have h621 : constraint_621 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_621, hround_next] using h621)
  · have h622 : constraint_622 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_622, hround_next] using h622)
  · have h623 : constraint_623 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_623, hround_next] using h623)
  · have h624 : constraint_624 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_624, hround_next] using h624)
  · have h625 : constraint_625 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_625, hround_next] using h625)
  · have h626 : constraint_626 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_626, hround_next] using h626)
  · have h627 : constraint_627 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_627, hround_next] using h627)
  · have h628 : constraint_628 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_628, hround_next] using h628)
  · have h629 : constraint_629 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_629, hround_next] using h629)
  · have h630 : constraint_630 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_630, hround_next] using h630)
  · have h631 : constraint_631 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_631, hround_next] using h631)
  · have h632 : constraint_632 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_632, hround_next] using h632)
  · have h633 : constraint_633 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_633, hround_next] using h633)
  · have h634 : constraint_634 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_634, hround_next] using h634)
  · have h635 : constraint_635 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_635, hround_next] using h635)
  · have h636 : constraint_636 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_636, hround_next] using h636)
  · have h637 : constraint_637 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_637, hround_next] using h637)
  · have h638 : constraint_638 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_638, hround_next] using h638)
  · have h639 : constraint_639 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_639, hround_next] using h639)
  · have h640 : constraint_640 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_640, hround_next] using h640)
  · have h641 : constraint_641 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_641, hround_next] using h641)
  · have h642 : constraint_642 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_642, hround_next] using h642)
  · have h643 : constraint_643 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_643, hround_next] using h643)
  · have h644 : constraint_644 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_644, hround_next] using h644)

theorem schedule_bit_boolean_raw_slot2 (air : C FBB ExtF) (row bit : ℕ)
    (hbit : bit < 32)
    (hs : schedule_constraints air row)
    (hround_next : next_is_round_row air row = 1) :
    next_msg_schedule_w air 2 bit row = 0 ∨
      next_msg_schedule_w air 2 bit row = 1 := by
  have h650_699 := constraints_650_699_of_schedule_constraints air row hs
  unfold constraints_650_699 at h650_699
  interval_cases bit
  · have h651 : constraint_651 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_651, hround_next] using h651)
  · have h652 : constraint_652 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_652, hround_next] using h652)
  · have h653 : constraint_653 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_653, hround_next] using h653)
  · have h654 : constraint_654 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_654, hround_next] using h654)
  · have h655 : constraint_655 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_655, hround_next] using h655)
  · have h656 : constraint_656 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_656, hround_next] using h656)
  · have h657 : constraint_657 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_657, hround_next] using h657)
  · have h658 : constraint_658 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_658, hround_next] using h658)
  · have h659 : constraint_659 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_659, hround_next] using h659)
  · have h660 : constraint_660 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_660, hround_next] using h660)
  · have h661 : constraint_661 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_661, hround_next] using h661)
  · have h662 : constraint_662 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_662, hround_next] using h662)
  · have h663 : constraint_663 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_663, hround_next] using h663)
  · have h664 : constraint_664 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_664, hround_next] using h664)
  · have h665 : constraint_665 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_665, hround_next] using h665)
  · have h666 : constraint_666 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_666, hround_next] using h666)
  · have h667 : constraint_667 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_667, hround_next] using h667)
  · have h668 : constraint_668 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_668, hround_next] using h668)
  · have h669 : constraint_669 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_669, hround_next] using h669)
  · have h670 : constraint_670 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_670, hround_next] using h670)
  · have h671 : constraint_671 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_671, hround_next] using h671)
  · have h672 : constraint_672 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_672, hround_next] using h672)
  · have h673 : constraint_673 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_673, hround_next] using h673)
  · have h674 : constraint_674 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_674, hround_next] using h674)
  · have h675 : constraint_675 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_675, hround_next] using h675)
  · have h676 : constraint_676 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_676, hround_next] using h676)
  · have h677 : constraint_677 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_677, hround_next] using h677)
  · have h678 : constraint_678 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_678, hround_next] using h678)
  · have h679 : constraint_679 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_679, hround_next] using h679)
  · have h680 : constraint_680 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_680, hround_next] using h680)
  · have h681 : constraint_681 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_681, hround_next] using h681)
  · have h682 : constraint_682 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_682, hround_next] using h682)

theorem schedule_bit_boolean_raw_slot3 (air : C FBB ExtF) (row bit : ℕ)
    (hbit : bit < 32)
    (hs : schedule_constraints air row)
    (hround_next : next_is_round_row air row = 1) :
    next_msg_schedule_w air 3 bit row = 0 ∨
      next_msg_schedule_w air 3 bit row = 1 := by
  have h650_699 := constraints_650_699_of_schedule_constraints air row hs
  have h700_720 := constraints_700_720_of_schedule_constraints air row hs
  unfold constraints_650_699 at h650_699
  unfold constraints_700_720 at h700_720
  interval_cases bit
  · have h689 : constraint_689 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_689, hround_next] using h689)
  · have h690 : constraint_690 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_690, hround_next] using h690)
  · have h691 : constraint_691 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_691, hround_next] using h691)
  · have h692 : constraint_692 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_692, hround_next] using h692)
  · have h693 : constraint_693 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_693, hround_next] using h693)
  · have h694 : constraint_694 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_694, hround_next] using h694)
  · have h695 : constraint_695 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_695, hround_next] using h695)
  · have h696 : constraint_696 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_696, hround_next] using h696)
  · have h697 : constraint_697 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_697, hround_next] using h697)
  · have h698 : constraint_698 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_698, hround_next] using h698)
  · have h699 : constraint_699 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_699, hround_next] using h699)
  · have h700 : constraint_700 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_700, hround_next] using h700)
  · have h701 : constraint_701 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_701, hround_next] using h701)
  · have h702 : constraint_702 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_702, hround_next] using h702)
  · have h703 : constraint_703 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_703, hround_next] using h703)
  · have h704 : constraint_704 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_704, hround_next] using h704)
  · have h705 : constraint_705 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_705, hround_next] using h705)
  · have h706 : constraint_706 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_706, hround_next] using h706)
  · have h707 : constraint_707 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_707, hround_next] using h707)
  · have h708 : constraint_708 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_708, hround_next] using h708)
  · have h709 : constraint_709 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_709, hround_next] using h709)
  · have h710 : constraint_710 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_710, hround_next] using h710)
  · have h711 : constraint_711 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_711, hround_next] using h711)
  · have h712 : constraint_712 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_712, hround_next] using h712)
  · have h713 : constraint_713 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_713, hround_next] using h713)
  · have h714 : constraint_714 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_714, hround_next] using h714)
  · have h715 : constraint_715 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_715, hround_next] using h715)
  · have h716 : constraint_716 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_716, hround_next] using h716)
  · have h717 : constraint_717 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_717, hround_next] using h717)
  · have h718 : constraint_718 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_718, hround_next] using h718)
  · have h719 : constraint_719 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_719, hround_next] using h719)
  · have h720 : constraint_720 air row := by tauto
    exact bit_boolean_of_sq_eq_zero _ (by simpa [constraint_720, hround_next] using h720)

/-- Schedule word bits are boolean on round rows. -/
theorem schedule_bits_boolean (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hs : schedule_constraints air row)
    (hf_next : next_is_round_row air row = 1) :
    ∀ slot bit, slot < 4 → bit < 32 →
      msg_schedule_w air slot bit (nextRow air row) = 0 ∨
      msg_schedule_w air slot bit (nextRow air row) = 1 := by
  intro slot bit hslot hbit
  interval_cases slot
  · simpa [next_msg_schedule_w_eq_nextRow air hrot 0 bit row hrow] using
      schedule_bit_boolean_raw_slot0 air row bit hbit hs hf_next
  · simpa [next_msg_schedule_w_eq_nextRow air hrot 1 bit row hrow] using
      schedule_bit_boolean_raw_slot1 air row bit hbit hs hf_next
  · simpa [next_msg_schedule_w_eq_nextRow air hrot 2 bit row hrow] using
      schedule_bit_boolean_raw_slot2 air row bit hbit hs hf_next
  · simpa [next_msg_schedule_w_eq_nextRow air hrot 3 bit row hrow] using
      schedule_bit_boolean_raw_slot3 air row bit hbit hs hf_next

end MatrixProjection

end Sha2BlockHasherVmAir_sha256.BlockSpec
