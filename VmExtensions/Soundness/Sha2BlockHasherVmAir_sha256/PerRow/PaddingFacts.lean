/- 
  Layer A: Per-Row Facts (Padding Continuation)

  Packages the raw padding-row carry-over constraints into the proof-side
  contract `paddingPreservesWorkVars`.
-/
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.PerRow.TraceFacts

set_option autoImplicit false

set_option maxHeartbeats 1200000

namespace Sha2BlockHasherVmAir_sha256.BlockSpec

open BabyBear
open Sha2BlockHasherVmAir_sha256.constraints

section MatrixProjection

variable {C : Type → Type → Type} {ExtF : Type} [Field ExtF] [Circuit FBB ExtF C]

private theorem padding_bit_eq_of_poly {x y pad : FBB}
    (hpad : pad = 1)
    (hpoly : pad * (x - y) = 0) :
    x = y := by
  rw [hpad, one_mul] at hpoly
  exact sub_eq_zero.mp hpoly

private theorem next_padding_flag_eq_one_of_next_padding
    (air : C FBB ExtF) (row : ℕ)
    (hrot : rotation_consistent air)
    (hrow : row ≤ Circuit.last_row air)
    (hnext_pad :
      (1 - (is_round_row air (nextRow air row) + is_digest_row air (nextRow air row))) = 1) :
    next_padding_flag air row = 1 := by
  simpa [next_padding_flag, next_is_round_row_eq_nextRow air hrot row hrow,
    next_is_digest_row_eq_nextRow air hrot row hrow] using hnext_pad

private theorem padding_preserves_slot0
    (air : C FBB ExtF) (row : ℕ)
    (hp : padding_constraints air row)
    (hpad : next_padding_flag air row = 1) :
    ∀ bit, bit < 32 →
      work_vars_a air 0 bit row = next_work_vars_a air 0 bit row ∧
      work_vars_e air 0 bit row = next_work_vars_e air 0 bit row := by
  rcases hp with ⟨hp250_299, hp300_349, _, _, _, _⟩
  rcases hp250_299 with
    ⟨h250, h251, h252, h253, h254, h255, h256, h257, h258, h259, h260, h261, h262, h263, h264,
      h265, h266, h267, h268, h269, h270, h271, h272, h273, h274, h275, h276, h277, h278, h279,
      h280, h281, h282, h283, h284, h285, h286, h287, h288, h289, h290, h291, h292, h293, h294,
      h295, h296, h297, h298, h299⟩
  rcases hp300_349 with
    ⟨h300, h301, h302, h303, h304, h305, h306, h307, h308, h309, h310, h311, h312, h313, h314,
      h315, h316, h317, h318, h319, h320, h321, h322, h323, h324, h325, h326, h327, h328, h329,
      h330, h331, h332, h333, h334, h335, h336, h337, h338, h339, h340, h341, h342, h343, h344,
      h345, h346, h347, h348, h349⟩
  intro bit hbit
  interval_cases bit
  · exact ⟨padding_bit_eq_of_poly hpad h283, padding_bit_eq_of_poly hpad h284⟩
  · exact ⟨padding_bit_eq_of_poly hpad h285, padding_bit_eq_of_poly hpad h286⟩
  · exact ⟨padding_bit_eq_of_poly hpad h287, padding_bit_eq_of_poly hpad h288⟩
  · exact ⟨padding_bit_eq_of_poly hpad h289, padding_bit_eq_of_poly hpad h290⟩
  · exact ⟨padding_bit_eq_of_poly hpad h291, padding_bit_eq_of_poly hpad h292⟩
  · exact ⟨padding_bit_eq_of_poly hpad h293, padding_bit_eq_of_poly hpad h294⟩
  · exact ⟨padding_bit_eq_of_poly hpad h295, padding_bit_eq_of_poly hpad h296⟩
  · exact ⟨padding_bit_eq_of_poly hpad h297, padding_bit_eq_of_poly hpad h298⟩
  · exact ⟨padding_bit_eq_of_poly hpad h299, padding_bit_eq_of_poly hpad h300⟩
  · exact ⟨padding_bit_eq_of_poly hpad h301, padding_bit_eq_of_poly hpad h302⟩
  · exact ⟨padding_bit_eq_of_poly hpad h303, padding_bit_eq_of_poly hpad h304⟩
  · exact ⟨padding_bit_eq_of_poly hpad h305, padding_bit_eq_of_poly hpad h306⟩
  · exact ⟨padding_bit_eq_of_poly hpad h307, padding_bit_eq_of_poly hpad h308⟩
  · exact ⟨padding_bit_eq_of_poly hpad h309, padding_bit_eq_of_poly hpad h310⟩
  · exact ⟨padding_bit_eq_of_poly hpad h311, padding_bit_eq_of_poly hpad h312⟩
  · exact ⟨padding_bit_eq_of_poly hpad h313, padding_bit_eq_of_poly hpad h314⟩
  · exact ⟨padding_bit_eq_of_poly hpad h315, padding_bit_eq_of_poly hpad h316⟩
  · exact ⟨padding_bit_eq_of_poly hpad h317, padding_bit_eq_of_poly hpad h318⟩
  · exact ⟨padding_bit_eq_of_poly hpad h319, padding_bit_eq_of_poly hpad h320⟩
  · exact ⟨padding_bit_eq_of_poly hpad h321, padding_bit_eq_of_poly hpad h322⟩
  · exact ⟨padding_bit_eq_of_poly hpad h323, padding_bit_eq_of_poly hpad h324⟩
  · exact ⟨padding_bit_eq_of_poly hpad h325, padding_bit_eq_of_poly hpad h326⟩
  · exact ⟨padding_bit_eq_of_poly hpad h327, padding_bit_eq_of_poly hpad h328⟩
  · exact ⟨padding_bit_eq_of_poly hpad h329, padding_bit_eq_of_poly hpad h330⟩
  · exact ⟨padding_bit_eq_of_poly hpad h331, padding_bit_eq_of_poly hpad h332⟩
  · exact ⟨padding_bit_eq_of_poly hpad h333, padding_bit_eq_of_poly hpad h334⟩
  · exact ⟨padding_bit_eq_of_poly hpad h335, padding_bit_eq_of_poly hpad h336⟩
  · exact ⟨padding_bit_eq_of_poly hpad h337, padding_bit_eq_of_poly hpad h338⟩
  · exact ⟨padding_bit_eq_of_poly hpad h339, padding_bit_eq_of_poly hpad h340⟩
  · exact ⟨padding_bit_eq_of_poly hpad h341, padding_bit_eq_of_poly hpad h342⟩
  · exact ⟨padding_bit_eq_of_poly hpad h343, padding_bit_eq_of_poly hpad h344⟩
  · exact ⟨padding_bit_eq_of_poly hpad h345, padding_bit_eq_of_poly hpad h346⟩

private theorem padding_preserves_slot1
    (air : C FBB ExtF) (row : ℕ)
    (hp : padding_constraints air row)
    (hpad : next_padding_flag air row = 1) :
    ∀ bit, bit < 32 →
      work_vars_a air 1 bit row = next_work_vars_a air 1 bit row ∧
      work_vars_e air 1 bit row = next_work_vars_e air 1 bit row := by
  rcases hp with ⟨_, hp300_349, hp350_399, hp400_449, _, _⟩
  rcases hp300_349 with
    ⟨h300, h301, h302, h303, h304, h305, h306, h307, h308, h309, h310, h311, h312, h313, h314,
      h315, h316, h317, h318, h319, h320, h321, h322, h323, h324, h325, h326, h327, h328, h329,
      h330, h331, h332, h333, h334, h335, h336, h337, h338, h339, h340, h341, h342, h343, h344,
      h345, h346, h347, h348, h349⟩
  rcases hp350_399 with
    ⟨h350, h351, h352, h353, h354, h355, h356, h357, h358, h359, h360, h361, h362, h363, h364,
      h365, h366, h367, h368, h369, h370, h371, h372, h373, h374, h375, h376, h377, h378, h379,
      h380, h381, h382, h383, h384, h385, h386, h387, h388, h389, h390, h391, h392, h393, h394,
      h395, h396, h397, h398, h399⟩
  rcases hp400_449 with
    ⟨h400, h401, h402, h403, h404, h405, h406, h407, h408, h409, h410, h411, h412, h413, h414,
      h415, h416, h417, h418, h419, h420, h421, h422, h423, h424, h425, h426, h427, h428, h429,
      h430, h431, h432, h433, h434, h435, h436, h437, h438, h439, h440, h441, h442, h443, h444,
      h445, h446, h447, h448, h449⟩
  intro bit hbit
  interval_cases bit
  · exact ⟨padding_bit_eq_of_poly hpad h347, padding_bit_eq_of_poly hpad h348⟩
  · exact ⟨padding_bit_eq_of_poly hpad h349, padding_bit_eq_of_poly hpad h350⟩
  · exact ⟨padding_bit_eq_of_poly hpad h351, padding_bit_eq_of_poly hpad h352⟩
  · exact ⟨padding_bit_eq_of_poly hpad h353, padding_bit_eq_of_poly hpad h354⟩
  · exact ⟨padding_bit_eq_of_poly hpad h355, padding_bit_eq_of_poly hpad h356⟩
  · exact ⟨padding_bit_eq_of_poly hpad h357, padding_bit_eq_of_poly hpad h358⟩
  · exact ⟨padding_bit_eq_of_poly hpad h359, padding_bit_eq_of_poly hpad h360⟩
  · exact ⟨padding_bit_eq_of_poly hpad h361, padding_bit_eq_of_poly hpad h362⟩
  · exact ⟨padding_bit_eq_of_poly hpad h363, padding_bit_eq_of_poly hpad h364⟩
  · exact ⟨padding_bit_eq_of_poly hpad h365, padding_bit_eq_of_poly hpad h366⟩
  · exact ⟨padding_bit_eq_of_poly hpad h367, padding_bit_eq_of_poly hpad h368⟩
  · exact ⟨padding_bit_eq_of_poly hpad h369, padding_bit_eq_of_poly hpad h370⟩
  · exact ⟨padding_bit_eq_of_poly hpad h371, padding_bit_eq_of_poly hpad h372⟩
  · exact ⟨padding_bit_eq_of_poly hpad h373, padding_bit_eq_of_poly hpad h374⟩
  · exact ⟨padding_bit_eq_of_poly hpad h375, padding_bit_eq_of_poly hpad h376⟩
  · exact ⟨padding_bit_eq_of_poly hpad h377, padding_bit_eq_of_poly hpad h378⟩
  · exact ⟨padding_bit_eq_of_poly hpad h379, padding_bit_eq_of_poly hpad h380⟩
  · exact ⟨padding_bit_eq_of_poly hpad h381, padding_bit_eq_of_poly hpad h382⟩
  · exact ⟨padding_bit_eq_of_poly hpad h383, padding_bit_eq_of_poly hpad h384⟩
  · exact ⟨padding_bit_eq_of_poly hpad h385, padding_bit_eq_of_poly hpad h386⟩
  · exact ⟨padding_bit_eq_of_poly hpad h387, padding_bit_eq_of_poly hpad h388⟩
  · exact ⟨padding_bit_eq_of_poly hpad h389, padding_bit_eq_of_poly hpad h390⟩
  · exact ⟨padding_bit_eq_of_poly hpad h391, padding_bit_eq_of_poly hpad h392⟩
  · exact ⟨padding_bit_eq_of_poly hpad h393, padding_bit_eq_of_poly hpad h394⟩
  · exact ⟨padding_bit_eq_of_poly hpad h395, padding_bit_eq_of_poly hpad h396⟩
  · exact ⟨padding_bit_eq_of_poly hpad h397, padding_bit_eq_of_poly hpad h398⟩
  · exact ⟨padding_bit_eq_of_poly hpad h399, padding_bit_eq_of_poly hpad h400⟩
  · exact ⟨padding_bit_eq_of_poly hpad h401, padding_bit_eq_of_poly hpad h402⟩
  · exact ⟨padding_bit_eq_of_poly hpad h403, padding_bit_eq_of_poly hpad h404⟩
  · exact ⟨padding_bit_eq_of_poly hpad h405, padding_bit_eq_of_poly hpad h406⟩
  · exact ⟨padding_bit_eq_of_poly hpad h407, padding_bit_eq_of_poly hpad h408⟩
  · exact ⟨padding_bit_eq_of_poly hpad h409, padding_bit_eq_of_poly hpad h410⟩

private theorem padding_preserves_slot2
    (air : C FBB ExtF) (row : ℕ)
    (hp : padding_constraints air row)
    (hpad : next_padding_flag air row = 1) :
    ∀ bit, bit < 32 →
      work_vars_a air 2 bit row = next_work_vars_a air 2 bit row ∧
      work_vars_e air 2 bit row = next_work_vars_e air 2 bit row := by
  rcases hp with ⟨_, _, _, hp400_449, hp450_499, _⟩
  rcases hp400_449 with
    ⟨h400, h401, h402, h403, h404, h405, h406, h407, h408, h409, h410, h411, h412, h413, h414,
      h415, h416, h417, h418, h419, h420, h421, h422, h423, h424, h425, h426, h427, h428, h429,
      h430, h431, h432, h433, h434, h435, h436, h437, h438, h439, h440, h441, h442, h443, h444,
      h445, h446, h447, h448, h449⟩
  rcases hp450_499 with
    ⟨h450, h451, h452, h453, h454, h455, h456, h457, h458, h459, h460, h461, h462, h463, h464,
      h465, h466, h467, h468, h469, h470, h471, h472, h473, h474, h475, h476, h477, h478, h479,
      h480, h481, h482, h483, h484, h485, h486, h487, h488, h489, h490, h491, h492, h493, h494,
      h495, h496, h497, h498, h499⟩
  intro bit hbit
  interval_cases bit
  · exact ⟨padding_bit_eq_of_poly hpad h411, padding_bit_eq_of_poly hpad h412⟩
  · exact ⟨padding_bit_eq_of_poly hpad h413, padding_bit_eq_of_poly hpad h414⟩
  · exact ⟨padding_bit_eq_of_poly hpad h415, padding_bit_eq_of_poly hpad h416⟩
  · exact ⟨padding_bit_eq_of_poly hpad h417, padding_bit_eq_of_poly hpad h418⟩
  · exact ⟨padding_bit_eq_of_poly hpad h419, padding_bit_eq_of_poly hpad h420⟩
  · exact ⟨padding_bit_eq_of_poly hpad h421, padding_bit_eq_of_poly hpad h422⟩
  · exact ⟨padding_bit_eq_of_poly hpad h423, padding_bit_eq_of_poly hpad h424⟩
  · exact ⟨padding_bit_eq_of_poly hpad h425, padding_bit_eq_of_poly hpad h426⟩
  · exact ⟨padding_bit_eq_of_poly hpad h427, padding_bit_eq_of_poly hpad h428⟩
  · exact ⟨padding_bit_eq_of_poly hpad h429, padding_bit_eq_of_poly hpad h430⟩
  · exact ⟨padding_bit_eq_of_poly hpad h431, padding_bit_eq_of_poly hpad h432⟩
  · exact ⟨padding_bit_eq_of_poly hpad h433, padding_bit_eq_of_poly hpad h434⟩
  · exact ⟨padding_bit_eq_of_poly hpad h435, padding_bit_eq_of_poly hpad h436⟩
  · exact ⟨padding_bit_eq_of_poly hpad h437, padding_bit_eq_of_poly hpad h438⟩
  · exact ⟨padding_bit_eq_of_poly hpad h439, padding_bit_eq_of_poly hpad h440⟩
  · exact ⟨padding_bit_eq_of_poly hpad h441, padding_bit_eq_of_poly hpad h442⟩
  · exact ⟨padding_bit_eq_of_poly hpad h443, padding_bit_eq_of_poly hpad h444⟩
  · exact ⟨padding_bit_eq_of_poly hpad h445, padding_bit_eq_of_poly hpad h446⟩
  · exact ⟨padding_bit_eq_of_poly hpad h447, padding_bit_eq_of_poly hpad h448⟩
  · exact ⟨padding_bit_eq_of_poly hpad h449, padding_bit_eq_of_poly hpad h450⟩
  · exact ⟨padding_bit_eq_of_poly hpad h451, padding_bit_eq_of_poly hpad h452⟩
  · exact ⟨padding_bit_eq_of_poly hpad h453, padding_bit_eq_of_poly hpad h454⟩
  · exact ⟨padding_bit_eq_of_poly hpad h455, padding_bit_eq_of_poly hpad h456⟩
  · exact ⟨padding_bit_eq_of_poly hpad h457, padding_bit_eq_of_poly hpad h458⟩
  · exact ⟨padding_bit_eq_of_poly hpad h459, padding_bit_eq_of_poly hpad h460⟩
  · exact ⟨padding_bit_eq_of_poly hpad h461, padding_bit_eq_of_poly hpad h462⟩
  · exact ⟨padding_bit_eq_of_poly hpad h463, padding_bit_eq_of_poly hpad h464⟩
  · exact ⟨padding_bit_eq_of_poly hpad h465, padding_bit_eq_of_poly hpad h466⟩
  · exact ⟨padding_bit_eq_of_poly hpad h467, padding_bit_eq_of_poly hpad h468⟩
  · exact ⟨padding_bit_eq_of_poly hpad h469, padding_bit_eq_of_poly hpad h470⟩
  · exact ⟨padding_bit_eq_of_poly hpad h471, padding_bit_eq_of_poly hpad h472⟩
  · exact ⟨padding_bit_eq_of_poly hpad h473, padding_bit_eq_of_poly hpad h474⟩

private theorem padding_preserves_slot3
    (air : C FBB ExtF) (row : ℕ)
    (hp : padding_constraints air row)
    (hpad : next_padding_flag air row = 1) :
    ∀ bit, bit < 32 →
      work_vars_a air 3 bit row = next_work_vars_a air 3 bit row ∧
      work_vars_e air 3 bit row = next_work_vars_e air 3 bit row := by
  rcases hp with ⟨_, _, _, _, hp450_499, hp500_538⟩
  rcases hp450_499 with
    ⟨h450, h451, h452, h453, h454, h455, h456, h457, h458, h459, h460, h461, h462, h463, h464,
      h465, h466, h467, h468, h469, h470, h471, h472, h473, h474, h475, h476, h477, h478, h479,
      h480, h481, h482, h483, h484, h485, h486, h487, h488, h489, h490, h491, h492, h493, h494,
      h495, h496, h497, h498, h499⟩
  rcases hp500_538 with
    ⟨h500, h501, h502, h503, h504, h505, h506, h507, h508, h509, h510, h511, h512, h513, h514,
      h515, h516, h517, h518, h519, h520, h521, h522, h523, h524, h525, h526, h527, h528, h529,
      h530, h531, h532, h533, h534, h535, h536, h537, h538⟩
  intro bit hbit
  interval_cases bit
  · exact ⟨padding_bit_eq_of_poly hpad h475, padding_bit_eq_of_poly hpad h476⟩
  · exact ⟨padding_bit_eq_of_poly hpad h477, padding_bit_eq_of_poly hpad h478⟩
  · exact ⟨padding_bit_eq_of_poly hpad h479, padding_bit_eq_of_poly hpad h480⟩
  · exact ⟨padding_bit_eq_of_poly hpad h481, padding_bit_eq_of_poly hpad h482⟩
  · exact ⟨padding_bit_eq_of_poly hpad h483, padding_bit_eq_of_poly hpad h484⟩
  · exact ⟨padding_bit_eq_of_poly hpad h485, padding_bit_eq_of_poly hpad h486⟩
  · exact ⟨padding_bit_eq_of_poly hpad h487, padding_bit_eq_of_poly hpad h488⟩
  · exact ⟨padding_bit_eq_of_poly hpad h489, padding_bit_eq_of_poly hpad h490⟩
  · exact ⟨padding_bit_eq_of_poly hpad h491, padding_bit_eq_of_poly hpad h492⟩
  · exact ⟨padding_bit_eq_of_poly hpad h493, padding_bit_eq_of_poly hpad h494⟩
  · exact ⟨padding_bit_eq_of_poly hpad h495, padding_bit_eq_of_poly hpad h496⟩
  · exact ⟨padding_bit_eq_of_poly hpad h497, padding_bit_eq_of_poly hpad h498⟩
  · exact ⟨padding_bit_eq_of_poly hpad h499, padding_bit_eq_of_poly hpad h500⟩
  · exact ⟨padding_bit_eq_of_poly hpad h501, padding_bit_eq_of_poly hpad h502⟩
  · exact ⟨padding_bit_eq_of_poly hpad h503, padding_bit_eq_of_poly hpad h504⟩
  · exact ⟨padding_bit_eq_of_poly hpad h505, padding_bit_eq_of_poly hpad h506⟩
  · exact ⟨padding_bit_eq_of_poly hpad h507, padding_bit_eq_of_poly hpad h508⟩
  · exact ⟨padding_bit_eq_of_poly hpad h509, padding_bit_eq_of_poly hpad h510⟩
  · exact ⟨padding_bit_eq_of_poly hpad h511, padding_bit_eq_of_poly hpad h512⟩
  · exact ⟨padding_bit_eq_of_poly hpad h513, padding_bit_eq_of_poly hpad h514⟩
  · exact ⟨padding_bit_eq_of_poly hpad h515, padding_bit_eq_of_poly hpad h516⟩
  · exact ⟨padding_bit_eq_of_poly hpad h517, padding_bit_eq_of_poly hpad h518⟩
  · exact ⟨padding_bit_eq_of_poly hpad h519, padding_bit_eq_of_poly hpad h520⟩
  · exact ⟨padding_bit_eq_of_poly hpad h521, padding_bit_eq_of_poly hpad h522⟩
  · exact ⟨padding_bit_eq_of_poly hpad h523, padding_bit_eq_of_poly hpad h524⟩
  · exact ⟨padding_bit_eq_of_poly hpad h525, padding_bit_eq_of_poly hpad h526⟩
  · exact ⟨padding_bit_eq_of_poly hpad h527, padding_bit_eq_of_poly hpad h528⟩
  · exact ⟨padding_bit_eq_of_poly hpad h529, padding_bit_eq_of_poly hpad h530⟩
  · exact ⟨padding_bit_eq_of_poly hpad h531, padding_bit_eq_of_poly hpad h532⟩
  · exact ⟨padding_bit_eq_of_poly hpad h533, padding_bit_eq_of_poly hpad h534⟩
  · exact ⟨padding_bit_eq_of_poly hpad h535, padding_bit_eq_of_poly hpad h536⟩
  · exact ⟨padding_bit_eq_of_poly hpad h537, padding_bit_eq_of_poly hpad h538⟩

/-- The raw padding constraints do prove the proof-side `nextRow` transport
    contract for work variables. -/
theorem paddingPreservesWorkVars_of_constraints
    (air : C FBB ExtF) (row : ℕ)
    (hrot : rotation_consistent air)
    (hc : blockHasherConstraints air) :
    paddingPreservesWorkVars air row := by
  unfold paddingPreservesWorkVars
  refine fun hrow hnext_pad slot bit hslot hbit => ?_
  rcases hc row with ⟨_, _, _, hp, _, _, _, _⟩
  have hpad : next_padding_flag air row = 1 :=
    next_padding_flag_eq_one_of_next_padding air row hrot hrow hnext_pad
  interval_cases slot
  · rcases padding_preserves_slot0 air row hp hpad bit hbit with ⟨ha, he⟩
    refine ⟨?_, ?_⟩
    · calc
        work_vars_a air 0 bit row = next_work_vars_a air 0 bit row := ha
        _ = work_vars_a air 0 bit (nextRow air row) :=
          next_work_vars_a_eq_nextRow air hrot 0 bit row hrow
    · calc
        work_vars_e air 0 bit row = next_work_vars_e air 0 bit row := he
        _ = work_vars_e air 0 bit (nextRow air row) :=
          next_work_vars_e_eq_nextRow air hrot 0 bit row hrow
  · rcases padding_preserves_slot1 air row hp hpad bit hbit with ⟨ha, he⟩
    refine ⟨?_, ?_⟩
    · calc
        work_vars_a air 1 bit row = next_work_vars_a air 1 bit row := ha
        _ = work_vars_a air 1 bit (nextRow air row) :=
          next_work_vars_a_eq_nextRow air hrot 1 bit row hrow
    · calc
        work_vars_e air 1 bit row = next_work_vars_e air 1 bit row := he
        _ = work_vars_e air 1 bit (nextRow air row) :=
          next_work_vars_e_eq_nextRow air hrot 1 bit row hrow
  · rcases padding_preserves_slot2 air row hp hpad bit hbit with ⟨ha, he⟩
    refine ⟨?_, ?_⟩
    · calc
        work_vars_a air 2 bit row = next_work_vars_a air 2 bit row := ha
        _ = work_vars_a air 2 bit (nextRow air row) :=
          next_work_vars_a_eq_nextRow air hrot 2 bit row hrow
    · calc
        work_vars_e air 2 bit row = next_work_vars_e air 2 bit row := he
        _ = work_vars_e air 2 bit (nextRow air row) :=
          next_work_vars_e_eq_nextRow air hrot 2 bit row hrow
  · rcases padding_preserves_slot3 air row hp hpad bit hbit with ⟨ha, he⟩
    refine ⟨?_, ?_⟩
    · calc
        work_vars_a air 3 bit row = next_work_vars_a air 3 bit row := ha
        _ = work_vars_a air 3 bit (nextRow air row) :=
          next_work_vars_a_eq_nextRow air hrot 3 bit row hrow
    · calc
        work_vars_e air 3 bit row = next_work_vars_e air 3 bit row := he
        _ = work_vars_e air 3 bit (nextRow air row) :=
          next_work_vars_e_eq_nextRow air hrot 3 bit row hrow

end MatrixProjection

end Sha2BlockHasherVmAir_sha256.BlockSpec
