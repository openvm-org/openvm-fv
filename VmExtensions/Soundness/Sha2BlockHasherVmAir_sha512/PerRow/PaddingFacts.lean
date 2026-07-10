/-
  Layer A: Per-Row Facts (Padding Continuation)

  Packages the grouped SHA-512 padding-row carry-over constraints into the
  proof-side contract `paddingPreservesWorkVars`, following the SHA-256 proof
  shape.
-/
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.PerRow.TraceFacts

set_option autoImplicit false

namespace Sha2BlockHasherVmAir_sha512.BlockSpec

open BabyBear
open Sha2BlockHasherVmAir_sha512.constraints

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
    ∀ bit, bit < 64 →
      work_vars_a air 0 bit row = next_work_vars_a air 0 bit row ∧
      work_vars_e air 0 bit row = next_work_vars_e air 0 bit row := by
  rcases hp with ⟨h500_549, h550_599, h600_649, h650_699, _, _, _, _, _, _, _, _⟩
  rcases h500_549 with
    ⟨h500, h501, h502, h503, h504, h505, h506, h507, h508, h509, h510, h511, h512, h513, h514, h515, h516, h517, h518, h519, h520, h521, h522, h523, h524, h525, h526, h527, h528, h529, h530, h531, h532, h533, h534, h535, h536, h537, h538, h539, h540, h541, h542, h543, h544, h545, h546, h547, h548, h549⟩
  rcases h550_599 with
    ⟨h550, h551, h552, h553, h554, h555, h556, h557, h558, h559, h560, h561, h562, h563, h564, h565, h566, h567, h568, h569, h570, h571, h572, h573, h574, h575, h576, h577, h578, h579, h580, h581, h582, h583, h584, h585, h586, h587, h588, h589, h590, h591, h592, h593, h594, h595, h596, h597, h598, h599⟩
  rcases h600_649 with
    ⟨h600, h601, h602, h603, h604, h605, h606, h607, h608, h609, h610, h611, h612, h613, h614, h615, h616, h617, h618, h619, h620, h621, h622, h623, h624, h625, h626, h627, h628, h629, h630, h631, h632, h633, h634, h635, h636, h637, h638, h639, h640, h641, h642, h643, h644, h645, h646, h647, h648, h649⟩
  rcases h650_699 with
    ⟨h650, h651, h652, h653, h654, h655, h656, h657, h658, h659, h660, h661, h662, h663, h664, h665, h666, h667, h668, h669, h670, h671, h672, h673, h674, h675, h676, h677, h678, h679, h680, h681, h682, h683, h684, h685, h686, h687, h688, h689, h690, h691, h692, h693, h694, h695, h696, h697, h698, h699⟩
  intro bit hbit
  interval_cases bit
  · exact ⟨padding_bit_eq_of_poly hpad h540, padding_bit_eq_of_poly hpad h541⟩
  · exact ⟨padding_bit_eq_of_poly hpad h542, padding_bit_eq_of_poly hpad h543⟩
  · exact ⟨padding_bit_eq_of_poly hpad h544, padding_bit_eq_of_poly hpad h545⟩
  · exact ⟨padding_bit_eq_of_poly hpad h546, padding_bit_eq_of_poly hpad h547⟩
  · exact ⟨padding_bit_eq_of_poly hpad h548, padding_bit_eq_of_poly hpad h549⟩
  · exact ⟨padding_bit_eq_of_poly hpad h550, padding_bit_eq_of_poly hpad h551⟩
  · exact ⟨padding_bit_eq_of_poly hpad h552, padding_bit_eq_of_poly hpad h553⟩
  · exact ⟨padding_bit_eq_of_poly hpad h554, padding_bit_eq_of_poly hpad h555⟩
  · exact ⟨padding_bit_eq_of_poly hpad h556, padding_bit_eq_of_poly hpad h557⟩
  · exact ⟨padding_bit_eq_of_poly hpad h558, padding_bit_eq_of_poly hpad h559⟩
  · exact ⟨padding_bit_eq_of_poly hpad h560, padding_bit_eq_of_poly hpad h561⟩
  · exact ⟨padding_bit_eq_of_poly hpad h562, padding_bit_eq_of_poly hpad h563⟩
  · exact ⟨padding_bit_eq_of_poly hpad h564, padding_bit_eq_of_poly hpad h565⟩
  · exact ⟨padding_bit_eq_of_poly hpad h566, padding_bit_eq_of_poly hpad h567⟩
  · exact ⟨padding_bit_eq_of_poly hpad h568, padding_bit_eq_of_poly hpad h569⟩
  · exact ⟨padding_bit_eq_of_poly hpad h570, padding_bit_eq_of_poly hpad h571⟩
  · exact ⟨padding_bit_eq_of_poly hpad h572, padding_bit_eq_of_poly hpad h573⟩
  · exact ⟨padding_bit_eq_of_poly hpad h574, padding_bit_eq_of_poly hpad h575⟩
  · exact ⟨padding_bit_eq_of_poly hpad h576, padding_bit_eq_of_poly hpad h577⟩
  · exact ⟨padding_bit_eq_of_poly hpad h578, padding_bit_eq_of_poly hpad h579⟩
  · exact ⟨padding_bit_eq_of_poly hpad h580, padding_bit_eq_of_poly hpad h581⟩
  · exact ⟨padding_bit_eq_of_poly hpad h582, padding_bit_eq_of_poly hpad h583⟩
  · exact ⟨padding_bit_eq_of_poly hpad h584, padding_bit_eq_of_poly hpad h585⟩
  · exact ⟨padding_bit_eq_of_poly hpad h586, padding_bit_eq_of_poly hpad h587⟩
  · exact ⟨padding_bit_eq_of_poly hpad h588, padding_bit_eq_of_poly hpad h589⟩
  · exact ⟨padding_bit_eq_of_poly hpad h590, padding_bit_eq_of_poly hpad h591⟩
  · exact ⟨padding_bit_eq_of_poly hpad h592, padding_bit_eq_of_poly hpad h593⟩
  · exact ⟨padding_bit_eq_of_poly hpad h594, padding_bit_eq_of_poly hpad h595⟩
  · exact ⟨padding_bit_eq_of_poly hpad h596, padding_bit_eq_of_poly hpad h597⟩
  · exact ⟨padding_bit_eq_of_poly hpad h598, padding_bit_eq_of_poly hpad h599⟩
  · exact ⟨padding_bit_eq_of_poly hpad h600, padding_bit_eq_of_poly hpad h601⟩
  · exact ⟨padding_bit_eq_of_poly hpad h602, padding_bit_eq_of_poly hpad h603⟩
  · exact ⟨padding_bit_eq_of_poly hpad h604, padding_bit_eq_of_poly hpad h605⟩
  · exact ⟨padding_bit_eq_of_poly hpad h606, padding_bit_eq_of_poly hpad h607⟩
  · exact ⟨padding_bit_eq_of_poly hpad h608, padding_bit_eq_of_poly hpad h609⟩
  · exact ⟨padding_bit_eq_of_poly hpad h610, padding_bit_eq_of_poly hpad h611⟩
  · exact ⟨padding_bit_eq_of_poly hpad h612, padding_bit_eq_of_poly hpad h613⟩
  · exact ⟨padding_bit_eq_of_poly hpad h614, padding_bit_eq_of_poly hpad h615⟩
  · exact ⟨padding_bit_eq_of_poly hpad h616, padding_bit_eq_of_poly hpad h617⟩
  · exact ⟨padding_bit_eq_of_poly hpad h618, padding_bit_eq_of_poly hpad h619⟩
  · exact ⟨padding_bit_eq_of_poly hpad h620, padding_bit_eq_of_poly hpad h621⟩
  · exact ⟨padding_bit_eq_of_poly hpad h622, padding_bit_eq_of_poly hpad h623⟩
  · exact ⟨padding_bit_eq_of_poly hpad h624, padding_bit_eq_of_poly hpad h625⟩
  · exact ⟨padding_bit_eq_of_poly hpad h626, padding_bit_eq_of_poly hpad h627⟩
  · exact ⟨padding_bit_eq_of_poly hpad h628, padding_bit_eq_of_poly hpad h629⟩
  · exact ⟨padding_bit_eq_of_poly hpad h630, padding_bit_eq_of_poly hpad h631⟩
  · exact ⟨padding_bit_eq_of_poly hpad h632, padding_bit_eq_of_poly hpad h633⟩
  · exact ⟨padding_bit_eq_of_poly hpad h634, padding_bit_eq_of_poly hpad h635⟩
  · exact ⟨padding_bit_eq_of_poly hpad h636, padding_bit_eq_of_poly hpad h637⟩
  · exact ⟨padding_bit_eq_of_poly hpad h638, padding_bit_eq_of_poly hpad h639⟩
  · exact ⟨padding_bit_eq_of_poly hpad h640, padding_bit_eq_of_poly hpad h641⟩
  · exact ⟨padding_bit_eq_of_poly hpad h642, padding_bit_eq_of_poly hpad h643⟩
  · exact ⟨padding_bit_eq_of_poly hpad h644, padding_bit_eq_of_poly hpad h645⟩
  · exact ⟨padding_bit_eq_of_poly hpad h646, padding_bit_eq_of_poly hpad h647⟩
  · exact ⟨padding_bit_eq_of_poly hpad h648, padding_bit_eq_of_poly hpad h649⟩
  · exact ⟨padding_bit_eq_of_poly hpad h650, padding_bit_eq_of_poly hpad h651⟩
  · exact ⟨padding_bit_eq_of_poly hpad h652, padding_bit_eq_of_poly hpad h653⟩
  · exact ⟨padding_bit_eq_of_poly hpad h654, padding_bit_eq_of_poly hpad h655⟩
  · exact ⟨padding_bit_eq_of_poly hpad h656, padding_bit_eq_of_poly hpad h657⟩
  · exact ⟨padding_bit_eq_of_poly hpad h658, padding_bit_eq_of_poly hpad h659⟩
  · exact ⟨padding_bit_eq_of_poly hpad h660, padding_bit_eq_of_poly hpad h661⟩
  · exact ⟨padding_bit_eq_of_poly hpad h662, padding_bit_eq_of_poly hpad h663⟩
  · exact ⟨padding_bit_eq_of_poly hpad h664, padding_bit_eq_of_poly hpad h665⟩
  · exact ⟨padding_bit_eq_of_poly hpad h666, padding_bit_eq_of_poly hpad h667⟩

private theorem padding_preserves_slot1
    (air : C FBB ExtF) (row : ℕ)
    (hp : padding_constraints air row)
    (hpad : next_padding_flag air row = 1) :
    ∀ bit, bit < 64 →
      work_vars_a air 1 bit row = next_work_vars_a air 1 bit row ∧
      work_vars_e air 1 bit row = next_work_vars_e air 1 bit row := by
  rcases hp with ⟨_, _, _, h650_699, h700_749, h750_799, _, _, _, _, _, _⟩
  rcases h650_699 with
    ⟨h650, h651, h652, h653, h654, h655, h656, h657, h658, h659, h660, h661, h662, h663, h664, h665, h666, h667, h668, h669, h670, h671, h672, h673, h674, h675, h676, h677, h678, h679, h680, h681, h682, h683, h684, h685, h686, h687, h688, h689, h690, h691, h692, h693, h694, h695, h696, h697, h698, h699⟩
  rcases h700_749 with
    ⟨h700, h701, h702, h703, h704, h705, h706, h707, h708, h709, h710, h711, h712, h713, h714, h715, h716, h717, h718, h719, h720, h721, h722, h723, h724, h725, h726, h727, h728, h729, h730, h731, h732, h733, h734, h735, h736, h737, h738, h739, h740, h741, h742, h743, h744, h745, h746, h747, h748, h749⟩
  rcases h750_799 with
    ⟨h750, h751, h752, h753, h754, h755, h756, h757, h758, h759, h760, h761, h762, h763, h764, h765, h766, h767, h768, h769, h770, h771, h772, h773, h774, h775, h776, h777, h778, h779, h780, h781, h782, h783, h784, h785, h786, h787, h788, h789, h790, h791, h792, h793, h794, h795, h796, h797, h798, h799⟩
  intro bit hbit
  interval_cases bit
  · exact ⟨padding_bit_eq_of_poly hpad h668, padding_bit_eq_of_poly hpad h669⟩
  · exact ⟨padding_bit_eq_of_poly hpad h670, padding_bit_eq_of_poly hpad h671⟩
  · exact ⟨padding_bit_eq_of_poly hpad h672, padding_bit_eq_of_poly hpad h673⟩
  · exact ⟨padding_bit_eq_of_poly hpad h674, padding_bit_eq_of_poly hpad h675⟩
  · exact ⟨padding_bit_eq_of_poly hpad h676, padding_bit_eq_of_poly hpad h677⟩
  · exact ⟨padding_bit_eq_of_poly hpad h678, padding_bit_eq_of_poly hpad h679⟩
  · exact ⟨padding_bit_eq_of_poly hpad h680, padding_bit_eq_of_poly hpad h681⟩
  · exact ⟨padding_bit_eq_of_poly hpad h682, padding_bit_eq_of_poly hpad h683⟩
  · exact ⟨padding_bit_eq_of_poly hpad h684, padding_bit_eq_of_poly hpad h685⟩
  · exact ⟨padding_bit_eq_of_poly hpad h686, padding_bit_eq_of_poly hpad h687⟩
  · exact ⟨padding_bit_eq_of_poly hpad h688, padding_bit_eq_of_poly hpad h689⟩
  · exact ⟨padding_bit_eq_of_poly hpad h690, padding_bit_eq_of_poly hpad h691⟩
  · exact ⟨padding_bit_eq_of_poly hpad h692, padding_bit_eq_of_poly hpad h693⟩
  · exact ⟨padding_bit_eq_of_poly hpad h694, padding_bit_eq_of_poly hpad h695⟩
  · exact ⟨padding_bit_eq_of_poly hpad h696, padding_bit_eq_of_poly hpad h697⟩
  · exact ⟨padding_bit_eq_of_poly hpad h698, padding_bit_eq_of_poly hpad h699⟩
  · exact ⟨padding_bit_eq_of_poly hpad h700, padding_bit_eq_of_poly hpad h701⟩
  · exact ⟨padding_bit_eq_of_poly hpad h702, padding_bit_eq_of_poly hpad h703⟩
  · exact ⟨padding_bit_eq_of_poly hpad h704, padding_bit_eq_of_poly hpad h705⟩
  · exact ⟨padding_bit_eq_of_poly hpad h706, padding_bit_eq_of_poly hpad h707⟩
  · exact ⟨padding_bit_eq_of_poly hpad h708, padding_bit_eq_of_poly hpad h709⟩
  · exact ⟨padding_bit_eq_of_poly hpad h710, padding_bit_eq_of_poly hpad h711⟩
  · exact ⟨padding_bit_eq_of_poly hpad h712, padding_bit_eq_of_poly hpad h713⟩
  · exact ⟨padding_bit_eq_of_poly hpad h714, padding_bit_eq_of_poly hpad h715⟩
  · exact ⟨padding_bit_eq_of_poly hpad h716, padding_bit_eq_of_poly hpad h717⟩
  · exact ⟨padding_bit_eq_of_poly hpad h718, padding_bit_eq_of_poly hpad h719⟩
  · exact ⟨padding_bit_eq_of_poly hpad h720, padding_bit_eq_of_poly hpad h721⟩
  · exact ⟨padding_bit_eq_of_poly hpad h722, padding_bit_eq_of_poly hpad h723⟩
  · exact ⟨padding_bit_eq_of_poly hpad h724, padding_bit_eq_of_poly hpad h725⟩
  · exact ⟨padding_bit_eq_of_poly hpad h726, padding_bit_eq_of_poly hpad h727⟩
  · exact ⟨padding_bit_eq_of_poly hpad h728, padding_bit_eq_of_poly hpad h729⟩
  · exact ⟨padding_bit_eq_of_poly hpad h730, padding_bit_eq_of_poly hpad h731⟩
  · exact ⟨padding_bit_eq_of_poly hpad h732, padding_bit_eq_of_poly hpad h733⟩
  · exact ⟨padding_bit_eq_of_poly hpad h734, padding_bit_eq_of_poly hpad h735⟩
  · exact ⟨padding_bit_eq_of_poly hpad h736, padding_bit_eq_of_poly hpad h737⟩
  · exact ⟨padding_bit_eq_of_poly hpad h738, padding_bit_eq_of_poly hpad h739⟩
  · exact ⟨padding_bit_eq_of_poly hpad h740, padding_bit_eq_of_poly hpad h741⟩
  · exact ⟨padding_bit_eq_of_poly hpad h742, padding_bit_eq_of_poly hpad h743⟩
  · exact ⟨padding_bit_eq_of_poly hpad h744, padding_bit_eq_of_poly hpad h745⟩
  · exact ⟨padding_bit_eq_of_poly hpad h746, padding_bit_eq_of_poly hpad h747⟩
  · exact ⟨padding_bit_eq_of_poly hpad h748, padding_bit_eq_of_poly hpad h749⟩
  · exact ⟨padding_bit_eq_of_poly hpad h750, padding_bit_eq_of_poly hpad h751⟩
  · exact ⟨padding_bit_eq_of_poly hpad h752, padding_bit_eq_of_poly hpad h753⟩
  · exact ⟨padding_bit_eq_of_poly hpad h754, padding_bit_eq_of_poly hpad h755⟩
  · exact ⟨padding_bit_eq_of_poly hpad h756, padding_bit_eq_of_poly hpad h757⟩
  · exact ⟨padding_bit_eq_of_poly hpad h758, padding_bit_eq_of_poly hpad h759⟩
  · exact ⟨padding_bit_eq_of_poly hpad h760, padding_bit_eq_of_poly hpad h761⟩
  · exact ⟨padding_bit_eq_of_poly hpad h762, padding_bit_eq_of_poly hpad h763⟩
  · exact ⟨padding_bit_eq_of_poly hpad h764, padding_bit_eq_of_poly hpad h765⟩
  · exact ⟨padding_bit_eq_of_poly hpad h766, padding_bit_eq_of_poly hpad h767⟩
  · exact ⟨padding_bit_eq_of_poly hpad h768, padding_bit_eq_of_poly hpad h769⟩
  · exact ⟨padding_bit_eq_of_poly hpad h770, padding_bit_eq_of_poly hpad h771⟩
  · exact ⟨padding_bit_eq_of_poly hpad h772, padding_bit_eq_of_poly hpad h773⟩
  · exact ⟨padding_bit_eq_of_poly hpad h774, padding_bit_eq_of_poly hpad h775⟩
  · exact ⟨padding_bit_eq_of_poly hpad h776, padding_bit_eq_of_poly hpad h777⟩
  · exact ⟨padding_bit_eq_of_poly hpad h778, padding_bit_eq_of_poly hpad h779⟩
  · exact ⟨padding_bit_eq_of_poly hpad h780, padding_bit_eq_of_poly hpad h781⟩
  · exact ⟨padding_bit_eq_of_poly hpad h782, padding_bit_eq_of_poly hpad h783⟩
  · exact ⟨padding_bit_eq_of_poly hpad h784, padding_bit_eq_of_poly hpad h785⟩
  · exact ⟨padding_bit_eq_of_poly hpad h786, padding_bit_eq_of_poly hpad h787⟩
  · exact ⟨padding_bit_eq_of_poly hpad h788, padding_bit_eq_of_poly hpad h789⟩
  · exact ⟨padding_bit_eq_of_poly hpad h790, padding_bit_eq_of_poly hpad h791⟩
  · exact ⟨padding_bit_eq_of_poly hpad h792, padding_bit_eq_of_poly hpad h793⟩
  · exact ⟨padding_bit_eq_of_poly hpad h794, padding_bit_eq_of_poly hpad h795⟩

private theorem padding_preserves_slot2
    (air : C FBB ExtF) (row : ℕ)
    (hp : padding_constraints air row)
    (hpad : next_padding_flag air row = 1) :
    ∀ bit, bit < 64 →
      work_vars_a air 2 bit row = next_work_vars_a air 2 bit row ∧
      work_vars_e air 2 bit row = next_work_vars_e air 2 bit row := by
  rcases hp with ⟨_, _, _, _, _, h750_799, h800_849, h850_899, h900_949, _, _, _⟩
  rcases h750_799 with
    ⟨h750, h751, h752, h753, h754, h755, h756, h757, h758, h759, h760, h761, h762, h763, h764, h765, h766, h767, h768, h769, h770, h771, h772, h773, h774, h775, h776, h777, h778, h779, h780, h781, h782, h783, h784, h785, h786, h787, h788, h789, h790, h791, h792, h793, h794, h795, h796, h797, h798, h799⟩
  rcases h800_849 with
    ⟨h800, h801, h802, h803, h804, h805, h806, h807, h808, h809, h810, h811, h812, h813, h814, h815, h816, h817, h818, h819, h820, h821, h822, h823, h824, h825, h826, h827, h828, h829, h830, h831, h832, h833, h834, h835, h836, h837, h838, h839, h840, h841, h842, h843, h844, h845, h846, h847, h848, h849⟩
  rcases h850_899 with
    ⟨h850, h851, h852, h853, h854, h855, h856, h857, h858, h859, h860, h861, h862, h863, h864, h865, h866, h867, h868, h869, h870, h871, h872, h873, h874, h875, h876, h877, h878, h879, h880, h881, h882, h883, h884, h885, h886, h887, h888, h889, h890, h891, h892, h893, h894, h895, h896, h897, h898, h899⟩
  rcases h900_949 with
    ⟨h900, h901, h902, h903, h904, h905, h906, h907, h908, h909, h910, h911, h912, h913, h914, h915, h916, h917, h918, h919, h920, h921, h922, h923, h924, h925, h926, h927, h928, h929, h930, h931, h932, h933, h934, h935, h936, h937, h938, h939, h940, h941, h942, h943, h944, h945, h946, h947, h948, h949⟩
  intro bit hbit
  interval_cases bit
  · exact ⟨padding_bit_eq_of_poly hpad h796, padding_bit_eq_of_poly hpad h797⟩
  · exact ⟨padding_bit_eq_of_poly hpad h798, padding_bit_eq_of_poly hpad h799⟩
  · exact ⟨padding_bit_eq_of_poly hpad h800, padding_bit_eq_of_poly hpad h801⟩
  · exact ⟨padding_bit_eq_of_poly hpad h802, padding_bit_eq_of_poly hpad h803⟩
  · exact ⟨padding_bit_eq_of_poly hpad h804, padding_bit_eq_of_poly hpad h805⟩
  · exact ⟨padding_bit_eq_of_poly hpad h806, padding_bit_eq_of_poly hpad h807⟩
  · exact ⟨padding_bit_eq_of_poly hpad h808, padding_bit_eq_of_poly hpad h809⟩
  · exact ⟨padding_bit_eq_of_poly hpad h810, padding_bit_eq_of_poly hpad h811⟩
  · exact ⟨padding_bit_eq_of_poly hpad h812, padding_bit_eq_of_poly hpad h813⟩
  · exact ⟨padding_bit_eq_of_poly hpad h814, padding_bit_eq_of_poly hpad h815⟩
  · exact ⟨padding_bit_eq_of_poly hpad h816, padding_bit_eq_of_poly hpad h817⟩
  · exact ⟨padding_bit_eq_of_poly hpad h818, padding_bit_eq_of_poly hpad h819⟩
  · exact ⟨padding_bit_eq_of_poly hpad h820, padding_bit_eq_of_poly hpad h821⟩
  · exact ⟨padding_bit_eq_of_poly hpad h822, padding_bit_eq_of_poly hpad h823⟩
  · exact ⟨padding_bit_eq_of_poly hpad h824, padding_bit_eq_of_poly hpad h825⟩
  · exact ⟨padding_bit_eq_of_poly hpad h826, padding_bit_eq_of_poly hpad h827⟩
  · exact ⟨padding_bit_eq_of_poly hpad h828, padding_bit_eq_of_poly hpad h829⟩
  · exact ⟨padding_bit_eq_of_poly hpad h830, padding_bit_eq_of_poly hpad h831⟩
  · exact ⟨padding_bit_eq_of_poly hpad h832, padding_bit_eq_of_poly hpad h833⟩
  · exact ⟨padding_bit_eq_of_poly hpad h834, padding_bit_eq_of_poly hpad h835⟩
  · exact ⟨padding_bit_eq_of_poly hpad h836, padding_bit_eq_of_poly hpad h837⟩
  · exact ⟨padding_bit_eq_of_poly hpad h838, padding_bit_eq_of_poly hpad h839⟩
  · exact ⟨padding_bit_eq_of_poly hpad h840, padding_bit_eq_of_poly hpad h841⟩
  · exact ⟨padding_bit_eq_of_poly hpad h842, padding_bit_eq_of_poly hpad h843⟩
  · exact ⟨padding_bit_eq_of_poly hpad h844, padding_bit_eq_of_poly hpad h845⟩
  · exact ⟨padding_bit_eq_of_poly hpad h846, padding_bit_eq_of_poly hpad h847⟩
  · exact ⟨padding_bit_eq_of_poly hpad h848, padding_bit_eq_of_poly hpad h849⟩
  · exact ⟨padding_bit_eq_of_poly hpad h850, padding_bit_eq_of_poly hpad h851⟩
  · exact ⟨padding_bit_eq_of_poly hpad h852, padding_bit_eq_of_poly hpad h853⟩
  · exact ⟨padding_bit_eq_of_poly hpad h854, padding_bit_eq_of_poly hpad h855⟩
  · exact ⟨padding_bit_eq_of_poly hpad h856, padding_bit_eq_of_poly hpad h857⟩
  · exact ⟨padding_bit_eq_of_poly hpad h858, padding_bit_eq_of_poly hpad h859⟩
  · exact ⟨padding_bit_eq_of_poly hpad h860, padding_bit_eq_of_poly hpad h861⟩
  · exact ⟨padding_bit_eq_of_poly hpad h862, padding_bit_eq_of_poly hpad h863⟩
  · exact ⟨padding_bit_eq_of_poly hpad h864, padding_bit_eq_of_poly hpad h865⟩
  · exact ⟨padding_bit_eq_of_poly hpad h866, padding_bit_eq_of_poly hpad h867⟩
  · exact ⟨padding_bit_eq_of_poly hpad h868, padding_bit_eq_of_poly hpad h869⟩
  · exact ⟨padding_bit_eq_of_poly hpad h870, padding_bit_eq_of_poly hpad h871⟩
  · exact ⟨padding_bit_eq_of_poly hpad h872, padding_bit_eq_of_poly hpad h873⟩
  · exact ⟨padding_bit_eq_of_poly hpad h874, padding_bit_eq_of_poly hpad h875⟩
  · exact ⟨padding_bit_eq_of_poly hpad h876, padding_bit_eq_of_poly hpad h877⟩
  · exact ⟨padding_bit_eq_of_poly hpad h878, padding_bit_eq_of_poly hpad h879⟩
  · exact ⟨padding_bit_eq_of_poly hpad h880, padding_bit_eq_of_poly hpad h881⟩
  · exact ⟨padding_bit_eq_of_poly hpad h882, padding_bit_eq_of_poly hpad h883⟩
  · exact ⟨padding_bit_eq_of_poly hpad h884, padding_bit_eq_of_poly hpad h885⟩
  · exact ⟨padding_bit_eq_of_poly hpad h886, padding_bit_eq_of_poly hpad h887⟩
  · exact ⟨padding_bit_eq_of_poly hpad h888, padding_bit_eq_of_poly hpad h889⟩
  · exact ⟨padding_bit_eq_of_poly hpad h890, padding_bit_eq_of_poly hpad h891⟩
  · exact ⟨padding_bit_eq_of_poly hpad h892, padding_bit_eq_of_poly hpad h893⟩
  · exact ⟨padding_bit_eq_of_poly hpad h894, padding_bit_eq_of_poly hpad h895⟩
  · exact ⟨padding_bit_eq_of_poly hpad h896, padding_bit_eq_of_poly hpad h897⟩
  · exact ⟨padding_bit_eq_of_poly hpad h898, padding_bit_eq_of_poly hpad h899⟩
  · exact ⟨padding_bit_eq_of_poly hpad h900, padding_bit_eq_of_poly hpad h901⟩
  · exact ⟨padding_bit_eq_of_poly hpad h902, padding_bit_eq_of_poly hpad h903⟩
  · exact ⟨padding_bit_eq_of_poly hpad h904, padding_bit_eq_of_poly hpad h905⟩
  · exact ⟨padding_bit_eq_of_poly hpad h906, padding_bit_eq_of_poly hpad h907⟩
  · exact ⟨padding_bit_eq_of_poly hpad h908, padding_bit_eq_of_poly hpad h909⟩
  · exact ⟨padding_bit_eq_of_poly hpad h910, padding_bit_eq_of_poly hpad h911⟩
  · exact ⟨padding_bit_eq_of_poly hpad h912, padding_bit_eq_of_poly hpad h913⟩
  · exact ⟨padding_bit_eq_of_poly hpad h914, padding_bit_eq_of_poly hpad h915⟩
  · exact ⟨padding_bit_eq_of_poly hpad h916, padding_bit_eq_of_poly hpad h917⟩
  · exact ⟨padding_bit_eq_of_poly hpad h918, padding_bit_eq_of_poly hpad h919⟩
  · exact ⟨padding_bit_eq_of_poly hpad h920, padding_bit_eq_of_poly hpad h921⟩
  · exact ⟨padding_bit_eq_of_poly hpad h922, padding_bit_eq_of_poly hpad h923⟩

private theorem padding_preserves_slot3
    (air : C FBB ExtF) (row : ℕ)
    (hp : padding_constraints air row)
    (hpad : next_padding_flag air row = 1) :
    ∀ bit, bit < 64 →
      work_vars_a air 3 bit row = next_work_vars_a air 3 bit row ∧
      work_vars_e air 3 bit row = next_work_vars_e air 3 bit row := by
  rcases hp with ⟨_, _, _, _, _, _, _, _, h900_949, h950_999, h1000_1049, h1050_1099⟩
  rcases h900_949 with
    ⟨h900, h901, h902, h903, h904, h905, h906, h907, h908, h909, h910, h911, h912, h913, h914, h915, h916, h917, h918, h919, h920, h921, h922, h923, h924, h925, h926, h927, h928, h929, h930, h931, h932, h933, h934, h935, h936, h937, h938, h939, h940, h941, h942, h943, h944, h945, h946, h947, h948, h949⟩
  rcases h950_999 with
    ⟨h950, h951, h952, h953, h954, h955, h956, h957, h958, h959, h960, h961, h962, h963, h964, h965, h966, h967, h968, h969, h970, h971, h972, h973, h974, h975, h976, h977, h978, h979, h980, h981, h982, h983, h984, h985, h986, h987, h988, h989, h990, h991, h992, h993, h994, h995, h996, h997, h998, h999⟩
  rcases h1000_1049 with
    ⟨h1000, h1001, h1002, h1003, h1004, h1005, h1006, h1007, h1008, h1009, h1010, h1011, h1012, h1013, h1014, h1015, h1016, h1017, h1018, h1019, h1020, h1021, h1022, h1023, h1024, h1025, h1026, h1027, h1028, h1029, h1030, h1031, h1032, h1033, h1034, h1035, h1036, h1037, h1038, h1039, h1040, h1041, h1042, h1043, h1044, h1045, h1046, h1047, h1048, h1049⟩
  rcases h1050_1099 with
    ⟨h1050, h1051, h1052, h1053, h1054, h1055, h1056, h1057, h1058, h1059, h1060, h1061, h1062, h1063, h1064, h1065, h1066, h1067, h1068, h1069, h1070, h1071, h1072, h1073, h1074, h1075, h1076, h1077, h1078, h1079, h1080, h1081, h1082, h1083, h1084, h1085, h1086, h1087, h1088, h1089, h1090, h1091, h1092, h1093, h1094, h1095, h1096, h1097, h1098, h1099⟩
  intro bit hbit
  interval_cases bit
  · exact ⟨padding_bit_eq_of_poly hpad h924, padding_bit_eq_of_poly hpad h925⟩
  · exact ⟨padding_bit_eq_of_poly hpad h926, padding_bit_eq_of_poly hpad h927⟩
  · exact ⟨padding_bit_eq_of_poly hpad h928, padding_bit_eq_of_poly hpad h929⟩
  · exact ⟨padding_bit_eq_of_poly hpad h930, padding_bit_eq_of_poly hpad h931⟩
  · exact ⟨padding_bit_eq_of_poly hpad h932, padding_bit_eq_of_poly hpad h933⟩
  · exact ⟨padding_bit_eq_of_poly hpad h934, padding_bit_eq_of_poly hpad h935⟩
  · exact ⟨padding_bit_eq_of_poly hpad h936, padding_bit_eq_of_poly hpad h937⟩
  · exact ⟨padding_bit_eq_of_poly hpad h938, padding_bit_eq_of_poly hpad h939⟩
  · exact ⟨padding_bit_eq_of_poly hpad h940, padding_bit_eq_of_poly hpad h941⟩
  · exact ⟨padding_bit_eq_of_poly hpad h942, padding_bit_eq_of_poly hpad h943⟩
  · exact ⟨padding_bit_eq_of_poly hpad h944, padding_bit_eq_of_poly hpad h945⟩
  · exact ⟨padding_bit_eq_of_poly hpad h946, padding_bit_eq_of_poly hpad h947⟩
  · exact ⟨padding_bit_eq_of_poly hpad h948, padding_bit_eq_of_poly hpad h949⟩
  · exact ⟨padding_bit_eq_of_poly hpad h950, padding_bit_eq_of_poly hpad h951⟩
  · exact ⟨padding_bit_eq_of_poly hpad h952, padding_bit_eq_of_poly hpad h953⟩
  · exact ⟨padding_bit_eq_of_poly hpad h954, padding_bit_eq_of_poly hpad h955⟩
  · exact ⟨padding_bit_eq_of_poly hpad h956, padding_bit_eq_of_poly hpad h957⟩
  · exact ⟨padding_bit_eq_of_poly hpad h958, padding_bit_eq_of_poly hpad h959⟩
  · exact ⟨padding_bit_eq_of_poly hpad h960, padding_bit_eq_of_poly hpad h961⟩
  · exact ⟨padding_bit_eq_of_poly hpad h962, padding_bit_eq_of_poly hpad h963⟩
  · exact ⟨padding_bit_eq_of_poly hpad h964, padding_bit_eq_of_poly hpad h965⟩
  · exact ⟨padding_bit_eq_of_poly hpad h966, padding_bit_eq_of_poly hpad h967⟩
  · exact ⟨padding_bit_eq_of_poly hpad h968, padding_bit_eq_of_poly hpad h969⟩
  · exact ⟨padding_bit_eq_of_poly hpad h970, padding_bit_eq_of_poly hpad h971⟩
  · exact ⟨padding_bit_eq_of_poly hpad h972, padding_bit_eq_of_poly hpad h973⟩
  · exact ⟨padding_bit_eq_of_poly hpad h974, padding_bit_eq_of_poly hpad h975⟩
  · exact ⟨padding_bit_eq_of_poly hpad h976, padding_bit_eq_of_poly hpad h977⟩
  · exact ⟨padding_bit_eq_of_poly hpad h978, padding_bit_eq_of_poly hpad h979⟩
  · exact ⟨padding_bit_eq_of_poly hpad h980, padding_bit_eq_of_poly hpad h981⟩
  · exact ⟨padding_bit_eq_of_poly hpad h982, padding_bit_eq_of_poly hpad h983⟩
  · exact ⟨padding_bit_eq_of_poly hpad h984, padding_bit_eq_of_poly hpad h985⟩
  · exact ⟨padding_bit_eq_of_poly hpad h986, padding_bit_eq_of_poly hpad h987⟩
  · exact ⟨padding_bit_eq_of_poly hpad h988, padding_bit_eq_of_poly hpad h989⟩
  · exact ⟨padding_bit_eq_of_poly hpad h990, padding_bit_eq_of_poly hpad h991⟩
  · exact ⟨padding_bit_eq_of_poly hpad h992, padding_bit_eq_of_poly hpad h993⟩
  · exact ⟨padding_bit_eq_of_poly hpad h994, padding_bit_eq_of_poly hpad h995⟩
  · exact ⟨padding_bit_eq_of_poly hpad h996, padding_bit_eq_of_poly hpad h997⟩
  · exact ⟨padding_bit_eq_of_poly hpad h998, padding_bit_eq_of_poly hpad h999⟩
  · exact ⟨padding_bit_eq_of_poly hpad h1000, padding_bit_eq_of_poly hpad h1001⟩
  · exact ⟨padding_bit_eq_of_poly hpad h1002, padding_bit_eq_of_poly hpad h1003⟩
  · exact ⟨padding_bit_eq_of_poly hpad h1004, padding_bit_eq_of_poly hpad h1005⟩
  · exact ⟨padding_bit_eq_of_poly hpad h1006, padding_bit_eq_of_poly hpad h1007⟩
  · exact ⟨padding_bit_eq_of_poly hpad h1008, padding_bit_eq_of_poly hpad h1009⟩
  · exact ⟨padding_bit_eq_of_poly hpad h1010, padding_bit_eq_of_poly hpad h1011⟩
  · exact ⟨padding_bit_eq_of_poly hpad h1012, padding_bit_eq_of_poly hpad h1013⟩
  · exact ⟨padding_bit_eq_of_poly hpad h1014, padding_bit_eq_of_poly hpad h1015⟩
  · exact ⟨padding_bit_eq_of_poly hpad h1016, padding_bit_eq_of_poly hpad h1017⟩
  · exact ⟨padding_bit_eq_of_poly hpad h1018, padding_bit_eq_of_poly hpad h1019⟩
  · exact ⟨padding_bit_eq_of_poly hpad h1020, padding_bit_eq_of_poly hpad h1021⟩
  · exact ⟨padding_bit_eq_of_poly hpad h1022, padding_bit_eq_of_poly hpad h1023⟩
  · exact ⟨padding_bit_eq_of_poly hpad h1024, padding_bit_eq_of_poly hpad h1025⟩
  · exact ⟨padding_bit_eq_of_poly hpad h1026, padding_bit_eq_of_poly hpad h1027⟩
  · exact ⟨padding_bit_eq_of_poly hpad h1028, padding_bit_eq_of_poly hpad h1029⟩
  · exact ⟨padding_bit_eq_of_poly hpad h1030, padding_bit_eq_of_poly hpad h1031⟩
  · exact ⟨padding_bit_eq_of_poly hpad h1032, padding_bit_eq_of_poly hpad h1033⟩
  · exact ⟨padding_bit_eq_of_poly hpad h1034, padding_bit_eq_of_poly hpad h1035⟩
  · exact ⟨padding_bit_eq_of_poly hpad h1036, padding_bit_eq_of_poly hpad h1037⟩
  · exact ⟨padding_bit_eq_of_poly hpad h1038, padding_bit_eq_of_poly hpad h1039⟩
  · exact ⟨padding_bit_eq_of_poly hpad h1040, padding_bit_eq_of_poly hpad h1041⟩
  · exact ⟨padding_bit_eq_of_poly hpad h1042, padding_bit_eq_of_poly hpad h1043⟩
  · exact ⟨padding_bit_eq_of_poly hpad h1044, padding_bit_eq_of_poly hpad h1045⟩
  · exact ⟨padding_bit_eq_of_poly hpad h1046, padding_bit_eq_of_poly hpad h1047⟩
  · exact ⟨padding_bit_eq_of_poly hpad h1048, padding_bit_eq_of_poly hpad h1049⟩
  · exact ⟨padding_bit_eq_of_poly hpad h1050, padding_bit_eq_of_poly hpad h1051⟩

/-- The top-level SHA-512 block-hasher constraints prove the proof-side
    `nextRow` transport contract for work variables. -/
theorem paddingPreservesWorkVars_of_constraints
    (air : C FBB ExtF) (row : ℕ)
    (hrot : rotation_consistent air)
    (hc : blockHasherConstraints air) :
    paddingPreservesWorkVars air row := by
  unfold paddingPreservesWorkVars
  refine fun hrow hnext_pad slot bit hslot hbit => ?_
  have hp := padding_constraints_of_blockHasherConstraints air hc row
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

end Sha2BlockHasherVmAir_sha512.BlockSpec
