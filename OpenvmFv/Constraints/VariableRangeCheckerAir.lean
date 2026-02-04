import OpenvmFv.Airs.VariableRangeCheckerAir
import OpenvmFv.Extraction.VariableRangeCheckerAir

namespace VariableRangeCheckerAir.constraints

  lemma constrain_interactions [Field F] [Field ExtF]
    (c: Valid_VariableRangeCheckerAir F ExtF)
    (h: VariableRangeCheckerAir.extraction.constrain_interactions c)
  : c.buses = fun index ↦
    if index = 4 then
      List.map
        (fun row ↦ (-c.main_cols.mult row 0, [c.preprocessed_cols.value row 0, c.preprocessed_cols.max_bits row 0]))
        (List.range (c.last_row + 1))
    else [] := by
    unfold VariableRangeCheckerAir.extraction.constrain_interactions at h
    simp [openvm_encapsulation] at h
    exact h

end VariableRangeCheckerAir.constraints
