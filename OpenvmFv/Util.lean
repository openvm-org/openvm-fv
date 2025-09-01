import Mathlib

import LeanZKCircuit.OpenVM.Circuit

-- @[openvm_encapsulation]
-- lemma eq_one_of_sub_one_eq_zero [Field F] (a: F):
--   (a - 1 = 0) = (a = 1)
-- := by grind only

@[openvm_encapsulation]
lemma assert_eq [Field F] (a b: F):
  (a - b = 0) = (a = b)
:= by grind
