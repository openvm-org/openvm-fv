import Mathlib

import LeanZKCircuit.OpenVM.Circuit

@[openvm_encapsulation]
lemma eq_one_of_sub_one_eq_zero [Field F] (a: F):
  (a - 1 = 0) = (a = 1)
:= by grind only
