import Mathlib

import LeanZKCircuit.OpenVM.Circuit

opaque undefined : Prop

@[openvm_encapsulation]
lemma assert_eq [Field F] (a b: F):
  (a - b = 0) = (a = b)
:= by grind
