/-
Original source: https://github.com/gdncc/Cryptography
Copyright (c) 2024 Gerald Doussot
Released under MIT license as described in the file LICENSE.
Authors: Gerald Doussot
-/

import VmExtensions.Keccak.Spec.Basic

/-!
# SHA-3 / Keccak Tests

This file contains a basic sanity check using the streaming (update/final) API.
-/

/-- Verify that hashing via update/final equals one-shot hashData. -/
def testHashEqUpdateFinal :=
  let a := ByteArray.mk $ Array.replicate 10 1
  let b := ByteArray.mk $ Array.replicate 20 2
  let c := a.append b
  let state := SHA3_256.mk |> (SHA3_256.update ·  a ) |> (SHA3_256.update ·  b )
  (SHA3_256.hashData c) == (SHA3_256.final state)

#guard testHashEqUpdateFinal
