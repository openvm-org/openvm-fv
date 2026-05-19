/-
Original source: https://github.com/gdncc/Cryptography
Copyright (c) 2024 Gerald Doussot
Released under MIT license as described in the file LICENSE.
Authors: Gerald Doussot
-/

import VmExtensions.Keccak.Spec.Basic

/-!
# SHA-3 / Keccak Usage Examples

Examples showing the streaming (update/final) API and XOF squeeze API.
-/

/-- One-shot hash -/
def exampleOneShot : ByteArray :=
  let input := ByteArray.mk $ Array.replicate 32 0xAB
  SHA3_256.hashData input

/-- Streaming hash via update/final -/
def exampleStreaming : ByteArray :=
  let a := ByteArray.mk $ Array.replicate 10 1
  let b := ByteArray.mk $ Array.replicate 20 2
  let c := ByteArray.mk $ Array.replicate 30 3
  let state := SHA3_256.mk |> (SHA3_256.update · a) |> (SHA3_256.update · b)
  let state := SHA3_256.update state c
  SHA3_256.final state

/-- Keccak-256 (Ethereum variant) -/
def exampleKeccak256 : ByteArray :=
  let input := ByteArray.mk $ Array.replicate 32 0xAB
  Keccak256.hashData input
