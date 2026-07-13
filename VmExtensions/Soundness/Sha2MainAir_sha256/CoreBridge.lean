import VmExtensions.Soundness.Sha2MainAir_sha256.WordBridge
import VmExtensions.Sha2.Core
import Init.Data.Range.Lemmas

set_option autoImplicit false
set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 20_000

namespace VmExtensions.Sha2CompressOpcode

open BabyBear
open Sha2CompressionBridge_sha256
open Sha2BlockHasherVmAir_sha256.BlockSpec
open Sha2BlockHasherVmAir_sha256.Soundness.BusFacts
open Sha2MainAir_sha256.Soundness
open Sha2MainAir_sha256.constraints
open Sha2BlockHasherVmAir_sha256.constraints

private theorem getElem!_push_lt {α : Type} [Inhabited α]
    {xs : Array α} {x : α} {i : Nat} (hi : i < xs.size) :
    (xs.push x)[i]! = xs[i]! := by
  simp [Array.getElem!_eq_getD, Array.getElem?_push, hi, Nat.ne_of_lt hi]

private theorem getElem!_push_size {α : Type} [Inhabited α]
    {xs : Array α} {x : α} :
    (xs.push x)[xs.size]! = x := by
  rw [Array.getElem!_eq_getD]
  simp

def workingVarsToVector (state : WorkingVars) : Vector Word 8 :=
  Vector.ofFn fun i =>
    match i.1 with
    | 0 => state.a
    | 1 => state.b
    | 2 => state.c
    | 3 => state.d
    | 4 => state.e
    | 5 => state.f
    | 6 => state.g
    | _ => state.h

def vectorToWorkingVars (v : Vector Word 8) : WorkingVars where
  a := v[0]
  b := v[1]
  c := v[2]
  d := v[3]
  e := v[4]
  f := v[5]
  g := v[6]
  h := v[7]

private theorem vectorToWorkingVars_workingVarsToVector (state : WorkingVars) :
    vectorToWorkingVars (workingVarsToVector state) = state := by
  cases state
  simp [workingVarsToVector, vectorToWorkingVars]

private theorem workingVarsToVector_inj {x y : WorkingVars}
    (h : workingVarsToVector x = workingVarsToVector y) : x = y := by
  have := congrArg vectorToWorkingVars h
  simpa [vectorToWorkingVars_workingVarsToVector] using this

private theorem workingVarsToVector_add (x y : WorkingVars) :
    workingVarsToVector (x.add y) =
      #v[x.a + y.a, x.b + y.b, x.c + y.c, x.d + y.d,
        x.e + y.e, x.f + y.f, x.g + y.g, x.h + y.h] := by
  cases x
  cases y
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [workingVarsToVector, WorkingVars.add]

private theorem sha256K_vector_eq_coreK :
    Vector.ofFn (fun i : Fin 64 => sha256K[i.1]!) = CryptoHash.SHA256.K := by
  rfl

private theorem sha256K_eq_coreK (i : Fin 64) :
    sha256K[i.1]! = CryptoHash.SHA256.K[i] := by
  have h := congrArg (fun v => v[i]) sha256K_vector_eq_coreK
  simpa using h

private theorem sigma0_eq_smallSigma0 (x : Word) :
    CryptoHash.SHA256.sigma0 x = smallSigma0 x := by
  apply UInt32.toBitVec_inj.1
  change x.toBitVec.rotateRight 7 ^^^ x.toBitVec.rotateRight 18 ^^^ (x.toBitVec >>> 3) =
    (x.toBitVec >>> 7 ||| x.toBitVec <<< 25) ^^^
      (x.toBitVec >>> 18 ||| x.toBitVec <<< 14) ^^^
      (x.toBitVec >>> 3)
  simp [BitVec.rotateRight_def, rotr]

private theorem sigma1_eq_smallSigma1 (x : Word) :
    CryptoHash.SHA256.sigma1 x = smallSigma1 x := by
  apply UInt32.toBitVec_inj.1
  change x.toBitVec.rotateRight 17 ^^^ x.toBitVec.rotateRight 19 ^^^ (x.toBitVec >>> 10) =
    (x.toBitVec >>> 17 ||| x.toBitVec <<< 15) ^^^
      (x.toBitVec >>> 19 ||| x.toBitVec <<< 13) ^^^
      (x.toBitVec >>> 10)
  simp [BitVec.rotateRight_def, rotr]

private theorem Sigma0_eq_bigSigma0 (x : Word) :
    CryptoHash.SHA256.Sigma0 x = bigSigma0 x := by
  apply UInt32.toBitVec_inj.1
  change x.toBitVec.rotateRight 2 ^^^ x.toBitVec.rotateRight 13 ^^^ x.toBitVec.rotateRight 22 =
    (x.toBitVec >>> 2 ||| x.toBitVec <<< 30) ^^^
      (x.toBitVec >>> 13 ||| x.toBitVec <<< 19) ^^^
      (x.toBitVec >>> 22 ||| x.toBitVec <<< 10)
  simp [BitVec.rotateRight_def, rotr]

private theorem Sigma1_eq_bigSigma1 (x : Word) :
    CryptoHash.SHA256.Sigma1 x = bigSigma1 x := by
  apply UInt32.toBitVec_inj.1
  change x.toBitVec.rotateRight 6 ^^^ x.toBitVec.rotateRight 11 ^^^ x.toBitVec.rotateRight 25 =
    (x.toBitVec >>> 6 ||| x.toBitVec <<< 26) ^^^
      (x.toBitVec >>> 11 ||| x.toBitVec <<< 21) ^^^
      (x.toBitVec >>> 25 ||| x.toBitVec <<< 7)
  simp [BitVec.rotateRight_def, rotr]

private theorem Ch_eq_ch (x y z : Word) :
    CryptoHash.SHA256.Ch x y z = ch x y z := by
  simp [CryptoHash.SHA256.Ch, ch]

private theorem Maj_eq_maj (x y z : Word) :
    CryptoHash.SHA256.Maj x y z = maj x y z := by
  simp [CryptoHash.SHA256.Maj, maj]

private def scheduleLoadRange : Std.Range where
  start := 0
  stop := 16
  step := 1
  step_pos := by simp

private def coreRoundStep (state : Vector Word 8) (k w : Word) : Vector Word 8 :=
  let a := state[0]
  let b := state[1]
  let c := state[2]
  let d := state[3]
  let e := state[4]
  let f := state[5]
  let g := state[6]
  let h := state[7]
  let temp1 := h + CryptoHash.SHA256.Sigma1 e + CryptoHash.SHA256.Ch e f g + k + w
  let temp2 := CryptoHash.SHA256.Sigma0 a + CryptoHash.SHA256.Maj a b c
  #v[temp1 + temp2, a, b, c, d + temp1, e, f, g]

private theorem coreRoundStep_eq_roundStep (state : WorkingVars) (k w : Word) :
    coreRoundStep (workingVarsToVector state) k w =
      workingVarsToVector (roundStep state k w) := by
  cases state
  apply Vector.ext
  intro i hi
  interval_cases i <;>
    simp [coreRoundStep, workingVarsToVector, roundStep,
      Sigma1_eq_bigSigma1, Ch_eq_ch, Sigma0_eq_bigSigma0, Maj_eq_maj]

private def compressionPrefixStep (schedule : Array Word)
    (acc : WorkingVars × Array WorkingVars) (t : ℕ) :
    WorkingVars × Array WorkingVars :=
  let state := roundStep acc.1 (sha256K[t]!) (schedule[t]!)
  (state, acc.2.push state)

private def compressionPrefix (startState : WorkingVars) (schedule : Array Word) (n : ℕ) :
    WorkingVars × Array WorkingVars :=
  (List.range n).foldl (compressionPrefixStep schedule) (startState, #[startState])

private theorem compressionPrefix_succ
    (startState : WorkingVars) (schedule : Array Word) (n : ℕ) :
    compressionPrefix startState schedule (n + 1) =
      compressionPrefixStep schedule (compressionPrefix startState schedule n) n := by
  simp [compressionPrefix, List.range_succ, List.foldl_append, compressionPrefixStep]

private theorem compressionPrefix_size
    (startState : WorkingVars) (schedule : Array Word) :
    ∀ n, (compressionPrefix startState schedule n).2.size = n + 1 := by
  intro n
  induction n with
  | zero =>
      simp [compressionPrefix]
  | succ n ih =>
      rw [compressionPrefix_succ]
      simp [compressionPrefixStep, ih]

private theorem compressionPrefix_get_last
    (startState : WorkingVars) (schedule : Array Word) :
    ∀ n, (compressionPrefix startState schedule n).2[n]! =
      (compressionPrefix startState schedule n).1 := by
  intro n
  induction n with
  | zero =>
      simp [compressionPrefix]
  | succ n ih =>
      rw [compressionPrefix_succ]
      let state :=
        roundStep (compressionPrefix startState schedule n).1 (sha256K[n]!) (schedule[n]!)
      have hsize : (compressionPrefix startState schedule n).2.size = n + 1 :=
        compressionPrefix_size startState schedule n
      simpa [compressionPrefixStep, state, hsize] using
        (getElem!_push_size (xs := (compressionPrefix startState schedule n).2) (x := state))

private theorem compressionPrefix_get
    (startState : WorkingVars) (schedule : Array Word) :
    ∀ {n m}, n ≤ m →
      (compressionPrefix startState schedule m).2[n]! =
        (compressionPrefix startState schedule n).1 := by
  intro n m hnm
  induction m generalizing n with
  | zero =>
      have : n = 0 := by omega
      subst this
      simpa using compressionPrefix_get_last startState schedule 0
  | succ m ih =>
      by_cases hEq : n = m + 1
      · subst hEq
        simpa using compressionPrefix_get_last startState schedule (m + 1)
      · have hnm' : n ≤ m := by omega
        have hlt : n < (compressionPrefix startState schedule m).2.size := by
          simpa [compressionPrefix_size] using (show n < m + 1 by omega)
        rw [compressionPrefix_succ]
        simpa [compressionPrefixStep, getElem!_push_lt hlt] using ih hnm'

private theorem compressionTrace_eq_prefix
    (startState : WorkingVars) (schedule : Array Word) :
    compressionTrace startState schedule = (compressionPrefix startState schedule 64).2 := by
  rw [show compressionTrace startState schedule =
      (Id.run do
        let mut acc := (startState, #[startState])
        for t in List.range 64 do
          acc := compressionPrefixStep schedule acc t
        pure acc).2 by rfl]
  have hfold :=
    List.idRun_forIn_yield_eq_foldl
      (l := List.range 64)
      (f := fun t acc => pure (compressionPrefixStep schedule acc t))
      (init := (startState, #[startState]))
  exact congrArg Prod.snd (by simpa using hfold)

private theorem compressionTrace_get
    (startState : WorkingVars) (schedule : Array Word) {n : ℕ} (hn : n ≤ 64) :
    (compressionTrace startState schedule)[n]! = (compressionPrefix startState schedule n).1 := by
  rw [compressionTrace_eq_prefix]
  exact compressionPrefix_get startState schedule hn

private def scheduleArrayPrefix (msg : Fin 16 → Word) : Nat → Array Word
  | 0 => Array.ofFn msg
  | n + 1 =>
      let acc := scheduleArrayPrefix msg n
      acc.push
        (smallSigma1 acc[n + 14]! +
         acc[n + 9]! +
         smallSigma0 acc[n + 1]! +
         acc[n]!)

private def scheduleVectorLoadStep (msg : Fin 16 → Word)
    (acc : Vector Word 64) (i : Nat) : Vector Word 64 :=
  if hi : i < 16 then
    acc.set i (msg ⟨i, hi⟩) (by omega)
  else
    acc

private def scheduleVectorLoadPrefix (msg : Fin 16 → Word) : Nat → Vector Word 64
  | 0 => Vector.replicate 64 0
  | n + 1 => scheduleVectorLoadStep msg (scheduleVectorLoadPrefix msg n) n

private def scheduleVectorInit (msg : Fin 16 → Word) : Vector Word 64 :=
  Vector.ofFn fun i =>
    if h : i.1 < 16 then msg ⟨i.1, h⟩ else 0

private def scheduleVectorPrefix (msg : Fin 16 → Word) : Nat → Vector Word 64
  | 0 => scheduleVectorInit msg
  | n + 1 =>
      let acc := scheduleVectorPrefix msg n
      if h : n < 48 then
        let t := 16 + n
        let ht2 : t - 2 < 64 := by omega
        let ht7 : t - 7 < 64 := by omega
        let ht15 : t - 15 < 64 := by omega
        let ht16 : t - 16 < 64 := by omega
        let ht : t < 64 := by omega
        acc.set t
          (CryptoHash.SHA256.sigma1 (acc.get ⟨t - 2, ht2⟩) +
           acc.get ⟨t - 7, ht7⟩ +
           CryptoHash.SHA256.sigma0 (acc.get ⟨t - 15, ht15⟩) +
           acc.get ⟨t - 16, ht16⟩)
          ht
      else
        acc

private theorem scheduleVectorLoadPrefix_eq_fold (msg : Fin 16 → Word) :
    ∀ n, n ≤ 16 →
      scheduleVectorLoadPrefix msg n =
        (List.range n).foldl (scheduleVectorLoadStep msg) (Vector.replicate 64 0)
  | 0, _ => by simp [scheduleVectorLoadPrefix]
  | n + 1, hn => by
      simp [scheduleVectorLoadPrefix, scheduleVectorLoadPrefix_eq_fold msg n (by omega),
        List.range_succ, List.foldl_append]

private theorem scheduleVectorLoadPrefix_get_lt (msg : Fin 16 → Word) :
    ∀ n, n ≤ 16 → ∀ i, i < n → ∀ hi64 : i < 64,
      (scheduleVectorLoadPrefix msg n)[i]'hi64 = (scheduleVectorInit msg)[i]'hi64
  | 0, _, i, hi, _ => by omega
  | n + 1, hn, i, hi, hi64 => by
      have hn' : n < 16 := by omega
      by_cases hEq : i = n
      · subst hEq
        simp [scheduleVectorLoadPrefix, scheduleVectorLoadStep, scheduleVectorInit, hn']
      · have hold : i < n := by omega
        have ih := scheduleVectorLoadPrefix_get_lt msg n (by omega) i hold (by omega)
        have hset :
            ((scheduleVectorLoadPrefix msg n).set n (msg ⟨n, hn'⟩) (by omega))[i] =
              (scheduleVectorLoadPrefix msg n)[i] := by
          simpa using
            (Vector.getElem_set_ne
              (xs := scheduleVectorLoadPrefix msg n)
              (x := msg ⟨n, hn'⟩)
              (hi := by omega)
              (hj := hi64)
              (h := by omega))
        simp [scheduleVectorLoadPrefix, scheduleVectorLoadStep, hn', hset, ih]

private theorem scheduleVectorLoadPrefix_get_ge (msg : Fin 16 → Word) :
    ∀ n, n ≤ 16 → ∀ i, n ≤ i → ∀ hi64 : i < 64,
      (scheduleVectorLoadPrefix msg n)[i]'hi64 = 0
  | 0, _, i, _, hi64 => by
      simp [scheduleVectorLoadPrefix]
  | n + 1, hn, i, hi, hi64 => by
      have hn' : n < 16 := by omega
      have hne : i ≠ n := by omega
      have hge : n ≤ i := by omega
      have ih := scheduleVectorLoadPrefix_get_ge msg n (by omega) i hge hi64
      have hset :
          ((scheduleVectorLoadPrefix msg n).set n (msg ⟨n, hn'⟩) (by omega))[i] =
            (scheduleVectorLoadPrefix msg n)[i] := by
        simpa using
          (Vector.getElem_set_ne
            (xs := scheduleVectorLoadPrefix msg n)
            (x := msg ⟨n, hn'⟩)
            (hi := by omega)
            (hj := hi64)
            (h := Ne.symm hne))
      simp [scheduleVectorLoadPrefix, scheduleVectorLoadStep, hn', hset, ih]

private theorem scheduleVectorLoadPrefix_eq_init (msg : Fin 16 → Word) :
    scheduleVectorLoadPrefix msg 16 = scheduleVectorInit msg := by
  apply Vector.ext
  intro i hi64
  by_cases hi16 : i < 16
  · have hload := scheduleVectorLoadPrefix_get_lt msg 16 (by omega) i hi16 hi64
    simpa [scheduleVectorInit, hi16] using hload
  · have hload := scheduleVectorLoadPrefix_get_ge msg 16 (by omega) i (by omega) hi64
    simp [scheduleVectorInit, hi16, hload]

private def coreScheduleLoadLoop (msg : Fin 16 → Word) : Vector Word 64 :=
  (forIn' (m := Id) scheduleLoadRange (Vector.replicate 64 0) fun i h acc =>
      let hiUpper : i < scheduleLoadRange.stop := Membership.mem.upper h
      let hi16 : i < 16 := by simpa using hiUpper
      pure (.yield (acc.set i (msg ⟨i, hi16⟩) (by omega)))).run

private theorem coreScheduleLoadLoop_eq_fold (msg : Fin 16 → Word) :
    coreScheduleLoadLoop msg =
      (List.range' 0 16 1).foldl (scheduleVectorLoadStep msg) (Vector.replicate 64 0) := by
  unfold coreScheduleLoadLoop
  rw [Std.Range.forIn'_eq_forIn'_range']
  rw [List.forIn'_pure_yield_eq_foldl]
  simp [scheduleLoadRange]
  have hfun :
      (fun b (x : {a // a ∈ List.range' 0 16 1}) =>
        b.set x.1
          (msg ⟨x.1, by simpa [List.mem_range'_1] using x.2⟩)
          (by
            have hx : x.1 < 16 := by
              simpa [List.mem_range'_1] using x.2
            omega)) =
      (fun b (x : {a // a ∈ List.range' 0 16 1}) => scheduleVectorLoadStep msg b x.1) := by
    funext b x
    dsimp [scheduleVectorLoadStep]
    have hx : x.1 < 16 := by
      simpa [List.mem_range'_1] using x.2
    simp [hx]
  rw [hfun]
  rfl

private theorem coreScheduleLoadLoop_eq_init (msg : Fin 16 → Word) :
    coreScheduleLoadLoop msg = scheduleVectorInit msg := by
  calc
    coreScheduleLoadLoop msg =
        (List.range' 0 16 1).foldl (scheduleVectorLoadStep msg) (Vector.replicate 64 0) :=
      coreScheduleLoadLoop_eq_fold msg
    _ = (List.range 16).foldl (scheduleVectorLoadStep msg) (Vector.replicate 64 0) := by
      simp [List.range_eq_range']
    _ = scheduleVectorLoadPrefix msg 16 := by
      symm
      simpa using scheduleVectorLoadPrefix_eq_fold msg 16 (by omega)
    _ = scheduleVectorInit msg := scheduleVectorLoadPrefix_eq_init msg

private def coreScheduleLoadLoopBlock (block : Vector Word 16) : Vector Word 64 :=
  (forIn' (m := Id) ([0:16]) (Vector.replicate 64 0) fun i h acc =>
      let hi16 : i < 16 := by
        simpa using (Membership.mem.upper (r := ([0:16] : Std.Range)) h)
      pure (.yield (acc.set i block[i] (by omega)))).run

private theorem coreScheduleLoadLoopBlock_ofFn_eq (msg : Fin 16 → Word) :
    coreScheduleLoadLoopBlock (Vector.ofFn msg) = coreScheduleLoadLoop msg := by
  unfold coreScheduleLoadLoopBlock coreScheduleLoadLoop
  simp [scheduleLoadRange]

private def scheduleVectorExtendStep (acc : Vector Word 64) (offset : Nat) : Vector Word 64 :=
  if h : offset < 48 then
    let t := 16 + offset
    let ht2 : t - 2 < 64 := by omega
    let ht7 : t - 7 < 64 := by omega
    let ht15 : t - 15 < 64 := by omega
    let ht16 : t - 16 < 64 := by omega
    let ht : t < 64 := by omega
    acc.set t
      (CryptoHash.SHA256.sigma1 (acc.get ⟨t - 2, ht2⟩) +
       acc.get ⟨t - 7, ht7⟩ +
       CryptoHash.SHA256.sigma0 (acc.get ⟨t - 15, ht15⟩) +
       acc.get ⟨t - 16, ht16⟩)
      ht
  else
    acc

private theorem scheduleVectorPrefix_eq_fold (msg : Fin 16 → Word) :
    ∀ n, n ≤ 48 →
      scheduleVectorPrefix msg n =
        (List.range n).foldl scheduleVectorExtendStep (scheduleVectorInit msg)
  | 0, _ => by simp [scheduleVectorPrefix]
  | n + 1, hn => by
      simp [scheduleVectorPrefix, scheduleVectorPrefix_eq_fold msg n (by omega),
        scheduleVectorExtendStep, List.range_succ, List.foldl_append]

private def scheduleVectorCoreExtendStep (acc : Vector Word 64) (i : Nat) : Vector Word 64 :=
  if h : 16 ≤ i ∧ i < 64 then
    let ht2 : i - 2 < 64 := by omega
    let ht7 : i - 7 < 64 := by omega
    let ht15 : i - 15 < 64 := by omega
    let ht16 : i - 16 < 64 := by omega
    let ht : i < 64 := by omega
    acc.set i
      (acc.get ⟨i - 16, ht16⟩ +
       CryptoHash.SHA256.sigma0 (acc.get ⟨i - 15, ht15⟩) +
       acc.get ⟨i - 7, ht7⟩ +
       CryptoHash.SHA256.sigma1 (acc.get ⟨i - 2, ht2⟩))
      ht
  else
    acc

private theorem scheduleVectorCoreExtendStep_eq (acc : Vector Word 64) (offset : Nat)
    (hoffset : offset < 48) :
    scheduleVectorCoreExtendStep acc (16 + offset) = scheduleVectorExtendStep acc offset := by
  have hcore : 16 ≤ 16 + offset ∧ 16 + offset < 64 := by omega
  simp [scheduleVectorCoreExtendStep, scheduleVectorExtendStep, hoffset, hcore]
  rw [sigma0_eq_smallSigma0, sigma1_eq_smallSigma1]
  ac_rfl

private def scheduleExtendRange : Std.Range where
  start := 16
  stop := 64
  step := 1
  step_pos := by simp

private def coreScheduleExtendLoopFrom (init : Vector Word 64) : Vector Word 64 :=
  (forIn' (m := Id) scheduleExtendRange init fun i _ acc =>
      pure (.yield (scheduleVectorCoreExtendStep acc i))).run

private def coreScheduleExtendLoopRaw (init : Vector Word 64) : Vector Word 64 :=
  (forIn' (m := Id) ([16:64]) init fun i h acc =>
      let hi64 : i < 64 := by
        simpa using (Membership.mem.upper (r := ([16:64] : Std.Range)) h)
      let s0 := CryptoHash.SHA256.sigma0 acc[i - 15]
      let s1 := CryptoHash.SHA256.sigma1 acc[i - 2]
      let newWord := acc[i - 16] + s0 + acc[i - 7] + s1
      pure (.yield (acc.set i newWord hi64))).run

private def coreScheduleExtendLoop (msg : Fin 16 → Word) : Vector Word 64 :=
  coreScheduleExtendLoopFrom (scheduleVectorInit msg)

private theorem coreScheduleExtendLoop_eq_fold (msg : Fin 16 → Word) :
    coreScheduleExtendLoop msg =
      (List.range' 16 48 1).foldl scheduleVectorCoreExtendStep (scheduleVectorInit msg) := by
  unfold coreScheduleExtendLoop
  unfold coreScheduleExtendLoopFrom
  rw [Std.Range.forIn'_eq_forIn'_range']
  rw [List.forIn'_pure_yield_eq_foldl]
  simp [scheduleExtendRange]
  rfl

private theorem coreScheduleExtendLoopFrom_eq_fold (init : Vector Word 64) :
    coreScheduleExtendLoopFrom init =
      (List.range' 16 48 1).foldl scheduleVectorCoreExtendStep init := by
  unfold coreScheduleExtendLoopFrom
  rw [Std.Range.forIn'_eq_forIn'_range']
  rw [List.forIn'_pure_yield_eq_foldl]
  simp [scheduleExtendRange]
  rfl

private theorem coreScheduleExtendLoopRaw_eq_fold (init : Vector Word 64) :
    coreScheduleExtendLoopRaw init =
      (List.range' 16 48 1).foldl scheduleVectorCoreExtendStep init := by
  unfold coreScheduleExtendLoopRaw
  simp
  have hcongr :
      forIn' (m := Id) (List.range' 16 48 1) init
          (fun a h b =>
            let hx : 16 ≤ a ∧ a < 64 := by
              simpa [List.mem_range'_1] using h
            let h16 : a - 16 < 64 := by omega
            let h15 : a - 15 < 64 := by omega
            let h7 : a - 7 < 64 := by omega
            let h2 : a - 2 < 64 := by omega
            ForInStep.yield
              (b.set a
                (b[a - 16]'h16 + CryptoHash.SHA256.sigma0 (b[a - 15]'h15) + b[a - 7]'h7 +
                  CryptoHash.SHA256.sigma1 (b[a - 2]'h2))
                (by omega))) =
      forIn' (m := Id) (List.range' 16 48 1) init
          (fun a h b => ForInStep.yield (scheduleVectorCoreExtendStep b a)) := by
    apply List.forIn'_congr (w := rfl) (hb := rfl)
    intro a m b
    have hx : 16 ≤ a ∧ a < 64 := by
      simpa [List.mem_range'_1] using m
    have h15 : a - 15 < 64 := by omega
    have h2 : a - 2 < 64 := by omega
    have h16 : a - 16 < 64 := by omega
    have h7 : a - 7 < 64 := by omega
    change
      ForInStep.yield
        (b.set a
          (b.get ⟨a - 16, h16⟩ +
            CryptoHash.SHA256.sigma0 (b.get ⟨a - 15, h15⟩) +
            b.get ⟨a - 7, h7⟩ +
            CryptoHash.SHA256.sigma1 (b.get ⟨a - 2, h2⟩))
          (by omega)) =
      ForInStep.yield (scheduleVectorCoreExtendStep b a)
    simp [scheduleVectorCoreExtendStep, hx]
  calc
    (forIn' (m := Id) (List.range' 16 48 1) init
        (fun a h b =>
          let hx : 16 ≤ a ∧ a < 64 := by
            simpa [List.mem_range'_1] using h
          let h16 : a - 16 < 64 := by omega
          let h15 : a - 15 < 64 := by omega
          let h7 : a - 7 < 64 := by omega
          let h2 : a - 2 < 64 := by omega
          ForInStep.yield
            (b.set a
              (b[a - 16]'h16 + CryptoHash.SHA256.sigma0 (b[a - 15]'h15) + b[a - 7]'h7 +
                CryptoHash.SHA256.sigma1 (b[a - 2]'h2))
              (by omega)))).run
        =
      (forIn' (m := Id) (List.range' 16 48 1) init
          (fun a h b => ForInStep.yield (scheduleVectorCoreExtendStep b a))).run := by
      exact congrArg Id.run hcongr
    _ = (List.range' 16 48 1).foldl scheduleVectorCoreExtendStep init := by
      simpa using
        (List.idRun_forIn'_yield_eq_foldl
          (l := List.range' 16 48 1)
          (f := fun a _ b => scheduleVectorCoreExtendStep b a)
          (init := init))

private theorem coreScheduleExtendLoopRaw_eq_from (init : Vector Word 64) :
    coreScheduleExtendLoopRaw init = coreScheduleExtendLoopFrom init := by
  rw [coreScheduleExtendLoopRaw_eq_fold, coreScheduleExtendLoopFrom_eq_fold]

private theorem coreScheduleExtendLoop_eq_prefix (msg : Fin 16 → Word) :
    coreScheduleExtendLoop msg = scheduleVectorPrefix msg 48 := by
  calc
    coreScheduleExtendLoop msg =
        (List.range' 16 48 1).foldl scheduleVectorCoreExtendStep (scheduleVectorInit msg) :=
      coreScheduleExtendLoop_eq_fold msg
    _ =
        (List.range 48).foldl
          (fun acc offset => scheduleVectorCoreExtendStep acc (16 + offset))
          (scheduleVectorInit msg) := by
      rw [List.range'_eq_map_range, List.foldl_map]
    _ =
        (List.range 48).foldl scheduleVectorExtendStep (scheduleVectorInit msg) := by
      congr
      funext acc offset
      by_cases hoffset : offset < 48
      · simpa using scheduleVectorCoreExtendStep_eq acc offset hoffset
      · have h64 : ¬ 16 + offset < 64 := by omega
        simp [scheduleVectorCoreExtendStep, scheduleVectorExtendStep, hoffset, h64]
    _ = scheduleVectorPrefix msg 48 := by
      symm
      simpa using scheduleVectorPrefix_eq_fold msg 48 (by omega)

private theorem rcoToList_0_16 :
    (((0 : Nat)...16).toList) = List.range' 0 16 1 := by
  native_decide

private theorem rcoToList_16_64 :
    (((16 : Nat)...64).toList) = List.range' 16 48 1 := by
  native_decide

private theorem expandMessageSchedule_eq_scheduleVectorPrefix (msg : Fin 16 → Word) :
    CryptoHash.SHA256.expandMessageSchedule (Vector.ofFn msg) = scheduleVectorPrefix msg 48 := by
  let normalizedRaw :=
    (forIn' (m := Id) (((16 : Nat)...64).toList)
        ((forIn' (m := Id) (((0 : Nat)...16).toList) (Vector.replicate 64 0) fun a h b => do
            PUnit.unit
            let ha16 : a < 16 := Std.Rco.lt_upper_of_mem (Std.Rco.mem_toList_iff_mem.mp h)
            ForInStep.yield
              (b.set a
                (msg ⟨a, ha16⟩)
                (by omega))).run)
        fun a h b => do
          PUnit.unit
          let hmem : a ∈ ((16 : Nat)...64) := Std.Rco.mem_toList_iff_mem.mp h
          let hBounds : 16 ≤ a ∧ a < 64 := by
            exact ⟨Std.Rco.lower_le_of_mem hmem, Std.Rco.lt_upper_of_mem hmem⟩
          let h16 : a - 16 < 64 := by omega
          let h15 : a - 15 < 64 := by omega
          let h7 : a - 7 < 64 := by omega
          let h2 : a - 2 < 64 := by omega
          ForInStep.yield
            (b.set a
              (b[a - 16]'h16 + CryptoHash.SHA256.sigma0 (b[a - 15]'h15) + b[a - 7]'h7 +
                CryptoHash.SHA256.sigma1 (b[a - 2]'h2))
              (by omega))).run
  let expandedRaw :=
    (forIn' (m := Id) (((16 : Nat)...64).toList)
        ((forIn' (m := Id) (((0 : Nat)...16).toList) (Vector.replicate 64 0) fun a h b =>
            let hmem : a ∈ ((0 : Nat)...16) := Std.Rco.mem_toList_iff_mem.mp h
            let ha16 : a < 16 := Std.Rco.lt_upper_of_mem hmem
            pure (.yield (b.set a (msg ⟨a, ha16⟩) (by omega)))).run)
        fun a h b =>
          let hmem : a ∈ ((16 : Nat)...64) := Std.Rco.mem_toList_iff_mem.mp h
          let hBounds : 16 ≤ a ∧ a < 64 := by
            exact ⟨Std.Rco.lower_le_of_mem hmem, Std.Rco.lt_upper_of_mem hmem⟩
          let h16 : a - 16 < 64 := by omega
          let h15 : a - 15 < 64 := by omega
          let h7 : a - 7 < 64 := by omega
          let h2 : a - 2 < 64 := by omega
          pure (.yield
            (b.set a
              (b[a - 16]'h16 + CryptoHash.SHA256.sigma0 (b[a - 15]'h15) + b[a - 7]'h7 +
                CryptoHash.SHA256.sigma1 (b[a - 2]'h2))
              (by omega)))).run
  have hNormalizedEqExpanded : normalizedRaw = expandedRaw := by
    unfold normalizedRaw expandedRaw
    have hInner :
        (forIn' (m := Id) (((0 : Nat)...16).toList) (Vector.replicate 64 0) fun a h b => do
            PUnit.unit
            let ha16 : a < 16 := Std.Rco.lt_upper_of_mem (Std.Rco.mem_toList_iff_mem.mp h)
            ForInStep.yield
              (b.set a
                (msg ⟨a, ha16⟩)
                (by omega))).run =
          (forIn' (m := Id) (((0 : Nat)...16).toList) (Vector.replicate 64 0) fun a h b =>
            let hmem : a ∈ ((0 : Nat)...16) := Std.Rco.mem_toList_iff_mem.mp h
            let ha16 : a < 16 := Std.Rco.lt_upper_of_mem hmem
            pure (.yield (b.set a (msg ⟨a, ha16⟩) (by omega)))).run := by
      apply congrArg Id.run
      apply List.forIn'_congr (w := rfl) (hb := rfl)
      intro a h b
      rfl
    rw [hInner]
    apply congrArg Id.run
    apply List.forIn'_congr (w := rfl) (hb := rfl)
    intro a h b
    rfl
  calc
    CryptoHash.SHA256.expandMessageSchedule (Vector.ofFn msg) =
        normalizedRaw := by
      unfold CryptoHash.SHA256.expandMessageSchedule normalizedRaw
      simp [Std.Rco.forIn'_eq_forIn'_toList]
      have hInnerNormalized :
          (forIn' (m := Id) (((0 : Nat)...16).toList) (Vector.replicate 64 0) fun a h b => do
              PUnit.unit
              ForInStep.yield
                (b.set a
                  (msg ⟨a, Std.Rco.lt_upper_of_mem (Std.Rco.mem_toList_iff_mem.mp h)⟩)
                  (by
                    have ha16 : a < 16 := Std.Rco.lt_upper_of_mem (Std.Rco.mem_toList_iff_mem.mp h)
                    omega))).run =
            (forIn' (m := Id) (((0 : Nat)...16).toList) (Vector.replicate 64 0) fun a h b => do
              PUnit.unit
              let ha16 : a < 16 := Std.Rco.lt_upper_of_mem (Std.Rco.mem_toList_iff_mem.mp h)
              ForInStep.yield
                (b.set a
                  (msg ⟨a, ha16⟩)
                  (by omega))).run := by
        apply congrArg Id.run
        apply List.forIn'_congr (w := rfl) (hb := rfl)
        intro a h b
        rfl
      rw [hInnerNormalized]
      apply congrArg Id.run
      apply List.forIn'_congr (w := rfl) (hb := rfl)
      intro a h b
      rfl
    _ = expandedRaw := hNormalizedEqExpanded
    _ = coreScheduleExtendLoopRaw (coreScheduleLoadLoopBlock (Vector.ofFn msg)) := by
      simp [expandedRaw, coreScheduleExtendLoopRaw, coreScheduleLoadLoopBlock,
        rcoToList_0_16, rcoToList_16_64]
    _ = coreScheduleExtendLoopRaw (coreScheduleLoadLoop msg) := by
      rw [coreScheduleLoadLoopBlock_ofFn_eq]
    _ = coreScheduleExtendLoopFrom (coreScheduleLoadLoop msg) := by
      rw [coreScheduleExtendLoopRaw_eq_from]
    _ = coreScheduleExtendLoopFrom (scheduleVectorInit msg) := by
      rw [coreScheduleLoadLoop_eq_init]
    _ = scheduleVectorPrefix msg 48 := by
      simpa [coreScheduleExtendLoop] using coreScheduleExtendLoop_eq_prefix msg

private theorem scheduleArrayPrefix_size (msg : Fin 16 → Word) :
    ∀ n, (scheduleArrayPrefix msg n).size = 16 + n
  | 0 => by simp [scheduleArrayPrefix]
  | n + 1 => by
      rw [scheduleArrayPrefix]
      simp [scheduleArrayPrefix_size msg n]
      omega

private theorem scheduleArrayPrefix_get_lt (msg : Fin 16 → Word) :
    ∀ n i, i < 16 + n →
      (scheduleArrayPrefix msg (n + 1))[i]! = (scheduleArrayPrefix msg n)[i]!
  | n, i, hi => by
      rw [scheduleArrayPrefix]
      have hi' : i < (scheduleArrayPrefix msg n).size := by
        simpa [scheduleArrayPrefix_size msg n] using hi
      simpa using
        (getElem!_push_lt
          (xs := scheduleArrayPrefix msg n)
          (x :=
            smallSigma1 (scheduleArrayPrefix msg n)[n + 14]! +
            (scheduleArrayPrefix msg n)[n + 9]! +
            smallSigma0 (scheduleArrayPrefix msg n)[n + 1]! +
            (scheduleArrayPrefix msg n)[n]!)
          hi')

private theorem scheduleArrayPrefix_get_new (msg : Fin 16 → Word) :
    ∀ n,
      (scheduleArrayPrefix msg (n + 1))[16 + n]! =
        (smallSigma1 (scheduleArrayPrefix msg n)[n + 14]! +
         (scheduleArrayPrefix msg n)[n + 9]! +
         smallSigma0 (scheduleArrayPrefix msg n)[n + 1]! +
         (scheduleArrayPrefix msg n)[n]!)
  | n => by
      rw [scheduleArrayPrefix, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
      rw [← scheduleArrayPrefix_size msg n]
      rw [Array.getElem?_push_eq]
      simp

private theorem scheduleArrayPrefix_eq_fold (msg : Fin 16 → Word) :
    ∀ n,
      scheduleArrayPrefix msg n =
        (List.range n).foldl
          (fun acc offset =>
            acc.push
              (smallSigma1 acc[offset + 14]! +
               acc[offset + 9]! +
               smallSigma0 acc[offset + 1]! +
               acc[offset]!))
          (Array.ofFn msg)
  | 0 => by simp [scheduleArrayPrefix]
  | n + 1 => by
      simp [scheduleArrayPrefix, scheduleArrayPrefix_eq_fold msg n, List.range_succ, List.foldl_append]

private theorem expandSchedule_eq_scheduleArrayPrefix (msg : Fin 16 → Word) :
    expandSchedule (Array.ofFn msg) = scheduleArrayPrefix msg 48 := by
  rw [scheduleArrayPrefix_eq_fold]
  simpa [expandSchedule] using
    (List.idRun_forIn_yield_eq_foldl
      (l := List.range 48)
      (f := fun offset acc =>
        pure
          (acc.push
            (smallSigma1 acc[offset + 14]! +
             acc[offset + 9]! +
             smallSigma0 acc[offset + 1]! +
             acc[offset]!)))
      (init := Array.ofFn msg))

private theorem scheduleVectorPrefix_agrees (msg : Fin 16 → Word) :
    ∀ n, n ≤ 48 → ∀ i, ∀ hi : i < 16 + n, ∀ hi64 : i < 64,
      (scheduleVectorPrefix msg n)[i]'hi64 = (scheduleArrayPrefix msg n)[i]!
  | 0, _, i, hi, hi64 => by
      have hi' : i < 16 := by omega
      rw [show scheduleVectorPrefix msg 0 = scheduleVectorInit msg by rfl]
      dsimp [scheduleVectorInit, scheduleArrayPrefix]
      simp [hi']
  | n + 1, hn, i, hi, hi64 => by
      have hn' : n < 48 := by omega
      by_cases hnew : i = 16 + n
      · subst hnew
        have h14 := scheduleVectorPrefix_agrees msg n (by omega) (n + 14) (by omega) (by omega)
        have h9 := scheduleVectorPrefix_agrees msg n (by omega) (n + 9) (by omega) (by omega)
        have h1 := scheduleVectorPrefix_agrees msg n (by omega) (n + 1) (by omega) (by omega)
        have h0 := scheduleVectorPrefix_agrees msg n (by omega) n (by omega) (by omega)
        have hidx : 16 + n < 64 := by omega
        have ht2 : 16 + n - 2 = n + 14 := by omega
        have ht7 : 16 + n - 7 = n + 9 := by omega
        have ht15 : 16 + n - 15 = n + 1 := by omega
        have hv14 :
            (scheduleVectorPrefix msg n).get ⟨n + 14, by omega⟩ =
              (scheduleArrayPrefix msg n)[n + 14]! := by
          simpa using h14
        have hv9 :
            (scheduleVectorPrefix msg n).get ⟨n + 9, by omega⟩ =
              (scheduleArrayPrefix msg n)[n + 9]! := by
          simpa using h9
        have hv1 :
            (scheduleVectorPrefix msg n).get ⟨n + 1, by omega⟩ =
              (scheduleArrayPrefix msg n)[n + 1]! := by
          simpa using h1
        have hv0 :
            (scheduleVectorPrefix msg n).get ⟨n, by omega⟩ =
              (scheduleArrayPrefix msg n)[n]! := by
          simpa using h0
        calc
          (scheduleVectorPrefix msg (n + 1))[16 + n]'hidx
              =
                (smallSigma1 (scheduleArrayPrefix msg n)[n + 14]! +
                 (scheduleArrayPrefix msg n)[n + 9]! +
                 smallSigma0 (scheduleArrayPrefix msg n)[n + 1]! +
                 (scheduleArrayPrefix msg n)[n]!) := by
                  dsimp [scheduleVectorPrefix]
                  simp [hn', ht2, ht7, ht15]
                  rw [sigma1_eq_smallSigma1, sigma0_eq_smallSigma0]
                  rw [hv14, hv9, hv1, hv0]
          _ = (scheduleArrayPrefix msg (n + 1))[16 + n]! := by
                symm
                exact scheduleArrayPrefix_get_new msg n
      · have hold : i < 16 + n := by omega
        calc
          (scheduleVectorPrefix msg (n + 1))[i]'hi64 =
              (scheduleVectorPrefix msg n)[i]'(by omega) := by
                dsimp [scheduleVectorPrefix]
                let newWord :=
                  CryptoHash.SHA256.sigma1 ((scheduleVectorPrefix msg n).get ⟨16 + n - 2, by omega⟩) +
                  (scheduleVectorPrefix msg n).get ⟨16 + n - 7, by omega⟩ +
                  CryptoHash.SHA256.sigma0 ((scheduleVectorPrefix msg n).get ⟨16 + n - 15, by omega⟩) +
                  (scheduleVectorPrefix msg n).get ⟨n, by omega⟩
                have hset :
                    ((scheduleVectorPrefix msg n).set (16 + n) newWord (by omega))[i] =
                      (scheduleVectorPrefix msg n)[i] := by
                  simpa [newWord] using
                    (Vector.getElem_set_ne
                      (xs := scheduleVectorPrefix msg n)
                      (x := newWord)
                      (hi := by omega)
                      (hj := hi64)
                      (h := by omega))
                simpa [hn', newWord] using hset
          _ = (scheduleArrayPrefix msg n)[i]! :=
            scheduleVectorPrefix_agrees msg n (by omega) i hold (by omega)
          _ = (scheduleArrayPrefix msg (n + 1))[i]! := by
            symm
            exact scheduleArrayPrefix_get_lt msg n i hold

private abbrev CoreRoundAcc :=
  MProd Word
    (MProd Word
      (MProd Word
        (MProd Word
          (MProd Word
            (MProd Word
              (MProd Word Word))))))

private def coreRoundAccMk
    (a b c d e f g h : Word) : CoreRoundAcc :=
  MProd.mk a (MProd.mk b (MProd.mk c (MProd.mk d (MProd.mk e (MProd.mk f (MProd.mk g h))))))

private def coreRoundAccOfVector (state : Vector Word 8) : CoreRoundAcc :=
  coreRoundAccMk state[0] state[1] state[2] state[3] state[4] state[5] state[6] state[7]

private def coreRoundAccToVector (acc : CoreRoundAcc) : Vector Word 8 :=
  let a := MProd.fst acc
  let x1 := MProd.snd acc
  let b := MProd.fst x1
  let x2 := MProd.snd x1
  let c := MProd.fst x2
  let x3 := MProd.snd x2
  let d := MProd.fst x3
  let x4 := MProd.snd x3
  let e := MProd.fst x4
  let x5 := MProd.snd x4
  let f := MProd.fst x5
  let x6 := MProd.snd x5
  let g := MProd.fst x6
  let h := MProd.snd x6
  #v[a, b, c, d, e, f, g, h]

private theorem coreRoundAccToVector_ofVector (state : Vector Word 8) :
    coreRoundAccToVector (coreRoundAccOfVector state) = state := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [coreRoundAccToVector, coreRoundAccOfVector, coreRoundAccMk]

private def coreRoundAccRawStep (schedule : Vector Word 64)
    (acc : CoreRoundAcc) (i : Nat) (hi : i < 64) : CoreRoundAcc :=
  let a := MProd.fst acc
  let x1 := MProd.snd acc
  let b := MProd.fst x1
  let x2 := MProd.snd x1
  let c := MProd.fst x2
  let x3 := MProd.snd x2
  let d := MProd.fst x3
  let x4 := MProd.snd x3
  let e := MProd.fst x4
  let x5 := MProd.snd x4
  let f := MProd.fst x5
  let x6 := MProd.snd x5
  let g := MProd.fst x6
  let h := MProd.snd x6
  let temp1 := h + CryptoHash.SHA256.Sigma1 e + CryptoHash.SHA256.Ch e f g +
    (CryptoHash.SHA256.K.get ⟨i, hi⟩) + (schedule.get ⟨i, hi⟩)
  let temp2 := CryptoHash.SHA256.Sigma0 a + CryptoHash.SHA256.Maj a b c
  coreRoundAccMk (temp1 + temp2) a b c (d + temp1) e f g

private theorem coreRoundAccRawStep_eq_explicit
    (schedule : Vector Word 64) (acc : CoreRoundAcc) {a : Nat}
    (m : a ∈ List.range' 0 64 1) :
    coreRoundAccRawStep schedule acc a (by simpa [List.mem_range'_1] using m) =
      ⟨acc.snd.snd.snd.snd.snd.snd.snd + CryptoHash.SHA256.Sigma1 acc.snd.snd.snd.snd.fst +
            CryptoHash.SHA256.Ch acc.snd.snd.snd.snd.fst acc.snd.snd.snd.snd.snd.fst
              acc.snd.snd.snd.snd.snd.snd.fst +
          CryptoHash.SHA256.K[a]'(by simpa [List.mem_range'_1] using m) +
          schedule[a]'(by simpa [List.mem_range'_1] using m) +
            (CryptoHash.SHA256.Sigma0 acc.fst + CryptoHash.SHA256.Maj acc.fst acc.snd.fst acc.snd.snd.fst),
        acc.fst, acc.snd.fst, acc.snd.snd.fst,
        acc.snd.snd.snd.fst +
          (acc.snd.snd.snd.snd.snd.snd.snd + CryptoHash.SHA256.Sigma1 acc.snd.snd.snd.snd.fst +
              CryptoHash.SHA256.Ch acc.snd.snd.snd.snd.fst acc.snd.snd.snd.snd.snd.fst
                acc.snd.snd.snd.snd.snd.snd.fst +
            CryptoHash.SHA256.K[a]'(by simpa [List.mem_range'_1] using m) +
            schedule[a]'(by simpa [List.mem_range'_1] using m)),
        acc.snd.snd.snd.snd.fst,
        acc.snd.snd.snd.snd.snd.fst,
        acc.snd.snd.snd.snd.snd.snd.fst⟩ := by
  rfl

private theorem coreRoundAccRawStep_toVector
    (schedule : Vector Word 64) (acc : CoreRoundAcc) (i : Nat) (hi : i < 64) :
    coreRoundAccToVector (coreRoundAccRawStep schedule acc i hi) =
      coreRoundStep (coreRoundAccToVector acc)
        (CryptoHash.SHA256.K.get ⟨i, hi⟩) (schedule.get ⟨i, hi⟩) := by
  simp [coreRoundAccRawStep, coreRoundAccToVector, coreRoundStep, coreRoundAccMk]

private def coreRoundAccStepNat (schedule : Vector Word 64)
    (acc : CoreRoundAcc) (i : Nat) : CoreRoundAcc :=
  if hi : i < 64 then coreRoundAccRawStep schedule acc i hi else acc

private def coreCompressionVectorStepNat (schedule : Vector Word 64)
    (state : Vector Word 8) (i : Nat) : Vector Word 8 :=
  if hi : i < 64 then
    coreRoundStep state (CryptoHash.SHA256.K.get ⟨i, hi⟩) (schedule.get ⟨i, hi⟩)
  else
    state

private theorem coreRoundAccStepNat_toVector
    (schedule : Vector Word 64) (acc : CoreRoundAcc) (i : Nat) :
    coreRoundAccToVector (coreRoundAccStepNat schedule acc i) =
      coreCompressionVectorStepNat schedule (coreRoundAccToVector acc) i := by
  by_cases hi : i < 64
  · simp [coreRoundAccStepNat, coreCompressionVectorStepNat, hi,
      coreRoundAccRawStep_toVector]
  · simp [coreRoundAccStepNat, coreCompressionVectorStepNat, hi]

private def coreCompressLoopRaw
    (state : Vector Word 8) (schedule : Vector Word 64) : CoreRoundAcc :=
  (forIn' (m := Id) ([0:64]) (coreRoundAccOfVector state) fun i h acc =>
      let hi : i < 64 := by
        simpa using (Membership.mem.upper (r := ([0:64] : Std.Range)) h)
      do
        PUnit.unit
        ForInStep.yield (coreRoundAccRawStep schedule acc i hi)).run

private theorem coreCompressLoopRaw_eq_fold
    (state : Vector Word 8) (schedule : Vector Word 64) :
    coreCompressLoopRaw state schedule =
      (List.range 64).foldl (coreRoundAccStepNat schedule) (coreRoundAccOfVector state) := by
  unfold coreCompressLoopRaw
  rw [Std.Range.forIn'_eq_forIn'_range']
  have hcongr :
      forIn' (m := Id) (List.range' 0 64 1) (coreRoundAccOfVector state)
          (fun a h b =>
            let ha : a < 64 := by
              simpa [List.mem_range'_1] using h
            do
              PUnit.unit
              ForInStep.yield (coreRoundAccRawStep schedule b a ha)) =
      forIn' (m := Id) (List.range' 0 64 1) (coreRoundAccOfVector state)
          (fun a h b => ForInStep.yield (coreRoundAccStepNat schedule b a)) := by
    apply List.forIn'_congr (w := rfl) (hb := rfl)
    intro a m b
    have ha : a < 64 := by
      simpa [List.mem_range'_1] using m
    have hstep : coreRoundAccStepNat schedule b a = coreRoundAccRawStep schedule b a ha := by
      simp [coreRoundAccStepNat, ha]
    rw [hstep]
    rfl
  calc
    (forIn' (m := Id) (List.range' 0 64 1) (coreRoundAccOfVector state)
        (fun a h b =>
          let ha : a < 64 := by
            simpa [List.mem_range'_1] using h
          ForInStep.yield (coreRoundAccRawStep schedule b a ha))).run
        =
      (forIn' (m := Id) (List.range' 0 64 1) (coreRoundAccOfVector state)
          (fun a h b => ForInStep.yield (coreRoundAccStepNat schedule b a))).run := by
      exact congrArg Id.run hcongr
    _ = (List.range' 0 64 1).foldl (coreRoundAccStepNat schedule) (coreRoundAccOfVector state) := by
      simpa using
        (List.idRun_forIn'_yield_eq_foldl
          (l := List.range' 0 64 1)
          (f := fun a _ b => coreRoundAccStepNat schedule b a)
          (init := coreRoundAccOfVector state))
    _ = (List.range 64).foldl (coreRoundAccStepNat schedule) (coreRoundAccOfVector state) := by
      simp [List.range_eq_range']

private def coreCompressionVectorPrefix
    (startState : Vector Word 8) (schedule : Vector Word 64) (n : Nat) : Vector Word 8 :=
  (List.range n).foldl (coreCompressionVectorStepNat schedule) startState

private theorem coreRoundAccFold_toVector
    (startState : Vector Word 8) (schedule : Vector Word 64) :
    ∀ n, n ≤ 64 →
      coreRoundAccToVector
        ((List.range n).foldl (coreRoundAccStepNat schedule)
          (coreRoundAccOfVector startState)) =
        coreCompressionVectorPrefix startState schedule n
  | 0, _ => by
      simp [coreCompressionVectorPrefix, coreRoundAccToVector_ofVector]
  | n + 1, hn => by
      simp [coreCompressionVectorPrefix, List.range_succ, coreRoundAccStepNat_toVector,
        coreRoundAccFold_toVector startState schedule n (by omega)]

private theorem expandMessageSchedule_agrees
    (msg : Fin 16 → Word) (i : Fin 64) :
    (CryptoHash.SHA256.expandMessageSchedule (Vector.ofFn msg))[i] =
      (expandSchedule (Array.ofFn msg))[i.1]! := by
  rw [expandMessageSchedule_eq_scheduleVectorPrefix, expandSchedule_eq_scheduleArrayPrefix]
  simpa using
    (scheduleVectorPrefix_agrees msg 48 (by omega) i.1 (by omega) i.2)

private theorem coreCompressionVectorPrefix_eq_compressionPrefix
    (startState : WorkingVars) (scheduleVec : Vector Word 64) (scheduleArr : Array Word)
    (hschedule : ∀ i : Fin 64, scheduleVec[i] = scheduleArr[i.1]!) :
    ∀ n, n ≤ 64 →
      coreCompressionVectorPrefix (workingVarsToVector startState) scheduleVec n =
        workingVarsToVector ((compressionPrefix startState scheduleArr n).1)
  | 0, _ => by
      simp [coreCompressionVectorPrefix, compressionPrefix, workingVarsToVector]
  | n + 1, hn => by
      simp [coreCompressionVectorPrefix, List.range_succ, coreCompressionVectorStepNat,
        show n < 64 by omega]
      change
        coreRoundStep (coreCompressionVectorPrefix (workingVarsToVector startState) scheduleVec n)
            (CryptoHash.SHA256.K.get ⟨n, by omega⟩) (scheduleVec.get ⟨n, by omega⟩) =
          workingVarsToVector (compressionPrefix startState scheduleArr (n + 1)).1
      rw [coreCompressionVectorPrefix_eq_compressionPrefix startState scheduleVec scheduleArr
        hschedule n (by omega)]
      rw [compressionPrefix_succ]
      have hstep := coreRoundStep_eq_roundStep
        ((compressionPrefix startState scheduleArr n).1)
        (CryptoHash.SHA256.K.get ⟨n, by omega⟩) (scheduleVec.get ⟨n, by omega⟩)
      have hk : CryptoHash.SHA256.K.get ⟨n, by omega⟩ = sha256K[n]! := by
        simpa using (sha256K_eq_coreK ⟨n, by omega⟩).symm
      have hs : scheduleVec.get ⟨n, by omega⟩ = scheduleArr[n]! := by
        simpa using hschedule ⟨n, by omega⟩
      simpa [hk, hs, compressionPrefixStep] using hstep

private def vectorAdd8 (x y : Vector Word 8) : Vector Word 8 :=
  #v[x[0] + y[0], x[1] + y[1], x[2] + y[2], x[3] + y[3],
    x[4] + y[4], x[5] + y[5], x[6] + y[6], x[7] + y[7]]

private theorem vectorAdd8_eq_workingVarsToVector_add (x y : WorkingVars) :
    vectorAdd8 (workingVarsToVector x) (workingVarsToVector y) =
      workingVarsToVector (x.add y) := by
  simpa [vectorAdd8] using (workingVarsToVector_add x y).symm

private theorem vectorAdd8_coreRoundAccToVector
    (state : Vector Word 8) (acc : CoreRoundAcc) :
    vectorAdd8 state (coreRoundAccToVector acc) =
      #v[state[0] + MProd.fst acc,
        state[1] + MProd.fst (MProd.snd acc),
        state[2] + MProd.fst (MProd.snd (MProd.snd acc)),
        state[3] + MProd.fst (MProd.snd (MProd.snd (MProd.snd acc))),
        state[4] + MProd.fst (MProd.snd (MProd.snd (MProd.snd (MProd.snd acc)))),
        state[5] + MProd.fst (MProd.snd (MProd.snd (MProd.snd (MProd.snd (MProd.snd acc))))),
        state[6] + MProd.fst (MProd.snd (MProd.snd (MProd.snd (MProd.snd (MProd.snd (MProd.snd acc)))))),
        state[7] + MProd.snd (MProd.snd (MProd.snd (MProd.snd (MProd.snd (MProd.snd (MProd.snd acc))))))] := by
  simp [vectorAdd8, coreRoundAccToVector]

private theorem compressBlock_loop_eq_raw
    (state : Vector Word 8) (block : Vector Word 16) :
    (forIn' (m := Id) ([0:64]) (coreRoundAccOfVector state) fun a m b => do
        PUnit.unit
        ForInStep.yield
          ⟨b.snd.snd.snd.snd.snd.snd.snd + CryptoHash.SHA256.Sigma1 b.snd.snd.snd.snd.fst +
                CryptoHash.SHA256.Ch b.snd.snd.snd.snd.fst b.snd.snd.snd.snd.snd.fst
                  b.snd.snd.snd.snd.snd.snd.fst +
              CryptoHash.SHA256.K[a]'(by simpa using (Membership.mem.upper (r := ([0:64] : Std.Range)) m)) +
            (CryptoHash.SHA256.expandMessageSchedule block)[a]'(by
              simpa using (Membership.mem.upper (r := ([0:64] : Std.Range)) m)) +
            (CryptoHash.SHA256.Sigma0 b.fst + CryptoHash.SHA256.Maj b.fst b.snd.fst b.snd.snd.fst),
            b.fst, b.snd.fst, b.snd.snd.fst,
            b.snd.snd.snd.fst +
              (b.snd.snd.snd.snd.snd.snd.snd + CryptoHash.SHA256.Sigma1 b.snd.snd.snd.snd.fst +
                    CryptoHash.SHA256.Ch b.snd.snd.snd.snd.fst b.snd.snd.snd.snd.snd.fst
                      b.snd.snd.snd.snd.snd.snd.fst +
                  CryptoHash.SHA256.K[a]'(by simpa using (Membership.mem.upper (r := ([0:64] : Std.Range)) m)) +
                (CryptoHash.SHA256.expandMessageSchedule block)[a]'(by
                  simpa using (Membership.mem.upper (r := ([0:64] : Std.Range)) m))),
            b.snd.snd.snd.snd.fst, b.snd.snd.snd.snd.snd.fst, b.snd.snd.snd.snd.snd.snd.fst⟩).run =
      coreCompressLoopRaw state (CryptoHash.SHA256.expandMessageSchedule block) := by
  rw [Std.Range.forIn'_eq_forIn'_range']
  unfold coreCompressLoopRaw
  rw [Std.Range.forIn'_eq_forIn'_range']
  apply congrArg Id.run
  apply List.forIn'_congr (w := rfl) (hb := rfl)
  intro a m b
  have hm : a ∈ List.range' 0 64 1 := m
  have hlt : a < 64 := by
    simpa [List.mem_range'_1] using hm
  have hbody :
      (do
        PUnit.unit
        ForInStep.yield
          (coreRoundAccRawStep (CryptoHash.SHA256.expandMessageSchedule block) b a hlt) :
        Id (ForInStep CoreRoundAcc)) =
      (do
        PUnit.unit
        ForInStep.yield
          ⟨b.snd.snd.snd.snd.snd.snd.snd + CryptoHash.SHA256.Sigma1 b.snd.snd.snd.snd.fst +
                CryptoHash.SHA256.Ch b.snd.snd.snd.snd.fst b.snd.snd.snd.snd.snd.fst
                  b.snd.snd.snd.snd.snd.snd.fst +
              CryptoHash.SHA256.K[a]'hlt +
              (CryptoHash.SHA256.expandMessageSchedule block)[a]'hlt +
              (CryptoHash.SHA256.Sigma0 b.fst + CryptoHash.SHA256.Maj b.fst b.snd.fst b.snd.snd.fst),
            b.fst, b.snd.fst, b.snd.snd.fst,
            b.snd.snd.snd.fst +
              (b.snd.snd.snd.snd.snd.snd.snd + CryptoHash.SHA256.Sigma1 b.snd.snd.snd.snd.fst +
                  CryptoHash.SHA256.Ch b.snd.snd.snd.snd.fst b.snd.snd.snd.snd.snd.fst
                    b.snd.snd.snd.snd.snd.snd.fst +
                CryptoHash.SHA256.K[a]'hlt +
                (CryptoHash.SHA256.expandMessageSchedule block)[a]'hlt),
            b.snd.snd.snd.snd.fst, b.snd.snd.snd.snd.snd.fst, b.snd.snd.snd.snd.snd.snd.fst⟩ :
        Id (ForInStep CoreRoundAcc)) := by
    rw [coreRoundAccRawStep_eq_explicit
      (schedule := CryptoHash.SHA256.expandMessageSchedule block) (acc := b) (m := hm)]
  simpa [hlt] using hbody.symm

private theorem compressBlock_eq_raw
    (state : Vector Word 8) (block : Vector Word 16) :
    CryptoHash.SHA256.compressBlock state block =
      let schedule := CryptoHash.SHA256.expandMessageSchedule block
      let finalAcc := coreCompressLoopRaw state schedule
      #v[state[0] + MProd.fst finalAcc,
        state[1] + MProd.fst (MProd.snd finalAcc),
        state[2] + MProd.fst (MProd.snd (MProd.snd finalAcc)),
        state[3] + MProd.fst (MProd.snd (MProd.snd (MProd.snd finalAcc))),
        state[4] + MProd.fst (MProd.snd (MProd.snd (MProd.snd (MProd.snd finalAcc)))),
        state[5] + MProd.fst (MProd.snd (MProd.snd (MProd.snd (MProd.snd (MProd.snd finalAcc))))),
        state[6] + MProd.fst (MProd.snd (MProd.snd (MProd.snd (MProd.snd (MProd.snd (MProd.snd finalAcc)))))),
        state[7] + MProd.snd (MProd.snd (MProd.snd (MProd.snd (MProd.snd (MProd.snd (MProd.snd finalAcc))))))] := by
  unfold CryptoHash.SHA256.compressBlock
  change
    #v[state[0] +
        (forIn' (m := Id) ([0:64]) (coreRoundAccOfVector state) fun a m b => do
          PUnit.unit
          ForInStep.yield
            ⟨b.snd.snd.snd.snd.snd.snd.snd + CryptoHash.SHA256.Sigma1 b.snd.snd.snd.snd.fst +
                  CryptoHash.SHA256.Ch b.snd.snd.snd.snd.fst b.snd.snd.snd.snd.snd.fst
                    b.snd.snd.snd.snd.snd.snd.fst +
                CryptoHash.SHA256.K[a]'(by simpa using (Membership.mem.upper (r := ([0:64] : Std.Range)) m)) +
                (CryptoHash.SHA256.expandMessageSchedule block)[a]'(by
                  simpa using (Membership.mem.upper (r := ([0:64] : Std.Range)) m)) +
                (CryptoHash.SHA256.Sigma0 b.fst + CryptoHash.SHA256.Maj b.fst b.snd.fst b.snd.snd.fst),
              b.fst, b.snd.fst, b.snd.snd.fst,
              b.snd.snd.snd.fst +
                (b.snd.snd.snd.snd.snd.snd.snd + CryptoHash.SHA256.Sigma1 b.snd.snd.snd.snd.fst +
                      CryptoHash.SHA256.Ch b.snd.snd.snd.snd.fst b.snd.snd.snd.snd.snd.fst
                        b.snd.snd.snd.snd.snd.snd.fst +
                    CryptoHash.SHA256.K[a]'(by simpa using (Membership.mem.upper (r := ([0:64] : Std.Range)) m)) +
                    (CryptoHash.SHA256.expandMessageSchedule block)[a]'(by
                      simpa using (Membership.mem.upper (r := ([0:64] : Std.Range)) m))),
              b.snd.snd.snd.snd.fst, b.snd.snd.snd.snd.snd.fst, b.snd.snd.snd.snd.snd.snd.fst⟩).run.fst,
      state[1] +
        (forIn' (m := Id) ([0:64]) (coreRoundAccOfVector state) fun a m b => do
          PUnit.unit
          ForInStep.yield
            ⟨b.snd.snd.snd.snd.snd.snd.snd + CryptoHash.SHA256.Sigma1 b.snd.snd.snd.snd.fst +
                  CryptoHash.SHA256.Ch b.snd.snd.snd.snd.fst b.snd.snd.snd.snd.snd.fst
                    b.snd.snd.snd.snd.snd.snd.fst +
                CryptoHash.SHA256.K[a]'(by simpa using (Membership.mem.upper (r := ([0:64] : Std.Range)) m)) +
                (CryptoHash.SHA256.expandMessageSchedule block)[a]'(by
                  simpa using (Membership.mem.upper (r := ([0:64] : Std.Range)) m)) +
                (CryptoHash.SHA256.Sigma0 b.fst + CryptoHash.SHA256.Maj b.fst b.snd.fst b.snd.snd.fst),
              b.fst, b.snd.fst, b.snd.snd.fst,
              b.snd.snd.snd.fst +
                (b.snd.snd.snd.snd.snd.snd.snd + CryptoHash.SHA256.Sigma1 b.snd.snd.snd.snd.fst +
                      CryptoHash.SHA256.Ch b.snd.snd.snd.snd.fst b.snd.snd.snd.snd.snd.fst
                        b.snd.snd.snd.snd.snd.snd.fst +
                    CryptoHash.SHA256.K[a]'(by simpa using (Membership.mem.upper (r := ([0:64] : Std.Range)) m)) +
                    (CryptoHash.SHA256.expandMessageSchedule block)[a]'(by
                      simpa using (Membership.mem.upper (r := ([0:64] : Std.Range)) m))),
              b.snd.snd.snd.snd.fst, b.snd.snd.snd.snd.snd.fst, b.snd.snd.snd.snd.snd.snd.fst⟩).run.snd.fst,
      state[2] + (coreCompressLoopRaw state (CryptoHash.SHA256.expandMessageSchedule block)).snd.snd.fst,
      state[3] + (coreCompressLoopRaw state (CryptoHash.SHA256.expandMessageSchedule block)).snd.snd.snd.fst,
      state[4] + (coreCompressLoopRaw state (CryptoHash.SHA256.expandMessageSchedule block)).snd.snd.snd.snd.fst,
      state[5] + (coreCompressLoopRaw state (CryptoHash.SHA256.expandMessageSchedule block)).snd.snd.snd.snd.snd.fst,
      state[6] + (coreCompressLoopRaw state (CryptoHash.SHA256.expandMessageSchedule block)).snd.snd.snd.snd.snd.snd.fst,
      state[7] + (coreCompressLoopRaw state (CryptoHash.SHA256.expandMessageSchedule block)).snd.snd.snd.snd.snd.snd.snd] =
    #v[state[0] + (coreCompressLoopRaw state (CryptoHash.SHA256.expandMessageSchedule block)).fst,
      state[1] + (coreCompressLoopRaw state (CryptoHash.SHA256.expandMessageSchedule block)).snd.fst,
      state[2] + (coreCompressLoopRaw state (CryptoHash.SHA256.expandMessageSchedule block)).snd.snd.fst,
      state[3] + (coreCompressLoopRaw state (CryptoHash.SHA256.expandMessageSchedule block)).snd.snd.snd.fst,
      state[4] + (coreCompressLoopRaw state (CryptoHash.SHA256.expandMessageSchedule block)).snd.snd.snd.snd.fst,
      state[5] + (coreCompressLoopRaw state (CryptoHash.SHA256.expandMessageSchedule block)).snd.snd.snd.snd.snd.fst,
      state[6] + (coreCompressLoopRaw state (CryptoHash.SHA256.expandMessageSchedule block)).snd.snd.snd.snd.snd.snd.fst,
      state[7] + (coreCompressLoopRaw state (CryptoHash.SHA256.expandMessageSchedule block)).snd.snd.snd.snd.snd.snd.snd]
  have hloop := compressBlock_loop_eq_raw state block
  have hloopRange :
      (forIn' (m := Id) (List.range' 0 64 1) (coreRoundAccOfVector state) fun a m b => do
          PUnit.unit
          ForInStep.yield
              ⟨b.snd.snd.snd.snd.snd.snd.snd + CryptoHash.SHA256.Sigma1 b.snd.snd.snd.snd.fst +
                        CryptoHash.SHA256.Ch b.snd.snd.snd.snd.fst b.snd.snd.snd.snd.snd.fst
                          b.snd.snd.snd.snd.snd.snd.fst +
                      CryptoHash.SHA256.K[a]'(by simpa [List.mem_range'_1] using m) +
                    (CryptoHash.SHA256.expandMessageSchedule block)[a]'(by
                      simpa [List.mem_range'_1] using m) +
                  (CryptoHash.SHA256.Sigma0 b.fst + CryptoHash.SHA256.Maj b.fst b.snd.fst b.snd.snd.fst),
                b.fst, b.snd.fst, b.snd.snd.fst,
                b.snd.snd.snd.fst +
                  (b.snd.snd.snd.snd.snd.snd.snd + CryptoHash.SHA256.Sigma1 b.snd.snd.snd.snd.fst +
                        CryptoHash.SHA256.Ch b.snd.snd.snd.snd.fst b.snd.snd.snd.snd.snd.fst
                          b.snd.snd.snd.snd.snd.snd.fst +
                      CryptoHash.SHA256.K[a]'(by simpa [List.mem_range'_1] using m) +
                    (CryptoHash.SHA256.expandMessageSchedule block)[a]'(by
                      simpa [List.mem_range'_1] using m)),
                b.snd.snd.snd.snd.fst, b.snd.snd.snd.snd.snd.fst, b.snd.snd.snd.snd.snd.snd.fst⟩).run =
        coreCompressLoopRaw state (CryptoHash.SHA256.expandMessageSchedule block) := by
    simpa [Std.Range.forIn'_eq_forIn'_range'] using hloop
  have h0 := congrArg (fun finalAcc => state[0] + finalAcc.fst) hloopRange
  have h1 := congrArg (fun finalAcc => state[1] + finalAcc.snd.fst) hloopRange
  apply Vector.ext
  intro i hi
  interval_cases i <;> simpa [h0, h1]

theorem compressBlock_eq_sha256CompressWords_vector
    (initialState : WorkingVars) (messageWords : Fin 16 → Word) :
    CryptoHash.SHA256.compressBlock
        (workingVarsToVector initialState) (Vector.ofFn messageWords) =
      workingVarsToVector
        (sha256CompressWords initialState (Array.ofFn messageWords)) := by
  unfold sha256CompressWords
  rw [compressBlock_eq_raw]
  dsimp
  rw [← vectorAdd8_coreRoundAccToVector]
  have hloop :
      coreRoundAccToVector
          (coreCompressLoopRaw (workingVarsToVector initialState)
            (CryptoHash.SHA256.expandMessageSchedule (Vector.ofFn messageWords))) =
        workingVarsToVector
          ((compressionPrefix initialState (expandSchedule (Array.ofFn messageWords)) 64).1) := by
    rw [coreCompressLoopRaw_eq_fold]
    rw [coreRoundAccFold_toVector (workingVarsToVector initialState)
      (CryptoHash.SHA256.expandMessageSchedule (Vector.ofFn messageWords)) 64 (by omega)]
    exact coreCompressionVectorPrefix_eq_compressionPrefix
      initialState
      (CryptoHash.SHA256.expandMessageSchedule (Vector.ofFn messageWords))
      (expandSchedule (Array.ofFn messageWords))
      (expandMessageSchedule_agrees messageWords) 64 (by omega)
  rw [hloop]
  rw [compressionTrace_get initialState (expandSchedule (Array.ofFn messageWords)) (n := 64) (by omega)]
  exact vectorAdd8_eq_workingVarsToVector_add
    initialState ((compressionPrefix initialState (expandSchedule (Array.ofFn messageWords)) 64).1)

theorem sha256CompressWords_eq_compressBlock
    (initialState : WorkingVars) (messageWords : Fin 16 → Word) :
    sha256CompressWords initialState (Array.ofFn messageWords) =
      vectorToWorkingVars
        (CryptoHash.SHA256.compressBlock
          (workingVarsToVector initialState) (Vector.ofFn messageWords)) := by
  symm
  simpa [vectorToWorkingVars_workingVarsToVector] using
    congrArg vectorToWorkingVars
      (compressBlock_eq_sha256CompressWords_vector initialState messageWords)

private theorem workingVarsToVector_vectorToWorkingVars
    (v : Vector UInt32 8) :
    workingVarsToVector (vectorToWorkingVars v) = v := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [workingVarsToVector, vectorToWorkingVars]

private theorem byte_pair_val_eq (lo hi : FBB)
    (hlo : lo.val < 2 ^ 8) (hhi : hi.val < 2 ^ 8) :
    (lo + hi * 2 ^ 8).val = lo.val + hi.val * 2 ^ 8 := by
  have hlo256 : lo.val < 256 := by simpa using hlo
  have hhi256 : hi.val < 256 := by simpa using hhi
  have h256 : ((256 : FBB)).val = 256 := by
    exact ZMod.val_natCast_of_lt (by decide : 256 < BB_prime)
  have hmul_lt_nat : hi.val * 256 < BB_prime := by
    have hmul_le : hi.val * 256 ≤ 255 * 256 := by omega
    exact lt_of_le_of_lt hmul_le (by norm_num)
  have hmul : (hi * (256 : FBB)).val = hi.val * 256 := by
    rw [Fin.val_mul]
    rw [h256, Nat.mod_eq_of_lt hmul_lt_nat]
  have hadd_nat : lo.val + hi.val * 256 < BB_prime := by
    have hsum_le : lo.val + hi.val * 256 ≤ 255 + 255 * 256 := by omega
    exact lt_of_le_of_lt hsum_le (by norm_num)
  have hadd : lo.val + (hi * (256 : FBB)).val < BB_prime := by
    simpa [hmul] using hadd_nat
  have hadd' : (lo + hi * (256 : FBB)).val = lo.val + (hi * (256 : FBB)).val := by
    rw [Fin.val_add, Nat.mod_eq_of_lt hadd]
  calc
    (lo + hi * 2 ^ 8).val = (lo + hi * (256 : FBB)).val := by norm_num
    _ = lo.val + (hi * (256 : FBB)).val := hadd'
    _ = lo.val + hi.val * 256 := by rw [hmul]
    _ = lo.val + hi.val * 2 ^ 8 := by norm_num

private theorem explicit_prev_state_word_eq
    {CMain : Type → Type → Type} {ExtF : Type}
    [Field ExtF] [Circuit FBB ExtF CMain]
    (mainAir : CMain FBB ExtF) (row : ℕ)
    (word : Fin 8)
    (hPrevByteBound : ∀ i : Fin 32, (prev_state_byte mainAir i.1 row).val < 2 ^ 8) :
    UInt32.ofNat
      ((prev_state_byte mainAir (4 * word.1) row).val +
       (prev_state_byte mainAir (4 * word.1 + 1) row).val * 2 ^ 8 +
       (prev_state_byte mainAir (4 * word.1 + 2) row).val * 2 ^ 16 +
       (prev_state_byte mainAir (4 * word.1 + 3) row).val * 2 ^ 24) =
      rowPrevStateWord mainAir row word := by
  have h01 :
      (prev_state_byte mainAir (4 * word.1) row +
          prev_state_byte mainAir (4 * word.1 + 1) row * 2 ^ 8).val =
        (prev_state_byte mainAir (4 * word.1) row).val +
          (prev_state_byte mainAir (4 * word.1 + 1) row).val * 2 ^ 8 := by
    simpa using
      byte_pair_val_eq
        (prev_state_byte mainAir (4 * word.1) row)
        (prev_state_byte mainAir (4 * word.1 + 1) row)
        (hPrevByteBound ⟨4 * word.1, by omega⟩)
        (hPrevByteBound ⟨4 * word.1 + 1, by omega⟩)
  have h23 :
      (prev_state_byte mainAir (4 * word.1 + 2) row +
          prev_state_byte mainAir (4 * word.1 + 3) row * 2 ^ 8).val =
        (prev_state_byte mainAir (4 * word.1 + 2) row).val +
          (prev_state_byte mainAir (4 * word.1 + 3) row).val * 2 ^ 8 := by
    simpa using
      byte_pair_val_eq
        (prev_state_byte mainAir (4 * word.1 + 2) row)
        (prev_state_byte mainAir (4 * word.1 + 3) row)
        (hPrevByteBound ⟨4 * word.1 + 2, by omega⟩)
        (hPrevByteBound ⟨4 * word.1 + 3, by omega⟩)
  have hpair0 :
      (prev_state_u16 mainAir (2 * word.1) row).val =
        (prev_state_byte mainAir (4 * word.1) row).val +
          (prev_state_byte mainAir (4 * word.1 + 1) row).val * 2 ^ 8 := by
    have hidx0 : 2 * (2 * word.1) = 4 * word.1 := by omega
    have hidx1 : 2 * (2 * word.1) + 1 = 4 * word.1 + 1 := by omega
    simpa [prev_state_u16, hidx0, hidx1] using h01
  have hpair1 :
      (prev_state_u16 mainAir (2 * word.1 + 1) row).val =
        (prev_state_byte mainAir (4 * word.1 + 2) row).val +
          (prev_state_byte mainAir (4 * word.1 + 3) row).val * 2 ^ 8 := by
    have hidx2 : 2 * (2 * word.1 + 1) = 4 * word.1 + 2 := by omega
    have hidx3 : 2 * (2 * word.1 + 1) + 1 = 4 * word.1 + 3 := by omega
    simpa [prev_state_u16, hidx2, hidx3] using h23
  unfold rowPrevStateWord
  rw [hpair0, hpair1]
  congr 1
  omega

private theorem workingVarsToVector_rowPrevState_get
    {CMain : Type → Type → Type} {ExtF : Type}
    [Field ExtF] [Circuit FBB ExtF CMain]
    (mainAir : CMain FBB ExtF) (row : ℕ) (i : ℕ) (hi : i < 8) :
    (workingVarsToVector (rowPrevState mainAir row))[i] =
      rowPrevStateWord mainAir row ⟨i, hi⟩ := by
  interval_cases i <;> rfl

private theorem explicit_prev_state_vector_get
    {CMain : Type → Type → Type} {ExtF : Type}
    [Field ExtF] [Circuit FBB ExtF CMain]
    (mainAir : CMain FBB ExtF) (row : ℕ) (i : ℕ) (hi : i < 8) :
    (Vector.ofFn (fun w : Fin 8 =>
      UInt32.ofNat
        ((prev_state_byte mainAir (4 * w.1) row).val +
         (prev_state_byte mainAir (4 * w.1 + 1) row).val * 2 ^ 8 +
         (prev_state_byte mainAir (4 * w.1 + 2) row).val * 2 ^ 16 +
         (prev_state_byte mainAir (4 * w.1 + 3) row).val * 2 ^ 24)))[i] =
      UInt32.ofNat
        ((prev_state_byte mainAir (4 * i) row).val +
         (prev_state_byte mainAir (4 * i + 1) row).val * 2 ^ 8 +
         (prev_state_byte mainAir (4 * i + 2) row).val * 2 ^ 16 +
         (prev_state_byte mainAir (4 * i + 3) row).val * 2 ^ 24) := by
  simp

private theorem explicit_prev_state_words_eq
    {CMain : Type → Type → Type} {ExtF : Type}
    [Field ExtF] [Circuit FBB ExtF CMain]
    (mainAir : CMain FBB ExtF) (row : ℕ)
    (hPrevByteBound : ∀ i : Fin 32, (prev_state_byte mainAir i.1 row).val < 2 ^ 8) :
    (Vector.ofFn (fun w : Fin 8 =>
      UInt32.ofNat
        ((prev_state_byte mainAir (4 * w.1) row).val +
         (prev_state_byte mainAir (4 * w.1 + 1) row).val * 2 ^ 8 +
         (prev_state_byte mainAir (4 * w.1 + 2) row).val * 2 ^ 16 +
         (prev_state_byte mainAir (4 * w.1 + 3) row).val * 2 ^ 24))) =
      workingVarsToVector (rowPrevState mainAir row) := by
  apply Vector.ext
  intro i hi
  rw [explicit_prev_state_vector_get mainAir row i hi]
  rw [workingVarsToVector_rowPrevState_get mainAir row i hi]
  exact explicit_prev_state_word_eq mainAir row ⟨i, hi⟩ hPrevByteBound

private theorem explicit_message_words_eq
    {CMain : Type → Type → Type} {ExtF : Type}
    [Field ExtF] [Circuit FBB ExtF CMain]
    (mainAir : CMain FBB ExtF) (row : ℕ) :
    (Vector.ofFn (fun w : Fin 16 =>
      UInt32.ofNat
        ((message_byte mainAir (4 * w.1) row).val * 2 ^ 24 +
         (message_byte mainAir (4 * w.1 + 1) row).val * 2 ^ 16 +
         (message_byte mainAir (4 * w.1 + 2) row).val * 2 ^ 8 +
         (message_byte mainAir (4 * w.1 + 3) row).val))) =
      Vector.ofFn (rowMessageWord mainAir row) := by
  apply Vector.ext
  intro i hi
  simp [rowMessageWord, beFieldBytesToWord, beFieldBytesNat]

private theorem explicit_output_words_eq
    {CMain : Type → Type → Type} {ExtF : Type}
    [Field ExtF] [Circuit FBB ExtF CMain]
    (mainAir : CMain FBB ExtF) (row : ℕ) :
    (Vector.ofFn (fun w : Fin 8 =>
      UInt32.ofNat
        ((new_state_byte mainAir (4 * w.1) row).val +
         (new_state_byte mainAir (4 * w.1 + 1) row).val * 2 ^ 8 +
         (new_state_byte mainAir (4 * w.1 + 2) row).val * 2 ^ 16 +
         (new_state_byte mainAir (4 * w.1 + 3) row).val * 2 ^ 24))) =
      workingVarsToVector (rowNewState mainAir row) := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [workingVarsToVector, rowNewState, rowNewStateWord]

private theorem blockWrapperState_new_state_bytes_get
    {CBlock : Type → Type → Type} {ExtF : Type}
    [Field ExtF] [Circuit FBB ExtF CBlock]
    (blockAir : CBlock FBB ExtF) (row : ℕ) (word : Fin 8) (byte : Fin 4) :
    (Sha2BlockHasherVmAir_sha256.constraints.wrapperStateEntry blockAir row).new_state_bytes.get
      ⟨4 * word.1 + byte.1, by omega⟩ =
        Sha2BlockHasherVmAir_sha256.constraints.final_hash blockAir word.1 byte.1 row := by
  fin_cases word <;> fin_cases byte <;>
    simp [Sha2BlockHasherVmAir_sha256.constraints.wrapperStateEntry]

private theorem new_state_byte_eq_block_final_hash_of_columns
    {CMain CBlock : Type → Type → Type} {ExtF : Type}
    [Field ExtF] [Circuit FBB ExtF CMain] [Circuit FBB ExtF CBlock]
    (mainAir : CMain FBB ExtF) (blockAir : CBlock FBB ExtF) (row start : ℕ)
    (hcols : rowBlockColumnAgreementSpec mainAir blockAir row start)
    (i : Fin 32) :
    new_state_byte mainAir i.1 row =
      Sha2BlockHasherVmAir_sha256.constraints.final_hash blockAir (i.1 / 4) (i.1 % 4) (start + 16) := by
  rcases hcols with ⟨_, hnew, _, _, _, _⟩
  let word : Fin 8 := ⟨i.1 / 4, by omega⟩
  let byte : Fin 4 := ⟨i.1 % 4, by omega⟩
  have hsplit : 4 * word.1 + byte.1 = i.1 := by
    dsimp [word, byte]
    omega
  calc
    new_state_byte mainAir i.1 row =
        (Sha2BlockHasherVmAir_sha256.constraints.wrapperStateEntry blockAir (start + 16)).new_state_bytes.get i :=
      hnew i
    _ =
        (Sha2BlockHasherVmAir_sha256.constraints.wrapperStateEntry blockAir (start + 16)).new_state_bytes.get
          ⟨4 * word.1 + byte.1, by omega⟩ := by
      simp [hsplit]
    _ = Sha2BlockHasherVmAir_sha256.constraints.final_hash blockAir word.1 byte.1 (start + 16) := by
      simpa using blockWrapperState_new_state_bytes_get blockAir (start + 16) word byte
    _ = Sha2BlockHasherVmAir_sha256.constraints.final_hash blockAir (i.1 / 4) (i.1 % 4) (start + 16) := by
      rfl

private theorem output_byte_bounds_of_soundness
    {CMain CBlock : Type → Type → Type} {ExtF : Type}
    [Field ExtF] [Circuit FBB ExtF CMain] [Circuit FBB ExtF CBlock]
    (mainAir : CMain FBB ExtF)
    (blockAir : CBlock FBB ExtF)
    (row start : ℕ)
    (hcols : rowBlockColumnAgreementSpec mainAir blockAir row start)
    (hwindow : blockWindowSupported blockAir start)
    (hrot : rotation_consistent blockAir)
    (hshape : blockWindowHasShape blockAir start)
    (hc : blockHasherConstraints blockAir)
    (hBlockBitwiseWf : ∀ mult a b c op,
      (mult, [a, b, c, op]) ∈ Circuit.buses blockAir BitwiseBus →
      mult = 1 → a.val < 2 ^ 8 ∧ b.val < 2 ^ 8) :
    ∀ i : Fin 32, (new_state_byte mainAir i.1 row).val < 2 ^ 8 := by
  have h_wf_prev :
      Sha2BlockHasherVmAir_sha256.constraints.bitwise_lookup_send_properties blockAir (start + 15) := by
    refine bitwise_lookup_send_properties_of_bus_wf blockAir (start + 15) ?_ ?_ hBlockBitwiseWf
    · dsimp [blockWindowSupported] at hwindow
      omega
    · exact constrain_interactions_of_extraction blockAir hc.constrain_interactions
  rcases hshape with ⟨_, _, _, _, hdigest⟩
  intro i
  have hEq :=
    new_state_byte_eq_block_final_hash_of_columns mainAir blockAir row start hcols i
  have hrange :
      (Sha2BlockHasherVmAir_sha256.constraints.final_hash blockAir (i.1 / 4) (i.1 % 4) (start + 16)).val <
        2 ^ 8 := by
    have hrange256 :=
      digest_final_hash_byte_range_of_bus blockAir (start + 16) (i.1 / 4) (i.1 % 4)
        (by omega) (by omega)
        (by
          dsimp [blockWindowSupported] at hwindow
          omega)
        hrot hdigest h_wf_prev
    simpa using hrange256
  simpa [hEq] using hrange

/-- Explicit output equivalence for one SHA-256 `compress` row, with the
written output bytes proved to be genuine bytes and the input bytes for `H`
and `M` assumed to be genuine bytes. -/
theorem equiv_SHA256_COMPRESS_word_explicit_bounded
    {CMain CBlock : Type → Type → Type} {ExtF : Type}
    [Field ExtF] [Circuit FBB ExtF CMain] [Circuit FBB ExtF CBlock]
    (mainAir : CMain FBB ExtF)
    (blockAir : CBlock FBB ExtF)
    (row : ℕ)
    (hMainRow : row ≤ Circuit.last_row mainAir)
    (hMainEnabled : is_enabled mainAir row = 1)
    (hMainTraceFits : Circuit.last_row mainAir + 1 < BB_prime)
    (hMainConstraints : mainTraceConstraints mainAir)
    (hSharedRawPerm : InteractionList.is_balanced
      (Circuit.buses mainAir Sha2MainWrapperBus ++ Circuit.buses blockAir Sha2WrapperBus))
    (hMainRot :
      (∀ column row', row' < Circuit.last_row mainAir →
        Circuit.main mainAir (id := 0) (column := column) (row := row') (rotation := 1) =
          Circuit.main mainAir (id := 0) (column := column) (row := row' + 1) (rotation := 0)) ∧
      (∀ column,
        Circuit.main mainAir (id := 0) (column := column)
            (row := Circuit.last_row mainAir) (rotation := 1) =
          Circuit.main mainAir (id := 0) (column := column) (row := 0) (rotation := 0)))
    (hBlockRot :
      (∀ column row', row' < Circuit.last_row blockAir →
        Circuit.main blockAir (id := 0) (column := column) (row := row') (rotation := 1) =
          Circuit.main blockAir (id := 0) (column := column) (row := row' + 1) (rotation := 0)) ∧
      (∀ column,
        Circuit.main blockAir (id := 0) (column := column)
            (row := Circuit.last_row blockAir) (rotation := 1) =
          Circuit.main blockAir (id := 0) (column := column) (row := 0) (rotation := 0)))
    (hBlockConstraints : blockHasherConstraints blockAir)
    (hBlockRawPerm : InteractionList.is_balanced (Circuit.buses blockAir Sha2PrivateBus))
    (hBlockTraceFits : Circuit.last_row blockAir + 1 < BB_prime)
    (hBlockBitwiseWf : ∀ mult a b c op,
      (mult, [a, b, c, op]) ∈ Circuit.buses blockAir BitwiseBus →
      mult = 1 → a.val < 2 ^ 8 ∧ b.val < 2 ^ 8)
    (hPrevByteBound : ∀ i : Fin 32,
      (prev_state_byte mainAir i.1 row).val < 2 ^ 8) :
    let H : Vector UInt32 8 :=
      Vector.ofFn (fun w : Fin 8 =>
        UInt32.ofNat
          ((prev_state_byte mainAir (4 * w.1) row).val +
           (prev_state_byte mainAir (4 * w.1 + 1) row).val * 2 ^ 8 +
           (prev_state_byte mainAir (4 * w.1 + 2) row).val * 2 ^ 16 +
           (prev_state_byte mainAir (4 * w.1 + 3) row).val * 2 ^ 24))
    let M : Vector UInt32 16 :=
      Vector.ofFn (fun w : Fin 16 =>
        UInt32.ofNat
          ((message_byte mainAir (4 * w.1) row).val * 2 ^ 24 +
           (message_byte mainAir (4 * w.1 + 1) row).val * 2 ^ 16 +
           (message_byte mainAir (4 * w.1 + 2) row).val * 2 ^ 8 +
           (message_byte mainAir (4 * w.1 + 3) row).val))
    let outWords : Vector UInt32 8 :=
      Vector.ofFn (fun w : Fin 8 =>
        UInt32.ofNat
          ((new_state_byte mainAir (4 * w.1) row).val +
           (new_state_byte mainAir (4 * w.1 + 1) row).val * 2 ^ 8 +
           (new_state_byte mainAir (4 * w.1 + 2) row).val * 2 ^ 16 +
           (new_state_byte mainAir (4 * w.1 + 3) row).val * 2 ^ 24))
    (∀ i : Fin 32,
      (new_state_byte mainAir i.1 row).val < 2 ^ 8) ∧
    outWords = CryptoHash.SHA256.compressBlock H M := by
  dsimp
  have hMainRot' : rotation_consistent mainAir := hMainRot
  have hBlockRot' : rotation_consistent blockAir := hBlockRot
  have hSharedOld : sharedWrapperRawPermutationSemantics mainAir blockAir := by
    simp only [sharedWrapperRawPermutationSemantics, sharedWrapperTraceEntries]
    rw [← Sha2MainAir_sha256.constraints.wrapperBus_trace_of_extraction mainAir
          hMainConstraints.constrain_interactions,
      ← Sha2BlockHasherVmAir_sha256.constraints.wrapperBus_trace_of_extraction blockAir
          hBlockConstraints.constrain_interactions]
    exact hSharedRawPerm
  have hBlockOld : privateBusRawPermutationSemantics blockAir := by
    simp only [privateBusRawPermutationSemantics, privateBusTraceEntries]
    rw [← Sha2BlockHasherVmAir_sha256.constraints.privateBus_trace_of_extraction blockAir
          hBlockConstraints.constrain_interactions]
    exact hBlockRawPerm
  have hMainTraceFitsField : traceLengthFitsField mainAir := hMainTraceFits
  have hBlockTraceFitsField : traceLengthFitsField blockAir := hBlockTraceFits
  rcases exists_start_of_sharedWrapperRawPermutationSemantics
      mainAir blockAir row
      hMainConstraints hMainEnabled hMainRot' hMainTraceFitsField hMainRow
      hBlockRot' hBlockConstraints
      hSharedOld hBlockTraceFitsField with
      ⟨start, hstart, hsel, hpayload⟩
  have hmain := wrapperPayload_of_row mainAir row
  have hword :=
    compressWordEquivSpec_of_shared_payload_and_block_soundness
      mainAir blockAir row start hmain hpayload
      hstart hsel hBlockRot' hBlockConstraints hBlockOld hBlockTraceFitsField hBlockBitwiseWf
  have hboundary :=
    blockCompressionBoundarySpec_of_soundness_assumptions
      blockAir start hstart hsel hBlockRot' hBlockConstraints
      hBlockOld hBlockTraceFitsField hBlockBitwiseWf
  rcases hboundary with ⟨hwindow, hrot, _, hblockSpec⟩
  have hshape : blockWindowHasShape blockAir start := hblockSpec.1
  have hpackage :=
    rowBlockCompressionPackage_of_shared_payload
      mainAir blockAir row start hmain hpayload hblockSpec
  rcases rowBlockOutputState_of_block_package mainAir blockAir row start hpackage with
    ⟨hcols, _⟩
  have hbounds :=
    output_byte_bounds_of_soundness
      mainAir blockAir row start hcols hwindow hrot hshape
      hBlockConstraints hBlockBitwiseWf
  have houtputEq :
      workingVarsToVector (rowNewState mainAir row) =
        CryptoHash.SHA256.compressBlock
          (workingVarsToVector (rowPrevState mainAir row))
          (Vector.ofFn (rowMessageWord mainAir row)) := by
    have hwork :
        rowNewState mainAir row =
          vectorToWorkingVars
            (CryptoHash.SHA256.compressBlock
              (workingVarsToVector (rowPrevState mainAir row))
              (Vector.ofFn (rowMessageWord mainAir row))) := by
      calc
        rowNewState mainAir row
            = sha256CompressWords (rowPrevState mainAir row) (Array.ofFn (rowMessageWord mainAir row)) := by
                simpa [compressWordEquivSpec, rowMessageWords] using hword
        _ = vectorToWorkingVars
              (CryptoHash.SHA256.compressBlock
                (workingVarsToVector (rowPrevState mainAir row))
                (Vector.ofFn (rowMessageWord mainAir row))) :=
            sha256CompressWords_eq_compressBlock
              (rowPrevState mainAir row) (rowMessageWord mainAir row)
    simpa [workingVarsToVector_vectorToWorkingVars] using
      congrArg workingVarsToVector hwork
  refine ⟨hbounds, ?_⟩
  calc
    Vector.ofFn
        (fun w : Fin 8 =>
          UInt32.ofNat
            ((new_state_byte mainAir (4 * w.1) row).val +
             (new_state_byte mainAir (4 * w.1 + 1) row).val * 2 ^ 8 +
             (new_state_byte mainAir (4 * w.1 + 2) row).val * 2 ^ 16 +
             (new_state_byte mainAir (4 * w.1 + 3) row).val * 2 ^ 24)) =
        workingVarsToVector (rowNewState mainAir row) :=
      explicit_output_words_eq mainAir row
    _ =
        CryptoHash.SHA256.compressBlock
          (workingVarsToVector (rowPrevState mainAir row))
          (Vector.ofFn (rowMessageWord mainAir row)) :=
      houtputEq
    _ =
        CryptoHash.SHA256.compressBlock
          (Vector.ofFn (fun w : Fin 8 =>
            UInt32.ofNat
              ((prev_state_byte mainAir (4 * w.1) row).val +
               (prev_state_byte mainAir (4 * w.1 + 1) row).val * 2 ^ 8 +
               (prev_state_byte mainAir (4 * w.1 + 2) row).val * 2 ^ 16 +
               (prev_state_byte mainAir (4 * w.1 + 3) row).val * 2 ^ 24)))
          (Vector.ofFn (fun w : Fin 16 =>
            UInt32.ofNat
              ((message_byte mainAir (4 * w.1) row).val * 2 ^ 24 +
               (message_byte mainAir (4 * w.1 + 1) row).val * 2 ^ 16 +
               (message_byte mainAir (4 * w.1 + 2) row).val * 2 ^ 8 +
               (message_byte mainAir (4 * w.1 + 3) row).val))) := by
      rw [← explicit_prev_state_words_eq mainAir row hPrevByteBound, ← explicit_message_words_eq mainAir row]

end VmExtensions.Sha2CompressOpcode
