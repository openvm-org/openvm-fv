import Mathlib.Algebra.Field.Basic

import LeanZKCircuit.OpenVM.Circuit

set_option linter.all false

register_simp_attr VmAirWrapper_Rv32LoadStoreAdapterAir_LoadStoreCoreAir_4_air_simplification
register_simp_attr VmAirWrapper_Rv32LoadStoreAdapterAir_LoadStoreCoreAir_4_constraint_and_interaction_simplification

namespace VmAirWrapper_Rv32LoadStoreAdapterAir_LoadStoreCoreAir_4.extraction

-----Constraints for VmAirWrapper<Rv32LoadStoreAdapterAir, LoadStoreCoreAir<4>-----

-----Used Columns-------------------
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 0) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 1) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 2) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 3) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 4) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 5) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 6) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 7) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 8) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 9) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 10) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 11) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 12) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 13) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 14) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 15) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 16) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 17) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 18) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 19) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 20) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 21) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 22) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 23) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 24) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 25) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 26) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 27) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 28) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 29) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 30) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 31) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 32) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 33) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 34) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 35) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 36) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 37) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 38) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 39) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 40) (row := row) (rotation := 0)

-----Extracted constraints----------
  @[simp]
  def inter_0 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t18 := ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)))
    let t19 := (t18 + (Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)))
    let t20 := (t19 + (Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)))
    t20

  @[simp]
  def inter_1 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t22 := (inter_0 c row - 2)
    t22

  @[simp]
  def inter_2 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t21 := (inter_0 c row - 1)
    let t23 := (t21 * inter_1 c row)
    t23

  @[simp]
  def inter_3 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t32 := ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)) - 1)
    let t33 := ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)) * t32)
    let t34 := (t33 * 1006632961)
    t34

  @[simp]
  def inter_4 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t35 := ((Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)) - 1)
    let t36 := ((Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)) * t35)
    let t37 := (t36 * 1006632961)
    t37

  @[simp]
  def inter_5 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t38 := (inter_3 c row + inter_4 c row)
    t38

  @[simp]
  def inter_6 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t39 := ((Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)) - 1)
    let t40 := ((Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)) * t39)
    let t41 := (t40 * 1006632961)
    t41

  @[simp]
  def inter_7 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t43 := ((Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)) - 1)
    let t44 := ((Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)) * t43)
    let t45 := (t44 * 1006632961)
    t45

  @[simp]
  def inter_8 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t51 := ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)) * inter_1 c row)
    let t52 := (t51 * 2013265920)
    t52

  @[simp]
  def inter_9 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t54 := ((Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)) * inter_1 c row)
    let t55 := (t54 * 2013265920)
    t55

  @[simp]
  def inter_10 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t57 := ((Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)) * inter_1 c row)
    let t58 := (t57 * 2013265920)
    t58

  @[simp]
  def inter_11 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t88 := (inter_6 c row + inter_9 c row)
    t88

  @[simp]
  def inter_12 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t95 := ((Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)) * inter_1 c row)
    let t96 := (t95 * 2013265920)
    t96

  @[simp]
  def inter_13 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t97 := ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)))
    let t98 := (inter_12 c row + t97)
    t98

  @[simp]
  def inter_14 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t153 := ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)))
    let t154 := ((Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)))
    let t155 := (t153 + t154)
    t155

  @[simp]
  def inter_15 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t165 := ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)))
    let t166 := ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)))
    let t167 := (t165 + t166)
    let t168 := ((Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)))
    let t169 := (t167 + t168)
    t169

  @[simp]
  def inter_16 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t219 := ((Circuit.main c (id := 0) (column := 4) (row := row) (rotation := 0)) * 256)
    let t220 := ((Circuit.main c (id := 0) (column := 3) (row := row) (rotation := 0)) + t219)
    let t221 := (t220 + (Circuit.main c (id := 0) (column := 14) (row := row) (rotation := 0)))
    let t222 := (t221 - (Circuit.main c (id := 0) (column := 16) (row := row) (rotation := 0)))
    let t223 := (t222 * 2013235201)
    t223

  @[simp]
  def inter_17 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t230 := ((Circuit.main c (id := 0) (column := 6) (row := row) (rotation := 0)) * 256)
    let t231 := ((Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)) + t230)
    let t232 := ((Circuit.main c (id := 0) (column := 15) (row := row) (rotation := 0)) * 65535)
    let t233 := (t231 + t232)
    let t239 := (t233 + inter_16 c row)
    let t240 := (t239 - (Circuit.main c (id := 0) (column := 17) (row := row) (rotation := 0)))
    let t241 := (t240 * 2013235201)
    t241

  @[simp]
  def inter_18 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t245 := ((Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)) - (Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)))
    let t246 := (t245 * 2)
    let t247 := ((Circuit.main c (id := 0) (column := 18) (row := row) (rotation := 0)) - t246)
    t247

  @[simp]
  def inter_19 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t276 := ((Circuit.main c (id := 0) (column := 17) (row := row) (rotation := 0)) * 65536)
    let t277 := ((Circuit.main c (id := 0) (column := 16) (row := row) (rotation := 0)) + t276)
    t277

  @[simp]
  def inter_20 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t278 := ((Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)) * inter_19 c row)
    let t279 := (1 - (Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)))
    let t280 := (t279 * (Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)))
    let t281 := (t278 + t280)
    t281

  @[simp]
  def inter_21 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t294 := (inter_11 c row * 2)
    let t295 := (inter_8 c row + t294)
    let t298 := (inter_10 c row * 3)
    let t299 := (t295 + t298)
    t299

  @[simp]
  def inter_22 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t331 := (1 - (Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)))
    let t332 := (t331 * (Circuit.main c (id := 0) (column := 18) (row := row) (rotation := 0)))
    t332

  @[simp]
  def inter_23 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t334 := ((Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)))
    let t335 := (1 - (Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)))
    let t338 := (t335 * inter_19 c row)
    let t339 := (t334 + t338)
    t339

  @[simp]
  def inter_24 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t340 := ((Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)))
    let t344 := (inter_14 c row * 2)
    let t345 := (t340 + t344)
    let t346 := ((Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)))
    let t347 := (t346 * 3)
    let t348 := (t345 + t347)
    t348

  @[simp]
  def constraint_0 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t0 := ((Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)) - 1)
    let t1 := ((Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)) * t0)
    t1 = 0

  @[simp]
  def constraint_1 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t2 := ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)) - 1)
    let t3 := ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)) - 2)
    let t4 := (t2 * t3)
    let t5 := ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)) * t4)
    t5 = 0

  @[simp]
  def constraint_2 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t6 := ((Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)) - 1)
    let t7 := ((Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)) - 2)
    let t8 := (t6 * t7)
    let t9 := ((Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)) * t8)
    t9 = 0

  @[simp]
  def constraint_3 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t10 := ((Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)) - 1)
    let t11 := ((Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)) - 2)
    let t12 := (t10 * t11)
    let t13 := ((Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)) * t12)
    t13 = 0

  @[simp]
  def constraint_4 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t14 := ((Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)) - 1)
    let t15 := ((Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)) - 2)
    let t16 := (t14 * t15)
    let t17 := ((Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)) * t16)
    t17 = 0

  @[simp]
  def constraint_5 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t24 := (inter_0 c row * inter_2 c row)
    t24 = 0

  @[simp]
  def constraint_6 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t31 := (inter_2 c row * (Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)))
    t31 = 0

  @[simp]
  def constraint_7 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t42 := (inter_5 c row + inter_6 c row)
    let t46 := (t42 + inter_7 c row)
    let t53 := (t46 + inter_8 c row)
    let t56 := (t53 + inter_9 c row)
    let t59 := (t56 + inter_10 c row)
    let t60 := ((Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)) - t59)
    t60 = 0

  @[simp]
  def constraint_8 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t61 := ((Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)) - 1)
    let t62 := ((Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)) * t61)
    t62 = 0

  @[simp]
  def constraint_9 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t73 := (inter_5 c row + inter_7 c row)
    let t74 := (t73 * (Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)))
    let t81 := (inter_8 c row * (Circuit.main c (id := 0) (column := 30) (row := row) (rotation := 0)))
    let t82 := (t74 + t81)
    let t89 := (inter_11 c row * (Circuit.main c (id := 0) (column := 31) (row := row) (rotation := 0)))
    let t90 := (t82 + t89)
    let t93 := (inter_10 c row * (Circuit.main c (id := 0) (column := 32) (row := row) (rotation := 0)))
    let t94 := (t90 + t93)
    let t99 := ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)))
    let t100 := (inter_13 c row + t99)
    let t101 := (t100 * (Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)))
    let t102 := ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)))
    let t103 := ((Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)))
    let t104 := (t102 + t103)
    let t105 := ((Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)))
    let t106 := (t104 + t105)
    let t107 := ((Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)))
    let t108 := (t106 + t107)
    let t109 := (t108 * (Circuit.main c (id := 0) (column := 33) (row := row) (rotation := 0)))
    let t110 := (t101 + t109)
    let t111 := (t94 + t110)
    let t112 := ((Circuit.main c (id := 0) (column := 37) (row := row) (rotation := 0)) - t111)
    t112 = 0

  @[simp]
  def constraint_10 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t120 := (inter_5 c row * (Circuit.main c (id := 0) (column := 30) (row := row) (rotation := 0)))
    let t124 := (inter_6 c row * (Circuit.main c (id := 0) (column := 32) (row := row) (rotation := 0)))
    let t125 := (t120 + t124)
    let t126 := ((Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)))
    let t127 := (t126 * (Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)))
    let t136 := (inter_13 c row * (Circuit.main c (id := 0) (column := 30) (row := row) (rotation := 0)))
    let t137 := (t127 + t136)
    let t138 := ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)))
    let t139 := ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)))
    let t140 := (t138 + t139)
    let t141 := ((Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)))
    let t142 := (t140 + t141)
    let t143 := ((Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)))
    let t144 := (t142 + t143)
    let t145 := (t144 * (Circuit.main c (id := 0) (column := 34) (row := row) (rotation := 0)))
    let t146 := (t137 + t145)
    let t147 := (t125 + t146)
    let t148 := ((Circuit.main c (id := 0) (column := 38) (row := row) (rotation := 0)) - t147)
    t148 = 0

  @[simp]
  def constraint_11 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t152 := (inter_3 c row * (Circuit.main c (id := 0) (column := 31) (row := row) (rotation := 0)))
    let t156 := (inter_14 c row * (Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)))
    let t163 := (inter_12 c row * (Circuit.main c (id := 0) (column := 31) (row := row) (rotation := 0)))
    let t164 := (t156 + t163)
    let t170 := ((Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)))
    let t171 := (inter_15 c row + t170)
    let t172 := (t171 * (Circuit.main c (id := 0) (column := 35) (row := row) (rotation := 0)))
    let t173 := (t164 + t172)
    let t174 := (t152 + t173)
    let t175 := ((Circuit.main c (id := 0) (column := 39) (row := row) (rotation := 0)) - t174)
    t175 = 0

  @[simp]
  def constraint_12 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t179 := (inter_3 c row * (Circuit.main c (id := 0) (column := 32) (row := row) (rotation := 0)))
    let t180 := ((Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)))
    let t181 := (t180 * (Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)))
    let t182 := ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)))
    let t183 := (t182 * (Circuit.main c (id := 0) (column := 30) (row := row) (rotation := 0)))
    let t184 := (t181 + t183)
    let t191 := (inter_12 c row * (Circuit.main c (id := 0) (column := 32) (row := row) (rotation := 0)))
    let t192 := (t184 + t191)
    let t198 := ((Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)))
    let t199 := (inter_15 c row + t198)
    let t200 := (t199 * (Circuit.main c (id := 0) (column := 36) (row := row) (rotation := 0)))
    let t201 := (t192 + t200)
    let t202 := (t179 + t201)
    let t203 := ((Circuit.main c (id := 0) (column := 40) (row := row) (rotation := 0)) - t202)
    t203 = 0

  @[simp]
  def constraint_13 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t204 := ((Circuit.main c (id := 0) (column := 22) (row := row) (rotation := 0)) - 1)
    let t205 := ((Circuit.main c (id := 0) (column := 22) (row := row) (rotation := 0)) * t204)
    t205 = 0

  @[simp]
  def constraint_14 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t206 := ((Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)) - 1)
    let t207 := ((Circuit.main c (id := 0) (column := 22) (row := row) (rotation := 0)) * t206)
    t207 = 0

  @[simp]
  def constraint_15 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t208 := ((Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)) - (Circuit.main c (id := 0) (column := 22) (row := row) (rotation := 0)))
    let t209 := ((Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)) - 1)
    let t210 := (t208 * t209)
    t210 = 0

  @[simp]
  def constraint_16 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t211 := ((Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)) - (Circuit.main c (id := 0) (column := 22) (row := row) (rotation := 0)))
    let t212 := (t211 * (Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)))
    t212 = 0

  @[simp]
  def constraint_17 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t213 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) - (Circuit.main c (id := 0) (column := 7) (row := row) (rotation := 0)))
    let t214 := (t213 - 1)
    let t215 := ((Circuit.main c (id := 0) (column := 9) (row := row) (rotation := 0)) * 131072)
    let t216 := ((Circuit.main c (id := 0) (column := 8) (row := row) (rotation := 0)) + t215)
    let t217 := (t214 - t216)
    let t218 := ((Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)) * t217)
    t218 = 0

  @[simp]
  def constraint_18 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t224 := (inter_16 c row - 1)
    let t225 := (inter_16 c row * t224)
    let t226 := ((Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)) * t225)
    t226 = 0

  @[simp]
  def constraint_19 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t227 := ((Circuit.main c (id := 0) (column := 15) (row := row) (rotation := 0)) - 1)
    let t228 := ((Circuit.main c (id := 0) (column := 15) (row := row) (rotation := 0)) * t227)
    let t229 := ((Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)) * t228)
    t229 = 0

  @[simp]
  def constraint_20 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t242 := (inter_17 c row - 1)
    let t243 := (inter_17 c row * t242)
    let t244 := ((Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)) * t243)
    t244 = 0

  @[simp]
  def constraint_21 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t248 := (inter_18 c row - 1)
    let t249 := (inter_18 c row * t248)
    let t250 := (inter_18 c row - 2)
    let t251 := (t249 * t250)
    t251 = 0

  @[simp]
  def constraint_22 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t252 := (1 - (Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)))
    let t253 := (t252 * (Circuit.main c (id := 0) (column := 18) (row := row) (rotation := 0)))
    t253 = 0

  @[simp]
  def constraint_23 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t254 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) + 1)
    let t255 := (t254 - (Circuit.main c (id := 0) (column := 11) (row := row) (rotation := 0)))
    let t256 := (t255 - 1)
    let t257 := ((Circuit.main c (id := 0) (column := 13) (row := row) (rotation := 0)) * 131072)
    let t258 := ((Circuit.main c (id := 0) (column := 12) (row := row) (rotation := 0)) + t257)
    let t259 := (t256 - t258)
    let t260 := ((Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)) * t259)
    t260 = 0

  @[simp]
  def constraint_24 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t261 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) + 2)
    let t262 := (t261 - (Circuit.main c (id := 0) (column := 19) (row := row) (rotation := 0)))
    let t263 := (t262 - 1)
    let t264 := ((Circuit.main c (id := 0) (column := 21) (row := row) (rotation := 0)) * 131072)
    let t265 := ((Circuit.main c (id := 0) (column := 20) (row := row) (rotation := 0)) + t264)
    let t266 := (t263 - t265)
    let t267 := ((Circuit.main c (id := 0) (column := 22) (row := row) (rotation := 0)) * t266)
    t267 = 0

  def constrain_interactions {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) :=
    Circuit.buses c = λ index =>
      if index = 0 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          let t268 := -((Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)))
          let t269 := ((Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)) + 4)
          let t270 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) + 3)
          [(t268, [(Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0))]), ((Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)), [t269, t270])])
      else if index = 1 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          let t271 := (2013265920 * (Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)))
          let t272 := (2013265920 * (Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)))
          let t273 := ((Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 18) (row := row) (rotation := 0)))
          let t274 := (1 - (Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)))
          let t275 := (t273 + t274)
          let t300 := (inter_20 c row - inter_21 c row)
          let t301 := ((Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 18) (row := row) (rotation := 0)))
          let t302 := (1 - (Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)))
          let t303 := (t301 + t302)
          let t328 := (inter_20 c row - inter_21 c row)
          let t329 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) + 1)
          let t330 := (2013265920 * (Circuit.main c (id := 0) (column := 22) (row := row) (rotation := 0)))
          let t333 := ((Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)) + inter_22 c row)
          let t349 := (inter_23 c row - inter_24 c row)
          let t352 := ((Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)) + inter_22 c row)
          let t368 := (inter_23 c row - inter_24 c row)
          let t369 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) + 2)
          [(t271, [1, (Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 3) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 4) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 6) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 7) (row := row) (rotation := 0))]), ((Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)), [1, (Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 3) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 4) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 6) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0))]), (t272, [t275, t300, (Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 30) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 31) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 32) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 11) (row := row) (rotation := 0))]), ((Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)), [t303, t328, (Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 30) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 31) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 32) (row := row) (rotation := 0)), t329]), (t330, [t333, t349, (Circuit.main c (id := 0) (column := 33) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 34) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 35) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 36) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 19) (row := row) (rotation := 0))]), ((Circuit.main c (id := 0) (column := 22) (row := row) (rotation := 0)), [t352, t368, (Circuit.main c (id := 0) (column := 37) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 38) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 39) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 40) (row := row) (rotation := 0)), t369])])
      else if index = 2 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          let t376 := (inter_4 c row + inter_6 c row)
          let t377 := (t376 * 2)
          let t387 := (inter_7 c row + inter_8 c row)
          let t390 := (t387 + inter_9 c row)
          let t393 := (t390 + inter_10 c row)
          let t394 := (t377 + t393)
          let t397 := (inter_12 c row * 3)
          let t398 := (t394 + t397)
          let t399 := ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)))
          let t400 := ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)))
          let t401 := (t399 + t400)
          let t402 := (t401 * 4)
          let t403 := (t398 + t402)
          let t404 := ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)))
          let t405 := ((Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)))
          let t406 := (t404 + t405)
          let t407 := ((Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)))
          let t408 := (t406 + t407)
          let t409 := ((Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)))
          let t410 := (t408 + t409)
          let t411 := (t410 * 5)
          let t412 := (t403 + t411)
          let t413 := (528 + t412)
          [((Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)), [(Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)), t413, (Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 14) (row := row) (rotation := 0)), 1, (Circuit.main c (id := 0) (column := 18) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 22) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 15) (row := row) (rotation := 0))])])
      else if index = 3 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          let t441 := (inter_21 c row + inter_24 c row)
          let t442 := ((Circuit.main c (id := 0) (column := 16) (row := row) (rotation := 0)) - t441)
          let t443 := (t442 * 1509949441)
          [((Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)), [(Circuit.main c (id := 0) (column := 8) (row := row) (rotation := 0)), 17]), ((Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)), [(Circuit.main c (id := 0) (column := 9) (row := row) (rotation := 0)), 12]), ((Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)), [t443, 14]), ((Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)), [(Circuit.main c (id := 0) (column := 17) (row := row) (rotation := 0)), 13]), ((Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)), [(Circuit.main c (id := 0) (column := 12) (row := row) (rotation := 0)), 17]), ((Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)), [(Circuit.main c (id := 0) (column := 13) (row := row) (rotation := 0)), 12]), ((Circuit.main c (id := 0) (column := 22) (row := row) (rotation := 0)), [(Circuit.main c (id := 0) (column := 20) (row := row) (rotation := 0)), 17]), ((Circuit.main c (id := 0) (column := 22) (row := row) (rotation := 0)), [(Circuit.main c (id := 0) (column := 21) (row := row) (rotation := 0)), 12])])
    else []

end VmAirWrapper_Rv32LoadStoreAdapterAir_LoadStoreCoreAir_4.extraction
------
