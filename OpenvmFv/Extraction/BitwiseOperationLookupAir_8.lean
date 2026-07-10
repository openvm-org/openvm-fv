import Mathlib.Algebra.Field.Basic

import LeanZKCircuit.OpenVM.Circuit

set_option linter.all false

register_simp_attr BitwiseOperationLookupAir_8_air_simplification
register_simp_attr BitwiseOperationLookupAir_8_constraint_and_interaction_simplification

namespace BitwiseOperationLookupAir_8.extraction

-----Constraints for BitwiseOperationLookupAir<8>-----

-----Used Columns-------------------
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 0) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 0) (row := row) (rotation := 1)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 1) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 1) (row := row) (rotation := 1)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 2) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 2) (row := row) (rotation := 1)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 3) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 3) (row := row) (rotation := 1)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 4) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 4) (row := row) (rotation := 1)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 5) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 5) (row := row) (rotation := 1)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 6) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 6) (row := row) (rotation := 1)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 7) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 7) (row := row) (rotation := 1)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 8) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 8) (row := row) (rotation := 1)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 9) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 9) (row := row) (rotation := 1)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 10) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 10) (row := row) (rotation := 1)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 11) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 11) (row := row) (rotation := 1)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 12) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 12) (row := row) (rotation := 1)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 13) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 13) (row := row) (rotation := 1)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 14) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 14) (row := row) (rotation := 1)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 15) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 15) (row := row) (rotation := 1)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 16) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 17) (row := row) (rotation := 0)

-----Extracted constraints----------
  @[simp]
  def inter_0 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t62 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) * 2)
    let t63 := ((Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)) + t62)
    let t64 := ((Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0)) * 4)
    let t65 := (t63 + t64)
    let t66 := ((Circuit.main c (id := 0) (column := 3) (row := row) (rotation := 0)) * 8)
    let t67 := (t65 + t66)
    let t68 := ((Circuit.main c (id := 0) (column := 4) (row := row) (rotation := 0)) * 16)
    let t69 := (t67 + t68)
    let t70 := ((Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)) * 32)
    let t71 := (t69 + t70)
    let t72 := ((Circuit.main c (id := 0) (column := 6) (row := row) (rotation := 0)) * 64)
    let t73 := (t71 + t72)
    t73

  @[simp]
  def inter_1 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t77 := ((Circuit.main c (id := 0) (column := 9) (row := row) (rotation := 0)) * 2)
    let t78 := ((Circuit.main c (id := 0) (column := 8) (row := row) (rotation := 0)) + t77)
    let t79 := ((Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)) * 4)
    let t80 := (t78 + t79)
    let t81 := ((Circuit.main c (id := 0) (column := 11) (row := row) (rotation := 0)) * 8)
    let t82 := (t80 + t81)
    let t83 := ((Circuit.main c (id := 0) (column := 12) (row := row) (rotation := 0)) * 16)
    let t84 := (t82 + t83)
    let t85 := ((Circuit.main c (id := 0) (column := 13) (row := row) (rotation := 0)) * 32)
    let t86 := (t84 + t85)
    let t87 := ((Circuit.main c (id := 0) (column := 14) (row := row) (rotation := 0)) * 64)
    let t88 := (t86 + t87)
    t88

  @[simp]
  def inter_2 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t74 := ((Circuit.main c (id := 0) (column := 7) (row := row) (rotation := 0)) * 128)
    let t75 := (inter_0 c row + t74)
    let t76 := (t75 * 256)
    let t89 := ((Circuit.main c (id := 0) (column := 15) (row := row) (rotation := 0)) * 128)
    let t90 := (inter_1 c row + t89)
    let t91 := (t76 + t90)
    t91

  @[simp]
  def constraint_0 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t0 := ((Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)) - 1)
    let t1 := ((Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)) * t0)
    t1 = 0

  @[simp]
  def constraint_1 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t2 := ((Circuit.main c (id := 0) (column := 8) (row := row) (rotation := 0)) - 1)
    let t3 := ((Circuit.main c (id := 0) (column := 8) (row := row) (rotation := 0)) * t2)
    t3 = 0

  @[simp]
  def constraint_2 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t4 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) - 1)
    let t5 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) * t4)
    t5 = 0

  @[simp]
  def constraint_3 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t6 := ((Circuit.main c (id := 0) (column := 9) (row := row) (rotation := 0)) - 1)
    let t7 := ((Circuit.main c (id := 0) (column := 9) (row := row) (rotation := 0)) * t6)
    t7 = 0

  @[simp]
  def constraint_4 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t8 := ((Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0)) - 1)
    let t9 := ((Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0)) * t8)
    t9 = 0

  @[simp]
  def constraint_5 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t10 := ((Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)) - 1)
    let t11 := ((Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)) * t10)
    t11 = 0

  @[simp]
  def constraint_6 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t12 := ((Circuit.main c (id := 0) (column := 3) (row := row) (rotation := 0)) - 1)
    let t13 := ((Circuit.main c (id := 0) (column := 3) (row := row) (rotation := 0)) * t12)
    t13 = 0

  @[simp]
  def constraint_7 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t14 := ((Circuit.main c (id := 0) (column := 11) (row := row) (rotation := 0)) - 1)
    let t15 := ((Circuit.main c (id := 0) (column := 11) (row := row) (rotation := 0)) * t14)
    t15 = 0

  @[simp]
  def constraint_8 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t16 := ((Circuit.main c (id := 0) (column := 4) (row := row) (rotation := 0)) - 1)
    let t17 := ((Circuit.main c (id := 0) (column := 4) (row := row) (rotation := 0)) * t16)
    t17 = 0

  @[simp]
  def constraint_9 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t18 := ((Circuit.main c (id := 0) (column := 12) (row := row) (rotation := 0)) - 1)
    let t19 := ((Circuit.main c (id := 0) (column := 12) (row := row) (rotation := 0)) * t18)
    t19 = 0

  @[simp]
  def constraint_10 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t20 := ((Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)) - 1)
    let t21 := ((Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)) * t20)
    t21 = 0

  @[simp]
  def constraint_11 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t22 := ((Circuit.main c (id := 0) (column := 13) (row := row) (rotation := 0)) - 1)
    let t23 := ((Circuit.main c (id := 0) (column := 13) (row := row) (rotation := 0)) * t22)
    t23 = 0

  @[simp]
  def constraint_12 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t24 := ((Circuit.main c (id := 0) (column := 6) (row := row) (rotation := 0)) - 1)
    let t25 := ((Circuit.main c (id := 0) (column := 6) (row := row) (rotation := 0)) * t24)
    t25 = 0

  @[simp]
  def constraint_13 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t26 := ((Circuit.main c (id := 0) (column := 14) (row := row) (rotation := 0)) - 1)
    let t27 := ((Circuit.main c (id := 0) (column := 14) (row := row) (rotation := 0)) * t26)
    t27 = 0

  @[simp]
  def constraint_14 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t28 := ((Circuit.main c (id := 0) (column := 7) (row := row) (rotation := 0)) - 1)
    let t29 := ((Circuit.main c (id := 0) (column := 7) (row := row) (rotation := 0)) * t28)
    t29 = 0

  @[simp]
  def constraint_15 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t30 := ((Circuit.main c (id := 0) (column := 15) (row := row) (rotation := 0)) - 1)
    let t31 := ((Circuit.main c (id := 0) (column := 15) (row := row) (rotation := 0)) * t30)
    t31 = 0

  @[simp]
  def constraint_16 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t32 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 1)) * 2)
    let t33 := ((Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 1)) + t32)
    let t34 := ((Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 1)) * 4)
    let t35 := (t33 + t34)
    let t36 := ((Circuit.main c (id := 0) (column := 3) (row := row) (rotation := 1)) * 8)
    let t37 := (t35 + t36)
    let t38 := ((Circuit.main c (id := 0) (column := 4) (row := row) (rotation := 1)) * 16)
    let t39 := (t37 + t38)
    let t40 := ((Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 1)) * 32)
    let t41 := (t39 + t40)
    let t42 := ((Circuit.main c (id := 0) (column := 6) (row := row) (rotation := 1)) * 64)
    let t43 := (t41 + t42)
    let t44 := ((Circuit.main c (id := 0) (column := 7) (row := row) (rotation := 1)) * 128)
    let t45 := (t43 + t44)
    let t46 := (t45 * 256)
    let t47 := ((Circuit.main c (id := 0) (column := 9) (row := row) (rotation := 1)) * 2)
    let t48 := ((Circuit.main c (id := 0) (column := 8) (row := row) (rotation := 1)) + t47)
    let t49 := ((Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 1)) * 4)
    let t50 := (t48 + t49)
    let t51 := ((Circuit.main c (id := 0) (column := 11) (row := row) (rotation := 1)) * 8)
    let t52 := (t50 + t51)
    let t53 := ((Circuit.main c (id := 0) (column := 12) (row := row) (rotation := 1)) * 16)
    let t54 := (t52 + t53)
    let t55 := ((Circuit.main c (id := 0) (column := 13) (row := row) (rotation := 1)) * 32)
    let t56 := (t54 + t55)
    let t57 := ((Circuit.main c (id := 0) (column := 14) (row := row) (rotation := 1)) * 64)
    let t58 := (t56 + t57)
    let t59 := ((Circuit.main c (id := 0) (column := 15) (row := row) (rotation := 1)) * 128)
    let t60 := (t58 + t59)
    let t61 := (t46 + t60)
    let t92 := (t61 - inter_2 c row)
    let t93 := (t92 - 1)
    let t94 := ((Circuit.isTransitionRow c row) * t93)
    t94 = 0

  @[simp]
  def constraint_17 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t125 := ((Circuit.isFirstRow c row) * inter_2 c row)
    t125 = 0

  @[simp]
  def constraint_18 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t156 := (inter_2 c row - 65535)
    let t157 := ((Circuit.isLastRow c row) * t156)
    t157 = 0

  def constrain_interactions {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) :=
    Circuit.buses c = λ index =>
      if index = 6 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          let t158 := -((Circuit.main c (id := 0) (column := 16) (row := row) (rotation := 0)))
          let t171 := ((Circuit.main c (id := 0) (column := 7) (row := row) (rotation := 0)) * 128)
          let t172 := (inter_0 c row + t171)
          let t185 := ((Circuit.main c (id := 0) (column := 15) (row := row) (rotation := 0)) * 128)
          let t186 := (inter_1 c row + t185)
          let t187 := -((Circuit.main c (id := 0) (column := 17) (row := row) (rotation := 0)))
          let t200 := ((Circuit.main c (id := 0) (column := 7) (row := row) (rotation := 0)) * 128)
          let t201 := (inter_0 c row + t200)
          let t214 := ((Circuit.main c (id := 0) (column := 15) (row := row) (rotation := 0)) * 128)
          let t215 := (inter_1 c row + t214)
          let t216 := ((Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 8) (row := row) (rotation := 0)))
          let t217 := (2 * (Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)))
          let t218 := (t217 * (Circuit.main c (id := 0) (column := 8) (row := row) (rotation := 0)))
          let t219 := (t216 - t218)
          let t220 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 9) (row := row) (rotation := 0)))
          let t221 := (2 * (Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)))
          let t222 := (t221 * (Circuit.main c (id := 0) (column := 9) (row := row) (rotation := 0)))
          let t223 := (t220 - t222)
          let t224 := (t223 * 2)
          let t225 := (t219 + t224)
          let t226 := ((Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)))
          let t227 := (2 * (Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0)))
          let t228 := (t227 * (Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)))
          let t229 := (t226 - t228)
          let t230 := (t229 * 4)
          let t231 := (t225 + t230)
          let t232 := ((Circuit.main c (id := 0) (column := 3) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 11) (row := row) (rotation := 0)))
          let t233 := (2 * (Circuit.main c (id := 0) (column := 3) (row := row) (rotation := 0)))
          let t234 := (t233 * (Circuit.main c (id := 0) (column := 11) (row := row) (rotation := 0)))
          let t235 := (t232 - t234)
          let t236 := (t235 * 8)
          let t237 := (t231 + t236)
          let t238 := ((Circuit.main c (id := 0) (column := 4) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 12) (row := row) (rotation := 0)))
          let t239 := (2 * (Circuit.main c (id := 0) (column := 4) (row := row) (rotation := 0)))
          let t240 := (t239 * (Circuit.main c (id := 0) (column := 12) (row := row) (rotation := 0)))
          let t241 := (t238 - t240)
          let t242 := (t241 * 16)
          let t243 := (t237 + t242)
          let t244 := ((Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 13) (row := row) (rotation := 0)))
          let t245 := (2 * (Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)))
          let t246 := (t245 * (Circuit.main c (id := 0) (column := 13) (row := row) (rotation := 0)))
          let t247 := (t244 - t246)
          let t248 := (t247 * 32)
          let t249 := (t243 + t248)
          let t250 := ((Circuit.main c (id := 0) (column := 6) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 14) (row := row) (rotation := 0)))
          let t251 := (2 * (Circuit.main c (id := 0) (column := 6) (row := row) (rotation := 0)))
          let t252 := (t251 * (Circuit.main c (id := 0) (column := 14) (row := row) (rotation := 0)))
          let t253 := (t250 - t252)
          let t254 := (t253 * 64)
          let t255 := (t249 + t254)
          let t256 := ((Circuit.main c (id := 0) (column := 7) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 15) (row := row) (rotation := 0)))
          let t257 := (2 * (Circuit.main c (id := 0) (column := 7) (row := row) (rotation := 0)))
          let t258 := (t257 * (Circuit.main c (id := 0) (column := 15) (row := row) (rotation := 0)))
          let t259 := (t256 - t258)
          let t260 := (t259 * 128)
          let t261 := (t255 + t260)
          [(t158, [t172, t186, 0, 0]), (t187, [t201, t215, t261, 1])])
    else []

end BitwiseOperationLookupAir_8.extraction
------
