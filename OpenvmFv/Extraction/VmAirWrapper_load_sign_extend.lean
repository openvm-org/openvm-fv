import Mathlib.Algebra.Field.Basic

import LeanZKCircuit.OpenVM.Circuit

set_option linter.all false

register_simp_attr VmAirWrapper_Rv32LoadStoreAdapterAir_LoadSignExtendCoreAir_4_8_air_simplification
register_simp_attr VmAirWrapper_Rv32LoadStoreAdapterAir_LoadSignExtendCoreAir_4_8_constraint_and_interaction_simplification

namespace VmAirWrapper_Rv32LoadStoreAdapterAir_LoadSignExtendCoreAir_4_8.extraction

-----Constraints for VmAirWrapper<Rv32LoadStoreAdapterAir, LoadSignExtendCoreAir<4, 8>-----

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

-----Extracted constraints----------
  @[simp]
  def inter_0 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t6 := ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)))
    let t7 := (t6 + (Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)))
    t7

  @[simp]
  def inter_1 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t8 := (inter_0 c row - 1)
    t8

  @[simp]
  def inter_2 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t22 := (inter_0 c row - (Circuit.main c (id := 0) (column := 22) (row := row) (rotation := 0)))
    t22

  @[simp]
  def inter_3 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t39 := ((Circuit.main c (id := 0) (column := 4) (row := row) (rotation := 0)) * 256)
    let t40 := ((Circuit.main c (id := 0) (column := 3) (row := row) (rotation := 0)) + t39)
    let t41 := (t40 + (Circuit.main c (id := 0) (column := 14) (row := row) (rotation := 0)))
    let t42 := (t41 - (Circuit.main c (id := 0) (column := 16) (row := row) (rotation := 0)))
    let t43 := (t42 * 2013235201)
    t43

  @[simp]
  def inter_4 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t54 := ((Circuit.main c (id := 0) (column := 6) (row := row) (rotation := 0)) * 256)
    let t55 := ((Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)) + t54)
    let t56 := ((Circuit.main c (id := 0) (column := 15) (row := row) (rotation := 0)) * 65535)
    let t57 := (t55 + t56)
    let t63 := (t57 + inter_3 c row)
    let t64 := (t63 - (Circuit.main c (id := 0) (column := 17) (row := row) (rotation := 0)))
    let t65 := (t64 * 2013235201)
    t65

  @[simp]
  def inter_5 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t71 := (inter_0 c row - inter_0 c row)
    let t72 := (t71 * 2)
    let t73 := ((Circuit.main c (id := 0) (column := 18) (row := row) (rotation := 0)) - t72)
    t73

  @[simp]
  def inter_6 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t80 := (1 - inter_0 c row)
    t80

  @[simp]
  def inter_7 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t115 := (inter_0 c row * (Circuit.main c (id := 0) (column := 18) (row := row) (rotation := 0)))
    t115

  @[simp]
  def inter_8 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t120 := ((Circuit.main c (id := 0) (column := 17) (row := row) (rotation := 0)) * 65536)
    let t121 := ((Circuit.main c (id := 0) (column := 16) (row := row) (rotation := 0)) + t120)
    t121

  @[simp]
  def inter_9 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t122 := (inter_0 c row * inter_8 c row)
    let t124 := (inter_6 c row * (Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)))
    let t125 := (t122 + t124)
    t125

  @[simp]
  def inter_10 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t126 := ((Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)) * 2)
    let t127 := (t126 + (Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)))
    t127

  @[simp]
  def inter_11 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t130 := (1 - (Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)))
    let t131 := (t130 * (Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)))
    t131

  @[simp]
  def inter_12 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t134 := (1 - (Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)))
    let t135 := (t134 * (Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)))
    t135

  @[simp]
  def inter_13 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t138 := (1 - (Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)))
    let t139 := (t138 * (Circuit.main c (id := 0) (column := 30) (row := row) (rotation := 0)))
    t139

  @[simp]
  def inter_14 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t142 := (1 - (Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)))
    let t143 := (t142 * (Circuit.main c (id := 0) (column := 31) (row := row) (rotation := 0)))
    t143

  @[simp]
  def inter_15 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t184 := (inter_6 c row * (Circuit.main c (id := 0) (column := 18) (row := row) (rotation := 0)))
    t184

  @[simp]
  def inter_16 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t188 := (inter_0 c row * (Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)))
    t188

  @[simp]
  def inter_17 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t192 := (inter_6 c row * inter_8 c row)
    t192

  @[simp]
  def constraint_0 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t0 := ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)) - 1)
    let t1 := ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)) * t0)
    t1 = 0

  @[simp]
  def constraint_1 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t2 := ((Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)) - 1)
    let t3 := ((Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)) * t2)
    t3 = 0

  @[simp]
  def constraint_2 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t4 := ((Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)) - 1)
    let t5 := ((Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)) * t4)
    t5 = 0

  @[simp]
  def constraint_3 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t9 := (inter_0 c row * inter_1 c row)
    t9 = 0

  @[simp]
  def constraint_4 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t10 := ((Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)) - 1)
    let t11 := ((Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)) * t10)
    t11 = 0

  @[simp]
  def constraint_5 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t12 := ((Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)) - 1)
    let t13 := ((Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)) * t12)
    t13 = 0

  @[simp]
  def constraint_6 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t14 := ((Circuit.main c (id := 0) (column := 22) (row := row) (rotation := 0)) - 1)
    let t15 := ((Circuit.main c (id := 0) (column := 22) (row := row) (rotation := 0)) * t14)
    t15 = 0

  @[simp]
  def constraint_7 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t19 := ((Circuit.main c (id := 0) (column := 22) (row := row) (rotation := 0)) * inter_1 c row)
    t19 = 0

  @[simp]
  def constraint_8 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t24 := (inter_2 c row * inter_1 c row)
    t24 = 0

  @[simp]
  def constraint_9 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t28 := (inter_2 c row * (Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)))
    t28 = 0

  @[simp]
  def constraint_10 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t31 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) - (Circuit.main c (id := 0) (column := 7) (row := row) (rotation := 0)))
    let t32 := (t31 - 1)
    let t33 := ((Circuit.main c (id := 0) (column := 9) (row := row) (rotation := 0)) * 131072)
    let t34 := ((Circuit.main c (id := 0) (column := 8) (row := row) (rotation := 0)) + t33)
    let t35 := (t32 - t34)
    let t36 := (inter_0 c row * t35)
    t36 = 0

  @[simp]
  def constraint_11 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t44 := (inter_3 c row - 1)
    let t45 := (inter_3 c row * t44)
    let t46 := (inter_0 c row * t45)
    t46 = 0

  @[simp]
  def constraint_12 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t49 := ((Circuit.main c (id := 0) (column := 15) (row := row) (rotation := 0)) - 1)
    let t50 := ((Circuit.main c (id := 0) (column := 15) (row := row) (rotation := 0)) * t49)
    let t51 := (inter_0 c row * t50)
    t51 = 0

  @[simp]
  def constraint_13 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t66 := (inter_4 c row - 1)
    let t67 := (inter_4 c row * t66)
    let t68 := (inter_0 c row * t67)
    t68 = 0

  @[simp]
  def constraint_14 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t74 := (inter_5 c row - 1)
    let t75 := (inter_5 c row * t74)
    let t76 := (inter_5 c row - 2)
    let t77 := (t75 * t76)
    t77 = 0

  @[simp]
  def constraint_15 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t81 := (inter_6 c row * (Circuit.main c (id := 0) (column := 18) (row := row) (rotation := 0)))
    t81 = 0

  @[simp]
  def constraint_16 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t84 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) + 1)
    let t85 := (t84 - (Circuit.main c (id := 0) (column := 11) (row := row) (rotation := 0)))
    let t86 := (t85 - 1)
    let t87 := ((Circuit.main c (id := 0) (column := 13) (row := row) (rotation := 0)) * 131072)
    let t88 := ((Circuit.main c (id := 0) (column := 12) (row := row) (rotation := 0)) + t87)
    let t89 := (t86 - t88)
    let t90 := (inter_0 c row * t89)
    t90 = 0

  @[simp]
  def constraint_17 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t91 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) + 2)
    let t92 := (t91 - (Circuit.main c (id := 0) (column := 19) (row := row) (rotation := 0)))
    let t93 := (t92 - 1)
    let t94 := ((Circuit.main c (id := 0) (column := 21) (row := row) (rotation := 0)) * 131072)
    let t95 := ((Circuit.main c (id := 0) (column := 20) (row := row) (rotation := 0)) + t94)
    let t96 := (t93 - t95)
    let t97 := ((Circuit.main c (id := 0) (column := 22) (row := row) (rotation := 0)) * t96)
    t97 = 0

  def constrain_interactions {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) :=
    Circuit.buses c = λ index =>
      if index = 0 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          let t100 := -(inter_0 c row)
          let t101 := ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)))
          let t102 := (t101 + (Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)))
          let t103 := ((Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)) + 4)
          let t104 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) + 3)
          [(t100, [(Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0))]), (t102, [t103, t104])])
      else if index = 1 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          let t107 := (2013265920 * inter_0 c row)
          let t108 := ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)))
          let t109 := (t108 + (Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)))
          let t112 := (2013265920 * inter_0 c row)
          let t117 := (inter_7 c row + inter_6 c row)
          let t128 := (inter_9 c row - inter_10 c row)
          let t129 := ((Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 30) (row := row) (rotation := 0)))
          let t132 := (t129 + inter_11 c row)
          let t133 := ((Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 31) (row := row) (rotation := 0)))
          let t136 := (t133 + inter_12 c row)
          let t137 := ((Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)))
          let t140 := (t137 + inter_13 c row)
          let t141 := ((Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)))
          let t144 := (t141 + inter_14 c row)
          let t145 := ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)))
          let t146 := (t145 + (Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)))
          let t151 := (inter_7 c row + inter_6 c row)
          let t162 := (inter_9 c row - inter_10 c row)
          let t163 := ((Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 30) (row := row) (rotation := 0)))
          let t166 := (t163 + inter_11 c row)
          let t167 := ((Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 31) (row := row) (rotation := 0)))
          let t170 := (t167 + inter_12 c row)
          let t171 := ((Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)))
          let t174 := (t171 + inter_13 c row)
          let t175 := ((Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)))
          let t178 := (t175 + inter_14 c row)
          let t179 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) + 1)
          let t180 := (2013265920 * (Circuit.main c (id := 0) (column := 22) (row := row) (rotation := 0)))
          let t185 := (inter_0 c row + inter_15 c row)
          let t193 := (inter_16 c row + inter_17 c row)
          let t198 := (inter_0 c row + inter_15 c row)
          let t206 := (inter_16 c row + inter_17 c row)
          let t207 := ((Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)))
          let t208 := (t207 * (Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)))
          let t209 := ((Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)))
          let t210 := (t208 + t209)
          let t211 := ((Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)))
          let t212 := ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)))
          let t213 := ((Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)) * 255)
          let t214 := (t212 * t213)
          let t215 := (t211 + t214)
          let t216 := ((Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)) * 255)
          let t217 := ((Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)) * 255)
          let t218 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) + 2)
          [(t107, [1, (Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 3) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 4) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 6) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 7) (row := row) (rotation := 0))]), (t109, [1, (Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 3) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 4) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 6) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0))]), (t112, [t117, t128, t132, t136, t140, t144, (Circuit.main c (id := 0) (column := 11) (row := row) (rotation := 0))]), (t146, [t151, t162, t166, t170, t174, t178, t179]), (t180, [t185, t193, (Circuit.main c (id := 0) (column := 32) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 33) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 34) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 35) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 19) (row := row) (rotation := 0))]), ((Circuit.main c (id := 0) (column := 22) (row := row) (rotation := 0)), [t198, t206, t210, t215, t216, t217, t218])])
      else if index = 2 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          let t219 := ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)))
          let t220 := (t219 + (Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)))
          let t221 := ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)))
          let t222 := (t221 * 6)
          let t223 := ((Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)) * 7)
          let t224 := (t222 + t223)
          let t225 := (t224 + 528)
          [(t220, [(Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)), t225, (Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 14) (row := row) (rotation := 0)), 1, (Circuit.main c (id := 0) (column := 18) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 22) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 15) (row := row) (rotation := 0))])])
      else if index = 3 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          let t226 := ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)))
          let t227 := (t226 + (Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)))
          let t228 := ((Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)))
          let t229 := ((Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)))
          let t230 := (t228 + t229)
          let t231 := ((Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)))
          let t232 := (t230 + t231)
          let t233 := ((Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)) * 128)
          let t234 := (t232 - t233)
          let t235 := ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)))
          let t236 := (t235 + (Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)))
          let t237 := ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)))
          let t238 := (t237 + (Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)))
          let t239 := ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)))
          let t240 := (t239 + (Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)))
          let t243 := ((Circuit.main c (id := 0) (column := 16) (row := row) (rotation := 0)) - inter_10 c row)
          let t244 := (t243 * 1509949441)
          let t245 := ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)))
          let t246 := (t245 + (Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)))
          let t247 := ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)))
          let t248 := (t247 + (Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)))
          let t249 := ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)))
          let t250 := (t249 + (Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)))
          [(t227, [t234, 7]), (t236, [(Circuit.main c (id := 0) (column := 8) (row := row) (rotation := 0)), 17]), (t238, [(Circuit.main c (id := 0) (column := 9) (row := row) (rotation := 0)), 12]), (t240, [t244, 14]), (t246, [(Circuit.main c (id := 0) (column := 17) (row := row) (rotation := 0)), 13]), (t248, [(Circuit.main c (id := 0) (column := 12) (row := row) (rotation := 0)), 17]), (t250, [(Circuit.main c (id := 0) (column := 13) (row := row) (rotation := 0)), 12]), ((Circuit.main c (id := 0) (column := 22) (row := row) (rotation := 0)), [(Circuit.main c (id := 0) (column := 20) (row := row) (rotation := 0)), 17]), ((Circuit.main c (id := 0) (column := 22) (row := row) (rotation := 0)), [(Circuit.main c (id := 0) (column := 21) (row := row) (rotation := 0)), 12])])
    else []

end VmAirWrapper_Rv32LoadStoreAdapterAir_LoadSignExtendCoreAir_4_8.extraction
------
