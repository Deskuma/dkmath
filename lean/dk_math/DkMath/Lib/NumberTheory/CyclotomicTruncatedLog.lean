/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Truncated-logarithm identities adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_ExtCitation_Cyclotomic_unitsOmegaEigenvector_two_eq_zero_of_local_pow.lean.
Upstream blob: 89f85644f3cc853c293396363bd290c9ff81a237
Modified: expose reusable public ring identities and a group-to-additive map;
remove all external namespaces, export machinery and number-field specialization.
-/

import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Tactic.Ring

#print "file: DkMath.Lib.NumberTheory.CyclotomicTruncatedLog"

/-!
# 3次で消えるイデアル上の切断対数

tlog h z = (z−1) − h(z−1)², 2h=1 とする。
J の三つの元の積が零なら、1+J 上の乗法を加法へ送る。
数体・固有空間・単元消滅を仮定しない、環の恒等式である。
-/

namespace DkMath.Lib.NumberTheory.CyclotomicTruncatedLog

variable {Q : Type*} [CommRing Q]

/-- 3次項以降を捨てた対数。h=1/2 に相当する値を明示する。 -/
def tlog (h : Q) (z : Q) : Q := (z - 1) - h * (z - 1) ^ 2

theorem tlog_one (h : Q) : tlog h 1 = 0 := by simp [tlog]

/-- 3次の積が零のとき、1+J 上で乗法を加法に送る。 -/
theorem tlog_mul {J : Ideal Q} (hJ : ∀ a ∈ J, ∀ b ∈ J, ∀ c ∈ J, a * b * c = 0)
    {h : Q} (h2 : 2 * h = 1) {z w : Q} (hz : z - 1 ∈ J) (hw : w - 1 ∈ J) :
    tlog h (z * w) = tlog h z + tlog h w := by
  obtain ⟨a, rfl⟩ : ∃ a, z = 1 + a := ⟨z - 1, by ring⟩
  obtain ⟨b, rfl⟩ : ∃ b, w = 1 + b := ⟨w - 1, by ring⟩
  simp only [add_sub_cancel_left] at hz hw
  have h1 : a * a * b = 0 := hJ a hz a hz b hw
  have h3 : a * b * b = 0 := hJ a hz b hw b hw
  have key : tlog h ((1 + a) * (1 + b)) - (tlog h (1 + a) + tlog h (1 + b)) =
      (1 - 2 * h) * (a * b) - h * (2 * (a * a * b) + 2 * (a * b * b) + (a * a * b) * b) := by
    unfold tlog; ring
  rw [h1, h3, h2] at key
  rw [← sub_eq_zero, key]
  ring

/-- 環準同型は切断対数の明示式と可換する。 -/
theorem map_tlog {Q' : Type*} [CommRing Q'] (f : Q →+* Q') (h : Q) (z : Q) :
    f (tlog h z) = tlog (f h) (f z) := by
  simp [tlog, map_sub, map_mul, map_pow]

/-- 対数の値は元と同じ冪零イデアルに属する。 -/
theorem tlog_mem {J : Ideal Q} (h : Q) {z : Q} (hz : z - 1 ∈ J) : tlog h z ∈ J := by
  unfold tlog
  exact J.sub_mem hz (J.mul_mem_left _ (by rw [pow_two]; exact J.mul_mem_left _ hz))

section Hom

variable {G : Type*} [Group G]

/-- 像が 1+J に入る群準同型に対する、実際の加法準同型。 -/
def tlogHom {J : Ideal Q} (hJ : ∀ a ∈ J, ∀ b ∈ J, ∀ c ∈ J, a * b * c = 0)
    {h : Q} (h2 : 2 * h = 1) (f : G →* Q) (hf : ∀ g, f g - 1 ∈ J) : Additive G →+ Q where
  toFun x := tlog h (f x.toMul)
  map_zero' := by simp [tlog_one]
  map_add' x y := by
    simp only [toMul_add, map_mul]
    exact tlog_mul hJ h2 (hf _) (hf _)

theorem tlogHom_apply {J : Ideal Q} (hJ : ∀ a ∈ J, ∀ b ∈ J, ∀ c ∈ J, a * b * c = 0)
    {h : Q} (h2 : 2 * h = 1) (f : G →* Q) (hf : ∀ g, f g - 1 ∈ J) (g : G) :
    tlogHom hJ h2 f hf (Additive.ofMul g) = tlog h (f g) := rfl

end Hom

end DkMath.Lib.NumberTheory.CyclotomicTruncatedLog
