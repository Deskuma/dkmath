/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Algebra.BinomTail
import Mathlib.Data.ZMod.Basic
import Lean.Util.CollectAxioms

#print "file: DkMathTest.Lib.Algebra.BinomTail"

/-!
# GN-LIB-003a: 尾項と正性の条件を保つ回帰

Lib所有者だけから旧namespaceの5補題を使用する。
尾項分解は零因子を持つ環でも成立するが、厳密な正性は正の自然数で使う。
次数0・1、零座標、標数2、別の底の平方を境界として検査する。
-/

namespace DkMathTest.Lib.Algebra.BinomTail

open DkMath.Algebra.BinomTail

/-- 尾項の存在形は一般半環でn=2から使える。 -/
example {R : Type*} [CommSemiring R] (a b : R) :
    ∃ H : R, (a + b) ^ 2 = b ^ 2 + (2 : R) * b ^ (2 - 1) * a + a ^ 2 * H :=
  add_pow_tail_exists a b (by decide)

/-- a=0でも約分せず、そのまま加法恒等式を得る。 -/
example {R : Type*} [CommSemiring R] (b : R) {n : ℕ} (hn : 2 ≤ n) :
    ∃ H : R, (0 + b) ^ n = b ^ n + (n : R) * b ^ (n - 1) * 0 + 0 ^ 2 * H :=
  add_pow_tail_exists 0 b hn

/-- 零因子2を持つZMod 4でも存在形を失わない。 -/
example : ∃ H : ZMod 4, (2 + 1) ^ 4 = 1 ^ 4 + (4 : ZMod 4) * 1 ^ (4 - 1) * 2 + 2 ^ 2 * H :=
  add_pow_tail_exists 2 1 (by decide)

/-- 負の座標を許す環の等式と、自然数の正性は別に扱う。 -/
example : ∃ H : ℤ, (-3 + 2) ^ 3 = 2 ^ 3 + (3 : ℤ) * 2 ^ (3 - 1) * (-3) + (-3) ^ 2 * H :=
  add_pow_tail_exists (-3) 2 (by decide)

example : 3 ^ 2 ∣ ((3 + 5) ^ 2 - 5 ^ 2 - 2 * 5 ^ (2 - 1) * 3 : ℕ) :=
  binom_tail_nat_dvd 3 5 (by decide)

/-- 0が割るのは0であり、零座標を正性の仮定へすり替えない。 -/
example : 0 ^ 2 ∣ ((0 + 7) ^ 4 - 7 ^ 4 - 4 * 7 ^ (4 - 1) * 0 : ℕ) :=
  binom_tail_nat_dvd 0 7 (by decide)

example : 3 ^ 2 ∣ ((3 + 0) ^ 3 - 0 ^ 3 - 3 * 0 ^ (3 - 1) * 3 : ℕ) :=
  binom_tail_nat_dvd 3 0 (by decide)

/-- 具体的な切り捨て差も独立に計算する。 -/
example : ((3 + 5) ^ 3 - 5 ^ 3 - 3 * 5 ^ (3 - 1) * 3 : ℕ) = 162 := by decide

/-- 交差項の正性は二乗から始まる。 -/
example : (2 ^ (0 + 2) + 3 ^ (0 + 2) : ℕ) < (2 + 3) ^ (0 + 2) :=
  add_pow_gt_sum_pows_nat 2 3 (by decide) (by decide) 0

/-- 次数37でも二項係数の全展開を要求せず、一般定理を使える。 -/
example : (1 ^ 37 + 1 ^ 37 : ℕ) < (1 + 1) ^ 37 :=
  add_pow_gt_sum_pows_nat_of_two_le 1 1 (by decide) (by decide) (by decide)

example : ((2 + 3) ^ 4 : ℕ) ≠ 2 ^ 4 + 3 ^ 4 :=
  add_pow_ne_sum_pows_nat_of_two_le 2 3 (by decide) (by decide) (by decide)

/-- 正座標でも次数0・1には厳密不等式を拡張できない。 -/
example : ¬(1 ^ 0 + 1 ^ 0 < (1 + 1) ^ 0 : Prop) := by decide

example : ((2 + 3) ^ 1 : ℕ) = 2 ^ 1 + 3 ^ 1 := by decide

/-- 正次数でも零座標なら等号となる。 -/
example : ((0 + 7) ^ 37 : ℕ) = 0 ^ 37 + 7 ^ 37 := by simp

example : ((5 + 0) ^ 2 : ℕ) = 5 ^ 2 + 0 ^ 2 := by simp

/-- 標数2では交差項が消える。一般半環に自然数の厳密正性を持ち込まない。 -/
example : ((1 + 1) ^ 2 : ZMod 2) = 1 ^ 2 + 1 ^ 2 := by decide

/-- 底a+bでの厳密不等式は、別の底zの完全冪を排除しない。 -/
example : (3 ^ 2 + 4 ^ 2 : ℕ) < (3 + 4) ^ 2 ∧ 3 ^ 2 + 4 ^ 2 = (5 : ℕ) ^ 2 :=
  ⟨add_pow_gt_sum_pows_nat_of_two_le 3 4 (by decide) (by decide) (by decide), by decide⟩

end DkMathTest.Lib.Algebra.BinomTail

open Lean Elab Command in
run_cmd do
  let names : Array Name := #[
    ``DkMath.Algebra.BinomTail.add_pow_tail_exists,
    ``DkMath.Algebra.BinomTail.binom_tail_nat_dvd,
    ``DkMath.Algebra.BinomTail.add_pow_gt_sum_pows_nat,
    ``DkMath.Algebra.BinomTail.add_pow_gt_sum_pows_nat_of_two_le,
    ``DkMath.Algebra.BinomTail.add_pow_ne_sum_pows_nat_of_two_le]
  for n in names do
    for ax in ← Lean.collectAxioms n do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {n}: {ax}"
  logInfo m!"GN-LIB-003a: {names.size} promoted declarations use standard logical axioms only."
