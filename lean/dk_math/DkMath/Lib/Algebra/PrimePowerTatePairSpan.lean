/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Algebra.PrimePowerTateReduction
import Mathlib.Tactic.Abel

#print "file: DkMath.Lib.Algebra.PrimePowerTatePairSpan"

/-!
# 互換な二点の第0成分の生成性を全有限段へ持ち上げる

第 n 成分の p^n 倍を第0段で展開し、その差を一つ低い捩れ段へ戻す帰納法。
自由性・有限生成性・Nakayama を仮定しない実際の点の構成である。
-/
namespace DkMath.Lib.Algebra.PrimePowerTateSequence
variable {p : ℕ} {G : Type*} [AddCommGroup G] (v w : Tate p G)
    (hbase : ∀ x : G, p • x = 0 → ∃ a b : ℕ,
      x = a • evaluation 0 v + b • evaluation 0 w)

include hbase in
/-- 同じ二つの互換点列の成分が、各 p 冪捩れ段全体を生成する。 -/
theorem pair_span (n : ℕ) (x : G) (hx : p ^ (n + 1) • x = 0) :
    ∃ a b : ℕ, x = a • evaluation n v + b • evaluation n w := by
  induction n generalizing x with
  | zero =>
    apply hbase x
    simpa only [Nat.zero_add, pow_one] using hx
  | succ n ih =>
    have hk : p • (p ^ (n + 1) • x) = 0 := by
      rw [← mul_nsmul, ← pow_succ]
      exact hx
    obtain ⟨a, b, hab⟩ := hbase _ hk
    let y := x - a • evaluation (n + 1) v - b • evaluation (n + 1) w
    have hy : p ^ (n + 1) • y = 0 := by
      dsimp [y]
      rw [nsmul_sub, nsmul_sub, smul_comm (p ^ (n + 1)) a,
        smul_comm (p ^ (n + 1)) b, evaluation_to_zero, evaluation_to_zero, hab]
      abel
    obtain ⟨c, d, hcd⟩ := ih y hy
    refine ⟨a + p * c, b + p * d, ?_⟩
    calc
      x = y + a • evaluation (n + 1) v + b • evaluation (n + 1) w := by dsimp [y]; abel
      _ = (a + p * c) • evaluation (n + 1) v + (b + p * d) • evaluation (n + 1) w := by
        rw [hcd, add_nsmul, add_nsmul, mul_nsmul, mul_nsmul, compatible, compatible]
        abel

end DkMath.Lib.Algebra.PrimePowerTateSequence
