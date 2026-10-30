/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.FreyLocalTorsionOrderBound

#print "file: DkMathTest.Lib.NumberTheory.FreyLocalTorsionOrderBound"

namespace DkMathTest.Lib.NumberTheory.FreyLocalTorsionOrderBound

open DkMath.Lib.NumberTheory

noncomputable section

noncomputable local instance instDecidableEqFreyLocalTorsionOrderBoundTest :
    DecidableEq ℚ := DkMath.Lib.NumberTheory.instDecidableEqFreyLocalTorsionOrderBound

variable (q : ℕ) [Fact q.Prime]

/-- 教科書回帰例：整数モデルの良還元と `q ∤ n` から局所位数上界を得る。 -/
example (W : WeierstrassCurve ℤ)
    (hΔ : ¬ (q : ℤ) ∣ W.Δ)
    {n : ℕ}
    (hn : ¬ (q : ℤ) ∣ (n : ℤ))
    (Q : (W.map (Int.castRingHom ℚ)).toAffine.Point)
    (hQ : n • Q = 0) :
    addOrderOf Q ≤ 2 * q + 1 :=
  addOrderOf_le_two_mul_prime_add_one_of_integral_good q W hΔ hn Q hQ

#print axioms addOrderOf_le_two_mul_prime_add_one_of_integral_good

end
end DkMathTest.Lib.NumberTheory.FreyLocalTorsionOrderBound
