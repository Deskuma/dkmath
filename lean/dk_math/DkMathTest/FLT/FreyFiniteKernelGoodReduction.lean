/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFiniteKernelGoodReduction

#print "file: DkMathTest.FLT.FreyFiniteKernelGoodReduction"

namespace DkMathTest.FLT.FreyFiniteKernelGoodReduction

open DkMath.FLT.Frey
open DkMath.FLT.Frey.Source
open DkMath.Lib.RepresentationTheory

noncomputable section

variable {p : ℕ} [Fact p.Prime] (S : Source p)

/-- 教科書回帰例：良い奇素数で整数標的判別式の非可除性を直接取り出す。 -/
example (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    (hs : IsStable S.residualRepresentation L) {q : ℕ} [Fact q.Prime]
    (hq2 : q ≠ 2) (hqp : q ≠ p) (hd : ¬ (q : ℤ) ∣ S.a * S.b * S.c) :
    ¬ (q : ℤ) ∣ (S.residualIntegerKernelModel L hl hs).Δ :=
  S.residual_integer_target_discriminant_not_dvd_at_good_prime
    hp2 L hl hs hq2 hqp hd

#print axioms residual_integer_target_discriminant_not_dvd_at_good_prime

end
end DkMathTest.FLT.FreyFiniteKernelGoodReduction
