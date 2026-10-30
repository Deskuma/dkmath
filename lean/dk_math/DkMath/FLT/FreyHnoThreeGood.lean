/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFiniteKernelGoodReduction
import DkMath.FLT.FreyRationalTwoPTorsion
import DkMath.Lib.NumberTheory.FreyLocalTorsionOrderBound

#print "file: DkMath.FLT.FreyHnoThreeGood"

/-!
# NOTE-032: `q = 3` の良還元から得る条件付き hno

この章は、Cofixed な一次元核から作られる有理 `2 * p` 捩れ点を、整数商モデルの
`3` 上の良還元へ輸送する教科書的な合成である。`3 ∤ a*b*c` を仮定すると、既存の
整数判別式補題が `3` 上の良還元を与え、局所トーション次数上界はその点の位数を
`2*3+1` 以下に抑える。一方、`p ≥ 5` なら `2*p > 7` なので矛盾する。

従ってここで閉じるのは、

`3 ∤ a*b*c  ⟹  hno`

という条件付きの残余表現入口である。一般の `hno`、全ての Frey 住所の処理、または
FLT の結論はこの定理の主張に含めない。
-/

namespace DkMath.FLT.Frey.Source

open DkMath.Lib.NumberTheory
open DkMath.Lib.RepresentationTheory
open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open WeierstrassCurve WeierstrassCurve.Affine

noncomputable section

variable {p : ℕ} [Fact p.Prime] (S : Source p)

/--
If `p ≥ 5`, `Even S.b`, and `3 ∤ a*b*c`, then no one-dimensional stable
cofixed residual line can exist.

The proof is intentionally short at the top level: the rational-torsion
construction supplies a point of exact order `2*p`; the integral good-reduction
bridge supplies the arithmetic hypothesis for the local bound; and the prime
`3` makes that bound equal to `7`. This is the textbook decomposition of the
`q = 3` obstruction, with no appeal to Mazur's classification.
-/
theorem residual_hno_of_three_good (hp5 : 5 ≤ p) (hbe : Even S.b)
    (hd : ¬ (3 : ℤ) ∣ S.a * S.b * S.c) :
    ¬ ∃ L : Submodule (ZMod p) S.ResidualSpace,
      Module.finrank (ZMod p) L = 1 ∧ S.IsGaloisStable L ∧
        IsCofixedOn S.residualRepresentation L := by
  rintro ⟨L, hline, hstable, hcofixed⟩
  obtain ⟨Q, hQord⟩ :=
    S.residual_cofixed_implies_rational_two_p_torsion
      (by omega) hbe L hline hcofixed
  have hΔ := S.residual_integer_target_discriminant_not_dvd_at_good_prime
    (by omega) L hline hcofixed.isStable (q := 3) (by norm_num) (by omega) hd
  have hQzero : (2 * p) • Q = 0 := by
    rw [← hQord]
    exact addOrderOf_nsmul_eq_zero Q
  have hn : ¬ (3 : ℤ) ∣ ((2 * p : ℕ) : ℤ) := by
    intro hdiv
    have hnat : 3 ∣ 2 * p := by exact_mod_cast hdiv
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp hnat with htwo | hpdiv
    · norm_num at htwo
    · have heq : 3 = p :=
        (Nat.prime_dvd_prime_iff_eq Nat.prime_three (Fact.out : p.Prime)).mp hpdiv
      omega
  have hbound := addOrderOf_le_two_mul_prime_add_one_of_integral_good
    (q := 3) (W := S.residualIntegerKernelModel L hline hcofixed.isStable)
    hΔ (n := 2 * p) hn Q hQzero
  have hle : 2 * p ≤ 2 * 3 + 1 := by
    simpa [hQord] using hbound
  omega

end
end DkMath.FLT.Frey.Source
