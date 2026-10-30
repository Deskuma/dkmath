/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFiniteKernelGoodReduction
import DkMath.FLT.FreyRationalTwoPTorsion
import DkMath.FLT.FreyStableLineDiscriminantCriterion
import DkMath.FLT.FreyStableLineLocalGlobal
import DkMath.Lib.NumberTheory.FreyLocalTorsionOrderBound

#print "file: DkMath.FLT.FreyHnoSmallGoodPrime"

/-!
# NOTE-032: 小さい良還元素数からの `hno` 一般化

`q = 3` の証明で素数固有なのは、最後の数値比較ではなく、`q` が `2*p` を割らない
ことだけである。この章では `q` を任意の素数へ戻し、`q < p`、`q ≠ 2`、`q ∤ a*b*c`
から同じ Cofixed 直線排除を導く。

証明の教材的な流れは固定されている。

1. Cofixed 直線から整数商モデル上の厳密位数 `2*p` の有理点を得る。
2. 判別式非可除性を `residual_integer_target_discriminant_not_dvd_at_good_prime` から得る。
3. 整数モデルの局所上界 `2*q+1` を適用する。
4. `q < p` から `2*q+1 < 2*p` を得て矛盾する。

ここから既約性と分解群外脱出元は、既存の大域同値へこの `hno` を渡すだけである。
これは一般の `hno` や FLT の閉鎖ではなく、明示した有限素数住所の条件付き結果である。
-/

namespace DkMath.FLT.Frey.Source

open DkMath.Lib.NumberTheory
open DkMath.Lib.NumberTheory.ValuationInertia
open DkMath.Lib.RepresentationTheory
open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open WeierstrassCurve WeierstrassCurve.Affine

noncomputable section

variable {p : ℕ} [Fact p.Prime] (S : Source p)

/--
For a prime `q < p` away from `2` and from the Frey coefficient support,
the Cofixed stable-line obstruction is impossible.

The local torsion estimate is applied to the same integer kernel model that
produced the rational `2*p`-torsion point. The only arithmetic side lemma is
`q ∤ 2*p`, obtained from primality and the strict inequality `q < p`.
-/
theorem residual_hno_of_small_good_prime (hp5 : 5 ≤ p) (hbe : Even S.b)
    {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) (hqp : q < p)
    (hd : ¬ (q : ℤ) ∣ S.a * S.b * S.c) :
    ¬ ∃ L : Submodule (ZMod p) S.ResidualSpace,
      Module.finrank (ZMod p) L = 1 ∧ S.IsGaloisStable L ∧
        IsCofixedOn S.residualRepresentation L := by
  rintro ⟨L, hline, hstable, hcofixed⟩
  obtain ⟨Q, hQord⟩ :=
    S.residual_cofixed_implies_rational_two_p_torsion
      (by omega) hbe L hline hcofixed
  have hΔ := S.residual_integer_target_discriminant_not_dvd_at_good_prime
    (by omega) L hline hcofixed.isStable (q := q) hq2 (by omega) hd
  have hQzero : (2 * p) • Q = 0 := by
    rw [← hQord]
    exact addOrderOf_nsmul_eq_zero Q
  have hn : ¬ (q : ℤ) ∣ ((2 * p : ℕ) : ℤ) := by
    intro hdiv
    have hnat : q ∣ 2 * p := by exact_mod_cast hdiv
    rcases (Nat.Prime.dvd_mul (Fact.out : q.Prime)).mp hnat with hqtwo | hqpdiv
    · exact hq2 ((Nat.dvd_prime Nat.prime_two).mp hqtwo |>.resolve_left
        (Fact.out : q.Prime).ne_one)
    · have heq : q = p :=
        (Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime) (Fact.out : p.Prime)).mp hqpdiv
      omega
  have hbound := addOrderOf_le_two_mul_prime_add_one_of_integral_good
    (q := q) (W := S.residualIntegerKernelModel L hline hcofixed.isStable)
    hΔ (n := 2 * p) hn Q hQzero
  have hle : 2 * p ≤ 2 * q + 1 := by
    simpa [hQord] using hbound
  omega

/-- `q = 3` の既存入口を、一般小素数定理の教材的特殊化として再公開する。 -/
theorem residual_irreducible_of_three_good (hp5 : 5 ≤ p) (hbe : Even S.b)
    (hd : ¬ (3 : ℤ) ∣ S.a * S.b * S.c) :
    S.ResidualIsIrreducible :=
  S.residual_isIrreducible_of_oriented_cofixed_obstruction hp5 hbe
    (S.residual_hno_of_small_good_prime hp5 hbe (q := 3) (by norm_num) (by omega) hd)

/--
Under `a ≡ 7 mod 8`, the same small-good-prime obstruction yields an explicit
existence statement for an escape element outside the decomposition subgroup.
The element is obtained logically from the established `hno` equivalence; no
Galois automorphism is computed or chosen by a separate construction.
-/
theorem residual_escape_outside_decomposition_of_three_good_seven
    (hp5 : 5 ≤ p) (ha8 : S.a % 8 = 7)
    (hd : ¬ (3 : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2) :
    ∃ σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ),
      σ ∉ A.decompositionSubgroup ℚ ∧
      ∃ P : S.ResidualSpace,
        P ∈ S.residualZeroComponent A ∧
          S.residualRepresentation σ P ∉ S.residualZeroComponent A := by
  have hbe : Even S.b := S.b_even_of_a_mod_eight_seven ha8
  exact
    (S.residual_hno_iff_exists_zeroComponent_line_escape_outside_decomposition_of_seven
      hp5 hbe ha8 A hA).mp
      (S.residual_hno_of_small_good_prime hp5 hbe
        (q := 3) (by norm_num) (by omega) hd)

end
end DkMath.FLT.Frey.Source
