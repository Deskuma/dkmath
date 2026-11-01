/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyTorsionTowerObstruction
import DkMath.Lib.NumberTheory.EllipticTorsionInertiaAbsorption

#print "file: DkMath.FLT.FreyTorsionInertiaAbsorption"

/-!
# Frey の素数冪捩れ: 局所吸収から最終矛盾の大域入力へ

同じ `Source` の `E[p^m]` 上で、`2`、`p`、および `abc` を割る住所における
慣性変化量が `K` に入ることを仮定する。残る全住所は良還元なので慣性固定となり、
絶対慣性の大域生成定理によって全 Galois 元の変化量が `K` に入る。

前章の最終矛盾で外部入力だった大域固定性 `hfixed` は、ここで局所吸収から
証明される。未実装なのは残る悪い住所での吸収と適切な塔の構成、実際の
Frobenius の関係式であり、それらを完成済みと扱わない。
-/

namespace DkMath.FLT.Frey.Source

open DkMath.Lib.NumberTheory EllipticTorsionRepresentation ValuationInertia
open FreyPrimeValuation

variable {p : ℕ} [Fact p.Prime] (S : Source p)

/-- 全良還元素数を内部供給し、悪い住所の局所吸収だけから大域吸収を導く。
`m=0` も許す。素数冪の位数・点・曲線を変更せず同じ作用で結論する。 -/
theorem prime_power_pointAction_sub_mem_of_bad_inertia
    (m : ℕ) (K : AddSubgroup (Points S.rationalCurve))
    (hbad : ∀ q : ℕ, q.Prime → (q = 2 ∨ q = p ∨ (q : ℤ) ∣ S.a * S.b * S.c) →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), LiesOverPrime A q →
        ∀ τ ∈ inertiaSubgroupIn A ℚ, ∀ y : Points S.rationalCurve,
          p ^ m • y = 0 → pointAction S.rationalCurve τ y - y ∈ K)
    (σ : Field.absoluteGaloisGroup ℚ) {y : Points S.rationalCurve}
    (hy : p ^ m • y = 0) : pointAction S.rationalCurve σ y - y ∈ K := by
  apply pointAction_sub_mem_of_inertia_absorbs_bad_support S.rationalCurve S.curve S.curve_map
    (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) K ?_ σ hy
  intro q hq hsupport A hA τ hτ z hz
  apply hbad q hq ?_ A hA τ hτ z hz
  rcases hsupport with hqn | hΔ
  · have hqp : q ∣ p := hq.dvd_of_dvd_pow hqn
    exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (Fact.out : p.Prime)).mp hqp))
  · by_cases hq2 : q = 2
    · exact Or.inl hq2
    · let : Fact q.Prime := ⟨hq⟩
      exact Or.inr (Or.inr ((prime_dvd_integral_discriminant_iff
        (Nat.Prime.pos (Fact.out : p.Prime)) hq2 S.normalization S.equation).mp hΔ))

/-- 最終捩れ塔矛盾の大域固定性を局所慣性吸収から証明して除去した終点。
利用側に残すのは、同じ塔の底への包含、悪い住所の局所吸収、Frobenius 関係式。
Cofixed 性からこれらを構成する大域算術は引き続き別工程である。 -/
theorem residual_line_tower_inertia_frobenius_impossible
    (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (K : AddSubgroup (Points S.rationalCurve)) {N : ℕ} (hN : 0 < N)
    (hdown : ∀ x ∈ K, p • x = 0 → x ∈ pointSubgroup S.rationalCurve p L)
    (hbad : ∀ q : ℕ, q.Prime → (q = 2 ∨ q = p ∨ (q : ℤ) ∣ S.a * S.b * S.c) →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), LiesOverPrime A q →
        ∀ τ ∈ inertiaSubgroupIn A ℚ, ∀ y : Points S.rationalCurve,
          p ^ N • y = 0 → pointAction S.rationalCurve τ y - y ∈ K)
    (σ : Field.absoluteGaloisGroup ℚ) (ell : ℤ)
    (hCH : ∀ y : Points S.rationalCurve, p ^ N • y = 0 →
      pointAction S.rationalCurve σ (pointAction S.rationalCurve σ y) + ell • y =
        (ell + 1 - (N : ℤ)) • pointAction S.rationalCurve σ y) : False :=
  S.residual_line_tower_frobenius_impossible L hline K hN hdown σ ell
    (fun _y hy => S.prime_power_pointAction_sub_mem_of_bad_inertia N K hbad σ hy) hCH

end DkMath.FLT.Frey.Source
