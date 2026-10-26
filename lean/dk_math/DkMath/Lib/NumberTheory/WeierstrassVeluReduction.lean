/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Invariant correction identities adapted from
P2M/Sol/S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_c4_c6_discriminant_of_nodal.lean,
blob fbe8b46b385ec6f97df009c8cb22a7e62c104cc8.
Modified: indexed polynomial models, derivative-based singular vanishing and arbitrary rings.
-/

import DkMath.Lib.NumberTheory.WeierstrassVeluPolynomial
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.Tactic.LinearCombination

#print "file: DkMath.Lib.NumberTheory.WeierstrassVeluReduction"

/-!
# Vélu補正の剰余特異点での消滅と、小さい標数での不変量

[DkMath.Lib] 特異点ではt=a₁F_y−2F_x=0、w=F_y²+xt=0となる。
従って全代表が特異点へ写れば、剰余の五係数は源と完全に一致する。
c₄の補正は240T、c₆の補正は504b₂T+6048Uである。
このため標数2,3,5では核の還元の型に依らずc₄の補正が消える。
滑らかな核の一般標数での節点商公式は、本所有者の結論に含めない。
-/
namespace DkMath.Lib.NumberTheory.WeierstrassVeluPolynomial
open WeierstrassCurve WeierstrassCurve.Affine
open scoped BigOperators

/-- [DkMath.Lib] 特異な曲線上の点では二つのモーメントが零。2や3を約分しない。 -/
theorem moments_eq_zero_of_singular {k : Type*} [Field k] (W : WeierstrassCurve k) {x y : k}
    (he : W.toAffine.Equation x y) (hs : ¬ W.toAffine.Nonsingular x y) :
    momentT W x = 0 ∧ momentW W x y = 0 := by
  rw [nonsingular_iff'] at hs
  push Not at hs
  obtain ⟨hx, hy⟩ := hs he
  have ht : momentT W x = 0 := by
    simp only [momentT, b₂, b₄]
    linear_combination W.a₁ * hy - 2 * hx
  refine ⟨ht, ?_⟩
  simp only [momentW, ht, hy, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero]

/-- [DkMath.Lib] 全代表が特異な曲線上の点なら、多項式係数モデルは源と同一。 -/
theorem polynomialModel_eq_of_singular {k ι : Type*} [Field k]
    (W : WeierstrassCurve k) (s : Finset ι) (x y : ι → k)
    (hs : ∀ i ∈ s, W.toAffine.Equation (x i) (y i) ∧ ¬ W.toAffine.Nonsingular (x i) (y i)) :
    polynomialModel W s x y = W := by
  have ht : (∑ i ∈ s, momentT W (x i)) = 0 := Finset.sum_eq_zero (fun i hi =>
    (moments_eq_zero_of_singular W (hs i hi).1 (hs i hi).2).1)
  have hw : (∑ i ∈ s, momentW W (x i) (y i)) = 0 := Finset.sum_eq_zero (fun i hi =>
    (moments_eq_zero_of_singular W (hs i hi).1 (hs i hi).2).2)
  ext <;> simp [polynomialModel, ht, hw]

/-- [DkMath.Lib] 同じ二つのモーメント和によるc₄,c₆の正確な補正式。任意の可換環で成立。 -/
theorem polynomialModel_c_invariants {R ι : Type*} [CommRing R]
    (W : WeierstrassCurve R) (s : Finset ι) (x y : ι → R) :
    (polynomialModel W s x y).c₄ = W.c₄ + 240 * ∑ i ∈ s, momentT W (x i) ∧
      (polynomialModel W s x y).c₆ = W.c₆ + 504 * W.b₂ * (∑ i ∈ s, momentT W (x i)) +
        6048 * ∑ i ∈ s, momentW W (x i) (y i) := by
  have hb := polynomialModel_b_invariants W s x y
  simp only [c₄, c₆, hb.1, hb.2.1, hb.2.2]
  constructor <;> ring

/-- [DkMath.Lib] 240が零となる環では、任意の添字と座標についてc₄が保持される。
この結論だけから判別式の零性や良還元を推測しない。 -/
theorem polynomialModel_c4_eq_of_240_eq_zero {R ι : Type*} [CommRing R]
    (W : WeierstrassCurve R) (s : Finset ι) (x y : ι → R) (h240 : (240 : R) = 0) :
    (polynomialModel W s x y).c₄ = W.c₄ := by
  rw [(polynomialModel_c_invariants W s x y).1, h240, zero_mul, add_zero]

end DkMath.Lib.NumberTheory.WeierstrassVeluPolynomial
