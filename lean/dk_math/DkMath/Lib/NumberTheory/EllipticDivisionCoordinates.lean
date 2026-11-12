/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Modified for DkMath: local namespaces, current Mathlib API and characteristic-zero specialization.
Adapted from anthropics/fermats-last-theorem, Definitions/Def_WeierstrassCurve_EDSEngine.lean.
-/

import DkMath.Lib.NumberTheory.EllipticDivisionUniversal

#print "file: DkMath.Lib.NumberTheory.EllipticDivisionCoordinates"

/-!
# 有理係数による倍写像の座標分子

x座標の分子φと分母ψ²は既存の除法多項式を使う。y座標の分子ωは
  2ω = ψc − a₁φψ − a₃ψ³
から、有理係数環で2を割って構成する。ψcはMathlibの2補完列であり、ψψc=ψ₂ₙを満たす。
この方法は標数0に限定されるが、一般環上でωの整係数性を証明する工程を省ける。
全ての分子は多項式で、普遍座標環の関係式とともに特殊化できる。
-/
namespace DkMath.Lib.NumberTheory.EllipticDivision
open Polynomial
open scoped Polynomial.Bivariate
namespace WeierstrassCurve
open _root_.WeierstrassCurve
variable {R S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R)
noncomputable section
local macro "C_simp" : tactic =>
  `(tactic| simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])

/-- Mathlibの2補完列を除法多項式へ適用した、ψ₂ₙ/ψₙの多項式表示。 -/
def ψc : ℤ → R[X][Y] := complEDS₂ W.ψ₂ (C W.Ψ₃) (C W.preΨ₄)

open Affine (polynomial polynomialX polynomialY negPolynomial)
lemma C_Ψ₃_eq :
    C W.Ψ₃ = (3 * C X + CC W.a₂) * C W.Ψ₂Sq - polynomialX W ^ 2
      + CC W.a₁ * W.ψ₂ * polynomialX W - CC W.a₁ ^ 2 * polynomial W := by
  simp_rw [Ψ₃, Ψ₂Sq, polynomial, polynomialX, ψ₂, polynomialY, b₂, b₄, b₆, b₈, CC]; C_simp; ring

variable [Algebra ℚ R]

private lemma two_mul_half : (2 : R) * algebraMap ℚ R (1 / 2) = 1 := by
  rw [← map_ofNat (algebraMap ℚ R), ← map_mul]
  norm_num

private lemma halfPoly_mul_two : CC (algebraMap ℚ R (1 / 2)) * (2 : R[X][Y]) = 1 := by
  have h := congrArg (fun x : R => C (C x)) (two_mul_half (R := R))
  simpa only [CC, map_mul, map_ofNat, map_one, mul_comm] using h

/-- 有理係数で定義したy座標の分子。2の逆数を係数として使う。 -/
def ωe (n : ℤ) : R[X][Y] :=
  CC (algebraMap ℚ R (1 / 2)) *
    ((ψc W) n - CC W.a₁ * W.φ n * W.ψ n - CC W.a₃ * W.ψ n ^ 3)

/-- y座標の分子を特徴付ける恒等式。特殊化でも保存される。 -/
lemma two_mul_ωe (n : ℤ) :
    2 * (ωe W) n = (ψc W) n - CC W.a₁ * W.φ n * W.ψ n - CC W.a₃ * W.ψ n ^ 3 := by
  rw [WeierstrassCurve.ωe, ← mul_assoc, mul_comm 2, halfPoly_mul_two, one_mul]

lemma ωe_spec (n : ℤ) :
    2 * (ωe W) n + CC W.a₁ * W.φ n * W.ψ n + CC W.a₃ * W.ψ n ^ 3 = (ψc W) n := by
  rw [two_mul_ωe]
  ring

omit [Algebra ℚ R] in
lemma ψc_spec (n : ℤ) : W.ψ n * (ψc W) n = W.ψ (2 * n) := normEDS_mul_complEDS₂ _ _ _ _

@[simp] lemma ωe_zero : (ωe W) 0 = 1 := by
  simpa [WeierstrassCurve.ωe, ψc] using (halfPoly_mul_two (R := R))

@[simp] lemma ωe_one : (ωe W) 1 = Y := by
  have h := halfPoly_mul_two (R := R)
  calc (ωe W) 1 = (CC (algebraMap ℚ R (1 / 2)) * 2) * Y := by
        simp only [WeierstrassCurve.ωe, ψc, complEDS₂_one, φ_one, ψ_one, one_pow,
          mul_one, ψ₂, Affine.polynomialY, CC, map_add, map_mul, map_ofNat]
        ring
       _ = Y := by rw [h, one_mul]

omit [Algebra ℚ R] in
@[simp] lemma ψc_neg (n : ℤ) : (ψc W) (-n) = (ψc W) n := by simp [ψc]

variable (f : R →+* S)
omit [Algebra ℚ R] in
lemma map_ψc (n : ℤ) : (ψc (W.map f)) n = ((ψc W) n).map (mapRingHom f) := by
  simp only [ψc, ← coe_mapRingHom, map_complEDS₂, map_ψ₂, map_Ψ₃, map_preΨ₄]
  simp only [coe_mapRingHom, map_C]

variable [Algebra ℚ S]
lemma map_ωe (n : ℤ) : (ωe (W.map f)) n = ((ωe W) n).map (mapRingHom f) := by
  have hq : Polynomial.map (mapRingHom f) (algebraMap ℚ R[X][Y] (1 / 2)) =
      algebraMap ℚ S[X][Y] (1 / 2) :=
    RingHom.map_rat_algebraMap (Polynomial.mapRingHom (mapRingHom f)) (1 / 2)
  simp only [WeierstrassCurve.ωe, map_ψc, map_φ, map_ψ, map_a₁, map_a₃, CC,
    Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_C,
    coe_mapRingHom, Polynomial.map_C, RingHom.map_rat_algebraMap, hq]

end
end WeierstrassCurve
end DkMath.Lib.NumberTheory.EllipticDivision
