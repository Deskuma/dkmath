/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Modified for DkMath: local namespaces, current Mathlib API and characteristic-zero specialization.
Adapted from anthropics/fermats-last-theorem, Definitions/Def_WeierstrassCurve_EDSEngine.lean.
-/

import DkMath.Lib.NumberTheory.EllipticDivisionCoordinates

#print "file: DkMath.Lib.NumberTheory.EllipticDivisionMultiplication"

/-!
# 除法多項式の分子と、実際の点の倍写像を結ぶ

普遍点上でnet恒等式を加法公式へ翻訳し、φ/ψ²とω/ψ³が整数倍の座標であることを示す。
普遍座標環へ戻して多項式等式とし、任意の標数0の曲線上の点へ評価する。
Jacobian表示を経由するため、特殊化でψが零となる場合にも無限遠点を正しく扱える。
最後に実際の点群で [n]P=O と ψₙ(P)=0 の同値を得る。
有限性にはこの同値の前向きだけを使い、根の正確な個数や分離性は要求しない。
-/
namespace DkMath.Lib.NumberTheory.EllipticDivision
section PortEllSequenceZSMul

open scoped Polynomial.Bivariate

namespace WeierstrassCurve
open _root_.WeierstrassCurve

open Polynomial

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra ℚ R] [Algebra ℚ S] (W : WeierstrassCurve R) (f : R →+* S)

noncomputable section

variable {x y : R}

namespace Univ

lemma evalEval_ψ₂ : W.ψ₂.evalEval x y = polyEval W x y curve.ψ₂ := by
  simp_rw [polyEval_apply, ← map_ψ₂, map_specialize]

lemma evalEval_Ψ₃ : (C W.Ψ₃).evalEval x y = polyEval W x y (C curve.Ψ₃) := by
  simp_rw [polyEval_apply, map_C, coe_mapRingHom, ← map_Ψ₃, map_specialize]

lemma evalEval_preΨ₄ : (C W.preΨ₄).evalEval x y = polyEval W x y (C curve.preΨ₄) := by
  simp_rw [polyEval_apply, map_C, coe_mapRingHom, ← map_preΨ₄, map_specialize]

variable {m n : ℤ}

lemma evalEval_ψ : (W.ψ n).evalEval x y = polyEval W x y (curve.ψ n) := by
  simp_rw [polyEval_apply, ← map_ψ, map_specialize]

lemma evalEval_φ : (W.φ n).evalEval x y = polyEval W x y (curve.φ n) := by
  simp_rw [polyEval_apply, ← map_φ, map_specialize]

lemma evalEval_ωe : ((ωe W) n).evalEval x y =  polyEval W x y ((ωe curve) n) := by
  simp_rw [polyEval_apply, ← map_ωe, map_specialize]

lemma normEDS_rat_two_three_two (n : ℤ) : normEDS (2 : ℚ) 3 2 n = n := by
  have h := congrArg (Int.castRingHom ℚ) (congrFun normEDS_two_three_two n)
  simpa only [map_normEDS, map_ofNat, id_eq, Int.coe_castRingHom] using h

lemma complEDS₂_rat_two_three_two (n : ℤ) : complEDS₂ (2 : ℚ) 3 2 n = 2 := by
  obtain rfl | hn := eq_or_ne n 0
  · norm_num [complEDS₂]
  have h := normEDS_mul_complEDS₂ (2 : ℚ) 3 2 n
  simp only [normEDS_rat_two_three_two, Int.cast_mul, Int.cast_ofNat] at h
  have hne : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  exact (mul_left_cancel₀ hne) (h.trans (mul_comm _ _))

open _root_.WeierstrassCurve (ψ φ)
open WeierstrassCurve (ωe)

lemma cusp_ψ₂ : cusp.ψ₂ = 2 * Y := by
  simp [cusp, ψ₂, Affine.polynomialY, map_ofNat]

lemma cusp_Ψ₃ : cusp.Ψ₃ = 3 * X ^ 4 := by simp [cusp, Ψ₃, b₂, b₄, b₆, b₈]
lemma cusp_preΨ₄ : cusp.preΨ₄ = 2 * X ^ 6 := by simp [cusp, preΨ₄, b₂, b₄, b₆, b₈]

lemma polyEval_cusp_ψ : polyEval cusp 1 1 (curve.ψ n) = n := by
  rw [ψ, map_normEDS, ← evalEval_ψ₂, ← evalEval_Ψ₃, ← evalEval_preΨ₄, cusp_ψ₂, cusp_Ψ₃, cusp_preΨ₄]
  simp [evalEval, normEDS_rat_two_three_two]

lemma polyEval_cusp_φ : polyEval cusp 1 1 (curve.φ n) = 1 := by
  simp_rw [φ, map_sub, map_mul, map_pow, polyEval_cusp_ψ, polyEval]
  simp only [coe_eval₂RingHom, eval₂_C, eval₂_X]
  push_cast
  ring

lemma polyEval_cusp_ψc : polyEval cusp 1 1 ((ψc curve) n) = 2 := by
  rw [ψc, map_complEDS₂, ← evalEval_ψ₂, ← evalEval_Ψ₃, ← evalEval_preΨ₄]
  simp [cusp_ψ₂, cusp_Ψ₃, cusp_preΨ₄, evalEval, complEDS₂_rat_two_three_two]

lemma polyEval_cusp_ωe : polyEval cusp 1 1 ((ωe curve) n) = 1 := by
  have := congr(polyEval cusp 1 1 $((two_mul_ωe curve) n))
  simp_rw [map_sub, map_mul, map_ofNat, polyEval_cusp_ψc] at this
  simpa [cusp, polyEval, specialize, curve] using this

abbrev ψᵤ (n : ℤ) : Univ.Field := polyToField (curve.ψ n)

lemma ψᵤ_eq_normEDS :
    ψᵤ = normEDS
      (polyToField curve.ψ₂) (polyToField <| C curve.Ψ₃) (polyToField <| C curve.preΨ₄) := by
  ext; rw [← map_normEDS]; rfl

lemma isEllSequence_ψᵤ : IsEllSequence' ψᵤ := by rw [ψᵤ_eq_normEDS]; exact IsEllSequence'.normEDS
lemma net_ψᵤ (p q r s) : EllSequence.net ψᵤ p q r s = 0 := by rw [ψᵤ_eq_normEDS]; apply net_normEDS

/-- 普遍点では非零次数の分母は消えない。尖点への特殊化が整数nを返すためである。 -/
lemma ψᵤ_ne_zero (h0 : n ≠ 0) : ψᵤ n ≠ 0 := fun h ↦ by
  rw [ψᵤ, polyToField_apply, map_eq_zero_iff _ (IsFractionRing.injective _ _)] at h
  replace h := congr(ringEval cusp_equation_one_one $h)
  rw [ringEval_mk, polyEval_cusp_ψ, map_zero] at h
  exact h0 (by exact_mod_cast h)

lemma polyToField_φ_ne_zero : polyToField (curve.φ n) ≠ 0 := fun h ↦ by
  rw [polyToField_apply, map_eq_zero_iff _ (IsFractionRing.injective _ _)] at h
  replace h := congr(ringEval cusp_equation_one_one $h)
  rw [ringEval_mk, polyEval_cusp_φ, map_zero] at h
  exact one_ne_zero h

lemma polyToField_ψ₂Sq : polyToField (C curve.Ψ₂Sq) = ψᵤ 2 ^ 2 := by
  rw [← map_pow, ψ_two, ψ₂_sq, map_add, map_mul, polyToField_polynomial, mul_zero, add_zero]

namespace Affine

variable (n)

def smulX : Univ.Field := polyToField (curve.φ n) / (ψᵤ n) ^ 2

def smulY : Univ.Field := polyToField ((ωe curve) n) / (ψᵤ n) ^ 3
variable {n}

@[simp] lemma smulX_zero : smulX 0 = 0 := by simp [smulX, ψᵤ]
@[simp] lemma smulY_zero : smulY 0 = 0 := by simp [smulY, ψᵤ]
@[simp] lemma smulX_one : smulX 1 = polyToField (C X) := by simp [smulX, ψᵤ]
@[simp] lemma smulY_one : smulY 1 = polyToField Y := by simp [smulY, ψᵤ]

lemma smulX_eq (hn : n ≠ 0) :
    smulX n = smulX 1 - ψᵤ (n + 1) * ψᵤ (n - 1) / (ψᵤ n) ^ 2 := by
  rw [smulX, smulX_one, φ, map_sub, sub_div, map_mul, map_pow, mul_div_cancel_right₀, map_mul]
  exact pow_ne_zero _ (ψᵤ_ne_zero hn)

lemma smulX_two : smulX 2 = smulX 1 - ψᵤ 3 / (ψᵤ 2) ^ 2 := by
  simp [smulX_eq two_ne_zero, ψᵤ]

lemma smulX_sub_smulX (hm : m ≠ 0) (hn : n ≠ 0) :
    smulX m - smulX n = (ψᵤ (n + m) * ψᵤ (n - m)) / (ψᵤ n * ψᵤ m) ^ 2 := by
  rw [smulX_eq hm, smulX_eq hn, sub_sub_sub_cancel_left, div_sub_div]
  · rw [mul_pow]; congr; convert (isEllSequence_ψᵤ n m 1).symm using 1
    · ring
    · simp [ψᵤ]
  all_goals exact pow_ne_zero _ (ψᵤ_ne_zero <| by assumption)

lemma smulX_sub_sub_smulX_add (add_ne : n + m ≠ 0) (sub_ne : n - m ≠ 0) :
    smulX (n - m) - smulX (n + m) = (ψᵤ (2 * n) * ψᵤ (2 * m)) / (ψᵤ (n + m) * ψᵤ (n - m)) ^ 2 := by
  rw [smulX_sub_smulX sub_ne add_ne]; ring_nf

lemma smulX_neg : smulX (-n) = smulX n := by simp_rw [smulX, φ_neg, ψᵤ, ψ_neg, ← map_pow, neg_sq]

lemma smulX_ne_zero (h0 : n ≠ 0) : smulX n ≠ 0 :=
  div_ne_zero polyToField_φ_ne_zero (pow_ne_zero _ <| ψᵤ_ne_zero h0)

lemma smulX_ne_smulX (ne : m ≠ n) (ne_neg : m ≠ -n) : smulX m ≠ smulX n := by
  obtain rfl | hm := eq_or_ne m 0
  · rw [smulX_zero]; exact (smulX_ne_zero ne.symm).symm
  obtain rfl | hn := eq_or_ne n 0
  · rw [smulX_zero]; exact smulX_ne_zero ne
  rw [← sub_ne_zero, smulX_sub_smulX hm hn]
  rw [ne_comm, ← sub_ne_zero] at ne
  rw [Ne, ← add_eq_zero_iff_eq_neg, add_comm] at ne_neg
  refine div_ne_zero (mul_ne_zero ?_ ?_) (pow_ne_zero _ <| mul_ne_zero ?_ ?_) <;>
    apply ψᵤ_ne_zero <;> assumption

lemma smulX_eq_smulX_iff : smulX m = smulX n ↔ m = n ∨ m = -n := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · contrapose! h; exact smulX_ne_smulX h.1 h.2
  · rintro (rfl|rfl); exacts [rfl, smulX_neg]

private lemma smulY_sub_negY_aux {F} [Field F] {a₁ a₃ x y z : F} (h0 : z ≠ 0) :
    y / z ^ 3 - (-(y / z ^ 3) - a₁ * (x / z ^ 2) - a₃) =
      z * (2 * y + a₁ * x * z + a₃ * z ^ 3) / z ^ 4 := by
  field_simp; ring

lemma smulY_sub_negY (h0 : n ≠ 0) :
    smulY n - pointedCurve.toAffine.negY (smulX n) (smulY n) = ψᵤ (2 * n) / (ψᵤ n) ^ 4 := by
  simp_rw [Affine.negY, pointedCurve_a₁, pointedCurve_a₃, smulX, smulY, ψᵤ, ← ψc_spec, ← ωe_spec,
    map_mul, map_add, map_mul, map_pow, map_ofNat]
  exact smulY_sub_negY_aux (ψᵤ_ne_zero h0)

lemma smulY_one_sub_negY :
    smulY 1 - pointedCurve.toAffine.negY (smulX 1) (smulY 1) = ψᵤ 2 := by
  rw [smulY_sub_negY one_ne_zero, mul_one, ψᵤ, ψᵤ, ψ_one, map_one, one_pow, div_one]

lemma smulY_one_ne_negY : smulY 1 ≠ pointedCurve.toAffine.negY (smulX 1) (smulY 1) := by
  rw [← sub_ne_zero, smulY_one_sub_negY]; exact ψᵤ_ne_zero two_ne_zero

def slopeOne : Univ.Field :=
  pointedCurve.toAffine.slope (smulX 1) (smulX 1) (smulY 1) (smulY 1)

lemma slopeOne_eq_neg_div : slopeOne = -polyToField curve.polynomialX / ψᵤ 2 := by
  rw [slopeOne, Affine.slope_of_Y_ne rfl smulY_one_ne_negY, smulY_one_sub_negY, Affine.polynomialX]
  congr
  simp [algebraMap_field_eq_comp, Polynomial.algebraMap_apply, map_ofNat]

private lemma addX_smul_one_smul_one_aux {F} [Field F] {a₁ a₂ x dx dy : F} (h0 : dy ≠ 0) :
    (-dx / dy) ^ 2 + a₁ * (-dx / dy) - a₂ - x - x - x =
      (dx ^ 2 - a₁ * dx * dy - (3 * x + a₂) * dy ^ 2) / dy ^ 2 := by
  field_simp; ring

lemma addX_smul_one_smul_one :
    pointedCurve.toAffine.addX (smulX 1) (smulX 1) slopeOne = smulX 2 := .symm <| by
  rw [smulX_two, Affine.addX, sub_eq_neg_add, ← eq_sub_iff_add_eq, ← neg_div _ (polyToField _),
    slopeOne_eq_neg_div, addX_smul_one_smul_one_aux (ψᵤ_ne_zero two_ne_zero)]
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, polyToField_ψ₂Sq, ψᵤ,
    ψ_two, ψ_three, C_Ψ₃_eq, polyToField_polynomial, pointedCurve_a₁, pointedCurve_a₂, smulX_one]
  ring

private lemma addY_smul_one_smul_one_aux {F} [Field F] {a₁ a₃ dx dy x y ψ₃ t : F} (h0 : dy ≠ 0) :
    ((a₁ * dy - dx) * ψ₃ + 0 * t + (-y - (a₁ * x + a₃)) * dy ^ 3) / dy ^ 3 =
      -(-dx / dy * (x - ψ₃ / dy ^ 2 - x) + y) - a₁ * (x - ψ₃ / dy ^ 2) - a₃ := by
  field_simp; ring

lemma ωe_two_formula : (ωe curve) 2 =
    (CC curve.a₁ * curve.polynomialY - curve.polynomialX) * C curve.Ψ₃ +
      4 * curve.polynomial * (2 * curve.polynomial + C curve.Ψ₂Sq) +
      curve.negPolynomial * curve.ψ₂ ^ 3 := by
  apply mul_left_cancel₀ Poly.two_ne_zero
  rw [two_mul_ωe]
  simp only [ψc, complEDS₂_two, φ_two, ψ_two, preΨ₄, Ψ₃, Ψ₂Sq, ψ₂,
    Affine.polynomialY, Affine.polynomialX, Affine.polynomial, Affine.negPolynomial,
    b₂, b₄, b₆, b₈, curve, CC]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  ring

open EllSequence in
lemma addY_smul_one_smul_one :
    pointedCurve.toAffine.addY (smulX 1) (smulX 1) (smulY 1) slopeOne = smulY 2 := .symm <| by
  rw [smulY, ωe_two_formula, Affine.addY,
    Affine.negAddY, addX_smul_one_smul_one, smulX_two, Affine.negY, Affine.negPolynomial,
    slopeOne_eq_neg_div, ← ψ₂, ← ψ_two, smulX_one, smulY_one, ψᵤ, ψᵤ, ψ_three]
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, polyToField_polynomial, mul_zero]
  exact addY_smul_one_smul_one_aux (ψᵤ_ne_zero two_ne_zero)

private lemma smulY_neg_aux {F} [Field F] {a₁ a₃ x y z : F} (hz : z ≠ 0) :
    (y + a₁ * x * z + a₃ * z ^ 3) / (-z) ^ 3 = -(y / z ^ 3) - a₁ * (x / z ^ 2) - a₃ := by
  rw [neg_pow]; field_simp; ring

open Polynomial (CC) in
lemma ωe_neg' : (ωe curve) (-n) =
    (ωe curve) n + CC curve.a₁ * curve.φ n * curve.ψ n + CC curve.a₃ * curve.ψ n ^ 3 := by
  rw [← mul_cancel_left_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero Poly.two_ne_zero)]
  simp_rw [left_distrib, two_mul_ωe, ψc_neg, ψ_neg, φ_neg]; ring

lemma smulY_neg (h0 : n ≠ 0) :
    smulY (-n) = pointedCurve.toAffine.negY (smulX n) (smulY n) := by
  simp only [Affine.negY, pointedCurve_a₁, pointedCurve_a₃, smulX, smulY, ψ_neg, ωe_neg',
    map_add, map_neg, map_mul, map_pow, ψᵤ]
  exact smulY_neg_aux (ψᵤ_ne_zero h0)

private lemma smulX_add_aux {F} [Field F] {m n m₂ n₂ a s : F}
    (hm : m ≠ 0) (hn : n ≠ 0) (ha : a ≠ 0) (hs : s ≠ 0) :
    n₂ / n ^ 4 * (m₂ / m ^ 4) / (a * s / (n * m) ^ 2) ^ 2 = n₂ * m₂ / (a * s) ^ 2 := by
  field_simp

lemma smulX_add (hm : m ≠ 0) (hn : n ≠ 0) (add_ne : n + m ≠ 0) (sub_ne : n - m ≠ 0) :
    let ψ₂ x y := y - pointedCurve.toAffine.negY x y
    smulX (n + m) = smulX (n - m) -
      ψ₂ (smulX n) (smulY n) * ψ₂ (smulX m) (smulY m) / (smulX m - smulX n) ^ 2 := by
  rw [eq_sub_iff_add_eq, ← eq_sub_iff_add_eq', smulX_sub_sub_smulX_add add_ne sub_ne]
  simp_rw [smulY_sub_negY hm, smulY_sub_negY hn, smulX_sub_smulX hm hn]
  apply smulX_add_aux <;> apply ψᵤ_ne_zero <;> assumption

private lemma smulY_add_sub_negY_aux {F} [Field F] {m n m₂ n₂ a s am an : F}
    (hm : m ≠ 0) (hn : n ≠ 0) (ha : a ≠ 0) (hs : s ≠ 0) :
    (m₂ / m ^ 4 * (an * m / (a * n) ^ 2) - n₂ / n ^ 4 * (am * n / (a * m) ^ 2))
      / (a * s / (n * m) ^ 2)
      = (an * m₂ * n - am * n₂ * m) * a / (s * n * m) / a ^ 4 := by
  field_simp

lemma smulY_add_sub_negY (hm : m ≠ 0) (hn : n ≠ 0) (add_ne : n + m ≠ 0) (sub_ne : n - m ≠ 0) :
    let ψ₂ x y := y - pointedCurve.toAffine.negY x y
    ψ₂ (smulX (n + m)) (smulY (n + m)) =
      (ψ₂ (smulX m) (smulY m) * (smulX n - smulX (n + m))
        - ψ₂ (smulX n) (smulY n) * (smulX m - smulX (n + m))) / (smulX m - smulX n) := by
  simp_rw [smulY_sub_negY add_ne, smulY_sub_negY hm, smulY_sub_negY hn, smulX_sub_smulX hn add_ne,
    smulX_sub_smulX hm add_ne, smulX_sub_smulX hm hn, add_sub_cancel_left, add_sub_cancel_right]
  rw [smulY_add_sub_negY_aux]
  · congr; rw [eq_div_iff]
    · linear_combination (norm := ring_nf) (EllSequence.net_add_sub_iff _ n m).mp (net_ψᵤ _ _ _ _)
    apply_rules [mul_ne_zero, ψᵤ_ne_zero]
  all_goals apply ψᵤ_ne_zero; assumption

open Affine.Point

open _root_.WeierstrassCurve.Affine in
instance : AddGroup (curve⟮Univ.Field⟯) := inferInstance

/-- 普遍点の整数倍が座標有理式に一致する。加法関係を用いた帰納法。 -/
theorem zsmul_point_eq_smulX_smulY : n ≠ 0 →
    ∃ h : Affine.Nonsingular curveField (smulX n) (smulY n),
      n • Affine.point = .some (smulX n) (smulY n) h := by
  induction n using Int.negInduction with
  | nat n =>
    refine n.strong_induction_on fun n ih h0 ↦ ?_
    obtain _|_|_|n := n
    · exact (h0 rfl).elim
    · simp_rw [zero_add, Nat.cast_one, one_zsmul, smulX_one, smulY_one]
      exact ⟨(pointedCurve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero
        (by simpa only [pointedCurve, _root_.WeierstrassCurve.baseChange, map_Δ, map_ne_zero_iff _ algebraMap_field_injective]
          using Δ_curve_ne_zero)).mp equation_point, rfl⟩
    all_goals obtain ⟨ns, eq⟩ := ih 1 (by omega) one_ne_zero
    · erw [← addX_smul_one_smul_one, ← addY_smul_one_smul_one, zero_add, add_zsmul _ 1 1, eq]
      exact ⟨Affine.nonsingular_add ns ns fun h ↦ smulY_one_ne_negY h.2,
        dite_eq_right fun h ↦ smulY_one_ne_negY h.2⟩
    set n2 := n + 1 + 1
    obtain ⟨ns1, eq1⟩ := ih (n + 1) (by omega) (by omega)
    obtain ⟨ns2, eq2⟩ := ih n2 (by omega) (by omega)
    have ne : smulX n2 ≠ smulX 1 := smulX_ne_smulX (by omega) (by omega)
    simp_rw [show (n + 1 : ℕ) = n2 + (-1 : ℤ) by omega, add_zsmul, neg_smul] at eq1
    let _U := pointedCurve.toAffine
    erw [eq2, eq, add_of_X_ne ne, Affine.Point.some.injEq] at eq1
    let L := _U.slope (smulX n2) (smulX 1) (smulY n2) (smulY 1)
    have X_eq : smulX (n2 + 1 : ℕ) = _U.addX (smulX n2) (smulX 1) L := by
      rw [Nat.cast_add, Nat.cast_one, smulX_add one_ne_zero (by omega) (by omega) (by omega),
        Affine.addX_eq_addX_negY_sub _ _ ne, sub_eq_add_neg (n2 : ℤ), ← eq1.1]; rfl
    have Y_eq : smulY (n2 + 1 : ℕ) = _U.addY (smulX n2) (smulX 1) (smulY n2) L := by
      rw [← mul_cancel_left_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero Field.two_ne_zero),
        ← add_right_cancel_iff (a := _U.a₁ * smulX (n2 + 1 : ℕ) + _U.a₃)]
      convert smulY_add_sub_negY (n := n2) one_ne_zero (by omega) (by omega) (by omega) using 1
      · simp_rw [Affine.negY, Nat.cast_add]; simp only [_U]; ring_nf
      convert _U.addY_sub_negY_addY (smulY n2) (smulY 1) ne using 1
      · rw [Affine.negY, ← X_eq]; ring
      · rw [← X_eq]; rfl
    rw [X_eq, Y_eq, n2.cast_add, add_zsmul, eq, eq2]
    exact ⟨Affine.nonsingular_add ns2 ns fun h ↦ (ne h.1).elim, add_of_X_ne ne⟩
  | neg hn n =>
    rw [neg_ne_zero]; intro h0
    obtain ⟨ns, eq⟩ := hn n h0
    simp_rw [smulX_neg, smulY_neg h0, neg_smul, eq, neg_some]
    exact ⟨(Affine.nonsingular_neg ..).mpr ns, trivial⟩

lemma nonsingular_smulX_smulY (hn : n ≠ 0) : Affine.Nonsingular curveField (smulX n) (smulY n) := by
  exact (zsmul_point_eq_smulX_smulY hn).1

lemma zsmul_point_ne_zero (h0 : n ≠ 0) : n • Affine.point ≠ 0 := by
  obtain ⟨ns, eq⟩ := zsmul_point_eq_smulX_smulY h0
  rw [eq]; exact Affine.Point.some_ne_zero ns

end Affine

namespace Jacobian

open _root_.WeierstrassCurve.Jacobian

open Point in
lemma zsmul_point_ne_zero (h0 : n ≠ 0) : n • Jacobian.point ≠ 0 := by
  rw [Jacobian.point, ← toAffineAddEquiv_symm_apply, ← map_zsmul (toAffineAddEquiv _).symm,
    Ne, map_eq_zero_iff _ (toAffineAddEquiv _).symm.injective]
  exact Affine.zsmul_point_ne_zero h0

lemma zsmul_point_ne (h : m ≠ n) : m • Jacobian.point ≠ n • Jacobian.point := by
  rw [← sub_ne_zero, sub_eq_add_neg, ← sub_zsmul]
  exact zsmul_point_ne_zero (sub_ne_zero.mpr h)

lemma point_point : Jacobian.point.point = ⟦![polyToField (C X), polyToField Y, 1]⟧ := rfl

abbrev smulPoly (n : ℤ) : Fin 3 → Poly := ![curve.φ n, (ωe curve) n, curve.ψ n]

abbrev smulRing (n : ℤ) : Fin 3 → Univ.Ring := AdjoinRoot.mk _ ∘ smulPoly n

abbrev smulField (n : ℤ) : Fin 3 → Univ.Field := polyToField ∘ smulPoly n

lemma algebraMap_comp_smulRing (n : ℤ) : algebraMap _ _ ∘ smulRing n = smulField n := by
  ext i; fin_cases i <;> rfl

theorem zsmul_point_eq_smulField : (n • Jacobian.point).point = ⟦smulField n⟧ := by
  rw [← fin3_def (smulField n), smulField, smulPoly]
  simp_rw [Function.comp, fin3_def_ext]
  obtain rfl | hn := eq_or_ne n 0
  · simp_rw [zero_zsmul, φ_zero, ωe_zero, ψ_zero, map_zero, map_one]; rfl
  obtain ⟨ns, eq⟩ := Affine.zsmul_point_eq_smulX_smulY hn
  change (n • (Point.toAffineAddEquiv _).symm Affine.point).point = _
  rw [← map_zsmul, eq]
  have := ψᵤ_ne_zero hn
  refine Quotient.sound ⟨.mk0 _ (inv_ne_zero this), ?_⟩
  simp_rw [Units.smul_def, Jacobian.smul_fin3]
  ext i; fin_cases i <;>
    simp only [Units.val_mk0, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
    field_simp [Affine.smulX, Affine.smulY, this] <;> rfl

lemma dblZ_smulPoly : dblZ curvePoly (smulPoly n) = curve.ψ (2 * n) := by
  simp_rw [dblZ, smulPoly, negY, fin3_def_ext, curvePoly, _root_.WeierstrassCurve.baseChange, _root_.WeierstrassCurve.map, coe_algebraMap_eq_CC]
  rw [← ψc_spec _ n]; congr; convert (ωe_spec curve) n using 1; ring

lemma nonsingular_smulField : Nonsingular curveField (smulField n) := by
  simpa only [zsmul_point_eq_smulField, Jacobian.nonsingularLift_iff] using (n • Jacobian.point).nonsingular

lemma dblXYZ_smulField : dblXYZ curveField (smulField n) = smulField (2 * n) := by
  obtain rfl | hn := eq_or_ne n 0
  · rw [mul_zero]
    have h0 : smulField (0 : ℤ) = ![1, 1, 0] := by
      ext i
      fin_cases i <;> simp [smulField, smulPoly, φ_zero, ωe_zero, ψ_zero]
    rw [h0, dblXYZ_of_Z_eq_zero equation_zero rfl]
    simp
  have h2 : ((2 : ℤ) • (n • Jacobian.point)).point =
      ⟦dblXYZ curveField (smulField n)⟧ := by
    rw [two_zsmul, Point.add_point, zsmul_point_eq_smulField, addMap_eq, add_self]
  refine (equiv_iff_eq_of_Z_eq ?_ (ψᵤ_ne_zero <| mul_ne_zero two_ne_zero hn)).mp
    (Quotient.exact ?_)
  · simp only [smulField, smulPoly, fin3_def_ext, Function.comp, ← dblZ_smulPoly, ← map_dblZ]
    rfl
  rw [← h2, ← mul_zsmul]
  exact zsmul_point_eq_smulField

/-- 普遍体で検証した倍加公式を、単射な座標環の等式へ戻す。 -/
lemma dblXYZ_smulRing : dblXYZ curveRing (smulRing n) = smulRing (2 * n) :=
  (IsFractionRing.injective _ Univ.Field).comp_left <| by
    simp_rw [← map_dblXYZ]; exact dblXYZ_smulField

lemma addZ_smulPoly : addZ (smulPoly m) (smulPoly n) = curve.ψ (n + m) * curve.ψ (n - m) := by
  have hES : IsEllSequence' (_root_.WeierstrassCurve.ψ curve) := IsEllSequence'.normEDS
  simp_rw [addZ, smulPoly, φ]; convert (hES n m 1).symm using 1
  · simp only [fin3_def_ext]; ring
  · rw [ψ_one]; ring

lemma ωe_neg_eq_neg_negY : (ωe curve) (-n) = -negY curvePoly (smulPoly n) := by
  simp_rw [Affine.ωe_neg' (n := n), negY, smulPoly, fin3_def_ext, curvePoly, _root_.WeierstrassCurve.baseChange, _root_.WeierstrassCurve.map,
    coe_algebraMap_eq_CC]
  ring

lemma smulPoly_neg : smulPoly (-n) = (-1 : Poly) • neg curvePoly (smulPoly n) := by
  simp [smulPoly, ωe_neg_eq_neg_negY, neg, smul_fin3, (show Odd 3 by decide).neg_pow]

lemma smulRing_neg : smulRing (-n) = (-1 : Univ.Ring) • neg curveRing (smulRing n) := by
  simp_rw [smulRing, smulPoly_neg, Jacobian.comp_smul, ← Jacobian.map_neg, map_neg, map_one]; rfl

lemma smulField_neg : smulField (-n) = (-1 : Univ.Field) • neg curveField (smulField n) := by
  simp_rw [smulField, smulPoly_neg, Jacobian.comp_smul, ← Jacobian.map_neg, map_neg, map_one]; rfl

lemma smulPoly_zero : smulPoly 0 = ![1, 1, 0] := by simp [smulPoly]
lemma smulField_zero : smulField 0 = ![1, 1, 0] := by simp [smulField, smulPoly_zero, comp_fin3]

lemma addXYZ_smulField :
    addXYZ curveField (smulField m) (smulField n) =
      polyToField (curve.ψ (n - m)) • smulField (n + m) := by
  obtain rfl | h := eq_or_ne m n
  · rw [sub_self, ψ_zero, map_zero, smul_fin3,
      addXYZ_self nonsingular_smulField.1, zero_pow two_ne_zero, zero_pow (by decide)]
    simp_rw [zero_mul]
  obtain rfl | ne_neg := eq_or_ne n (-m)
  · rw [← one_smul (M := Univ.Field) (smulField m), smulField_neg, neg_add_cancel,
      addXYZ_smul, one_mul, neg_one_sq (R := Univ.Field), addXYZ_neg nonsingular_smulField.1,
      one_smul, ← neg_add', ← two_mul, ψ_neg, map_neg, ← dblZ_smulPoly, ← map_dblZ, smulField_zero]
    rfl
  have hne : ¬ smulField m ≈ smulField n := fun heq ↦ zsmul_point_ne h <| by
    rw [Point.ext_iff, zsmul_point_eq_smulField, zsmul_point_eq_smulField]
    exact Quotient.sound heq
  have key : (m • Jacobian.point + n • Jacobian.point).point =
      ⟦addXYZ curveField (smulField m) (smulField n)⟧ := by
    rw [Point.add_point, zsmul_point_eq_smulField, zsmul_point_eq_smulField, addMap_eq,
      add_of_not_equiv hne]
  erw [← equiv_iff_eq_of_Z_eq]
  · exact Quotient.exact (by
      rw [smul_eq _ (ψᵤ_ne_zero <| sub_ne_zero_of_ne h.symm).isUnit,
        ← zsmul_point_eq_smulField, add_comm, add_zsmul, key])
  · conv_rhs => rw [smulField, comp_fin3, smul_fin3, (fin3_def_ext _ _ _).2.2, mul_comm]
    simp_rw [addXYZ, fin3_def_ext, ← map_mul, ← addZ_smulPoly, ← map_addZ]
  · rw [(smul_fin3_ext _ _).2.2]
    apply mul_ne_zero <;> apply ψᵤ_ne_zero <;> omega

lemma addXYZ_smulRing :
    addXYZ curveRing (smulRing m) (smulRing n) =
      AdjoinRoot.mk curve.polynomial (curve.ψ (n - m)) • smulRing (n + m) :=
  (IsFractionRing.injective Univ.Ring Univ.Field).comp_left <| by
    simp_rw [← map_addXYZ, Jacobian.comp_smul]; exact addXYZ_smulField

lemma addXYZ_smulField₁ :
    addXYZ curveField (smulField n) (smulField (n + 1)) = smulField (2 * n + 1) := by
  rw [addXYZ_smulField, add_sub_cancel_left, ψ_one, map_one, one_smul, two_mul, add_comm, add_assoc]

lemma addXYZ_smulRing₁ :
    addXYZ curveRing (smulRing n) (smulRing (n + 1)) = smulRing (2 * n + 1) := by
  rw [addXYZ_smulRing, add_sub_cancel_left, ψ_one, map_one, one_smul, two_mul, add_comm, add_assoc]

end Jacobian

end Univ

variable (x y) in
abbrev smulEval (n : ℤ) : Fin 3 → R := evalEval x y ∘ ![W.φ n, (ωe W) n, W.ψ n]

variable {W} (eqn : W.toAffine.Equation x y)

open Univ Jacobian

lemma ringEval_comp_smulRing (n : ℤ) : ringEval eqn ∘ smulRing n = smulEval W x y n := by
  conv_rhs => rw [smulEval, ← (map_specialize W), map_φ, map_ωe, map_ψ, ← coe_mapRingHom,
    ← Jacobian.comp_fin3, ← Function.comp_assoc, ← smulPoly, ← coe_evalEvalRingHom,
    ← RingHom.coe_comp, ← eval₂RingHom_eval₂RingHom]
  rw [smulRing, ← Function.comp_assoc, ← RingHom.coe_comp, ringEval_comp_mk, polyEval]

lemma ringEval_ψ (n : ℤ) :
    ringEval eqn (AdjoinRoot.mk _ <| curve.ψ n) = evalEval x y (W.ψ n) :=
  congr_fun (ringEval_comp_smulRing eqn n) 2

include eqn in
lemma dblXYZ_smulEval (n : ℤ) : dblXYZ W (smulEval W x y n) = smulEval W x y (2 * n) := by
  simp_rw [← ringEval_comp_smulRing eqn, ← dblXYZ_smulRing, ← map_dblXYZ, curveRing_map_ringEval]

include eqn in
lemma addXYZ_smulEval (m n : ℤ) :
    addXYZ W (smulEval W x y m) (smulEval W x y n) =
      evalEval x y (W.ψ (n - m)) • smulEval W x y (n + m) := by
  simp_rw [← ringEval_comp_smulRing eqn, ← ringEval_ψ eqn]
  rw [← Jacobian.comp_smul, ← addXYZ_smulRing, ← map_addXYZ]
  simp_rw [curveRing_map_ringEval]

include eqn in
lemma addXYZ_smulEval₁ (n : ℤ) :
    addXYZ W (smulEval W x y n) (smulEval W x y (n + 1)) = smulEval W x y (2 * n + 1) := by
  simp_rw [← ringEval_comp_smulRing eqn, ← addXYZ_smulRing₁, ← map_addXYZ, curveRing_map_ringEval]

variable {F : Type*} [Field F] [CharZero F] (W : WeierstrassCurve F)

open Univ

/-- 任意の標数0の非特異点へ特殊化した倍写像公式。
Jacobian表示を使うことで、分母が消える場合も無限遠点として扱う。 -/
theorem zsmul_eq_smulEval {x y : F} (h : Affine.Nonsingular W x y) (n : ℤ) :
    (n • Point.fromAffine (Affine.Point.some x y h)).point = ⟦smulEval W x y n⟧ := by
  have add_point_eq : ∀ (P Q : Jacobian.Point W) (P' Q' : Fin 3 → F),
      P.point = ⟦P'⟧ → Q.point = ⟦Q'⟧ → (P + Q).point = ⟦Jacobian.add W P' Q'⟧ := by
    intro P Q P' Q' hP hQ
    rw [Point.add_point, hP, hQ, addMap_eq]
  have two_zsmul_point : ∀ (P : Jacobian.Point W) (P' : Fin 3 → F), P.point = ⟦P'⟧ →
      (2 • P).point = ⟦dblXYZ W P'⟧ := by
    intro P P' hP
    rw [two_smul, add_point_eq P P P' P' hP hP, Jacobian.add_self]
  have add_point_of_ne : ∀ (P Q : Jacobian.Point W) (P' Q' : Fin 3 → F), P.point = ⟦P'⟧ →
      Q.point = ⟦Q'⟧ → P ≠ Q → (P + Q).point = ⟦addXYZ W P' Q'⟧ := by
    intro P Q P' Q' hP hQ ne
    rw [add_point_eq P Q P' Q' hP hQ, Jacobian.add_of_not_equiv fun h' ↦
      ne (Point.ext <| hP.trans <| (Quotient.sound h').trans hQ.symm)]
  induction n using Int.negInduction with
  | nat n =>
    refine n.strong_induction_on fun n ih ↦ ?_
    obtain _|_|n := n
    · rw [Nat.cast_zero, zero_smul, smulEval, comp_fin3]; congrm(⟦?_⟧); simp [evalEval]
    · rw [Nat.cast_one, one_smul, smulEval, comp_fin3]; congrm(⟦?_⟧); simp [evalEval]
    obtain ⟨n, rfl|rfl⟩ := n.even_or_odd'
    · rw [add_assoc, ← two_mul, ← left_distrib, Nat.cast_mul, mul_smul, natCast_zsmul,
        two_zsmul_point _ _ (ih _ <| by omega), dblXYZ_smulEval h.1]; rfl
    · rw [show 2 * n + 1 + 1 + 1 = (n + 1) + (n + 1 + 1) by omega, Nat.cast_add, add_smul,
        add_point_of_ne _ _ _ _ (ih _ <| by omega) (ih _ <| by omega), Nat.cast_add (n + 1),
        Nat.cast_one, addXYZ_smulEval₁ h.1, ← add_assoc, two_mul]
      simp_rw [Nat.cast_add]
      rw [ne_comm, ← sub_ne_zero, ← sub_smul, add_sub_cancel_left, Nat.cast_one, one_smul]
      apply Point.fromAffine_some_ne_zero
  | neg hn n =>
    simp_rw [_root_.neg_smul, Point.neg_point, hn, eq_comm]
    refine Quotient.sound ⟨-1, ?_⟩
    simp_rw [← ringEval_comp_smulRing h.1, smulRing_neg, Jacobian.comp_smul, ← Jacobian.map_neg,
      curveRing_map_ringEval, map_neg, map_one]
    rfl

end

end WeierstrassCurve

end PortEllSequenceZSMul

section PortEllSequenceAffineBridge

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve
open _root_.WeierstrassCurve

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

omit [DecidableEq F] in
/-- 曲線の座標環の関係式により、二変数のψの平方は一変数のΨSqになる。 -/
theorem evalEval_ψ_sq {x y : F} (h : W.toAffine.Equation x y) (n : ℤ) :
    ((W.ψ n).evalEval x y) ^ 2 = (W.ΨSq n).eval x := by
  have h0 : W.toAffine.polynomial.eval₂ (evalRingHom x) y = 0 := by
    rw [eval₂_evalRingHom]; exact h
  let e : W.toAffine.CoordinateRing →+* F := AdjoinRoot.lift (evalRingHom x) y h0
  have he : ∀ p : F[X][Y], e (Affine.CoordinateRing.mk W p) = p.evalEval x y := fun p ↦ by
    change AdjoinRoot.lift (evalRingHom x) y h0 (AdjoinRoot.mk _ p) = _
    rw [AdjoinRoot.lift_mk, eval₂_evalRingHom]
  calc ((W.ψ n).evalEval x y) ^ 2
      = e (Affine.CoordinateRing.mk W (W.ψ n)) ^ 2 := by rw [he]
    _ = e (Affine.CoordinateRing.mk W (W.ψ n) ^ 2) := (map_pow e _ 2).symm
    _ = e (Affine.CoordinateRing.mk W (C (W.ΨSq n))) := by
        rw [Affine.CoordinateRing.mk_ψ, Affine.CoordinateRing.mk_Ψ_sq]
    _ = (C (W.ΨSq n)).evalEval x y := he _
    _ = (W.ΨSq n).eval x := evalEval_C x y _

omit [DecidableEq F] in
theorem evalEval_φ {x y : F} (h : W.toAffine.Equation x y) (n : ℤ) :
    (W.φ n).evalEval x y = (W.Φ n).eval x := by
  obtain ⟨p, hp⟩ := AdjoinRoot.mk_eq_mk.mp (Affine.CoordinateRing.mk_φ W n)
  have h0 : (W.toAffine.polynomial).evalEval x y = 0 := h
  have h1 := congrArg (evalEval x y) hp
  rw [evalEval_sub, evalEval_mul, h0, zero_mul, sub_eq_zero, evalEval_C] at h1
  exact h1

variable [CharZero F]

/-- 実際の点群のn倍零条件と、除法多項式の消滅は同値である。
点の加法を座標公式へ結ぶ証明を経由し、この同値を仮定としては受け取らない。 -/
theorem smul_eq_zero_iff_evalEval_ψ {x y : F} (h : W.toAffine.Nonsingular x y) (n : ℤ) :
    n • (Affine.Point.some x y h) = 0 ↔ (W.ψ n).evalEval x y = 0 := by
  have key := zsmul_eq_smulEval (W := W) h n
  have hQns := (n • Jacobian.Point.fromAffine (Affine.Point.some x y h)).nonsingular
  rw [key] at hQns
  calc n • (Affine.Point.some x y h) = 0
      ↔ (Jacobian.Point.toAffineAddEquiv W).symm (n • Affine.Point.some x y h) =
        (Jacobian.Point.toAffineAddEquiv W).symm 0 := (AddEquiv.injective _).eq_iff.symm
    _ ↔ n • Jacobian.Point.fromAffine (Affine.Point.some x y h) = 0 := by
        rw [map_zsmul, map_zero, Jacobian.Point.toAffineAddEquiv_symm_apply]
    _ ↔ (⟦smulEval W x y n⟧ : Jacobian.PointClass F) = ⟦![1, 1, 0]⟧ := by
        rw [Jacobian.Point.ext_iff, key, Jacobian.Point.zero_point]
    _ ↔ (W.ψ n).evalEval x y = 0 := by
        constructor
        · intro heq
          have hz := (Jacobian.Z_eq_zero_of_equiv (Quotient.eq.mp heq)).mpr rfl
          simpa only [smulEval, Function.comp_apply, Matrix.cons_val_two, Matrix.tail_cons,
            Matrix.head_cons] using hz
        · intro hz
          refine Quotient.eq.mpr (Jacobian.equiv_zero_of_Z_eq_zero
            ((Jacobian.nonsingularLift_iff _).mp hQns) ?_)
          simpa only [smulEval, Function.comp_apply, Matrix.cons_val_two, Matrix.tail_cons,
            Matrix.head_cons] using hz

end WeierstrassCurve

end PortEllSequenceAffineBridge
end DkMath.Lib.NumberTheory.EllipticDivision
