/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_WeierstrassCurve_Affine_eq_zero_of_forall_transEquiv_eq.lean.
Upstream blob: e82e468ec9dc155bbe1c531016cbd83735a3b037
Modified for DkMath: actual guarded natural-number pullback; textbook APIs and existing geometry.
-/

import DkMath.Lib.NumberTheory.EllipticMultiplicationFixedField
import DkMath.Lib.NumberTheory.EllipticMultiplicationValuation
import DkMath.Lib.Algebra.PullbackPrincipalPrime
import DkMath.Lib.NumberTheory.EllipticWeilGalois

#print "file: DkMath.Lib.NumberTheory.EllipticWeilNondegenerate"

/-!
# 同じWeil双指標の非退化性

全torsion平行移動で不変な関数は、028-Bから実際の倍写像の引き戻しである。
028-Cの局所付値の上界とファイバーの全射性を使い、一重零点の情報を主点イデアルへ戻す。
同じ曲線の点群から類群への単射がT=Oを与える。固定体の一致から付値の降下を省略しない。
-/
namespace DkMath.Lib.NumberTheory.EllipticFunctionField
open WeierstrassCurve WeierstrassCurve.Affine
variable {K : Type*} [Field K] (E : WeierstrassCurve K)

/-- 等しい有限点は同じ場所を与える。非零性の証拠の選択には依存しない。 -/
theorem placeOf_congr {L : Type*} [Field L] [Algebra K L]
    {P Q : (E⁄L).Point} (hP : P ≠ 0) (hQ : Q ≠ 0) (h : P = Q) :
    placeOf E L P hP = placeOf E L Q hQ := by subst h; rfl

end DkMath.Lib.NumberTheory.EllipticFunctionField

namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open EllipticFunctionField
variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
noncomputable local instance instDecidableEqEllipticWeilNondegenerate : DecidableEq (AlgebraicClosure K) := Classical.decEq _
attribute [local instance] geometricCoordinateRing_isDedekindDomain

/-- 有限ファイバー上の一重零点を持つ関数が全torsion平行移動で不変なら、目標点はOである。
Oへ写る場所はOption.noneとして除外し、残りの全素点への全射性と局所上界を明示する。 -/
theorem eq_zero_of_invariant_fiber_valuation (n : ℕ) (hn : n ≠ 0)
    (T : (E⁄(AlgebraicClosure K)).Point) (g : (E.toAffine⁄(AlgebraicClosure K)).FunctionField)
    (hg : ∀ (P : (E⁄(AlgebraicClosure K)).Point) (hP : P ≠ 0), n • P ≠ 0 →
      (placeOf E (AlgebraicClosure K) P hP).valuation _ g = if n • P = T then exp (-1) else 1)
    (hinv : ∀ S : Torsion E n, transEquiv E (AlgebraicClosure K) S.val g = g) : T = 0 := by
  classical
  by_contra hT0
  obtain ⟨h, hh⟩ := exists_multiplicationPull_of_invariant E n hn g hinv
  have hsurj : ∀ P : (E⁄(AlgebraicClosure K)).Point, ∃ Q : (E⁄(AlgebraicClosure K)).Point, n • Q = P :=
    multiplication_surjective E n hn
  let pt : HeightOneSpectrum (E.toAffine⁄(AlgebraicClosure K)).CoordinateRing → (E.toAffine⁄(AlgebraicClosure K)).Point := fun v =>
    Classical.choose (placeOf_surjective E (AlgebraicClosure K) v)
  have hpt0 : ∀ v, pt v ≠ 0 := fun v => Classical.choose (Classical.choose_spec (placeOf_surjective E (AlgebraicClosure K) v))
  have hptv : ∀ v, placeOf E (AlgebraicClosure K) (pt v) (hpt0 v) = v := fun v =>
    Classical.choose_spec (Classical.choose_spec (placeOf_surjective E (AlgebraicClosure K) v))
  let N : HeightOneSpectrum (E.toAffine⁄(AlgebraicClosure K)).CoordinateRing → Option (HeightOneSpectrum (E.toAffine⁄(AlgebraicClosure K)).CoordinateRing) :=
    fun v => if hv : n • pt v = 0 then none else Option.some (placeOf E (AlgebraicClosure K) (n • pt v) hv)
  have hNsome : ∀ v w, N v = Option.some w → ∃ hv : n • pt v ≠ 0, placeOf E (AlgebraicClosure K) (n • pt v) hv = w := by
    intro v w hvw
    by_cases hv : n • pt v = 0
    · simp only [N, hv, dite_true] at hvw; exact absurd hvw (by simp)
    · simp only [N, hv, dite_false, Option.some.injEq] at hvw
      exact ⟨hv, hvw⟩
  have hpt_of_place : ∀ {P : (E.toAffine⁄(AlgebraicClosure K)).Point} (hP : P ≠ 0), pt (placeOf E (AlgebraicClosure K) P hP) = P := fun hP =>
    placeOf_injective E (AlgebraicClosure K) _ _ (hptv _)
  have hN : ∀ w, ∃ v, N v = Option.some w := by
    intro w
    obtain ⟨U, hU, rfl⟩ := placeOf_surjective E (AlgebraicClosure K) w
    obtain ⟨Q, hQ⟩ := hsurj U
    have hQ0 : Q ≠ 0 := by rintro rfl; exact hU (by rw [← hQ, smul_zero])
    refine ⟨placeOf E (AlgebraicClosure K) Q hQ0, ?_⟩
    have hv : n • pt (placeOf E (AlgebraicClosure K) Q hQ0) ≠ 0 := by rw [hpt_of_place]; rwa [hQ]
    simp only [N, hv, dite_false, Option.some.injEq]
    exact EllipticFunctionField.placeOf_congr E (L := AlgebraicClosure K) _ _ (by rw [hpt_of_place, hQ])
  have key := DkMath.Lib.Algebra.PullbackPrincipalPrime.exists_eq_span_of_eq_pullback (R := (E.toAffine⁄(AlgebraicClosure K)).CoordinateRing) (K := (E.toAffine⁄(AlgebraicClosure K)).FunctionField)
    ((multiplicationPull E n hn).toRingHom : (E.toAffine⁄(AlgebraicClosure K)).FunctionField →+* (E.toAffine⁄(AlgebraicClosure K)).FunctionField) N hN ?_ g (placeOf E (AlgebraicClosure K) T hT0) ?_ ?_ ⟨h, hh⟩
  rotate_left
  · intro v w hvw x k hx
    obtain ⟨hv, rfl⟩ := hNsome v w hvw
    rw [← hptv v]
    exact valuation_multiplicationPull_le E n hn (pt v) (hpt0 v) hv x k hx
  · intro v hv
    obtain ⟨hv', hw⟩ := hNsome v _ hv
    have hPT : n • pt v = T := placeOf_injective E (AlgebraicClosure K) _ _ hw
    rw [← hptv v, hg (pt v) (hpt0 v) hv', ite_eq_left hPT]
  · intro v w hvw hw
    obtain ⟨hv', rfl⟩ := hNsome v w hvw
    have hPT : n • pt v ≠ T := fun h' => hw (EllipticFunctionField.placeOf_congr E (L := AlgebraicClosure K) _ _ h')
    rw [← hptv v, hg (pt v) (hpt0 v) hv', ite_eq_right hPT]
  obtain ⟨r, hr⟩ := key
  have hr0 : r ≠ 0 := by
    intro h0
    apply (placeOf E (AlgebraicClosure K) T hT0).ne_bot
    rw [hr, h0, Ideal.span_singleton_eq_bot]
  have hTs := Point.eq_some_xc_yc hT0
  have hcls : Point.toClass T = 0 := by
    rw [hTs, Point.toClass_some]
    exact (ClassGroup.mk_eq_one_of_coe_ideal (by rfl)).mpr ⟨r, hr0, hr⟩
  exact hT0 ((Point.toClass_eq_zero T).mp hcls)


/-- 同じ実際の移動固有値の右非退化性。全ての移動Sで値1となる目標Tは零に限る。 -/
theorem weilTranslationUnit_nondegenerate_right (n : ℕ) (hn : n ≠ 0) (T : Torsion E n)
    (hT : ∀ S : Torsion E n, weilTranslationUnit E n hn T S = 1) : T = 0 := by
  classical
  apply Subtype.ext
  apply eq_zero_of_invariant_fiber_valuation E n hn T.val (weilFunction E n hn T.val T.property)
  · intro P hP hnP
    have hval := valuation_weilFunction E n hn T.val T.property P hP
    refine hval.trans ((congrArg₂ (fun a b : ℤᵐ⁰ => a / b) ?_ ?_).trans (div_one _))
    · exact (ite_eq_ite _ _ _).mpr trivial
    · exact ite_eq_right hnP
  · intro S
    have hs := weilTranslationUnit_spec E n hn T S
    rw [hT S, Units.val_one, map_one, one_mul] at hs
    exact hs

/-- 交代双指標の右非退化性。値はNOTE-025と同じ比例定数である。 -/
theorem weilAlternatingBicharacter_nondegenerate_right (n : ℕ) (hn : n ≠ 0) (T : Torsion E n)
    (hT : ∀ S, weilAlternatingBicharacter E n hn S T = 1) : T = 0 :=
  weilTranslationUnit_nondegenerate_right E n hn T (fun S => congrArg Subtype.val (hT S))

/-- 反対称性を使って、同じ双指標の左非退化性も得る。 -/
theorem weilAlternatingBicharacter_nondegenerate_left (n : ℕ) (hn : n ≠ 0) (S : Torsion E n)
    (hS : ∀ T, weilAlternatingBicharacter E n hn S T = 1) : S = 0 := by
  apply weilAlternatingBicharacter_nondegenerate_right E n hn S
  intro T
  rw [weilAlternatingBicharacter_swap, hS T, inv_one]

end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
