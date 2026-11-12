/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_WeierstrassCurve_Affine_exists_map_weilFun_eq_mul_weilFun_smul.lean
(blob 60e4631bea5ae21bf113739f6471516d5e6ac7c3), and
P2M/Sol/S_WeierstrassCurve_Affine_weilPairing0_galois.lean
(blob cc05c14d0a942efea28586bee5cc9b8d1bea7c41).
Modified for DkMath: constructed lifts, existing actual torsion action, unique constants,
and the same NOTE-025/026 unit and root-valued bicharacter; no pairing-data assumptions.
-/

import DkMath.Lib.NumberTheory.EllipticGaloisValuation
import DkMath.Lib.NumberTheory.EllipticWeilBicharacter

#print "file: DkMath.Lib.NumberTheory.EllipticWeilGalois"

/-!
# 同じ移動固有値のガロア同変性

半線形な関数体作用で写したw(T)とw(σT)の比を、全有限場所の付値1から非零定数へ戻す。
非標準的に選んだ生成元そのものの一致を要求しない。既存の固有方程式へ半線形作用を
適用し、平行移動との交換則と非零因子の消去、一意性からc(σS,σT)=σ(c(S,T))を得る。
非退化性と固定体の同定は次の段階であり、ここでは入力にも置かない。
-/
namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open WeierstrassCurve WeierstrassCurve.Affine
open EllipticFunctionField
variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
attribute [local instance] geometricCoordinateRing_isDedekindDomain

omit [CharZero K] [E.IsElliptic] in
/-- 逆ガロア作用を先に施すと、元の実際の点へ戻る。 -/
theorem pointAction_inv_cancel (σ : Field.absoluteGaloisGroup K) (P : Points E) :
    pointAction E σ (pointAction E σ⁻¹ P) = P := by
  rw [← pointAction_mul, mul_inv_cancel, pointAction_one]

/-- 生成元の選択の違いを、一意な非零定数倍に吸収する。
主イデアルの生成元をガロア不変に選んだとは仮定しない。 -/
theorem existsUnique_scalar_galois_weilFunction (n : ℕ) (hn : n ≠ 0)
    (σ : Field.absoluteGaloisGroup K) (T : Torsion E n) :
    ∃! a : (AlgebraicClosure K)ˣ,
      galFunctionFieldEquiv E σ (weilFunction E n hn T.val T.property) =
        algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField (a : AlgebraicClosure K) *
          weilFunction E n hn (torsionAction E n σ T).val (torsionAction E n σ T).property := by
  classical
  let γ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := σ
  let Tσ := torsionAction E n σ T
  have hT : n • T.val = 0 := T.property
  have hTσ : n • Tσ.val = 0 := Tσ.property
  have hwσ := weilFunction_ne_zero E n hn Tσ.val hTσ
  have hv : ∀ v : IsDedekindDomain.HeightOneSpectrum (E.toAffine⁄(AlgebraicClosure K)).CoordinateRing,
      v.valuation (E.toAffine⁄(AlgebraicClosure K)).FunctionField
        (galFunctionFieldEquiv E γ (weilFunction E n hn T.val hT) / weilFunction E n hn Tσ.val hTσ) = 1 := by
    intro v
    obtain ⟨Q, hQ, rfl⟩ := placeOf_surjective E (AlgebraicClosure K) v
    let P : Points E := pointAction E σ⁻¹ Q
    have hP : P ≠ 0 := pointAction_ne_zero E σ⁻¹ hQ
    have hPQ : pointAction E σ P = Q := pointAction_inv_cancel E σ Q
    have hm : n • Q = pointAction E σ (n • P) := by
      exact (congrArg (fun X : Points E => n • X) hPQ.symm).trans (map_nsmul _ n P).symm
    have e1 : n • Q = Tσ.val ↔ n • P = T.val := by
      constructor
      · intro h
        apply pointAction_injective E σ
        exact hm.symm.trans h
      · intro h
        exact hm.trans (congrArg (pointAction E σ) h)
    have e2 : n • Q = 0 ↔ n • P = 0 := by
      constructor
      · intro h
        apply pointAction_injective E σ
        exact (hm.symm.trans h).trans (map_zero _).symm
      · intro h
        exact (hm.trans (congrArg (pointAction E σ) h)).trans (map_zero _)
    have hval : finitePointValuation E Q hQ (galFunctionFieldEquiv E γ (weilFunction E n hn T.val hT)) =
        finitePointValuation E P hP (weilFunction E n hn T.val hT) := by
      have h : finitePointValuation E (pointAction E σ P) (pointAction_ne_zero E σ hP)
          (galFunctionFieldEquiv E γ (weilFunction E n hn T.val hT)) =
          finitePointValuation E P hP (weilFunction E n hn T.val hT) :=
        finitePointValuation_galois E σ P hP (weilFunction E n hn T.val hT)
      simpa only [hPQ] using h
    have hden := valuation_weilFunction E n hn Tσ.val hTσ Q hQ
    have hden' := hden.trans (congrArg₂ (fun a b : WithZero (Multiplicative ℤ) => a / b)
      (if_congr e1 rfl rfl) (if_congr e2 rfl rfl))
    have he := hval.trans ((valuation_weilFunction E n hn T.val hT P hP).trans hden'.symm)
    change finitePointValuation E Q hQ
      (galFunctionFieldEquiv E γ (weilFunction E n hn T.val hT) / weilFunction E n hn Tσ.val hTσ) = 1
    rw [map_div₀, he, div_self ((finitePointValuation E Q hQ).ne_zero_iff.mpr hwσ)]
  obtain ⟨a, ha, -⟩ := EllipticFunctionFieldConstants.existsUnique_unit_of_valuation_eq_one
    (E.baseChange (AlgebraicClosure K))
    (div_ne_zero ((galFunctionFieldEquiv E γ).map_ne_zero_iff.mpr (weilFunction_ne_zero E n hn T.val hT)) hwσ) hv
  have he := (div_eq_iff hwσ).mp ha
  refine ⟨a, he, ?_⟩
  intro b hb
  exact function_scalar_unique E _ hwσ (hb.symm.trans he)

omit [CharZero K] [E.IsElliptic] in
/-- 係数体の単元へのガロア作用。非零性と乗法を保つ通常の単元写像である。 -/
noncomputable def galoisUnitMap (σ : Field.absoluteGaloisGroup K) :
    (AlgebraicClosure K)ˣ →* (AlgebraicClosure K)ˣ := Units.map σ.toRingEquiv.toMonoidHom

omit [CharZero K] [E.IsElliptic] in
/-- 単元作用を係数体の元に戻すと、元の係数自己同型に一致する。 -/
theorem galoisUnitMap_val (σ : Field.absoluteGaloisGroup K) (c : (AlgebraicClosure K)ˣ) :
    (galoisUnitMap σ c : AlgebraicClosure K) = σ.toAlgHom (c : AlgebraicClosure K) := rfl

set_option maxHeartbeats 1600000 in
-- 半線形作用と実際の点作用の型を照合するため、局所的に探索量を増やす。
/-- 主定理：同じ実際の平行移動固有値のガロア同変性。 -/
theorem weilTranslationUnit_galois (n : ℕ) (hn : n ≠ 0) (σ : Field.absoluteGaloisGroup K)
    (S T : Torsion E n) :
    weilTranslationUnit E n hn (torsionAction E n σ T) (torsionAction E n σ S) =
      galoisUnitMap σ (weilTranslationUnit E n hn T S) := by
  classical
  let γ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := σ
  let Sσ := torsionAction E n σ S
  let Tσ := torsionAction E n σ T
  let S0 : (E⁄(AlgebraicClosure K)).Point := S.val
  let S1 : (E⁄(AlgebraicClosure K)).Point := Sσ.val
  have hT : n • T.val = 0 := T.property
  have hTσ : n • Tσ.val = 0 := Tσ.property
  obtain ⟨a, ha, -⟩ := existsUnique_scalar_galois_weilFunction E n hn σ T
  have ha' : galFunctionFieldEquiv E γ (weilFunction E n hn T.val hT) =
      algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField (a : AlgebraicClosure K) *
        weilFunction E n hn Tσ.val hTσ := ha
  clear ha
  have hs : transEquiv E (AlgebraicClosure K) S0 (weilFunction E n hn T.val hT) =
      algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField
        (weilTranslationUnit E n hn T S : AlgebraicClosure K) * weilFunction E n hn T.val hT :=
    weilTranslationUnit_spec E n hn T S
  have h1 := congrArg (galFunctionFieldEquiv E γ) hs
  have hcomm : galFunctionFieldEquiv E γ
      (transEquiv E (AlgebraicClosure K) S0 (weilFunction E n hn T.val hT)) =
      transEquiv E (AlgebraicClosure K) S1 (galFunctionFieldEquiv E γ (weilFunction E n hn T.val hT)) :=
    gal_transEquiv E γ S0 _
  rw [hcomm, galFunctionFieldEquiv_const_mul, ha', map_mul, AlgEquiv.commutes] at h1
  apply Eq.symm
  apply weilTranslationUnit_unique E n hn Tσ Sσ (galoisUnitMap σ (weilTranslationUnit E n hn T S))
  have ha0 : algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField
      (a : AlgebraicClosure K) ≠ 0 := (_root_.map_ne_zero _).mpr a.ne_zero
  apply mul_left_cancel₀ ha0
  change algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField (a : AlgebraicClosure K) *
    transEquiv E (AlgebraicClosure K) S1 (weilFunction E n hn Tσ.val hTσ) = _
  rw [h1]
  change _ = algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField (a : AlgebraicClosure K) *
    (algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField
      (γ (weilTranslationUnit E n hn T S : AlgebraicClosure K)) * _)
  ring

omit [CharZero K] [E.IsElliptic] in
/-- n乗根への係数作用。n乗が1という条件は環自己同型で保存される。
これは非退化性や原始根の選択を必要としない。 -/
noncomputable def galoisRootMap (n : ℕ) (σ : Field.absoluteGaloisGroup K) :
    rootsOfUnity n (AlgebraicClosure K) →* rootsOfUnity n (AlgebraicClosure K) where
  toFun z := ⟨galoisUnitMap σ z.val, by
    have hz : z.val ^ n = 1 := z.property
    change (galoisUnitMap σ z.val) ^ n = 1
    rw [← map_pow, hz, map_one]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ a.val b.val)

omit [CharZero K] [E.IsElliptic] in
/-- 根の作用は、同じ単元の係数作用に制限したものである。 -/
theorem galoisRootMap_val (n : ℕ) (σ : Field.absoluteGaloisGroup K)
    (z : rootsOfUnity n (AlgebraicClosure K)) :
    (galoisRootMap n σ z).val = galoisUnitMap σ z.val := rfl

/-- μₙの等式としての固有指標のガロア同変性。 -/
theorem weilTranslationCharacter_galois (n : ℕ) (hn : n ≠ 0)
    (σ : Field.absoluteGaloisGroup K) (S T : Torsion E n) :
    weilTranslationCharacter E n hn (torsionAction E n σ T) (torsionAction E n σ S) =
      galoisRootMap n σ (weilTranslationCharacter E n hn T S) :=
  Subtype.ext (weilTranslationUnit_galois E n hn σ S T)

/-- 二重AddCharの値も、同じ比例定数の同変性を引き継ぐ。
外側の引数は移動S、内側は目標Tである。 -/
theorem weilAlternatingBicharacter_galois (n : ℕ) (hn : n ≠ 0)
    (σ : Field.absoluteGaloisGroup K) (S T : Torsion E n) :
    weilAlternatingBicharacter E n hn (torsionAction E n σ S) (torsionAction E n σ T) =
      galoisRootMap n σ (weilAlternatingBicharacter E n hn S T) :=
  weilTranslationCharacter_galois E n hn σ S T

/-- 既存の剰余表現への入口。同じ実際のtorsion作用を線形写像として見るだけなので、
新たな形式的対や非退化性の仮定を導入しない。 -/
theorem weilAlternatingBicharacter_representation (n : ℕ) (hn : n ≠ 0)
    (σ : Field.absoluteGaloisGroup K) (S T : Torsion E n) :
    weilAlternatingBicharacter E n hn (representation E n σ S) (representation E n σ T) =
      galoisRootMap n σ (weilAlternatingBicharacter E n hn S T) :=
  weilAlternatingBicharacter_galois E n hn σ S T

end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
