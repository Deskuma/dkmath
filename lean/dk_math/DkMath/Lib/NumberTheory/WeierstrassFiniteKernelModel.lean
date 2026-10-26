/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelVeluEquation
import DkMath.Lib.NumberTheory.WeierstrassNodalVelu
import DkMath.Lib.Algebra.FiniteInversionHalfTransport

#print "file: DkMath.Lib.NumberTheory.WeierstrassFiniteKernelModel"

/-!
# 奇標数の同じ有限核による多項式標的の非特異性

[DkMath.Lib] 既存kernelModelの方程式と三根分離を、2が非零の体へ一般化して再利用する。
基礎体上の単射な有限核を代数閉包へ写し、同じ半集合の和を既存半核へ輸送する。
源も標的も既存の同じ座標・係数を保ち、標的非特異性のproviderを入力しない。
-/
namespace DkMath.Lib.NumberTheory.WeierstrassFiniteKernelModel
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassVeluPolynomial
open EllipticTorsionRepresentation EllipticFiniteKernel EllipticNodalTorsion.NodalTorsion
open DkMath.Lib.Algebra.FiniteInversionHalf
noncomputable local instance instDecidableEqWeierstrassFiniteKernelModel {α : Type*} : DecidableEq α :=
  Classical.decEq _

/-- [DkMath.Lib] 単射な体写像で同じ実点を写すと、両座標も同じ写像で写る。Oも扱う。 -/
theorem point_map_coordinates {k L : Type*} [Field k] [Field L] [DecidableEq k] [DecidableEq L]
    (W : WeierstrassCurve k) (ι : k →+* L) (hi : Function.Injective ι) (P : W.toAffine.Point) :
    (toMap W ι hi P).xc = ι P.xc ∧ (toMap W ι hi P).yc = ι P.yc := by
  rcases P with _ | ⟨x,y,h⟩
  · exact ⟨(map_zero _).symm,(map_zero _).symm⟩
  · exact ⟨rfl,rfl⟩

/-- [DkMath.Lib] 2が非零の体上で、同じ単射な奇数位数核と同じ半集合の多項式標的は非特異。
巡回生成元・標数0・標的楕円性の入力を必要とせず、任意の奇数有限核に適用できる。 -/
theorem polynomialModel_discriminant_ne_zero {k : Type*} [Field k] [DecidableEq k] [NeZero (2 : k)]
    (W : WeierstrassCurve k) [W.IsElliptic]
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (f : G →+ W.toAffine.Point) (hf : Function.Injective f) (ho : Odd (Nat.card G))
    (s : Finset G) (hs : IsHalf s) :
    (polynomialModel W s (fun q => (f q).xc) (fun q => (f q).yc)).Δ ≠ 0 := by
  let ι : k →+* AlgebraicClosure k := algebraMap _ _
  let g := (toMap W ι ι.injective).comp f
  have hg : Function.Injective g := (toMap_injective W ι ι.injective).comp hf
  let R : AddSubgroup (Points W) := g.range
  let e : G ≃+ R := AddMonoidHom.ofInjective hg
  let : Finite R := Finite.of_surjective e e.surjective
  let := Fintype.ofFinite R
  have hcard : Nat.card R = Nat.card G := (Nat.card_congr e.toEquiv).symm
  have hodd : Odd (Nat.card R) := hcard ▸ ho
  let V := W.map ι
  have hx (q : G) : (e q).val.xc = ι (f q).xc := (point_map_coordinates W ι ι.injective (f q)).1
  have hy (q : G) : (e q).val.yc = ι (f q).yc := (point_map_coordinates W ι ι.injective (f q)).2
  have ht : (∑ q ∈ s, momentT V (ι (f q).xc)) =
      ∑ Q ∈ halfKernel W R, momentT V Q.val.xc := by
    have h := sum_eq_equiv hs (halfKernel_partition W R hodd) e
      (fun Q : R => momentT V Q.val.xc)
      (fun Q => (WeierstrassNodalVelu.point_moments_neg V Q.val).1)
    simpa only [hx] using h
  have hw : (∑ q ∈ s, momentW V (ι (f q).xc) (ι (f q).yc)) =
      ∑ Q ∈ halfKernel W R, momentW V Q.val.xc Q.val.yc := by
    have h := sum_eq_equiv hs (halfKernel_partition W R hodd) e
      (fun Q : R => momentW V Q.val.xc Q.val.yc)
      (fun Q => (WeierstrassNodalVelu.point_moments_neg V Q.val).2)
    simpa only [hx,hy] using h
  dsimp only [V,ι] at ht hw
  have he : (polynomialModel W s (fun q => (f q).xc) (fun q => (f q).yc)).map ι =
      halfKernelPolynomialModel W R := by
    rw [polynomialModel_map]
    unfold halfKernelPolynomialModel
    ext
    · rfl
    · rfl
    · rfl
    · simpa only [polynomialModel,Function.comp_apply] using congrArg
        (fun T => (W.map ι).a₄ - 5 * T) ht
    · simp only [polynomialModel,Function.comp_apply]
      change (W.map ι).a₆ - (W.map ι).b₂ * _ - 7 * _ = _
      rw [ht,hw]
  have hd : (halfKernelPolynomialModel W R).Δ ≠ 0 := by
    rw [halfKernelPolynomialModel_eq_kernelModel W R hodd]
    exact kernelModel_discriminant_ne_zero_of_odd_card W R hodd
  intro hz
  apply hd
  rw [← he,map_Δ,hz,map_zero]

/-- [DkMath.Lib] 同じ半集合の標的に楕円性を供給する。判別式非零を独立の仮定に戻さない。 -/
theorem polynomialModel_isElliptic {k : Type*} [Field k] [DecidableEq k] [NeZero (2 : k)]
    (W : WeierstrassCurve k) [W.IsElliptic]
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (f : G →+ W.toAffine.Point) (hf : Function.Injective f) (ho : Odd (Nat.card G))
    (s : Finset G) (hs : IsHalf s) :
    (polynomialModel W s (fun q => (f q).xc) (fun q => (f q).yc)).IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (polynomialModel_discriminant_ne_zero W f hf ho s hs)⟩

end DkMath.Lib.NumberTheory.WeierstrassFiniteKernelModel
