/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.WeierstrassNodalCenterSmallChar
import DkMathTest.Lib.NumberTheory.WeierstrassNodalVelu

#print "file: DkMathTest.Lib.NumberTheory.WeierstrassNodalCenterSmallChar"

/-! 実際の節点点群から作った同じ核・同じ多項式標的で、標数2,3の中心比較を検証する。 -/
namespace WeierstrassNodalCenterSmallCharTest
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory WeierstrassVeluPolynomial WeierstrassNodalCenterSmallChar
open EllipticNodalTorsion.NodalTorsion WeierstrassNodalVeluTest
open DkMath.Lib.Algebra.FiniteInversionHalf
open scoped BigOperators
noncomputable section
local instance {α : Type*} : DecidableEq α := Classical.decEq _
variable {k : Type*} [Field k] {p : ℕ} [Fact p.Prime]

/-- 実際の生成核から作った既存標的の任意の特異点は、同じ核の候補中心にある。 -/
theorem actual_quotient_singular_center {u : k} (hu : IsPrimitiveRoot u p) (hp2 : p ≠ 2)
    (h6 : (6 : k) = 0) (X Y : k) (he : (quotient hu).toAffine.Equation X Y)
    (hsg : ¬ (quotient hu).toAffine.Nonsingular X Y) :
    letI : Finite (sampleKernel hu) := Nat.finite_of_card_ne_zero ((sampleKernel_card hu).symm ▸
      (Fact.out : p.Prime).ne_zero)
    letI := Fintype.ofFinite (sampleKernel hu)
    X = -(∑ Q : sampleKernel hu, Q.val.xc) := by
  let : Finite (sampleKernel hu) := Nat.finite_of_card_ne_zero ((sampleKernel_card hu).symm ▸
    (Fact.out : p.Prime).ne_zero)
  let := Fintype.ofFinite (sampleKernel hu)
  let e : ZMod p ≃+ sampleKernel hu := addEquivOfPrimeCardEq (Nat.card_zmod p) (sampleKernel_card hu)
  have F : Frame (splitCurve k) 0 0 0 := by constructor <;> norm_num [splitCurve]
  have hsep : (0 : k) ≠ -(splitCurve k).a₁ - 0 := by norm_num [splitCurve]
  have hn := (Fact.out : p.Prime).odd_of_ne_two hp2
  have h := candidate_center_eq_singular_of_six_eq_zero (splitCurve k) hn h6 e
    (sampleKernel hu).subtype Subtype.coe_injective (cyclicHalf e) (cyclicHalf_isHalf hn e) F hsep X Y
  have hm : quotient hu = polynomialModel (splitCurve k) (cyclicHalf e)
      (fun q => q.val.xc) (fun q => q.val.yc) := rfl
  have hh := h (hm ▸ he) (hm ▸ hsg)
  simpa only [mul_zero, zero_sub, AddSubgroup.subtype_apply] using hh

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- 標数2の実3点核・同じ既存商で中心比較を実行する。 -/
theorem characteristic_two_three_kernel :
    ∃ (u : AlgebraicClosure (ZMod 2)) (hu : IsPrimitiveRoot u 3),
      Nat.card (sampleKernel hu) = 3 ∧ (quotient hu).Δ = 0 ∧
      ∀ X Y, (quotient hu).toAffine.Equation X Y → ¬ (quotient hu).toAffine.Nonsingular X Y →
        letI : Finite (sampleKernel hu) := Nat.finite_of_card_ne_zero ((sampleKernel_card hu).symm ▸ (by decide : 3 ≠ 0))
        letI := Fintype.ofFinite (sampleKernel hu)
        X = -(∑ Q : sampleKernel hu, Q.val.xc) := by
  have : NeZero (3 : ZMod 2) := ⟨by decide⟩
  obtain ⟨u, hu⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure (ZMod 2)) 3
  have h6 : (6 : AlgebraicClosure (ZMod 2)) = 0 := by
    simpa only [map_ofNat, map_zero] using congrArg (algebraMap (ZMod 2) (AlgebraicClosure (ZMod 2)))
      (by decide : (6 : ZMod 2) = 0)
  exact ⟨u, hu, sampleKernel_card hu, (quotient_invariants hu (by decide)).2.2,
    fun X Y he hsg => actual_quotient_singular_center hu (by decide) h6 X Y he hsg⟩

/-- 標数3の実5点核・同じ既存商で中心比較を実行する。 -/
theorem characteristic_three_five_kernel :
    ∃ (u : AlgebraicClosure (ZMod 3)) (hu : IsPrimitiveRoot u 5),
      Nat.card (sampleKernel hu) = 5 ∧ (quotient hu).Δ = 0 ∧
      ∀ X Y, (quotient hu).toAffine.Equation X Y → ¬ (quotient hu).toAffine.Nonsingular X Y →
        letI : Finite (sampleKernel hu) := Nat.finite_of_card_ne_zero ((sampleKernel_card hu).symm ▸ (by decide : 5 ≠ 0))
        letI := Fintype.ofFinite (sampleKernel hu)
        X = -(∑ Q : sampleKernel hu, Q.val.xc) := by
  have : NeZero (5 : ZMod 3) := ⟨by decide⟩
  obtain ⟨u, hu⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure (ZMod 3)) 5
  have h6 : (6 : AlgebraicClosure (ZMod 3)) = 0 := by
    simpa only [map_ofNat, map_zero] using congrArg (algebraMap (ZMod 3) (AlgebraicClosure (ZMod 3)))
      (by decide : (6 : ZMod 3) = 0)
  exact ⟨u, hu, sampleKernel_card hu, (quotient_invariants hu (by decide)).2.2,
    fun X Y he hsg => actual_quotient_singular_center hu (by decide) h6 X Y he hsg⟩

end
end WeierstrassNodalCenterSmallCharTest
