/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.WeierstrassNodalVelu
import DkMath.Lib.NumberTheory.EllipticNodalReduction
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

#print "file: DkMathTest.Lib.NumberTheory.WeierstrassNodalVelu"

/-!
節点曲線y²+xy=x³の実際の滑らかな点を原始根から構成し、その生成部分群を使う。
標数2では実3点核、標数3では実5点核を内部構成して同じ多項式標的を検査する。
1728が零の体でもΔ=0を独立に確認するための回帰例である。
-/
namespace WeierstrassNodalVeluTest
open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open DkMath.Lib.NumberTheory WeierstrassVeluPolynomial WeierstrassNodalFrame
open EllipticNodalTorsion.NodalTorsion
open DkMath.Lib.Algebra.FiniteInversionHalf
noncomputable section
local instance {α : Type*} : DecidableEq α := Classical.decEq _

/-- 二方向の分離した節点を持つ実際の曲線。楕円性を仮定しない。 -/
def splitCurve (k : Type*) [Field k] : WeierstrassCurve k := ⟨1,0,0,0,0⟩

private theorem frame (k : Type*) [Field k] : Frame (splitCurve k) 0 0 0 := by
  constructor <;> norm_num [splitCurve]

private theorem separated (k : Type*) [Field k] : (0 : k) ≠ -(splitCurve k).a₁ - 0 := by
  norm_num [splitCurve]

private theorem parameter_nonsingular {k : Type*} [Field k] (u : k) (h0 : u ≠ 0) (h1 : u ≠ 1) :
    (splitCurve k).toAffine.Nonsingular (u / (1-u)^2) (u^2 / (1-u)^3) := by
  have hn : 1-u ≠ 0 := sub_ne_zero.mpr h1.symm
  apply EllipticNodalReduction.nonsingular_of_node_of_x_ne (splitCurve k) 0 0
    (by norm_num [splitCurve,equation_iff]) (not_nonsingular_centre (frame k))
    (by norm_num [splitCurve,b₂])
  · norm_num only [splitCurve,equation_iff]
    field_simp [hn]
    ring
  · exact div_ne_zero h0 (pow_ne_zero 2 hn)

/-- 原始根パラメータを同じ節点曲線上の実際の有限点へ写す。 -/
def parameterPoint {k : Type*} [Field k] (u : k) (h0 : u ≠ 0) (h1 : u ≠ 1) :
    (splitCurve k).toAffine.Point := .some _ _ (parameter_nonsingular u h0 h1)

/-- 構成した点の同じ節点比は、与えたuそのものである。 -/
theorem parameter_tc {k : Type*} [Field k] (u : k) (h0 : u ≠ 0) (h1 : u ≠ 1) :
    tc (splitCurve k) 0 0 0 (parameterPoint u h0 h1) = u := by
  have hn : 1-u ≠ 0 := sub_ne_zero.mpr h1.symm
  simp only [parameterPoint,tc,splitCurve,sub_zero,zero_mul,sub_neg_eq_add,neg_mul,one_mul]
  field_simp [hn,h0]
  ring

variable {k : Type*} [Field k] {p : ℕ} [Fact p.Prime]

private theorem root_nonzero {u : k} (hu : IsPrimitiveRoot u p) : u ≠ 0 :=
  (hu.isUnit (Fact.out : p.Prime).ne_zero).ne_zero

private theorem root_ne_one {u : k} (hu : IsPrimitiveRoot u p) : u ≠ 1 := by
  intro he
  have hh := hu.unique (he ▸ (by simp : IsPrimitiveRoot (1:k) 1))
  exact (Fact.out : p.Prime).ne_one hh

/-- 原始p乗根から構成した同じ実点の加法位数は正確にpである。 -/
theorem parameter_order {u : k} (hu : IsPrimitiveRoot u p) :
    addOrderOf (parameterPoint u (root_nonzero hu) (root_ne_one hu)) = p := by
  have hh := primitiveRoot_tc (frame k) (separated k) (parameterPoint u (root_nonzero hu) (root_ne_one hu))
  rw [parameter_tc] at hh
  exact hh.unique hu

/-- 同じ実点が生成する実際の有限核。 -/
def sampleKernel {u : k} (hu : IsPrimitiveRoot u p) : AddSubgroup (splitCurve k).toAffine.Point :=
  AddSubgroup.zmultiples (parameterPoint u (root_nonzero hu) (root_ne_one hu))

/-- 同じ生成核には正確にp点がある。 -/
theorem sampleKernel_card {u : k} (hu : IsPrimitiveRoot u p) : Nat.card (sampleKernel hu) = p :=
  (Nat.card_zmultiples _).trans (parameter_order hu)

private noncomputable def kernelEquiv {u : k} (hu : IsPrimitiveRoot u p) : ZMod p ≃+ sampleKernel hu :=
  addEquivOfPrimeCardEq (Nat.card_zmod p) (sampleKernel_card hu)

/-- 同じ実核の巡回半集合と実座標で作った多項式標的。 -/
noncomputable def quotient {u : k} (hu : IsPrimitiveRoot u p) : WeierstrassCurve k := by
  let : Finite (sampleKernel hu) := Nat.finite_of_card_ne_zero ((sampleKernel_card hu).symm ▸
    (Fact.out : p.Prime).ne_zero)
  let := Fintype.ofFinite (sampleKernel hu)
  exact polynomialModel (splitCurve k) (cyclicHalf (kernelEquiv hu)) (fun q => q.val.xc) (fun q => q.val.yc)

/-- 同じ実核から作った商は節点を保ち、c₄,c₆は正確な重みで変わる。 -/
theorem quotient_invariants {u : k} (hu : IsPrimitiveRoot u p) (hp2 : p ≠ 2) :
    (quotient hu).c₄ = (p:k)^4 ∧ (quotient hu).c₆ = -(p:k)^6 ∧ (quotient hu).Δ = 0 := by
  let : Finite (sampleKernel hu) := Nat.finite_of_card_ne_zero ((sampleKernel_card hu).symm ▸
    (Fact.out : p.Prime).ne_zero)
  let := Fintype.ofFinite (sampleKernel hu)
  have hn := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hh := WeierstrassNodalVelu.polynomialModel_invariants (splitCurve k) hn (kernelEquiv hu)
    (sampleKernel hu).subtype Subtype.coe_injective _ (cyclicHalf_isHalf hn (kernelEquiv hu))
    (frame k) (separated k)
  change (quotient hu).c₄ = (p:k)^4 * (splitCurve k).c₄ ∧
    (quotient hu).c₆ = (p:k)^6 * (splitCurve k).c₆ ∧ (quotient hu).Δ = 0 at hh
  have hc4 : (splitCurve k).c₄ = 1 := by norm_num [splitCurve,c₄,b₂,b₄]
  have hc6 : (splitCurve k).c₆ = -1 := by norm_num [splitCurve,c₆,b₂,b₄,b₆]
  simpa only [hc4,hc6,mul_one,mul_neg_one] using hh

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- 標数2に実3点核が存在し、同じ標的はΔ=0,c₄=1を満たす。 -/
theorem characteristic_two_example :
    ∃ (u : AlgebraicClosure (ZMod 2)) (hu : IsPrimitiveRoot u 3),
      Nat.card (sampleKernel hu) = 3 ∧ (quotient hu).Δ = 0 ∧ (quotient hu).c₄ = 1 := by
  have : NeZero (3 : ZMod 2) := ⟨by decide⟩
  obtain ⟨u,hu⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure (ZMod 2)) 3
  have hi := quotient_invariants hu (by decide)
  refine ⟨u,hu,sampleKernel_card hu,hi.2.2,?_⟩
  have h3 : (3 : AlgebraicClosure (ZMod 2)) = 1 := by
    simpa only [map_ofNat,map_one] using congrArg (algebraMap (ZMod 2) (AlgebraicClosure (ZMod 2)))
      (by decide : (3:ZMod 2)=1)
  simpa only [Nat.cast_ofNat,h3,one_pow] using hi.1

/-- 標数3に実5点核が存在する。1728で割らず、同じ標的のΔ=0を確認する。 -/
theorem characteristic_three_example :
    ∃ (u : AlgebraicClosure (ZMod 3)) (hu : IsPrimitiveRoot u 5),
      Nat.card (sampleKernel hu) = 5 ∧ (quotient hu).Δ = 0 ∧ (quotient hu).c₄ = 1 := by
  have : NeZero (5 : ZMod 3) := ⟨by decide⟩
  obtain ⟨u,hu⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure (ZMod 3)) 5
  have hi := quotient_invariants hu (by decide)
  refine ⟨u,hu,sampleKernel_card hu,hi.2.2,?_⟩
  have h5 : (5 : AlgebraicClosure (ZMod 3)) = -1 := by
    simpa only [map_ofNat,map_neg,map_one] using congrArg (algebraMap (ZMod 3) (AlgebraicClosure (ZMod 3)))
      (by decide : (5:ZMod 3)=-1)
  simpa only [Nat.cast_ofNat,h5,(by decide : Even 4).neg_one_pow] using hi.1

local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

/-- 標数2で同じ構成を37点核へ拡張する。37乗の直接展開を使わない。 -/
theorem characteristic_two_thirtySeven_example :
    ∃ (u : AlgebraicClosure (ZMod 2)) (hu : IsPrimitiveRoot u 37),
      Nat.card (sampleKernel hu) = 37 ∧ (quotient hu).Δ = 0 ∧ (quotient hu).c₄ = 1 := by
  have : NeZero (37 : ZMod 2) := ⟨by decide⟩
  obtain ⟨u,hu⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure (ZMod 2)) 37
  have hi := quotient_invariants hu (by decide)
  have hn : (37 : AlgebraicClosure (ZMod 2)) = 1 := by
    simpa only [map_ofNat,map_one] using congrArg (algebraMap (ZMod 2) (AlgebraicClosure (ZMod 2)))
      (by decide : (37:ZMod 2)=1)
  exact ⟨u,hu,sampleKernel_card hu,hi.2.2,by simpa only [Nat.cast_ofNat,hn,one_pow] using hi.1⟩

/-- 標数3でも実37点核の同じ商は節点を保つ。非空の三次対称和まで使用する例。 -/
theorem characteristic_three_thirtySeven_example :
    ∃ (u : AlgebraicClosure (ZMod 3)) (hu : IsPrimitiveRoot u 37),
      Nat.card (sampleKernel hu) = 37 ∧ (quotient hu).Δ = 0 ∧ (quotient hu).c₄ = 1 := by
  have : NeZero (37 : ZMod 3) := ⟨by decide⟩
  obtain ⟨u,hu⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure (ZMod 3)) 37
  have hi := quotient_invariants hu (by decide)
  have hn : (37 : AlgebraicClosure (ZMod 3)) = 1 := by
    simpa only [map_ofNat,map_one] using congrArg (algebraMap (ZMod 3) (AlgebraicClosure (ZMod 3)))
      (by decide : (37:ZMod 3)=1)
  exact ⟨u,hu,sampleKernel_card hu,hi.2.2,by simpa only [Nat.cast_ofNat,hn,one_pow] using hi.1⟩

/-- 偶数位数では半周に反転固定点が入り、互いに交わらない半集合にはならない。 -/
theorem even_half_boundary : ¬ IsHalf (cyclicHalf (AddEquiv.refl (ZMod 2))) := by
  intro he
  have hx : (1:ZMod 2) ∈ cyclicHalf (AddEquiv.refl (ZMod 2)) := by
    change (1:ZMod 2) ∈ (Finset.Icc 1 (2/2)).image (fun j:ℕ => (j:ZMod 2))
    exact Finset.mem_image.mpr ⟨1,by decide,rfl⟩
  have hn : -(1:ZMod 2)=1 := by decide
  exact (Finset.disjoint_left.mp he.2) hx (Finset.mem_image.mpr ⟨1,hx,hn⟩)

end
end WeierstrassNodalVeluTest
