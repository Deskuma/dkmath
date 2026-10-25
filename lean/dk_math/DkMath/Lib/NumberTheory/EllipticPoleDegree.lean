/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelDegree
import DkMath.Lib.NumberTheory.EllipticFunctionFieldConstants
import DkMath.Lib.Algebra.PoleSpaceDegree
import DkMath.Lib.Algebra.ValuationDegreeLower

#print "file: DkMath.Lib.NumberTheory.EllipticPoleDegree"

/-!
# 平行移動不変な関数の一つの極から次数を計算する

[DkMath.Lib] 核Hの外で正則な不変関数は、H上のどの点でもOと同じ極位数を持つ。
極位数0なら全点で正則なので定数である。Oでの一段ごとの最高項相殺と整基底の増大を
組み合わせ、総極位数の一般理論を導入せず固定体の相対次数を抑える。
-/
namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel
open Polynomial IntermediateField WeierstrassCurve WeierstrassCurve.Affine WithZero
open EllipticTorsionRepresentation EllipticFunctionField
open DkMath.Lib.Algebra
open scoped Polynomial.Bivariate
variable {K : Type*} [Field K] (E : WeierstrassCurve K) [E.IsElliptic]
attribute [local instance] geometricCoordinateRing_isDedekindDomain
noncomputable local instance instDecidableEqEllipticPoleDegree :
    DecidableEq (AlgebraicClosure K) := Classical.decEq _

/-- [DkMath.Lib] 全点で正則な楕円有理関数は定数である。
有限点での整性から座標環へ戻し、Oのノルム次数0がY成分と正次数X成分を除く。 -/
theorem eq_const_of_pointValuation_le_one
    (f : (E.toAffine⁄(AlgebraicClosure K)).FunctionField)
    (hf : ∀ P : Points E, pointValuation E P f ≤ 1) :
    ∃ c : AlgebraicClosure K, f = algebraMap _ _ c := by
  classical
  let W := E.toAffine⁄(AlgebraicClosure K)
  obtain ⟨a, ha⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one
    W.FunctionField f (fun v => by
      obtain ⟨P, hP, rfl⟩ := placeOf_surjective E (AlgebraicClosure K) v
      simpa only [pointValuation, dite_eq_right hP, finitePointValuation] using hf P)
  by_cases ha0 : a = 0
  · exact ⟨0, by simpa [ha0] using ha.symm⟩
  have hd : (Algebra.norm (AlgebraicClosure K)[X] a).natDegree = 0 := by
    have hv := hf 0
    change pointValuation E (0 : (E⁄(AlgebraicClosure K)).Point) f ≤ 1 at hv
    rw [pointValuation, dite_eq_left rfl, ← ha,
      EllipticInfinityValuation.valuationInfty_algebraMap_of_ne_zero _ ha0,
      ← exp_zero, exp_le_exp] at hv
    omega
  obtain ⟨p, q, he⟩ := CoordinateRing.exists_smul_basis_eq a
  have hq : q = 0 := by
    by_contra hn
    rw [← he, EllipticInfinityValuation.CoordinateRing.natDegree_norm_smul_basis_of_ne_zero _ _ _ hn] at hd
    omega
  have hp : p.natDegree = 0 := by
    rw [← he, hq,
      EllipticInfinityValuation.CoordinateRing.natDegree_norm_smul_basis_of_eq_zero] at hd
    omega
  refine ⟨p.coeff 0, ?_⟩
  rw [← ha, ← he, hq, zero_smul, add_zero, Polynomial.eq_C_of_natDegree_eq_zero hp,
    CoordinateRing.smul, mul_one]
  simpa only [coeff_C_zero] using
    (EllipticInfinityValuation.FunctionField.algebraMap_mk_C_C W (p.coeff 0))

/-- [DkMath.Lib] 同じ固定体の関数は、核上の点ではOと同じ付値を持つ。 -/
theorem pointValuation_kernel_eq_zero (H : AddSubgroup (Points E))
    {f : (E.toAffine⁄(AlgebraicClosure K)).FunctionField} (hf : f ∈ kernelFixedField E H)
    (P : H) : pointValuation E P.val f = pointValuation E (0 : Points E) f := by
  have ht : pointValuation E (0 : Points E)
      (transEquiv E (AlgebraicClosure K) P.val f) =
      pointValuation E ((0 : Points E) + P.val) f :=
    pointValuation_transEquiv E 0 P.val f
  rw [(mem_kernelFixedField_iff E H f).mp hf P, zero_add] at ht
  exact ht.symm

/-- [DkMath.Lib] 同じ固定体の中で、Hの外で正則な関数からなる実際の部分代数。
Oでの極上界は別のフィルトレーションで与え、対称性を捨てない。 -/
noncomputable def kernelRegularAlgebra (H : AddSubgroup (Points E)) :
    Subalgebra (AlgebraicClosure K) (kernelFixedField E H) where
  carrier := {f | ∀ P : Points E, P ∉ H → pointValuation E P (f : _) ≤ 1}
  algebraMap_mem' c P _ := pointValuation_const_le_one E P c
  zero_mem' P _ := by simp
  add_mem' hf hg P hP := (map_add_le_max _ _ _).trans (max_le (hf P hP) (hg P hP))
  mul_mem' hf hg P hP := by
    change pointValuation E P (_ * _) ≤ 1
    rw [map_mul]
    exact (mul_le_mul' (hf P hP) (hg P hP)).trans_eq (one_mul 1)

/-- [DkMath.Lib] 核外正則な同じ不変関数のOでの極位数dが、固定体上の相対次数を抑える。
H上の極を別々に数える代わりに、不変性で一つの極空間へまとめる。 -/
theorem relfinrank_le_poleOrder (H : AddSubgroup (Points E)) [Finite H]
    (f : (E.toAffine⁄(AlgebraicClosure K)).FunctionField)
    (hf : f ∈ kernelFixedField E H)
    (hout : ∀ P : Points E, P ∉ H → pointValuation E P f ≤ 1)
    (d : ℕ) (hd : 0 < d) (hpole : pointValuation E (0 : Points E) f = exp (d : ℤ)) :
    ((AlgebraicClosure K)⟮f⟯).relfinrank (kernelFixedField E H) ≤ d := by
  classical
  let k := AlgebraicClosure K
  let F := (E.toAffine⁄k).FunctionField
  let A := k⟮f⟯
  let N := kernelFixedField E H
  have hA : A ≤ N := adjoin_simple_le_iff.mpr hf
  let : Algebra A N := (extendScalars hA).algebra
  let : IsScalarTower A N F := (extendScalars hA).isScalarTower_mid'
  let : IsScalarTower k A N := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have htrans : Transcendental k f := transcendental_of_point_pole E (0 : Points E) f (by
    rw [hpole, ← exp_zero, exp_lt_exp]; exact_mod_cast hd)
  let := finiteDimensional_over_transcendental E f htrans
  let : FiniteDimensional A N := FiniteDimensional.left A N F
  let v : Valuation N ℤᵐ⁰ := (pointValuation E (0 : Points E)).comap N.val.toRingHom
  let R := kernelRegularAlgebra E H
  have hc : ∀ c : k, v (algebraMap k N c) ≤ 1 := fun c => pointValuation_const_le_one E 0 c
  have hreg : ∀ g ∈ R, v g ≤ 1 → ∃ c : k, g = algebraMap k N c := by
    intro g hg hv
    obtain ⟨c, he⟩ := eq_const_of_pointValuation_le_one E (g : F) (fun P => by
      by_cases hP : P ∈ H
      · rw [pointValuation_kernel_eq_zero E H g.2 ⟨P, hP⟩]
        exact hv
      · exact hg P hP)
    exact ⟨c, Subtype.ext he⟩
  have hcan : ∀ {g h : N}, h ≠ 0 → v g = v h → ∃ c : k, v (g - c • h) < v h := by
    intro g h hh he
    let := finiteDimensional_over_genericX E
    have hxp : 1 < pointValuation E (0 : Points E) (genericX E k) := by
      change 1 < pointValuation E (0 : (E⁄(AlgebraicClosure K)).Point)
        (genericX E (AlgebraicClosure K))
      rw [pointValuation_zero_genericX, ← exp_zero, exp_lt_exp]
      norm_num
    obtain ⟨c, hc⟩ := ValuationPoleSpace.exists_sub_smul_lt (pointValuation E (0 : Points E))
      (fun c h => pointValuation_const_eq_one E (0 : Points E) h)
      (genericX E k) (transcendental_of_point_pole E (0 : Points E) _ hxp) hxp
      (Subtype.coe_ne_coe.mpr hh) he
    exact ⟨c, hc⟩
  have hint : ∀ g : N, IsIntegral (Algebra.adjoin k {AdjoinSimple.gen k f}) g → g ∈ R := by
    intro g hg P hP
    have hgi : IsIntegral (Algebra.adjoin k {AdjoinSimple.gen k f}) (g : F) :=
      hg.map (IsScalarTower.toAlgHom (Algebra.adjoin k {AdjoinSimple.gen k f}) N F)
    exact ValuationPoleSpace.le_one_of_isIntegral_adjoin (pointValuation E P)
      (fun c => pointValuation_const_le_one E P c) (AdjoinSimple.gen k f) (hout P hP) _ hgi
  have hfm : algebraMap A N (AdjoinSimple.gen k f) ∈ R := hout
  have hft : Transcendental k (AdjoinSimple.gen k f) := fun h => htrans h.algebraMap
  have hbound := PoleSpaceDegree.finrank_le (AdjoinSimple.gen k f) hft
    (PoleSpaceDegree.adjoin_gen_eq_top f) R v hc hreg hcan hint hfm d hpole
  rw [relfinrank_eq_finrank_of_le hA]
  exact hbound

/-- [DkMath.Lib] 同じ固定体にあるgの冪の付値合同類がn個異なれば、相対次数はn以上。
関数体内の実際の独立族を構成し、極位数を形式的な次数と読み替えない。 -/
theorem le_relfinrank_of_pole_classes (H : AddSubgroup (Points E))
    (f g : (E.toAffine⁄(AlgebraicClosure K)).FunctionField)
    (hf : f ∈ kernelFixedField E H) (hg : g ∈ kernelFixedField E H)
    (d e n : ℕ) (hd : 0 < d)
    (hfv : pointValuation E (0 : Points E) f = exp (d : ℤ))
    (hgv : pointValuation E (0 : Points E) g = exp (e : ℤ))
    (hsep : ∀ i j : Fin n, ∀ r s : ℤ,
      (d : ℤ) * r + e * i = (d : ℤ) * s + e * j → i = j) :
    n ≤ ((AlgebraicClosure K)⟮f⟯).relfinrank (kernelFixedField E H) := by
  let k := AlgebraicClosure K
  let F := (E.toAffine⁄k).FunctionField
  let A := k⟮f⟯
  let N := kernelFixedField E H
  have hA : A ≤ N := adjoin_simple_le_iff.mpr hf
  let : Algebra A N := (extendScalars hA).algebra
  let : IsScalarTower A N F := (extendScalars hA).isScalarTower_mid'
  have htrans : Transcendental k f := transcendental_of_point_pole E (0 : Points E) f (by
    rw [hfv, ← exp_zero, exp_lt_exp]; exact_mod_cast hd)
  let := finiteDimensional_over_transcendental E f htrans
  let : FiniteDimensional A N := FiniteDimensional.left A N F
  let v : Valuation N ℤᵐ⁰ := (pointValuation E (0 : Points E)).comap N.val.toRingHom
  let u : Fin n → N := fun i => (⟨g, hg⟩ : N) ^ (i : ℕ)
  have hsc : ∀ a : A, a ≠ 0 → ∃ m : ℤ, v (algebraMap A N a) = exp ((d : ℤ) * m) := by
    intro a ha
    exact ValuationPoleSpace.value_adjoin_simple (pointValuation E (0 : Points E))
      (fun c hc => pointValuation_const_eq_one E 0 hc) f d hd hfv a ha
  have hu : ∀ i, v (u i) = exp ((e : ℤ) * i) := by
    intro i
    change pointValuation E (0 : Points E) (g ^ (i : ℕ)) = _
    rw [map_pow, hgv, ← exp_nsmul, nsmul_eq_mul, mul_comm]
  have hli := ValuationDegreeLower.linearIndependent_of_value_classes v (d : ℤ) hsc u
    (fun i => (e : ℤ) * i) hu hsep
  have hbound := hli.fintype_card_le_finrank
  rw [relfinrank_eq_finrank_of_le hA]
  rw [Fintype.card_fin] at hbound
  exact hbound

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
