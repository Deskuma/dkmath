/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelNoncollision
import DkMath.Lib.NumberTheory.WeierstrassNodalDistance

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelNodalDistance"

/-!
# 同じ商Xの剰余と候補節点の距離

[DkMath.Lib] 非衝突条件、還元核の単射性と素数位数から、同じ源の剰余点のn倍がOでない。
前章の同じ商Xの剰余公式と節点距離を合わせれば、候補中心との差は非零となる。
候補中心が同じ剰余標的の節点であることはこの章の結論に含めない。
-/
namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel
open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open EllipticTorsionRepresentation EllipticGoodReductionSeparation WeierstrassModelReduction
open EllipticNodalTorsion.NodalTorsion
open scoped BigOperators
noncomputable local instance instDecidableEqEllipticFiniteKernelNodalDistance {α : Type*} : DecidableEq α :=
  Classical.decEq _
variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
  (H : AddSubgroup (Points E)) [Fintype H] (n : ℕ) [Fact n.Prime]
  (hkill : ∀ Q : H, n • Q.val = 0)
  (A : ValuationSubring (AlgebraicClosure K)) (M : WeierstrassCurve A)
  (hM : M.map A.subtype = E.map (algebraMap K (AlgebraicClosure K)))
  (hn : A.valuation (n : AlgebraicClosure K) = 1)
  (hs : ∀ Q : H, HasSmoothReduction M Q.val)
  (P : Points E) (hP : HasSmoothReduction M P)
  (hout : ∀ Q : H, modelReduce A M _ hM P ≠ modelReduce A M _ hM Q.val)
  (hcard : Nat.card H = n)
  {x₀ y₀ α : ResidueField A} (F : Frame (M.map (residue A)) x₀ y₀ α)
  (hsep : α ≠ -(M.map (residue A)).a₁ - α)

include hn hkill hs hout hcard F hsep in
omit [Fintype H] [E.IsElliptic] in
/-- [DkMath.Lib] 同じ核との非衝突から、同じ源の剰余点のn倍はOでない。
素数位数と同じ還元核の単射性から原始根を作り、n捩れの全てを同じ核へ戻す。 -/
theorem noncollision_reduced_nsmul_ne_zero : n • modelReduce A M _ hM P ≠ 0 := by
  let : NeZero n := ⟨(Fact.out : n.Prime).ne_zero⟩
  let e : ZMod n ≃+ H := addEquivOfPrimeCardEq (Nat.card_zmod n) hcard
  let f := smoothKernelReduction E H A M hM hs
  let R := f (e 1)
  have hord : addOrderOf R = n :=
    (addOrderOf_injective f (smoothKernelReduction_injective E H A M hM hs n hkill hn) (e 1)).trans
      ((e.addOrderOf_eq 1).trans (ZMod.addOrderOf_one n))
  have hroot := hord ▸ WeierstrassNodalFrame.primitiveRoot_tc F hsep R
  intro hz
  have ht : tc (M.map (residue A)) x₀ y₀ α (modelReduce A M _ hM P) ^ n = 1 :=
    (WeierstrassNodalOrbit.nsmul_eq_zero_iff F hsep _).mp hz
  obtain ⟨j, _, hj⟩ := hroot.eq_pow_of_pow_eq_one ht
  have he : modelReduce A M _ hM P = j • R := WeierstrassNodalOrbit.tc_injective F hsep (by
    rw [tc_nsmul F]
    exact hj.symm)
  have heq : f (e (j : ZMod n)) = j • R := by
    dsimp [R]
    rw [← Nat.smul_one_eq_cast, map_nsmul, map_nsmul]
  exact hout (e (j : ZMod n)) (he.trans heq.symm)

include hcard F hsep in
/-- [DkMath.Lib] 同じ商Xの剰余は、候補中心n*x₀−Σx(Q̄)から非零の距離を持つ。
実際の商座標の整性・候補との差の公式・源のn倍点の非衝突を全て内部供給する。
剰余標的の真の中心との一致は、この定理には仮定せず結論もしない。 -/
theorem kernelXAt_residue_ne_nodal_candidate :
    let hp := not_mem_of_reduction_noncollision E H A M hM P hout
    let hx := (kernelAt_coordinates_mem E H n hkill A M hM hn hs P hP hout).1
    residue A ⟨kernelXAt E H P hp, hx⟩ ≠
      (n : ResidueField A) * x₀ - ∑ Q : H, (smoothKernelReduction E H A M hM hs Q).xc := by
  have hn0 : (n : ResidueField A) ≠ 0 := by
    have hh := (WeierstrassResidueModel.residue_ne_zero_iff A (n : A)).mpr hn
    simpa only [map_natCast] using hh
  have ht := noncollision_reduced_nsmul_ne_zero E H n hkill A M hM hn hs P hout hcard F hsep
  have hx0 := WeierstrassNodalDistance.xc_ne_centre F hsep _ ht
  have hd : (n : ResidueField A) ^ 2 * ((n • modelReduce A M _ hM P).xc - x₀) ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hn0) (sub_ne_zero.mpr hx0)
  have hformula := kernelXAt_residue_nodal_prime E H n hkill A M hM hn hs P hP hout hcard F hsep
  dsimp only at hformula ⊢
  intro he
  apply hd
  linear_combination he - hformula

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
