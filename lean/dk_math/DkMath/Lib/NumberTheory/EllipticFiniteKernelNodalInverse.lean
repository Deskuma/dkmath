/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelReducedHom

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelNodalInverse"

/-!
# 滑らかな有限核による商と零成分の逆像

[DkMath.Lib] 特異に還元する点に滑らかな核点を加えても、零成分の部分群性から
特異のままである。軌道全体の x 座標は源の節点に合同なので、Vélu の座標和は
同じ標的節点の候補座標に合同となる。標的節点の一致と合わせて逆像を判定する。
-/
namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel
open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open EllipticTorsionRepresentation EllipticGoodReductionSeparation EllipticSmoothReduction
open EllipticCriticalCentre EllipticNodalReduction WeierstrassModelReduction ValuationResidue
open EllipticNodalTorsion.NodalTorsion
open scoped BigOperators
noncomputable local instance {α : Type*} : DecidableEq α := Classical.decEq _

variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
  (H : AddSubgroup (Points E)) [Fintype H] (p : ℕ) [Fact p.Prime]
  (hcard : Nat.card H = p) (hp2 : p ≠ 2) (hkill : ∀ Q : H, p • Q.val = 0)
  (A : ValuationSubring (AlgebraicClosure K)) (M : WeierstrassCurve A)
  (hM : M.map A.subtype = E.map (algebraMap K (AlgebraicClosure K)))
  (hp : A.valuation (p : AlgebraicClosure K) = 1)
  (hs : ∀ Q : H, HasSmoothReduction M Q.val)
  (C : CriticalCentre A (E.map (algebraMap K (AlgebraicClosure K))))
  {x₀ y₀ α : ResidueField A} (F : Frame (M.map (residue A)) x₀ y₀ α)
  (hsep : α ≠ -(M.map (residue A)).a₁ - α)
  (hCx : residue A ⟨C.x, C.x_mem⟩ = x₀)

include hM hs in
omit [Fintype H] [CharZero K] [E.IsElliptic] in
/-- [DkMath.Lib] 特異点を滑らかな核点で平行移動すると特異のままである。
そうでなければ滑らかな二点の差として元の点も滑らかになる。 -/
theorem nonsmooth_translate_smooth_kernel (P : Points E) (hP : ¬ HasSmoothReduction M P) (Q : H) :
    ¬ HasSmoothReduction M (P + Q.val) := by
  intro h
  have hd := smooth_sub_of_model A M _ hM h (hs Q)
  apply hP
  have he : P + Q.val - Q.val = P := by abel
  exact he ▸ hd

include hs in
omit [Fintype H] [CharZero K] [E.IsElliptic] in
/-- [DkMath.Lib] 特異に還元する点は滑らかな核の外にある。 -/
theorem not_mem_of_nonsmooth (P : Points E) (hP : ¬ HasSmoothReduction M P) : P ∉ H := by
  intro hm
  exact hP (hs ⟨P, hm⟩)

include hcard hM hs in
omit [CharZero K] [Fact p.Prime] in
/-- [DkMath.Lib] 特異点の商 x 座標は、源の節点を核の個数だけ数え、
核の x 座標を差し引いた候補値へ合同する。軌道の全点で特異性を使う。 -/
theorem kernelXAt_nonsmooth_congr_candidate (P : Points E) (hP : ¬ HasSmoothReduction M P) :
    A.valuation (kernelXAt E H P (not_mem_of_nonsmooth E H A M hs P hP) -
      ((p : AlgebraicClosure K) * C.x - ∑ Q : H, Q.val.xc)) < 1 := by
  have heach (Q : H) : A.valuation ((P + Q.val).xc - C.x) < 1 :=
    (nonsmooth_coordinates_congr E A M hM C (P + Q.val)
      (nonsmooth_translate_smooth_kernel E H A M hM hs P hP Q)).1
  have hsum := A.valuation.map_sum_lt one_ne_zero (s := Finset.univ)
    (f := fun Q : H => (P + Q.val).xc - C.x) (fun Q _ => heach Q)
  rw [Finset.sum_sub_distrib] at hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  rw [← Nat.card_eq_fintype_card, hcard] at hsum
  rw [kernelXAt_eq_sum]
  convert hsum using 1
  ring_nf

include hcard hp2 hkill hM hp hs F hsep hCx in
/-- [DkMath.Lib] 源が特異に還元すれば、同じ商像も特異に還元する。
Vélu の x 座標和を標的節点に一致させ、標数 2 と 3 を含む中心判定を用いる。 -/
theorem oddKernelPointMap_nonsmooth_of_nonsmooth (P : Points E) (hP : ¬ HasSmoothReduction M P) :
    ¬ HasSmoothReduction (valuationKernelModel E H p hkill A M hM hp)
      (oddKernelPointMap E H (hcard ▸ (Fact.out : p.Prime).odd_of_ne_two hp2) P) := by
  let ho : Odd (Nat.card H) := hcard ▸ (Fact.out : p.Prime).odd_of_ne_two hp2
  let := kernelModel_isElliptic_of_odd_card E H ho
  let U := valuationKernelModel E H p hkill A M hM hp
  let hU := valuationKernelModel_map E H p hkill A M hM hp ho
  let T := Classical.choice (exists_nodal_kernel_criticalCentre E H p hcard hp2 hkill A M hM hp hs F hsep)
  let hP' := not_mem_of_nonsmooth E H A M hs P hP
  let kx (Q : H) : A := ⟨Q.val.xc, (kernel_coordinates_mem E H p hkill A M hM hp Q).1⟩
  let b : A := (p : A) * ⟨C.x, C.x_mem⟩ - ∑ Q : H, kx Q
  have hb : (b : AlgebraicClosure K) = (p : AlgebraicClosure K) * C.x - ∑ Q : H, Q.val.xc := by
    change A.subtype ((p : A) * ⟨C.x, C.x_mem⟩ - ∑ Q : H, kx Q) = _
    simp only [map_sub, map_mul, map_natCast, map_sum]
    rfl
  have hxsmall := kernelXAt_nonsmooth_congr_candidate E H p hcard A M hM hs C P hP
  rw [← hb] at hxsmall
  have hxi : kernelXAt E H P hP' ∈ A := by
    have hh := A.add_mem _ _ ((A.valuation_le_one_iff _).mp hxsmall.le) b.property
    simpa only [sub_add_cancel] using hh
  have hxb : residue A ⟨kernelXAt E H P hP', hxi⟩ = residue A b :=
    (residue_eq_residue_iff_sub_mem_nonunits A hxi b.property).mpr
      ((ValuationSubring.mem_nonunits_iff _).mpr hxsmall)
  have hbt : residue A b = residue A ⟨T.x, T.x_mem⟩ := by
    rw [nodal_center_residue_eq_candidate_all E H p hcard hp2 hkill A M hM hp hs F hsep T]
    change residue A ((p : A) * ⟨C.x, C.x_mem⟩ - ∑ Q : H, kx Q) = _
    rw [map_sub, map_mul, map_natCast, hCx, map_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro Q _
    exact (smoothKernelReduction_coordinates E H A M hM hs p hkill hp Q).1.symm
  have hxT : A.valuation (kernelXAt E H P hP' - T.x) < 1 :=
    (ValuationSubring.mem_nonunits_iff _).mp
      ((residue_eq_residue_iff_sub_mem_nonunits A hxi T.x_mem).mp (hxb.trans hbt))
  rw [show oddKernelPointMap E H ho P = Point.some _ _ (kernelAt_nonsingular E H P hP') from
    kernelPointMap_of_not_mem E H P hP']
  exact (not_hasSmoothReduction_some_iff_of_model U _ hU T _).mpr hxT

include hcard hp2 hkill hM hp hs F hsep hCx in
/-- [DkMath.Lib] 滑らかな核側では、同じ商像が零成分に属することと源点が零成分に属することは同値。
両方向とも同じ有限核、同じ付値環モデルと同じ商点を使用する。 -/
theorem oddKernelPointMap_smooth_iff (P : Points E) :
    HasSmoothReduction (valuationKernelModel E H p hkill A M hM hp)
      (oddKernelPointMap E H (hcard ▸ (Fact.out : p.Prime).odd_of_ne_two hp2) P) ↔
    HasSmoothReduction M P := by
  constructor
  · intro hh
    by_contra hn
    exact oddKernelPointMap_nonsmooth_of_nonsmooth E H p hcard hp2 hkill A M hM hp hs C F hsep hCx P hn hh
  · exact oddKernelPointMap_smooth_of_nodal_frame E H p hcard hp2 hkill A M hM hp hs F hsep P

include hkill hM hp in
omit [Fact p.Prime] in
/-- [DkMath.Lib] 特異核側では零成分の逆像判定をそのまま一般化できない。
実際に非零核点 Q が特異に還元するなら、その商像は O で滑らかに還元する。
したがって滑らかな核という仮定は定理の数学的な境界である。 -/
theorem nonsmooth_kernel_point_counterexample (ho : Odd (Nat.card H)) (Q : H)
    (hQ : ¬ HasSmoothReduction M Q.val) :
    HasSmoothReduction (valuationKernelModel E H p hkill A M hM hp) (oddKernelPointMap E H ho Q.val) ∧
      ¬ HasSmoothReduction M Q.val := by
  let := kernelModel_isElliptic_of_odd_card E H ho
  constructor
  · rw [show oddKernelPointMap E H ho Q.val = 0 from kernelPointMap_of_mem E H Q.val Q.property]
    exact hasSmoothReduction_zero _ _
  · exact hQ

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
