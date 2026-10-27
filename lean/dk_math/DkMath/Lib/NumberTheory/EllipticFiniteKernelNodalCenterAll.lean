/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelCriticalCentre
import DkMath.Lib.NumberTheory.WeierstrassNodalCenterSmallChar

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelNodalCenterAll"

/-!
# 標数2・3を含む同じ節点商の中心と零成分輸送

[DkMath.Lib] 標的の剰余が、同じ還元核と同じ半核の多項式商であることを使う。
任意標数の中心一致を適用して、同じ全点商準同型から中心一致と12非零の仮定を外す。
源の節点Frameと標的臨界中心の存在は、既存の供給定理と別々に接続する。
-/
namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel
open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open EllipticTorsionRepresentation EllipticGoodReductionSeparation EllipticCriticalCentre
open EllipticNodalTorsion.NodalTorsion WeierstrassVeluPolynomial
open DkMath.Lib.Algebra.FiniteInversionHalf
open scoped BigOperators
noncomputable local instance instDecidableEqEllipticFiniteKernelNodalCenterAll {α : Type*} : DecidableEq α :=
  Classical.decEq _
variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
  (H : AddSubgroup (Points E)) [Fintype H] (p : ℕ) [Fact p.Prime]
  (hcard : Nat.card H = p) (hp2 : p ≠ 2) (hkill : ∀ Q : H, p • Q.val = 0)
  (A : ValuationSubring (AlgebraicClosure K)) (M : WeierstrassCurve A)
  (hM : M.map A.subtype = E.map (algebraMap K (AlgebraicClosure K)))
  (hp : A.valuation (p : AlgebraicClosure K) = 1)
  (hs : ∀ Q : H, HasSmoothReduction M Q.val)
  {x₀ y₀ α : ResidueField A} (F : Frame (M.map (residue A)) x₀ y₀ α)
  (hsep : α ≠ -(M.map (residue A)).a₁ - α)
  (C : CriticalCentre A (kernelModel E H))

include hcard hp2 hkill hp hs F hsep C in
/-- [DkMath.Lib] 標数2・3を含め、同じ標的の中心の剰余xは同じ還元核の候補値に等しい。 -/
theorem nodal_center_residue_eq_candidate_all :
    residue A ⟨C.x, C.x_mem⟩ = (p : ResidueField A) * x₀ -
      ∑ Q : H, (smoothKernelReduction E H A M hM hs Q).xc := by
  let U := valuationKernelModel E H p hkill A M hM hp
  have ho : Odd (Nat.card H) := hcard ▸ (Fact.out : p.Prime).odd_of_ne_two hp2
  let hU := valuationKernelModel_map E H p hkill A M hM hp ho
  let e : ZMod p ≃+ H := addEquivOfPrimeCardEq (Nat.card_zmod p) hcard
  let f := smoothKernelReduction E H A M hM hs
  have hpinj := smoothKernelReduction_injective E H A M hM hs p hkill hp
  have hp0 : (p : ResidueField A) ≠ 0 := by
    have hh := (WeierstrassResidueModel.residue_ne_zero_iff A (p : A)).mpr hp
    simpa only [map_natCast] using hh
  have hC := CriticalCentre.residue_singular_of_model U hU C
  rw [valuationKernelModel_residue_of_smooth E H A M hM hs p hkill hp] at hC
  exact WeierstrassNodalCenterSmallChar.candidate_center_eq_singular (M.map (residue A))
    ((Fact.out : p.Prime).odd_of_ne_two hp2) hp0 e f hpinj (halfKernel E H)
    (halfKernel_partition E H ho) F hsep _ _ hC.1 hC.2

include hcard hp2 hkill hp hs F hsep C in
/-- [DkMath.Lib] 標数2・3を含む同じ滑らかな素数核の全零成分輸送。
中心一致は内部供給する。源のFrameと標的の臨界中心を保持する。 -/
theorem oddKernelPointMap_smooth_of_nodal_all (P : Points E)
    (hP : HasSmoothReduction M P) :
    HasSmoothReduction (valuationKernelModel E H p hkill A M hM hp)
      (oddKernelPointMap E H (hcard ▸ (Fact.out : p.Prime).odd_of_ne_two hp2) P) := by
  exact oddKernelPointMap_smooth_of_candidate E H p hkill A M hM hp hs hcard _ F hsep C
    (nodal_center_residue_eq_candidate_all E H p hcard hp2 hkill A M hM hp hs F hsep C) P hP

include hcard hp2 hkill hp hs F hsep in
/-- [DkMath.Lib] 同じ源のFrameだけから、同じ商標的の中心を内部構成して全零成分を輸送する。
2,3を除外せず、標的中心とその候補一致を外部入力としない。 -/
theorem oddKernelPointMap_smooth_of_nodal_frame (P : Points E)
    (hP : HasSmoothReduction M P) :
    HasSmoothReduction (valuationKernelModel E H p hkill A M hM hp)
      (oddKernelPointMap E H (hcard ▸ (Fact.out : p.Prime).odd_of_ne_two hp2) P) := by
  obtain ⟨T⟩ := exists_nodal_kernel_criticalCentre E H p hcard hp2 hkill A M hM hp hs F hsep
  exact oddKernelPointMap_smooth_of_nodal_all E H p hcard hp2 hkill A M hM hp hs F hsep T P hP

include hcard hp2 hkill hp hs F hsep in
/-- [DkMath.Lib] 同じ実点商準同型の全零成分への制限。
標的の臨界中心と候補一致を内部供給し、同じ一般ファイバーと同じ核を保持する。 -/
noncomputable def nodalZeroComponentHom :
    EllipticSmoothReduction.zeroComponentSubgroup M →+
      EllipticSmoothReduction.zeroComponentSubgroup (valuationKernelModel E H p hkill A M hM hp) := by
  let T := Classical.choice (exists_nodal_kernel_criticalCentre E H p hcard hp2 hkill A M hM hp hs F hsep)
  exact nodalCandidateZeroComponentHom E H p hkill A M hM hp hs hcard (hcard ▸ (Fact.out : p.Prime).odd_of_ne_two hp2) F hsep T
    (nodal_center_residue_eq_candidate_all E H p hcard hp2 hkill A M hM hp hs F hsep T)

/-- [DkMath.Lib] 同じ全零成分制限の零ファイバーは、元の一般ファイバーの同じHに等しい。
滑らかな核を潰すため、制限の単射性は主張しない。 -/
theorem nodalZeroComponentHom_eq_zero_iff (P : EllipticSmoothReduction.zeroComponentSubgroup M) :
    nodalZeroComponentHom E H p hcard hp2 hkill A M hM hp hs F hsep P = 0 ↔
      WeierstrassVariableChange.pointEquivOfModelEq hM P.val ∈ H := by
  let T := Classical.choice (exists_nodal_kernel_criticalCentre E H p hcard hp2 hkill A M hM hp hs F hsep)
  exact nodalCandidateZeroComponentHom_eq_zero_iff E H p hkill A M hM hp hs hcard (hcard ▸ (Fact.out : p.Prime).odd_of_ne_two hp2) F hsep T
    (nodal_center_residue_eq_candidate_all E H p hcard hp2 hkill A M hM hp hs F hsep T) P

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
