/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelSmoothReduction
import DkMath.Lib.NumberTheory.WeierstrassNodalVelu

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelNodalReduction"

/-!
# 同じ素数位数核の節点商と局所還元条件

[DkMath.Lib] 前章の同じ付値環標的・同じ還元準同型へ節点商公式を接続する。
核の素数位数から巡回表示を内部構成する。半核は元のHのままである。
滑らかな側は原始根モーメント、特異な側は剰余一致で処理し、両側でΔ非単元・c₄単元を得る。
この段階でもΔの深さや源の全零成分の点の輸送は結論しない。
-/
namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel
open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open EllipticTorsionRepresentation EllipticGoodReductionSeparation WeierstrassVeluPolynomial
open EllipticNodalTorsion.NodalTorsion WeierstrassResidueModel
open DkMath.Lib.Algebra.FiniteInversionHalf
noncomputable local instance instDecidableEqEllipticFiniteKernelNodalReduction {α : Type*} : DecidableEq α :=
  Classical.decEq _
variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
  (H : AddSubgroup (Points E)) [Fintype H] {p : ℕ} [Fact p.Prime]
  (hcard : Nat.card H = p) (hp2 : p ≠ 2) (hkill : ∀ Q : H, p • Q.val = 0)
  (A : ValuationSubring (AlgebraicClosure K)) (M : WeierstrassCurve A)
  (hM : M.map A.subtype = E.map (algebraMap K (AlgebraicClosure K)))
  (hp : A.valuation (p : AlgebraicClosure K) = 1)

omit [E.IsElliptic] in
include hcard hp2 in
/-- [DkMath.Lib] 同じ滑らかな素数位数核の剰余標的に、節点商の三つの不変量公式を供給する。
巡回表示と奇数性は同じHの位数から内部構成する。 -/
theorem valuationKernelModel_nodal_invariants_of_smooth
    (hs : ∀ Q : H, HasSmoothReduction M Q.val)
    {x₀ y₀ α : ResidueField A} (F : Frame (M.map (residue A)) x₀ y₀ α)
    (hsep : α ≠ -(M.map (residue A)).a₁ - α) :
    ((valuationKernelModel E H p hkill A M hM hp).map (residue A)).c₄ =
        (p : ResidueField A) ^ 4 * (M.map (residue A)).c₄ ∧
      ((valuationKernelModel E H p hkill A M hM hp).map (residue A)).c₆ =
        (p : ResidueField A) ^ 6 * (M.map (residue A)).c₆ ∧
      ((valuationKernelModel E H p hkill A M hM hp).map (residue A)).Δ = 0 := by
  have ho : Odd (Nat.card H) := hcard ▸ (Nat.Prime.odd_of_ne_two (Fact.out : p.Prime) hp2)
  let e : ZMod p ≃+ H := addEquivOfPrimeCardEq (Nat.card_zmod p) hcard
  rw [valuationKernelModel_residue_of_smooth E H A M hM hs p hkill hp]
  exact WeierstrassNodalVelu.polynomialModel_invariants _ (Nat.Prime.odd_of_ne_two (Fact.out : p.Prime) hp2)
    e (smoothKernelReduction E H A M hM hs) (smoothKernelReduction_injective E H A M hM hs p hkill hp)
    (halfKernel E H) (halfKernel_partition E H ho) F hsep

omit [E.IsElliptic] in
include hcard hp2 in
/-- [DkMath.Lib] 同じ核の両側を処理し、付値環標的の節点性を得る。
滑らかな側ではpが剰余で非零、特異な側では同じ源との剰余一致を使う。 -/
theorem valuationKernelModel_nodal_invariants
    (hcases : (∀ Q : H, HasSmoothReduction M Q.val) ∨
      (∀ Q : H, Q.val ≠ 0 → ¬ HasSmoothReduction M Q.val))
    {x₀ y₀ α : ResidueField A} (F : Frame (M.map (residue A)) x₀ y₀ α)
    (hsep : α ≠ -(M.map (residue A)).a₁ - α) :
    ((valuationKernelModel E H p hkill A M hM hp).map (residue A)).Δ = 0 ∧
      ((valuationKernelModel E H p hkill A M hM hp).map (residue A)).c₄ ≠ 0 := by
  have hsrc := WeierstrassNodalFrame.nodal_invariants F hsep
  rcases hcases with hs | hs
  · have hi := valuationKernelModel_nodal_invariants_of_smooth E H hcard hp2 hkill A M hM hp hs F hsep
    have hp0 : (p : ResidueField A) ≠ 0 := by
      have hh := (residue_ne_zero_iff A (p : A)).mpr hp
      simpa only [map_natCast] using hh
    exact ⟨hi.2.2,hi.1 ▸ mul_ne_zero (pow_ne_zero 4 hp0) hsrc.2⟩
  · rw [valuationKernelModel_residue_eq_of_not_smooth E H p hkill A M hM hp hs]
    exact hsrc

include p hcard hp2 hkill hM hp in
/-- [DkMath.Lib] 同じ既存kernelModelのΔ非単元性・c₄単元性。局所核の分岐は結論から除去する。
一般ファイバーのモデル同定を保持し、剰余だけの別モデルに結論を留めない。 -/
theorem kernelModel_nodal_conditions
    (hcases : (∀ Q : H, HasSmoothReduction M Q.val) ∨
      (∀ Q : H, Q.val ≠ 0 → ¬ HasSmoothReduction M Q.val))
    {x₀ y₀ α : ResidueField A} (F : Frame (M.map (residue A)) x₀ y₀ α)
    (hsep : α ≠ -(M.map (residue A)).a₁ - α) :
    A.valuation (kernelModel E H).Δ < 1 ∧ A.valuation (kernelModel E H).c₄ = 1 := by
  have ho : Odd (Nat.card H) := hcard ▸ (Nat.Prime.odd_of_ne_two (Fact.out : p.Prime) hp2)
  have hi := valuationKernelModel_nodal_invariants E H hcard hp2 hkill A M hM hp hcases F hsep
  have hd := congrArg WeierstrassCurve.Δ (valuationKernelModel_map E H p hkill A M hM hp ho)
  have hc := congrArg WeierstrassCurve.c₄ (valuationKernelModel_map E H p hkill A M hM hp ho)
  simp only [map_Δ] at hd
  simp only [map_c₄] at hc
  simp only [map_Δ,map_c₄] at hi
  rw [← hd,← hc]
  exact ⟨(residue_zero_iff A _).mp hi.1,(residue_ne_zero_iff A _).mp hi.2⟩

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
