/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelNodalTransport
import DkMath.Lib.NumberTheory.EllipticFiniteKernelNodalReduction

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelCriticalCentre"

/-!
# 同じ節点商標的の臨界中心を内部構成する

[DkMath.Lib] 同じ商モデルの整性、判別式非零、剰余での節点不変量を組み合わせる。
源のFrameが与えられれば、既存の臨界中心存在定理が同じ商標的の中心を供給する。
2・3を含む任意の剰余標数で成立し、中心一致の証明とは独立している。
-/
namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel
open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open EllipticTorsionRepresentation EllipticGoodReductionSeparation EllipticCriticalCentre
open EllipticNodalTorsion.NodalTorsion
noncomputable local instance instDecidableEqEllipticFiniteKernelCriticalCentre {α : Type*} : DecidableEq α :=
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

include p hcard hp2 hkill hM hp hs F hsep in
/-- [DkMath.Lib] 同じ滑らかな核の商標的には、同じ付値環上の臨界中心が存在する。
源の節点Frameと核条件からΔ非単元性・c₄単元性を供給し、同じ商の楕円性を使う。 -/
theorem exists_nodal_kernel_criticalCentre : Nonempty (CriticalCentre A (kernelModel E H)) := by
  have ho : Odd (Nat.card H) := hcard ▸ (Fact.out : p.Prime).odd_of_ne_two hp2
  let U := valuationKernelModel E H p hkill A M hM hp
  have hU : U.map A.subtype = kernelModel E H := valuationKernelModel_map E H p hkill A M hM hp ho
  have hi := kernelModel_nodal_conditions E H hcard hp2 hkill A M hM hp (Or.inl hs) F hsep
  apply EllipticCriticalCentre.exists_criticalCentre A (kernelModel E H)
  · rw [← hU, map_a₁]; exact U.a₁.property
  · rw [← hU, map_a₂]; exact U.a₂.property
  · rw [← hU, map_a₃]; exact U.a₃.property
  · rw [← hU, map_a₄]; exact U.a₄.property
  · rw [← hU, map_a₆]; exact U.a₆.property
  · exact kernelModel_discriminant_ne_zero_of_odd_card E H ho
  · exact hi.1
  · exact hi.2

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
