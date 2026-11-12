/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyDecompositionQuotientAction

#print "file: DkMath.FLT.FreyConnectingDecompositionEquivariance"

/-! # 既存 Q/F≃K の同じ連結像を分解群同変にする
同型を作り直さず、作用の輸送と元の coset での計算を明示する。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))
variable (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)
include hp5 hq hqp haddr hA

/-- 元の同じ連結核上の、既存同型を経由した D の整数線形作用。 -/
def ResidualCyclicStage.kernelDecompositionAction :
    A.decompositionSubgroup ℚ →* Module.End ℤ (T.fixedH1CoefficientKernel A) :=
  (T.quotientConnectingKernelEquiv A hp5 hq hqp haddr hA).conjRingEquiv.toMonoidHom.comp
    (T.quotientDecompositionAction A)

/-- 既存の同じ連結同型は D 同変。 -/
theorem ResidualCyclicStage.quotientKernelEquiv_decomposition (σ : A.decompositionSubgroup ℚ)
    (z : T.fixedQuotientCoefficient A) :
    T.kernelDecompositionAction A hp5 hq hqp haddr hA σ
      (T.quotientConnectingKernelEquiv A hp5 hq hqp haddr hA z) =
    T.quotientConnectingKernelEquiv A hp5 hq hqp haddr hA (T.quotientDecompositionAction A σ z) := by
  change (T.quotientConnectingKernelEquiv A hp5 hq hqp haddr hA)
    (T.quotientDecompositionAction A σ ((T.quotientConnectingKernelEquiv A hp5 hq hqp haddr hA).symm
      (T.quotientConnectingKernelEquiv A hp5 hq hqp haddr hA z))) = _
  rw [LinearEquiv.symm_apply_apply]

/-- 元の点の核元を輸送すると、輸送した同じ点の核元になる。 -/
theorem ResidualCyclicStage.kernelDecompositionAction_coset (σ : A.decompositionSubgroup ℚ)
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    T.kernelDecompositionAction A hp5 hq hqp haddr hA σ
      (T.fixedCosetKernelElement hp5 hq hqp haddr A hA x) =
    T.fixedCosetKernelElement hp5 hq hqp haddr A hA (ResidualCyclicStage.globalTranslateTorsion σ.val x) := by
  rw [← T.quotientKernelEquiv_coset A hp5 hq hqp haddr hA x, T.quotientKernelEquiv_decomposition A hp5 hq hqp haddr hA]
  exact T.quotientKernelEquiv_coset A hp5 hq hqp haddr hA _
end
end DkMath.FLT.Frey.Source

