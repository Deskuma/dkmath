/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyContinuousKernelCharacters

#print "file: DkMath.FLT.FreyContinuousConnectingComparison"

/-! # 同じ有限捩れ連結 cocycle の連続性と通常 H¹ の比較
新しい H¹ 理論への同型を仮定せず、実際に使う cocycle と連結像を同定する。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)
include hp5 hq hqp haddr hA

/-- 元の有限捩れ点から作る、同じ連続な連結 cocycle。 -/
def ResidualCyclicStage.continuousConnectingCocycle
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :=
  ContinuousTrivialCharacterH1.cocycle (T.continuousKernelCharacter A hp5 hq hqp haddr hA
    (T.fixedCosetKernelElement hp5 hq hqp haddr A hA x))

/-- 実際の連結 cocycle の連続性を内部供給する。 -/
theorem ResidualCyclicStage.continuousConnectingCocycle_continuous
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    Continuous (fun σ : inertiaSubgroupIn A ℚ =>
      T.continuousConnectingCocycle A hp5 hq hqp haddr hA x σ) :=
  ContinuousTrivialCharacterH1.cocycle_continuous _

/-- 連続代表は、通常 H¹ で以前から使用している差分 cocycle と一致する。 -/
theorem ResidualCyclicStage.continuousConnectingCocycle_eq
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    T.continuousConnectingCocycle A hp5 hq hqp haddr hA x =
      TrivialCharacterH1.cocycle (T.inertiaFixedDifferenceCharacter hp5 hq hqp haddr A hA x) := by
  change TrivialCharacterH1.cocycle (T.fixedKernelCharacter A
    (T.fixedCosetKernelElement hp5 hq hqp haddr A hA x)) = _
  rw [T.fixedKernelCharacter_coset A hp5 hq hqp haddr hA x]

/-- 同じ連続 cocycle の通常 H¹ 像は、同じ短完全列の連結像 δ₀ と一致する。 -/
theorem ResidualCyclicStage.continuousConnectingClass_eq_delta
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    groupCohomology.H1π _ (T.continuousConnectingCocycle A hp5 hq hqp haddr hA x) =
      T.fixedConnecting A (T.fixedCosetH0 hp5 hq hqp haddr A hA x) := by
  rw [T.continuousConnectingCocycle_eq A hp5 hq hqp haddr hA x]
  exact (T.fixedCoset_connecting hp5 hq hqp haddr A hA x).symm
end
end DkMath.FLT.Frey.Source

