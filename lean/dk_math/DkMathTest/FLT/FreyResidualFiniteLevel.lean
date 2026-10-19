/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyResidualFiniteLevel
import DkMathTest.FLT.FreyResidualRepresentation

#print "file: DkMathTest.FLT.FreyResidualFiniteLevel"

/-!
# NOTE-011: 点を保つ同変アダプタ、非零条件、有限レベルの回帰

実在するSource 2の非零点を標準torsionByへ移し、非零性と固定性が残ることを調べる。
その点の生成する部分加群は実際に安定である。E[1]では空間が零になるため、
安定部分加群の分類だけでは既約性を主張できない。有限レベルの定理はE[1]には
無条件に適用でき、Source 37には有限性または位数providerを明示して適用する。
-/
namespace FreyResidualFiniteLevelTest
open DkMath.FLT.Frey
open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open FreyResidualRepresentationTest

/-- 実際の非零2-torsion点は標準表示でも非零である。 -/
theorem standardTwoPoint_ne_zero : sample.residualStandardEquiv twoPoint ≠ 0 := by
  intro h
  apply twoPoint_ne_zero
  apply sample.residualStandardEquiv.injective
  simpa only [map_zero] using h

/-- 同変性により、同じ有理点の標準表示も全ガロア元で固定される。 -/
theorem standardTwoPoint_fixed (σ : Field.absoluteGaloisGroup ℚ) :
    standardRepresentation sample.rationalCurve 2 σ (sample.residualStandardEquiv twoPoint) =
      sample.residualStandardEquiv twoPoint := by
  rw [← sample.residualStandardEquiv_equivariant, twoPoint_fixed]

/-- 固定された点の生成する部分加群は、線形性から安定になる。 -/
theorem twoPoint_span_stable :
    sample.IsGaloisStable (Submodule.span (ZMod 2) {twoPoint}) := by
  intro σ x hx
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
  rw [map_smul, twoPoint_fixed]
  exact Submodule.smul_mem _ a (Submodule.mem_span_singleton_self twoPoint)

/-- 上の安定部分加群は零部分加群ではない。 -/
theorem twoPoint_span_ne_bot : Submodule.span (ZMod 2) {twoPoint} ≠ ⊥ := by
  intro h
  have hm := Submodule.mem_span_singleton_self (R := ZMod 2) twoPoint
  rw [h] at hm
  exact twoPoint_ne_zero hm

/-- E[1]が零であることを、既約性の非零条件の回帰に使う。 -/
theorem torsionOne_subsingleton (E : WeierstrassCurve ℚ) : Subsingleton (Torsion E 1) :=
  ⟨fun P Q => (torsion_one_eq_zero E P).trans (torsion_one_eq_zero E Q).symm⟩

/-- 零空間の表現は、非零条件を持つ今回の意味では既約でない。 -/
theorem torsionOne_not_irreducible (E : WeierstrassCurve ℚ) : ¬ IsIrreducible E 1 := by
  intro h
  have := torsionOne_subsingleton E
  exact not_nontrivial (Torsion E 1) h.1

/-- E[1]では有限性を実証できるので、有限レベルを無条件に得られる。 -/
theorem torsionOne_finite_level (E : WeierstrassCurve ℚ) : FactorsThroughFiniteLevel E 1 := by
  have := torsionOne_subsingleton E
  exact factorsThroughFiniteLevel E 1

/-- 37次では標準表示の位数公式を受け取り、同じ実際の空間の次元2を得る。 -/
theorem source37_standard_rank (S : Source 37)
    (hcard : Nat.card (StandardTorsion S.rationalCurve 37) = 37 ^ 2) :
    Module.finrank (ZMod 37) S.ResidualSpace = 2 := by
  have : Fact (Nat.Prime 37) := ⟨by decide⟩
  exact finrank_eq_two_of_standard_card_sq S.rationalCurve 37 hcard

/-- 37次の位数入力は、次元・開核・有限レベルを同じ曲線上でまとめて供給する。 -/
theorem source37_profile (S : Source 37) (hcard : Nat.card S.ResidualSpace = 37 ^ 2) :
    Module.finrank (ZMod 37) S.ResidualSpace = 2 ∧
      IsOpen (S.residualKernel : Set (Field.absoluteGaloisGroup ℚ)) ∧
      S.ResidualFactorsThroughFiniteLevel := by
  have : Fact (Nat.Prime 37) := ⟨by decide⟩
  exact S.residual_profile_of_card_sq hcard

example : (sample.residualStandardEquiv twoPoint).val = twoPoint.val := rfl

example (N : Submodule (ZMod 2) sample.ResidualSpace) :
    DkMath.Lib.RepresentationTheory.IsStable (standardRepresentation sample.rationalCurve 2)
      (N.map sample.residualStandardEquiv.toLinearMap) ↔ sample.IsGaloisStable N :=
  sample.residual_standard_isStable_iff N

example (S : Source 37) :
    S.ResidualIsIrreducible ↔ DkMath.Lib.RepresentationTheory.IsIrreducible
      (standardRepresentation S.rationalCurve 37) := S.residual_standard_isIrreducible_iff

example (S : Source 37) [Finite S.ResidualSpace] :
    ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ),
      FiniteDimensional ℚ L ∧ Normal ℚ L ∧ L.fixingSubgroup ≤ S.residualKernel :=
  exists_normal_finite_level S.rationalCurve 37

end FreyResidualFiniteLevelTest
