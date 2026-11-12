/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyResidualRepresentation
import DkMath.Lib.NumberTheory.EllipticTorsionStandardEquiv

#print "file: DkMath.FLT.FreyResidualIrreducibility"

/-!
# 同じFrey Sourceに対する既約性の証明目標

実際の残余空間と標準torsionByの間で、点・線形構造・ガロア作用を同時に保つ。
安定部分加群の条件と既約性の条件は、この同変同型を通じて相互翻訳される。
将来のMazur型入力が満たすべき命題を固定する章であり、既約性を仮定なしに結論しない。
非零性を別途含めるので、次元2がまだ供給されていない段階にも意味が明確である。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory
variable {p : ℕ} (S : Source p)

/-- 同じ実際のE[p]におけるガロア安定部分加群。 -/
def IsGaloisStable (N : Submodule (ZMod p) S.ResidualSpace) : Prop :=
  DkMath.Lib.RepresentationTheory.IsStable S.residualRepresentation N

/-- Frey表現の既約性という証明目標。非零性も含む。 -/
def ResidualIsIrreducible : Prop :=
  DkMath.Lib.RepresentationTheory.IsIrreducible S.residualRepresentation

/-- 同じ曲線の標準整数torsion表示への、点を保つ線形同型。 -/
noncomputable def residualStandardEquiv :
    S.ResidualSpace ≃ₗ[ZMod p]
      EllipticTorsionRepresentation.StandardTorsion S.rationalCurve p :=
  EllipticTorsionRepresentation.torsionByLinearEquiv S.rationalCurve p

/-- Frey Source上の線形アダプタは、ガロア作用と可換する。 -/
theorem residualStandardEquiv_equivariant (σ : Field.absoluteGaloisGroup ℚ)
    (P : S.ResidualSpace) :
    S.residualStandardEquiv (S.residualRepresentation σ P) =
      EllipticTorsionRepresentation.standardRepresentation S.rationalCurve p σ
        (S.residualStandardEquiv P) := rfl

/-- 安定部分加群の条件を、同じ曲線の標準表示へ相互翻訳する。 -/
theorem residual_standard_isStable_iff (N : Submodule (ZMod p) S.ResidualSpace) :
    DkMath.Lib.RepresentationTheory.IsStable
      (EllipticTorsionRepresentation.standardRepresentation S.rationalCurve p)
      (N.map S.residualStandardEquiv.toLinearMap) ↔ S.IsGaloisStable N :=
  DkMath.Lib.RepresentationTheory.isStable_map_iff _ _ _
    S.residualStandardEquiv_equivariant N

/-- 標準torsion表示での既約性との同値。既約性自体のproviderではない。 -/
theorem residual_standard_isIrreducible_iff :
    S.ResidualIsIrreducible ↔ DkMath.Lib.RepresentationTheory.IsIrreducible
      (EllipticTorsionRepresentation.standardRepresentation S.rationalCurve p) :=
  EllipticTorsionRepresentation.standard_isIrreducible_iff S.rationalCurve p

/-- 既約性の定義を、非零性と全ての安定部分加群の分類という形で展開する。 -/
theorem residual_isIrreducible_iff :
    S.ResidualIsIrreducible ↔ Nontrivial S.ResidualSpace ∧
      ∀ N, S.IsGaloisStable N → N = ⊥ ∨ N = ⊤ := Iff.rfl

end DkMath.FLT.Frey.Source
