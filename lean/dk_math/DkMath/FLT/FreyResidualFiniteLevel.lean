/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyResidualIrreducibility
import DkMath.Lib.NumberTheory.EllipticTorsionRankTwo
import DkMath.Lib.NumberTheory.EllipticTorsionFiniteLevel

#print "file: DkMath.FLT.FreyResidualFiniteLevel"

/-!
# Frey表現の位数providerから次元と有限レベルを取り出す

Sourceの曲線・実際の残余空間・座標作用を変えずに、有限性が得られた後の結論を公開する。
有限性だけで開核と有限レベルが得られ、位数p²があればさらに次元2が得られる。
位数公式は明示的な引数であり、Frey曲線が楕円曲線であることだけからここで証明する
わけではない。有限性が必要な場所を切り分けることで、後の幾何学的providerを接続する。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory
variable {p : ℕ} (S : Source p)

/-- 全点への作用の核。元の同じ残余表現の核である。 -/
noncomputable abbrev residualKernel := S.residualRepresentation.ker

/-- 有限性が供給された場合の開核。次元2や既約性を要求しない。 -/
theorem residualKernel_isOpen [Finite S.ResidualSpace] :
    IsOpen (S.residualKernel : Set (Field.absoluteGaloisGroup ℚ)) :=
  EllipticTorsionRepresentation.representationKernel_isOpen S.rationalCurve p

/-- 模範解答の有限レベル条件と同じ量化。σは有限中間体の全元を固定する。 -/
def ResidualFactorsThroughFiniteLevel : Prop :=
  ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
    ∀ σ : Field.absoluteGaloisGroup ℚ,
      (∀ x ∈ L, σ.toAlgHom x = x) → S.residualRepresentation σ = 1

/-- 実際のE[p]が有限なら、その表現は有限中間体上で定義される。 -/
theorem residual_factorsThroughFiniteLevel [Finite S.ResidualSpace] :
    S.ResidualFactorsThroughFiniteLevel :=
  EllipticTorsionRepresentation.factorsThroughFiniteLevel S.rationalCurve p

/-- 位数p²という幾何学的入力から、同じ空間の次元2を得る。 -/
theorem residual_finrank_eq_two_of_card_sq [Fact p.Prime]
    (hcard : Nat.card S.ResidualSpace = p ^ 2) :
    Module.finrank (ZMod p) S.ResidualSpace = 2 :=
  EllipticTorsionRepresentation.finrank_eq_two_of_card_sq S.rationalCurve p hcard

/-- 位数providerから次元2・開核・有限レベルをまとめて接続する条件付き入口。 -/
theorem residual_profile_of_card_sq [Fact p.Prime]
    (hcard : Nat.card S.ResidualSpace = p ^ 2) :
    Module.finrank (ZMod p) S.ResidualSpace = 2 ∧
      IsOpen (S.residualKernel : Set (Field.absoluteGaloisGroup ℚ)) ∧
      S.ResidualFactorsThroughFiniteLevel := by
  have := EllipticTorsionRepresentation.finite_of_card_sq S.rationalCurve p hcard
  exact ⟨S.residual_finrank_eq_two_of_card_sq hcard,
    S.residualKernel_isOpen, S.residual_factorsThroughFiniteLevel⟩

end DkMath.FLT.Frey.Source
