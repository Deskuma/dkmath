/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticTorsionContinuity

#print "file: DkMath.Lib.NumberTheory.EllipticTorsionFiniteLevel"

/-!
# 有限torsionから開核・有限レベルへ

各点の固定部分群の開性は既に座標の代数性から証明した。E[n]が有限なら、
全作用の核は有限個の開固定部分群の共通部分となり、開く。
Krull位相の単位元近傍の基底は有限中間体の固定部分群なので、ある有限中間体Lの
固定部分群が核に含まれる。従ってLを固定する全ての自己同型は全torsion点を固定する。

これは `Definitions/Def_GaloisRep_Residual.lean` の有限レベル条件に対応する。
さらに正規な有限中間体を選べることもKrull近傍の正規閉包版から従う。
この章は実際のE[n]の有限性を引数として要求し、その幾何学的証明を隠さない。
局所慣性の自明性やWeil対についての主張ではない。
-/
namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
variable {K : Type*} [Field K] (E : WeierstrassCurve K) (n : ℕ)

/-- 全torsion点への作用が恒等となる、実際の表現の核。 -/
noncomputable def representationKernel : Subgroup (Field.absoluteGaloisGroup K) :=
  (representation E n).ker

/-- 表現の核は、各点の固定部分群の共通部分と一致する。 -/
theorem representationKernel_eq_iInter :
    (representationKernel E n : Set (Field.absoluteGaloisGroup K)) =
      ⋂ P : Torsion E n,
        (MulAction.stabilizer (Field.absoluteGaloisGroup K) P : Set (Field.absoluteGaloisGroup K)) := by
  ext σ
  change representation E n σ = 1 ↔ _
  simp only [Set.mem_iInter]
  constructor
  · intro h P
    change representation E n σ P = P
    rw [h]
    rfl
  · intro h
    apply LinearMap.ext
    exact h

/-- 有限性と各点の開固定部分群を合わせて、表現全体の核の開性を得る。 -/
theorem representationKernel_isOpen [Finite (Torsion E n)] :
    IsOpen (representationKernel E n : Set (Field.absoluteGaloisGroup K)) := by
  rw [representationKernel_eq_iInter]
  exact isOpen_iInter_of_finite (torsion_stabilizer_isOpen E n)

/-- 有限中間体Lを固定する自己同型が、全torsion点に恒等に作用するという条件。 -/
def FactorsThroughFiniteLevel : Prop :=
  ∃ L : IntermediateField K (AlgebraicClosure K), FiniteDimensional K L ∧
    ∀ σ : Field.absoluteGaloisGroup K,
      (∀ x ∈ L, σ.toAlgHom x = x) → representation E n σ = 1

/-- 有限torsionの連続表現は有限レベルを持つ。正規な有限中間体も選べる。 -/
theorem exists_normal_finite_level [Finite (Torsion E n)] :
    ∃ L : IntermediateField K (AlgebraicClosure K),
      FiniteDimensional K L ∧ Normal K L ∧
        L.fixingSubgroup ≤ representationKernel E n := by
  have hn := (representationKernel_isOpen E n).mem_nhds (representationKernel E n).one_mem
  exact (krullTopology_mem_nhds_one_iff_of_normal K (AlgebraicClosure K) _).mp hn

/-- 模範解答と同じ、有限中間体による固定条件の形で因子化を公開する。 -/
theorem factorsThroughFiniteLevel [Finite (Torsion E n)] : FactorsThroughFiniteLevel E n := by
  obtain ⟨L, hfin, _, hker⟩ := exists_normal_finite_level E n
  refine ⟨L, hfin, fun σ hσ => ?_⟩
  apply hker
  exact (IntermediateField.mem_fixingSubgroup_iff L σ).mpr hσ

end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
