/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyStableLineLocalGlobal
import DkMathTest.FLT.FreyRationalTorsionBridge
import DkMathTest.FLT.InertiaLocalGlobal

#print "file: DkMathTest.FLT.FreyStableLineLocalGlobal"

/-!
# NOTE-031-005: 追加providerのない指数37の接続と、論理的境界

Source37の全ガロア二択には局所条件を追加せず、Cofixed抽出にはhcasesを追加しない。
既約性の入口にはhnoだけを残す。反例の入口では同じ選択済みSourceの原始化と向き付けの証拠を保持する。
Source37や整数反例の存在を主張する回帰ではなく、公開APIの供給条件を固定する。
p=2の実際の固定点、および各局所群で独立した二択では大域化できない有限表現も境界に残す。
-/
namespace FreyStableLineLocalGlobalTest
open Module DkMath.FLT.Frey
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory LocalFixedCofixed
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

/-- 指数37の大域二択はhbeやhlocalを要求せず、同じ安定直線について成立する。 -/
theorem source37_dichotomy (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hline : finrank (ZMod 37) L = 1) (hstable : S.IsGaloisStable L) :
    IsFixedOn S.residualRepresentation L ∨ IsCofixedOn S.residualRepresentation L :=
  S.residual_stable_line_fixed_or_cofixed (by decide) L hline hstable

/-- b偶数なら、任意の同じ安定直線の商は全ガロア群で固定される。 -/
theorem source37_stable_line_cofixed (S : Source 37) (hbe : Even S.b)
    (L : Submodule (ZMod 37) S.ResidualSpace) (hline : finrank (ZMod 37) L = 1)
    (hstable : S.IsGaloisStable L) : IsCofixedOn S.residualRepresentation L :=
  S.residual_stable_line_cofixed_of_oriented (by decide) hbe L hline hstable

/-- 可約性からのCofixed直線抽出では、hcasesを外部入力へ戻さない。 -/
theorem source37_cofixed_of_reducible (S : Source 37) (hbe : Even S.b)
    (hred : ¬ S.ResidualIsIrreducible) :
    ∃ L : Submodule (ZMod 37) S.ResidualSpace, finrank (ZMod 37) L = 1 ∧
      S.IsGaloisStable L ∧ IsCofixedOn S.residualRepresentation L :=
  S.residual_exists_cofixed_line_of_not_irreducible (by decide) hbe hred

/-- 既約性は条件付きであり、残るhnoを明示する。hcasesやhratは要求しない。 -/
theorem source37_irreducible_with_obstruction (S : Source 37) (hbe : Even S.b)
    (hno : ¬ ∃ L : Submodule (ZMod 37) S.ResidualSpace, finrank (ZMod 37) L = 1 ∧
      S.IsGaloisStable L ∧ IsCofixedOn S.residualRepresentation L) : S.ResidualIsIrreducible :=
  S.residual_isIrreducible_of_oriented_cofixed_obstruction (by decide) hbe hno

/-- 非零整数反例からの同じSourceを使い、共通因子と符号付き置換の証拠を残す。 -/
theorem counterexample37_profile (a b c : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (he : a ^ 37 + b ^ 37 = c ^ 37) :
    let S := Source.ofCounterexample 37 (by decide) (by decide) a b c ha hb hc he
    ¬ S.ResidualIsIrreducible →
      4 ∣ S.a + 1 ∧ Even S.b ∧
        (∃ R : PrimitiveReduction 37 a b c, OrientationTrace R.A R.B R.C S.a S.b S.c) ∧
        ∃ L : Submodule (ZMod 37) S.ResidualSpace, finrank (ZMod 37) L = 1 ∧
          S.IsGaloisStable L ∧ IsCofixedOn S.residualRepresentation L :=
  Source.ofCounterexample_residual_exists_cofixed_line (by decide) a b c ha hb hc he

/-- p≥5の条件を落とさない。指数2の実在するSourceには非零の固定残余点がある。 -/
theorem actual_two_boundary : ¬ (5 ≤ 2) ∧
    ¬ NoNonzeroFixed FreyResidualRepresentationTest.sample.residualRepresentation :=
  FreyRationalTorsionBridgeTest.actual_two_fixed_boundary

/-- 一次元安定部分空間を持つ有限二次元表現では、各局所群での二択だけでは大域二択にならない。 -/
theorem incompatible_local_sides_boundary :
    let B := InertiaLocalGlobalTest.SideBoundary.line
    finrank InertiaLocalGlobalTest.SideBoundary.k B = 1 ∧
      (∀ i, FixedOn InertiaLocalGlobalTest.SideBoundary.rho B
          (InertiaLocalGlobalTest.SideBoundary.localGroups i) ∨
        CofixedOn InertiaLocalGlobalTest.SideBoundary.rho B
          (InertiaLocalGlobalTest.SideBoundary.localGroups i)) ∧
      ¬ (IsFixedOn InertiaLocalGlobalTest.SideBoundary.rho B ∨
        IsCofixedOn InertiaLocalGlobalTest.SideBoundary.rho B) :=
  ⟨InertiaLocalGlobalTest.SideBoundary.line_finrank,
    InertiaLocalGlobalTest.SideBoundary.pointwise_local_alternative,
    fun h => h.elim InertiaLocalGlobalTest.SideBoundary.not_global_fixed
      InertiaLocalGlobalTest.SideBoundary.not_global_cofixed⟩

end FreyStableLineLocalGlobalTest
