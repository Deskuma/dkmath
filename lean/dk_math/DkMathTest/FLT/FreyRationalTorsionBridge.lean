/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyRationalTorsionBridge
import DkMathTest.FLT.FreyStableLine

#print "file: DkMathTest.FLT.FreyRationalTorsionBridge"

/-!
# NOTE-030-008: 同じ残余表現への接続と未完成境界の回帰

Source 37ではhratを外部入力に要求しない固定点・cofixed入口を検査する。
反例からの入口では同じ選択済みSourceと正規化の証拠を保持する。
実在するSource 2の固定点を境界として残す。
さらに既存の有限二次元表現でNoNonzeroFixedを証明し、それでも可約であり、
fixed/cofixed二択が出ないことを検査する。Frey表現の代用にはしない。
-/
namespace FreyRationalTorsionBridgeTest
open Module DkMath.FLT.Frey
open DkMath.Lib.NumberTheory EllipticTorsionRepresentation
open DkMath.Lib.RepresentationTheory
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

/-- 同じSource 37の固定点は、明示されたb偶数条件だけで零となる。 -/
theorem source_thirtySeven_fixed_zero (S : Source 37) (hbe : Even S.b)
    (P : S.ResidualSpace) (hP : ∀ σ, S.residualRepresentation σ P = P) : P = 0 :=
  S.residual_fixed_eq_zero_of_oriented (by decide) (by decide) hbe P hP

/-- hratを供給した後のNoNonzeroFixedそのものが、固定された同じSourceの表現で成立する。 -/
theorem source_thirtySeven_no_fixed (S : Source 37) (hbe : Even S.b) :
    NoNonzeroFixed S.residualRepresentation :=
  S.residual_noNonzeroFixed_of_oriented (by decide) (by decide) hbe

/-- 部分加群を点ごとに固定する条件なら零になる。安定性だけを仮定した定理ではない。 -/
theorem source_thirtySeven_fixed_submodule (S : Source 37) (hbe : Even S.b)
    (L : Submodule (ZMod 37) S.ResidualSpace) (hL : IsFixedOn S.residualRepresentation L) : L = ⊥ :=
  S.residual_fixed_submodule_eq_bot_of_oriented (by decide) (by decide) hbe L hL

/-- cofixed抽出にhratは不要になったが、hcasesは依然として明示的な入力である。 -/
theorem source_thirtySeven_cofixed (S : Source 37) (hbe : Even S.b)
    (hred : ¬ S.ResidualIsIrreducible)
    (hcases : ∀ L : Submodule (ZMod 37) S.ResidualSpace, finrank (ZMod 37) L = 1 →
      S.IsGaloisStable L → IsFixedOn S.residualRepresentation L ∨ IsCofixedOn S.residualRepresentation L) :
    ∃ L : Submodule (ZMod 37) S.ResidualSpace, finrank (ZMod 37) L = 1 ∧
      S.IsGaloisStable L ∧ IsCofixedOn S.residualRepresentation L :=
  S.residual_exists_cofixed_line_of_oriented (by decide) hbe hred hcases

/-- 既約性の入口にはhcasesとhnoを残す。二つの未完成算術をテストの仮定で隠さない。 -/
theorem source_thirtySeven_conditional_irreducible (S : Source 37) (hbe : Even S.b)
    (hcases : ∀ L : Submodule (ZMod 37) S.ResidualSpace, finrank (ZMod 37) L = 1 →
      S.IsGaloisStable L → IsFixedOn S.residualRepresentation L ∨ IsCofixedOn S.residualRepresentation L)
    (hno : ¬ ∃ L : Submodule (ZMod 37) S.ResidualSpace, finrank (ZMod 37) L = 1 ∧
      S.IsGaloisStable L ∧ IsCofixedOn S.residualRepresentation L) : S.ResidualIsIrreducible :=
  S.residual_isIrreducible_of_oriented_no_cofixed_line (by decide) hbe hcases hno

/-- 整数反例からの同じSourceの向き付けと、共通因子・符号付き置換の証拠を保持する。 -/
theorem counterexample_thirtySeven_profile (a b c : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (he : a ^ 37 + b ^ 37 = c ^ 37) :
    let S := Source.ofCounterexample 37 (by decide) (by decide) a b c ha hb hc he
    4 ∣ S.a + 1 ∧ Even S.b ∧
      (∃ R : PrimitiveReduction 37 a b c, OrientationTrace R.A R.B R.C S.a S.b S.c) ∧
      NoNonzeroFixed S.residualRepresentation :=
  Source.ofCounterexample_residual_noNonzeroFixed 37 (by decide) (by decide) a b c ha hb hc he

/-- p=2には実際の非零固定点が存在する。完成したp≥5の入口からこの境界を除去しない。 -/
theorem actual_two_fixed_boundary : ¬ (5 ≤ 2) ∧
    ¬ NoNonzeroFixed FreyResidualRepresentationTest.sample.residualRepresentation :=
  ⟨by decide, FreyStableLineTest.actual_two_has_fixed⟩

namespace LinearBoundary
open FreyStableLineTest.DeterminantBoundary
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- 二つの非自明指標g²,g³の対角表現にも、非零固定ベクトルは存在しない。
g=2の両座標の固有値が1と異なることから直接証明する。 -/
theorem diagonal_no_fixed : NoNonzeroFixed rho := by
  intro x hx
  let g : G := ⟨2, 3, by decide, by decide⟩
  have h0 := congrFun (hx g) 0
  have h1 := congrFun (hx g) 1
  change (2 : k) ^ 2 * x 0 = x 0 at h0
  change (2 : k) ^ 3 * x 1 = x 1 at h1
  have hc0 : ((2 : k) ^ 2 - 1) * x 0 = 0 := by linear_combination h0
  have hc1 : ((2 : k) ^ 3 - 1) * x 1 = 0 := by linear_combination h1
  have hz0 : x 0 = 0 := (mul_eq_zero.mp hc0).resolve_left (by decide)
  have hz1 : x 1 = 0 := (mul_eq_zero.mp hc1).resolve_left (by decide)
  funext i
  fin_cases i
  · exact hz0
  · exact hz1

/-- 固定点消滅を加えても安定直線のfixed/cofixed二択は従わない。 -/
theorem no_fixed_without_dichotomy : NoNonzeroFixed rho ∧ IsStable rho line ∧
    ¬ (IsFixedOn rho line ∨ IsCofixedOn rho line) :=
  ⟨diagonal_no_fixed, stable_without_dichotomy⟩

/-- NoNonzeroFixedだけでは既約性も従わない。実際の一次元安定部分空間が残る。 -/
theorem no_fixed_but_reducible : NoNonzeroFixed rho ∧ ¬ IsIrreducible rho := by
  refine ⟨diagonal_no_fixed, ?_⟩
  intro hirr
  have hd : finrank k V = 2 := by simp
  exact (isIrreducible_iff_no_stable_line rho hd).mp hirr ⟨line, line_finrank, line_stable⟩

end LinearBoundary
end FreyRationalTorsionBridgeTest
