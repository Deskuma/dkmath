/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyStableLine
import DkMath.FLT.FreyRationalTorsion

#print "file: DkMath.FLT.FreyRationalTorsionBridge"

/-!
# NOTE-030-008: 有理torsion排除を同じ残余表現の固定点へ接続する

前章のp倍零点の排除をhratとして供給し、既存の固定点の降下同値へ渡す。
固定される幾何学的p-torsion点は同じ有理曲線上の点へ降下するので、同じ点が零となる。
表現・曲線・点・Sourceを取り替えず、p≥5とb偶数を明示する。

これでNoNonzeroFixedと固定部分加群の消滅が得られる。
cofixed直線の抽出には依然として局所慣性などからのfixed/cofixed二択が必要であり、
既約性にはさらにcofixed直線の不存在が必要である。この二入力を引数に残す。
整数反例からの入口では既存の同じ選択済みSourceを使い、共通因子・符号付き置換の証拠も保持する。
NOTE-030の八段階はここで完了するが、一般FLTや無条件既約性の完成は含まない。
-/
namespace DkMath.FLT.Frey.Source
open Module
open DkMath.Lib.NumberTheory EllipticTorsionRepresentation
open DkMath.Lib.RepresentationTheory
variable {p : ℕ} (S : Source p)

/-- 素数p≥5・b偶数の同じSourceには非零ガロア固定残余点が存在しない。
有理torsion排除を入力に要求せず、030-007から証明して一般の降下同値へ渡す。 -/
theorem residual_noNonzeroFixed_of_oriented (hp : p.Prime) (hp5 : 5 ≤ p) (hbe : Even S.b) :
    NoNonzeroFixed S.residualRepresentation :=
  S.residual_noNonzeroFixed_iff_rational_torsion.mpr (S.rational_p_torsion_eq_zero hp hp5 hbe)

/-- 全ガロア元で固定される同じ幾何学的なp-torsion点は零となる。
非零性や有理点への降下のproviderを追加仮定に取らない。 -/
theorem residual_fixed_eq_zero_of_oriented (hp : p.Prime) (hp5 : 5 ≤ p) (hbe : Even S.b)
    (P : S.ResidualSpace) (hP : ∀ σ, S.residualRepresentation σ P = P) : P = 0 :=
  S.residual_noNonzeroFixed_of_oriented hp hp5 hbe P hP

/-- 点ごとに固定される残余部分加群は零である。安定な部分加群全体の消滅とは区別する。 -/
theorem residual_fixed_submodule_eq_bot_of_oriented (hp : p.Prime) (hp5 : 5 ≤ p) (hbe : Even S.b)
    (L : Submodule (ZMod p) S.ResidualSpace) (hL : IsFixedOn S.residualRepresentation L) : L = ⊥ :=
  eq_bot_of_isFixedOn (S.residual_noNonzeroFixed_of_oriented hp hp5 hbe) hL

/-- 非零部分加群の二択が別に得られれば、証明済みの固定点消滅でcofixed側を選べる。
二択自体を、行列式や固定点消滅から導いたとは主張しない。 -/
theorem residual_isCofixedOn_of_oriented (hp : p.Prime) (hp5 : 5 ≤ p) (hbe : Even S.b)
    (L : Submodule (ZMod p) S.ResidualSpace) (hne : L ≠ ⊥)
    (hcases : IsFixedOn S.residualRepresentation L ∨ IsCofixedOn S.residualRepresentation L) :
    IsCofixedOn S.residualRepresentation L :=
  isCofixedOn_of_fixed_or_cofixed (S.residual_noNonzeroFixed_of_oriented hp hp5 hbe) hne hcases

section PrimeField
variable [Fact p.Prime]

/-- 可約性と安定直線の二択を入力とするcofixed直線の抽出。
hratは同じSourceから供給済みなので引数に取らない。hcasesは未供給の算術として明示する。 -/
theorem residual_exists_cofixed_line_of_oriented (hp5 : 5 ≤ p) (hbe : Even S.b)
    (hred : ¬ S.ResidualIsIrreducible)
    (hcases : ∀ L : Submodule (ZMod p) S.ResidualSpace, finrank (ZMod p) L = 1 →
      S.IsGaloisStable L → IsFixedOn S.residualRepresentation L ∨ IsCofixedOn S.residualRepresentation L) :
    ∃ L : Submodule (ZMod p) S.ResidualSpace, finrank (ZMod p) L = 1 ∧
      S.IsGaloisStable L ∧ IsCofixedOn S.residualRepresentation L :=
  S.residual_exists_cofixed_line hred hcases (S.rational_p_torsion_eq_zero Fact.out hp5 hbe)

/-- 二択hcasesとcofixed不存在hnoが別途得られた場合の既約性。
三入力の一般形からhratだけを今回供給したもので、残る二入力を隠さない。 -/
theorem residual_isIrreducible_of_oriented_no_cofixed_line (hp5 : 5 ≤ p) (hbe : Even S.b)
    (hcases : ∀ L : Submodule (ZMod p) S.ResidualSpace, finrank (ZMod p) L = 1 →
      S.IsGaloisStable L → IsFixedOn S.residualRepresentation L ∨ IsCofixedOn S.residualRepresentation L)
    (hno : ¬ ∃ L : Submodule (ZMod p) S.ResidualSpace, finrank (ZMod p) L = 1 ∧
      S.IsGaloisStable L ∧ IsCofixedOn S.residualRepresentation L) : S.ResidualIsIrreducible :=
  S.residual_isIrreducible_of_no_cofixed_line hcases
    (S.rational_p_torsion_eq_zero Fact.out hp5 hbe) hno

end PrimeField

/-- 任意の非零整数反例から選んだ同じSourceにも固定点消滅を供給する。
共通因子を保持するPrimitiveReductionと符号付き置換OrientationTraceを結論へ残し、
元の整数座標と正規化後の座標を同一視しない。反例の存在やFLT終点は使わない。 -/
theorem ofCounterexample_residual_noNonzeroFixed (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (a b c : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (he : a ^ p + b ^ p = c ^ p) :
    let S := Source.ofCounterexample p hp hp5 a b c ha hb hc he
    4 ∣ S.a + 1 ∧ Even S.b ∧
      (∃ R : PrimitiveReduction p a b c, OrientationTrace R.A R.B R.C S.a S.b S.c) ∧
      NoNonzeroFixed S.residualRepresentation := by
  let S := Source.ofCounterexample p hp hp5 a b c ha hb hc he
  obtain ⟨ha4, hbe, htrace⟩ := Source.ofCounterexample_spec p hp hp5 a b c ha hb hc he
  exact ⟨ha4, hbe, htrace, S.residual_noNonzeroFixed_of_oriented hp hp5 hbe⟩

end DkMath.FLT.Frey.Source
