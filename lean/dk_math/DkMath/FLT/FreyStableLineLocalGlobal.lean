/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyInertiaTransport
import DkMath.FLT.FreyPrimeFiltration
import DkMath.FLT.FreyDyadicInertia
import DkMath.FLT.FreyUnramifiedAway
import DkMath.FLT.FreyRationalTorsionBridge

#print "file: DkMath.FLT.FreyStableLineLocalGlobal"

/-!
# NOTE-031-005: 同じ安定直線の局所条件を合流して大域へ運ぶ

p上で選んだFixedまたはCofixedの側を、全ての素数で保持する。
2上と2,p以外では両方の条件が成立するため、p上の側へ合わせられる。
従って「各場所で独立に二択がある」条件ではなく、全場所共通の側を大域化へ渡せる。

局所合流と大域二択にはbの偶数性は不要である。
同じSourceのbが偶数ならNOTE-030の固定点消滅でFixed側を排除でき、安定直線はCofixedとなる。
可約性からのCofixed直線抽出で、従来入力だったhcasesをこの章が供給する。
既約性へ進む場合にはCofixed直線の不存在hnoを明示入力として残す。
反例の存在、Cofixed直線の不存在、一般FLTの完成は結論しない。
-/
namespace DkMath.FLT.Frey.Source
open Module DkMath.Lib.NumberTheory ValuationInertia
open DkMath.Lib.RepresentationTheory LocalFixedCofixed
variable {p : ℕ} [Fact p.Prime] (S : Source p)

/-- p上の一つの側を、2および2,p以外での両側固定へ合わせて、全素数共通の側にする。
同じNを全場所で保持し、各素数で側を選び直さない。 -/
theorem residual_inertia_common_side_of_stable (hp5 : 5 ≤ p)
    (N : Submodule (ZMod p) S.ResidualSpace) (hN : IsStable S.residualRepresentation N)
    (hbot : N ≠ ⊥) (htop : N ≠ ⊤) :
    (∀ q : ℕ, q.Prime → ∀ A : ValuationSubring (AlgebraicClosure ℚ), LiesOverPrime A q →
      FixedOn S.residualRepresentation N (inertiaSubgroupIn A ℚ)) ∨
    (∀ q : ℕ, q.Prime → ∀ A : ValuationSubring (AlgebraicClosure ℚ), LiesOverPrime A q →
      CofixedOn S.residualRepresentation N (inertiaSubgroupIn A ℚ)) := by
  have hp2 : p ≠ 2 := by omega
  obtain hfixed | hcofixed := S.residual_common_side_at_p hp5 N hN hbot htop
  · left
    intro q hq A hA
    by_cases hqp : q = p
    · subst q
      exact hfixed A hA
    · by_cases hq2 : q = 2
      · subst q
        exact (S.residual_fixed_and_cofixed_at_two hp2 N hN hbot htop A hA).1
      · exact (S.residual_fixed_and_cofixed_away_two_self hp2 hq hq2 hqp A hA N).1
  · right
    intro q hq A hA
    by_cases hqp : q = p
    · subst q
      exact hcofixed A hA
    · by_cases hq2 : q = 2
      · subst q
        exact (S.residual_fixed_and_cofixed_at_two hp2 N hN hbot htop A hA).2
      · exact (S.residual_fixed_and_cofixed_away_two_self hp2 hq hq2 hqp A hA N).2

/-- 全ガロア安定な真の非零部分空間は、大域でFixedまたはCofixedとなる。
全局所条件を実際のFrey算術から供給し、031-001の有限レベル・慣性生成へ渡す。 -/
theorem residual_stable_submodule_fixed_or_cofixed (hp5 : 5 ≤ p)
    (N : Submodule (ZMod p) S.ResidualSpace) (hN : IsStable S.residualRepresentation N)
    (hbot : N ≠ ⊥) (htop : N ≠ ⊤) :
    IsFixedOn S.residualRepresentation N ∨ IsCofixedOn S.residualRepresentation N :=
  S.residual_fixed_or_cofixed_of_inertia_common_side N
    (S.residual_inertia_common_side_of_stable hp5 N hN hbot htop)

/-- 031-005の大域二択。次元1を真の非零条件へ翻訳し、同じ安定直線を大域化する。
b偶数は二択には不要であり、次のFixed側の排除でのみ要求する。 -/
theorem residual_stable_line_fixed_or_cofixed (hp5 : 5 ≤ p)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : finrank (ZMod p) L = 1)
    (hstable : S.IsGaloisStable L) :
    IsFixedOn S.residualRepresentation L ∨ IsCofixedOn S.residualRepresentation L := by
  have := S.rationalCurve_isElliptic
  obtain ⟨hbot, htop⟩ := (proper_nonzero_iff_finrank_one S.residual_finrank_eq_two L).mpr hline
  exact S.residual_stable_submodule_fixed_or_cofixed hp5 L hstable hbot htop

/-- b偶数の同じSourceでは、全ガロア安定直線はCofixedである。
大域二択のFixed側をNOTE-030の実際の有理p-torsion排除で除く。 -/
theorem residual_stable_line_cofixed_of_oriented (hp5 : 5 ≤ p) (hbe : Even S.b)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : finrank (ZMod p) L = 1)
    (hstable : S.IsGaloisStable L) : IsCofixedOn S.residualRepresentation L := by
  have := S.rationalCurve_isElliptic
  have hbot := ((proper_nonzero_iff_finrank_one S.residual_finrank_eq_two L).mpr hline).1
  exact S.residual_isCofixedOn_of_oriented Fact.out hp5 hbe L hbot
    (S.residual_stable_line_fixed_or_cofixed hp5 L hline hstable)

/-- 可約な同じ向き付きSourceからCofixed安定直線を抽出する。
従来のhcasesを上の大域二択で供給し、未証明の局所providerを引数に取らない。 -/
theorem residual_exists_cofixed_line_of_not_irreducible (hp5 : 5 ≤ p) (hbe : Even S.b)
    (hred : ¬ S.ResidualIsIrreducible) :
    ∃ L : Submodule (ZMod p) S.ResidualSpace, finrank (ZMod p) L = 1 ∧
      S.IsGaloisStable L ∧ IsCofixedOn S.residualRepresentation L :=
  S.residual_exists_cofixed_line_of_oriented hp5 hbe hred
    (fun L hline hstable => S.residual_stable_line_fixed_or_cofixed hp5 L hline hstable)

/-- 既約性へ残る算術入力はCofixed安定直線の不存在hnoである。
hcasesと有理p-torsion排除は同じSourceから供給済みだが、hnoそのものは証明しない。 -/
theorem residual_isIrreducible_of_oriented_cofixed_obstruction (hp5 : 5 ≤ p) (hbe : Even S.b)
    (hno : ¬ ∃ L : Submodule (ZMod p) S.ResidualSpace, finrank (ZMod p) L = 1 ∧
      S.IsGaloisStable L ∧ IsCofixedOn S.residualRepresentation L) : S.ResidualIsIrreducible :=
  S.residual_isIrreducible_of_oriented_no_cofixed_line hp5 hbe
    (fun L hline hstable => S.residual_stable_line_fixed_or_cofixed hp5 L hline hstable) hno

end DkMath.FLT.Frey.Source
