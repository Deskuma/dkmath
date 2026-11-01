/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyHnoSmallIndex
import DkMath.FLT.FreyHnoRegularPrime
import DkMath.FLT.FreyModEightIrreducibility
import DkMath.FLT.FreyMazurLocalInputs

#print "file: DkMath.FLT.FreyHnoHardCase"

/-!
# 一般 hno の残存分岐を確定する

`p ≥ 5` と元の向き付け `4 ∣ a+1` のもとで Cofixed 直線が残るとする。
小指数は既存 FLT で除かれ、`a ≡ 3 (mod 8)` は既存の局所枝交換で除かれる。
従って残るのは `p ≥ 17`, `a ≡ 7 (mod 8)` の枝だけである。
完成済み GN–Kummer FLT は正則素数も排除し、残存指数が円分体の類群濃度を
割ることを証明する。さらに各 `q < p` の良還元による排除から `primorial(p-1) ∣ abc` が従う。

本章はこの三条件を**矛盾とはしない**。最後の同値は一般 hno を残存枝の排除へ
正規化するものである。新たな算術的排除を仮定する provider は導入しない。
本章は小指数 FLT を使用する上位層なので、その FLT 証明へ戻してはならない。
-/

namespace DkMath.FLT.Frey.Source

open DkMath.Lib.RepresentationTheory
open scoped NumberField

variable {p : ℕ} [Fact p.Prime] (S : Source p)

/-- 生き残る Cofixed 直線が強制する三条件。位数や合同の必要条件と、
大域的矛盾そのものを区別する。 -/
theorem residual_cofixed_line_forces_hard_case
    (hp5 : 5 ≤ p) (ha4 : (4 : ℤ) ∣ S.a + 1)
    (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (hstable : S.IsGaloisStable L)
    (hcofixed : IsCofixedOn S.residualRepresentation L) :
    17 ≤ p ∧ S.a % 8 = 7 ∧ (primorial (p - 1) : ℤ) ∣ S.a * S.b * S.c := by
  have hp17 := S.seventeen_le_of_five_le hp5
  have ha7 : S.a % 8 = 7 := by
    rcases S.a_mod_eight_cases_of_oriented ha4 with h3 | h7
    · exact (S.residual_no_cofixed_line_of_a_mod_eight hp5 h3
        ⟨L, hline, hstable, hcofixed⟩).elim
    · exact h7
  exact ⟨hp17, ha7, S.residual_cofixed_forces_primorial_support
    hp5 (S.b_even_of_a_mod_eight_seven ha7) hline hstable hcofixed⟩

/-- 正則素数の排除も含めた残存分岐。最後の可除性は Source 自体から従い、
Cofixed 性や局所条件から正則性を否定したものではない。 -/
theorem residual_cofixed_line_forces_irregular_hard_case
    (hp5 : 5 ≤ p) (ha4 : (4 : ℤ) ∣ S.a + 1)
    (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (hstable : S.IsGaloisStable L)
    (hcofixed : IsCofixedOn S.residualRepresentation L) :
    17 ≤ p ∧ S.a % 8 = 7 ∧ (primorial (p - 1) : ℤ) ∣ S.a * S.b * S.c ∧
      p ∣ Fintype.card (ClassGroup (𝓞 (CyclotomicField p ℚ))) := by
  obtain ⟨hp, ha, hd⟩ := S.residual_cofixed_line_forces_hard_case hp5 ha4 L hline hstable hcofixed
  exact ⟨hp, ha, hd, S.prime_dvd_cyclotomic_classGroup_card hp5⟩

/-- Cofixed 直線の存在と、大指数・7側・primorial 支持を全て満たす直線の存在は同値。
右辺でも元の Source と同じ直線を保持する。 -/
theorem residual_cofixed_exists_iff_hard_case
    (hp5 : 5 ≤ p) (ha4 : (4 : ℤ) ∣ S.a + 1) :
    (∃ L : Submodule (ZMod p) S.ResidualSpace,
      Module.finrank (ZMod p) L = 1 ∧ S.IsGaloisStable L ∧
        IsCofixedOn S.residualRepresentation L) ↔
      17 ≤ p ∧ S.a % 8 = 7 ∧ (primorial (p - 1) : ℤ) ∣ S.a * S.b * S.c ∧
        ∃ L : Submodule (ZMod p) S.ResidualSpace,
          Module.finrank (ZMod p) L = 1 ∧ S.IsGaloisStable L ∧
            IsCofixedOn S.residualRepresentation L := by
  constructor
  · rintro ⟨L, hl, hs, hc⟩
    obtain ⟨hp, ha, hd⟩ := S.residual_cofixed_line_forces_hard_case hp5 ha4 L hl hs hc
    exact ⟨hp, ha, hd, L, hl, hs, hc⟩
  · rintro ⟨_, _, _, hL⟩
    exact hL

/-- 一般 hno の正確な残存命題。右辺は未証明の排除目標であり、この同値自体は
その排除の証明でも、hno 完成の宣言でもない。 -/
theorem residual_hno_iff_no_hard_case
    (hp5 : 5 ≤ p) (ha4 : (4 : ℤ) ∣ S.a + 1) :
    (¬ ∃ L : Submodule (ZMod p) S.ResidualSpace,
      Module.finrank (ZMod p) L = 1 ∧ S.IsGaloisStable L ∧
        IsCofixedOn S.residualRepresentation L) ↔
      ¬ (17 ≤ p ∧ S.a % 8 = 7 ∧ (primorial (p - 1) : ℤ) ∣ S.a * S.b * S.c ∧
        ∃ L : Submodule (ZMod p) S.ResidualSpace,
          Module.finrank (ZMod p) L = 1 ∧ S.IsGaloisStable L ∧
            IsCofixedOn S.residualRepresentation L) :=
  not_congr (S.residual_cofixed_exists_iff_hard_case hp5 ha4)

/-- 一般 hno を、非正則側の大指数・7側・primorial 支持ありの枝の排除へ縮約する。
これ以上の大域排除は本章の結論に含めない。 -/
theorem residual_hno_iff_no_irregular_hard_case
    (hp5 : 5 ≤ p) (ha4 : (4 : ℤ) ∣ S.a + 1) :
    (¬ ∃ L : Submodule (ZMod p) S.ResidualSpace,
      Module.finrank (ZMod p) L = 1 ∧ S.IsGaloisStable L ∧
        IsCofixedOn S.residualRepresentation L) ↔
      ¬ (p ∣ Fintype.card (ClassGroup (𝓞 (CyclotomicField p ℚ))) ∧
        17 ≤ p ∧ S.a % 8 = 7 ∧ (primorial (p - 1) : ℤ) ∣ S.a * S.b * S.c ∧
        ∃ L : Submodule (ZMod p) S.ResidualSpace,
          Module.finrank (ZMod p) L = 1 ∧ S.IsGaloisStable L ∧
            IsCofixedOn S.residualRepresentation L) := by
  apply not_congr
  constructor
  · intro hL
    exact ⟨S.prime_dvd_cyclotomic_classGroup_card hp5,
      (S.residual_cofixed_exists_iff_hard_case hp5 ha4).mp hL⟩
  · rintro ⟨_, hcase⟩
    exact (S.residual_cofixed_exists_iff_hard_case hp5 ha4).mpr hcase

/-- 元の非零整数解からの原始化・符号付き向き付けの証拠を保持した縮約。
共通因子を消した別の解へ黙って置き換えず、既存 `OrientationTrace` を残す。 -/
theorem ofCounterexample_hard_case_of_cofixed (hp5 : 5 ≤ p)
    (a b c : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (he : a ^ p + b ^ p = c ^ p) :
    let S := Source.ofCounterexample p Fact.out hp5 a b c ha hb hc he
    (∃ L : Submodule (ZMod p) S.ResidualSpace,
      Module.finrank (ZMod p) L = 1 ∧ S.IsGaloisStable L ∧
        IsCofixedOn S.residualRepresentation L) →
      (∃ R : PrimitiveReduction p a b c, OrientationTrace R.A R.B R.C S.a S.b S.c) ∧
      17 ≤ p ∧ S.a % 8 = 7 ∧ (primorial (p - 1) : ℤ) ∣ S.a * S.b * S.c := by
  dsimp only
  intro hL
  obtain ⟨ha4, _, htrace⟩ := Source.ofCounterexample_spec p Fact.out hp5 a b c ha hb hc he
  obtain ⟨L, hl, hs, hcof⟩ := hL
  exact ⟨htrace, (Source.ofCounterexample p Fact.out hp5 a b c ha hb hc he).residual_cofixed_line_forces_hard_case hp5 ha4 L hl hs hcof⟩

end DkMath.FLT.Frey.Source
