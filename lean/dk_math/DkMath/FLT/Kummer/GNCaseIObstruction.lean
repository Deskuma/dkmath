/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.GNFirstCase
import DkMath.FLT.Kummer.CaseIConjugationPacket
import DkMath.FLT.Kummer.IntegerCounterexampleOrientation
import DkMath.Lib.NumberTheory.SparsePhaseObstruction

#print "file: DkMath.FLT.Kummer.GNCaseIObstruction"

/-!
# GN の因子抽出から Case I の終端へ

既存の GN 構造定理から、同じ線形因子 `a+ζb` の単元倍 p 乗表示を得る。
その表示を共役 packet へ、packet を疎な係数剛性へ渡す。
GN の整数ノルムが p 乗になるだけで矛盾とする推論は用いない。

`a≡b` の例外は整数の向き付けで除去する。正則性は類数との互いに素性
として明示される。Case I の終端は State の深度0を排除するものではない。
-/

namespace DkMath.FLT.Kummer

open DkMath.Lib.NumberTheory
open scoped NumberField

variable {p : ℕ} [hp : Fact p.Prime] {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] {ζ : K}

/-- GN で抽出した i=1 の同じ因子を共役 packet に変換する。
イデアル生成元と単元は抽出定理から実際に得る。 -/
theorem first_case_conjugation_packet (hζ : IsPrimitiveRoot ζ p) (hp5 : 5 ≤ p)
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p) (hcop : IsCoprime a b)
    (hfirst : ¬ (p : ℤ) ∣ a * b * c)
    (hreg : Nat.Coprime p (Fintype.card (ClassGroup (𝓞 K)))) :
    Nonempty (CaseIConjugation.Packet (p := p) hζ.toInteger a b) := by
  have hodd := hp.out.odd_of_ne_two (by omega)
  obtain ⟨_, ε, γ, _, _, hε, _, hfactor⟩ :=
    GN_kummer_structure_of_first_case hζ hodd heq hcop hfirst hreg hp.out.one_lt
  obtain ⟨u, rfl⟩ := hε
  exact CaseIConjugation.packet_of_factor hp5 hζ.toInteger_isPrimitiveRoot
    (by simpa only [pow_one] using hfactor.symm)

/-- 非合同に向き付けた Case I の反例は、4項の位相剛性に反する。 -/
theorem not_int_solution_caseI_of_not_modEq (hζ : IsPrimitiveRoot ζ p) (hp5 : 5 ≤ p)
    (hreg : Nat.Coprime p (Fintype.card (ClassGroup (𝓞 K))))
    {a b c : ℤ} (hcop : IsCoprime a b) (hab : ¬ Int.ModEq p a b)
    (hfirst : ¬ (p : ℤ) ∣ a * b * c) : a ^ p + b ^ p ≠ c ^ p := by
  intro heq
  obtain ⟨packet⟩ := first_case_conjugation_packet hζ hp5 heq hcop hfirst hreg
  have ha : ¬ (p : ℤ) ∣ a := fun h => hfirst (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h b) c)
  have hb : ¬ (p : ℤ) ∣ b := fun h => hfirst (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h a) c)
  exact four_phase_obstruction hp.out hp5 hζ.toInteger_isPrimitiveRoot ha hb hab
    packet.k₁ packet.k₂ packet.adjacent packet.divisible

/-- p≥5 の一般 Case I を排除する。必要なのは整数の原始性と類数条件。
単元の p 乗 criterion は Case II 用であり、この終端には不要である。 -/
theorem not_int_solution_caseI
    (hζ : IsPrimitiveRoot ζ p)
    (hp5 : 5 ≤ p)
    (hreg : Nat.Coprime p (Fintype.card (ClassGroup (𝓞 K))))
    {a b c : ℤ} (hcop : IsCoprime a b) (hfirst : ¬ (p : ℤ) ∣ a * b * c) :
    a ^ p + b ^ p ≠ c ^ p := by
  intro heq
  obtain ⟨x, y, z, h, hxy, hne, hfirst'⟩ := orient_first_case hp5 heq hcop hfirst
  exact not_int_solution_caseI_of_not_modEq hζ hp5 hreg hxy hne hfirst' h

end DkMath.FLT.Kummer
