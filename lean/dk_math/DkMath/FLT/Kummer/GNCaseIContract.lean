/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.SparsePhaseObstruction
import DkMath.FLT.Kummer.GNFirstCase
import DkMath.FLT.Kummer.CaseIConjugationContract
import DkMath.FLT.Kummer.IntegerCounterexampleOrientation

#print "file: DkMath.FLT.Kummer.GNCaseIContract"

/-!
# GN 因子抽出と交換可能な位相供給

このファイルは `UnitConjugation` と古典的な Packet 構成を import しない。
GN 側が取り出した同じ線形因子の `ε*γ^p` 表示を、引数で渡した供給証明へ送る。
GN の整数ノルム `GN_p=t^p` だけを矛盾の根拠にする経路はない。

終端は Packet と中立な係数剛性を使う。古典的共役による供給と、将来の
GN による供給は、同じ契約の別の証明として差し替えられる。
後者の新たな証明をこのファイルで得たと主張するものではない。
-/

namespace DkMath.FLT.Kummer.CaseIConjugation

open scoped NumberField

/-- Packet の出所を問わない4項障害。使用する終端は中立な係数剛性だけである。
`a≢b mod p` と p≥5 は位相衝突と空位相のために必要なので保持する。 -/
theorem Packet.false_of_not_modEq
    {p : ℕ} {K : Type*} [Field K] [CharZero K] [IsCyclotomicExtension {p} ℚ K]
    (hp : p.Prime) (hp5 : 5 ≤ p) {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p)
    {a b : ℤ} (packet : Packet (p := p) ζ a b)
    (ha : ¬ (p : ℤ) ∣ a) (hb : ¬ (p : ℤ) ∣ b) (hab : ¬ Int.ModEq p a b) : False :=
  DkMath.Lib.NumberTheory.four_phase_obstruction hp hp5 hζ ha hb hab
    packet.k₁ packet.k₂ packet.adjacent packet.divisible


end DkMath.FLT.Kummer.CaseIConjugation

namespace DkMath.FLT.Kummer

open CaseIConjugation
open scoped NumberField

variable {p : ℕ} [hp : Fact p.Prime] {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] {ζ : K}

/-- GN の i=1 因子を、指定された供給証明へ渡す。
ノルムを取らず、抽出された単元 u と根 γ の同一性を保持する。 -/
theorem first_case_conjugation_packet_using (hζ : IsPrimitiveRoot ζ p) (hp5 : 5 ≤ p)
    (provider : FactorPacketProvider (p := p) hζ.toInteger)
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p) (hcop : IsCoprime a b)
    (hfirst : ¬ (p : ℤ) ∣ a * b * c)
    (hreg : Nat.Coprime p (Fintype.card (ClassGroup (𝓞 K)))) :
    Nonempty (Packet (p := p) hζ.toInteger a b) := by
  have hodd := hp.out.odd_of_ne_two (by omega)
  obtain ⟨_, ε, γ, _, _, hε, _, hfactor⟩ :=
    GN_kummer_structure_of_first_case hζ hodd heq hcop hfirst hreg hp.out.one_lt
  obtain ⟨u, rfl⟩ := hε
  exact provider (by simpa only [pow_one] using hfactor.symm)

/-- 因子単位の供給証明と GN 構造定理を合成し、方程式単位の契約を満たす。
類数条件はここで消費され、終端の固定契約には持ち込まない。 -/
theorem solution_packet_provider_using (hζ : IsPrimitiveRoot ζ p) (hp5 : 5 ≤ p)
    (hreg : Nat.Coprime p (Fintype.card (ClassGroup (𝓞 K))))
    (provider : FactorPacketProvider (p := p) hζ.toInteger) :
    SolutionPacketProvider (p := p) hζ.toInteger := by
  intro a b c heq hcop hfirst
  exact first_case_conjugation_packet_using hζ hp5 provider heq hcop hfirst hreg

/-- Packet の供給証明だけを受け取る、非合同 Case I の終端。
CM 共役や類数計算の具体的な証明本体には依存しない。 -/
theorem not_int_solution_caseI_of_not_modEq_using (hζ : IsPrimitiveRoot ζ p) (hp5 : 5 ≤ p)
    (provider : SolutionPacketProvider (p := p) hζ.toInteger)
    {a b c : ℤ} (hcop : IsCoprime a b) (hab : ¬ Int.ModEq p a b)
    (hfirst : ¬ (p : ℤ) ∣ a * b * c) : a ^ p + b ^ p ≠ c ^ p := by
  intro heq
  obtain ⟨packet⟩ := provider heq hcop hfirst
  have ha : ¬ (p : ℤ) ∣ a := fun h => hfirst (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h b) c)
  have hb : ¬ (p : ℤ) ∣ b := fun h => hfirst (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h a) c)
  exact packet.false_of_not_modEq hp.out hp5 hζ.toInteger_isPrimitiveRoot ha hb hab

/-- 一般 Case I の供給非依存な終端。合同例外の向き付けと係数障害は固定し、
方程式から Packet を作る証明だけを差し替える。 -/
theorem not_int_solution_caseI_using (hζ : IsPrimitiveRoot ζ p) (hp5 : 5 ≤ p)
    (provider : SolutionPacketProvider (p := p) hζ.toInteger)
    {a b c : ℤ} (hcop : IsCoprime a b) (hfirst : ¬ (p : ℤ) ∣ a * b * c) :
    a ^ p + b ^ p ≠ c ^ p := by
  intro heq
  obtain ⟨x, y, z, h, hxy, hne, hfirst'⟩ := orient_first_case hp5 heq hcop hfirst
  exact not_int_solution_caseI_of_not_modEq_using hζ hp5 provider hxy hne hfirst' h

end DkMath.FLT.Kummer
