/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.ValuationPrimeExistence
import DkMath.Lib.NumberTheory.ValuationPrimeSupport
import DkMath.Lib.NumberTheory.ValuationFrobenius
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.RatFunc.Basic

#print "file: DkMathTest.Lib.NumberTheory.ValuationPrimeExistence"

/-!
NOTE-032-004の住所の検証。超越拡大ℚ(X)にも適用でき、ℚの代数閉包では
実際のFrobeniusの存在へ接続する。一方、1は住所にならず、2と3は同じ住所にならない。
正標数では任意の素数の住所は存在しないため、標数0の条件を落とせない。
-/
namespace ValuationPrimeExistenceTest
open DkMath.Lib.NumberTheory ValuationInertia ValuationPrimeExistence ValuationPrimeSupport

/-- 代数的拡大に限定されないことをℚ(X)と剰余標数37で確認する。 -/
theorem transcendental_address :
    ∃ A : ValuationSubring (RatFunc ℚ), LiesOverPrime A 37 ∧
      CharP (IsLocalRing.ResidueField A) 37 := by
  obtain ⟨A, hA⟩ := exists_liesOverPrime (L := RatFunc ℚ) (by decide : Nat.Prime 37)
  exact ⟨A, hA, charP_residueField A (by decide) hA⟩

/-- Sourceの存在を仮定せず、2上の住所と実際のFrobeniusを同時に供給できる。 -/
theorem rational_closure_frobenius :
    ∃ A : ValuationSubring (AlgebraicClosure ℚ), LiesOverPrime A 2 ∧
      ∃ σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ),
        ValuationFrobenius.IsFrobeniusAt A σ 2 := by
  obtain ⟨A, hA⟩ := exists_liesOverPrime (L := AlgebraicClosure ℚ) Nat.prime_two
  exact ⟨A, hA, ValuationFrobenius.exists_isFrobeniusAt_of_liesOverPrime Nat.prime_two A hA⟩

/-- 1は全ての付値環で単元。素数の入力を任意の自然数に弱められない。 -/
theorem one_address_boundary {L : Type*} [Field L] (A : ValuationSubring L) :
    ¬ LiesOverPrime A 1 := by
  intro h
  have hlt := (ValuationSubring.mem_nonunits_iff A).mp h
  norm_num at hlt

/-- 住所の選択は素数に依存する。2と3の両方を非単元とする付値環は存在しない。 -/
theorem two_three_address_boundary {L : Type*} [Field L] :
    ¬ ∃ A : ValuationSubring L, LiesOverPrime A 2 ∧ LiesOverPrime A 3 := by
  rintro ⟨A, h2, h3⟩
  have h2lt := (ValuationSubring.mem_nonunits_iff A).mp h2
  have h3lt := (ValuationSubring.mem_nonunits_iff A).mp h3
  have h3unit : A.valuation (3 : L) = 1 := by
    simpa using valuation_intCast_eq_one_of_not_dvd A Nat.prime_two h2lt (z := 3) (by norm_num)
  exact h3lt.ne h3unit

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- 標数2では素数3が1になるため、3上の住所はない。標数0の条件は実質的である。 -/
theorem positive_characteristic_boundary :
    ¬ ∃ A : ValuationSubring (ZMod 2), LiesOverPrime A 3 := by
  rintro ⟨A, hA⟩
  have hlt := (ValuationSubring.mem_nonunits_iff A).mp hA
  rw [show ((3 : ℕ) : ZMod 2) = 1 from by decide, map_one] at hlt
  exact (lt_irrefl _ hlt)

end ValuationPrimeExistenceTest
