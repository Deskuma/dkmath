/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

-- import Mathlib
import DkMath.Algebra.DiffPow
import DkMath.NumberTheory.GcdNatAbsDivD

namespace DkMath.NumberTheory.GcdDiffPow

open scoped BigOperators
open Finset
open DkMath.Algebra.DiffPow

/-!
素因子補題：もし素数 p が `a - b` と `diffPowSum (a,b,d)` 両方を割るなら、かつ `gcd a b = 1` のとき p は d を割る。
これは `gcd (a-b, S_d(a,b)) | d` の核心部分となる補題である。
-/

/-- 主定理：|a-b| と |S| の整数 gcd が d を割る。 -/
theorem gcd_divides_d {a b : ℤ} {d : ℕ} (hd : 1 ≤ d) (hab : Int.gcd a b = 1) :
    Int.gcd (a - b) (diffPowSum a b d) ∣ d := by
  -- Case split: a = b or a ≠ b
  by_cases hab_ne :  a = b
  · -- Case a = b: then gcd a b = |a| = 1, so a = ±1
    subst hab_ne
    -- a = b implies a - b = 0, so gcd 0 (diffPowSum a a d)
    -- gcd a a = |a| = 1, so a = ±1, and diffPowSum a a d = d * a^(d-1) = ±d
    -- Therefore gcd 0 (±d) = d, and d ∣ d
    have hab0 : a - a = 0 := by ring
    rw [hab0]
    have hgcd : Int.gcd 0 (diffPowSum a a d) = Int.natAbs (diffPowSum a a d) :=
      Int.gcd_zero_left _
    rw [hgcd]
    -- Show |a| = 1 from gcd a a = 1
    have ha : Int.natAbs a = 1 := by
      have := Int.gcd_eq_natAbs (a := a) (b := a)
      rw [hab] at this
      simp [Nat.gcd_self] at this
      exact this.symm
    -- diffPowSum a a d = ∑_{i < d} a^(d-1) = d * a^(d-1)
    have hs : diffPowSum a a d = d * a ^ (d - 1) := by
      unfold diffPowSum
      have : ∀ i ∈ Finset.range d, a ^ (d - 1 - i) * a ^ i = a ^ (d - 1) := by
        intro i hi
        rw [← pow_add]
        congr 1
        have : i < d := Finset.mem_range.mp hi
        omega
      calc ∑ i ∈ Finset.range d, a ^ (d - 1 - i) * a ^ i
        = ∑ i ∈ Finset.range d, a ^ (d - 1) := Finset.sum_congr rfl (fun i hi => this i hi)
        _ = Finset.card (Finset.range d) • a ^ (d - 1) := Finset.sum_const _
        _ = d • a ^ (d - 1) := by rw [Finset.card_range]
        _ = d * a ^ (d - 1) := by rw [nsmul_eq_mul]
    rw [hs]
    -- |d * a^(d-1)| = d since |a^(d-1)| = 1
    have : Int.natAbs (d * a ^ (d - 1)) = d := by
      rw [Int.natAbs_mul, Int.natAbs_pow, ha, Int.natAbs_natCast]
      ring
    rw [this]
  · -- Case a ≠ b: use the natural-level gcd lemma
    -- Use natural-level gcd lemma directly to finish
    have h_natAbs : (a - b).natAbs.gcd (diffPowSum a b d).natAbs ∣ d :=
      gcd_natAbs_divides_d hab hab_ne
    -- use the basic lemma `gcd_eq_natAbs` to relate integer gcd to nat gcd
    have h := Int.gcd_eq_natAbs (a := a - b) (b := diffPowSum a b d)
    have eqN : Int.gcd (a - b) (diffPowSum a b d)
      = ((a - b).natAbs.gcd (diffPowSum a b d).natAbs : ℤ) := by simpa using h.symm
    obtain ⟨k, hk⟩ := h_natAbs
    use k
    have eq_nat : (Int.gcd (a - b) (diffPowSum a b d) : ℕ)
      = (a - b).natAbs.gcd (diffPowSum a b d).natAbs := by
      exact Int.natAbs_gcd (a - b) (diffPowSum a b d)
    have h_cast : (Int.gcd (a - b) (diffPowSum a b d) : ℤ) * ↑k = ↑d := by
      have eq := congrArg (fun (x : ℕ) => (x : ℤ)) hk
      simp only [Nat.cast_mul] at eq
      exact eq.symm
    have h_eq : d = (a - b).gcd (diffPowSum a b d) * k := by
      have : (d : ℤ) = ((a - b).gcd (diffPowSum a b d) : ℤ) * ↑k := h_cast.symm
      have : d = (a - b).gcd (diffPowSum a b d) * k := by omega
      exact this
    exact h_eq


end DkMath.NumberTheory.GcdDiffPow
