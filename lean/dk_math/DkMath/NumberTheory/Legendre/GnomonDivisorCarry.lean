/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.DivisorIncidence
import DkMath.NumberTheory.Legendre.SquareShellPrimePowerGauge

#print "file: DkMath.NumberTheory.Legendre.GnomonDivisorCarry"

/-! Exact divisor incidence and factorial cancellation expose the binary carry
coordinate of the old Pascal frontier. Every prime provider remains conditional. -/

namespace DkMath.NumberTheory.Legendre

open scoped BigOperators

/-- Total floor difference; the zero-divisor value is zero. -/
def gnomonShellMultipleCount (n d : ℕ) : ℕ :=
  (n ^ 2 + 2 * n) / d - n ^ 2 / d

/-- Exact number of shell multiples of a positive divisor. -/
theorem gnomonShellMultipleCount_eq_card (n d : ℕ) (hd : 0 < d) :
    gnomonShellMultipleCount n d =
      ((Finset.Icc (n ^ 2 + 1) (n ^ 2 + 2 * n)).filter (d ∣ ·)).card :=
  (card_shell_filter_dvd (by omega) hd).symm

/-- Full finite incidence transpose, with no discarded lower divisors. -/
theorem gnomonShell_divisor_incidence (n : ℕ) (_hn : 1 ≤ n) :
    (∑ m ∈ Finset.Icc (n ^ 2 + 1) (n ^ 2 + 2 * n),
      ∑ d ∈ m.divisors, ArithmeticFunction.vonMangoldt d) =
    ∑ d ∈ Finset.Icc 1 (n ^ 2 + 2 * n),
      (gnomonShellMultipleCount n d : ℝ) * ArithmeticFunction.vonMangoldt d :=
  sum_shell_divisors_eq_floor (by omega) _

theorem gnomonShell_log_sum_eq_divisor_mass (n : ℕ) (_hn : 1 ≤ n) :
    (∑ m ∈ Finset.Icc (n ^ 2 + 1) (n ^ 2 + 2 * n), Real.log ((m : ℕ) : ℝ)) =
    ∑ d ∈ Finset.Icc 1 (n ^ 2 + 2 * n),
      (gnomonShellMultipleCount n d : ℝ) * ArithmeticFunction.vonMangoldt d :=
  sum_shell_log_eq_floor (by omega)

theorem gnomonShell_log_prod_eq_divisor_mass (n : ℕ) (_hn : 1 ≤ n) :
    Real.log ((∏ m ∈ Finset.Icc (n ^ 2 + 1) (n ^ 2 + 2 * n), m : ℕ) : ℝ) =
    ∑ d ∈ Finset.Icc 1 (n ^ 2 + 2 * n),
      (gnomonShellMultipleCount n d : ℝ) * ArithmeticFunction.vonMangoldt d :=
  log_shell_prod_eq_floor (by omega)

/-- Reindex the existing Pascal factorial product onto the strict shell carrier. -/
theorem gnomonPascalCell_mul_factorial_eq_shell_prod (n : ℕ) :
    GnomonPascalCell n * (2 * n).factorial =
      ∏ m ∈ Finset.Icc (n ^ 2 + 1) (n ^ 2 + 2 * n), m := by
  rw [gnomonPascalCell_mul_factorial]
  apply Finset.prod_bij (fun i _ => n ^ 2 + (i + 1))
  · intro i hi
    have hi' := Finset.mem_range.mp hi
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro i _ j _ he; omega
  · intro m hm
    have hm' := Finset.mem_Icc.mp hm
    refine ⟨m - (n ^ 2 + 1), Finset.mem_range.mpr (by omega), ?_⟩
    omega
  · intro i _; rfl

/-- Taking logs preserves the complete product, including the uniform factorial. -/
theorem gnomonPascalCell_log_add_factorial_eq_shell_log (n : ℕ) (_hn : 1 ≤ n) :
    Real.log (GnomonPascalCell n : ℝ) + Real.log ((2 * n).factorial : ℝ) =
      ∑ m ∈ Finset.Icc (n ^ 2 + 1) (n ^ 2 + 2 * n), Real.log ((m : ℕ) : ℝ) := by
  have hc : (GnomonPascalCell n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_ne_zero (by omega : 2 * n ≤ n ^ 2 + 2 * n))
  have hf : ((2 * n).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2 * n)
  have hp := congrArg (fun k : ℕ => Real.log (k : ℝ))
    (gnomonPascalCell_mul_factorial_eq_shell_prod n)
  rw [Nat.cast_mul, Real.log_mul hc hf, Nat.cast_prod, Real.log_prod] at hp
  · exact hp
  · intro m hm; exact_mod_cast (show m ≠ 0 by have h := Finset.mem_Icc.mp hm; omega)

/-- Multiplicity-weighted lower-divisor part of the shell log product. -/
noncomputable def gnomonPascalLowerDivisorMass (n : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 (n ^ 2),
    (gnomonShellMultipleCount n d : ℝ) * ArithmeticFunction.vonMangoldt d

theorem gnomonPascalLowerDivisorMass_nonneg (n : ℕ) :
    0 ≤ gnomonPascalLowerDivisorMass n :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) ArithmeticFunction.vonMangoldt_nonneg

/-- Every divisor label above the square has itself as its sole shell multiple. -/
theorem gnomonShell_high_divisor_packet {n d : ℕ} (hn : 3 ≤ n)
    (hd : n ^ 2 < d) (ht : d ≤ n ^ 2 + 2 * n) :
    n ^ 2 + 2 * n < 2 * d ∧ gnomonShellMultipleCount n d = 1 := by
  have htop : n ^ 2 + 2 * n < 2 * d := by nlinarith
  refine ⟨htop, ?_⟩
  unfold gnomonShellMultipleCount
  rw [Nat.div_eq_of_lt hd]
  have hdiv : (n ^ 2 + 2 * n) / d = 1 :=
    Nat.div_eq_of_lt_le (by simpa using ht) (by simpa using htop)
  omega

/-- Split the full divisor carrier at the square boundary. -/
theorem gnomonShell_divisor_mass_eq_lower_add_shellVM {n : ℕ} (hn : 3 ≤ n) :
    (∑ d ∈ Finset.Icc 1 (n ^ 2 + 2 * n),
      (gnomonShellMultipleCount n d : ℝ) * ArithmeticFunction.vonMangoldt d) =
    gnomonPascalLowerDivisorMass n + gnomonPascalShellVonMangoldtMass n := by
  have hu : Finset.Icc 1 (n ^ 2 + 2 * n) =
      Finset.Icc 1 (n ^ 2) ∪ Finset.Icc (n ^ 2 + 1) (n ^ 2 + 2 * n) := by
    ext d; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hj : Disjoint (Finset.Icc 1 (n ^ 2))
      (Finset.Icc (n ^ 2 + 1) (n ^ 2 + 2 * n)) := by
    apply Finset.disjoint_left.mpr
    intro d hd he
    have h := Finset.mem_Icc.mp hd
    have h' := Finset.mem_Icc.mp he
    omega
  rw [hu, Finset.sum_union hj]
  congr 1
  rw [gnomonPascalShellVonMangoldtMass, squareOffsets_sum_eq_values]
  apply Finset.sum_congr rfl
  intro d hd
  have hd' := Finset.mem_Icc.mp hd
  rw [(gnomonShell_high_divisor_packet hn (by omega) hd'.2).2]
  simp

/-- The report-027 bridge retains every lower divisor and the full factorial. -/
theorem gnomonPascalCell_log_add_factorial_eq_shellVM_add_lowerDivisorMass
    {n : ℕ} (hn : 3 ≤ n) :
    Real.log (GnomonPascalCell n : ℝ) + Real.log ((2 * n).factorial : ℝ) =
      gnomonPascalShellVonMangoldtMass n + gnomonPascalLowerDivisorMass n := by
  rw [gnomonPascalCell_log_add_factorial_eq_shell_log n (by omega),
    gnomonShell_log_sum_eq_divisor_mass n (by omega),
    gnomonShell_divisor_mass_eq_lower_add_shellVM hn, add_comm]

/-- A single remainder-phase crossing, with a harmless zero-divisor convention. -/
def gnomonLowDivisorCarryBit (n d : ℕ) : ℕ :=
  if d = 0 then 0 else if d ≤ n ^ 2 % d + (2 * n) % d then 1 else 0

theorem gnomonLowDivisorCarryBit_binary (n d : ℕ) :
    gnomonLowDivisorCarryBit n d = 0 ∨ gnomonLowDivisorCarryBit n d = 1 := by
  unfold gnomonLowDivisorCarryBit
  split
  · simp
  · split <;> simp

theorem gnomonLowDivisorCarryBit_le_one (n d : ℕ) :
    gnomonLowDivisorCarryBit n d ≤ 1 := by
  rcases gnomonLowDivisorCarryBit_binary n d with h | h <;> omega

theorem gnomonLowDivisorCarryBit_eq_one_iff {n d : ℕ} (hd : 0 < d) :
    gnomonLowDivisorCarryBit n d = 1 ↔ d ≤ n ^ 2 % d + (2 * n) % d := by
  simp [gnomonLowDivisorCarryBit, Nat.ne_of_gt hd]

theorem gnomonLowDivisorCarryBit_eq_zero_iff {n d : ℕ} (hd : 0 < d) :
    gnomonLowDivisorCarryBit n d = 0 ↔ n ^ 2 % d + (2 * n) % d < d := by
  simp [gnomonLowDivisorCarryBit, Nat.ne_of_gt hd]

/-- Thin floor-addition consequence; both divisions are natural divisions. -/
theorem gnomonShellMultipleCount_eq_div_add_carry {n d : ℕ} (hd : 0 < d) :
    gnomonShellMultipleCount n d = (2 * n) / d + gnomonLowDivisorCarryBit n d := by
  unfold gnomonShellMultipleCount gnomonLowDivisorCarryBit
  rw [ite_eq_right (Nat.ne_of_gt hd), Nat.add_div hd]
  rw [Nat.add_assoc, Nat.add_sub_cancel_left]

/-- Distance to the next strictly later grid point; aligned points have gap d. -/
def nextMultipleGap (base d : ℕ) : ℕ := if d = 0 then 0 else d - base % d

theorem gnomonLowDivisorCarryBit_eq_one_iff_gap {n d : ℕ} (hd : 0 < d) :
    gnomonLowDivisorCarryBit n d = 1 ↔ nextMultipleGap (n ^ 2) d ≤ (2 * n) % d := by
  rw [gnomonLowDivisorCarryBit_eq_one_iff hd]
  have hm := Nat.mod_lt (n ^ 2) hd
  simp only [nextMultipleGap, ite_eq_right (Nat.ne_of_gt hd)]
  omega

theorem gnomonLowDivisorCarryBit_large_gap {n d : ℕ} (hd : 2 * n < d) :
    gnomonLowDivisorCarryBit n d = 1 ↔ nextMultipleGap (n ^ 2) d ≤ 2 * n := by
  simpa only [Nat.mod_eq_of_lt hd] using
    gnomonLowDivisorCarryBit_eq_one_iff_gap (n := n) (by omega : 0 < d)

/-- Residual binary carry mass after uniform factorial contribution is removed. -/
noncomputable def gnomonPascalLowDivisorCarryMass (n : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 (n ^ 2),
    (gnomonLowDivisorCarryBit n d : ℝ) * ArithmeticFunction.vonMangoldt d

theorem gnomonPascalLowDivisorCarryMass_nonneg (n : ℕ) :
    0 ≤ gnomonPascalLowDivisorCarryMass n :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) ArithmeticFunction.vonMangoldt_nonneg

/-- Exact uniform/residual decomposition on the lower interval. -/
theorem gnomonPascalLowerDivisorMass_eq_factorial_add_carry {n : ℕ} (hn : 3 ≤ n) :
    gnomonPascalLowerDivisorMass n =
      Real.log ((2 * n).factorial : ℝ) + gnomonPascalLowDivisorCarryMass n := by
  rw [log_factorial_eq_floor_cutoff (by nlinarith : 2 * n ≤ n ^ 2)]
  unfold gnomonPascalLowerDivisorMass gnomonPascalLowDivisorCarryMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  rw [gnomonShellMultipleCount_eq_div_add_carry (Finset.mem_Icc.mp hd).1, Nat.cast_add,
    add_mul]

/-- Central cancellation identity. It creates no unconditional lower provider. -/
theorem gnomonPascalCell_log_eq_shellVM_add_lowCarryMass {n : ℕ} (hn : 3 ≤ n) :
    Real.log (GnomonPascalCell n : ℝ) =
      gnomonPascalShellVonMangoldtMass n + gnomonPascalLowDivisorCarryMass n := by
  have h := gnomonPascalCell_log_add_factorial_eq_shellVM_add_lowerDivisorMass hn
  rw [gnomonPascalLowerDivisorMass_eq_factorial_add_carry hn] at h
  linarith

/-- The binary coordinate is exactly the old ledger minus its higher correction. -/
theorem gnomonPascalOldLogBudget_eq_higher_add_lowCarryMass {n : ℕ} (hn : 3 ≤ n) :
    gnomonPascalOldLogBudget n =
      gnomonPascalShellHigherPrimePowerMass n + gnomonPascalLowDivisorCarryMass n := by
  have h := gnomonPascalCell_log_eq_shellVM_add_lowCarryMass hn
  rw [gnomonPascalCell_log_eq_old_add_birth hn,
    gnomonPascalShellVonMangoldtMass_eq_birth_add_higher] at h
  linarith

/-- Exact finite binary event carrier, restricted to nonzero von Mangoldt support. -/
def gnomonPascalLowCarryEvents (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (n ^ 2)).filter (fun d => IsPrimePow d ∧ gnomonLowDivisorCarryBit n d = 1)

theorem mem_gnomonPascalLowCarryEvents {n d : ℕ} :
    d ∈ gnomonPascalLowCarryEvents n ↔
      1 ≤ d ∧ d ≤ n ^ 2 ∧ IsPrimePow d ∧ gnomonLowDivisorCarryBit n d = 1 := by
  simp [gnomonPascalLowCarryEvents, and_assoc]

theorem gnomonPascalLowDivisorCarryMass_eq_events (n : ℕ) :
    gnomonPascalLowDivisorCarryMass n =
      ∑ d ∈ gnomonPascalLowCarryEvents n, ArithmeticFunction.vonMangoldt d := by
  classical
  unfold gnomonPascalLowDivisorCarryMass gnomonPascalLowCarryEvents
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hpp : IsPrimePow d
  · rcases gnomonLowDivisorCarryBit_binary n d with hc | hc <;> simp [hpp, hc]
  · simp [hpp, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp]

/-- Pointwise agreement with the exact predicate of factorization_choose. -/
theorem gnomonLowDivisorCarryBit_prime_pow_iff {n p i : ℕ} (hp : p.Prime)
    (_hi : 0 < i) (_hold : p ^ i ≤ n ^ 2) :
    gnomonLowDivisorCarryBit n (p ^ i) = 1 ↔
      p ^ i ≤ (2 * n) % p ^ i + n ^ 2 % p ^ i := by
  rw [gnomonLowDivisorCarryBit_eq_one_iff (pow_pos hp.pos i), Nat.add_comm]

/-- Small labels retain the full modular width phase. -/
def gnomonPascalSmallCarryEvents (n : ℕ) : Finset ℕ :=
  (gnomonPascalLowCarryEvents n).filter (· ≤ 2 * n)

/-- Large labels have at most one shell multiple. -/
def gnomonPascalLargeCarryEvents (n : ℕ) : Finset ℕ :=
  (gnomonPascalLowCarryEvents n).filter (2 * n < ·)

/-- Band masses are consumed by the exact decomposition and conditional bounds. -/
noncomputable def gnomonPascalSmallCarryMass (n : ℕ) : ℝ :=
  ∑ d ∈ gnomonPascalSmallCarryEvents n, ArithmeticFunction.vonMangoldt d

noncomputable def gnomonPascalLargeCarryMass (n : ℕ) : ℝ :=
  ∑ d ∈ gnomonPascalLargeCarryEvents n, ArithmeticFunction.vonMangoldt d

theorem gnomonPascalLowCarryMass_eq_small_add_large (n : ℕ) :
    gnomonPascalLowDivisorCarryMass n =
      gnomonPascalSmallCarryMass n + gnomonPascalLargeCarryMass n := by
  rw [gnomonPascalLowDivisorCarryMass_eq_events]
  exact by
    simpa only [gnomonPascalSmallCarryMass, gnomonPascalLargeCarryMass,
      gnomonPascalSmallCarryEvents, gnomonPascalLargeCarryEvents, not_le] using
      (Finset.sum_filter_add_sum_filter_not (gnomonPascalLowCarryEvents n)
        (fun d => d ≤ 2 * n) ArithmeticFunction.vonMangoldt).symm

/-- The canonical next multiple after the square boundary. -/
def gnomonNextShellMultiple (n d : ℕ) : ℕ := d * (n ^ 2 / d + 1)

/-- A large carry's next grid point belongs to the strict shell and is divisible by d. -/
theorem gnomonNextShellMultiple_packet {n d : ℕ} (hd : 2 * n < d)
    (hc : gnomonLowDivisorCarryBit n d = 1) :
    SquareCell n (gnomonNextShellMultiple n d) ∧ d ∣ gnomonNextShellMultiple n d := by
  have hd0 : 0 < d := by omega
  have hg := (gnomonLowDivisorCarryBit_large_gap hd).mp hc
  have hm := Nat.mod_lt (n ^ 2) hd0
  have he := Nat.div_add_mod (n ^ 2) d
  simp only [nextMultipleGap, ite_eq_right (Nat.ne_of_gt hd0)] at hg
  have hgap : d ≤ n ^ 2 % d + 2 * n := by omega
  constructor
  · unfold SquareCell gnomonNextShellMultiple
    constructor <;> nlinarith
  · exact ⟨n ^ 2 / d + 1, rfl⟩

/-- Large-grid spacing makes this shell multiple unique, without label injectivity. -/
theorem gnomonNextShellMultiple_unique {n d m : ℕ} (hd : 2 * n < d)
    (hc : gnomonLowDivisorCarryBit n d = 1) (hm : SquareCell n m) (hdm : d ∣ m) :
    m = gnomonNextShellMultiple n d := by
  have hs := (gnomonNextShellMultiple_packet hd hc).1
  obtain ⟨k, rfl⟩ := hdm
  have he := Nat.div_add_mod (n ^ 2) d
  have hmod := Nat.mod_lt (n ^ 2) (by omega : 0 < d)
  unfold SquareCell at hm hs
  unfold gnomonNextShellMultiple at hs
  unfold gnomonNextShellMultiple
  have hk : k = n ^ 2 / d + 1 := by
    by_contra hk
    have hcases : k ≤ n ^ 2 / d ∨ n ^ 2 / d + 2 ≤ k := by omega
    rcases hcases with h | h
    · have hmul := Nat.mul_le_mul_left d h
      nlinarith [hm.1]
    · have hmul := Nat.mul_le_mul_left d h
      nlinarith [hs.1, hm.2]
  rw [hk]

/-- Label collisions are exactly shared shell multiples; no injection is assumed. -/
theorem gnomonNextShellMultiple_collision_iff {n d e : ℕ}
    (hd : 2 * n < d) (he : 2 * n < e)
    (hc : gnomonLowDivisorCarryBit n d = 1) (hc' : gnomonLowDivisorCarryBit n e = 1) :
    gnomonNextShellMultiple n d = gnomonNextShellMultiple n e ↔
      ∃ m, SquareCell n m ∧ d ∣ m ∧ e ∣ m := by
  constructor
  · intro h
    have hdp := gnomonNextShellMultiple_packet hd hc
    have hep := gnomonNextShellMultiple_packet he hc'
    exact ⟨_, hdp.1, hdp.2, h.symm ▸ hep.2⟩
  · rintro ⟨m, hm, hdm, hem⟩
    exact (gnomonNextShellMultiple_unique hd hc hm hdm).symm.trans
      (gnomonNextShellMultiple_unique he hc' hm hem)

/-- A large label's canonical shell cofactor is strictly below the anchor. -/
theorem gnomonNextShellMultiple_cofactor_lt {n d : ℕ} (hn : 3 ≤ n) (hd : 2 * n < d) :
    n ^ 2 / d + 1 < n := by
  have he : n - 1 + 1 = n := by omega
  have hmul : n ^ 2 < (n - 1) * d := by nlinarith
  have hdiv := (Nat.div_lt_iff_lt_mul (by omega : 0 < d)).mpr hmul
  omega

/-- Distinct prime bases cannot supply two large power divisors of one shell integer.
Same-base exponent chains can still collide, so this is not label injectivity. -/
theorem gnomonLarge_prime_power_divisors_same_base {n m p q a b : ℕ}
    (hn : 3 ≤ n) (hm : SquareCell n m) (hp : p.Prime) (hq : q.Prime)
    (hd : 2 * n < p ^ a) (he : 2 * n < q ^ b)
    (hdm : p ^ a ∣ m) (hem : q ^ b ∣ m) : p = q := by
  by_contra hne
  have hcop := Nat.coprime_pow_primes a b hp hq hne
  have hprod := hcop.mul_dvd_of_dvd_of_dvd hdm hem
  have hm0 : 0 < m := by have h := hm.1; omega
  have hle := Nat.le_of_dvd hm0 hprod
  have hlarge : (2 * n + 1) ^ 2 ≤ p ^ a * q ^ b := by
    calc
      _ = (2 * n + 1) * (2 * n + 1) := by ring
      _ ≤ _ := Nat.mul_le_mul (by omega) (by omega)
  have htop := hm.2
  nlinarith

/-- Every prime-power label contributes its prime-base logarithm once. -/
theorem gnomonCarry_prime_pow_weight {p a : ℕ} (hp : p.Prime) (ha : 0 < a) :
    ArithmeticFunction.vonMangoldt (p ^ a) = Real.log (p : ℝ) := by
  rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega : a ≠ 0),
    ArithmeticFunction.vonMangoldt_apply_prime hp]

/-- A proved carry upper bound and a strict residual margin feed the exact shell mass. -/
theorem gnomonShellVM_margin_of_carry_bound {n : ℕ} (hn : 3 ≤ n) {B margin : ℝ}
    (hcarry : gnomonPascalLowDivisorCarryMass n ≤ B)
    (hstrict : B + margin < Real.log (GnomonPascalCell n : ℝ)) :
    margin < gnomonPascalShellVonMangoldtMass n := by
  rw [gnomonPascalCell_log_eq_shellVM_add_lowCarryMass hn] at hstrict
  linarith

/-- A band-wise provider uses the two exact carrier masses. -/
theorem gnomonShellVM_margin_of_band_bounds {n : ℕ} (hn : 3 ≤ n) {S L margin : ℝ}
    (hs : gnomonPascalSmallCarryMass n ≤ S) (hl : gnomonPascalLargeCarryMass n ≤ L)
    (hstrict : S + L + margin < Real.log (GnomonPascalCell n : ℝ)) :
    margin < gnomonPascalShellVonMangoldtMass n := by
  apply gnomonShellVM_margin_of_carry_bound hn (B := S + L) _ hstrict
  rw [gnomonPascalLowCarryMass_eq_small_add_large]
  linarith

/-- Exact reformulation of the 027 sufficient shell-mass comparison. -/
theorem gnomonLowCarry_logLog_criterion_iff {n : ℕ} (hn : 3 ≤ n) :
    gnomonPascalLowDivisorCarryMass n + shellHigherPrimePowerLogLogBudget n <
      Real.log (GnomonPascalCell n : ℝ) ↔
    shellHigherPrimePowerLogLogBudget n < gnomonPascalShellVonMangoldtMass n := by
  rw [gnomonPascalCell_log_eq_shellVM_add_lowCarryMass hn]
  constructor <;> intro h <;> linarith

theorem exists_prime_squareCell_of_lowCarry_logLog_lt {n : ℕ} (hn : 3 ≤ n)
    (hstrict : gnomonPascalLowDivisorCarryMass n + shellHigherPrimePowerLogLogBudget n <
      Real.log (GnomonPascalCell n : ℝ)) : ∃ p, p.Prime ∧ SquareCell n p :=
  exists_prime_squareCell_of_logLogBudget_lt hn
    ((gnomonLowCarry_logLog_criterion_iff hn).mp hstrict)

/-- Using the exact higher correction recovers precisely the old strict criterion. -/
theorem gnomonLowCarry_exact_higher_criterion_iff {n : ℕ} (hn : 3 ≤ n) :
    gnomonPascalLowDivisorCarryMass n + gnomonPascalShellHigherPrimePowerMass n <
      Real.log (GnomonPascalCell n : ℝ) ↔
    gnomonPascalOldLogBudget n < Real.log (GnomonPascalCell n : ℝ) := by
  rw [gnomonPascalOldLogBudget_eq_higher_add_lowCarryMass hn, add_comm]

/-- The upper-budget criterion implies the old criterion; a converse is not asserted. -/
theorem gnomonLowCarry_logLog_implies_old_strict {n : ℕ} (hn : 3 ≤ n)
    (hstrict : gnomonPascalLowDivisorCarryMass n + shellHigherPrimePowerLogLogBudget n <
      Real.log (GnomonPascalCell n : ℝ)) :
    gnomonPascalOldLogBudget n < Real.log (GnomonPascalCell n : ℝ) := by
  rw [gnomonPascalOldLogBudget_eq_higher_add_lowCarryMass hn]
  have h := gnomonPascalShellHigherPrimePowerMass_le_logLogBudget hn
  linarith

/-- Elementary multiplicative growth retains the factorial contribution. -/
theorem gnomonPascalCell_mul_factorial_lower (n : ℕ) :
    (n ^ 2 + 1) ^ (2 * n) ≤ GnomonPascalCell n * (2 * n).factorial := by
  rw [gnomonPascalCell_mul_factorial]
  calc
    _ = ∏ _i ∈ Finset.range (2 * n), (n ^ 2 + 1) := by simp
    _ ≤ _ := Finset.prod_le_prod fun i _ => by omega

/-- Product growth alone bounds the total log, not the residual shell mass. -/
theorem gnomonPascalCell_log_add_factorial_lower (n : ℕ) :
    (2 * n : ℝ) * Real.log ((n ^ 2 + 1 : ℕ) : ℝ) ≤
      Real.log (GnomonPascalCell n : ℝ) + Real.log ((2 * n).factorial : ℝ) := by
  have hc : (GnomonPascalCell n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_ne_zero (by omega : 2 * n ≤ n ^ 2 + 2 * n))
  have hf : ((2 * n).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2 * n)
  have hpow : (0 : ℝ) < ((n ^ 2 + 1 : ℕ) : ℝ) ^ (2 * n) :=
    pow_pos (by positivity) _
  have hle : ((n ^ 2 + 1 : ℕ) : ℝ) ^ (2 * n) ≤
      (GnomonPascalCell n : ℝ) * ((2 * n).factorial : ℝ) := by
    exact_mod_cast gnomonPascalCell_mul_factorial_lower n
  simpa only [Real.log_pow, Real.log_mul hc hf, Nat.cast_mul, Nat.cast_ofNat] using Real.log_le_log hpow hle

end DkMath.NumberTheory.Legendre
