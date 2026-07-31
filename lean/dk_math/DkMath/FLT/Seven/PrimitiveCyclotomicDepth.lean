/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.AxisDepth

#print "file: DkMath.FLT.Seven.PrimitiveCyclotomicDepth"

namespace DkMath.FLT.Seven

open DkMath.CosmicFormulaBinom
open DkMath.NumberTheory.TraceOneQuadratic

local notation "tqNorm" => DkMath.NumberTheory.TraceOneQuadratic.norm

/-- Direct endpoint-gap expansion of the homogeneous seventh cyclotomic
kernel. -/
theorem cyclotomicSeven_substitution_expansion (d y : ℤ) :
    cyclotomicSeven (y + d) y =
      d ^ 6 + 7 * d ^ 5 * y + 21 * d ^ 4 * y ^ 2
        + 35 * d ^ 3 * y ^ 3 + 35 * d ^ 2 * y ^ 4
        + 21 * d * y ^ 5 + 7 * y ^ 6 := by
  simp [cyclotomicSeven]
  ring

/-- On the gap-divisible channel, the seventh cyclotomic kernel is congruent
to `7*y^6` modulo `49`. -/
theorem fortyNine_dvd_cyclotomicSeven_sub_seven_mul_pow
    {z y : ℤ} (hgap : (7 : ℤ) ∣ z - y) :
    (49 : ℤ) ∣ cyclotomicSeven z y - 7 * y ^ 6 := by
  rcases hgap with ⟨k, hk⟩
  have hz : z = y + 7 * k := by linarith
  refine ⟨7 ^ 4 * k ^ 6 + 7 ^ 4 * k ^ 5 * y
      + 3 * 7 ^ 3 * k ^ 4 * y ^ 2 + 5 * 7 ^ 2 * k ^ 3 * y ^ 3
      + 35 * k ^ 2 * y ^ 4 + 3 * k * y ^ 5, ?_⟩
  rw [hz, cyclotomicSeven_substitution_expansion]
  ring

/-- Under the primitive endpoint condition, the gap-divisible cyclotomic
kernel cannot contain a second factor of `7`. -/
theorem not_fortyNine_dvd_cyclotomicSeven
    {z y : ℤ} (hgap : (7 : ℤ) ∣ z - y) (hy : ¬ (7 : ℤ) ∣ y) :
    ¬ (49 : ℤ) ∣ cyclotomicSeven z y := by
  intro h49
  have hres := fortyNine_dvd_cyclotomicSeven_sub_seven_mul_pow hgap
  have hy6mul : (49 : ℤ) ∣ 7 * y ^ 6 := by
    have hsub := dvd_sub h49 hres
    convert hsub using 1
    all_goals first | rfl | ring
  rcases hy6mul with ⟨k, hk⟩
  have hy6 : y ^ 6 = 7 * k := by
    apply mul_left_cancel₀ (by norm_num : (7 : ℤ) ≠ 0)
    norm_num at hk ⊢
    nlinarith
  apply hy
  apply (show Prime (7 : ℤ) by norm_num).dvd_of_dvd_pow
  exact ⟨k, hy6⟩

/-- Primitive endpoint data makes the cyclotomic coordinate package nonzero. -/
theorem cyclotomicSevenToTraceOne_ne_zero_of_not_seven_dvd_right
    {z y : ℤ} (hy : ¬ (7 : ℤ) ∣ y) :
    cyclotomicSevenToTraceOne z y ≠ 0 := by
  intro hzero
  have hf := congrArg TraceOneInt.fst hzero
  have hs := congrArg TraceOneInt.snd hzero
  have hcoords : cyclotomicSevenFst z y = 0 ∧ cyclotomicSevenSnd z y = 0 := by
    simpa [cyclotomicSevenToTraceOne] using And.intro hf hs
  have hy0 := (cyclotomicSeven_coordinates_eq_zero_iff z y).mp hcoords |>.2
  subst y
  exact hy (dvd_zero 7)

/-- The primitive gap-divisible cyclotomic core has exactly one axis layer. -/
theorem sevenAxisDepth_cyclotomicSeven_eq_one
    {z y : ℤ} (hgap : (7 : ℤ) ∣ z - y) (hy : ¬ (7 : ℤ) ∣ y) :
    sevenAxisDepth (cyclotomicSevenToTraceOne z y) = 1 := by
  have hcore :=
    cyclotomicSevenToTraceOne_ne_zero_of_not_seven_dvd_right (z := z) hy
  have hone : sevenAxis ∣ cyclotomicSevenToTraceOne z y :=
    (sevenAxis_dvd_cyclotomicSevenToTraceOne_iff z y).mpr hgap
  have hle : 1 ≤ sevenAxisDepth (cyclotomicSevenToTraceOne z y) :=
    (sevenAxis_pow_dvd_iff_le_sevenAxisDepth hcore 1).mp (by simpa using hone)
  have hnotTwo : ¬ 2 ≤ sevenAxisDepth (cyclotomicSevenToTraceOne z y) := by
    intro htwo
    have hpow := (sevenAxis_pow_dvd_iff_le_sevenAxisDepth hcore 2).mpr htwo
    have h49 : (49 : ℤ) ∣ cyclotomicSeven z y := by
      have := (sevenAxis_pow_dvd_cyclotomicSevenToTraceOne_iff 2 z y).mp hpow
      norm_num at this ⊢
      exact this
    exact not_fortyNine_dvd_cyclotomicSeven hgap hy h49
  omega

/-- Off the gap channel, a primitive cyclotomic core has depth zero. -/
theorem sevenAxisDepth_cyclotomicSeven_eq_zero
    {z y : ℤ} (hgap : ¬ (7 : ℤ) ∣ z - y) (hy : ¬ (7 : ℤ) ∣ y) :
    sevenAxisDepth (cyclotomicSevenToTraceOne z y) = 0 := by
  have hcore :=
    cyclotomicSevenToTraceOne_ne_zero_of_not_seven_dvd_right (z := z) hy
  by_contra hne
  have hpos : 1 ≤ sevenAxisDepth (cyclotomicSevenToTraceOne z y) :=
    Nat.one_le_iff_ne_zero.mpr hne
  have haxis : sevenAxis ∣ cyclotomicSevenToTraceOne z y := by
    have := (sevenAxis_pow_dvd_iff_le_sevenAxisDepth hcore 1).mpr hpos
    simpa using this
  exact hgap ((sevenAxis_dvd_cyclotomicSevenToTraceOne_iff z y).mp haxis)

/-- Stable primitive local classification: the cyclotomic axis depth is one on
the gap channel and zero off it. -/
theorem sevenAxisDepth_cyclotomicSeven_eq_if
    {z y : ℤ} (hy : ¬ (7 : ℤ) ∣ y) :
    sevenAxisDepth (cyclotomicSevenToTraceOne z y) =
      if (7 : ℤ) ∣ z - y then 1 else 0 := by
  by_cases hgap : (7 : ℤ) ∣ z - y
  · simp [hgap, sevenAxisDepth_cyclotomicSeven_eq_one hgap hy]
  · simp [hgap, sevenAxisDepth_cyclotomicSeven_eq_zero hgap hy]

/-- Peeling the unique primitive cyclotomic axis layer produces a terminal
non-`7` residual core. -/
theorem exists_cyclotomicSeven_terminal_core
    {z y : ℤ} (hgap : (7 : ℤ) ∣ z - y) (hy : ¬ (7 : ℤ) ∣ y) :
    ∃ r : TraceOneInt (-2),
      cyclotomicSevenToTraceOne z y = sevenAxis * r ∧
      r ≠ 0 ∧ ¬ sevenAxis ∣ r ∧ ¬ (7 : ℤ) ∣ tqNorm r ∧
      cyclotomicSeven z y = 7 * tqNorm r ∧ 1 ≤ tqNorm r := by
  have hcore :=
    cyclotomicSevenToTraceOne_ne_zero_of_not_seven_dvd_right (z := z) hy
  rcases exists_terminal_sevenAxis_core hcore with
    ⟨r, hfactor, hr0, hrAxis, hrNorm, hnorm, hrOne⟩
  have hdepth := sevenAxisDepth_cyclotomicSeven_eq_one hgap hy
  refine ⟨r, ?_, hr0, hrAxis, hrNorm, ?_, hrOne⟩
  · simpa [hdepth] using hfactor
  · rw [cyclotomicSeven_eq_traceOneNorm_negTwo]
    simpa [hdepth] using hnorm

/-- A coprime natural endpoint pair on the gap channel has right endpoint not
divisible by `7`. -/
theorem not_seven_dvd_right_of_coprime_of_seven_dvd_sub
    {a b : ℕ} (hab : b ≤ a) (hcop : Nat.Coprime a b)
    (hgap : 7 ∣ a - b) : ¬ 7 ∣ b := by
  intro hb
  have ha : 7 ∣ a := by
    rw [← Nat.sub_add_cancel hab]
    exact dvd_add hgap hb
  have hgcd : 7 ∣ Nat.gcd a b := Nat.dvd_gcd ha hb
  rw [hcop.gcd_eq_one] at hgcd
  norm_num at hgcd

/-- Natural primitive endpoint form of exact cyclotomic depth one. -/
theorem sevenAxisDepth_cyclotomicSeven_nat_eq_one
    {a b : ℕ} (hab : b ≤ a) (hcop : Nat.Coprime a b)
    (hgap : 7 ∣ a - b) :
    sevenAxisDepth (cyclotomicSevenToTraceOne (a : ℤ) (b : ℤ)) = 1 := by
  apply sevenAxisDepth_cyclotomicSeven_eq_one
  · have hgapInt : (7 : ℤ) ∣ ((a - b : ℕ) : ℤ) := Int.ofNat_dvd.mpr hgap
    simpa [Int.ofNat_sub hab] using hgapInt
  · intro hb
    apply not_seven_dvd_right_of_coprime_of_seven_dvd_sub hab hcop hgap
    exact Int.ofNat_dvd.mp hb

/-- Exact primitive `GN 7` valuation classification. -/
theorem padicValNat_GN_seven_sub_eq_if
    {a b : ℕ} (hab : b ≤ a) (hcop : Nat.Coprime a b) :
    padicValNat 7 (GN 7 (a - b) b) = if 7 ∣ a - b then 1 else 0 := by
  by_cases hgap : 7 ∣ a - b
  · have hdepth := sevenAxisDepth_cyclotomicSeven_nat_eq_one hab hcop hgap
    have hbridge :
        sevenAxisDepth (cyclotomicSevenToTraceOne (a : ℤ) (b : ℤ)) =
          padicValNat 7 (GN 7 (a - b) b) := by
      unfold sevenAxisDepth
      congr 1
      calc
        Int.natAbs (tqNorm (cyclotomicSevenToTraceOne (a : ℤ) (b : ℤ))) =
            Int.natAbs (((GN 7 (a - b) b : ℕ) : ℤ)) := by
              rw [GN_seven_sub_eq_traceOneNorm_negTwo a b hab]
        _ = GN 7 (a - b) b := rfl
    rw [if_pos hgap]
    exact hbridge.symm.trans hdepth
  · have hnot : ¬ 7 ∣ GN 7 (a - b) b := by
      rw [seven_dvd_GN_seven_sub_iff a b hab]
      exact hgap
    rw [if_neg hgap]
    exact padicValNat.eq_zero_of_not_dvd hnot

/-- Primitive `GN 7` valuation is always at most one. -/
theorem padicValNat_GN_seven_sub_le_one
    {a b : ℕ} (hab : b ≤ a) (hcop : Nat.Coprime a b) :
    padicValNat 7 (GN 7 (a - b) b) ≤ 1 := by
  rw [padicValNat_GN_seven_sub_eq_if hab hcop]
  split <;> omega

/-- Primitive `GN 7` valuation equals one exactly on the gap channel. -/
theorem padicValNat_GN_seven_sub_eq_one_iff
    {a b : ℕ} (hab : b ≤ a) (hcop : Nat.Coprime a b) :
    padicValNat 7 (GN 7 (a - b) b) = 1 ↔ 7 ∣ a - b := by
  rw [padicValNat_GN_seven_sub_eq_if hab hcop]
  by_cases hgap : 7 ∣ a - b <;> simp [hgap]

/-- Primitive gap-divisible `GN 7` has no second factor of `7`. -/
theorem not_fortyNine_dvd_GN_seven_sub
    {a b : ℕ} (hab : b ≤ a) (hcop : Nat.Coprime a b)
    (hgap : 7 ∣ a - b) : ¬ 49 ∣ GN 7 (a - b) b := by
  intro h49
  have hyNat := not_seven_dvd_right_of_coprime_of_seven_dvd_sub hab hcop hgap
  have hgapInt : (7 : ℤ) ∣ (a : ℤ) - (b : ℤ) := by
    have : (7 : ℤ) ∣ ((a - b : ℕ) : ℤ) := Int.ofNat_dvd.mpr hgap
    simpa [Int.ofNat_sub hab] using this
  have hyInt : ¬ (7 : ℤ) ∣ (b : ℤ) := by
    intro hb
    exact hyNat (Int.ofNat_dvd.mp hb)
  apply not_fortyNine_dvd_cyclotomicSeven hgapInt hyInt
  have h49Int : (49 : ℤ) ∣ ((GN 7 (a - b) b : ℕ) : ℤ) :=
    Int.ofNat_dvd.mpr h49
  have heq : ((GN 7 (a - b) b : ℕ) : ℤ) =
      cyclotomicSeven (a : ℤ) (b : ℤ) := by
    rw [GN_seven_sub_eq_traceOneNorm_negTwo a b hab,
      ← cyclotomicSeven_eq_traceOneNorm_negTwo]
  rw [heq] at h49Int
  exact h49Int

end DkMath.FLT.Seven
