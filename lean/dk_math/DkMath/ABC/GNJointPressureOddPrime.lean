/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNExceptionalExcessOddPrime

#print "file: DkMath.ABC.GNJointPressureOddPrime"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# Joint GN support-multiplicity pressure at odd-prime exponents

At an odd-prime exponent the exceptional valuation excess vanishes.  This
module combines lifted radical support and the remaining non-exceptional
multiplicity into one affine pressure.  The resulting logarithmic and
pointwise height bridges never split that pressure back into two independent
arithmetic hypotheses.
-/

namespace DkMath.ABC

open DkMath.CosmicFormulaBinom

/--
At an odd-prime exponent, the exact logarithmic GN decomposition contains
only the non-exceptional valuation excess.
-/
theorem Triple.log_GN_eq_log_rad_add_nonExceptionalExcess_of_oddPrime
    (T : Triple) {p : ℕ}
    (hp : Nat.Prime p)
    (hpOdd : Odd p)
    (ha : 0 < T.a) (hb : 0 < T.b) :
    Real.log ((GN p T.a T.b : ℕ) : ℝ) =
      Real.log (rad (GN p T.a T.b) : ℝ) +
        GNNonExceptionalValuationExcess p T.a T.b := by
  have hidentity :=
    T.log_GN_eq_log_rad_add_GNValuationExcess hp.two_le ha hb
  have hsplit :=
    GNValuationExcess_eq_exceptional_add_nonExceptional p T.a T.b
  have hzero :=
    T.GNExceptionalValuationExcess_eq_zero_of_oddPrime hp hpOdd
  rw [hsplit, hzero, zero_add] at hidentity
  exact hidentity

/--
Exact odd-prime accounting by exceptional support, fresh support, and
non-exceptional depth.

The exceptional logarithm is not replaced by `log (rad p)`: the exceptional
support may be empty.
-/
theorem Triple.log_GN_eq_log_exceptional_add_log_nonExceptional_add_excess
    (T : Triple) {p : ℕ}
    (hp : Nat.Prime p)
    (hpOdd : Odd p)
    (ha : 0 < T.a) (hb : 0 < T.b) :
    Real.log ((GN p T.a T.b : ℕ) : ℝ) =
      Real.log (GNExceptionalSupportProduct p T.a T.b : ℝ) +
        Real.log (GNNonExceptionalSupportProduct p T.a T.b : ℝ) +
          GNNonExceptionalValuationExcess p T.a T.b := by
  have hnormal :=
    T.log_GN_eq_log_rad_add_nonExceptionalExcess_of_oddPrime
      hp hpOdd ha hb
  have hrad :=
    rad_GN_eq_exceptional_mul_nonExceptional p T.a T.b
  have hlogRad :
      Real.log (rad (GN p T.a T.b) : ℝ) =
        Real.log (GNExceptionalSupportProduct p T.a T.b : ℝ) +
          Real.log (GNNonExceptionalSupportProduct p T.a T.b : ℝ) := by
    rw [hrad, Nat.cast_mul]
    apply Real.log_mul
    · exact_mod_cast
        (Nat.ne_of_gt (GNExceptionalSupportProduct_pos p T.a T.b))
    · exact_mod_cast
        (Nat.ne_of_gt (GNNonExceptionalSupportProduct_pos p T.a T.b))
  rw [hlogRad] at hnormal
  linarith

/--
Affine budget for the combined lifted-support and non-exceptional
multiplicity pressure.

The extra `1` on the right retains the original ABC radical layer already
present in the lifted radical.
-/
def GNOddPrimeJointPressureBudgetAffine
    (T : Triple) (p : ℕ) (ρ C : ℝ) : Prop :=
  Real.log (rad ((T.gnPowerLift p).a *
      (T.gnPowerLift p).b * (T.gnPowerLift p).c) : ℝ) +
        GNNonExceptionalValuationExcess p T.a T.b ≤
    (1 + ρ) * Real.log (rad (T.a * T.b * T.c) : ℝ) + C

/--
At an odd-prime exponent the lifted radical is exactly the original ABC
radical times the fresh non-exceptional GN support.

Exceptional GN support is not a new lifted prime: divisibility by the prime
exponent forces that prime to divide the original left coordinate.
-/
theorem Triple.rad_gnPowerLift_eq_rad_mul_nonExceptionalSupport_of_prime
    (T : Triple) {p : ℕ}
    (hp : Nat.Prime p)
    (ha : 0 < T.a) (hb : 0 < T.b) :
    rad ((T.gnPowerLift p).a *
        (T.gnPowerLift p).b * (T.gnPowerLift p).c) =
      rad (T.a * T.b * T.c) *
        GNNonExceptionalSupportProduct p T.a T.b := by
  classical
  let original := T.a * T.b * T.c
  let lifted := (T.gnPowerLift p).a *
    (T.gnPowerLift p).b * (T.gnPowerLift p).c
  let S := original.factorization.support ∪
    GNNonExceptionalSupport p T.a T.b
  have hc : 0 < T.c := by
    rw [← T.hsum]
    omega
  have horiginal : original ≠ 0 := by
    exact Nat.ne_of_gt (Nat.mul_pos (Nat.mul_pos ha hb) hc)
  have hGN : GN p T.a T.b ≠ 0 :=
    GN_ne_zero_nat_of_two_le hp.two_le ha hb
  have hlifted : lifted ≠ 0 := by
    dsimp [lifted]
    exact Nat.mul_ne_zero
      (Nat.mul_ne_zero
        (Nat.mul_ne_zero (Nat.ne_of_gt ha) hGN)
        (pow_ne_zero p (Nat.ne_of_gt hb)))
      (pow_ne_zero p (Nat.ne_of_gt hc))
  have hsupport : lifted.factorization.support = S := by
    ext q
    constructor
    · intro hqLift
      rcases mem_support_factorization_iff.mp hqLift with
        ⟨_, hqPrime, hqDvdLift⟩
      have hqDvdLift' :
          q ∣ (T.a * GN p T.a T.b) * T.b ^ p * T.c ^ p := by
        simpa [lifted] using hqDvdLift
      rcases hqPrime.dvd_mul.mp hqDvdLift' with hqDvdAB | hqDvdCPow
      · rcases hqPrime.dvd_mul.mp hqDvdAB with hqDvdAGN | hqDvdBPow
        · rcases hqPrime.dvd_mul.mp hqDvdAGN with hqDvdA | hqDvdGN
          · apply Finset.mem_union.mpr
            apply Or.inl
            exact mem_support_factorization_iff.mpr
              ⟨horiginal, hqPrime,
                dvd_mul_of_dvd_left
                  (dvd_mul_of_dvd_left hqDvdA T.b) T.c⟩
          · by_cases hqP : q ∣ p
            · have hqEq : q = p :=
                (Nat.prime_dvd_prime_iff_eq hqPrime hp).mp hqP
              subst q
              have hpA : p ∣ T.a :=
                prime_dvd_boundary_of_dvd_GN_prime hp hqDvdGN
              apply Finset.mem_union.mpr
              apply Or.inl
              exact mem_support_factorization_iff.mpr
                ⟨horiginal, hp,
                  dvd_mul_of_dvd_left
                    (dvd_mul_of_dvd_left hpA T.b) T.c⟩
            · apply Finset.mem_union.mpr
              apply Or.inr
              exact Finset.mem_filter.mpr
                ⟨mem_support_factorization_iff.mpr
                    ⟨hGN, hqPrime, hqDvdGN⟩,
                  hqP⟩
        · have hqDvdB : q ∣ T.b :=
            hqPrime.dvd_of_dvd_pow hqDvdBPow
          apply Finset.mem_union.mpr
          apply Or.inl
          exact mem_support_factorization_iff.mpr
            ⟨horiginal, hqPrime,
              dvd_mul_of_dvd_left
                (dvd_mul_of_dvd_right hqDvdB T.a) T.c⟩
      · have hqDvdC : q ∣ T.c :=
          hqPrime.dvd_of_dvd_pow hqDvdCPow
        apply Finset.mem_union.mpr
        apply Or.inl
        exact mem_support_factorization_iff.mpr
          ⟨horiginal, hqPrime,
            dvd_mul_of_dvd_right hqDvdC (T.a * T.b)⟩
    · intro hqS
      rcases Finset.mem_union.mp hqS with hqOriginal | hqGN
      · rcases mem_support_factorization_iff.mp hqOriginal with
          ⟨_, hqPrime, hqDvdOriginal⟩
        rcases hqPrime.dvd_mul.mp hqDvdOriginal with hqDvdAB | hqDvdC
        · rcases hqPrime.dvd_mul.mp hqDvdAB with hqDvdA | hqDvdB
          · apply mem_support_factorization_iff.mpr
            refine ⟨hlifted, hqPrime, ?_⟩
            change q ∣ (T.a * GN p T.a T.b) * T.b ^ p * T.c ^ p
            exact dvd_mul_of_dvd_left
              (dvd_mul_of_dvd_left
                (dvd_mul_of_dvd_left hqDvdA (GN p T.a T.b))
                (T.b ^ p))
              (T.c ^ p)
          · apply mem_support_factorization_iff.mpr
            refine ⟨hlifted, hqPrime, ?_⟩
            change q ∣ (T.a * GN p T.a T.b) * T.b ^ p * T.c ^ p
            exact dvd_mul_of_dvd_left
              (dvd_mul_of_dvd_right
                (dvd_pow hqDvdB hp.ne_zero) (T.a * GN p T.a T.b))
              (T.c ^ p)
        · apply mem_support_factorization_iff.mpr
          refine ⟨hlifted, hqPrime, ?_⟩
          change q ∣ (T.a * GN p T.a T.b) * T.b ^ p * T.c ^ p
          exact dvd_mul_of_dvd_right
            (dvd_pow hqDvdC hp.ne_zero)
            ((T.a * GN p T.a T.b) * T.b ^ p)
      · have hqMem := Finset.mem_filter.mp hqGN
        rcases mem_support_factorization_iff.mp hqMem.1 with
          ⟨_, hqPrime, hqDvdGN⟩
        apply mem_support_factorization_iff.mpr
        refine ⟨hlifted, hqPrime, ?_⟩
        change q ∣ (T.a * GN p T.a T.b) * T.b ^ p * T.c ^ p
        exact dvd_mul_of_dvd_left
          (dvd_mul_of_dvd_left
            (dvd_mul_of_dvd_right hqDvdGN T.a)
            (T.b ^ p))
          (T.c ^ p)
  have hdis :
      Disjoint original.factorization.support
        (GNNonExceptionalSupport p T.a T.b) := by
    refine Finset.disjoint_left.mpr ?_
    intro q hqOriginal hqGN
    exact
      (T.nonExceptionalSupport_fresh hp.one_le ha hqGN).2.2.2.2.2
        (mem_support_factorization_iff.mp hqOriginal).2.2
  have hprod :
      S.prod id =
        rad original * GNNonExceptionalSupportProduct p T.a T.b := by
    unfold S GNNonExceptionalSupportProduct rad
    simpa only [id_eq] using Finset.prod_union hdis
  change lifted.factorization.support.prod id =
    rad original * GNNonExceptionalSupportProduct p T.a T.b
  rw [hsupport]
  exact hprod

/-- Logarithmic form of the exact prime-exponent lifted-radical identity. -/
theorem Triple.log_rad_gnPowerLift_eq_log_rad_add_log_nonExceptionalSupport_of_prime
    (T : Triple) {p : ℕ}
    (hp : Nat.Prime p)
    (ha : 0 < T.a) (hb : 0 < T.b) :
    Real.log (rad ((T.gnPowerLift p).a *
        (T.gnPowerLift p).b * (T.gnPowerLift p).c) : ℝ) =
      Real.log (rad (T.a * T.b * T.c) : ℝ) +
        Real.log (GNNonExceptionalSupportProduct p T.a T.b : ℝ) := by
  rw [T.rad_gnPowerLift_eq_rad_mul_nonExceptionalSupport_of_prime
    hp ha hb, Nat.cast_mul]
  apply Real.log_mul
  · have hc : 0 < T.c := by
      rw [← T.hsum]
      omega
    have habc : 0 < T.a * T.b * T.c :=
      Nat.mul_pos (Nat.mul_pos ha hb) hc
    exact_mod_cast (Nat.ne_of_gt (rad_pos habc))
  · exact_mod_cast
      (Nat.ne_of_gt (GNNonExceptionalSupportProduct_pos p T.a T.b))

/-- Affine budget for the exact fresh support-plus-depth channel mass. -/
def GNNonExceptionalChannelMassBudgetAffine
    (T : Triple) (p : ℕ) (ρ C : ℝ) : Prop :=
  Real.log (GNNonExceptionalSupportProduct p T.a T.b : ℝ) +
      GNNonExceptionalValuationExcess p T.a T.b ≤
    ρ * Real.log (rad (T.a * T.b * T.c) : ℝ) + C

/--
The channel-mass budget is exactly a logarithmic upper bound for `GN` after
retaining the possibly-empty exceptional support term.
-/
theorem Triple.nonExceptionalChannelMassBudget_iff_log_GN_le
    (T : Triple) {p : ℕ} {ρ C : ℝ}
    (hp : Nat.Prime p)
    (hpOdd : Odd p)
    (ha : 0 < T.a) (hb : 0 < T.b) :
    GNNonExceptionalChannelMassBudgetAffine T p ρ C ↔
      Real.log ((GN p T.a T.b : ℕ) : ℝ) ≤
        ρ * Real.log (rad (T.a * T.b * T.c) : ℝ) + C +
          Real.log (GNExceptionalSupportProduct p T.a T.b : ℝ) := by
  let S : ℝ := Real.log (GNNonExceptionalSupportProduct p T.a T.b : ℝ)
  let E : ℝ := GNNonExceptionalValuationExcess p T.a T.b
  let R : ℝ := Real.log (rad (T.a * T.b * T.c) : ℝ)
  let G : ℝ := Real.log ((GN p T.a T.b : ℕ) : ℝ)
  let X : ℝ := Real.log (GNExceptionalSupportProduct p T.a T.b : ℝ)
  have haccount :=
    T.log_GN_eq_log_exceptional_add_log_nonExceptional_add_excess
      hp hpOdd ha hb
  change G = X + S + E at haccount
  change (S + E ≤ ρ * R + C) ↔ (G ≤ ρ * R + C + X)
  constructor <;> intro h <;> nlinarith

/--
For a prime exponent, the lifted formulation of joint pressure is equivalent
to the exact fresh support-plus-depth mass formulation.
-/
theorem Triple.oddPrimeJointPressure_iff_nonExceptionalChannelMass
    (T : Triple) {p : ℕ} {ρ C : ℝ}
    (hp : Nat.Prime p)
    (ha : 0 < T.a) (hb : 0 < T.b) :
    GNOddPrimeJointPressureBudgetAffine T p ρ C ↔
      GNNonExceptionalChannelMassBudgetAffine T p ρ C := by
  let L : ℝ := Real.log (rad ((T.gnPowerLift p).a *
    (T.gnPowerLift p).b * (T.gnPowerLift p).c) : ℝ)
  let R : ℝ := Real.log (rad (T.a * T.b * T.c) : ℝ)
  let S : ℝ := Real.log (GNNonExceptionalSupportProduct p T.a T.b : ℝ)
  let E : ℝ := GNNonExceptionalValuationExcess p T.a T.b
  have hexact :=
    T.log_rad_gnPowerLift_eq_log_rad_add_log_nonExceptionalSupport_of_prime
      hp ha hb
  change L = R + S at hexact
  change (L + E ≤ (1 + ρ) * R + C) ↔
    (S + E ≤ ρ * R + C)
  constructor <;> intro h <;> nlinarith

/--
Separate lifted-radical and non-exceptional-excess budgets imply the joint
budget.  This is a one-way compatibility theorem; later callers may establish
the joint budget directly.
-/
theorem GNOddPrimeJointPressureBudgetAffine.of_liftGrowth_and_nonExceptional
    {T : Triple} {p : ℕ} {σ Cs τ D : ℝ}
    (hlift : GNLiftRadicalGrowthBudgetAffine T p σ Cs)
    (hexcess : GNNonExceptionalExcessBudgetAffine T p τ D) :
    GNOddPrimeJointPressureBudgetAffine T p (σ + τ) (Cs + D) := by
  dsimp [GNLiftRadicalGrowthBudgetAffine] at hlift
  dsimp [GNNonExceptionalExcessBudgetAffine] at hexcess
  dsimp [GNOddPrimeJointPressureBudgetAffine]
  nlinarith

/--
The joint pressure directly bounds the logarithmic ABC height at an
odd-prime exponent.
-/
theorem Triple.log_c_mul_pred_le_of_oddPrime_jointPressure
    (T : Triple) {p : ℕ} {ρ C : ℝ}
    (hp : Nat.Prime p)
    (hpOdd : Odd p)
    (ha : 0 < T.a) (hb : 0 < T.b)
    (hjoint : GNOddPrimeJointPressureBudgetAffine T p ρ C) :
    (((p - 1 : ℕ) : ℝ) * Real.log (T.c : ℝ)) ≤
      ρ * Real.log (rad (T.a * T.b * T.c) : ℝ) +
        (C + Real.log (rad p : ℝ)) := by
  let R : ℝ := Real.log (rad (T.a * T.b * T.c) : ℝ)
  let L : ℝ := Real.log (rad ((T.gnPowerLift p).a *
    (T.gnPowerLift p).b * (T.gnPowerLift p).c) : ℝ)
  let S : ℝ := Real.log (GNNonExceptionalSupportProduct p T.a T.b : ℝ)
  let E : ℝ := GNNonExceptionalValuationExcess p T.a T.b
  let Q : ℝ := Real.log (rad (GN p T.a T.b) : ℝ)
  let G : ℝ := Real.log ((GN p T.a T.b : ℕ) : ℝ)
  let H : ℝ := Real.log (T.c : ℝ)
  let P : ℝ := Real.log (rad p : ℝ)
  have hreturn :=
    T.log_c_mul_pred_le_log_GN hp.two_le ha hb
  have hidentity :=
    T.log_GN_eq_log_rad_add_nonExceptionalExcess_of_oddPrime
      hp hpOdd ha hb
  have hsupport :=
    log_rad_GN_le_log_rad_exp_add_log_nonExceptional
      (n := p) (a := T.a) (b := T.b) hp.one_le
  have hfresh :=
    T.log_rad_add_log_nonExceptional_le_log_lift_rad
      hp.two_le ha hb
  change L + E ≤ (1 + ρ) * R + C at hjoint
  change (((p - 1 : ℕ) : ℝ) * H) ≤ G at hreturn
  change G = Q + E at hidentity
  change Q ≤ P + S at hsupport
  change R + S ≤ L at hfresh
  change (((p - 1 : ℕ) : ℝ) * H) ≤ ρ * R + (C + P)
  nlinarith

/-- Pointwise ABC bound obtained directly from a joint odd-prime pressure. -/
theorem Triple.abc_bound_of_oddPrime_jointPressure
    (T : Triple) {p : ℕ} {ε ρ C : ℝ}
    (hp : Nat.Prime p)
    (hpOdd : Odd p)
    (ha : 0 < T.a) (hb : 0 < T.b)
    (hmargin :
      ρ ≤ ((p - 1 : ℕ) : ℝ) * (1 + ε))
    (hjoint : GNOddPrimeJointPressureBudgetAffine T p ρ C) :
    (T.c : ℝ) ≤
      GNABCConstant p C 0 *
        (rad (T.a * T.b * T.c) : ℝ) ^ (1 + ε) := by
  let d : ℝ := ((p - 1 : ℕ) : ℝ)
  let R : ℝ := (rad (T.a * T.b * T.c) : ℝ)
  let B : ℝ := C + Real.log (rad p : ℝ)
  have hpTwo : 2 ≤ p := hp.two_le
  have hd : 1 ≤ d := by
    dsimp [d]
    exact_mod_cast (show 1 ≤ p - 1 by omega)
  have hdpos : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have hRlog : 0 ≤ Real.log R :=
    le_of_lt (T.log_rad_abc_pos ha hb)
  have hheight :=
    T.log_c_mul_pred_le_of_oddPrime_jointPressure
      hp hpOdd ha hb hjoint
  change d * Real.log (T.c : ℝ) ≤ ρ * Real.log R + B at hheight
  have hcoef :
      ρ * Real.log R ≤
        (d * (1 + ε)) * Real.log R :=
    mul_le_mul_of_nonneg_right hmargin hRlog
  have hB : B ≤ d * |B| := by
    have h1 : B ≤ |B| := le_abs_self B
    have h2 : |B| ≤ d * |B| := by
      nlinarith [abs_nonneg B]
    exact h1.trans h2
  have hlog :
      Real.log (T.c : ℝ) ≤
        (1 + ε) * Real.log R + |B| := by
    nlinarith
  have hc : 0 < (T.c : ℝ) := by
    exact_mod_cast (by rw [← T.hsum]; omega : 0 < T.c)
  have hR : 0 < R := by
    dsimp [R]
    exact_mod_cast rad_pos (by
      have hcNat : 0 < T.c := by rw [← T.hsum]; omega
      exact Nat.mul_pos (Nat.mul_pos ha hb) hcNat)
  have hexp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log hc, Real.exp_add] at hexp
  have hrpow :
      Real.exp ((1 + ε) * Real.log R) = R ^ (1 + ε) := by
    rw [mul_comm]
    exact (Real.rpow_def_of_pos hR _).symm
  rw [hrpow] at hexp
  have hconst :
      Real.exp |B| ≤ GNABCConstant p C 0 := by
    simp [GNABCConstant, B]
  have hrpow_nonneg : 0 ≤ R ^ (1 + ε) :=
    Real.rpow_nonneg (le_of_lt hR) _
  calc
    (T.c : ℝ) ≤ R ^ (1 + ε) * Real.exp |B| := hexp
    _ = Real.exp |B| * R ^ (1 + ε) := mul_comm _ _
    _ ≤ GNABCConstant p C 0 * R ^ (1 + ε) :=
      mul_le_mul_of_nonneg_right hconst hrpow_nonneg

/-- Uniform joint-pressure contract sufficient for positive ABC triples. -/
structure ABCGNOddPrimeJointContract (ε : ℝ) where
  hε : 0 < ε
  p : ℕ
  hp : Nat.Prime p
  hpOdd : Odd p
  ρ : ℝ
  C : ℝ
  margin :
    ρ ≤ ((p - 1 : ℕ) : ℝ) * (1 + ε)
  jointBudget :
    ∀ T : Triple, 0 < T.a → 0 < T.b →
      GNOddPrimeJointPressureBudgetAffine T p ρ C

/-- A uniform joint-pressure contract yields ABC for all positive triples. -/
theorem abc_positive_of_GNOddPrimeJointContract
    {ε : ℝ}
    (H : ABCGNOddPrimeJointContract ε) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ T : Triple, 0 < T.a → 0 < T.b →
        (T.c : ℝ) ≤
          K * (rad (T.a * T.b * T.c) : ℝ) ^ (1 + ε) := by
  refine ⟨GNABCConstant H.p H.C 0,
    one_le_GNABCConstant _ _ _, ?_⟩
  intro T ha hb
  exact T.abc_bound_of_oddPrime_jointPressure
    H.hp H.hpOdd ha hb H.margin (H.jointBudget T ha hb)

/--
A uniform joint-pressure contract yields the full raw-variable ABC statement,
including both zero-coordinate endpoints.

This theorem is a deterministic reduction.  It does not construct the
arithmetic joint-pressure contract.
-/
theorem abc_of_GNOddPrimeJointContract
    {ε : ℝ}
    (H : ABCGNOddPrimeJointContract ε) :
    ∃ K : ℝ, (1 : ℝ) ≤ K ∧
      ∀ (a b c : ℕ), a + b = c → Nat.Coprime a b →
        (c : ℝ) ≤
          K * (rad (a * b * c) : ℝ) ^ (1 + ε) := by
  obtain ⟨K, hK, hpositive⟩ :=
    abc_positive_of_GNOddPrimeJointContract H
  refine ⟨K, hK, ?_⟩
  intro a b c hab hcop
  by_cases ha0 : a = 0
  · subst a
    have hb1 : b = 1 := by
      simpa using hcop
    subst b
    have hc1 : c = 1 := by
      omega
    subst c
    simpa using hK
  by_cases hb0 : b = 0
  · subst b
    have ha1 : a = 1 := by
      simpa using hcop
    subst a
    have hc1 : c = 1 := by
      omega
    subst c
    simpa using hK
  let T : Triple :=
    { a := a
      b := b
      c := c
      hsum := hab
      hcop := hcop }
  exact hpositive T (Nat.pos_of_ne_zero ha0) (Nat.pos_of_ne_zero hb0)

end DkMath.ABC
