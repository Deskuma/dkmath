/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNJointDepthExponential
import Mathlib.Algebra.BigOperators.Ring.Finset

#print "file: DkMath.ABC.GNExcessActiveProfiles"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# Excess-active GN profiles

This module compresses full GN valuation profiles to excess profiles
`(v_q - 1)`.  Only primes carrying positive excess enter the simultaneous CRT
modulus and pay a root-address factor.  The resulting finite profile space is
split into a small-modulus density part and a large-modulus joint-pressure
boundary part.

No infinite Euler-product majorant or pointwise joint contract is asserted
here.
-/

namespace DkMath.ABC

open DkMath.CosmicFormulaBinom

/-- The valuation excess `(v_q(GN) - 1)` at one point of a finite prime
family. -/
def GNExcessDepthProfileAt
    (Q : Finset ℕ) (p b a : ℕ) :
    ∀ q ∈ Q, ℕ :=
  fun q _hq => padicValNat q (GN p a b) - 1

/-- A finite container for all excess profiles occurring on `[0, X]`. -/
def GNExcessDepthProfileSpace
    (Q : Finset ℕ) (p b X : ℕ) :
    Finset (∀ q ∈ Q, ℕ) :=
  Q.pi fun q =>
    Finset.range (Nat.log q (p * (X + b) ^ p) + 1)

/-- Extend an excess profile by zero outside its finite prime family. -/
def GNExcessProfileValue
    (Q : Finset ℕ) (excess : ∀ q ∈ Q, ℕ) :
    ℕ → ℕ :=
  fun q => if hq : q ∈ Q then excess q hq else 0

/-- The primes which carry strictly positive excess in a profile. -/
def GNExcessActivePrimeSet
    (Q : Finset ℕ) (excess : ∀ q ∈ Q, ℕ) :
    Finset ℕ :=
  Q.filter fun q => 0 < GNExcessProfileValue Q excess q

/-- Convert an excess profile to the divisibility depth used by the active CRT
event: positive excess `e_q` requests depth `e_q + 1`; zero excess requests
nothing. -/
def GNExcessProfileExtension
    (Q : Finset ℕ) (excess : ∀ q ∈ Q, ℕ) :
    ℕ → ℕ :=
  fun q =>
    let e := GNExcessProfileValue Q excess q
    if 0 < e then e + 1 else 0

/-- Product of the active prime-power moduli in an excess profile. -/
def GNExcessJointDepthModulus
    (Q : Finset ℕ) (excess : ∀ q ∈ Q, ℕ) : ℕ :=
  GNJointDepthModulus
    (GNExcessActivePrimeSet Q excess)
    (GNExcessProfileExtension Q excess)

/-- Weighted logarithmic excess encoded by an excess profile. -/
noncomputable def GNExcessActiveProfileMass
    (Q : Finset ℕ) (excess : ∀ q ∈ Q, ℕ) : ℝ :=
  ∑ q ∈ Q,
    (GNExcessProfileValue Q excess q : ℝ) *
      Real.log (q : ℝ)

/-- First-layer logarithmic support mass of the active primes. -/
noncomputable def GNExcessActiveSupportMass
    (Q : Finset ℕ) (excess : ∀ q ∈ Q, ℕ) : ℝ :=
  ∑ q ∈ GNExcessActivePrimeSet Q excess,
    Real.log (q : ℝ)

/-- Interval points having exactly the prescribed excess profile. -/
def GNExactExcessProfileEvent
    (Q : Finset ℕ) (excess : ∀ q ∈ Q, ℕ)
    (p b X : ℕ) : Finset ℕ :=
  (Finset.Icc 0 X).filter
    (fun a => GNExcessDepthProfileAt Q p b a = excess)

/-- Excess profiles whose active modulus fits in the interval length. -/
def GNExcessSmallProfileSpace
    (Q : Finset ℕ) (p b X : ℕ) :
    Finset (∀ q ∈ Q, ℕ) :=
  (GNExcessDepthProfileSpace Q p b X).filter
    (fun excess =>
      GNExcessJointDepthModulus Q excess ≤ X + 1)

/-- Excess profiles whose active modulus is larger than the interval length. -/
def GNExcessLargeProfileSpace
    (Q : Finset ℕ) (p b X : ℕ) :
    Finset (∀ q ∈ Q, ℕ) :=
  (GNExcessDepthProfileSpace Q p b X).filter
    (fun excess =>
      X + 1 < GNExcessJointDepthModulus Q excess)

/-- Every interval point determines an element of the finite excess-profile
space. -/
theorem GNExcessDepthProfileAt_mem_space
    {Q : Finset ℕ} {p b a X : ℕ}
    (hb : 0 < b)
    (haX : a ≤ X) :
    GNExcessDepthProfileAt Q p b a ∈
      GNExcessDepthProfileSpace Q p b X := by
  classical
  apply Finset.mem_pi.mpr
  intro q hq
  apply Finset.mem_range.mpr
  apply Nat.lt_succ_of_le
  exact (Nat.sub_le _ _).trans
    ((padicValNat_le_nat_log (GN p a b)).trans
      (Nat.log_mono_right
        (GN_le_mul_interval_add_pow hb haX)))

/-- On an exact excess-profile fiber, pointwise excess mass is exactly its
profile weight. -/
theorem GNExcessMassAt_eq_activeProfileMass
    {Q : Finset ℕ} {excess : ∀ q ∈ Q, ℕ}
    {p b a : ℕ}
    (hprofile :
      GNExcessDepthProfileAt Q p b a = excess) :
    GNExcessMassAt Q p b a =
      GNExcessActiveProfileMass Q excess := by
  unfold GNExcessMassAt GNExcessActiveProfileMass
  apply Finset.sum_congr rfl
  intro q hq
  have hqprofile :
      padicValNat q (GN p a b) - 1 =
        excess q hq :=
    congr_fun (congr_fun hprofile q) hq
  have hvalue :
      GNExcessProfileValue Q excess q = excess q hq := by
    simp [GNExcessProfileValue, hq]
  rw [hvalue, hqprofile]

/-- An exact excess-profile fiber is contained in the simultaneous
divisibility event on its active prime set. -/
theorem GNExactExcessProfileEvent_subset_joint
    {Q : Finset ℕ} {excess : ∀ q ∈ Q, ℕ}
    {p b X : ℕ} :
    GNExactExcessProfileEvent Q excess p b X ⊆
      GNJointDepthEvent
        (GNExcessActivePrimeSet Q excess)
        (GNExcessProfileExtension Q excess) p b X := by
  classical
  intro a ha
  have ha' := Finset.mem_filter.mp ha
  apply Finset.mem_filter.mpr
  refine ⟨ha'.1, ?_⟩
  intro q hqactive
  have hqQ :
      q ∈ Q :=
    (Finset.mem_filter.mp hqactive).1
  have hepos :
      0 < excess q hqQ := by
    simpa [GNExcessProfileValue, hqQ] using
      (Finset.mem_filter.mp hqactive).2
  have hqprofile :
      padicValNat q (GN p a b) - 1 =
        excess q hqQ :=
    congr_fun (congr_fun ha'.2 q) hqQ
  have hv :
      padicValNat q (GN p a b) =
        excess q hqQ + 1 := by
    omega
  simpa [GNExcessProfileExtension,
    GNExcessProfileValue, hqQ, hepos, ← hv] using
      (pow_padicValNat_dvd :
        q ^ padicValNat q (GN p a b) ∣ GN p a b)

/-- The exact excess-profile fiber pays CRT root-address cost only for its
active primes. -/
theorem card_GNExactExcessProfileEvent_le
    {Q : Finset ℕ} {excess : ∀ q ∈ Q, ℕ}
    {p b X : ℕ}
    (hp : Nat.Prime p)
    (hQprime : ∀ q ∈ Q, Nat.Prime q)
    (hQp : ∀ q ∈ Q, ¬ q ∣ p)
    (hQb : ∀ q ∈ Q, ¬ q ∣ b) :
    (GNExactExcessProfileEvent Q excess p b X).card ≤
      (p - 1) ^
          (GNExcessActivePrimeSet Q excess).card *
        ((X + 1) / GNExcessJointDepthModulus Q excess + 1) := by
  have hprimeActive :
      ∀ q ∈ GNExcessActivePrimeSet Q excess,
        Nat.Prime q := by
    intro q hq
    exact hQprime q (Finset.mem_filter.mp hq).1
  have hpActive :
      ∀ q ∈ GNExcessActivePrimeSet Q excess,
        ¬ q ∣ p := by
    intro q hq
    exact hQp q (Finset.mem_filter.mp hq).1
  have hbActive :
      ∀ q ∈ GNExcessActivePrimeSet Q excess,
        ¬ q ∣ b := by
    intro q hq
    exact hQb q (Finset.mem_filter.mp hq).1
  exact
    (Finset.card_le_card
      GNExactExcessProfileEvent_subset_joint).trans
        (card_gn_joint_deep_lift_interval_le
          hp hprimeActive hpActive hbActive)

/-- Every active joint modulus is positive. -/
theorem GNExcessJointDepthModulus_pos
    {Q : Finset ℕ} {excess : ∀ q ∈ Q, ℕ}
    (hQprime : ∀ q ∈ Q, Nat.Prime q) :
    0 < GNExcessJointDepthModulus Q excess := by
  apply GNJointDepthModulus_pos
  intro q hq
  exact hQprime q (Finset.mem_filter.mp hq).1

/-- On an active prime, the CRT depth is exactly `excess + 1`. -/
theorem GNExcessProfileExtension_eq_add_one
    {Q : Finset ℕ} {excess : ∀ q ∈ Q, ℕ}
    {q : ℕ}
    (hq : q ∈ GNExcessActivePrimeSet Q excess) :
    GNExcessProfileExtension Q excess q =
      GNExcessProfileValue Q excess q + 1 := by
  have hepos :
      0 < GNExcessProfileValue Q excess q :=
    (Finset.mem_filter.mp hq).2
  simp [GNExcessProfileExtension, hepos]

/-- Expanded product formula for the active joint modulus. -/
theorem GNExcessJointDepthModulus_eq_prod
    {Q : Finset ℕ} {excess : ∀ q ∈ Q, ℕ} :
    GNExcessJointDepthModulus Q excess =
      ∏ q ∈ GNExcessActivePrimeSet Q excess,
        q ^ (GNExcessProfileValue Q excess q + 1) := by
  unfold GNExcessJointDepthModulus GNJointDepthModulus
  apply Finset.prod_congr rfl
  intro q hq
  rw [GNExcessProfileExtension_eq_add_one hq]

/-- Inactive primes contribute zero, so the profile mass can be summed only
over the active set. -/
theorem GNExcessActiveProfileMass_eq_sum_active
    {Q : Finset ℕ} {excess : ∀ q ∈ Q, ℕ} :
    GNExcessActiveProfileMass Q excess =
      ∑ q ∈ GNExcessActivePrimeSet Q excess,
        (GNExcessProfileValue Q excess q : ℝ) *
          Real.log (q : ℝ) := by
  classical
  unfold GNExcessActiveProfileMass
    GNExcessActivePrimeSet
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q hq
  simp only [GNExcessProfileValue, hq, ↓reduceDIte]
  by_cases he : 0 < excess q hq
  · rw [ite_eq_left he]
  · rw [ite_eq_right he]
    have hz : excess q hq = 0 := Nat.eq_zero_of_not_pos he
    simp [hz]

/-- The logarithm of an active profile modulus is exactly active support mass
plus excess mass. -/
theorem log_GNExcessJointDepthModulus_eq_support_add_excess
    {Q : Finset ℕ} {excess : ∀ q ∈ Q, ℕ}
    (hQprime : ∀ q ∈ Q, Nat.Prime q) :
    Real.log (GNExcessJointDepthModulus Q excess : ℝ) =
      GNExcessActiveSupportMass Q excess +
        GNExcessActiveProfileMass Q excess := by
  classical
  rw [GNExcessJointDepthModulus_eq_prod]
  push_cast
  rw [Real.log_prod]
  · rw [GNExcessActiveProfileMass_eq_sum_active]
    unfold GNExcessActiveSupportMass
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Real.log_pow]
    push_cast
    ring
  · intro q hq
    have hqQ := (Finset.mem_filter.mp hq).1
    exact pow_ne_zero _
      (Nat.cast_ne_zero.mpr (hQprime q hqQ).ne_zero)

/-- A large active modulus certifies that active support plus excess already
exceeds the logarithmic interval scale. -/
theorem GNExcessLargeProfile_jointMass_gt_log_interval
    {Q : Finset ℕ} {excess : ∀ q ∈ Q, ℕ}
    {X : ℕ}
    (hQprime : ∀ q ∈ Q, Nat.Prime q)
    (hlarge :
      X + 1 < GNExcessJointDepthModulus Q excess) :
    Real.log (X + 1 : ℝ) <
      GNExcessActiveSupportMass Q excess +
        GNExcessActiveProfileMass Q excess := by
  rw [←
    log_GNExcessJointDepthModulus_eq_support_add_excess
      hQprime]
  apply Real.log_lt_log
  · positivity
  · exact_mod_cast hlarge

/-- Elementary small-modulus conversion of the CRT boundary `+1` to twice
the interval density. -/
theorem div_add_one_le_two_mul_div_of_le
    {N M : ℕ}
    (hM : 0 < M)
    (hMN : M ≤ N) :
    N / M + 1 ≤ 2 * (N / M) := by
  have hone : 1 ≤ N / M := by
    exact (Nat.le_div_iff_mul_le hM).mpr
      (by simpa using hMN)
  omega

/-- Density weight of one excess profile. -/
noncomputable def GNExcessProfileDensityWeight
    (Q : Finset ℕ) (p : ℕ)
    (excess : ∀ q ∈ Q, ℕ) (t : ℝ) : ℝ :=
  (((p - 1) ^
      (GNExcessActivePrimeSet Q excess).card : ℕ) : ℝ) /
      (GNExcessJointDepthModulus Q excess : ℝ) *
    Real.exp (t * GNExcessActiveProfileMass Q excess)

/-- Finite Euler-density sum over every allowed excess profile. -/
noncomputable def GNExcessFiniteEulerDensity
    (Q : Finset ℕ) (p b X : ℕ) (t : ℝ) : ℝ :=
  ∑ excess ∈ GNExcessDepthProfileSpace Q p b X,
    GNExcessProfileDensityWeight Q p excess t

/-- The density contribution from profiles whose active modulus fits in the
interval. -/
noncomputable def GNExcessSmallDensityProfileSum
    (Q : Finset ℕ) (p b X : ℕ) (t : ℝ) : ℝ :=
  ∑ excess ∈ GNExcessSmallProfileSpace Q p b X,
    GNExcessProfileDensityWeight Q p excess t

/-- The undivided CRT boundary contribution from profiles whose active
modulus exceeds the interval length. -/
noncomputable def GNExcessLargeBoundaryProfileSum
    (Q : Finset ℕ) (p b X : ℕ) (t : ℝ) : ℝ :=
  ∑ excess ∈ GNExcessLargeProfileSpace Q p b X,
    (((p - 1) ^
        (GNExcessActivePrimeSet Q excess).card : ℕ) : ℝ) *
      Real.exp (t * GNExcessActiveProfileMass Q excess)

/-- A profile density weight is nonnegative. -/
theorem GNExcessProfileDensityWeight_nonneg
    {Q : Finset ℕ} {p : ℕ}
    {excess : ∀ q ∈ Q, ℕ} {t : ℝ} :
    0 ≤ GNExcessProfileDensityWeight Q p excess t := by
  unfold GNExcessProfileDensityWeight
  exact mul_nonneg
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (Real.exp_pos _).le

/-- One local Euler-density weight.  Excess zero contributes the neutral
factor; positive excess `j` contributes its active root charge, exponential
weight, and prime-power density. -/
noncomputable def GNExcessLocalDensityWeight
    (p q j : ℕ) (t : ℝ) : ℝ :=
  if j = 0 then 1
  else
    ((p - 1 : ℕ) : ℝ) *
        Real.exp (t * (j : ℝ) * Real.log (q : ℝ)) /
      (q : ℝ) ^ (j + 1)

/-- The local finite Euler factor with excess cap `K`. -/
noncomputable def GNExcessLocalDensityFactor
    (p q K : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range K,
    GNExcessLocalDensityWeight p q j t

/-- Arithmetic density weight equals the product of its active local
components. -/
theorem GNExcessProfileDensityWeight_eq_prod_active
    {Q : Finset ℕ} {p : ℕ}
    {excess : ∀ q ∈ Q, ℕ} {t : ℝ} :
    GNExcessProfileDensityWeight Q p excess t =
      ∏ q ∈ GNExcessActivePrimeSet Q excess,
        ((p - 1 : ℕ) : ℝ) *
            Real.exp
              (t *
                (GNExcessProfileValue Q excess q : ℝ) *
                Real.log (q : ℝ)) /
          (q : ℝ) ^
            (GNExcessProfileValue Q excess q + 1) := by
  classical
  unfold GNExcessProfileDensityWeight
  rw [GNExcessJointDepthModulus_eq_prod]
  push_cast
  rw [GNExcessActiveProfileMass_eq_sum_active]
  rw [Finset.mul_sum, Real.exp_sum]
  rw [Finset.prod_div_distrib]
  rw [Finset.prod_mul_distrib]
  rw [Finset.prod_const]
  ring_nf

/-- Arithmetic density weight equals the product of all local weights, with
inactive components automatically equal to one. -/
theorem GNExcessProfileDensityWeight_eq_prod_local
    {Q : Finset ℕ} {p : ℕ}
    {excess : ∀ q ∈ Q, ℕ} {t : ℝ} :
    GNExcessProfileDensityWeight Q p excess t =
      ∏ q ∈ Q.attach,
        GNExcessLocalDensityWeight p q
          (excess q q.property) t := by
  classical
  rw [GNExcessProfileDensityWeight_eq_prod_active]
  have hattach :
      (∏ q ∈ Q.attach,
          GNExcessLocalDensityWeight p q
            (excess q q.property) t) =
        ∏ q ∈ Q,
          GNExcessLocalDensityWeight p q
            (GNExcessProfileValue Q excess q) t := by
    rw [← Finset.prod_attach Q
      (fun q =>
        GNExcessLocalDensityWeight p q
          (GNExcessProfileValue Q excess q) t)]
    apply Finset.prod_congr rfl
    intro q hq
    simp [GNExcessProfileValue]
  rw [hattach]
  unfold GNExcessLocalDensityWeight
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, one_mul]
  apply Finset.prod_congr
  · ext q
    simp [GNExcessActivePrimeSet, Nat.pos_iff_ne_zero]
  · intro q hq
    rfl

/-- The unrestricted finite excess-profile density sum factors exactly as a
finite product of local prime factors. -/
theorem sum_GNExcessProfileDensityWeight_eq_prod
    {Q : Finset ℕ} {p b X : ℕ} {t : ℝ} :
    GNExcessFiniteEulerDensity Q p b X t =
      ∏ q ∈ Q,
        GNExcessLocalDensityFactor p q
          (Nat.log q (p * (X + b) ^ p) + 1) t := by
  classical
  unfold GNExcessFiniteEulerDensity
    GNExcessDepthProfileSpace
    GNExcessLocalDensityFactor
  rw [Finset.prod_sum]
  apply Finset.sum_congr rfl
  intro excess hexcess
  exact GNExcessProfileDensityWeight_eq_prod_local

/-- The small-profile density sum is bounded by the unrestricted finite Euler
density. -/
theorem GNExcessSmallDensityProfileSum_le_finiteEulerDensity
    {Q : Finset ℕ} {p b X : ℕ} {t : ℝ} :
    GNExcessSmallDensityProfileSum Q p b X t ≤
      GNExcessFiniteEulerDensity Q p b X t := by
  classical
  unfold GNExcessSmallDensityProfileSum
    GNExcessFiniteEulerDensity
    GNExcessSmallProfileSpace
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset _ _)
    (fun _ _ _ => GNExcessProfileDensityWeight_nonneg)

/-- Small-modulus cardinality bound in real density form. -/
theorem card_GNExactExcessProfileEvent_le_smallDensity
    {Q : Finset ℕ} {excess : ∀ q ∈ Q, ℕ}
    {p b X : ℕ}
    (hp : Nat.Prime p)
    (hQprime : ∀ q ∈ Q, Nat.Prime q)
    (hQp : ∀ q ∈ Q, ¬ q ∣ p)
    (hQb : ∀ q ∈ Q, ¬ q ∣ b)
    (hsmall :
      GNExcessJointDepthModulus Q excess ≤ X + 1) :
    ((GNExactExcessProfileEvent
      Q excess p b X).card : ℝ) ≤
      2 * (X + 1 : ℝ) *
        ((((p - 1) ^
          (GNExcessActivePrimeSet Q excess).card : ℕ) : ℝ) /
            (GNExcessJointDepthModulus Q excess : ℝ)) := by
  let C :=
    (p - 1) ^
      (GNExcessActivePrimeSet Q excess).card
  let M := GNExcessJointDepthModulus Q excess
  let N := X + 1
  have hM : 0 < M :=
    GNExcessJointDepthModulus_pos hQprime
  have hcard :
      (GNExactExcessProfileEvent
        Q excess p b X).card ≤
        C * (N / M + 1) := by
    exact card_GNExactExcessProfileEvent_le
      hp hQprime hQp hQb
  have hdiv :
      N / M + 1 ≤ 2 * (N / M) :=
    div_add_one_le_two_mul_div_of_le hM hsmall
  have hnat :
      (GNExactExcessProfileEvent
        Q excess p b X).card ≤
        2 * C * (N / M) := by
    calc
      (GNExactExcessProfileEvent
        Q excess p b X).card ≤
          C * (N / M + 1) := hcard
      _ ≤ C * (2 * (N / M)) :=
        Nat.mul_le_mul_left C hdiv
      _ = 2 * C * (N / M) := by ring
  calc
    ((GNExactExcessProfileEvent
      Q excess p b X).card : ℝ) ≤
        ((2 * C * (N / M) : ℕ) : ℝ) := by
      exact_mod_cast hnat
    _ = 2 * (C : ℝ) * ((N / M : ℕ) : ℝ) := by
      norm_num
    _ ≤ 2 * (C : ℝ) * ((N : ℝ) / (M : ℝ)) := by
      gcongr
      exact Nat.cast_div_le
    _ = 2 * (X + 1 : ℝ) *
        ((((p - 1) ^
          (GNExcessActivePrimeSet Q excess).card : ℕ) : ℝ) /
            (GNExcessJointDepthModulus Q excess : ℝ)) := by
      dsimp [C, M, N]
      push_cast
      ring

/-- A large-modulus exact profile fiber pays only its active root-address
charge because the interval contains at most one representative per address. -/
theorem card_GNExactExcessProfileEvent_le_largeBoundary
    {Q : Finset ℕ} {excess : ∀ q ∈ Q, ℕ}
    {p b X : ℕ}
    (hp : Nat.Prime p)
    (hQprime : ∀ q ∈ Q, Nat.Prime q)
    (hQp : ∀ q ∈ Q, ¬ q ∣ p)
    (hQb : ∀ q ∈ Q, ¬ q ∣ b)
    (hlarge :
      X + 1 < GNExcessJointDepthModulus Q excess) :
    (GNExactExcessProfileEvent
      Q excess p b X).card ≤
        (p - 1) ^
          (GNExcessActivePrimeSet Q excess).card := by
  have hcard :=
    card_GNExactExcessProfileEvent_le
      hp hQprime hQp hQb
      (Q := Q) (excess := excess) (X := X)
  simpa [Nat.div_eq_of_lt hlarge] using hcard

/-- Exact-fiber exponential moment split into small-modulus density profiles
and large-modulus boundary profiles. -/
theorem exp_GNExcessMassAt_sum_le_small_add_large
    {Q : Finset ℕ} {p b X : ℕ} {t : ℝ}
    (hp : Nat.Prime p)
    (hb : 0 < b)
    (hQprime : ∀ q ∈ Q, Nat.Prime q)
    (hQp : ∀ q ∈ Q, ¬ q ∣ p)
    (hQb : ∀ q ∈ Q, ¬ q ∣ b) :
    ∑ a ∈ Finset.Icc 0 X,
        Real.exp (t * GNExcessMassAt Q p b a) ≤
      2 * (X + 1 : ℝ) *
          GNExcessSmallDensityProfileSum Q p b X t +
        GNExcessLargeBoundaryProfileSum Q p b X t := by
  classical
  let S := Finset.Icc 0 X
  let P := GNExcessDepthProfileSpace Q p b X
  let profile := GNExcessDepthProfileAt Q p b
  have hmaps :
      ∀ a ∈ S, profile a ∈ P := by
    intro a ha
    exact GNExcessDepthProfileAt_mem_space hb
      (Finset.mem_Icc.mp ha).2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun a => Real.exp (t * GNExcessMassAt Q p b a))]
  calc
    ∑ excess ∈ P,
        ∑ a ∈ S with profile a = excess,
          Real.exp (t * GNExcessMassAt Q p b a) ≤
        ∑ excess ∈ P,
          if GNExcessJointDepthModulus Q excess ≤ X + 1 then
            2 * (X + 1 : ℝ) *
              GNExcessProfileDensityWeight Q p excess t
          else
            (((p - 1) ^
                (GNExcessActivePrimeSet Q excess).card : ℕ) : ℝ) *
              Real.exp
                (t * GNExcessActiveProfileMass Q excess) := by
      apply Finset.sum_le_sum
      intro excess hexcess
      let E := GNExactExcessProfileEvent Q excess p b X
      have hfiber :
          {a ∈ S | profile a = excess} = E := by
        rfl
      rw [hfiber]
      have hmass :
          ∑ a ∈ E,
              Real.exp (t * GNExcessMassAt Q p b a) =
            (E.card : ℝ) *
              Real.exp
                (t * GNExcessActiveProfileMass Q excess) := by
        calc
          ∑ a ∈ E,
              Real.exp (t * GNExcessMassAt Q p b a) =
              ∑ _a ∈ E,
                Real.exp
                  (t * GNExcessActiveProfileMass Q excess) := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [GNExcessMassAt_eq_activeProfileMass
              (Finset.mem_filter.mp ha).2]
          _ = (E.card : ℝ) *
              Real.exp
                (t * GNExcessActiveProfileMass Q excess) := by
            simp
      rw [hmass]
      by_cases hsmall :
          GNExcessJointDepthModulus Q excess ≤ X + 1
      · rw [ite_eq_left hsmall]
        unfold GNExcessProfileDensityWeight
        calc
          (E.card : ℝ) *
              Real.exp
                (t * GNExcessActiveProfileMass Q excess) ≤
              (2 * (X + 1 : ℝ) *
                ((((p - 1) ^
                  (GNExcessActivePrimeSet Q excess).card : ℕ) : ℝ) /
                    (GNExcessJointDepthModulus Q excess : ℝ))) *
                Real.exp
                  (t * GNExcessActiveProfileMass Q excess) := by
            exact mul_le_mul_of_nonneg_right
              (card_GNExactExcessProfileEvent_le_smallDensity
                hp hQprime hQp hQb hsmall)
              (Real.exp_pos _).le
          _ = 2 * (X + 1 : ℝ) *
              ((((p - 1) ^
                (GNExcessActivePrimeSet Q excess).card : ℕ) : ℝ) /
                  (GNExcessJointDepthModulus Q excess : ℝ) *
                Real.exp
                  (t * GNExcessActiveProfileMass Q excess)) := by
            ring
      · rw [ite_eq_right hsmall]
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast
            card_GNExactExcessProfileEvent_le_largeBoundary
              hp hQprime hQp hQb (Nat.lt_of_not_ge hsmall)
        · exact (Real.exp_pos _).le
    _ = 2 * (X + 1 : ℝ) *
          GNExcessSmallDensityProfileSum Q p b X t +
        GNExcessLargeBoundaryProfileSum Q p b X t := by
      simp only [P, GNExcessSmallDensityProfileSum,
        GNExcessLargeBoundaryProfileSum,
        GNExcessSmallProfileSpace,
        GNExcessLargeProfileSpace,
        Finset.sum_filter]
      rw [Finset.mul_sum]
      simp only [mul_ite, mul_zero]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro excess hexcess
      split_ifs with hsmall hlarge
      · omega
      · simp
      · simp
      · omega

/-- The requested public moment bound with the small contribution enlarged to
the unrestricted finite Euler-density sum. -/
theorem exp_GNExcessMassAt_sum_le_finiteEuler_add_large
    {Q : Finset ℕ} {p b X : ℕ} {t : ℝ}
    (hp : Nat.Prime p)
    (hb : 0 < b)
    (hQprime : ∀ q ∈ Q, Nat.Prime q)
    (hQp : ∀ q ∈ Q, ¬ q ∣ p)
    (hQb : ∀ q ∈ Q, ¬ q ∣ b) :
    ∑ a ∈ Finset.Icc 0 X,
        Real.exp (t * GNExcessMassAt Q p b a) ≤
      2 * (X + 1 : ℝ) *
          GNExcessFiniteEulerDensity Q p b X t +
        GNExcessLargeBoundaryProfileSum Q p b X t := by
  have hcoef : 0 ≤ 2 * (X + 1 : ℝ) := by
    norm_num
    positivity
  have hsmall :
      2 * (X + 1 : ℝ) *
          GNExcessSmallDensityProfileSum Q p b X t ≤
        2 * (X + 1 : ℝ) *
          GNExcessFiniteEulerDensity Q p b X t :=
    mul_le_mul_of_nonneg_left
      (GNExcessSmallDensityProfileSum_le_finiteEulerDensity
        (Q := Q) (p := p) (b := b) (X := X) (t := t))
      hcoef
  exact (exp_GNExcessMassAt_sum_le_small_add_large
    hp hb hQprime hQp hQb).trans
      (add_le_add hsmall (le_refl _))

end DkMath.ABC
