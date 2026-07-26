/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNDepthMassBadSet
import DkMath.NumberTheory.UniqueFactorizationGN
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Fintype.BigOperators

#print "file: DkMath.ABC.GNJointDepthExponential"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# Exact GN mass, joint CRT depths, and finite exponential tails

This module connects the averaged GN mass to the existing non-exceptional
part, combines simultaneous prime-power conditions through CRT, and packages
a finite exponential-moment/Chernoff interface.

The CRT theorem gives the sharp joint-address count for every fixed finite
depth profile.  The exponential endpoint presently uses an explicit finite
depth cap; summing CRT profiles into an `X`-independent analytic moment
constant remains a separate obligation.
-/

namespace DkMath.ABC

open DkMath.CosmicFormulaBinom

/-- The logarithmic support mass contributed by primes in `Q` which divide the
GN value.  Each prime is counted once, independently of its valuation depth. -/
noncomputable def GNSupportMassAt
    (Q : Finset ℕ) (p b a : ℕ) : ℝ :=
  ∑ q ∈ Q.filter (fun q => q ∣ GN p a b),
    Real.log (q : ℝ)

/-- Exact pointwise decomposition of GN depth mass into first-layer support
mass and valuation excess. -/
theorem GNDepthMassAt_eq_support_add_excess
    {Q : Finset ℕ} {p b a : ℕ}
    (hQprime : ∀ q ∈ Q, Nat.Prime q)
    (hGN : GN p a b ≠ 0) :
    GNDepthMassAt Q p b a =
      GNSupportMassAt Q p b a +
        GNExcessMassAt Q p b a := by
  classical
  unfold GNDepthMassAt GNSupportMassAt GNExcessMassAt
  rw [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  letI : Fact (Nat.Prime q) := ⟨hQprime q hq⟩
  by_cases hqdvd : q ∣ GN p a b
  · have hvone : 1 ≤ padicValNat q (GN p a b) :=
      one_le_padicValNat_of_dvd hGN hqdvd
    rw [if_pos hqdvd]
    have hvsplit :
        (padicValNat q (GN p a b) : ℝ) =
          1 + ((padicValNat q (GN p a b) - 1 : ℕ) : ℝ) := by
      have hvsplitNat :
          padicValNat q (GN p a b) =
            1 + (padicValNat q (GN p a b) - 1) := by
        omega
      exact_mod_cast hvsplitNat
    rw [hvsplit]
    ring
  · have hvzero :
      padicValNat q (GN p a b) = 0 :=
      padicValNat.eq_zero_of_not_dvd hqdvd
    rw [if_neg hqdvd, hvzero]
    norm_num

/-- On a coprime interval point, the canonical non-exceptional interval family
captures exactly the logarithm of the non-exceptional GN part. -/
theorem GNDepthMassAt_intervalFamily_eq_log_nonExceptionalPart
    {p b a X : ℕ}
    (hp : Nat.Prime p)
    (hb : 0 < b)
    (haX : a ∈ Finset.Icc 0 X)
    (hcop : Nat.Coprime a b) :
    GNDepthMassAt
        (GNNonExceptionalIntervalPrimeFamily p b X) p b a =
      Real.log (GNNonExceptionalPart p a b : ℝ) := by
  classical
  let Q := GNNonExceptionalIntervalPrimeFamily p b X
  let S := GNNonExceptionalSupport p a b
  let F := fun q : ℕ =>
    (padicValNat q (GN p a b) : ℝ) * Real.log (q : ℝ)
  have hGN : GN p a b ≠ 0 :=
    GN_ne_zero_of_prime_of_right_ne_zero hp (Nat.ne_of_gt hb)
  have hSsub : S ⊆ Q := by
    intro q hq
    have hqprime :
        Nat.Prime q :=
      (mem_support_factorization_iff.mp
        (Finset.mem_filter.mp hq).1).2.1
    have hqnotb : ¬ q ∣ b :=
      DkMath.NumberTheory.prime_dvd_right_not_dvd_GN_of_coprime
        hp.one_le hcop hqprime
        |> fun hnot hqb =>
          hnot hqb
            (mem_support_factorization_iff.mp
              (Finset.mem_filter.mp hq).1).2.2
    exact mem_GNNonExceptionalIntervalPrimeFamily_iff.mpr
      ⟨a, haX, hq, hqnotb⟩
  have houtside :
      ∀ q ∈ Q, q ∉ S → F q = 0 := by
    intro q hqQ hqS
    have hqprime :=
      GNNonExceptionalIntervalPrimeFamily_prime hqQ
    have hqnotGN : ¬ q ∣ GN p a b := by
      intro hqdvd
      have hmem :
          q ∈ (GN p a b).factorization.support :=
        mem_support_factorization_iff.mpr
          ⟨hGN, hqprime, hqdvd⟩
      exact hqS (Finset.mem_filter.mpr
        ⟨hmem,
          GNNonExceptionalIntervalPrimeFamily_not_dvd_exponent hqQ⟩)
    have hvzero :
        padicValNat q (GN p a b) = 0 :=
      padicValNat.eq_zero_of_not_dvd hqnotGN
    simp only [F, hvzero, Nat.cast_zero, zero_mul]
  calc
    GNDepthMassAt Q p b a = ∑ q ∈ Q, F q := by
      rfl
    _ = ∑ q ∈ S, F q := by
      symm
      exact Finset.sum_subset hSsub houtside
    _ = ∑ q ∈ S,
        ((GNNonExceptionalPart p a b).factorization q : ℝ) *
          Real.log (q : ℝ) := by
      apply Finset.sum_congr rfl
      intro q hq
      have hqprime :
          Nat.Prime q :=
        (mem_support_factorization_iff.mp
          (Finset.mem_filter.mp hq).1).2.1
      rw [GNNonExceptionalPart_factorization, if_pos hq]
      rw [Nat.factorization_def (GN p a b) hqprime]
    _ = Real.log (GNNonExceptionalPart p a b : ℝ) := by
      dsimp [S]
      rw [← GNNonExceptionalPart_factorization_support]
      exact
        DkMath.NumberTheory.PrimitiveSet.sum_factorization_mul_log_eq_log_nat
          (Nat.ne_of_gt (GNNonExceptionalPart_pos p a b))

/-- Product modulus attached to a finite prime family and a depth profile. -/
def GNJointDepthModulus
    (Q : Finset ℕ) (depth : ℕ → ℕ) : ℕ :=
  ∏ q ∈ Q, q ^ depth q

/-- Canonical residue representatives satisfying every divisibility condition
in a finite joint depth profile. -/
def GNJointDepthResidues
    (Q : Finset ℕ) (depth : ℕ → ℕ)
    (p b : ℕ) : Finset ℕ :=
  (Finset.range (GNJointDepthModulus Q depth)).filter
    (fun r => ∀ q ∈ Q, q ^ depth q ∣ GN p r b)

/-- Componentwise congruence modulo pairwise-coprime prime powers combines to
congruence modulo the joint depth modulus. -/
theorem GNJointDepth_modEq
    {Q : Finset ℕ} {depth : ℕ → ℕ} {a r : ℕ}
    (hQprime : ∀ q ∈ Q, Nat.Prime q)
    (hmods : ∀ q ∈ Q, Nat.ModEq (q ^ depth q) a r) :
    Nat.ModEq (GNJointDepthModulus Q depth) a r := by
  classical
  induction Q using Finset.induction_on with
  | empty =>
      simp [GNJointDepthModulus, Nat.modEq_one]
  | @insert q Q hq ih =>
      have hqprime : Nat.Prime q :=
        hQprime q (Finset.mem_insert_self q Q)
      have hcop :
          Nat.Coprime (q ^ depth q)
            (∏ s ∈ Q, s ^ depth s) := by
        apply Nat.Coprime.prod_right
        intro s hs
        exact Nat.coprime_pow_primes
          (depth q) (depth s) hqprime
          (hQprime s (Finset.mem_insert_of_mem hs))
          (by
            intro hqs
            subst s
            exact hq hs)
      have htail :
          Nat.ModEq (GNJointDepthModulus Q depth) a r :=
        ih
          (fun s hs => hQprime s (Finset.mem_insert_of_mem hs))
          (fun s hs => hmods s (Finset.mem_insert_of_mem hs))
      rw [GNJointDepthModulus, Finset.prod_insert hq]
      exact (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp
        ⟨hmods q (Finset.mem_insert_self q Q), htail⟩

/-- A joint depth modulus over a finite family of primes is positive. -/
theorem GNJointDepthModulus_pos
    {Q : Finset ℕ} {depth : ℕ → ℕ}
    (hQprime : ∀ q ∈ Q, Nat.Prime q) :
    0 < GNJointDepthModulus Q depth := by
  unfold GNJointDepthModulus
  exact Finset.prod_pos fun q hq =>
    pow_pos (hQprime q hq).pos _

/-- Under the simple-root hypotheses, a joint depth profile has at most
`(p - 1) ^ Q.card` canonical residue addresses. -/
theorem card_GNJointDepthResidues_le
    {Q : Finset ℕ} {depth : ℕ → ℕ} {p b : ℕ}
    (hp : Nat.Prime p)
    (hQprime : ∀ q ∈ Q, Nat.Prime q)
    (hQp : ∀ q ∈ Q, ¬ q ∣ p)
    (hQb : ∀ q ∈ Q, ¬ q ∣ b) :
    (GNJointDepthResidues Q depth p b).card ≤
      (p - 1) ^ Q.card := by
  classical
  let J := GNJointDepthResidues Q depth p b
  let R := fun q => GNDeepLiftResidues p q b (depth q)
  let P := Q.pi R
  let f : ℕ → (∀ q ∈ Q, ℕ) :=
    fun r q _hq => r % q ^ depth q
  have hmap : J.image f ⊆ P := by
    intro g hg
    obtain ⟨r, hrJ, rfl⟩ := Finset.mem_image.mp hg
    apply Finset.mem_pi.mpr
    intro q hq
    have hr :=
      Finset.mem_filter.mp hrJ
    have hqprime := hQprime q hq
    have hmod :
        Nat.ModEq (q ^ depth q)
          (GN p (r % q ^ depth q) b) (GN p r b) :=
      GN_modEq_left (Nat.mod_modEq r (q ^ depth q))
    have hz :
        Nat.ModEq (q ^ depth q) (GN p r b) 0 :=
      Nat.modEq_zero_iff_dvd.mpr (hr.2 q hq)
    exact mem_GNDeepLiftResidues_iff.mpr
      ⟨Nat.mod_lt _ (pow_pos hqprime.pos _),
        Nat.modEq_zero_iff_dvd.mp (hmod.trans hz)⟩
  have hinj :
      ∀ r ∈ J, ∀ s ∈ J, f r = f s → r = s := by
    intro r hr s hs hrs
    have hmods :
        ∀ q ∈ Q, Nat.ModEq (q ^ depth q) r s := by
      intro q hq
      have hrem :
          r % q ^ depth q = s % q ^ depth q :=
        congr_fun (congr_fun hrs q) hq
      calc
        r ≡ r % q ^ depth q [MOD q ^ depth q] :=
          (Nat.mod_modEq r (q ^ depth q)).symm
        _ = s % q ^ depth q := hrem
        _ ≡ s [MOD q ^ depth q] :=
          Nat.mod_modEq s (q ^ depth q)
    have hprod :=
      GNJointDepth_modEq hQprime hmods
    have hrlt :
        r < GNJointDepthModulus Q depth :=
      Finset.mem_range.mp (Finset.mem_filter.mp hr).1
    have hslt :
        s < GNJointDepthModulus Q depth :=
      Finset.mem_range.mp (Finset.mem_filter.mp hs).1
    change
      r % GNJointDepthModulus Q depth =
        s % GNJointDepthModulus Q depth at hprod
    rwa [Nat.mod_eq_of_lt hrlt, Nat.mod_eq_of_lt hslt] at hprod
  calc
    J.card = (J.image f).card := by
      symm
      apply Finset.card_image_iff.mpr
      exact hinj
    _ ≤ P.card := Finset.card_le_card hmap
    _ = ∏ q ∈ Q, (R q).card := by
      simp [P]
    _ ≤ ∏ _q ∈ Q, (p - 1) := by
      apply Finset.prod_le_prod (fun _q _hq => Nat.zero_le _)
      intro q hq
      by_cases hk : depth q = 0
      · have hone : 1 ≤ p - 1 := by
          have hp2 := hp.two_le
          omega
        simpa [R, GNDeepLiftResidues, hk] using hone
      · exact GNDeepLiftResidues_card_le_of_simpleRoot
          hp (hQprime q hq) (hQp q hq) (hQb q hq)
            (Nat.pos_of_ne_zero hk)
    _ = (p - 1) ^ Q.card := by simp

/-- Interval points satisfying all divisibility conditions in a joint depth
profile. -/
def GNJointDepthEvent
    (Q : Finset ℕ) (depth : ℕ → ℕ)
    (p b X : ℕ) : Finset ℕ :=
  (Finset.Icc 0 X).filter
    (fun a => ∀ q ∈ Q, q ^ depth q ∣ GN p a b)

/-- CRT interval count for a fixed joint depth profile.  The address count is
uniform in the depths; the interval density is controlled by the product
modulus. -/
theorem card_gn_joint_deep_lift_interval_le
    {Q : Finset ℕ} {depth : ℕ → ℕ}
    {p b X : ℕ}
    (hp : Nat.Prime p)
    (hQprime : ∀ q ∈ Q, Nat.Prime q)
    (hQp : ∀ q ∈ Q, ¬ q ∣ p)
    (hQb : ∀ q ∈ Q, ¬ q ∣ b) :
    (GNJointDepthEvent Q depth p b X).card ≤
      (p - 1) ^ Q.card *
        ((X + 1) / GNJointDepthModulus Q depth + 1) := by
  classical
  let M := GNJointDepthModulus Q depth
  let J := GNJointDepthResidues Q depth p b
  let C := fun r =>
    (Finset.Icc 0 X).filter (fun a => Nat.ModEq M a r)
  have hM : 0 < M :=
    GNJointDepthModulus_pos hQprime
  have hsub :
      GNJointDepthEvent Q depth p b X ⊆
        J.biUnion C := by
    intro a ha
    have ha' := Finset.mem_filter.mp ha
    let r := a % M
    have hrJ : r ∈ J := by
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_range.mpr (Nat.mod_lt a hM)
      · intro q hq
        have hqm : q ^ depth q ∣ M := by
          dsimp [M, GNJointDepthModulus]
          exact Finset.dvd_prod_of_mem
            (fun s => s ^ depth s) hq
        have hmod :
            Nat.ModEq (q ^ depth q) r a :=
          (Nat.mod_modEq a M).of_dvd hqm
        have hGNmod :
            Nat.ModEq (q ^ depth q)
              (GN p r b) (GN p a b) :=
          GN_modEq_left hmod
        have hz :
            Nat.ModEq (q ^ depth q) (GN p a b) 0 :=
          Nat.modEq_zero_iff_dvd.mpr (ha'.2 q hq)
        exact Nat.modEq_zero_iff_dvd.mp (hGNmod.trans hz)
    exact Finset.mem_biUnion.mpr
      ⟨r, hrJ, Finset.mem_filter.mpr
        ⟨ha'.1, (Nat.mod_modEq a M).symm⟩⟩
  calc
    (GNJointDepthEvent Q depth p b X).card ≤
        (J.biUnion C).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ r ∈ J, (C r).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _r ∈ J, ((X + 1) / M + 1) := by
      apply Finset.sum_le_sum
      intro r hr
      have hcount :=
        Nat.count_modEq_card (X + 1) hM r
      have hcount' :
          (C r).card =
            (X + 1) / M +
              if r % M < (X + 1) % M then 1 else 0 := by
        simpa [C, ← Nat.range_succ_eq_Icc_zero,
          Nat.count_eq_card_filter_range] using hcount
      rw [hcount']
      split_ifs <;> omega
    _ = J.card * ((X + 1) / M + 1) := by simp
    _ ≤ (p - 1) ^ Q.card * ((X + 1) / M + 1) :=
      Nat.mul_le_mul_right _
        (card_GNJointDepthResidues_le hp hQprime hQp hQb)

/-- The valuation-depth profile of one GN value on a finite prime family. -/
def GNDepthProfileAt
    (Q : Finset ℕ) (p b a : ℕ) :
    ∀ q ∈ Q, ℕ :=
  fun q _hq => padicValNat q (GN p a b)

/-- All depth profiles allowed by the elementary size cap on `[0, X]`. -/
def GNDepthProfileSpace
    (Q : Finset ℕ) (p b X : ℕ) :
    Finset (∀ q ∈ Q, ℕ) :=
  Q.pi fun q =>
    Finset.range (Nat.log q (p * (X + b) ^ p) + 1)

/-- Extend a dependent depth profile on `Q` by zero outside `Q`. -/
def GNDepthProfileExtension
    (Q : Finset ℕ) (depth : ∀ q ∈ Q, ℕ) :
    ℕ → ℕ :=
  fun q => if hq : q ∈ Q then depth q hq else 0

/-- The weighted valuation-excess mass encoded by a finite depth profile. -/
noncomputable def GNExcessProfileMass
    (Q : Finset ℕ) (depth : ∀ q ∈ Q, ℕ) : ℝ :=
  ∑ q ∈ Q.attach,
    ((depth q q.property - 1 : ℕ) : ℝ) *
      Real.log (q : ℝ)

/-- Interval points having exactly a prescribed finite depth profile. -/
def GNExactDepthProfileEvent
    (Q : Finset ℕ) (depth : ∀ q ∈ Q, ℕ)
    (p b X : ℕ) : Finset ℕ :=
  (Finset.Icc 0 X).filter
    (fun a => GNDepthProfileAt Q p b a = depth)

/-- Every interval point has a valuation profile in the finite profile space. -/
theorem GNDepthProfileAt_mem_space
    {Q : Finset ℕ} {p b a X : ℕ}
    (hb : 0 < b)
    (haX : a ≤ X) :
    GNDepthProfileAt Q p b a ∈
      GNDepthProfileSpace Q p b X := by
  classical
  apply Finset.mem_pi.mpr
  intro q hq
  apply Finset.mem_range.mpr
  apply Nat.lt_succ_of_le
  exact (padicValNat_le_nat_log (GN p a b)).trans
    (Nat.log_mono_right
      (GN_le_mul_interval_add_pow hb haX))

/-- On an exact profile fiber, pointwise excess mass is the profile mass. -/
theorem GNExcessMassAt_eq_profileMass
    {Q : Finset ℕ} {depth : ∀ q ∈ Q, ℕ}
    {p b a : ℕ}
    (hdepth : GNDepthProfileAt Q p b a = depth) :
    GNExcessMassAt Q p b a =
      GNExcessProfileMass Q depth := by
  unfold GNExcessMassAt GNExcessProfileMass
  rw [← Finset.sum_attach Q
    (fun q =>
      ((padicValNat q (GN p a b) - 1 : ℕ) : ℝ) *
        Real.log (q : ℝ))]
  apply Finset.sum_congr rfl
  intro q hq
  have hqdepth :
      padicValNat q (GN p a b) = depth q q.property :=
    congr_fun (congr_fun hdepth q) q.property
  rw [hqdepth]

/-- An exact depth-profile fiber is contained in its joint divisibility event. -/
theorem GNExactDepthProfileEvent_subset_joint
    {Q : Finset ℕ} {depth : ∀ q ∈ Q, ℕ}
    {p b X : ℕ} :
    GNExactDepthProfileEvent Q depth p b X ⊆
      GNJointDepthEvent Q
        (GNDepthProfileExtension Q depth) p b X := by
  intro a ha
  have ha' := Finset.mem_filter.mp ha
  apply Finset.mem_filter.mpr
  refine ⟨ha'.1, ?_⟩
  intro q hq
  have hqdepth :
      padicValNat q (GN p a b) = depth q hq :=
    congr_fun (congr_fun ha'.2 q) hq
  simpa [GNDepthProfileExtension, hq, ← hqdepth] using
    (pow_padicValNat_dvd :
      q ^ padicValNat q (GN p a b) ∣ GN p a b)

/-- Finite CRT-profile exponential-moment bound.  Each exact valuation fiber
is assigned its unique finite profile and then bounded by the simultaneous
prime-power interval count.  The remaining analytic task is to majorize this
finite profile sum uniformly in `X`. -/
theorem exp_GNExcessMassAt_sum_le_profile
    {Q : Finset ℕ} {p b X : ℕ} {t : ℝ}
    (hp : Nat.Prime p)
    (hb : 0 < b)
    (hQprime : ∀ q ∈ Q, Nat.Prime q)
    (hQp : ∀ q ∈ Q, ¬ q ∣ p)
    (hQb : ∀ q ∈ Q, ¬ q ∣ b) :
    ∑ a ∈ Finset.Icc 0 X,
        Real.exp (t * GNExcessMassAt Q p b a) ≤
      ∑ depth ∈ GNDepthProfileSpace Q p b X,
        ((((p - 1) ^ Q.card *
          ((X + 1) /
              GNJointDepthModulus Q
                (GNDepthProfileExtension Q depth) + 1) : ℕ) : ℝ) *
          Real.exp (t * GNExcessProfileMass Q depth)) := by
  classical
  let S := Finset.Icc 0 X
  let P := GNDepthProfileSpace Q p b X
  let profile := GNDepthProfileAt Q p b
  have hmaps :
      ∀ a ∈ S, profile a ∈ P := by
    intro a ha
    exact GNDepthProfileAt_mem_space hb
      (Finset.mem_Icc.mp ha).2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun a => Real.exp (t * GNExcessMassAt Q p b a))]
  apply Finset.sum_le_sum
  intro depth hdepth
  let E := GNExactDepthProfileEvent Q depth p b X
  let J := GNJointDepthEvent Q
    (GNDepthProfileExtension Q depth) p b X
  have hEJ : E ⊆ J :=
    GNExactDepthProfileEvent_subset_joint
  have hcard :
      E.card ≤
        (p - 1) ^ Q.card *
          ((X + 1) /
              GNJointDepthModulus Q
                (GNDepthProfileExtension Q depth) + 1) :=
    (Finset.card_le_card hEJ).trans
      (card_gn_joint_deep_lift_interval_le
        hp hQprime hQp hQb)
  have hfiber :
      {a ∈ S | profile a = depth} = E := by
    rfl
  rw [hfiber]
  calc
    ∑ a ∈ E,
        Real.exp (t * GNExcessMassAt Q p b a) =
        ∑ _a ∈ E,
          Real.exp (t * GNExcessProfileMass Q depth) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [GNExcessMassAt_eq_profileMass
        (Finset.mem_filter.mp ha).2]
    _ = (E.card : ℝ) *
        Real.exp (t * GNExcessProfileMass Q depth) := by
      simp
    _ ≤ (((p - 1) ^ Q.card *
          ((X + 1) /
              GNJointDepthModulus Q
                (GNDepthProfileExtension Q depth) + 1) : ℕ) : ℝ) *
        Real.exp (t * GNExcessProfileMass Q depth) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast hcard
      · exact (Real.exp_pos _).le

/-- Explicit finite upper cap for the weighted GN excess mass on `[0, X]`. -/
noncomputable def GNExcessDepthCap
    (Q : Finset ℕ) (p b X : ℕ) : ℝ :=
  ∑ q ∈ Q,
    ((Nat.log q (p * (X + b) ^ p) - 1 : ℕ) : ℝ) *
      Real.log (q : ℝ)

/-- Interval points whose weighted GN excess mass exceeds `threshold`. -/
noncomputable def GNExcessMassBadSet
    (Q : Finset ℕ) (p b X : ℕ)
    (threshold : ℝ) : Finset ℕ :=
  (Finset.Icc 0 X).filter
    (fun a => threshold < GNExcessMassAt Q p b a)

/-- Weighted GN excess mass is nonnegative for a finite prime family. -/
theorem GNExcessMassAt_nonneg
    {Q : Finset ℕ} {p b a : ℕ}
    (hQprime : ∀ q ∈ Q, Nat.Prime q) :
    0 ≤ GNExcessMassAt Q p b a := by
  unfold GNExcessMassAt
  apply Finset.sum_nonneg
  intro q hq
  exact mul_nonneg (Nat.cast_nonneg _)
    (Real.log_nonneg
      (by exact_mod_cast (hQprime q hq).one_le))

/-- The excess mass at an interval point is bounded by the explicit finite
depth cap. -/
theorem GNExcessMassAt_le_depthCap
    {Q : Finset ℕ} {p b a X : ℕ}
    (hb : 0 < b)
    (haX : a ≤ X)
    (hQprime : ∀ q ∈ Q, Nat.Prime q) :
    GNExcessMassAt Q p b a ≤
      GNExcessDepthCap Q p b X := by
  unfold GNExcessMassAt GNExcessDepthCap
  apply Finset.sum_le_sum
  intro q hq
  have hv :
      padicValNat q (GN p a b) ≤
        Nat.log q (p * (X + b) ^ p) := by
    exact (padicValNat_le_nat_log (GN p a b)).trans
      (Nat.log_mono_right
        (GN_le_mul_interval_add_pow hb haX))
  have hvpred :
      padicValNat q (GN p a b) - 1 ≤
        Nat.log q (p * (X + b) ^ p) - 1 :=
    Nat.sub_le_sub_right hv 1
  exact mul_le_mul_of_nonneg_right
    (by exact_mod_cast hvpred)
    (Real.log_nonneg
      (by exact_mod_cast (hQprime q hq).one_le))

/-- Finite exponential-moment bound obtained from the explicit depth cap.
This is a baseline bound, not an `X`-independent CRT-profile estimate. -/
theorem exp_GNExcessMassAt_sum_le
    {Q : Finset ℕ} {p b X : ℕ} {t : ℝ}
    (hb : 0 < b)
    (hQprime : ∀ q ∈ Q, Nat.Prime q)
    (ht : 0 ≤ t) :
    ∑ a ∈ Finset.Icc 0 X,
        Real.exp (t * GNExcessMassAt Q p b a) ≤
      (X + 1 : ℝ) *
        Real.exp (t * GNExcessDepthCap Q p b X) := by
  calc
    ∑ a ∈ Finset.Icc 0 X,
        Real.exp (t * GNExcessMassAt Q p b a) ≤
        ∑ _a ∈ Finset.Icc 0 X,
          Real.exp (t * GNExcessDepthCap Q p b X) := by
      apply Finset.sum_le_sum
      intro a ha
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left
        (GNExcessMassAt_le_depthCap hb
          (Finset.mem_Icc.mp ha).2 hQprime) ht
    _ = (X + 1 : ℝ) *
        Real.exp (t * GNExcessDepthCap Q p b X) := by
      rw [Finset.sum_const, Nat.card_Icc]
      norm_num

/-- Chernoff bound expressing the cardinality of an excess-mass bad set in
terms of its exponential moment. -/
theorem card_GNExcessMassBadSet_le_exp
    {Q : Finset ℕ} {p b X : ℕ}
    {t threshold : ℝ}
    (ht : 0 < t) :
    ((GNExcessMassBadSet
      Q p b X threshold).card : ℝ) ≤
      Real.exp (-t * threshold) *
        (∑ a ∈ Finset.Icc 0 X,
          Real.exp (t * GNExcessMassAt Q p b a)) := by
  let Y := fun a =>
    Real.exp (t * GNExcessMassAt Q p b a)
  let A := Real.exp (t * threshold)
  have hmarkov :=
    markov_card_bound X Y
      (fun n hn => (Real.exp_pos _).le)
      (A := A) (Real.exp_pos _)
  have heq :
      (Finset.Icc 0 X).filter
          (fun a => a ≤ X ∧ A < Y a) =
        GNExcessMassBadSet Q p b X threshold := by
    unfold GNExcessMassBadSet
    ext a
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · intro ha
      exact ⟨ha.1,
        (mul_lt_mul_iff_right₀ ht).mp
          (Real.exp_lt_exp.mp ha.2.2)⟩
    · intro ha
      exact ⟨ha.1, ha.1.2,
        Real.exp_lt_exp.mpr
          ((mul_lt_mul_iff_right₀ ht).mpr ha.2)⟩
  rw [heq] at hmarkov
  calc
    ((GNExcessMassBadSet
      Q p b X threshold).card : ℝ) ≤
        (∑ a ∈ Finset.Icc 0 X, Y a) / A :=
      hmarkov
    _ = Real.exp (-t * threshold) *
        (∑ a ∈ Finset.Icc 0 X,
          Real.exp (t * GNExcessMassAt Q p b a)) := by
      simp only [Y, A, div_eq_mul_inv, ← Real.exp_neg]
      ring_nf

/-- CRT-profile Chernoff bound for the finite excess-mass bad set.  It combines
the exact profile partition with simultaneous prime-power counting; only the
uniform analytic majorization of the displayed finite profile sum remains. -/
theorem card_GNExcessMassBadSet_le_exp_profile
    {Q : Finset ℕ} {p b X : ℕ}
    {t threshold : ℝ}
    (hp : Nat.Prime p)
    (hb : 0 < b)
    (hQprime : ∀ q ∈ Q, Nat.Prime q)
    (hQp : ∀ q ∈ Q, ¬ q ∣ p)
    (hQb : ∀ q ∈ Q, ¬ q ∣ b)
    (ht : 0 < t) :
    ((GNExcessMassBadSet
      Q p b X threshold).card : ℝ) ≤
      Real.exp (-t * threshold) *
        (∑ depth ∈ GNDepthProfileSpace Q p b X,
          ((((p - 1) ^ Q.card *
            ((X + 1) /
                GNJointDepthModulus Q
                  (GNDepthProfileExtension Q depth) + 1) : ℕ) : ℝ) *
            Real.exp (t * GNExcessProfileMass Q depth))) := by
  calc
    ((GNExcessMassBadSet
      Q p b X threshold).card : ℝ) ≤
        Real.exp (-t * threshold) *
          (∑ a ∈ Finset.Icc 0 X,
            Real.exp (t * GNExcessMassAt Q p b a)) :=
      card_GNExcessMassBadSet_le_exp ht
    _ ≤ Real.exp (-t * threshold) *
        (∑ depth ∈ GNDepthProfileSpace Q p b X,
          ((((p - 1) ^ Q.card *
            ((X + 1) /
                GNJointDepthModulus Q
                  (GNDepthProfileExtension Q depth) + 1) : ℕ) : ℝ) *
            Real.exp (t * GNExcessProfileMass Q depth))) := by
      exact mul_le_mul_of_nonneg_left
        (exp_GNExcessMassAt_sum_le_profile
          hp hb hQprime hQp hQb)
        (Real.exp_pos _).le

/-- Explicit finite Chernoff bound obtained by inserting
`GNExcessDepthCap`.  Its cap still depends on the interval endpoint `X`. -/
theorem card_GNExcessMassBadSet_le_explicit
    {Q : Finset ℕ} {p b X : ℕ}
    {t threshold : ℝ}
    (hb : 0 < b)
    (hQprime : ∀ q ∈ Q, Nat.Prime q)
    (ht : 0 < t) :
    ((GNExcessMassBadSet
      Q p b X threshold).card : ℝ) ≤
      (X + 1 : ℝ) *
        Real.exp
          (t * (GNExcessDepthCap Q p b X - threshold)) := by
  calc
    ((GNExcessMassBadSet
      Q p b X threshold).card : ℝ) ≤
        Real.exp (-t * threshold) *
          (∑ a ∈ Finset.Icc 0 X,
            Real.exp (t * GNExcessMassAt Q p b a)) :=
      card_GNExcessMassBadSet_le_exp ht
    _ ≤ Real.exp (-t * threshold) *
        ((X + 1 : ℝ) *
          Real.exp (t * GNExcessDepthCap Q p b X)) := by
      exact mul_le_mul_of_nonneg_left
        (exp_GNExcessMassAt_sum_le hb hQprime ht.le)
        (Real.exp_pos _).le
    _ = (X + 1 : ℝ) *
        (Real.exp (-t * threshold) *
          Real.exp (t * GNExcessDepthCap Q p b X)) := by
      ring
    _ = (X + 1 : ℝ) *
        Real.exp
          (t * (GNExcessDepthCap Q p b X - threshold)) := by
      rw [← Real.exp_add]
      congr 2
      ring

end DkMath.ABC
