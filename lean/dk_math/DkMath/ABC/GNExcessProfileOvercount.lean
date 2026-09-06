/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNExcessLargeBoundaryPacket
import DkMath.NumberTheory.GNThreeQuadratic

open DkMath.CosmicFormulaBinom DkMath.NumberTheory
#print "file: DkMath.ABC.GNExcessProfileOvercount"

/-!
# Unrealized profiles obstruct a linear raw boundary bound

The existing rectangular profile container counts impossible joint profiles within one orientation.
For the canonical cubic family at t = 3/8, this overcount rules out every
constant-times-interval-length upper bound on the raw boundary sum.
Each local requested depth separately passes even the quadratic size test.
A joint height cutoff is necessary for every realized profile.
These are statements about the existing majorant, not the actual moment or ABC.
-/

namespace DkMath.ABC

/-- Both 7 and 13 request depth 2n; other primes are inactive. -/
def GNExcessTwoPrimeProfile (Q : Finset ℕ) (n : ℕ) : ∀ q ∈ Q, ℕ :=
  fun q _ => if q = 7 ∨ q = 13 then 2*n-1 else 0

/-- The two-prime profile activates exactly 7 and 13. -/
theorem GNExcessTwoPrimeProfile_active {Q : Finset ℕ} {n : ℕ}
    (h7 : 7 ∈ Q) (h13 : 13 ∈ Q) (hn : 1 ≤ n) :
    GNExcessActivePrimeSet Q (GNExcessTwoPrimeProfile Q n) = {7,13} := by
  ext q
  by_cases hq7 : q = 7
  · subst q
    simp [GNExcessActivePrimeSet, GNExcessProfileValue, GNExcessTwoPrimeProfile,
      h7, show 0 < 2*n-1 by omega]
  by_cases hq13 : q = 13
  · subst q
    simp [GNExcessActivePrimeSet, GNExcessProfileValue, GNExcessTwoPrimeProfile,
      h13, show 0 < 2*n-1 by omega]
  · simp [GNExcessActivePrimeSet, GNExcessProfileValue, GNExcessTwoPrimeProfile, hq7, hq13]

/-- The exact two-prime modulus is the product of the two requested prime powers. -/
theorem GNExcessTwoPrimeProfile_modulus {Q : Finset ℕ} {n : ℕ}
    (h7 : 7 ∈ Q) (h13 : 13 ∈ Q) (hn : 1 ≤ n) :
    GNExcessJointDepthModulus Q (GNExcessTwoPrimeProfile Q n) = 7^(2*n)*13^(2*n) := by
  rw [GNExcessJointDepthModulus_eq_prod, GNExcessTwoPrimeProfile_active h7 h13 hn]
  simp [GNExcessProfileValue, GNExcessTwoPrimeProfile, h7, h13, show 2*n-1+1=2*n by omega]

/-- The profile's mass is (2n-1) log 91. -/
theorem GNExcessTwoPrimeProfile_mass {Q : Finset ℕ} {n : ℕ}
    (h7 : 7 ∈ Q) (h13 : 13 ∈ Q) (hn : 1 ≤ n) :
    GNExcessActiveProfileMass Q (GNExcessTwoPrimeProfile Q n) = (2*n-1:ℕ)*Real.log 91 := by
  rw [GNExcessActiveProfileMass_eq_sum_active, GNExcessTwoPrimeProfile_active h7 h13 hn]
  simp only [Finset.sum_insert (by norm_num : (7:ℕ) ∉ {13}), Finset.sum_singleton]
  simp only [GNExcessProfileValue, h7, h13, ↓reduceDIte, GNExcessTwoPrimeProfile,
    true_or, or_true, ↓reduceIte]
  rw [show (91:ℝ) = 7*13 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  ring_nf

/-- Each requested prime power separately fits below an actual value in the interval. -/
theorem GNExcessTwoPrimeProfile_local_depth_fits (n : ℕ) :
    (7:ℕ)^(2*n) ≤ GN 3 (13^n) 1 ∧ (13:ℕ)^(2*n) ≤ GN 3 (13^n) 1 := by
  have hpow : (13:ℕ)^(2*n) = (13^n)^2 := by rw [Nat.mul_comm 2 n, pow_mul]
  have hle : (13^n:ℕ)^2 ≤ GN 3 (13^n) 1 := by rw [GN_three_dual_explicit]; omega
  exact ⟨(Nat.pow_le_pow_left (by norm_num : 7 ≤ 13) (2*n)).trans (by rwa [hpow]), by rwa [hpow]⟩

/-- The joint modulus nevertheless exceeds every cubic value on the interval. -/
theorem GNExcessTwoPrimeProfile_modulus_gt_cubic_bound {n : ℕ} (hn : 1 ≤ n) :
    3*(13^n+1)^2 < (7:ℕ)^(2*n)*13^(2*n) := by
  have h7 : 7 ≤ (7:ℕ)^n := by simpa using Nat.pow_le_pow_right (by norm_num : 0 < 7) hn
  have h13 : 13 ≤ (13:ℕ)^n := by simpa using Nat.pow_le_pow_right (by norm_num : 0 < 13) hn
  rw [Nat.mul_comm 2 n, pow_mul, pow_mul]
  have hsq : 49 ≤ (7^n:ℕ)^2 := by nlinarith
  have hmul := Nat.mul_le_mul_right ((13^n)^2) hsq
  nlinarith

/-- The existing profile container admits the profile with both requested depths. -/
theorem GNExcessTwoPrimeProfile_mem_large {Q : Finset ℕ} {n : ℕ}
    (h7 : 7 ∈ Q) (h13 : 13 ∈ Q) (hn : 1 ≤ n) :
    GNExcessTwoPrimeProfile Q n ∈ GNExcessLargeProfileSpace Q 3 1 (13^n) := by
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_pi.mpr
    intro q hq
    apply Finset.mem_range.mpr
    dsimp [GNExcessTwoPrimeProfile]
    split_ifs with heq
    · apply Nat.lt_succ_of_le
      apply Nat.le_log_of_pow_le (by rcases heq with rfl | rfl <;> norm_num)
      have hlocal : q^(2*n) ≤ GN 3 (13^n) 1 := by
        rcases heq with rfl | rfl
        · exact (GNExcessTwoPrimeProfile_local_depth_fits n).1
        · exact (GNExcessTwoPrimeProfile_local_depth_fits n).2
      have hqpos : 0 < q := by rcases heq with rfl | rfl <;> norm_num
      exact (Nat.pow_le_pow_right hqpos (Nat.sub_le _ _)).trans
        (hlocal.trans (GN_le_mul_interval_add_pow (by norm_num : 0 < 1) (le_refl (13^n))))
    · omega
  · rw [GNExcessTwoPrimeProfile_modulus h7 h13 hn]
    have h := GNExcessTwoPrimeProfile_modulus_gt_cubic_bound hn
    nlinarith

/-- The two-prime profile is empty despite both local depths passing the size test. -/
theorem GNExcessTwoPrimeProfile_event_eq_empty {Q : Finset ℕ} {n : ℕ}
    (h7 : 7 ∈ Q) (h13 : 13 ∈ Q) (hn : 1 ≤ n) :
    GNExactExcessProfileEvent Q (GNExcessTwoPrimeProfile Q n) 3 1 (13^n) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  obtain ⟨haI,haE⟩ := Finset.mem_filter.mp ha
  have haX := (Finset.mem_Icc.mp haI).2
  have hd : ∀ q ∈ ({7,13}:Finset ℕ), q^(2*n) ∣ GN 3 a 1 := by
    intro q hq
    have hq' : q = 7 ∨ q = 13 := by simpa using hq
    have hqQ : q ∈ Q := by rcases hq' with rfl | rfl <;> assumption
    have hv := congr_fun (congr_fun haE q) hqQ
    change padicValNat q (GN 3 a 1)-1 = (if q=7 ∨ q=13 then 2*n-1 else 0) at hv
    rw [if_pos hq'] at hv
    have hv' : padicValNat q (GN 3 a 1) = 2*n := by omega
    rw [← hv']
    exact pow_padicValNat_dvd
  have hprod : (7:ℕ)^(2*n)*13^(2*n) ∣ GN 3 a 1 :=
    ((show Nat.Coprime 7 13 by norm_num).pow (2*n) (2*n)).mul_dvd_of_dvd_of_dvd
      (hd 7 (by simp)) (hd 13 (by simp))
  have hpos : 0 < GN 3 a 1 := by rw [GN_three_dual_explicit]; positivity
  have hle := Nat.le_of_dvd hpos hprod
  have hsize : GN 3 a 1 ≤ 3*(13^n+1)^2 := by
    rw [GN_three_dual_explicit]
    have ha2 := Nat.pow_le_pow_left haX 2
    nlinarith
  have hlarge := GNExcessTwoPrimeProfile_modulus_gt_cubic_bound hn
  omega

/-- The empty two-prime profile still contributes its full exponential weight. -/
theorem GNExcessLargeBoundaryProfileSum_ge_two_prime_profile {Q : Finset ℕ} {n : ℕ}
    (h7 : 7 ∈ Q) (h13 : 13 ∈ Q) (hn : 1 ≤ n) (t : ℝ) :
    4*Real.exp (t*((2*n-1:ℕ):ℝ)*Real.log 91) ≤
      GNExcessLargeBoundaryProfileSum Q 3 1 (13^n) t := by
  have h := Finset.single_le_sum
    (s := GNExcessLargeProfileSpace Q 3 1 (13^n))
    (f := fun e => (((3-1)^ (GNExcessActivePrimeSet Q e).card : ℕ):ℝ) *
      Real.exp (t*GNExcessActiveProfileMass Q e))
    (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le)
    (GNExcessTwoPrimeProfile_mem_large h7 h13 hn)
  rw [GNExcessTwoPrimeProfile_active h7 h13 hn, GNExcessTwoPrimeProfile_mass h7 h13 hn] at h
  simpa [GNExcessLargeBoundaryProfileSum, mul_assoc] using h

/-- Both fixed order primes occur in the canonical interval family. -/
theorem seven_thirteen_mem_GNNonExceptionalIntervalPrimeFamily_three {X : ℕ} (hX : 2 ≤ X) :
    7 ∈ GNNonExceptionalIntervalPrimeFamily 3 1 X ∧
      13 ∈ GNNonExceptionalIntervalPrimeFamily 3 1 X := by
  constructor
  · apply mem_GNNonExceptionalIntervalPrimeFamily_iff.mpr
    refine ⟨1, by simp; omega, ?_, by norm_num⟩
    apply Finset.mem_filter.mpr
    refine ⟨mem_support_factorization_iff.mpr ⟨?_, by norm_num, ?_⟩, by norm_num⟩
    · rw [GN_three_dual_explicit]; norm_num
    · rw [GN_three_dual_explicit]; norm_num
  · apply mem_GNNonExceptionalIntervalPrimeFamily_iff.mpr
    refine ⟨2, by simp [hX], ?_, by norm_num⟩
    apply Finset.mem_filter.mpr
    refine ⟨mem_support_factorization_iff.mpr ⟨?_, by norm_num, ?_⟩, by norm_num⟩
    · rw [GN_three_dual_explicit]; norm_num
    · rw [GN_three_dual_explicit]; norm_num


/-- Along n = 4m+1, the impossible profile forces an exponentially growing normalized cost. -/
theorem GNExcessLargeBoundaryProfileSum_three_eighths_ge_geometric {Q : Finset ℕ}
    (h7 : 7 ∈ Q) (h13 : 13 ∈ Q) (m : ℕ) :
    4*(26:ℝ)^m*13^(4*m) ≤
      GNExcessLargeBoundaryProfileSum Q 3 1 (13^(4*m+1)) (3/8) := by
  have hbase := GNExcessLargeBoundaryProfileSum_ge_two_prime_profile h7 h13
    (by omega : 1 ≤ 4*m+1) (3/8:ℝ)
  have he : 2*(4*m+1)-1 = 8*m+1 := by omega
  rw [he] at hbase
  have hlog : 0 ≤ Real.log (91:ℝ) := Real.log_nonneg (by norm_num)
  have hexp : Real.exp (((3*m:ℕ):ℝ)*Real.log 91) ≤
      Real.exp ((3/8:ℝ)*((8*m+1:ℕ):ℝ)*Real.log 91) := by
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith
  rw [Real.exp_nat_mul, Real.exp_log (by norm_num : 0 < (91:ℝ))] at hexp
  have hpow : (26:ℝ)^m*13^(4*m) ≤ 91^(3*m) := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 26*13^4)
      (by norm_num : (26:ℝ)*13^4 ≤ 91^3) m
    simpa only [mul_pow, ← pow_mul, Nat.mul_comm 4 m, Nat.mul_comm 3 m] using h
  calc
    4*(26:ℝ)^m*13^(4*m) = 4*((26:ℝ)^m*13^(4*m)) := by ring
    _ ≤ 4*91^(3*m) := mul_le_mul_of_nonneg_left hpow (by norm_num)
    _ ≤ _ := (mul_le_mul_of_nonneg_left hexp (by norm_num : (0:ℝ) ≤ 4)).trans hbase

/-- No constant times interval length bounds the existing canonical 3/8 boundary sum. -/
theorem not_exists_GNExcess_cubic_largeBoundary_linear_bound :
    ¬ ∃ C : ℝ, ∀ X : ℕ,
      GNExcessLargeBoundaryProfileSum (GNNonExceptionalIntervalPrimeFamily 3 1 X)
        3 1 X (3/8) ≤ C*(X+1:ℝ) := by
  rintro ⟨C,hC⟩
  let B := max C 0
  have hB : 0 ≤ B := le_max_right _ _
  obtain ⟨m,hm⟩ := pow_unbounded_of_one_lt (4*B) (by norm_num : (1:ℝ) < 26)
  let H : ℝ := 13^(4*m)
  have hHp : 0 < H := by dsimp [H]; positivity
  have hH1 : 1 ≤ H := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 13)
  have hX : 2 ≤ (13:ℕ)^(4*m+1) := by
    rw [pow_succ]
    have : 0 < (13:ℕ)^(4*m) := pow_pos (by norm_num) _
    omega
  obtain ⟨h7,h13⟩ := seven_thirteen_mem_GNNonExceptionalIntervalPrimeFamily_three hX
  have hlow := GNExcessLargeBoundaryProfileSum_three_eighths_ge_geometric h7 h13 m
  have hu := hC (13^(4*m+1))
  have hcast : (((13:ℕ)^(4*m+1):ℕ):ℝ)+1 = 13*H+1 := by
    push_cast
    dsimp [H]
    rw [pow_succ]
    ring_nf
  rw [hcast] at hu
  have hCB : C*(13*H+1) ≤ B*(13*H+1) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  have hsize : B*(13*H+1) ≤ 14*B*H := by nlinarith
  have hstrict : 14*B*H < 4*(26:ℝ)^m*H := by
    have hcoef : 14*B < 4*(26:ℝ)^m := by nlinarith
    exact mul_lt_mul_of_pos_right hcoef hHp
  change 4*(26:ℝ)^m*H ≤ _ at hlow
  exact (not_lt_of_ge (hlow.trans (hu.trans (hCB.trans hsize)))) hstrict

/-- A realized canonical cubic profile necessarily passes the joint height cutoff. -/
theorem GNExcess_cubic_realized_modulus_le_height {X : ℕ}
    {e : ∀ q ∈ GNNonExceptionalIntervalPrimeFamily 3 1 X, ℕ}
    (he : (GNExactExcessProfileEvent (GNNonExceptionalIntervalPrimeFamily 3 1 X)
      e 3 1 X).Nonempty) :
    GNExcessJointDepthModulus (GNNonExceptionalIntervalPrimeFamily 3 1 X) e ≤
      3*(X+1)^2 := by
  obtain ⟨a,ha⟩ := he
  obtain ⟨haI,haE⟩ := Finset.mem_filter.mp ha
  rw [← haE, GNExcessJointDepthModulus_target_eq_repeatedPart Nat.prime_three haI (by simp)]
  have hpos : 0 < GN 3 a 1 := by rw [GN_three_dual_explicit]; positivity
  have hle := Nat.le_of_dvd hpos (GNNonExceptionalRepeatedPart_dvd_GN hpos.ne')
  have haX := (Finset.mem_Icc.mp haI).2
  have hsize : GN 3 a 1 ≤ 3*(X+1)^2 := by
    rw [GN_three_dual_explicit]
    have ha2 := Nat.pow_le_pow_left haX 2
    nlinarith
  exact hle.trans hsize

end DkMath.ABC
