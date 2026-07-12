/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.FloatWindow.DriftBridge
import DkMath.Collatz.PetalBridge.PressureCore
import DkMath.Collatz.PetalBridge.PressureDecay
import DkMath.Collatz.PetalBridge.TailGrammar

#print "file: DkMath.Collatz.PetalBridge.FloatWindow.PressureIncidenceBridge"

namespace DkMath.Collatz

/-!
# Orbit-time / pressure-depth incidence

Pressure depth is a refinement axis, not a function of orbit time.  The
predicates below deliberately form a relation: one time index may be retained
at every depth below its exact all-ones depth.
-/

/-- A positive modulus sees `q` in its all-ones cell iff it divides `q + 1`. -/
theorem mod_eq_sub_one_iff_dvd_add_one
    {q m : ℕ} (hm : 0 < m) :
    q % m = m - 1 ↔ m ∣ q + 1 := by
  rw [Nat.dvd_iff_mod_eq_zero]
  have hmod : (q + 1) % m = (q % m + 1) % m := by
    simp [Nat.add_mod]
  rw [hmod]
  have hlt := Nat.mod_lt q hm
  constructor
  · intro h
    rw [h]
    have hm1 : m - 1 + 1 = m := by omega
    simp [hm1]
  · intro h
    have hsum : q % m + 1 = m := by
      have hle : q % m + 1 ≤ m := by omega
      by_contra hne
      have hsmall : q % m + 1 < m := by omega
      rw [Nat.mod_eq_of_lt hsmall] at h
      omega
    omega

/-- All-ones depth is characterized by membership in the nested residue cell. -/
theorem le_residualAllOnesDepth_iff_mod_eq_allOnes
    (q d : ℕ) :
    d ≤ ResidualAllOnesDepth q ↔ q % 2 ^ d = 2 ^ d - 1 := by
  unfold ResidualAllOnesDepth v2
  rw [DkMath.ABC.padicValNat_le_iff_dvd Nat.prime_two (by omega) d]
  exact (mod_eq_sub_one_iff_dvd_add_one (pow_pos (by norm_num) d)).symm

/-- Orbit time `i` belongs to the retained all-ones cell at depth `d`. -/
def OrbitDepthRetainedAt (n : OddNat) (i d : ℕ) : Prop :=
  d ≤ ResidualAllOnesDepth (oddOrbitLabel n i)

/-- Orbit time `i` continues from depth `d` into its all-ones child. -/
def OrbitDepthContinuesBeyond (n : OddNat) (i d : ℕ) : Prop :=
  d + 1 ≤ ResidualAllOnesDepth (oddOrbitLabel n i)

/-- Orbit time `i` exits the all-ones ladder exactly at depth `d`. -/
def OrbitDepthRecoversExactlyAt (n : OddNat) (i d : ℕ) : Prop :=
  ResidualAllOnesDepth (oddOrbitLabel n i) = d

/-- Retention incidence is exactly the existing parent residue condition. -/
theorem orbitDepthRetainedAt_iff_mod_eq_allOnes
    (n : OddNat) (i d : ℕ) :
    OrbitDepthRetainedAt n i d ↔
      oddOrbitLabel n i % 2 ^ d = 2 ^ d - 1 := by
  exact le_residualAllOnesDepth_iff_mod_eq_allOnes _ _

/-- Continuation incidence is exactly the deeper all-ones child condition. -/
theorem orbitDepthContinuesBeyond_iff_mod_eq_allOnes_succ
    (n : OddNat) (i d : ℕ) :
    OrbitDepthContinuesBeyond n i d ↔
      oddOrbitLabel n i % 2 ^ (d + 1) = 2 ^ (d + 1) - 1 := by
  exact le_residualAllOnesDepth_iff_mod_eq_allOnes _ _

/-- Exact recovery is retained at `d` but does not continue beyond `d`. -/
theorem orbitDepthRecoversExactlyAt_iff_retained_and_not_continues
    (n : OddNat) (i d : ℕ) :
    OrbitDepthRecoversExactlyAt n i d ↔
      OrbitDepthRetainedAt n i d ∧ ¬ OrbitDepthContinuesBeyond n i d := by
  unfold OrbitDepthRecoversExactlyAt OrbitDepthRetainedAt
    OrbitDepthContinuesBeyond
  omega

/-- Exact recovery is the existing recovery-sibling residue condition. -/
theorem orbitDepthRecoversExactlyAt_iff_recoverySibling
    (n : OddNat) (i d : ℕ) :
    OrbitDepthRecoversExactlyAt n i d ↔
      oddOrbitLabel n i % 2 ^ (d + 1) = 2 ^ d - 1 := by
  rw [orbitDepthRecoversExactlyAt_iff_retained_and_not_continues]
  rw [orbitDepthRetainedAt_iff_mod_eq_allOnes]
  rw [orbitDepthContinuesBeyond_iff_mod_eq_allOnes_succ]
  have hpow : 2 ^ d < 2 ^ (d + 1) := by
    rw [pow_succ]
    have hp : 0 < 2 ^ d := pow_pos (by norm_num) d
    omega
  have hp : 0 < 2 ^ d := pow_pos (by norm_num) d
  have hpSucc : 0 < 2 ^ (d + 1) := pow_pos (by norm_num) (d + 1)
  constructor
  · rintro ⟨hparent, hnotChild⟩
    have hsplit := Nat.mod_mod_of_dvd (oddOrbitLabel n i)
      (pow_dvd_pow 2 (by omega : d ≤ d + 1))
    have hresLt := Nat.mod_lt (oddOrbitLabel n i) hpSucc
    have hchildCases :
        oddOrbitLabel n i % 2 ^ (d + 1) = 2 ^ d - 1 ∨
          oddOrbitLabel n i % 2 ^ (d + 1) = 2 ^ (d + 1) - 1 := by
      have hxmod :
          (oddOrbitLabel n i % 2 ^ (d + 1)) % 2 ^ d = 2 ^ d - 1 := by
        calc
          (oddOrbitLabel n i % 2 ^ (d + 1)) % 2 ^ d =
              oddOrbitLabel n i % 2 ^ d := hsplit
          _ = 2 ^ d - 1 := hparent
      have hdivlt :
          (oddOrbitLabel n i % 2 ^ (d + 1)) / 2 ^ d < 2 := by
        apply (Nat.div_lt_iff_lt_mul hp).2
        simpa [pow_succ, Nat.mul_comm] using hresLt
      have hdivCases :
          (oddOrbitLabel n i % 2 ^ (d + 1)) / 2 ^ d = 0 ∨
            (oddOrbitLabel n i % 2 ^ (d + 1)) / 2 ^ d = 1 := by
        rcases Nat.eq_zero_or_pos
            ((oddOrbitLabel n i % 2 ^ (d + 1)) / 2 ^ d) with hzero | hpos
        · exact Or.inl hzero
        · exact Or.inr (by omega)
      have hdecomp := Nat.mod_add_div
        (oddOrbitLabel n i % 2 ^ (d + 1)) (2 ^ d)
      rcases hdivCases with hzero | hone
      · left
        rw [hzero] at hdecomp
        simpa [hxmod] using hdecomp.symm
      · right
        rw [hone, hxmod] at hdecomp
        rw [pow_succ]
        omega
    exact hchildCases.resolve_right hnotChild
  · intro hrecovery
    constructor
    · rw [← orbitDepthRetainedAt_iff_mod_eq_allOnes]
      exact (show d ≤ ResidualAllOnesDepth (oddOrbitLabel n i) from
        (le_residualAllOnesDepth_iff_mod_eq_allOnes _ _).2 (by
          have hmod := Nat.mod_mod_of_dvd (oddOrbitLabel n i)
            (pow_dvd_pow 2 (by omega : d ≤ d + 1))
          rw [hrecovery] at hmod
          simpa using hmod.symm))
    · intro hcontinue
      rw [hcontinue] at hrecovery
      omega

/-- Number of retained time/depth incidences in a finite orbit window. -/
noncomputable def orbitDepthRetentionFiberCount
    (n : OddNat) (k d : ℕ) : ℕ :=
  (List.range k).countP fun i =>
    decide (oddOrbitLabel n i % 2 ^ d = 2 ^ d - 1)

/-- Number of continuing time/depth incidences in a finite orbit window. -/
noncomputable def orbitDepthContinuationFiberCount
    (n : OddNat) (k d : ℕ) : ℕ :=
  (List.range k).countP fun i =>
    decide (oddOrbitLabel n i % 2 ^ (d + 1) = 2 ^ (d + 1) - 1)

/-- Number of exact-recovery incidences in a finite orbit window. -/
noncomputable def orbitDepthRecoveryFiberCount
    (n : OddNat) (k d : ℕ) : ℕ :=
  (List.range k).countP fun i =>
    decide (oddOrbitLabel n i % 2 ^ (d + 1) = 2 ^ d - 1)

/-- Retention fiber count is definitionally the existing retention mass. -/
theorem orbitDepthRetentionFiberCount_eq_retentionMass
    (n : OddNat) (k d : ℕ) :
    orbitDepthRetentionFiberCount n k d =
      orbitWindowRetentionMassPow2 n k d := by
  unfold orbitDepthRetentionFiberCount orbitWindowRetentionMassPow2
    orbitWindowResidueCountPow2
  rfl

/-- Continuation fiber count is the existing continuation sibling mass. -/
theorem orbitDepthContinuationFiberCount_eq_continuationMass
    (n : OddNat) (k d : ℕ) :
    orbitDepthContinuationFiberCount n k d =
      orbitWindowContinuationSiblingMassPow2 n k d := by
  unfold orbitDepthContinuationFiberCount
    orbitWindowContinuationSiblingMassPow2 orbitWindowResidueCountPow2
  rfl

/-- Exact-recovery fiber count is the existing recovery sibling mass. -/
theorem orbitDepthRecoveryFiberCount_eq_recoveryMass
    (n : OddNat) (k d : ℕ) :
    orbitDepthRecoveryFiberCount n k d =
      orbitWindowRecoverySiblingMassPow2 n k d := by
  unfold orbitDepthRecoveryFiberCount
    orbitWindowRecoverySiblingMassPow2 orbitWindowResidueCountPow2
  rfl

/-- Every retained incidence exits here or continues to the deeper child. -/
theorem orbitDepthRetentionFiberCount_eq_recovery_add_continuation
    (n : OddNat) (k d : ℕ) :
    orbitDepthRetentionFiberCount n k d =
      orbitDepthRecoveryFiberCount n k d +
        orbitDepthContinuationFiberCount n k d := by
  rw [orbitDepthRetentionFiberCount_eq_retentionMass]
  rw [orbitDepthRecoveryFiberCount_eq_recoveryMass]
  rw [orbitDepthContinuationFiberCount_eq_continuationMass]
  exact orbitWindowRetentionMass_split n k d

/--
Source pressure margin is continuation incidence surplus over exact recovery.
-/
theorem sourcePressureMarginInt_eq_continuationFiber_sub_recoveryFiber
    (n : OddNat) (k d : ℕ) :
    SourcePressureMarginInt n k d =
      (orbitDepthContinuationFiberCount n k d : ℤ) -
        orbitDepthRecoveryFiberCount n k d := by
  rw [orbitDepthContinuationFiberCount_eq_continuationMass]
  rw [orbitDepthRecoveryFiberCount_eq_recoveryMass]
  unfold SourcePressureMarginInt
  rw [orbitWindowRetentionMass_split]
  push_cast
  ring

/-- Positive pressure is exactly continuation outnumbering exact recovery. -/
theorem sourcePressureMarginInt_pos_iff_recoveryFiber_lt_continuationFiber
    (n : OddNat) (k d : ℕ) :
    0 < SourcePressureMarginInt n k d ↔
      orbitDepthRecoveryFiberCount n k d <
        orbitDepthContinuationFiberCount n k d := by
  rw [sourcePressureMarginInt_eq_continuationFiber_sub_recoveryFiber]
  omega

/-- The incidence reading agrees with the existing pressure predicate. -/
theorem continuationOutrunsRecovery_iff_recoveryFiber_lt_continuationFiber
    (n : OddNat) (k d : ℕ) :
    ContinuationOutrunsRecovery n k d ↔
      orbitDepthRecoveryFiberCount n k d <
        orbitDepthContinuationFiberCount n k d := by
  unfold ContinuationOutrunsRecovery
  rw [orbitDepthRecoveryFiberCount_eq_recoveryMass]
  rw [orbitDepthContinuationFiberCount_eq_continuationMass]

/-- Exact all-ones depth decreases by one along a recovery transition. -/
theorem orbitDepthRecoversExactlyAt_succ_of_three_le
    (n : OddNat) (i d : ℕ)
    (hd : 3 ≤ d)
    (h : OrbitDepthRecoversExactlyAt n i d) :
    OrbitDepthRecoversExactlyAt n (i + 1) (d - 1) := by
  have hsource :
      oddOrbitLabel n i % 2 ^ (d + 1) = 2 ^ d - 1 :=
    (orbitDepthRecoversExactlyAt_iff_recoverySibling n i d).1 h
  have hd1 : d - 1 + 1 = d := by omega
  have hd2 : d - 1 + 2 = d + 1 := by omega
  have hsource' :
      oddOrbitLabel n i % 2 ^ (d - 1 + 2) = 2 ^ (d - 1 + 1) - 1 := by
    simpa [hd1, hd2] using hsource
  have hnext := oddOrbitLabel_succ_recovery_residue_of_mod
    (d - 1) (by omega) n i hsource'
  apply (orbitDepthRecoversExactlyAt_iff_recoverySibling n (i + 1) (d - 1)).2
  simpa [hd1] using hnext

/--
Generic delayed horizon: exact all-ones depth `d >= 2` pays an extra height at
the exact orbit index `i + d - 1`.
-/
theorem orbitDepthRecoversExactlyAt_delayed_height_two_le
    (n : OddNat) (i d : ℕ)
    (hd : 2 ≤ d)
    (hexact : OrbitDepthRecoversExactlyAt n i d) :
    2 ≤ orbitWindowHeight n (i + d - 1) := by
  have aux : ∀ depth, 2 ≤ depth → ∀ time,
      OrbitDepthRecoversExactlyAt n time depth →
        2 ≤ orbitWindowHeight n (time + depth - 1) := by
    intro depth
    refine Nat.strong_induction_on depth ?_
    intro depth ih hdepth time htime
    by_cases hd2 : depth = 2
    · rw [hd2] at htime ⊢
      have hmod : oddOrbitLabel n time % 8 = 3 := by
        simpa using
          (orbitDepthRecoversExactlyAt_iff_recoverySibling n time 2).1 htime
      simpa using
        orbitWindowNextHeight_two_le_of_mod_eight_eq_three n time hmod
    · have hd3 : 3 ≤ depth := by omega
      have hnext :=
        orbitDepthRecoversExactlyAt_succ_of_three_le n time depth hd3 htime
      have hpay := ih (depth - 1) (by omega) (by omega) (time + 1) hnext
      simpa [show time + 1 + (depth - 1) - 1 =
          time + depth - 1 by omega] using hpay
  exact aux d hd i hexact

/-- A Float growth debt is a strict increase in binary width at orbit time `i`. -/
def FloatDebtAt (n : OddNat) (i : ℕ) : Prop :=
  bitWidth (iterateT i n).1 < bitWidth (iterateT (i + 1) n).1

/-- A lower Petal payment is an extra-height event at orbit time `j`. -/
def PetalPaymentAt (n : OddNat) (j : ℕ) : Prop :=
  2 ≤ orbitWindowHeight n j

/--
Proof-carrying debt/payment incidence.  This remains a relation because
different debts may share a payment and one time belongs to nested depths.
-/
def FloatDebtPaymentDischarge
    (n : OddNat) (i j : ℕ) : Prop :=
  FloatDebtAt n i ∧
    ∃ depth,
      2 ≤ depth ∧
        OrbitDepthRecoversExactlyAt n i depth ∧
          j = i + depth - 1 ∧
            PetalPaymentAt n j

/-- Every Float growth debt has an exact-depth delayed Petal payment witness. -/
theorem floatDebtAt_exists_paymentDischarge
    (n : OddNat) (i : ℕ)
    (hdebt : FloatDebtAt n i) :
    ∃ j, FloatDebtPaymentDischarge n i j := by
  let d := ResidualAllOnesDepth (oddOrbitLabel n i)
  have hgrowth :
      bitWidth (iterateT i n).1 < bitWidth (T (iterateT i n)).1 := by
    simpa [FloatDebtAt, iterateT_succ_eq_T_iterateT] using hdebt
  have hmod := upperGrowth_implies_mod8_three_or_seven (iterateT i n) hgrowth
  have hmod8 : oddOrbitLabel n i % 8 = 3 ∨ oddOrbitLabel n i % 8 = 7 := by
    simpa [oddOrbitLabel] using hmod
  have hretained : 2 ≤ d := by
    apply (le_residualAllOnesDepth_iff_mod_eq_allOnes _ 2).2
    rcases hmod8 with hthree | hseven <;> omega
  have hexact : OrbitDepthRecoversExactlyAt n i d := by
    rfl
  refine ⟨i + d - 1, hdebt, d, hretained, hexact, rfl, ?_⟩
  exact orbitDepthRecoversExactlyAt_delayed_height_two_le n i d hretained hexact

/-- Two distinct Float debts select the same lower payment slot. -/
def FloatPaymentCollisionAt (n : OddNat) (j : ℕ) : Prop :=
  ∃ i₁ i₂,
    i₁ ≠ i₂ ∧
      FloatDebtPaymentDischarge n i₁ j ∧
        FloatDebtPaymentDischarge n i₂ j

/-- A collision still carries an actual extra-height payment at its target. -/
theorem FloatPaymentCollisionAt.payment
    {n : OddNat} {j : ℕ}
    (h : FloatPaymentCollisionAt n j) :
    PetalPaymentAt n j := by
  rcases h with ⟨i₁, i₂, hne, h₁, h₂⟩
  rcases h₁ with ⟨_, depth, _, _, _, hpay⟩
  exact hpay

/-- A collision exposes both distinct debt sources without choosing one. -/
theorem FloatPaymentCollisionAt.exists_distinct_debts
    {n : OddNat} {j : ℕ}
    (h : FloatPaymentCollisionAt n j) :
    ∃ i₁ i₂, i₁ ≠ i₂ ∧ FloatDebtAt n i₁ ∧ FloatDebtAt n i₂ := by
  rcases h with ⟨i₁, i₂, hne, h₁, h₂⟩
  exact ⟨i₁, i₂, hne, h₁.1, h₂.1⟩

/-!
## Multiplicity boundary

The relation above proves existence of a payment for every growth debt, but it
does not prove that the selected payments are injective.  A collision theorem
must retain the fiber of debts over one payment index and compare that
multiplicity with the exact-depth continuation/recovery fibers.  No current
API bounds that fiber or turns multiplicity `>= 2` into positive pressure.
This is the next genuine obstruction; replacing the relation by a function
would erase precisely the collision data that pressure must measure.
-/

end DkMath.Collatz
