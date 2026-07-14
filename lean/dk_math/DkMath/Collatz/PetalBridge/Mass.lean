/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.Ratios

#print "file: DkMath.Collatz.PetalBridge.Mass"

namespace DkMath.Collatz


/--
Source retention mass at depth `r`.

This is the occupation count of the all-ones residue cell `2^r - 1` in the
source window.
-/
noncomputable def orbitWindowRetentionMassPow2
    (n : OddNat) (k r : ℕ) : ℕ :=
  orbitWindowResidueCountPow2 n k r (2 ^ r - 1)

/--
Shifted-tail retention mass at depth `r`.

This is the tail-window counterpart of `orbitWindowRetentionMassPow2`.
-/
noncomputable def orbitWindowRetentionMassPow2Tail
    (n : OddNat) (k r : ℕ) : ℕ :=
  orbitWindowResidueCountPow2Tail n k r (2 ^ r - 1)

/--
Recovery sibling mass inside the next deeper source layer.

At parent depth `r`, this is the child residue `2^r - 1` at depth `r + 1`.
-/
noncomputable def orbitWindowRecoverySiblingMassPow2
    (n : OddNat) (k r : ℕ) : ℕ :=
  orbitWindowResidueCountPow2 n k (r + 1) (2 ^ r - 1)

/--
Continuation sibling mass inside the next deeper source layer.

At parent depth `r`, this is the child residue `2^(r+1) - 1` at depth `r + 1`.
-/
noncomputable def orbitWindowContinuationSiblingMassPow2
    (n : OddNat) (k r : ℕ) : ℕ :=
  orbitWindowResidueCountPow2 n k (r + 1) (2 ^ (r + 1) - 1)

/--
Shifted-tail recovery sibling mass at parent depth `r`.

This is the tail-window child residue `2^r - 1` at depth `r + 1`.
-/
noncomputable def orbitWindowRecoverySiblingMassPow2Tail
    (n : OddNat) (k r : ℕ) : ℕ :=
  orbitWindowResidueCountPow2Tail n k (r + 1) (2 ^ r - 1)

/--
Shifted-tail continuation sibling mass at parent depth `r`.

This is definitionally the same residue shape as tail retention at depth
`r + 1`.
-/
noncomputable def orbitWindowContinuationSiblingMassPow2Tail
    (n : OddNat) (k r : ℕ) : ℕ :=
  orbitWindowResidueCountPow2Tail n k (r + 1) (2 ^ (r + 1) - 1)

/-- Source retention mass is bounded by the window size. -/
theorem orbitWindowRetentionMassPow2_le_window
    (n : OddNat) (k r : ℕ) :
    orbitWindowRetentionMassPow2 n k r ≤ k := by
  unfold orbitWindowRetentionMassPow2
  exact orbitWindowResidueCountPow2_le_window n k r (2 ^ r - 1)

/-- Shifted-tail retention mass is bounded by the window size. -/
theorem orbitWindowRetentionMassPow2Tail_le_window
    (n : OddNat) (k r : ℕ) :
    orbitWindowRetentionMassPow2Tail n k r ≤ k := by
  unfold orbitWindowRetentionMassPow2Tail
  exact orbitWindowResidueCountPow2Tail_le_window n k r (2 ^ r - 1)

/-- Recovery sibling mass is bounded by the window size. -/
theorem orbitWindowRecoverySiblingMassPow2_le_window
    (n : OddNat) (k r : ℕ) :
    orbitWindowRecoverySiblingMassPow2 n k r ≤ k := by
  unfold orbitWindowRecoverySiblingMassPow2
  exact orbitWindowResidueCountPow2_le_window n k (r + 1) (2 ^ r - 1)

/-- Continuation sibling mass is bounded by the window size. -/
theorem orbitWindowContinuationSiblingMassPow2_le_window
    (n : OddNat) (k r : ℕ) :
    orbitWindowContinuationSiblingMassPow2 n k r ≤ k := by
  unfold orbitWindowContinuationSiblingMassPow2
  exact orbitWindowResidueCountPow2_le_window n k (r + 1) (2 ^ (r + 1) - 1)

/-- Shifted-tail recovery sibling mass is bounded by the window size. -/
theorem orbitWindowRecoverySiblingMassPow2Tail_le_window
    (n : OddNat) (k r : ℕ) :
    orbitWindowRecoverySiblingMassPow2Tail n k r ≤ k := by
  unfold orbitWindowRecoverySiblingMassPow2Tail
  exact orbitWindowResidueCountPow2Tail_le_window n k (r + 1) (2 ^ r - 1)

/-- Shifted-tail continuation sibling mass is bounded by the window size. -/
theorem orbitWindowContinuationSiblingMassPow2Tail_le_window
    (n : OddNat) (k r : ℕ) :
    orbitWindowContinuationSiblingMassPow2Tail n k r ≤ k := by
  unfold orbitWindowContinuationSiblingMassPow2Tail
  exact orbitWindowResidueCountPow2Tail_le_window n k (r + 1) (2 ^ (r + 1) - 1)

/--
Deep all-ones power-of-two residue cells are nested inside shallow ones.

If a label is `-1` modulo `2^(e+1)` and `d ≤ e`, then the same label is `-1`
modulo `2^(d+1)`.  This is the pointwise reason selected continuation depths
overlap: deeper continuation channels refine shallower continuation channels.
-/
theorem allOnes_mod_pow_two_of_allOnes_mod_pow_two_of_le
    (q d e : ℕ)
    (hde : d ≤ e)
    (h : q % (2 ^ (e + 1)) = 2 ^ (e + 1) - 1) :
    q % (2 ^ (d + 1)) = 2 ^ (d + 1) - 1 := by
  have hdvd : 2 ^ (d + 1) ∣ 2 ^ (e + 1) := by
    exact pow_dvd_pow 2 (by omega)
  rw [mod_eq_mod_of_dvd_modulus hdvd, h]
  rcases exists_add_of_le hde with ⟨a, rfl⟩
  rw [show d + a + 1 = d + 1 + a by omega, pow_add]
  have hbase : 0 < 2 ^ (d + 1) := pow_pos (by decide) (d + 1)
  have hscale : 0 < 2 ^ a := pow_pos (by decide) a
  have hsplit :
      2 ^ (d + 1) * 2 ^ a - 1 =
        (2 ^ (d + 1) - 1) + (2 ^ a - 1) * 2 ^ (d + 1) := by
    rw [Nat.sub_mul]
    rw [Nat.mul_comm (2 ^ a) (2 ^ (d + 1))]
    ring_nf
    have hle :
        2 ^ d * 2 ≤ 2 ^ d * 2 ^ a * 2 := by
      have ha : 1 ≤ 2 ^ a := by omega
      nlinarith [ha, pow_pos (by decide : 0 < 2) d]
    omega
  rw [hsplit]
  rw [Nat.add_mul_mod_self_right]
  exact Nat.mod_eq_of_lt (by omega)

/--
All-ones retention residue cells are nested by depth.

This is the retention-indexed version of
`allOnes_mod_pow_two_of_allOnes_mod_pow_two_of_le`: the visible retention layer
uses modulus `2^d` rather than the continuation sibling modulus `2^(d+1)`.
-/
theorem retention_allOnes_mod_pow_two_of_le
    (q d e : ℕ)
    (hde : d ≤ e)
    (h : q % (2 ^ e) = 2 ^ e - 1) :
    q % (2 ^ d) = 2 ^ d - 1 := by
  cases d with
  | zero =>
      exact Nat.mod_one q
  | succ d =>
      cases e with
      | zero =>
          omega
      | succ e =>
          exact allOnes_mod_pow_two_of_allOnes_mod_pow_two_of_le
            q d e (by omega) h

/--
Source continuation mass is anti-monotone in depth.

Increasing the depth asks for a more refined all-ones residue cell, so the
finite window count cannot increase.
-/
theorem sourceContinuationMass_anti_mono_depth
    (n : OddNat) (k d e : ℕ)
    (hde : d ≤ e) :
    orbitWindowContinuationSiblingMassPow2 n k e ≤
      orbitWindowContinuationSiblingMassPow2 n k d := by
  induction k with
  | zero =>
      simp [orbitWindowContinuationSiblingMassPow2, orbitWindowResidueCountPow2]
  | succ k ih =>
      have ih' :
          orbitWindowResidueCountPow2 n k (e + 1) (2 ^ (e + 1) - 1) ≤
            orbitWindowResidueCountPow2 n k (d + 1) (2 ^ (d + 1) - 1) := by
        simpa [orbitWindowContinuationSiblingMassPow2] using ih
      rw [orbitWindowContinuationSiblingMassPow2,
        orbitWindowResidueCountPow2_succ]
      rw [orbitWindowContinuationSiblingMassPow2,
        orbitWindowResidueCountPow2_succ]
      by_cases hdeep :
          oddOrbitLabel n k % (2 ^ (e + 1)) = 2 ^ (e + 1) - 1
      · have hshallow :
            oddOrbitLabel n k % (2 ^ (d + 1)) = 2 ^ (d + 1) - 1 :=
          allOnes_mod_pow_two_of_allOnes_mod_pow_two_of_le
            (oddOrbitLabel n k) d e hde hdeep
        simpa [hdeep, hshallow] using ih'
      · by_cases hshallow :
          oddOrbitLabel n k % (2 ^ (d + 1)) = 2 ^ (d + 1) - 1
        · simpa [hdeep, hshallow] using
            (Nat.le_trans ih' (Nat.le_succ
              (orbitWindowResidueCountPow2 n k (d + 1) (2 ^ (d + 1) - 1))))
        · simpa [hdeep, hshallow] using ih'

/--
Shifted-tail continuation mass is anti-monotone in depth.

This is the tail-window counterpart of
`sourceContinuationMass_anti_mono_depth`.
-/
theorem tailContinuationMass_anti_mono_depth
    (n : OddNat) (k d e : ℕ)
    (hde : d ≤ e) :
    orbitWindowContinuationSiblingMassPow2Tail n k e ≤
      orbitWindowContinuationSiblingMassPow2Tail n k d := by
  induction k with
  | zero =>
      simp [orbitWindowContinuationSiblingMassPow2Tail,
        orbitWindowResidueCountPow2Tail]
  | succ k ih =>
      have ih' :
          orbitWindowResidueCountPow2Tail n k (e + 1) (2 ^ (e + 1) - 1) ≤
            orbitWindowResidueCountPow2Tail n k (d + 1) (2 ^ (d + 1) - 1) := by
        simpa [orbitWindowContinuationSiblingMassPow2Tail] using ih
      rw [orbitWindowContinuationSiblingMassPow2Tail,
        orbitWindowResidueCountPow2Tail_succ]
      rw [orbitWindowContinuationSiblingMassPow2Tail,
        orbitWindowResidueCountPow2Tail_succ]
      by_cases hdeep :
          oddOrbitLabel n (k + 1) % (2 ^ (e + 1)) = 2 ^ (e + 1) - 1
      · have hshallow :
            oddOrbitLabel n (k + 1) % (2 ^ (d + 1)) = 2 ^ (d + 1) - 1 :=
          allOnes_mod_pow_two_of_allOnes_mod_pow_two_of_le
            (oddOrbitLabel n (k + 1)) d e hde hdeep
        simpa [hdeep, hshallow] using ih'
      · by_cases hshallow :
          oddOrbitLabel n (k + 1) % (2 ^ (d + 1)) = 2 ^ (d + 1) - 1
        · simpa [hdeep, hshallow] using
            (Nat.le_trans ih' (Nat.le_succ
              (orbitWindowResidueCountPow2Tail n k (d + 1) (2 ^ (d + 1) - 1))))
        · simpa [hdeep, hshallow] using ih'

/--
Selected source continuation masses are nested by selected-depth index.

For a fixed base depth `r`, a later selected index asks for a deeper all-ones
channel and therefore has no more mass than an earlier selected index.
-/
theorem selectedContinuationMass_nested_of_lt
    (n : OddNat) (k r j₁ j₂ : ℕ)
    (hlt : j₁ < j₂) :
    orbitWindowContinuationSiblingMassPow2 n k (r + j₂) ≤
      orbitWindowContinuationSiblingMassPow2 n k (r + j₁) := by
  exact sourceContinuationMass_anti_mono_depth n k (r + j₁) (r + j₂) (by omega)

/--
If the deeper selected continuation mass is positive, then the shallower one
is positive as well.

This is the count-level "overlap is automatic" observation: deeper all-ones
hits are already shallow all-ones hits.
-/
theorem selectedContinuationMass_overlap_of_lt_of_deeper_pos
    (n : OddNat) (k r j₁ j₂ : ℕ)
    (hlt : j₁ < j₂)
    (hpos : 0 < orbitWindowContinuationSiblingMassPow2 n k (r + j₂)) :
    0 < orbitWindowContinuationSiblingMassPow2 n k (r + j₁) :=
  lt_of_lt_of_le hpos (selectedContinuationMass_nested_of_lt n k r j₁ j₂ hlt)

/--
Source retention mass is anti-monotone in depth.

Deeper all-ones retention cells refine shallower all-ones retention cells, so
their finite-window counts cannot increase with depth.
-/
theorem sourceRetentionMass_anti_mono_depth
    (n : OddNat) (k d e : ℕ)
    (hde : d ≤ e) :
    orbitWindowRetentionMassPow2 n k e ≤
      orbitWindowRetentionMassPow2 n k d := by
  induction k with
  | zero =>
      simp [orbitWindowRetentionMassPow2, orbitWindowResidueCountPow2]
  | succ k ih =>
      have ih' :
          orbitWindowResidueCountPow2 n k e (2 ^ e - 1) ≤
            orbitWindowResidueCountPow2 n k d (2 ^ d - 1) := by
        simpa [orbitWindowRetentionMassPow2] using ih
      rw [orbitWindowRetentionMassPow2, orbitWindowResidueCountPow2_succ]
      rw [orbitWindowRetentionMassPow2, orbitWindowResidueCountPow2_succ]
      by_cases hdeep : oddOrbitLabel n k % (2 ^ e) = 2 ^ e - 1
      · have hshallow : oddOrbitLabel n k % (2 ^ d) = 2 ^ d - 1 :=
          retention_allOnes_mod_pow_two_of_le (oddOrbitLabel n k) d e hde hdeep
        simpa [hdeep, hshallow] using ih'
      · by_cases hshallow : oddOrbitLabel n k % (2 ^ d) = 2 ^ d - 1
        · simpa [hdeep, hshallow] using
            (Nat.le_trans ih'
              (Nat.le_succ (orbitWindowResidueCountPow2 n k d (2 ^ d - 1))))
        · simpa [hdeep, hshallow] using ih'

/--
Shifted-tail retention mass is anti-monotone in depth.

This is the tail-window counterpart of
`sourceRetentionMass_anti_mono_depth`.
-/
theorem tailRetentionMass_anti_mono_depth
    (n : OddNat) (k d e : ℕ)
    (hde : d ≤ e) :
    orbitWindowRetentionMassPow2Tail n k e ≤
      orbitWindowRetentionMassPow2Tail n k d := by
  induction k with
  | zero =>
      simp [orbitWindowRetentionMassPow2Tail, orbitWindowResidueCountPow2Tail]
  | succ k ih =>
      have ih' :
          orbitWindowResidueCountPow2Tail n k e (2 ^ e - 1) ≤
            orbitWindowResidueCountPow2Tail n k d (2 ^ d - 1) := by
        simpa [orbitWindowRetentionMassPow2Tail] using ih
      rw [orbitWindowRetentionMassPow2Tail, orbitWindowResidueCountPow2Tail_succ]
      rw [orbitWindowRetentionMassPow2Tail, orbitWindowResidueCountPow2Tail_succ]
      by_cases hdeep : oddOrbitLabel n (k + 1) % (2 ^ e) = 2 ^ e - 1
      · have hshallow : oddOrbitLabel n (k + 1) % (2 ^ d) = 2 ^ d - 1 :=
          retention_allOnes_mod_pow_two_of_le
            (oddOrbitLabel n (k + 1)) d e hde hdeep
        simpa [hdeep, hshallow] using ih'
      · by_cases hshallow : oddOrbitLabel n (k + 1) % (2 ^ d) = 2 ^ d - 1
        · simpa [hdeep, hshallow] using
            (Nat.le_trans ih'
              (Nat.le_succ (orbitWindowResidueCountPow2Tail n k d (2 ^ d - 1))))
        · simpa [hdeep, hshallow] using ih'

/-- The all-ones retention residue is inside its power-of-two modulus. -/
theorem twoAdicRetentionResidue_lt_pow
    (r : ℕ) :
    2 ^ r - 1 < 2 ^ r := by
  have hpos : 0 < 2 ^ r := pow_pos (by decide) r
  omega

/--
Pointwise refinement of a power-of-two residue cell.

If `residue` is a valid cell at depth `depth`, then a number in that cell has
one of exactly two residues at depth `depth + 1`: the left child `residue` or
the right child `residue + 2^depth`.
-/
theorem mod_pow2_succ_eq_left_or_right_of_mod_pow2_eq
    (x depth residue : ℕ)
    (_hres : residue < 2 ^ depth)
    (h : x % (2 ^ depth) = residue) :
    x % (2 ^ (depth + 1)) = residue ∨
      x % (2 ^ (depth + 1)) = residue + 2 ^ depth := by
  let m := 2 ^ depth
  let y := x % (2 ^ (depth + 1))
  have hmpos : 0 < m := by
    dsimp [m]
    exact pow_pos (by decide) depth
  have hpow : 2 ^ (depth + 1) = 2 * m := by
    dsimp [m]
    rw [pow_succ]
    ring
  have hmod : y % m = residue := by
    dsimp [y, m]
    rw [← h]
    rw [Nat.mod_mod_of_dvd]
    · exact ⟨2, by rw [hpow, Nat.mul_comm]⟩
  have hylt : y < 2 * m := by
    dsimp [y]
    rw [hpow]
    exact Nat.mod_lt _ (Nat.mul_pos (by decide) hmpos)
  have hdecomp : y = y % m + m * (y / m) := by
    exact (Nat.mod_add_div y m).symm
  have hydiv_lt : y / m < 2 := by
    exact (Nat.div_lt_iff_lt_mul hmpos).2 hylt
  have hydiv_cases : y / m = 0 ∨ y / m = 1 :=
    Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.lt_succ_iff.mp hydiv_lt)
  cases hydiv_cases with
  | inl hzero =>
      left
      rw [hzero, mul_zero, add_zero, hmod] at hdecomp
      dsimp [y] at hdecomp
      exact hdecomp
  | inr hone =>
      right
      rw [hone, mul_one, hmod] at hdecomp
      dsimp [y, m] at hdecomp
      exact hdecomp

/--
The two child residues at the next power-of-two depth both collapse back to
the parent residue.
-/
theorem mod_pow2_eq_of_mod_pow2_succ_eq_left_or_right
    (x depth residue : ℕ)
    (hres : residue < 2 ^ depth)
    (h :
      x % (2 ^ (depth + 1)) = residue ∨
        x % (2 ^ (depth + 1)) = residue + 2 ^ depth) :
    x % (2 ^ depth) = residue := by
  have hdvd : 2 ^ depth ∣ 2 ^ (depth + 1) := by
    exact ⟨2, by rw [pow_succ, Nat.mul_comm]⟩
  cases h with
  | inl hleft =>
      calc
        x % (2 ^ depth)
            = (x % (2 ^ (depth + 1))) % (2 ^ depth) := by
                rw [Nat.mod_mod_of_dvd _ hdvd]
        _ = residue % (2 ^ depth) := by rw [hleft]
        _ = residue := Nat.mod_eq_of_lt hres
  | inr hright =>
      calc
        x % (2 ^ depth)
            = (x % (2 ^ (depth + 1))) % (2 ^ depth) := by
                rw [Nat.mod_mod_of_dvd _ hdvd]
        _ = (residue + 2 ^ depth) % (2 ^ depth) := by rw [hright]
        _ = residue := by
          rw [Nat.add_mod_right, Nat.mod_eq_of_lt hres]

/--
Pointwise `0/1` indicator split for a valid power-of-two residue cell.

The parent cell at depth `depth` is the disjoint union of the left child
`residue` and the right child `residue + 2^depth` at depth `depth + 1`.
-/
theorem pow2ResidueIndicator_refine_succ
    (x depth residue : ℕ)
    (hres : residue < 2 ^ depth) :
    (if x % (2 ^ depth) = residue then 1 else 0) =
      (if x % (2 ^ (depth + 1)) = residue then 1 else 0) +
        if x % (2 ^ (depth + 1)) = residue + 2 ^ depth then 1 else 0 := by
  by_cases hparent : x % (2 ^ depth) = residue
  · have hsplit :=
      mod_pow2_succ_eq_left_or_right_of_mod_pow2_eq x depth residue hres hparent
    cases hsplit with
    | inl hleft =>
        simp [hparent, hleft]
    | inr hright =>
        simp [hparent, hright]
  · have hleft_not : x % (2 ^ (depth + 1)) ≠ residue := by
      intro hleft
      exact hparent
        (mod_pow2_eq_of_mod_pow2_succ_eq_left_or_right
          x depth residue hres (Or.inl hleft))
    have hright_not :
        x % (2 ^ (depth + 1)) ≠ residue + 2 ^ depth := by
      intro hright
      exact hparent
        (mod_pow2_eq_of_mod_pow2_succ_eq_left_or_right
          x depth residue hres (Or.inr hright))
    simp [hparent, hleft_not, hright_not]

/--
Depth refinement for generic source-window residue counts.

Counting a valid parent cell at depth `depth` is the same as counting both of
its child cells at depth `depth + 1`.
-/
theorem orbitWindowResidueCountPow2_refine_succ
    (n : OddNat) (k depth residue : ℕ)
    (hres : residue < 2 ^ depth) :
    orbitWindowResidueCountPow2 n k depth residue =
      orbitWindowResidueCountPow2 n k (depth + 1) residue +
        orbitWindowResidueCountPow2 n k (depth + 1) (residue + 2 ^ depth) := by
  induction k with
  | zero =>
      simp [orbitWindowResidueCountPow2]
  | succ k ih =>
      rw [orbitWindowResidueCountPow2_succ]
      rw [orbitWindowResidueCountPow2_succ]
      rw [orbitWindowResidueCountPow2_succ]
      rw [ih]
      have hindicator :=
        pow2ResidueIndicator_refine_succ (oddOrbitLabel n k) depth residue hres
      omega

/--
Retention mass splits into the recovery and continuation sibling masses at the
next depth.
-/
theorem orbitWindowRetentionMass_split
    (n : OddNat) (k r : ℕ) :
    orbitWindowRetentionMassPow2 n k r =
      orbitWindowRecoverySiblingMassPow2 n k r +
        orbitWindowContinuationSiblingMassPow2 n k r := by
  unfold orbitWindowRetentionMassPow2
  unfold orbitWindowRecoverySiblingMassPow2
  unfold orbitWindowContinuationSiblingMassPow2
  have hres : 2 ^ r - 1 < 2 ^ r := twoAdicRetentionResidue_lt_pow r
  have hsplit :=
    orbitWindowResidueCountPow2_refine_succ n k r (2 ^ r - 1) hres
  have hright : 2 ^ r - 1 + 2 ^ r = 2 ^ (r + 1) - 1 := by
    have hpos : 0 < 2 ^ r := pow_pos (by decide) r
    rw [pow_succ]
    omega
  simpa [hright] using hsplit

/-- Recovery sibling mass is bounded by the parent retention mass. -/
theorem orbitWindowRecoverySiblingMassPow2_le_retentionMass
    (n : OddNat) (k r : ℕ) :
    orbitWindowRecoverySiblingMassPow2 n k r ≤
      orbitWindowRetentionMassPow2 n k r := by
  rw [orbitWindowRetentionMass_split]
  omega

/-- Continuation sibling mass is bounded by the parent retention mass. -/
theorem orbitWindowContinuationSiblingMassPow2_le_retentionMass
    (n : OddNat) (k r : ℕ) :
    orbitWindowContinuationSiblingMassPow2 n k r ≤
      orbitWindowRetentionMassPow2 n k r := by
  rw [orbitWindowRetentionMass_split]
  omega

/--
Depth refinement for generic shifted-tail residue counts.

This is the tail-window counterpart of
`orbitWindowResidueCountPow2_refine_succ`.
-/
theorem orbitWindowResidueCountPow2Tail_refine_succ
    (n : OddNat) (k depth residue : ℕ)
    (hres : residue < 2 ^ depth) :
    orbitWindowResidueCountPow2Tail n k depth residue =
      orbitWindowResidueCountPow2Tail n k (depth + 1) residue +
        orbitWindowResidueCountPow2Tail n k (depth + 1)
          (residue + 2 ^ depth) := by
  induction k with
  | zero =>
      simp [orbitWindowResidueCountPow2Tail]
  | succ k ih =>
      rw [orbitWindowResidueCountPow2Tail_succ]
      rw [orbitWindowResidueCountPow2Tail_succ]
      rw [orbitWindowResidueCountPow2Tail_succ]
      rw [ih]
      have hindicator :=
        pow2ResidueIndicator_refine_succ
          (oddOrbitLabel n (k + 1)) depth residue hres
      omega

/--
Tail retention mass splits into the tail recovery and tail continuation sibling
masses at the next depth.
-/
theorem orbitWindowRetentionMassPow2Tail_split
    (n : OddNat) (k r : ℕ) :
    orbitWindowRetentionMassPow2Tail n k r =
      orbitWindowRecoverySiblingMassPow2Tail n k r +
        orbitWindowContinuationSiblingMassPow2Tail n k r := by
  unfold orbitWindowRetentionMassPow2Tail
  unfold orbitWindowRecoverySiblingMassPow2Tail
  unfold orbitWindowContinuationSiblingMassPow2Tail
  have hres : 2 ^ r - 1 < 2 ^ r := twoAdicRetentionResidue_lt_pow r
  have hsplit :=
    orbitWindowResidueCountPow2Tail_refine_succ n k r (2 ^ r - 1) hres
  have hright : 2 ^ r - 1 + 2 ^ r = 2 ^ (r + 1) - 1 := by
    have hpos : 0 < 2 ^ r := pow_pos (by decide) r
    rw [pow_succ]
    omega
  simpa [hright] using hsplit

/-- Tail recovery sibling mass is bounded by tail retention mass. -/
theorem orbitWindowRecoverySiblingMassPow2Tail_le_retentionMassTail
    (n : OddNat) (k r : ℕ) :
    orbitWindowRecoverySiblingMassPow2Tail n k r ≤
      orbitWindowRetentionMassPow2Tail n k r := by
  rw [orbitWindowRetentionMassPow2Tail_split]
  omega

/-- Tail continuation sibling mass is bounded by tail retention mass. -/
theorem orbitWindowContinuationSiblingMassPow2Tail_le_retentionMassTail
    (n : OddNat) (k r : ℕ) :
    orbitWindowContinuationSiblingMassPow2Tail n k r ≤
      orbitWindowRetentionMassPow2Tail n k r := by
  rw [orbitWindowRetentionMassPow2Tail_split]
  omega


end DkMath.Collatz
