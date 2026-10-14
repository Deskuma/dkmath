/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionCenteredPolynomial

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionCenteredGnomonGap"

namespace DkMath.FLT.Seven

/-- A positive adjacent sixth-power step dominates the fifth power.
The additive form avoids truncated subtraction. -/
theorem adjacent_sixth_power_add_le {Q : ℕ} (hQ : 0 < Q) :
    (Q - 1) ^ 6 + Q ^ 5 ≤ Q ^ 6 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hQ)
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
  have hidentity : (k + 1) ^ 6 = k ^ 6 + (k + 1) ^ 5 +
      k * (5 * k ^ 4 + 10 * k ^ 3 + 10 * k ^ 2 + 5 * k + 1) := by ring
  rw [hidentity]
  omega

theorem adjacent_sixth_power_sub_ge {Q : ℕ} (hQ : 0 < Q) :
    Q ^ 5 ≤ Q ^ 6 - (Q - 1) ^ 6 := by
  have h := adjacent_sixth_power_add_le hQ
  omega

/-- The three higher terms are bounded uniformly, without a real root. -/
theorem centeredSevenSextic_extra_le_fiftySeven {D Q : ℕ} (hDQ : D ≤ Q) :
    35 * D ^ 2 * (Q - 1) ^ 4 + 21 * D ^ 4 * (Q - 1) ^ 2 + D ^ 6 ≤
      57 * D ^ 2 * Q ^ 4 := by
  have hD2Q2 := Nat.pow_le_pow_left hDQ 2
  have hsmall : Q - 1 ≤ Q := Nat.sub_le Q 1
  have hfirst := Nat.mul_le_mul_left (35 * D ^ 2) (Nat.pow_le_pow_left hsmall 4)
  have hsecond : D ^ 4 * (Q - 1) ^ 2 ≤ D ^ 2 * Q ^ 4 := by
    calc
      _ ≤ D ^ 4 * Q ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsmall 2)
      _ = D ^ 2 * (D ^ 2 * Q ^ 2) := by ring
      _ ≤ D ^ 2 * (Q ^ 2 * Q ^ 2) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hD2Q2)
      _ = _ := by ring
  have hthird : D ^ 6 ≤ D ^ 2 * Q ^ 4 := by
    calc
      _ = D ^ 2 * (D ^ 2) ^ 2 := by ring
      _ ≤ D ^ 2 * (Q ^ 2) ^ 2 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hD2Q2 2)
      _ = _ := by ring
  have hsecond' := Nat.mul_le_mul_left 21 hsecond
  nlinarith

/-- A symbolic adjacent-power bracket excludes the entire integer image
near the pure sixth-power target, when the gap is small enough. -/
theorem centeredSevenSextic_adjacent_sixth_bracket {D Q : ℕ} (hD : 0 < D)
    (hscale : 9 * D ^ 2 ≤ Q) :
    centeredSevenSextic D (Q - 1) < 7 * Q ^ 6 ∧
      7 * Q ^ 6 < centeredSevenSextic D Q := by
  have hD2 : 0 < D ^ 2 := pow_pos hD 2
  have hQ : 0 < Q := by omega
  have hDle : D ≤ D ^ 2 := by
    have h := Nat.mul_le_mul_left D (show 1 ≤ D by omega)
    simpa only [mul_one, ← pow_two] using h
  have hD2Q : D ^ 2 ≤ Q := by omega
  have hextra := centeredSevenSextic_extra_le_fiftySeven (hDle.trans hD2Q)
  have hstep := Nat.mul_le_mul_left 7 (adjacent_sixth_power_add_le hQ)
  have hmargin : 57 * D ^ 2 * Q ^ 4 < 7 * Q ^ 5 := by
    calc
      _ < 63 * D ^ 2 * Q ^ 4 := Nat.mul_lt_mul_of_pos_right
        (Nat.mul_lt_mul_of_pos_right (by decide : 57 < 63) hD2) (pow_pos hQ 4)
      _ = 7 * (9 * D ^ 2) * Q ^ 4 := by ring
      _ ≤ 7 * Q * Q ^ 4 := by gcongr
      _ = _ := by ring
  have hD6 : 0 < D ^ 6 := pow_pos hD 6
  constructor
  · unfold centeredSevenSextic
    rw [mul_add] at hstep
    omega
  · unfold centeredSevenSextic
    omega

/-- A monotone integer polynomial cannot meet a target strictly between
two adjacent evaluations. This is a certificate, not an automatic bracket. -/
theorem centeredSevenSextic_no_image_of_adjacent_bracket {D k target : ℕ}
    (hlow : centeredSevenSextic D k < target)
    (hupp : target < centeredSevenSextic D (k + 1)) :
    ¬ ∃ q : ℕ, centeredSevenSextic D q = target := by
  rintro ⟨q, hq⟩
  rcases le_or_gt q k with h | h
  · exact (ne_of_lt (lt_of_le_of_lt ((centeredSevenSextic_strictMono D).monotone h) hlow)) hq
  · exact (ne_of_lt (lt_of_lt_of_le hupp
      ((centeredSevenSextic_strictMono D).monotone (Nat.succ_le_iff.mpr h)))) hq.symm

theorem centeredSevenSextic_perfectSixth_target (t : ℕ) :
    448 * (t ^ 6) ^ 49 = 7 * (2 * t ^ 49) ^ 6 := by
  simp only [mul_pow, ← pow_mul]
  ring

theorem centeredSevenSextic_perfectSixth_bracket {D t : ℕ} (hD : 0 < D) (ht : 0 < t)
    (hscale : 9 * D ^ 2 ≤ 2 * t ^ 49) :
    centeredSevenSextic D (2 * t ^ 49 - 1) < 448 * (t ^ 6) ^ 49 ∧
      448 * (t ^ 6) ^ 49 < centeredSevenSextic D (2 * t ^ 49) := by
  have hQ : 0 < 2 * t ^ 49 := Nat.mul_pos (by decide) (pow_pos ht 49)
  rw [centeredSevenSextic_perfectSixth_target]
  exact centeredSevenSextic_adjacent_sixth_bracket hD hscale

theorem centeredSevenSextic_perfectSixth_no_image {D t : ℕ} (hD : 0 < D) (ht : 0 < t)
    (hscale : 9 * D ^ 2 ≤ 2 * t ^ 49) :
    ¬ ∃ q : ℕ, centeredSevenSextic D q = 448 * (t ^ 6) ^ 49 := by
  have hQ : 0 < 2 * t ^ 49 := Nat.mul_pos (by decide) (pow_pos ht 49)
  have hbracket := centeredSevenSextic_perfectSixth_bracket hD ht hscale
  apply centeredSevenSextic_no_image_of_adjacent_bracket hbracket.1
  simpa only [Nat.sub_add_cancel (show 1 ≤ 2 * t ^ 49 from hQ)] using hbracket.2

/-- The numerical constant needed to specialize the symbolic bracket. -/
theorem nestedCentered_perfectSixth_scale_constant :
    9 * (7 : ℕ) ^ 54 ≤ 2 * 9 ^ 49 := by decide

theorem nestedCentered_perfectSixth_scale {r t : ℕ} (hsize : 9 * r ^ 2 ≤ t) :
    9 * (7 ^ 27 * r ^ 49) ^ 2 ≤ 2 * t ^ 49 := by
  calc
    _ = (9 * 7 ^ 54) * r ^ 98 := by simp only [mul_pow, ← pow_mul]; ring
    _ ≤ (2 * 9 ^ 49) * r ^ 98 :=
      Nat.mul_le_mul_right _ nestedCentered_perfectSixth_scale_constant
    _ = 2 * (9 * r ^ 2) ^ 49 := by simp only [mul_pow, ← pow_mul]; ring
    _ ≤ 2 * t ^ 49 := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hsize 49)

/-- An infinite conditional family of scalar exclusions. Perfect sixth
power and size are extra hypotheses, not consequences of residue support. -/
theorem nestedCentered_perfectSixth_ne {r s t : ℕ} (hr : 0 < r)
    (hsize : 9 * r ^ 2 ≤ t) (hs : s = t ^ 6) (q : ℕ) :
    centeredSevenSextic (7 ^ 27 * r ^ 49) q ≠ 448 * s ^ 49 := by
  have ht : 0 < t := lt_of_lt_of_le (Nat.mul_pos (by decide) (pow_pos hr 2)) hsize
  have hD : 0 < 7 ^ 27 * r ^ 49 := Nat.mul_pos (by positivity) (pow_pos hr 49)
  rw [hs]
  exact fun h => centeredSevenSextic_perfectSixth_no_image hD ht
    (nestedCentered_perfectSixth_scale hsize) ⟨q, h⟩

theorem nestedCenteredAllocation_excluded_of_perfectSixth {M r t : ℕ} (hr : 0 < r)
    (hM : M = r * t ^ 6) (hsize : 9 * r ^ 2 ≤ t) :
    ¬ ∃ q : ℕ, CenteredNestedAllocationCandidate M r q := by
  rintro ⟨q, hq⟩
  have hquot : M / r = t ^ 6 := by rw [hM, Nat.mul_div_cancel_left _ hr]
  apply nestedCentered_perfectSixth_ne hr hsize hquot q
  simpa only [← mul_assoc, show (64 : ℕ) * 7 = 448 by decide] using hq.2.1

theorem nestedAllocation_excluded_of_perfectSixth {M r t : ℕ} (hr : 0 < r)
    (hM : M = r * t ^ 6) (hsize : 9 * r ^ 2 ≤ t) :
    ¬ (NestedGNAllocationCondition M r ∨ NestedRHSAllocationCondition M r) :=
  fun h => nestedCenteredAllocation_excluded_of_perfectSixth hr hM hsize
    ((nestedAllocation_iff_centered M r).mp h)

namespace RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

/-- Fixed source allocation obstruction, conditional on perfect sixth
power and size. It does not assert nonexistence of the original packet. -/
theorem internalDepthFourAllocation_excluded_of_perfectSixth (p : RamifiedSignedRootRoutingPacket)
    {r t : ℕ} (hmem : r ∈ (internalDepthFourSeventhCore p).divisors)
    (hpower : internalDepthFourSeventhCore p / r = t ^ 6) (hsize : 9 * r ^ 2 ≤ t) :
    ¬ (NestedGNAllocationCondition (internalDepthFourSeventhCore p) r ∨
      NestedRHSAllocationCondition (internalDepthFourSeventhCore p) r) := by
  have hdiv := Nat.dvd_of_mem_divisors hmem
  have hr := Nat.pos_of_dvd_of_pos hdiv (internalDepthFourSeventhCore_pos p)
  apply nestedAllocation_excluded_of_perfectSixth hr _ hsize
  rw [← hpower, Nat.mul_div_cancel' hdiv]

/-- A global family premise would obstruct reconstruction. The premise is
not supplied by the source APIs, and the conclusion does not exclude p. -/
theorem internalDepthFourReconstruction_excluded_of_perfectSixth_family
    (p : RamifiedSignedRootRoutingPacket)
    (hfamily : ∀ r : ℕ, r ∈ (internalDepthFourSeventhCore p).divisors →
      Nat.Coprime r (internalDepthFourSeventhCore p / r) →
      7 ^ 3 * r ^ 7 < internalDepthFourSeventhCore p →
      Nat.ModEq 7 (internalDepthFourSeventhCore p / r) 1 →
      SixthPowerAllocationSieve r (internalDepthFourSeventhCore p / r) →
      ∃ t : ℕ, internalDepthFourSeventhCore p / r = t ^ 6 ∧ 9 * r ^ 2 ≤ t) :
    ¬ InternalDepthFourCounterexampleReconstructionObligation p := by
  intro h
  rcases (internalDepthFourReconstruction_iff_centered p).mp h with
    ⟨r, hmem, hcop, hsize, h7, hsixth, q, hq, _⟩
  rcases hfamily r hmem hcop hsize h7 hsixth with ⟨t, hpower, ht⟩
  have hr := Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hmem)
    (internalDepthFourSeventhCore_pos p)
  apply nestedCentered_perfectSixth_ne hr ht hpower q
  simpa only [← mul_assoc, show (64 : ℕ) * 7 = 448 by decide] using hq.2.1

end RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

end DkMath.FLT.Seven
