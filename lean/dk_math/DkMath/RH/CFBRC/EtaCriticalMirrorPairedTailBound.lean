/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedTail
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedTailBound"

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Set MeasureTheory
open DkMath.RH.Weave.Analytic

/--
Explicit integral-test bound for a shifted real p-series tail.

For `sigma > 0` and `K >= 1`, the tail beginning at `K + 1` is bounded by
`K^(-sigma) / sigma`.
-/
theorem shifted_rpow_tail_le
    {σ : ℝ} (hσ : 0 < σ) {K : ℕ} (hK : 1 ≤ K) :
    (∑' j : ℕ,
      (((j + K + 1 : ℕ) : ℝ) ^ (-σ - 1))) ≤
      ((K : ℝ) ^ (-σ)) / σ := by
  have hKposNat : 0 < K := by omega
  have hKpos : 0 < (K : ℝ) := by exact_mod_cast hKposNat
  have hExpLt : -σ - 1 < -1 := by linarith
  have hExpNonpos : -σ - 1 ≤ 0 := by linarith
  have hendpoint :
      (((K + 1 : ℕ) : ℝ) - 1) = (K : ℝ) := by
    norm_num [Nat.cast_add]
  have hanti :
      AntitoneOn
        (fun x : ℝ => x ^ (-σ - 1))
        (Ici (((K + 1 : ℕ) : ℝ) - 1)) := by
    rw [hendpoint]
    intro x hx y hy hxy
    exact
      Real.antitoneOn_rpow_Ioi_of_exponent_nonpos hExpNonpos
        (hKpos.trans_le hx) (hKpos.trans_le hy) hxy
  have hint :
      IntegrableOn
        (fun x : ℝ => x ^ (-σ - 1))
        (Ioi (((K + 1 : ℕ) : ℝ) - 1)) := by
    rw [hendpoint]
    exact integrableOn_Ioi_rpow_of_lt hExpLt hKpos
  have hnonneg :
      ∀ x ∈ Ioi (((K + 1 : ℕ) : ℝ) - 1),
        0 ≤ x ^ (-σ - 1) := by
    intro x hx
    rw [hendpoint] at hx
    exact Real.rpow_nonneg (hKpos.trans hx).le _
  have herror :=
    hanti.abs_tsum_sub_sum_range_le_integral
      (N := K + 1) (by omega) hint hnonneg
  have hp : 1 < σ + 1 := by linarith
  have hsumBase :
      Summable (fun n : ℕ => (n : ℝ) ^ (-(σ + 1))) := by
    simpa only [one_div, Real.rpow_neg (Nat.cast_nonneg _)] using
      (Real.summable_one_div_nat_rpow.2 hp)
  have hsum :
      Summable (fun n : ℕ => (n : ℝ) ^ (-σ - 1)) := by
    simpa [show -σ - 1 = -(σ + 1) by ring] using hsumBase
  have hsplit := hsum.sum_add_tsum_nat_add (K + 1)
  have htailEq :
      (∑' j : ℕ,
        (((j + (K + 1) : ℕ) : ℝ) ^ (-σ - 1))) =
        (∑' n : ℕ, ((n : ℝ) ^ (-σ - 1))) -
          ∑ n ∈ Finset.range (K + 1),
            ((n : ℝ) ^ (-σ - 1)) := by
    linear_combination hsplit
  have htailNonneg :
      0 ≤
        (∑' j : ℕ,
          (((j + (K + 1) : ℕ) : ℝ) ^ (-σ - 1))) :=
    tsum_nonneg fun j => Real.rpow_nonneg (by positivity) _
  rw [← htailEq, abs_of_nonneg htailNonneg] at herror
  have hintegral :
      (∫ x : ℝ in Ioi (((K + 1 : ℕ) : ℝ) - 1),
        x ^ (-σ - 1)) =
        ((K : ℝ) ^ (-σ)) / σ := by
    rw [hendpoint]
    rw [integral_Ioi_rpow_of_lt hExpLt hKpos]
    rw [show -σ - 1 + 1 = -σ by ring]
    field_simp [ne_of_gt hσ]
  rw [hintegral] at herror
  simpa [Nat.add_assoc] using herror

/-- Real summable majorant for one paired critical-mirror defect. -/
noncomputable def etaCriticalMirrorDefectPairMajorant
    (s : ℂ) (k : ℕ) : ℝ :=
  ‖criticalMirror s‖ *
      (((k + 1 : ℕ) : ℝ) ^ (-(criticalMirror s).re - 1)) +
    ‖s‖ * (((k + 1 : ℕ) : ℝ) ^ (-s.re - 1))

/-- The paired defect norm is bounded by the sum of the two eta-pair majorants. -/
theorem norm_etaCriticalMirrorDefectPairTerm_le_majorant
    {s : ℂ} (hs : 0 < s.re) (hm : 0 < (criticalMirror s).re)
    (k : ℕ) :
    ‖etaCriticalMirrorDefectPairTerm s k‖ ≤
      etaCriticalMirrorDefectPairMajorant s k := by
  rw [etaCriticalMirrorDefectPairTerm_eq_etaPairTerm_sub]
  calc
    ‖etaPairTerm (criticalMirror s) k - etaPairTerm s k‖ ≤
        ‖etaPairTerm (criticalMirror s) k‖ + ‖etaPairTerm s k‖ :=
      norm_sub_le _ _
    _ ≤ etaCriticalMirrorDefectPairMajorant s k := by
      unfold etaCriticalMirrorDefectPairMajorant
      exact add_le_add
        (norm_etaPairTerm_le_summableMajorant hm k)
        (norm_etaPairTerm_le_summableMajorant hs k)

/-- The paired defect majorant is summable in the open mirror strip. -/
theorem summable_etaCriticalMirrorDefectPairMajorant
    {s : ℂ} (hs : 0 < s.re) (hm : 0 < (criticalMirror s).re) :
    Summable (etaCriticalMirrorDefectPairMajorant s) := by
  unfold etaCriticalMirrorDefectPairMajorant
  exact (summable_etaPairMajorant hm).add (summable_etaPairMajorant hs)

/--
Explicit power bound for the paired critical-mirror defect tail.

The two exponents are the distances from the left and right boundaries of the
critical strip.  Both are positive at every nontrivial zeta zero.
-/
theorem norm_etaCriticalMirrorDefectPairTail_le
    {s : ℂ} (hs : 0 < s.re) (hm : 0 < (criticalMirror s).re)
    {K : ℕ} (hK : 1 ≤ K) :
    ‖etaCriticalMirrorDefectPairTail K s‖ ≤
      ‖criticalMirror s‖ *
          (((K : ℝ) ^ (-(criticalMirror s).re)) /
            (criticalMirror s).re) +
        ‖s‖ * (((K : ℝ) ^ (-s.re)) / s.re) := by
  have hMajorant :=
    summable_etaCriticalMirrorDefectPairMajorant hs hm
  have hMajorantShift :
      Summable
        (fun j : ℕ =>
          etaCriticalMirrorDefectPairMajorant s (j + K)) :=
    (summable_nat_add_iff K).2 hMajorant
  have hnorm :
      ‖etaCriticalMirrorDefectPairTail K s‖ ≤
        ∑' j : ℕ,
          etaCriticalMirrorDefectPairMajorant s (j + K) := by
    unfold etaCriticalMirrorDefectPairTail
    exact
      tsum_of_norm_bounded hMajorantShift.hasSum
        (fun j =>
          norm_etaCriticalMirrorDefectPairTerm_le_majorant
            hs hm (j + K))
  have hMirrorTail := shifted_rpow_tail_le hm hK
  have hOriginalTail := shifted_rpow_tail_le hs hK
  have hMirrorSummable :
      Summable
        (fun j : ℕ =>
          (((j + K + 1 : ℕ) : ℝ) ^
            (-(criticalMirror s).re - 1))) := by
    have h := summable_etaPairMajorant hm
    by_cases hzero : ‖criticalMirror s‖ = 0
    · have : criticalMirror s = 0 := norm_eq_zero.mp hzero
      simp [this] at hm
    · exact
        (summable_mul_left_iff hzero).1
          (by simpa [Nat.add_assoc] using
            (summable_nat_add_iff K).2 h)
  have hOriginalSummable :
      Summable
        (fun j : ℕ =>
          (((j + K + 1 : ℕ) : ℝ) ^ (-s.re - 1))) := by
    have h := summable_etaPairMajorant hs
    have hzero : ‖s‖ ≠ 0 := by
      exact norm_ne_zero_iff.mpr (by
        intro hs0
        simp [hs0] at hs)
    exact
      (summable_mul_left_iff hzero).1
        (by simpa [Nat.add_assoc] using
          (summable_nat_add_iff K).2 h)
  have hmajorantTsum :
      (∑' j : ℕ,
        etaCriticalMirrorDefectPairMajorant s (j + K)) =
        ‖criticalMirror s‖ *
            (∑' j : ℕ,
              (((j + K + 1 : ℕ) : ℝ) ^
                (-(criticalMirror s).re - 1))) +
          ‖s‖ *
            (∑' j : ℕ,
              (((j + K + 1 : ℕ) : ℝ) ^ (-s.re - 1))) := by
    unfold etaCriticalMirrorDefectPairMajorant
    rw [tsum_add]
    · rw [tsum_mul_left, tsum_mul_left]
    · exact hMirrorSummable.mul_left _
    · exact hOriginalSummable.mul_left _
  rw [hmajorantTsum] at hnorm
  exact hnorm.trans <|
    add_le_add
      (mul_le_mul_of_nonneg_left hMirrorTail (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hOriginalTail (norm_nonneg _))

end DkMath.RH.CFBRCProjection
