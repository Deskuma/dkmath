/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorEndpointLimits
import DkMath.RH.CFBRC.EtaMirrorAmplitudeDecoder
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorWeightedTransport"

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/--
Exact complex weight transporting one eta term from `s` to its critical
mirror.  The exponent is real, so this weight changes magnitude without
rotating the term.
-/
noncomputable def etaCriticalMirrorTermWeight (s : ℂ) (m : ℕ) : ℂ :=
  (((m + 1 : ℕ) : ℂ) ^ (((2 * centeredSigma s.re : ℝ) : ℂ)))

/-- The transport exponent is exactly the difference of the two eta exponents. -/
theorem neg_criticalMirror_eq_transportExponent_add_neg
    (s : ℂ) :
    -criticalMirror s =
      ((2 * centeredSigma s.re : ℝ) : ℂ) + (-s) := by
  apply Complex.ext
  · simp [criticalMirror, centeredSigma]
    ring
  · simp [criticalMirror]

/--
Each eta term at the critical mirror is the original eta term multiplied by
one real-exponent transport weight.
-/
theorem etaUnsignedVector_criticalMirror_eq_weight_mul
    (s : ℂ) (m : ℕ) :
    etaUnsignedVector (criticalMirror s) m =
      etaCriticalMirrorTermWeight s m * etaUnsignedVector s m := by
  have hbase : (((m + 1 : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero m
  unfold etaUnsignedVector etaCriticalMirrorTermWeight
  rw [neg_criticalMirror_eq_transportExponent_add_neg]
  exact Complex.cpow_add _ _ hbase

/-- Alternating signs are preserved by the same transport weight. -/
theorem etaSignedVector_criticalMirror_eq_weight_mul
    (s : ℂ) (m : ℕ) :
    etaSignedVector (criticalMirror s) m =
      etaCriticalMirrorTermWeight s m * etaSignedVector s m := by
  by_cases hm : Even m
  · simp [etaSignedVector, hm,
      etaUnsignedVector_criticalMirror_eq_weight_mul]
  · simp [etaSignedVector, hm,
      etaUnsignedVector_criticalMirror_eq_weight_mul]

/-- The magnitude of the exact complex weight is the known real mirror ratio. -/
theorem norm_etaCriticalMirrorTermWeight
    (s : ℂ) (m : ℕ) :
    ‖etaCriticalMirrorTermWeight s m‖ =
      (((m + 1 : ℕ) : ℝ) ^ (2 * centeredSigma s.re)) := by
  unfold etaCriticalMirrorTermWeight
  rw [← Complex.ofReal_natCast]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos]
  · simp
  · exact_mod_cast Nat.succ_pos m

/-- The exact term weight has the same magnitude as the mirror-amplitude ratio. -/
theorem norm_etaCriticalMirrorTermWeight_eq_etaMirrorAmplitudeRatio
    (s : ℂ) (m : ℕ) :
    ‖etaCriticalMirrorTermWeight s m‖ = etaMirrorAmplitudeRatio s m := by
  rw [norm_etaCriticalMirrorTermWeight,
    etaMirrorAmplitudeRatio_eq_rpow]

/-- Finite eta endpoint obtained by transporting every original term. -/
noncomputable def etaCriticalMirrorWeightedEndpoint
    (N : ℕ) (s : ℂ) : ℂ :=
  (Finset.range N).sum fun m =>
    etaCriticalMirrorTermWeight s m * etaSignedVector s m

/--
The transported finite endpoint is exactly the ordinary finite endpoint at the
critical mirror.
-/
theorem etaCriticalMirrorWeightedEndpoint_eq_mirrorEndpoint
    (N : ℕ) (s : ℂ) :
    etaCriticalMirrorWeightedEndpoint N s =
      etaPartialEndpoint N (criticalMirror s) := by
  unfold etaCriticalMirrorWeightedEndpoint etaPartialEndpoint finiteEndpoint
  apply Finset.sum_congr rfl
  intro m hm
  exact (etaSignedVector_criticalMirror_eq_weight_mul s m).symm

/-- Difference between the transported and original finite endpoints. -/
noncomputable def etaCriticalMirrorTransportDefectEndpoint
    (N : ℕ) (s : ℂ) : ℂ :=
  etaCriticalMirrorWeightedEndpoint N s - etaPartialEndpoint N s

/-- The transport defect is the finite weighted moment with coefficient `weight - 1`. -/
theorem etaCriticalMirrorTransportDefectEndpoint_eq_sum
    (N : ℕ) (s : ℂ) :
    etaCriticalMirrorTransportDefectEndpoint N s =
      (Finset.range N).sum fun m =>
        (etaCriticalMirrorTermWeight s m - 1) * etaSignedVector s m := by
  unfold etaCriticalMirrorTransportDefectEndpoint
  unfold etaCriticalMirrorWeightedEndpoint etaPartialEndpoint finiteEndpoint
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  ring

/-- On the critical line every transport weight is exactly one. -/
theorem etaCriticalMirrorTermWeight_eq_one_of_re_eq_half
    {s : ℂ} (hre : s.re = (1 : ℝ) / 2) (m : ℕ) :
    etaCriticalMirrorTermWeight s m = 1 := by
  have hcenter : centeredSigma s.re = 0 :=
    (centeredSigma_eq_zero_iff s.re).2 hre
  simp [etaCriticalMirrorTermWeight, hcenter]

/-- On the critical line transported and original finite endpoints agree termwise. -/
theorem etaCriticalMirrorWeightedEndpoint_eq_original_of_re_eq_half
    {s : ℂ} (hre : s.re = (1 : ℝ) / 2) (N : ℕ) :
    etaCriticalMirrorWeightedEndpoint N s = etaPartialEndpoint N s := by
  unfold etaCriticalMirrorWeightedEndpoint etaPartialEndpoint finiteEndpoint
  apply Finset.sum_congr rfl
  intro m hm
  rw [etaCriticalMirrorTermWeight_eq_one_of_re_eq_half hre]
  simp

/--
At a nonreal nontrivial zeta zero, the transported original eta endpoint also
tends to zero.  This is the finite weighted cancellation supplied by the
completed-zeta reflection, not by the Riemann hypothesis.
-/
theorem etaCriticalMirrorWeightedEndpoint_tendsto_zero_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    Tendsto (fun N : ℕ => etaCriticalMirrorWeightedEndpoint N s)
      atTop (nhds 0) := by
  simpa [etaCriticalMirrorWeightedEndpoint_eq_mirrorEndpoint] using
    etaPartialEndpoint_criticalMirror_tendsto_zero_of_nontrivialRiemannZetaZero
      hs him

/--
The weighted-minus-unweighted transport defect tends to zero at every nonreal
nontrivial zeta zero.
-/
theorem etaCriticalMirrorTransportDefectEndpoint_tendsto_zero_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    Tendsto (fun N : ℕ => etaCriticalMirrorTransportDefectEndpoint N s)
      atTop (nhds 0) := by
  simpa [etaCriticalMirrorTransportDefectEndpoint] using
    (etaCriticalMirrorWeightedEndpoint_tendsto_zero_of_nontrivialRiemannZetaZero
      hs him).sub
      (etaPartialEndpoint_tendsto_zero_of_nontrivialRiemannZetaZero hs him)

/-- Original and transported eta cancellations packaged as one certificate. -/
structure EtaCriticalMirrorDoubleVanishing (s : ℂ) : Prop where
  original : Tendsto (fun N : ℕ => etaPartialEndpoint N s) atTop (nhds 0)
  transported :
    Tendsto (fun N : ℕ => etaCriticalMirrorWeightedEndpoint N s)
      atTop (nhds 0)
  defect :
    Tendsto (fun N : ℕ => etaCriticalMirrorTransportDefectEndpoint N s)
      atTop (nhds 0)

/-- Build the double-vanishing certificate from a nonreal nontrivial zero. -/
theorem etaCriticalMirrorDoubleVanishing_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    EtaCriticalMirrorDoubleVanishing s where
  original := etaPartialEndpoint_tendsto_zero_of_nontrivialRiemannZetaZero hs him
  transported :=
    etaCriticalMirrorWeightedEndpoint_tendsto_zero_of_nontrivialRiemannZetaZero
      hs him
  defect :=
    etaCriticalMirrorTransportDefectEndpoint_tendsto_zero_of_nontrivialRiemannZetaZero
      hs him

end DkMath.RH.CFBRCProjection
