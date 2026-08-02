/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CriticalMirrorGeometry
import DkMath.RH.CFBRC.EtaMirrorUnitSplit
import DkMath.RH.Weave.Analytic.EtaLimitBridge
import DkMath.RH.Weave.Finite.PairEnergy
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaMirrorEndpointPairEnergy"

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology
open DkMath.RH.Weave.Finite
open DkMath.RH.Weave.Analytic

/-!
# Finite original/mirror endpoint pair energy

This file pairs the finite eta endpoint at `s` with the endpoint at the critical
mirror of `s`.  The resulting Big/Gap identity is an exact finite algebraic
statement.

The limit audit is equally important: if both endpoint sequences tend to zero,
then both endpoint Big and endpoint Gap tend to zero automatically, with no
critical-line conclusion.  Hence this endpoint Gap must not be confused with
the term-amplitude `etaMirrorUnitGap`, whose zero locus is the critical line.
-/

/-- Symmetric center of the original and critical-mirror finite eta endpoints. -/
noncomputable def etaMirrorEndpointCenter (N : ℕ) (s : ℂ) : ℂ :=
  pairCenter (etaPartialEndpoint N s)
    (etaPartialEndpoint N (criticalMirror s))

/-- Antisymmetric offset of the original and mirror finite eta endpoints. -/
noncomputable def etaMirrorEndpointOffset (N : ℕ) (s : ℂ) : ℂ :=
  pairOffset (etaPartialEndpoint N s)
    (etaPartialEndpoint N (criticalMirror s))

/-- Sum of the squared norms of the two finite endpoints. -/
noncomputable def etaMirrorEndpointTotalEnergy (N : ℕ) (s : ℂ) : ℝ :=
  Complex.normSq (etaPartialEndpoint N s) +
    Complex.normSq (etaPartialEndpoint N (criticalMirror s))

/-- Squared norm of the symmetric endpoint sum. -/
noncomputable def etaMirrorEndpointBig (N : ℕ) (s : ℂ) : ℝ :=
  Complex.normSq
    (etaPartialEndpoint N s + etaPartialEndpoint N (criticalMirror s))

/-- Squared norm of the antisymmetric endpoint difference. -/
noncomputable def etaMirrorEndpointGap (N : ℕ) (s : ℂ) : ℝ :=
  Complex.normSq
    (etaPartialEndpoint N s - etaPartialEndpoint N (criticalMirror s))

/-- The original endpoint is reconstructed from center plus offset. -/
theorem etaMirrorEndpointCenter_add_offset (N : ℕ) (s : ℂ) :
    etaMirrorEndpointCenter N s + etaMirrorEndpointOffset N s =
      etaPartialEndpoint N s := by
  exact pairCenter_add_pairOffset
    (etaPartialEndpoint N s)
    (etaPartialEndpoint N (criticalMirror s))

/-- The mirror endpoint is reconstructed from center minus offset. -/
theorem etaMirrorEndpointCenter_sub_offset (N : ℕ) (s : ℂ) :
    etaMirrorEndpointCenter N s - etaMirrorEndpointOffset N s =
      etaPartialEndpoint N (criticalMirror s) := by
  exact pairCenter_sub_pairOffset
    (etaPartialEndpoint N s)
    (etaPartialEndpoint N (criticalMirror s))

/-- Exact finite center/offset energy decomposition. -/
theorem etaMirrorEndpointTotalEnergy_decomposition (N : ℕ) (s : ℂ) :
    etaMirrorEndpointTotalEnergy N s =
      2 * Complex.normSq (etaMirrorEndpointCenter N s) +
        2 * Complex.normSq (etaMirrorEndpointOffset N s) := by
  unfold etaMirrorEndpointTotalEnergy etaMirrorEndpointCenter
    etaMirrorEndpointOffset
  exact normSq_pair_decomposition
    (etaPartialEndpoint N s)
    (etaPartialEndpoint N (criticalMirror s))

/--
Endpoint parallelogram identity: endpoint Big plus endpoint Gap is twice the
total endpoint energy.
-/
theorem etaMirrorEndpointBig_add_gap_eq_two_mul_totalEnergy
    (N : ℕ) (s : ℂ) :
    etaMirrorEndpointBig N s + etaMirrorEndpointGap N s =
      2 * etaMirrorEndpointTotalEnergy N s := by
  simp [etaMirrorEndpointBig, etaMirrorEndpointGap,
    etaMirrorEndpointTotalEnergy, Complex.normSq_apply]
  ring

/-- Both endpoint limits zero force the symmetric endpoint Big to vanish. -/
theorem etaMirrorEndpointBig_tendsto_zero_of_endpoint_limits
    {s : ℂ}
    (horiginal :
      Tendsto (fun N : ℕ => etaPartialEndpoint N s) atTop (nhds 0))
    (hmirror :
      Tendsto (fun N : ℕ => etaPartialEndpoint N (criticalMirror s))
        atTop (nhds 0)) :
    Tendsto (fun N : ℕ => etaMirrorEndpointBig N s) atTop (nhds 0) := by
  have hsum :
      Tendsto
        (fun N : ℕ =>
          etaPartialEndpoint N s + etaPartialEndpoint N (criticalMirror s))
        atTop (nhds 0) := by
    simpa using horiginal.add hmirror
  have hnorm := Complex.continuous_normSq.continuousAt.tendsto.comp hsum
  simpa [etaMirrorEndpointBig] using hnorm

/-- Both endpoint limits zero force the antisymmetric endpoint Gap to vanish. -/
theorem etaMirrorEndpointGap_tendsto_zero_of_endpoint_limits
    {s : ℂ}
    (horiginal :
      Tendsto (fun N : ℕ => etaPartialEndpoint N s) atTop (nhds 0))
    (hmirror :
      Tendsto (fun N : ℕ => etaPartialEndpoint N (criticalMirror s))
        atTop (nhds 0)) :
    Tendsto (fun N : ℕ => etaMirrorEndpointGap N s) atTop (nhds 0) := by
  have hdiff :
      Tendsto
        (fun N : ℕ =>
          etaPartialEndpoint N s - etaPartialEndpoint N (criticalMirror s))
        atTop (nhds 0) := by
    simpa using horiginal.sub hmirror
  have hnorm := Complex.continuous_normSq.continuousAt.tendsto.comp hdiff
  simpa [etaMirrorEndpointGap] using hnorm

/-- Both endpoint limits zero force their total squared norm to vanish. -/
theorem etaMirrorEndpointTotalEnergy_tendsto_zero_of_endpoint_limits
    {s : ℂ}
    (horiginal :
      Tendsto (fun N : ℕ => etaPartialEndpoint N s) atTop (nhds 0))
    (hmirror :
      Tendsto (fun N : ℕ => etaPartialEndpoint N (criticalMirror s))
        atTop (nhds 0)) :
    Tendsto (fun N : ℕ => etaMirrorEndpointTotalEnergy N s)
      atTop (nhds 0) := by
  have horiginalNorm :=
    Complex.continuous_normSq.continuousAt.tendsto.comp horiginal
  have hmirrorNorm :=
    Complex.continuous_normSq.continuousAt.tendsto.comp hmirror
  simpa [etaMirrorEndpointTotalEnergy] using horiginalNorm.add hmirrorNorm

/--
Two zeta zeros, together with eta convergence at the original and mirror
coordinates, make all finite endpoint pair energies tend to zero.
-/
theorem etaMirrorEndpoint_pairEnergy_limits_of_riemannZeta_pair
    {s : ℂ}
    (horiginalConv : EtaPartialConvergesAt s)
    (hmirrorConv : EtaPartialConvergesAt (criticalMirror s))
    (horiginalZero : riemannZeta s = 0)
    (hmirrorZero : riemannZeta (criticalMirror s) = 0) :
    Tendsto (fun N : ℕ => etaMirrorEndpointTotalEnergy N s)
        atTop (nhds 0) ∧
      Tendsto (fun N : ℕ => etaMirrorEndpointBig N s)
        atTop (nhds 0) ∧
      Tendsto (fun N : ℕ => etaMirrorEndpointGap N s)
        atTop (nhds 0) := by
  have horiginal :=
    etaPartialEndpoint_tendsto_zero_of_riemannZeta_eq_zero
      horiginalConv horiginalZero
  have hmirror :=
    etaPartialEndpoint_tendsto_zero_of_riemannZeta_eq_zero
      hmirrorConv hmirrorZero
  exact
    ⟨etaMirrorEndpointTotalEnergy_tendsto_zero_of_endpoint_limits
        horiginal hmirror,
      etaMirrorEndpointBig_tendsto_zero_of_endpoint_limits horiginal hmirror,
      etaMirrorEndpointGap_tendsto_zero_of_endpoint_limits horiginal hmirror⟩

/--
Candidate coupling from endpoint Gap collapse to the term-amplitude UnitGap.
This is deliberately isolated because the finite parallelogram identity does
not supply it.
-/
def EtaMirrorEndpointGapControlsUnitGapAt (s : ℂ) : Prop :=
  Tendsto (fun N : ℕ => etaMirrorEndpointGap N s) atTop (nhds 0) →
    etaMirrorUnitGap s 1 = 0

/--
Once both endpoint sequences already tend to zero, controlling the term UnitGap
from endpoint Gap is exactly the critical-line condition.
-/
theorem etaMirrorEndpointGapControlsUnitGapAt_iff_re_eq_half
    {s : ℂ}
    (horiginal :
      Tendsto (fun N : ℕ => etaPartialEndpoint N s) atTop (nhds 0))
    (hmirror :
      Tendsto (fun N : ℕ => etaPartialEndpoint N (criticalMirror s))
        atTop (nhds 0)) :
    EtaMirrorEndpointGapControlsUnitGapAt s ↔
      s.re = (1 : ℝ) / 2 := by
  constructor
  · intro hcontrol
    apply (etaMirrorUnitGap_one_eq_zero_iff_re_eq_half s).mp
    exact hcontrol
      (etaMirrorEndpointGap_tendsto_zero_of_endpoint_limits
        horiginal hmirror)
  · intro hre _
    exact (etaMirrorUnitGap_one_eq_zero_iff_re_eq_half s).2 hre

end DkMath.RH.CFBRCProjection
