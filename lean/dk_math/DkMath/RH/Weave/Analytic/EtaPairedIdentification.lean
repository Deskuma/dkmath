/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.Weave.Analytic.EtaPairedSummability
import Mathlib.Tactic

#print "file: DkMath.RH.Weave.Analytic.EtaPairedIdentification"

noncomputable section

namespace DkMath.RH.Weave.Analytic

open Filter
open scoped Topology

/--
On the absolute-convergence half-plane, the paired eta infinite sum is exactly
the analytically continued eta value.

This is the anchor identity for the later continuation step: both values are
limits of the same genuine finite eta endpoint sequence, so uniqueness of
limits identifies them without rearranging an infinite series.
-/
theorem etaPairedTsumIdentifiesAnalyticAt_of_one_lt_re
    {s : ℂ} (hs : 1 < s.re) :
    EtaPairedTsumIdentifiesAnalyticAt s := by
  unfold EtaPairedTsumIdentifiesAnalyticAt
  have hpaired :=
    etaPartialEndpoint_tendsto_pairedTsum_of_pos_re
      (by linarith : 0 < s.re)
  have hanalytic := etaPartialConvergesAt_of_one_lt_re_unconditional hs
  unfold EtaPartialConvergesAt at hanalytic
  exact tendsto_nhds_unique hpaired hanalytic

end DkMath.RH.Weave.Analytic
