/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib
import DkMath.Basic  -- Basic Definitions and Utilities
import DkMath.RH.Basic
import DkMath.RH.Defs
import DkMath.RH.Lemmas
import DkMath.RH.Theorems
import DkMath.RH.EulerZeta
import DkMath.RH.EulerZetaLemmas
import DkMath.RH.HopcInfiniteLift
import DkMath.RH.CFBRCBridge
import DkMath.RH.CFBRC.OffCriticalExclusion
import DkMath.RH.CFBRC.OffCriticalExclusionGeneral
import DkMath.RH.CFBRC.MirrorThreatModel
import DkMath.RH.CFBRC.MirrorRootOfUnity
import DkMath.RH.CFBRC.MirrorAngleBranch
import DkMath.RH.CFBRC.MirrorIndexedRoot
import DkMath.RH.CFBRC.FiniteClosure
import DkMath.RH.CFBRC.FiniteClosurePermutation
import DkMath.RH.CFBRC.FiniteMassNormalization
import DkMath.RH.CFBRC.FiniteCenteredBridge
import DkMath.RH.CFBRC.EtaFiniteClosure
import DkMath.RH.CFBRC.StandardZetaBridge
import DkMath.RH.CFBRC.ZeroLocusFactorBridge
import DkMath.RH.CFBRC.CompletedZetaBridge
import DkMath.RH.CFBRC.CriticalMirrorGeometry
import DkMath.RH.Weave.Control.IndexShiftAudit
import DkMath.RH.Weave.Finite.PairEnergy
import DkMath.RH.EulerZetaConvergence

#print "file: DkMath.RH"

-- ============================================================================

namespace DkMath.RH

open DkMath.Basic
open DkMath.RH.Basic

#eval printValue ident
#eval printValue name

open CFBRCProjection

theorem standardZeta_map_zero_iff_riemannHypothesis
    {d : ℕ} (hd : 0 < d) (phase : ℂ → ℝ) :
    (∀ {s : ℂ}, NontrivialRiemannZetaZero s →
      offCriticalCFBRC d s.re (phase s) = 0) ↔
      RiemannHypothesis := by
  constructor
  · intro h
    exact riemannHypothesis_of_standardZeta_map_zero hd phase h
  · intro hRH s hs
    apply
      (offCriticalCFBRC_eq_zero_iff_re_eq_half
        hd s.re (phase s)).2
    exact
      (riemannHypothesis_iff_nontrivialZero_re_eq_half.mp hRH)
        s hs

end DkMath.RH

-- ============================================================================

namespace DkMath.RH.EulerZeta
-- #print axioms eulerZetaMag_multipliable_sigma_gt_one
-- #print axioms eulerZetaMag_pos_sigma_gt_one
end DkMath.RH.EulerZeta

-- ============================================================================
