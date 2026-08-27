/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameSpectralGaugeClosureDecision
import Mathlib.Tactic

namespace DkMathTest.RH

open DkMath.RH.CFBRCProjection

example {s z : ℂ} (him : s.im = z.im) (k : ℕ) :
    etaPairBaseRotation s k = etaPairBaseRotation z k := by
  exact etaPairBaseRotation_eq_of_im_eq him k

example {P : ℂ → Prop} (hP : SpectralRealShiftInvariant P) :
    ¬ ∀ s : ℂ, P s ↔ s.re = (1 : ℝ) / 2 := by
  exact not_characterizes_criticalLine_of_realShiftInvariant hP

example {k : ℕ} {P : ℂ → Prop}
    (hP : EtaPairBaseRotationDetermined k P) :
    ¬ ∀ s : ℂ, P s ↔ s.re = (1 : ℝ) / 2 := by
  exact
    not_characterizes_criticalLine_of_etaPairBaseRotationDetermined hP

example (k : ℕ) :
    ¬ ∃ Q : ℂ → Prop,
      ∀ s : ℂ,
        Q (etaPairBaseRotation s k) ↔
          s.re = (1 : ℝ) / 2 := by
  exact
    not_exists_etaPairBaseRotation_predicate_characterizing_criticalLine k

example {k : ℕ} {P : ℂ → Prop}
    (hP : EtaPairBaseRotationDetermined k P) :
    EtaPairSpectralGaugeClosureDecisionCertificate k P := by
  exact etaPairSpectralGaugeClosureDecisionCertificate_of_determined hP

end DkMathTest.RH
