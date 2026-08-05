/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameSpectralGaugeDirectionAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameSpectralGaugeClosureDecision"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

/-- Pair-left base rotations depend only on the imaginary spectral coordinate. -/
theorem etaPairBaseRotation_eq_of_im_eq
    {s z : ℂ} (him : s.im = z.im) (k : ℕ) :
    etaPairBaseRotation s k = etaPairBaseRotation z k := by
  unfold etaPairBaseRotation
  rw [him]

/-- A spectral predicate is invariant under every real translation. -/
def SpectralRealShiftInvariant (P : ℂ → Prop) : Prop :=
  ∀ (s : ℂ) (r : ℝ),
    P (s + (r : ℂ)) ↔ P s

/-- A spectral predicate is determined solely by one fixed pair-left gauge. -/
def EtaPairBaseRotationDetermined
    (k : ℕ) (P : ℂ → Prop) : Prop :=
  ∀ s z : ℂ,
    etaPairBaseRotation s k = etaPairBaseRotation z k →
      (P s ↔ P z)

/-- Every predicate determined by one pair-left gauge is real-shift invariant. -/
theorem spectralRealShiftInvariant_of_etaPairBaseRotationDetermined
    {k : ℕ} {P : ℂ → Prop}
    (hP : EtaPairBaseRotationDetermined k P) :
    SpectralRealShiftInvariant P := by
  intro s r
  exact hP (s + (r : ℂ)) s (etaPairBaseRotation_add_real s k r)

/--
No real-shift-invariant predicate can characterize the critical line on the
whole complex plane.
-/
theorem not_characterizes_criticalLine_of_realShiftInvariant
    {P : ℂ → Prop} (hP : SpectralRealShiftInvariant P) :
    ¬ ∀ s : ℂ, P s ↔ s.re = (1 : ℝ) / 2 := by
  intro hchar
  let s0 : ℂ := (((1 : ℝ) / 2 : ℝ) : ℂ)
  have hs0re : s0.re = (1 : ℝ) / 2 := by
    simp [s0]
  have hP0 : P s0 :=
    (hchar s0).2 hs0re
  have hPshift : P (s0 + ((1 : ℝ) : ℂ)) :=
    (hP s0 1).2 hP0
  have hshiftRe :
      (s0 + ((1 : ℝ) : ℂ)).re = (1 : ℝ) / 2 :=
    (hchar (s0 + ((1 : ℝ) : ℂ))).1 hPshift
  norm_num [s0] at hshiftRe

/--
A predicate determined solely by one fixed pair-left gauge cannot characterize
the critical line.
-/
theorem not_characterizes_criticalLine_of_etaPairBaseRotationDetermined
    {k : ℕ} {P : ℂ → Prop}
    (hP : EtaPairBaseRotationDetermined k P) :
    ¬ ∀ s : ℂ, P s ↔ s.re = (1 : ℝ) / 2 :=
  not_characterizes_criticalLine_of_realShiftInvariant
    (spectralRealShiftInvariant_of_etaPairBaseRotationDetermined hP)

/--
There is no predicate on the value of one pair-left base rotation that
characterizes the critical line for every spectral point.
-/
theorem not_exists_etaPairBaseRotation_predicate_characterizing_criticalLine
    (k : ℕ) :
    ¬ ∃ Q : ℂ → Prop,
      ∀ s : ℂ,
        Q (etaPairBaseRotation s k) ↔
          s.re = (1 : ℝ) / 2 := by
  rintro ⟨Q, hQ⟩
  apply
    not_characterizes_criticalLine_of_realShiftInvariant
      (P := fun s => Q (etaPairBaseRotation s k))
  · intro s r
    change Q (etaPairBaseRotation (s + (r : ℂ)) k) ↔
      Q (etaPairBaseRotation s k)
    rw [etaPairBaseRotation_add_real]
  · exact hQ

/--
Closure certificate for the pair-left spectral-gauge route.  It records that
a gauge-determined predicate is real-shift invariant and therefore cannot
characterize the critical line.
-/
structure EtaPairSpectralGaugeClosureDecisionCertificate
    (k : ℕ) (P : ℂ → Prop) : Prop where
  gauge_determined : EtaPairBaseRotationDetermined k P
  real_shift_invariant : SpectralRealShiftInvariant P
  cannot_characterize_criticalLine :
    ¬ ∀ s : ℂ, P s ↔ s.re = (1 : ℝ) / 2

/-- Build the spectral-gauge closure certificate from gauge determination. -/
theorem etaPairSpectralGaugeClosureDecisionCertificate_of_determined
    {k : ℕ} {P : ℂ → Prop}
    (hP : EtaPairBaseRotationDetermined k P) :
    EtaPairSpectralGaugeClosureDecisionCertificate k P := by
  have hshift : SpectralRealShiftInvariant P :=
    spectralRealShiftInvariant_of_etaPairBaseRotationDetermined hP
  exact
    { gauge_determined := hP
      real_shift_invariant := hshift
      cannot_characterize_criticalLine :=
        not_characterizes_criticalLine_of_realShiftInvariant hshift }

end DkMath.RH.CFBRCProjection
