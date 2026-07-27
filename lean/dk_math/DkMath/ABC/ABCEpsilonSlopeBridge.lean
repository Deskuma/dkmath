/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.ABCEpsilonIdentity
import DkMath.ABC.GNJointPressureOddPrime

#print "file: DkMath.ABC.ABCEpsilonSlopeBridge"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# Intrinsic ABC epsilon and GN pressure slope

This epilogue module places the external ABC epsilon, the GN budget slope, the
intrinsic epsilon coordinate of a triple, and ordinary ABC quality in one
coordinate system.
-/

namespace DkMath.ABC

/-- The intrinsic epsilon slope encoded by an odd-prime GN pressure budget. -/
noncomputable def GNEpsilon (p : ℕ) (ρ : ℝ) : ℝ :=
  ρ / ((p - 1 : ℕ) : ℝ) - 1

/--
The usual joint-pressure margin is exactly the statement that the GN slope is
at most the external epsilon.
-/
theorem GNEpsilon_le_iff_margin
    {p : ℕ} (hp : 2 ≤ p) (ρ ε : ℝ) :
    GNEpsilon p ρ ≤ ε ↔
      ρ ≤ ((p - 1 : ℕ) : ℝ) * (1 + ε) := by
  have hdNat : 0 < p - 1 := by omega
  have hd : 0 < (((p - 1 : ℕ) : ℝ)) := by
    exact_mod_cast hdNat
  constructor
  · intro h
    have h' : ρ / (((p - 1 : ℕ) : ℝ)) ≤ 1 + ε := by
      dsimp [GNEpsilon] at h
      linarith
    have h'' := (div_le_iff₀ hd).1 h'
    simpa [mul_comm] using h''
  · intro h
    have h' : ρ / (((p - 1 : ℕ) : ℝ)) ≤ 1 + ε := by
      apply (div_le_iff₀ hd).2
      simpa [mul_comm] using h
    dsimp [GNEpsilon]
    linarith

/--
An odd-prime joint-pressure budget bounds the intrinsic epsilon directly by its
GN slope plus the finite radical-log correction.
-/
theorem Triple.abcEpsilon_le_GNEpsilon_add_correction
    (T : Triple) {p : ℕ} {ρ C : ℝ}
    (hp : Nat.Prime p)
    (hpOdd : Odd p)
    (ha : 0 < T.a)
    (hb : 0 < T.b)
    (hjoint : GNOddPrimeJointPressureBudgetAffine T p ρ C) :
    T.abcEpsilon ≤
      GNEpsilon p ρ +
        (C + Real.log (rad p : ℝ)) /
          (((p - 1 : ℕ) : ℝ) * T.radLog) := by
  let d : ℝ := ((p - 1 : ℕ) : ℝ)
  let B : ℝ := C + Real.log (rad p : ℝ)
  have hdNat : 0 < p - 1 := by omega
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast hdNat
  have hrad : 0 < T.radLog := by
    simpa [Triple.radLog] using T.log_rad_abc_pos ha hb
  have hheight0 :=
    T.log_c_mul_pred_le_of_oddPrime_jointPressure
      hp hpOdd ha hb hjoint
  have hheight :
      d * Real.log (T.c : ℝ) ≤ ρ * T.radLog + B := by
    simpa [d, B, Triple.radLog] using hheight0
  have hdiv :
      Real.log (T.c : ℝ) ≤ (ρ * T.radLog + B) / d := by
    apply (le_div_iff₀ hd).2
    simpa [mul_comm] using hheight
  have hnormalized :
      Real.log (T.c : ℝ) / T.radLog ≤
        ρ / d + B / (d * T.radLog) := by
    apply (div_le_iff₀ hrad).2
    calc
      Real.log (T.c : ℝ) ≤ (ρ * T.radLog + B) / d := hdiv
      _ = (ρ / d + B / (d * T.radLog)) * T.radLog := by
        field_simp [ne_of_gt hd, ne_of_gt hrad]
        <;> ring
  have hquality := T.quality_eq_one_add_abcEpsilon ha hb
  change Real.log (T.c : ℝ) / T.radLog =
    1 + T.abcEpsilon at hquality
  have hfinal :
      T.abcEpsilon ≤ ρ / d - 1 + B / (d * T.radLog) := by
    linarith
  simpa [GNEpsilon, d, B] using hfinal

/--
A fixed GN slope strictly below `δ` forces intrinsic epsilon eventually below
`δ` along every family whose radical-log scale tends to infinity.
-/
theorem eventually_abcEpsilon_lt_of_oddPrime_jointPressure_slope
    {ι : Type*} {l : Filter ι}
    (T : ι → Triple)
    {p : ℕ} (ρ C δ : ℝ)
    (hp : Nat.Prime p)
    (hpOdd : Odd p)
    (ha : ∀ᶠ i in l, 0 < (T i).a)
    (hb : ∀ᶠ i in l, 0 < (T i).b)
    (hjoint :
      ∀ᶠ i in l,
        GNOddPrimeJointPressureBudgetAffine (T i) p ρ C)
    (hrad : Filter.Tendsto (fun i => (T i).radLog) l Filter.atTop)
    (hδ : GNEpsilon p ρ < δ) :
    ∀ᶠ i in l, (T i).abcEpsilon < δ := by
  let d : ℝ := ((p - 1 : ℕ) : ℝ)
  let B : ℝ := C + Real.log (rad p : ℝ)
  let K : ℝ := B / d
  have hdNat : 0 < p - 1 := by omega
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast hdNat
  have hcorr :
      Filter.Tendsto
        (fun i => K / (T i).radLog) l (nhds 0) :=
    tendsto_const_nhds.div_atTop hrad
  have hη : 0 < δ - GNEpsilon p ρ := sub_pos.mpr hδ
  have hsmall :
      ∀ᶠ i in l, K / (T i).radLog < δ - GNEpsilon p ρ :=
    (tendsto_order.1 hcorr).2 _ hη
  filter_upwards [ha, hb, hjoint, hsmall] with i hai hbi hjointi hsmalli
  have hpoint :=
    (T i).abcEpsilon_le_GNEpsilon_add_correction
      hp hpOdd hai hbi hjointi
  have hradI : 0 < (T i).radLog := by
    simpa [Triple.radLog] using (T i).log_rad_abc_pos hai hbi
  have hcorrEq :
      (C + Real.log (rad p : ℝ)) /
          (d * (T i).radLog) =
        K / (T i).radLog := by
    dsimp [K, B]
    field_simp [ne_of_gt hd, ne_of_gt hradI]
    <;> ring
  change (T i).abcEpsilon ≤
    GNEpsilon p ρ +
      (C + Real.log (rad p : ℝ)) /
        (d * (T i).radLog) at hpoint
  rw [hcorrEq] at hpoint
  linarith

/--
Margin-form corollary: the direct GN slope bridge recovers the familiar
external-epsilon asymptotic statement without passing through an ABC constant.
-/
theorem eventually_abcEpsilon_lt_of_oddPrime_jointPressure
    {ι : Type*} {l : Filter ι}
    (T : ι → Triple)
    {p : ℕ} (ε ρ C δ : ℝ)
    (hp : Nat.Prime p)
    (hpOdd : Odd p)
    (ha : ∀ᶠ i in l, 0 < (T i).a)
    (hb : ∀ᶠ i in l, 0 < (T i).b)
    (hmargin :
      ρ ≤ ((p - 1 : ℕ) : ℝ) * (1 + ε))
    (hjoint :
      ∀ᶠ i in l,
        GNOddPrimeJointPressureBudgetAffine (T i) p ρ C)
    (hrad : Filter.Tendsto (fun i => (T i).radLog) l Filter.atTop)
    (hεδ : ε < δ) :
    ∀ᶠ i in l, (T i).abcEpsilon < δ := by
  have hSlope : GNEpsilon p ρ < δ :=
    lt_of_le_of_lt
      ((GNEpsilon_le_iff_margin hp.two_le ρ ε).2 hmargin)
      hεδ
  exact eventually_abcEpsilon_lt_of_oddPrime_jointPressure_slope
    T ρ C δ hp hpOdd ha hb hjoint hrad hSlope

end DkMath.ABC
