/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.SevenGNDescent

#print "file: DkMathTest.FLT.Kummer.SevenGNDescent"

/-! 新しい教科書の全公開宣言と、MathlibそのもののFLT7型を監査する。 -/
#print axioms DkMath.FLT.Kummer.SevenDescent.no_state_one
#print axioms DkMath.FLT.Kummer.SevenDescent.descent_step
#print axioms DkMath.FLT.Kummer.SevenDescent.fermatLastTheoremFor_seven

run_cmd do
  for n in #[
      ``DkMath.FLT.Kummer.SevenDescent.State,
      ``DkMath.FLT.Kummer.SevenDescent.normalize_weighted,
      ``DkMath.FLT.Kummer.SevenDescent.seventh_sum_eq_gtail,
      ``DkMath.FLT.Kummer.SevenDescent.seventh_sum_eq_gn,
      ``DkMath.FLT.Kummer.SevenDescent.State.gn_equation,
      ``DkMath.FLT.Kummer.SevenDescent.State.pi_equation,
      ``DkMath.FLT.Kummer.SevenDescent.uniformizer_dvd_int_iff,
      ``DkMath.FLT.Kummer.SevenDescent.initial_state_of_summit,
      ``DkMath.FLT.Kummer.SevenDescent.initial_state_of_counterexample,
      ``DkMath.FLT.Kummer.SevenDescent.phaseSlope,
      ``DkMath.FLT.Kummer.SevenDescent.phaseSlope_spec,
      ``DkMath.FLT.Kummer.SevenDescent.phaseSlope_residue,
      ``DkMath.FLT.Kummer.SevenDescent.State.uniformizer_dvd_sum,
      ``DkMath.FLT.Kummer.SevenDescent.State.center,
      ``DkMath.FLT.Kummer.SevenDescent.State.center_spec,
      ``DkMath.FLT.Kummer.SevenDescent.State.quotient,
      ``DkMath.FLT.Kummer.SevenDescent.State.quotient_spec,
      ``DkMath.FLT.Kummer.SevenDescent.State.y_residue_ne_zero,
      ``DkMath.FLT.Kummer.SevenDescent.State.distinguishedPhase,
      ``DkMath.FLT.Kummer.SevenDescent.State.distinguished_dvd,
      ``DkMath.FLT.Kummer.SevenDescent.State.quotient_dvd_iff,
      ``DkMath.FLT.Kummer.SevenDescent.State.product_quotients,
      ``DkMath.FLT.Kummer.SevenDescent.State.uniformizer_pow_eight_dvd,
      ``DkMath.FLT.Kummer.SevenDescent.no_state_one,
      ``DkMath.FLT.Kummer.SevenDescent.phaseSlope_sub_isUnit,
      ``DkMath.FLT.Kummer.SevenDescent.State.quotient_coprime_y,
      ``DkMath.FLT.Kummer.SevenDescent.State.quotients_coprime,
      ``DkMath.FLT.Kummer.SevenDescent.State.quotient_product,
      ``DkMath.FLT.Kummer.SevenDescent.State.quotient_ideal_power,
      ``DkMath.FLT.Kummer.SevenDescent.State.exists_quotient_roots,
      ``DkMath.FLT.Kummer.SevenDescent.uniformizer_prime,
      ``DkMath.FLT.Kummer.SevenDescent.seventh_congr_integer,
      ``DkMath.FLT.Kummer.SevenDescent.coprime_seven_of_away,
      ``DkMath.FLT.Kummer.SevenDescent.ratio_congr_seventh,
      ``DkMath.FLT.Kummer.SevenDescent.ratio_seventh,
      ``DkMath.FLT.Kummer.SevenDescent.State.exists_descent_roots,
      ``DkMath.FLT.Kummer.SevenDescent.State.three_phase_identity,
      ``DkMath.FLT.Kummer.SevenDescent.State.exists_weighted_successor,
      ``DkMath.FLT.Kummer.SevenDescent.descent_step,
      ``DkMath.FLT.Kummer.SevenDescent.no_state,
      ``DkMath.FLT.Kummer.SevenDescent.no_counterexample,
      ``DkMath.FLT.Kummer.SevenDescent.coprime_of_gcd_triple_eq_one,
      ``DkMath.FLT.Kummer.SevenDescent.fermatLastTheoremFor_seven,
      ``DkMath.FLT.Kummer.SevenDescent.seventh_sum_ne_seventh] do
    for ax in ← Lean.collectAxioms n do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {n}"
  Lean.logInfo "PASS: all 44 public declarations; standard axiom whitelist only."

open DkMath.FLT.Kummer.SevenDescent

-- The endpoint has Mathlib's exact standard statement, with no provider arguments.
example : _root_.FermatLastTheoremFor 7 := fermatLastTheoremFor_seven

-- Removing primitive/gcd hypotheses really reaches ALL nonzero natural triples.
example (a b c : ℕ) (h : a ^ 7 + b ^ 7 = c ^ 7) : a = 0 ∨ b = 0 ∨ c = 0 := by
  by_contra hn
  push Not at hn
  exact fermatLastTheoremFor_seven a b c hn.1 hn.2.1 hn.2.2 h

-- Positive depth must be retained; State 0 has an actual witness.
example : Nonempty (State 0) := by
  open DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt in
    have h1 : ¬ ramifiedUniformizer ∣ (1 : Ring) := by
      intro h
      have := (uniformizer_dvd_int_iff 1).mp h
      norm_num at this
    exact ⟨{
      x := 0
      y := 1
      z := 1
      epsilon := 1
      coprime := isCoprime_one_right
      y_away := h1
      z_away := h1
      equation := by simp }⟩

example (m : ℕ) (hm : 1 ≤ m) : ¬ Nonempty (State m) := no_state m hm
