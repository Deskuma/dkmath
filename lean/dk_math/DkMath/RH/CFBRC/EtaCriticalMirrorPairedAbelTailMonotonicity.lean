/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedAbelProjection
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedAbelTailMonotonicity"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter Set
open scoped Topology

/-- An eventually positive successor drift gives strict monotonicity on a natural tail. -/
private theorem exists_strictMonoOn_Ici_nat_of_eventually_lt_succ
    {u : ℕ → ℝ}
    (hstep : ∀ᶠ n : ℕ in atTop, u n < u (n + 1)) :
    ∃ N : ℕ, StrictMonoOn u (Ici N) := by
  rcases eventually_atTop.1 hstep with ⟨N, hN⟩
  have hshift : StrictMono (fun n : ℕ => u (N + n)) := by
    apply strictMono_nat_of_lt_succ
    intro n
    simpa [Nat.add_assoc] using hN (N + n) (by omega)
  refine ⟨N, ?_⟩
  intro a ha b hb hab
  have haN : N ≤ a := ha
  have hbN : N ≤ b := hb
  have hdiff : a - N < b - N := by omega
  have h := hshift hdiff
  have haeq : N + (a - N) = a := by omega
  have hbeq : N + (b - N) = b := by omega
  simpa [haeq, hbeq] using h

/-- An eventually negative successor drift gives strict antitonicity on a natural tail. -/
private theorem exists_strictAntiOn_Ici_nat_of_eventually_succ_lt
    {u : ℕ → ℝ}
    (hstep : ∀ᶠ n : ℕ in atTop, u (n + 1) < u n) :
    ∃ N : ℕ, StrictAntiOn u (Ici N) := by
  rcases eventually_atTop.1 hstep with ⟨N, hN⟩
  have hshiftNeg : StrictMono (fun n : ℕ => -u (N + n)) := by
    apply strictMono_nat_of_lt_succ
    intro n
    have h := neg_lt_neg (hN (N + n) (by omega))
    simpa [Nat.add_assoc] using h
  refine ⟨N, ?_⟩
  intro a ha b hb hab
  have haN : N ≤ a := ha
  have hbN : N ≤ b := hb
  have hdiff : a - N < b - N := by omega
  have h := hshiftNeg hdiff
  have haeq : N + (a - N) = a := by omega
  have hbeq : N + (b - N) = b := by omega
  have hneg : -u a < -u b := by
    simpa [haeq, hbeq] using h
  linarith

/--
Right of the critical line, the projected moving-frame Abel partial sums are
strictly monotone on one complete natural tail.
-/
theorem exists_etaCriticalMirrorRotatedDefectProjectionPartial_strictMonoOn_tail_of_half_lt_re
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    ∃ K0 : ℕ,
      StrictMonoOn
        (fun K : ℕ =>
          etaCriticalMirrorRotatedDefectProjectionPartial K s)
        (Ici K0) :=
  exists_strictMonoOn_Ici_nat_of_eventually_lt_succ
    (eventually_etaCriticalMirrorRotatedDefectProjectionPartial_lt_succ_of_half_lt_re
      hs him hre)

/--
Left of the critical line, the projected moving-frame Abel partial sums are
strictly antitone on one complete natural tail.
-/
theorem exists_etaCriticalMirrorRotatedDefectProjectionPartial_strictAntiOn_tail_of_re_lt_half
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    ∃ K0 : ℕ,
      StrictAntiOn
        (fun K : ℕ =>
          etaCriticalMirrorRotatedDefectProjectionPartial K s)
        (Ici K0) :=
  exists_strictAntiOn_Ici_nat_of_eventually_succ_lt
    (eventually_etaCriticalMirrorRotatedDefectProjectionPartial_succ_lt_of_re_lt_half
      hs him hre)

/-- Every fixed positive forward block increases the projected partial sum on the right. -/
theorem eventually_etaCriticalMirrorRotatedDefectProjectionPartial_lt_add_of_half_lt_re
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re)
    {N : ℕ} (hN : 0 < N) :
    ∀ᶠ K : ℕ in atTop,
      etaCriticalMirrorRotatedDefectProjectionPartial K s <
        etaCriticalMirrorRotatedDefectProjectionPartial (K + N) s := by
  rcases
    exists_etaCriticalMirrorRotatedDefectProjectionPartial_strictMonoOn_tail_of_half_lt_re
      hs him hre with ⟨K0, hmono⟩
  filter_upwards [eventually_ge_atTop K0] with K hK
  exact hmono hK
    (by exact_mod_cast (show K0 ≤ K + N by omega))
    (by exact_mod_cast (show K < K + N by omega))

/-- Every fixed positive forward block decreases the projected partial sum on the left. -/
theorem eventually_etaCriticalMirrorRotatedDefectProjectionPartial_add_lt_of_re_lt_half
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2)
    {N : ℕ} (hN : 0 < N) :
    ∀ᶠ K : ℕ in atTop,
      etaCriticalMirrorRotatedDefectProjectionPartial (K + N) s <
        etaCriticalMirrorRotatedDefectProjectionPartial K s := by
  rcases
    exists_etaCriticalMirrorRotatedDefectProjectionPartial_strictAntiOn_tail_of_re_lt_half
      hs him hre with ⟨K0, hanti⟩
  filter_upwards [eventually_ge_atTop K0] with K hK
  exact hanti hK
    (by exact_mod_cast (show K0 ≤ K + N by omega))
    (by exact_mod_cast (show K < K + N by omega))

end DkMath.RH.CFBRCProjection
