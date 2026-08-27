/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set

open scoped ComplexConjugate

/-!
# Mellin critical-mirror adapter

This file contains the generic, zero-independent Mellin reflection algebra used
by the CFBRC projection layer.  The mirror of `h` is the positive-domain
function

`x ↦ x⁻¹ * conj (h x⁻¹)`.

The main theorem is deliberately stated with an explicit Mellin convergence
hypothesis.  Its proof is the B1 route: Mathlib's `mellin_cpow_smul` performs
the `x⁻¹` Mellin shift, `mellin_comp_inv` performs the inverse substitution, and
`integral_conj` exchanges complex conjugation with the Bochner integral.

This is a classical finite-integral adapter.  It does not assert an analytic
continuation, a Guinand--Weil formula, a zeta or Xi identity, a zero
classification, or an RH conclusion.  In particular, the convergence
hypothesis below is not a hidden claim that a later CFBRC family satisfies it.
-/

namespace DkMath.Analysis

/-! ## Definitions -/

/-- The critical Mellin mirror of a complex-valued function on the positive ray.

The formula is totalized on all real inputs only so that it is a Lean function;
all Mellin integrals in this file are over `Ioi 0`, where it is the classical
`x⁻¹ * conj (h (x⁻¹))` formula.
-/
noncomputable def mellinCriticalMirror (h : ℝ → ℂ) (x : ℝ) : ℂ :=
  (x⁻¹ : ℂ) * (starRingEnd ℂ) (h x⁻¹)

/-- The positive-domain involutivity of the Mellin critical mirror. -/
theorem mellinCriticalMirror_involutive_on_pos (h : ℝ → ℂ) {x : ℝ} (hx : 0 < x) :
    mellinCriticalMirror (mellinCriticalMirror h) x = h x := by
  unfold mellinCriticalMirror
  rw [map_mul, map_inv₀, inv_inv]
  simp only [starRingEnd_apply, map_inv₀, star_star, Complex.ofReal_inv,
    inv_inv]
  simp [hx.ne']

/-- Naming-compatible positive-domain form of the mirror involution theorem. -/
theorem mellinCriticalMirror_involutive_of_pos
    (h : ℝ → ℂ) {x : ℝ} (hx : 0 < x) :
    mellinCriticalMirror (mellinCriticalMirror h) x = h x :=
  mellinCriticalMirror_involutive_on_pos h hx

/-- The mirror's ordinary inverse factor is the Mellin `cpow` shift on `Ioi 0`. -/
private theorem mellinCriticalMirror_eq_cpow_neg_one_on_pos
    (h : ℝ → ℂ) {x : ℝ} (_hx : 0 < x) :
    mellinCriticalMirror h x = (x : ℂ) ^ (-1 : ℂ) •
      (starRingEnd ℂ) (h x⁻¹) := by
  simp [mellinCriticalMirror, smul_eq_mul, Complex.cpow_neg, Complex.cpow_one]

private theorem mellin_conj (h : ℝ → ℂ) (s : ℂ)
    (_hconv : MellinConvergent h ((starRingEnd ℂ) s)) :
    mellin (fun x => (starRingEnd ℂ) (h x)) s =
      (starRingEnd ℂ) (mellin h ((starRingEnd ℂ) s)) := by
  unfold mellin at *
  have hpoint : Set.EqOn
      (fun t : ℝ => (t : ℂ) ^ (s - 1) • (starRingEnd ℂ) (h t))
      (fun t : ℝ => (starRingEnd ℂ)
        ((t : ℂ) ^ ((starRingEnd ℂ) s - 1) • h t)) (Set.Ioi 0) := by
    intro t ht
    dsimp
    change (t : ℂ) ^ (s - 1) • (starRingEnd ℂ) (h t) =
      (starRingEnd ℂ) ((t : ℂ) ^ ((starRingEnd ℂ) s - 1) • h t)
    change (t : ℂ) ^ (s - 1) • star (h t) =
      star ((t : ℂ) ^ ((starRingEnd ℂ) s - 1) • h t)
    rw [star_smul]
    symm
    congr 1
    calc
      star ((t : ℂ) ^ ((starRingEnd ℂ) s - 1)) =
          star ((t : ℂ) ^ (star (s - 1))) := by
            rw [show (starRingEnd ℂ) s - 1 = star (s - 1) by
              change star s - 1 = star (s - 1)
              rw [star_sub, star_one]]
      _ = star (t : ℂ) ^ (s - 1) := by
        symm
        apply Complex.conj_cpow
        rw [Complex.arg_ofReal_of_nonneg ht.le]
        exact Real.pi_ne_zero.symm
      _ = (t : ℂ) ^ (s - 1) := by simp
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hpoint, integral_conj]

/-! ## Reflection theorem -/

/-- Mellin reflection through the critical line.

For every `s` at which the original Mellin integral at `1 - conj s` is
convergent, the Mellin transform of the critical mirror is the conjugate of
that original transform.  The mirror-side convergence argument is included as
an explicit parameter to expose the intended domain of the adapter, even
though Mathlib's normalized Mellin identities can evaluate both sides without
using it.
-/
theorem mellin_mellinCriticalMirror
    (h : ℝ → ℂ) (s : ℂ)
    (_hconv₁ : MellinConvergent (mellinCriticalMirror h) s)
    (hconv₂ : MellinConvergent h (1 - (starRingEnd ℂ) s)) :
    mellin (mellinCriticalMirror h) s =
      (starRingEnd ℂ) (mellin h (1 - (starRingEnd ℂ) s)) := by
  have hscale :
      mellin (mellinCriticalMirror h) s =
        mellin (fun t : ℝ => (t : ℂ) ^ (-1 : ℂ) •
          (starRingEnd ℂ) (h t⁻¹)) s := by
    unfold mellin
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp
    change (t : ℂ) ^ (s - 1) • mellinCriticalMirror h t =
      (t : ℂ) ^ (s - 1) •
        ((t : ℂ) ^ (-1 : ℂ) • (starRingEnd ℂ) (h t⁻¹))
    rw [mellinCriticalMirror_eq_cpow_neg_one_on_pos h ht]
  rw [hscale, mellin_cpow_smul]
  have hinv := mellin_comp_inv (fun t : ℝ => (starRingEnd ℂ) (h t)) (-(1 - s))
  rw [show s + (-1 : ℂ) = -(1 - s) by ring, hinv]
  have hstar : (starRingEnd ℂ) (1 - s) = 1 - (starRingEnd ℂ) s := by
    rw [map_sub, map_one]
  have hconv₂' : MellinConvergent h ((starRingEnd ℂ) (1 - s)) := by
    rw [hstar]
    exact hconv₂
  have hconj := mellin_conj h (1 - s) hconv₂'
  rw [hstar] at hconj
  simpa only [neg_neg] using hconj

/-- The centered complex parameter algebra used by the Mellin corollary. -/
theorem one_sub_conj_half_add (z : ℂ) :
    1 - (starRingEnd ℂ) ((1 : ℂ) / 2 + z) =
      (1 : ℂ) / 2 - (starRingEnd ℂ) z := by
  have hhalf : (starRingEnd ℂ) ((1 : ℂ) / 2) = (1 : ℂ) / 2 := by
    apply Complex.ext <;> norm_num
  rw [map_add, hhalf]
  ring

/-- Centered Mellin reflection, with `z` measured from `1/2`. -/
theorem mellin_mellinCriticalMirror_centered
    (h : ℝ → ℂ) (z : ℂ)
    (hconv₁ : MellinConvergent (mellinCriticalMirror h) ((1 : ℂ) / 2 + z))
    (hconv₂ : MellinConvergent h ((1 : ℂ) / 2 - (starRingEnd ℂ) z)) :
    mellin (mellinCriticalMirror h) ((1 : ℂ) / 2 + z) =
      (starRingEnd ℂ) (mellin h ((1 : ℂ) / 2 - (starRingEnd ℂ) z)) := by
  have hcenter := one_sub_conj_half_add z
  have hmain := mellin_mellinCriticalMirror h ((1 : ℂ) / 2 + z) hconv₁ (by
    rw [hcenter]
    exact hconv₂)
  rw [hcenter] at hmain
  exact hmain

/-- Candidate-name alias for the centered Mellin reflection corollary. -/
theorem mellin_mellinCriticalMirror_half_add
    (h : ℝ → ℂ) (z : ℂ)
    (hconv₁ : MellinConvergent (mellinCriticalMirror h) ((1 : ℂ) / 2 + z))
    (hconv₂ : MellinConvergent h ((1 : ℂ) / 2 - (starRingEnd ℂ) z)) :
    mellin (mellinCriticalMirror h) ((1 : ℂ) / 2 + z) =
      (starRingEnd ℂ)
        (mellin h ((1 : ℂ) / 2 - (starRingEnd ℂ) z)) :=
  mellin_mellinCriticalMirror_centered h z hconv₁ hconv₂

end DkMath.Analysis
