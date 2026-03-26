/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

-- cid: 696e90e6-f128-8323-8b07-86794a7730d2

import Mathlib
import DkMath.RH.Basic  -- Riemann Hypothesis Basic Utilities
import DkMath.RH.Defs  -- Riemann Hypothesis Definitions

#print "file: DkMath.RH.Lemmas"

-- ----------------------------------------------------------------------------

namespace DkMath.RH

-- Lemmas for Riemann Hypothesis Module

open scoped Real
open Complex

/-- 分母の定義と基本補題群 -/
lemma denom_eq_normSq (z : ℂ) : denom z = Complex.normSq z := by
  simp [denom, Complex.normSq]
  ring

/--
代数コア:
z ≠ 0 のとき、Im(dz / z) = torque z dz / normSq z
（文書の dθ/dt 公式の“形”そのもの）
-/
lemma im_div_eq_torque_div_normSq {z dz : ℂ} :
    (dz / z).im = (torque z dz) / (Complex.normSq z) := by
  -- dz / z = dz * (conj z) / normSq z を使って展開するのが定石
  -- ここは `simp` + `ring` で落ちることが多い
  calc
    (dz / z).im = dz.im * z.re / Complex.normSq z - dz.re * z.im / Complex.normSq z := by
      simp only [div_im]
    _ = (dz.im * z.re - dz.re * z.im) / Complex.normSq z := by
      simpa using (sub_div (dz.im * z.re) (dz.re * z.im) (Complex.normSq z)).symm
    _ = (z.re * dz.im - z.im * dz.re) / Complex.normSq z := by
      ring
    _ = (torque z dz) / Complex.normSq z := by
      simp [torque]

/--
局所ドリフト消失は Im(dz/z)=0 と同値（z≠0）。
-/
lemma driftFreeLocal_iff_im_div_eq_zero {z dz : ℂ} (hz : z ≠ 0) :
    driftFreeLocal z dz ↔ (dz / z).im = 0 := by
  -- 上の代数コアを使って分母を払う
  have hnorm : Complex.normSq z ≠ 0 := by
    intro h0
    exact hz ((Complex.normSq_eq_zero).1 h0)
  constructor
  · intro h
    calc
      (dz / z).im = (torque z dz) / Complex.normSq z := by
        simpa using (im_div_eq_torque_div_normSq (z:=z) (dz:=dz))
      _ = 0 := by simp [driftFreeLocal] at h; simp [h]
  · intro h
    have h' : (torque z dz) / Complex.normSq z = 0 := by
      simpa [im_div_eq_torque_div_normSq (z:=z) (dz:=dz)] using h
    have h'' : torque z dz = 0 ∨ Complex.normSq z = 0 := (div_eq_zero_iff).1 h'
    have ht : torque z dz = 0 := h''.resolve_right hnorm
    simpa [driftFreeLocal] using ht

/-- トルクと共役複素数の積の虚部の等式 star 版 -/
lemma torque_eq_im_mul_conj' (z dz : ℂ) :
    torque z dz = (dz * star z).im := by
  -- 展開して simp/ring
  simp only [torque, star, mul_im, mul_neg]
  ring

open scoped ComplexConjugate

/-- torque は dz * conj z の虚部に等しい -/
lemma torque_eq_im_mul_conj (z dz : ℂ) :
    torque z dz = (dz * (conj z)).im := by
  -- conj z は (starRingEnd ℂ) z のこと
  -- conj_re / conj_im が simp で使える
  simp [torque, Complex.mul_im]
  ring

-- ----------------------------------------------------------------------------

/-- 位相速度とトルクの関係式 -/
lemma phaseVel_eq_torque_div_normSq (f : ℝ → ℂ) (t : ℝ) :
    phaseVel f t
      = (torque (f t) (deriv f t)) / (Complex.normSq (f t)) := by
  -- phaseVel の定義を開いて、すでにある代数コアへ接続
  simpa [phaseVel] using
    (im_div_eq_torque_div_normSq (z := f t) (dz := deriv f t))

/-- 位相速度の別表現: Im( f' * conj f ) / normSq f -/
lemma phaseVel_eq_im_mul_conj_div_normSq (f : ℝ → ℂ) (t : ℝ) :
    phaseVel f t = ((deriv f t * conj (f t)).im) / Complex.normSq (f t) := by
  -- 既存補題 + torque_eq_im_mul_conj
  simp [phaseVel_eq_torque_div_normSq, torque_eq_im_mul_conj]

/--
位相速度の積法則。

`f(t), g(t) ≠ 0` の下で
`phaseVel (f*g) = phaseVel f + phaseVel g`。
-/
lemma phaseVel_mul
    (f g : ℝ → ℂ) (t : ℝ)
    (hf : DifferentiableAt ℝ f t) (hg : DifferentiableAt ℝ g t)
    (hf0 : f t ≠ 0) (hg0 : g t ≠ 0) :
    phaseVel (fun u => f u * g u) t = phaseVel f t + phaseVel g t := by
  unfold phaseVel
  have hderiv :
      deriv (fun u => f u * g u) t = deriv f t * g t + f t * deriv g t := by
    simpa using deriv_mul hf hg
  rw [hderiv]
  have hdiv :
      (deriv f t * g t + f t * deriv g t) / (f t * g t) =
        deriv f t / f t + deriv g t / g t := by
    field_simp [hf0, hg0]
  rw [hdiv, Complex.add_im]

/--
位相速度の逆数法則。

`f(t) ≠ 0` の下で `phaseVel (1/f) = - phaseVel f`。
-/
lemma phaseVel_inv
    (f : ℝ → ℂ) (t : ℝ)
    (hf : DifferentiableAt ℝ f t) (hf0 : f t ≠ 0) :
    phaseVel (fun u => (f u)⁻¹) t = - phaseVel f t := by
  unfold phaseVel
  have hderiv :
      deriv (fun u : ℝ => (1 : ℂ) / f u) t =
        ((deriv (fun _ : ℝ => (1 : ℂ)) t * f t - (1 : ℂ) * deriv f t) / (f t) ^ 2) := by
    simpa using
      (deriv_fun_div (𝕜 := ℝ)
        (c := fun _ : ℝ => (1 : ℂ)) (d := f) (x := t)
        (differentiableAt_const (x := t) (c := (1 : ℂ))) hf hf0)
  have hone : deriv (fun _ : ℝ => (1 : ℂ)) t = 0 := by simp
  rw [show (fun u => (f u)⁻¹) = (fun u : ℝ => (1 : ℂ) / f u) by
      funext u; simp [one_div], hderiv, hone]
  field_simp [hf0]
  simp [neg_div, Complex.neg_im]

/--
位相速度の除法則。

`g(t) ≠ 0` の下で `phaseVel (f/g) = phaseVel f - phaseVel g`。
-/
lemma phaseVel_div
    (f g : ℝ → ℂ) (t : ℝ)
    (hf : DifferentiableAt ℝ f t) (hg : DifferentiableAt ℝ g t)
    (hf0 : f t ≠ 0)
    (hg0 : g t ≠ 0) :
    phaseVel (fun u => f u / g u) t = phaseVel f t - phaseVel g t := by
  have hmul :
      phaseVel (fun u => f u * (g u)⁻¹) t =
        phaseVel f t + phaseVel (fun u => (g u)⁻¹) t := by
    exact phaseVel_mul (f := f) (g := fun u => (g u)⁻¹) (t := t)
      hf (hg.inv hg0) hf0 (inv_ne_zero hg0)
  have hinv :
      phaseVel (fun u => (g u)⁻¹) t = - phaseVel g t :=
    phaseVel_inv (f := g) (t := t) hg hg0
  simpa [div_eq_mul_inv, hinv, sub_eq_add_neg] using hmul

-- ----------------------------------------------------------------------------

/-- 局所ドリフト消失と位相速度ゼロの同値性 -/
lemma driftFreeLocal_iff_phaseVel_eq_zero
    (f : ℝ → ℂ) (t : ℝ) (hz : f t ≠ 0) :
    driftFreeLocal (f t) (deriv f t) ↔ phaseVel f t = 0 := by
  -- driftFreeLocal ↔ Im((deriv f t)/(f t))=0 ↔ phaseVel=0
  simpa [phaseVel] using
    (driftFreeLocal_iff_im_div_eq_zero (z := f t) (dz := deriv f t) hz)

/-- 点 t でのドリフト消失は位相速度ゼロと同値（f t ≠ 0） -/
lemma driftFreeAt_iff_phaseVel_eq_zero (f : ℝ → ℂ) (t : ℝ) (hz : f t ≠ 0) :
    driftFreeAt f t ↔ phaseVel f t = 0 := by
  simpa [driftFreeAt] using (driftFreeLocal_iff_phaseVel_eq_zero (f:=f) (t:=t) hz)

/-- 点 t でのドリフト消失は位相停留と同値（f t ≠ 0） -/
lemma driftFreeAt_iff_stationaryAt (f : ℝ → ℂ) (t : ℝ) (hz : f t ≠ 0) :
    driftFreeAt f t ↔ stationaryAt f t := by
  simpa [stationaryAt] using (driftFreeAt_iff_phaseVel_eq_zero (f := f) (t := t) hz)

/--
非退化停留点は「ドリフト消失」と「位相曲率非零」に分解できる（f t ≠ 0）。
-/
lemma nondegenerateStationaryAt_iff_driftFreeAt_and_phaseCurv_ne_zero
    (f : ℝ → ℂ) (t : ℝ) (hz : f t ≠ 0) :
    nondegenerateStationaryAt f t ↔ driftFreeAt f t ∧ phaseCurv f t ≠ 0 := by
  constructor
  · intro h
    rcases h with ⟨hstat, hcurv⟩
    exact ⟨(driftFreeAt_iff_stationaryAt (f := f) (t := t) hz).2 hstat, hcurv⟩
  · intro h
    rcases h with ⟨hdrift, hcurv⟩
    exact ⟨(driftFreeAt_iff_stationaryAt (f := f) (t := t) hz).1 hdrift, hcurv⟩

end DkMath.RH
