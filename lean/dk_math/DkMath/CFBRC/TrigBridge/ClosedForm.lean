/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CFBRC.TrigBridge.General
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Nat.Choose.Sum

open scoped BigOperators

namespace DkMath.CFBRC.TrigBridge

noncomputable section

/--
`cfbrcR d X Θ` の choose 形式（複素和）。

`(X+iΘ)^d - (iΘ)^d` の二項展開から、`k=0` 項を取り除いた形。
各項に `X` が残るよう `k+1` で添字を振っている。
-/
def cfbrcClosed (d : ℕ) (X Θ : ℝ) : ℂ :=
  ∑ k ∈ Finset.range d,
    (X : ℂ) ^ (k + 1) * (Complex.I * Θ) ^ (d - 1 - k) * (Nat.choose d (k + 1) : ℂ)

/--
`cfbrcR` は `cfbrcClosed`（choose 形式）に一致する。
-/
lemma cfbrcR_eq_cfbrcClosed (d : ℕ) (X Θ : ℝ) :
    cfbrcR d X Θ = cfbrcClosed d X Θ := by
  unfold cfbrcR cfbrc cfbrcClosed
  rw [add_pow]
  have hsplit :
      ∑ m ∈ Finset.range (d + 1),
          (X : ℂ) ^ m * (Complex.I * Θ) ^ (d - m) * (Nat.choose d m : ℂ)
        = (X : ℂ) ^ 0 * (Complex.I * Θ) ^ d * (Nat.choose d 0 : ℂ) +
          ∑ k ∈ Finset.range d,
            (X : ℂ) ^ (k + 1) * (Complex.I * Θ) ^ (d - 1 - k) *
              (Nat.choose d (k + 1) : ℂ) := by
    rw [Finset.sum_range_succ']
    simp only [Nat.sub_zero]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    congr 2
    have hsub : d - (k + 1) = d - 1 - k := by omega
    rw [hsub]
  rw [hsplit]
  simp

/--
`cfbrcClosed` の実部（raw 版）。

偶奇分離前の形として、複素位相項の実部をそのまま保持する。
-/
def cfbrcReClosedRaw (d : ℕ) (X Θ : ℝ) : ℝ :=
  ∑ k ∈ Finset.range d,
    X ^ (k + 1) * Complex.re ((Complex.I * Θ) ^ (d - 1 - k)) * (Nat.choose d (k + 1) : ℝ)

/--
`cfbrcClosed` の虚部（raw 版）。

偶奇分離前の形として、複素位相項の虚部をそのまま保持する。
-/
def cfbrcImClosedRaw (d : ℕ) (X Θ : ℝ) : ℝ :=
  ∑ k ∈ Finset.range d,
    X ^ (k + 1) * Complex.im ((Complex.I * Θ) ^ (d - 1 - k)) * (Nat.choose d (k + 1) : ℝ)

/--
`cfbrcRe` は `cfbrcReClosedRaw` に一致する。
-/
lemma cfbrcRe_eq_cfbrcReClosedRaw (d : ℕ) (X Θ : ℝ) :
    cfbrcRe d X Θ = cfbrcReClosedRaw d X Θ := by
  rw [cfbrcRe, cfbrcR_eq_cfbrcClosed, cfbrcClosed, cfbrcReClosedRaw, Complex.re_sum]
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hXRe : Complex.re ((X : ℂ) ^ (k + 1)) = X ^ (k + 1) := by
    simpa using ofReal_pow_re (d := k + 1) X
  have hXIm : Complex.im ((X : ℂ) ^ (k + 1)) = 0 := by
    simpa using ofReal_pow_im (d := k + 1) X
  calc
    Complex.re ((X : ℂ) ^ (k + 1) * (Complex.I * Θ) ^ (d - 1 - k) *
        (Nat.choose d (k + 1) : ℂ))
      = Complex.re ((X : ℂ) ^ (k + 1) * (Complex.I * Θ) ^ (d - 1 - k)) *
          (Nat.choose d (k + 1) : ℝ) := by
          rw [Complex.mul_re]
          simp
    _ = (X ^ (k + 1) * Complex.re ((Complex.I * Θ) ^ (d - 1 - k))) *
          (Nat.choose d (k + 1) : ℝ) := by
          rw [Complex.mul_re]
          rw [hXRe, hXIm]
          ring
    _ = X ^ (k + 1) * Complex.re ((Complex.I * Θ) ^ (d - 1 - k)) *
          (Nat.choose d (k + 1) : ℝ) := by
          ring

/--
`cfbrcIm` は `cfbrcImClosedRaw` に一致する。
-/
lemma cfbrcIm_eq_cfbrcImClosedRaw (d : ℕ) (X Θ : ℝ) :
    cfbrcIm d X Θ = cfbrcImClosedRaw d X Θ := by
  rw [cfbrcIm, cfbrcR_eq_cfbrcClosed, cfbrcClosed, cfbrcImClosedRaw, Complex.im_sum]
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hXRe : Complex.re ((X : ℂ) ^ (k + 1)) = X ^ (k + 1) := by
    simpa using ofReal_pow_re (d := k + 1) X
  have hXIm : Complex.im ((X : ℂ) ^ (k + 1)) = 0 := by
    simpa using ofReal_pow_im (d := k + 1) X
  calc
    Complex.im ((X : ℂ) ^ (k + 1) * (Complex.I * Θ) ^ (d - 1 - k) *
        (Nat.choose d (k + 1) : ℂ))
      = Complex.im ((X : ℂ) ^ (k + 1) * (Complex.I * Θ) ^ (d - 1 - k)) *
          (Nat.choose d (k + 1) : ℝ) := by
          rw [Complex.mul_im]
          simp
    _ = (X ^ (k + 1) * Complex.im ((Complex.I * Θ) ^ (d - 1 - k))) *
          (Nat.choose d (k + 1) : ℝ) := by
          rw [Complex.mul_im]
          rw [hXRe, hXIm]
          ring
    _ = X ^ (k + 1) * Complex.im ((Complex.I * Θ) ^ (d - 1 - k)) *
          (Nat.choose d (k + 1) : ℝ) := by
          ring

end

end DkMath.CFBRC.TrigBridge
