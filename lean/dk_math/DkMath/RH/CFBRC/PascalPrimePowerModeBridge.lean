/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalPrimeEulerModeBridge
import DkMath.NumberTheory.PrimitiveSet.VonMangoldtShadow
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.PascalPrimePowerModeBridge"

/-!
# Pascal prime-power / von-Mangoldt shadow bridge

This module lifts the PPW-007 primitive mode to positive integer powers and
attaches the explicit finite shadow cost `log p` carried by `PrimePowerLabel`.
The resulting rectangular ladder is a finite prime-power complex wave.  It is
not the analytic von Mangoldt function, not `-ζ'/ζ`, and not a claim about
zeros or RH.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.NumberTheory
open DkMath.NumberTheory.PrimitiveSet

/-- The `k`th positive-integer power of the primitive prime mode. -/
noncomputable def eulerPrimePowerMode (p k : ℕ) (s : ℂ) : ℂ :=
  (eulerPrimePrimitiveMode p s) ^ k

@[simp] theorem eulerPrimePowerMode_zero (p : ℕ) (s : ℂ) :
    eulerPrimePowerMode p 0 s = 1 := by
  simp [eulerPrimePowerMode]

@[simp] theorem eulerPrimePowerMode_succ (p k : ℕ) (s : ℂ) :
    eulerPrimePowerMode p (k + 1) s =
      eulerPrimePowerMode p k s * eulerPrimePrimitiveMode p s := by
  simp [eulerPrimePowerMode, pow_succ, mul_comm]

@[simp] theorem eulerPrimePowerMode_one
    {p : ℕ} (_hp : Nat.Prime p) (s : ℂ) :
    eulerPrimePowerMode p 1 s = eulerPrimePrimitiveMode p s := by
  simp [eulerPrimePowerMode]

/-- An explicit prime-power label born from prime `p` and positive exponent `k+1`. -/
noncomputable def pascalPrimePowerLabel
    (p : ℕ) (hp : Nat.Prime p) (k : ℕ) : PrimePowerLabel where
  q := p ^ (k + 1)
  p := p
  k := k + 1
  prime := hp
  k_pos := by omega
  eq_pow := rfl

@[simp] theorem pascalPrimePowerLabel_q
    (p : ℕ) (hp : Nat.Prime p) (k : ℕ) :
    (pascalPrimePowerLabel p hp k).q = p ^ (k + 1) := rfl

@[simp] theorem pascalPrimePowerLabel_p
    (p : ℕ) (hp : Nat.Prime p) (k : ℕ) :
    (pascalPrimePowerLabel p hp k).p = p := rfl

@[simp] theorem pascalPrimePowerLabel_k
    (p : ℕ) (hp : Nat.Prime p) (k : ℕ) :
    (pascalPrimePowerLabel p hp k).k = k + 1 := rfl

@[simp] theorem pascalPrimePowerLabel_vonMangoldtLogCost
    (p : ℕ) (hp : Nat.Prime p) (k : ℕ) :
    (pascalPrimePowerLabel p hp k).vonMangoldtLogCost =
      Real.log (p : ℝ) := rfl

/-- One weighted prime-power shadow mode with the explicit `log p` cost. -/
noncomputable def eulerPrimePowerShadowMode
    (p : ℕ) (hp : Nat.Prime p) (k : ℕ) (s : ℂ) : ℂ :=
  ((pascalPrimePowerLabel p hp k).vonMangoldtLogCost : ℂ) *
    eulerPrimePowerMode p (k + 1) s

/-- The shadow mode is `log p` times the `(k+1)`st primitive mode power. -/
theorem eulerPrimePowerShadowMode_eq_log_mul_mode
    (p : ℕ) (hp : Nat.Prime p) (k : ℕ) (s : ℂ) :
    eulerPrimePowerShadowMode p hp k s =
      (Real.log (p : ℝ) : ℂ) *
        (eulerPrimePrimitiveMode p s) ^ (k + 1) := by
  rfl

/-- Rectangular finite prime-power ladder on the Pascal-born prime support. -/
noncomputable def pascalPrimeEulerPrimePowerLogWaveUpTo
    (N K : ℕ) (s : ℂ) : ℂ :=
  ∑ p ∈ pascalPrimeCoordinateSupportUpTo N,
    ∑ k ∈ Finset.range K,
      (Real.log (p : ℝ) : ℂ) * eulerPrimePowerMode p (k + 1) s

@[simp] theorem pascalPrimeEulerPrimePowerLogWaveUpTo_zero
    (N : ℕ) (s : ℂ) :
    pascalPrimeEulerPrimePowerLogWaveUpTo N 0 s = 0 := by
  simp [pascalPrimeEulerPrimePowerLogWaveUpTo]

@[simp] theorem pascalPrimeEulerPrimePowerLogWaveUpTo_one
    (N : ℕ) (s : ℂ) :
    pascalPrimeEulerPrimePowerLogWaveUpTo N 1 s =
      pascalPrimeEulerPrimitiveLogWaveUpTo N s := by
  simp [pascalPrimeEulerPrimePowerLogWaveUpTo,
    pascalPrimeEulerPrimitiveLogWaveUpTo]

@[simp] theorem pascalPrimeEulerPrimePowerLogWaveUpTo_exponent_succ
    (N K : ℕ) (s : ℂ) :
    pascalPrimeEulerPrimePowerLogWaveUpTo N (K + 1) s =
      pascalPrimeEulerPrimePowerLogWaveUpTo N K s +
        ∑ p ∈ pascalPrimeCoordinateSupportUpTo N,
          (Real.log (p : ℝ) : ℂ) *
            eulerPrimePowerMode p (K + 1) s := by
  simp [pascalPrimeEulerPrimePowerLogWaveUpTo, Finset.sum_range_succ,
    Finset.sum_add_distrib]

@[simp] theorem pascalPrimeEulerPrimePowerLogWaveUpTo_prime_succ_sub
    (N K : ℕ) (s : ℂ) :
    pascalPrimeEulerPrimePowerLogWaveUpTo (N + 1) K s -
        pascalPrimeEulerPrimePowerLogWaveUpTo N K s =
      if _h : Nat.Prime (N + 1) then
        ∑ k ∈ Finset.range K,
          (Real.log ((N + 1 : ℕ) : ℝ) : ℂ) *
            eulerPrimePowerMode (N + 1) (k + 1) s
      else 0 := by
  by_cases hp : Nat.Prime (N + 1)
  · have hnot : N + 1 ∉ pascalPrimeCoordinateSupportUpTo N := by
      rw [mem_pascalPrimeCoordinateSupportUpTo_iff]
      omega
    have hlog : Complex.log ((N : ℂ) + 1) =
        (Real.log ((N : ℝ) + 1) : ℂ) := by
      simpa using (Complex.ofReal_log (show 0 ≤ ((N + 1 : ℕ) : ℝ) by positivity)).symm
    simp [pascalPrimeEulerPrimePowerLogWaveUpTo,
      pascalPrimeCoordinateSupportUpTo_succ, hp, hnot, hlog]
  · simp [pascalPrimeEulerPrimePowerLogWaveUpTo,
      pascalPrimeCoordinateSupportUpTo_succ, hp]

end DkMath.RH.CFBRCProjection
