/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeSqrtRoughMoments
import DkMathTest.NumberTheory.LegendreBlockLocalization

#print "file: DkMathTest.NumberTheory.LegendreSqrtRoughMomentCounts"

namespace DkMathTest.LegendreSqrtRoughMomentCalibration
open DkMath.NumberTheory.Legendre DkMathTest.LegendreBlockLocalization
open DkMathTest.LegendreFreshCost
open scoped BigOperators

set_option maxRecDepth 100000
set_option synthInstance.maxSize 1024

/-- n, P, R, roughI, M2, M3, U. Numerical discovery is checked by the kernel below. -/
abbrev MomentRow := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ

def momentData : Finset MomentRow :=
  {((211, 14, 82, 49, 13, 4, 42) : MomentRow),
   ((503, 22, 169, 105, 24, 7, 81) : MomentRow),
   ((1009, 31, 307, 188, 46, 14, 151) : MomentRow),
   ((1013, 31, 311, 181, 24, 7, 147) : MomentRow),
   ((1019, 31, 312, 196, 28, 9, 135) : MomentRow)}

/-- Complete explicit active inventories, checked once before seat arithmetic. -/
def calibrationActive (n : ℕ) : Finset ℕ :=
  if n = 211 then ⟨([3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199] : List ℕ), by decide⟩ else
  if n = 503 then ⟨([3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499] : List ℕ), by decide⟩ else
  if n = 1009 then ⟨([3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997] : List ℕ), by decide⟩ else
  if n = 1013 then ⟨([3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009] : List ℕ), by decide⟩ else
  if n = 1019 then ⟨([3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013] : List ℕ), by decide⟩ else
  ∅

def calibrationSmall (n : ℕ) : Finset ℕ :=
  if n = 211 then ⟨([3, 5, 7, 11, 13] : List ℕ), by decide⟩ else
  if n = 503 then ⟨([3, 5, 7, 11, 13, 17, 19] : List ℕ), by decide⟩ else
  if n = 1009 then ⟨([3, 5, 7, 11, 13, 17, 19, 23, 29, 31] : List ℕ), by decide⟩ else
  if n = 1013 then ⟨([3, 5, 7, 11, 13, 17, 19, 23, 29, 31] : List ℕ), by decide⟩ else
  if n = 1019 then ⟨([3, 5, 7, 11, 13, 17, 19, 23, 29, 31] : List ℕ), by decide⟩ else
  ∅

/-- Normal form of the existing rough carrier; only its numerical evaluation is diagnostic. -/
def calibrationRough (n : ℕ) : Finset ℕ :=
  ((Finset.Icc 1 (2 * n)).filter (fun r => Nat.Coprime n r ∧ (n ^ 2 + r) % 2 = 1)).filter
    (fun r => ∀ a ∈ calibrationSmall n, ¬a ∣ n ^ 2 + r)

def calibrationSupport (n r : ℕ) : Finset ℕ :=
  (calibrationActive n).filter (fun q => q ∣ n ^ 2 + r)

def calibrationRoughI (n : ℕ) : ℕ :=
  ∑ r ∈ calibrationRough n, (calibrationSupport n r).card

def calibrationM2 (n : ℕ) : ℕ :=
  ∑ r ∈ calibrationRough n, Nat.choose (calibrationSupport n r).card 2

def calibrationM3 (n : ℕ) : ℕ :=
  ∑ r ∈ calibrationRough n, Nat.choose (calibrationSupport n r).card 3

set_option maxHeartbeats 6000000 in
-- Complete prime inventories and the cutoff filters are checked once for the five anchors.
theorem inventories_checked : ∀ t ∈ momentData,
    t.1.Prime ∧ Nat.sqrt t.1 = t.2.1 ∧
    squareAnchorOddActivePrimes t.1 = calibrationActive t.1 ∧
    (calibrationActive t.1).filter (fun p => p ≤ Nat.sqrt t.1) = calibrationSmall t.1 := by
  simp_rw [oddActive_eq_filter_range]
  decide +kernel

set_option maxHeartbeats 20000000 in
-- Only sqrt-rough seats and their moments are reduced, never whole E or whole I.
theorem finite_moments_checked : ∀ t ∈ momentData,
    (calibrationRough t.1).card = t.2.2.1 ∧
    calibrationRoughI t.1 = t.2.2.2.1 ∧
    calibrationM2 t.1 = t.2.2.2.2.1 ∧
    calibrationM3 t.1 = t.2.2.2.2.2.1 := by
  decide +kernel

theorem row_margins_checked : ∀ t ∈ momentData,
    0 < t.1 ∧ t.2.2.2.1 + t.2.2.2.2.2.1 < t.2.2.1 + t.2.2.2.2.1 ∧
    t.2.2.1 + t.2.2.2.2.1 = t.2.2.2.2.2.2 + t.2.2.2.1 + t.2.2.2.2.2.1 := by
  decide +kernel

end DkMathTest.LegendreSqrtRoughMomentCalibration
