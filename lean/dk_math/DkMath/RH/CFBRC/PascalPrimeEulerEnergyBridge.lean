/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PascalPrimeCoordinateDecoder
import DkMath.RH.EulerZeta
import DkMath.RH.CFBRC.PrimeMirrorFiniteEnergy
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.PascalPrimeEulerEnergyBridge"

/-!
# Pascal–Euler–prime-mirror finite bridge

The Pascal birth decoder supplies one finite prime support to two different
observables: a finite Euler product and a positive prime-mirror log energy.
The bridge records their common prime birth events and `log p` coordinates;
it does not identify the multiplicative Euler product with the additive
energy, and it does not introduce prime-power or analytic von Mangoldt data.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.NumberTheory
open DkMath.RH.EulerZeta

/-- Finite Euler product over the prime coordinates born by Pascal rows up to `N`. -/
noncomputable def pascalPrimeEulerProductUpTo (N : ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ pascalPrimeCoordinateSupportUpTo N, eulerZetaFactor p s

/-- Euler factor contributed by the birth event at row `n`; non-prime rows are neutral. -/
noncomputable def pascalPrimeEulerBirthFactor (n : ℕ) (s : ℂ) : ℂ :=
  if Nat.Prime n then eulerZetaFactor n s else 1

/-- The finite Euler product updates by exactly the new prime birth factor. -/
@[simp] theorem pascalPrimeEulerProductUpTo_succ (N : ℕ) (s : ℂ) :
    pascalPrimeEulerProductUpTo (N + 1) s =
      pascalPrimeEulerProductUpTo N s * pascalPrimeEulerBirthFactor (N + 1) s := by
  by_cases hp : Nat.Prime (N + 1)
  · rw [pascalPrimeEulerBirthFactor, ite_eq_left hp]
    simp only [pascalPrimeEulerProductUpTo]
    have hnot : N + 1 ∉ pascalPrimeCoordinateSupportUpTo N := by
      rw [mem_pascalPrimeCoordinateSupportUpTo_iff]
      omega
    simp [pascalPrimeCoordinateSupportUpTo_succ, hp, hnot]
    ring
  · rw [pascalPrimeEulerBirthFactor, ite_eq_right hp]
    simp only [pascalPrimeEulerProductUpTo]
    simp [pascalPrimeCoordinateSupportUpTo_succ, hp]

/-- Pascal support reindexed by the subtype of natural prime numbers. -/
noncomputable def pascalPrimeEulerSubtypeSupportUpTo
    (N : ℕ) : Finset {p // Nat.Prime p} :=
  (pascalPrimeCoordinateSupportUpTo N).attach.map
    ⟨fun p => ⟨p.1, (mem_pascalPrimeCoordinateSupportUpTo_iff.mp p.2).1⟩,
      by intro p q h
         exact Subtype.ext
           (congrArg (fun x : {p // Nat.Prime p} => x.1) h)⟩

/-- A subtype prime belongs to the lifted support exactly when it is at most `N`. -/
@[simp]
theorem mem_pascalPrimeEulerSubtypeSupportUpTo_iff
    {p : {p // Nat.Prime p}} {N : ℕ} :
    p ∈ pascalPrimeEulerSubtypeSupportUpTo N ↔ p.1 ≤ N := by
  constructor
  · intro h
    rcases Finset.mem_map.mp h with ⟨q, hq, rfl⟩
    exact (mem_pascalPrimeCoordinateSupportUpTo_iff.mp q.2).2
  · intro hpN
    have hnat : p.1 ∈ pascalPrimeCoordinateSupportUpTo N :=
      mem_pascalPrimeCoordinateSupportUpTo_iff.mpr ⟨p.2, hpN⟩
    refine Finset.mem_map.mpr ⟨⟨p.1, hnat⟩, by simp, ?_⟩
    rfl

/-- The Nat-indexed product and the existing subtype-indexed Euler product agree. -/
theorem pascalPrimeEulerProductUpTo_eq_eulerZetaFinite
    (N : ℕ) (s : ℂ) :
    pascalPrimeEulerProductUpTo N s =
      eulerZetaFinite (pascalPrimeEulerSubtypeSupportUpTo N) s := by
  simp only [pascalPrimeEulerProductUpTo, eulerZetaFinite,
    pascalPrimeEulerSubtypeSupportUpTo]
  rw [Finset.prod_map]
  convert (Finset.prod_attach (pascalPrimeCoordinateSupportUpTo N)
      (fun p : ℕ => eulerZetaFactor p s)).symm using 1
  apply Finset.prod_congr rfl
  intro x hx
  rfl

/-- Finite prime-mirror log energy on the same Pascal-born support. -/
noncomputable def pascalPrimeMirrorLogEnergyUpTo (N : ℕ) (s : ℂ) : ℝ :=
  ∑ p ∈ pascalPrimeCoordinateSupportUpTo N,
    Real.log (p : ℝ) * primeMirrorOffsetGapAt p s

/-- The Pascal energy is the generic finite mirror energy with weight `log p`. -/
theorem pascalPrimeMirrorLogEnergyUpTo_eq_primeMirrorEnergyAt
    (N : ℕ) (s : ℂ) :
    pascalPrimeMirrorLogEnergyUpTo N s =
      primeMirrorEnergyAt (pascalPrimeCoordinateSupportUpTo N)
        (fun p => Real.log (p : ℝ)) s := by
  simp [primeMirrorEnergyAt, primeMirrorEnergy,
    pascalPrimeMirrorLogEnergyUpTo, primeMirrorOffsetGapAt]

/-- Every prime coordinate in the Pascal support is a genuinely nonconstant mode. -/
theorem one_lt_of_mem_pascalPrimeCoordinateSupportUpTo
    {p N : ℕ}
    (hp : p ∈ pascalPrimeCoordinateSupportUpTo N) :
    1 < p := by
  exact (mem_pascalPrimeCoordinateSupportUpTo_iff.mp hp).1.one_lt

/-- The logarithmic weight of every Pascal-supported prime is strictly positive. -/
theorem log_pos_of_mem_pascalPrimeCoordinateSupportUpTo
    {p N : ℕ}
    (hp : p ∈ pascalPrimeCoordinateSupportUpTo N) :
    0 < Real.log (p : ℝ) := by
  exact Real.log_pos (by exact_mod_cast one_lt_of_mem_pascalPrimeCoordinateSupportUpTo hp)

/-- Pascal prime-mirror log energy is nonnegative at every complex point. -/
theorem pascalPrimeMirrorLogEnergyUpTo_nonneg
    (N : ℕ) (s : ℂ) :
    0 ≤ pascalPrimeMirrorLogEnergyUpTo N s := by
  rw [pascalPrimeMirrorLogEnergyUpTo_eq_primeMirrorEnergyAt]
  apply primeMirrorEnergy_nonneg
  intro p hp
  exact (log_pos_of_mem_pascalPrimeCoordinateSupportUpTo hp).le

/-- For `N ≥ 2`, zero Pascal energy is equivalent to lying on the critical line. -/
theorem pascalPrimeMirrorLogEnergyUpTo_eq_zero_iff_re_eq_half
    {N : ℕ} (hN : 2 ≤ N) (s : ℂ) :
    pascalPrimeMirrorLogEnergyUpTo N s = 0 ↔
      s.re = (1 : ℝ) / 2 := by
  rw [pascalPrimeMirrorLogEnergyUpTo_eq_primeMirrorEnergyAt]
  apply primeMirrorEnergyAt_eq_zero_iff_re_eq_half
  · refine ⟨2, ?_⟩
    exact (mem_pascalPrimeCoordinateSupportUpTo_iff.mpr ⟨Nat.prime_two, hN⟩)
  · intro p hp
    exact one_lt_of_mem_pascalPrimeCoordinateSupportUpTo hp
  · intro p hp
    exact log_pos_of_mem_pascalPrimeCoordinateSupportUpTo hp

/-- For `N ≥ 2`, the Pascal energy is positive away from the critical line. -/
theorem pascalPrimeMirrorLogEnergyUpTo_pos_of_re_ne_half
    {N : ℕ} (hN : 2 ≤ N) {s : ℂ}
    (hre : s.re ≠ (1 : ℝ) / 2) :
    0 < pascalPrimeMirrorLogEnergyUpTo N s := by
  rw [pascalPrimeMirrorLogEnergyUpTo_eq_primeMirrorEnergyAt]
  apply primeMirrorEnergyAt_pos_of_re_ne_half
  · refine ⟨2, ?_⟩
    exact (mem_pascalPrimeCoordinateSupportUpTo_iff.mpr ⟨Nat.prime_two, hN⟩)
  · intro p hp
    exact one_lt_of_mem_pascalPrimeCoordinateSupportUpTo hp
  · intro p hp
    exact log_pos_of_mem_pascalPrimeCoordinateSupportUpTo hp
  · exact hre

/-- The energy difference at a successor cutoff is the new birth mass times its Gap. -/
@[simp]
theorem pascalPrimeMirrorLogEnergyUpTo_succ_sub (N : ℕ) (s : ℂ) :
    pascalPrimeMirrorLogEnergyUpTo (N + 1) s -
        pascalPrimeMirrorLogEnergyUpTo N s =
      pascalPrimeBirthLogMass (N + 1) *
        primeMirrorOffsetGapAt (N + 1) s := by
  by_cases hp : Nat.Prime (N + 1)
  · have hnot : N + 1 ∉ pascalPrimeCoordinateSupportUpTo N := by
      rw [mem_pascalPrimeCoordinateSupportUpTo_iff]
      omega
    simp [pascalPrimeBirthLogMass_eq, pascalPrimeCoordinateSupportUpTo_succ,
      pascalPrimeMirrorLogEnergyUpTo, hp, hnot]
  · simp [pascalPrimeBirthLogMass_eq, pascalPrimeCoordinateSupportUpTo_succ,
      pascalPrimeMirrorLogEnergyUpTo, hp]

/-- Additive form of the successor energy update. -/
@[simp]
theorem pascalPrimeMirrorLogEnergyUpTo_succ_eq (N : ℕ) (s : ℂ) :
    pascalPrimeMirrorLogEnergyUpTo (N + 1) s =
      pascalPrimeMirrorLogEnergyUpTo N s +
        pascalPrimeBirthLogMass (N + 1) *
          primeMirrorOffsetGapAt (N + 1) s := by
  linarith [pascalPrimeMirrorLogEnergyUpTo_succ_sub N s]

end DkMath.RH.CFBRCProjection
