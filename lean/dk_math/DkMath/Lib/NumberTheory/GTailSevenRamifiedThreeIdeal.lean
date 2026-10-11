/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.GTailSevenSplitIdeal
import DkMath.Lib.NumberTheory.TraceOneLatticeLanding

#print "file: DkMath.Lib.NumberTheory.GTailSevenRamifiedThreeIdeal"

/-!
# Ramified three in the existing Eisenstein order

The repeated-root kernel is identified by integral lattice landing, and its
square is compared with the scalar ideal using an explicit unit inverse.
No split comaximality, cyclotomic transfer or descent is used.
-/

namespace DkMath.Lib.NumberTheory

open DkMath.NumberTheory.TraceOneQuadratic

/-- The actual repeated root in characteristic three. -/
theorem eisensteinThreeRoot : (2 : ZMod 3) ^ 2 - 2 + 1 = 0 := by decide

/-- The integral ramified generator in the τ²=τ-1 convention. -/
def eisensteinThreeGenerator : TraceOneInt (-1) := 1 + tau (-1)

/-- Literal coordinates fix the generator convention. -/
theorem eisensteinThreeGenerator_eq :
    eisensteinThreeGenerator = (⟨1, 1⟩ : TraceOneInt (-1)) := by decide

/-- The existing integer norm of the generator is three. -/
theorem norm_eisensteinThreeGenerator : norm eisensteinThreeGenerator = 3 := by decide

/-- Squaring gives the scalar three times the integral generator τ. -/
theorem eisensteinThreeGenerator_mul_self :
    eisensteinThreeGenerator * eisensteinThreeGenerator = ofInt (-1) 3 * tau (-1) := by decide

/-- An explicit integral inverse for τ, with the actual ring product. -/
theorem eisenstein_tau_mul_inverse : tau (-1) * (1 - tau (-1)) = 1 := by decide

/-- The scalar three divides the generator square as a ring element. -/
theorem scalar_three_dvd_eisensteinThreeGenerator_square :
    ofInt (-1) 3 ∣ eisensteinThreeGenerator * eisensteinThreeGenerator :=
  ⟨tau (-1), eisensteinThreeGenerator_mul_self⟩

/-- The inverse of τ supplies the reverse generator divisibility. -/
theorem eisensteinThreeGenerator_square_dvd_scalar_three :
    eisensteinThreeGenerator * eisensteinThreeGenerator ∣ ofInt (-1) 3 := by
  refine ⟨1 - tau (-1), ?_⟩
  rw [eisensteinThreeGenerator_mul_self, mul_assoc, eisenstein_tau_mul_inverse, mul_one]

/-- The actual repeated-root kernel in the integral ring. -/
def eisensteinThreeRamifiedIdeal : Ideal (TraceOneInt (-1)) :=
  eisensteinResidueIdeal (2 : ZMod 3) eisensteinThreeRoot

/-- Kernel membership is one integer coordinate congruence, for every signed pair. -/
theorem mem_eisensteinThreeRamifiedIdeal_iff_coordinates (z : TraceOneInt (-1)) :
    z ∈ eisensteinThreeRamifiedIdeal ↔ (3 : ℤ) ∣ z.fst - z.snd := by
  rw [eisensteinThreeRamifiedIdeal, mem_eisensteinResidueIdeal_iff]
  have hcast : ((z.fst - z.snd : ℤ) : ZMod 3) = 0 ↔ (3 : ℤ) ∣ z.fst - z.snd := by
    simpa using (CharP.intCast_eq_zero_iff (ZMod 3) 3 (z.fst - z.snd))
  rw [← hcast]
  simp [eisensteinResidueEval, show (2 : ZMod 3) = -1 by decide,
    sub_eq_add_neg]

/-- The nonzero-norm lattice criterion identifies divisibility by the generator. -/
theorem eisensteinThreeGenerator_dvd_iff_coordinates (z : TraceOneInt (-1)) :
    eisensteinThreeGenerator ∣ z ↔ (3 : ℤ) ∣ z.fst - z.snd := by
  have hn : norm eisensteinThreeGenerator ≠ 0 := by rw [norm_eisensteinThreeGenerator]; norm_num
  have hlanding := traceOne_dvd_iff_norm_dvd_mul_conj_coordinates
    (alpha := z) (beta := eisensteinThreeGenerator) hn
  have hf : (z * conj eisensteinThreeGenerator).fst = 2 * z.fst + z.snd := by
    rw [eisensteinThreeGenerator_eq]
    simp [conj]
    ring
  have hs : (z * conj eisensteinThreeGenerator).snd = -z.fst + z.snd := by
    rw [eisensteinThreeGenerator_eq]
    simp [conj]
    ring
  rw [norm_eisensteinThreeGenerator, hf, hs] at hlanding
  rw [hlanding]
  constructor
  · rintro ⟨_, hsecond⟩
    have hneg : (3 : ℤ) ∣ -(z.fst - z.snd) := by convert hsecond using 1; ring
    exact dvd_neg.mp hneg
  · intro hdiff
    have hthree : (3 : ℤ) ∣ 3 * z.fst := ⟨z.fst, rfl⟩
    constructor
    · convert dvd_sub hthree hdiff using 1; ring
    · convert dvd_neg.mpr hdiff using 1; ring

/-- All elements of the kernel, not merely the selected natural coordinate, are divisible by π. -/
theorem mem_eisensteinThreeRamifiedIdeal_iff_dvd (z : TraceOneInt (-1)) :
    z ∈ eisensteinThreeRamifiedIdeal ↔ eisensteinThreeGenerator ∣ z := by
  rw [mem_eisensteinThreeRamifiedIdeal_iff_coordinates, eisensteinThreeGenerator_dvd_iff_coordinates]

/-- The entire repeated-root kernel is the principal ideal of π. -/
theorem eisensteinThreeRamifiedIdeal_eq_span :
    eisensteinThreeRamifiedIdeal =
      Ideal.span ({eisensteinThreeGenerator} : Set (TraceOneInt (-1))) := by
  ext z
  rw [mem_eisensteinThreeRamifiedIdeal_iff_dvd, Ideal.mem_span_singleton]

/-- The ramified generator belongs to the repeated-root kernel. -/
theorem eisensteinThreeGenerator_mem_ramifiedIdeal :
    eisensteinThreeGenerator ∈ eisensteinThreeRamifiedIdeal := by
  rw [mem_eisensteinThreeRamifiedIdeal_iff_dvd]

/-- The generator square lies in the scalar ideal (3). -/
theorem eisensteinThreeGenerator_square_mem_scalarIdeal :
    eisensteinThreeGenerator * eisensteinThreeGenerator ∈ eisensteinScalarIdeal 3 := by
  change _ ∈ Ideal.span ({ofInt (-1) ((3 : ℕ) : ℤ)} : Set (TraceOneInt (-1)))
  rw [Ideal.mem_span_singleton]
  exact scalar_three_dvd_eisensteinThreeGenerator_square

/-- Mutual integral generator divisibility identifies the square's principal ideal. -/
theorem eisensteinThreeGenerator_square_span_eq_scalarIdeal :
    Ideal.span ({eisensteinThreeGenerator * eisensteinThreeGenerator} : Set (TraceOneInt (-1))) =
      eisensteinScalarIdeal 3 := by
  change Ideal.span ({eisensteinThreeGenerator * eisensteinThreeGenerator} :
    Set (TraceOneInt (-1))) = Ideal.span ({ofInt (-1) 3} : Set (TraceOneInt (-1)))
  apply le_antisymm
  · exact Ideal.span_singleton_le_span_singleton.mpr scalar_three_dvd_eisensteinThreeGenerator_square
  · exact Ideal.span_singleton_le_span_singleton.mpr eisensteinThreeGenerator_square_dvd_scalar_three

/-- The ramified product is the scalar ideal (3), without a comaximality argument. -/
theorem eisensteinThreeRamifiedIdeal_mul_self :
    eisensteinThreeRamifiedIdeal * eisensteinThreeRamifiedIdeal = eisensteinScalarIdeal 3 := by
  calc
    eisensteinThreeRamifiedIdeal * eisensteinThreeRamifiedIdeal =
        Ideal.span ({eisensteinThreeGenerator} : Set (TraceOneInt (-1))) *
          Ideal.span ({eisensteinThreeGenerator} : Set (TraceOneInt (-1))) :=
      congrArg (fun I : Ideal (TraceOneInt (-1)) => I * I) eisensteinThreeRamifiedIdeal_eq_span
    _ = Ideal.span ({eisensteinThreeGenerator * eisensteinThreeGenerator} :
        Set (TraceOneInt (-1))) := Ideal.span_singleton_mul_span_singleton _ _
    _ = eisensteinScalarIdeal 3 := eisensteinThreeGenerator_square_span_eq_scalarIdeal

end DkMath.Lib.NumberTheory
