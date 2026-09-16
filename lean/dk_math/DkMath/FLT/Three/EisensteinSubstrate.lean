/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Three.CubicValuationDepth
import DkMath.NumberTheory.TraceOneQuadratic

#print "file: DkMath.FLT.Three.EisensteinSubstrate"

namespace DkMath.FLT.Three

open DkMath.CosmicFormulaBinom
open DkMath.FLT
open DkMath.FLT.PetalDetect
open DkMath.NumberTheory
open DkMath.NumberTheory.GcdNext
open DkMath.NumberTheory.TraceOneQuadratic

/-!
## Production Eisenstein coordinate substrate

The concrete ring used here is `TraceOneInt (-1)`, whose basis element
`tau (-1)` satisfies `tau^2 = tau - 1`.  This is the trace-one convention;
it is not the classical `omega^2 + omega + 1 = 0` basis.  No Euclidean,
principal-ideal, or unique-factorization structure is asserted here.
-/

/-- The concrete trace-one coordinate ring used by the FLT3 substrate. -/
abbrev EisensteinInt := TraceOneInt (-1)

/-- Coordinate constructor for `r + s * tau (-1)`. -/
def eisensteinCoord (r s : ℤ) : EisensteinInt := ⟨r, s⟩

/-- The trace-one basis element. -/
def eisensteinTau : EisensteinInt := tau (-1)

/-- The trace-one basis equation `tau^2 = tau - 1`. -/
theorem eisenstein_tau_sq : eisensteinTau ^ 2 = eisensteinTau - 1 := by
  change tau (-1) * tau (-1) = tau (-1) - 1
  rw [traceOne_tau_sq]
  ext <;> norm_num [tau, ofInt]

/-- Conjugation in coordinates: `(r + s * tau)̄ = (r+s) - s * tau`. -/
theorem eisenstein_conj_coords (r s : ℤ) :
    conj (eisensteinCoord r s) = eisensteinCoord (r + s) (-s) := by
  rfl

/-- The positive-definite trace-one norm in coordinates. -/
theorem eisenstein_norm_coords (r s : ℤ) :
    norm (eisensteinCoord r s) = r ^ 2 + r * s + s ^ 2 := by
  exact traceOneNorm_neg_one r s

/-- Norm multiplicativity on the concrete coordinate ring. -/
theorem eisenstein_norm_mul (x y : EisensteinInt) :
    norm (x * y) = norm x * norm y := by
  exact traceOne_norm_mul x y

/-- The basis element has norm `1`. -/
theorem eisenstein_tau_norm : norm eisensteinTau = 1 := by
  change norm (eisensteinCoord 0 1) = 1
  rw [eisenstein_norm_coords]
  norm_num

/-- The basis element has cube `-1`. -/
theorem eisenstein_tau_cube : eisensteinTau ^ 3 = -1 := by
  calc
    eisensteinTau ^ 3 = eisensteinTau ^ 2 * eisensteinTau := by ring
    _ = (eisensteinTau - 1) * eisensteinTau := by rw [eisenstein_tau_sq]
    _ = -1 := by
      rw [sub_mul, one_mul, ← pow_two, eisenstein_tau_sq]
      ring

/-- The basis element has sixth power `1`. -/
theorem eisenstein_tau_sixth : eisensteinTau ^ 6 = 1 := by
  calc
    eisensteinTau ^ 6 = (eisensteinTau ^ 3) ^ 2 := by ring
    _ = (-1 : EisensteinInt) ^ 2 := by rw [eisenstein_tau_cube]
    _ = 1 := by ring

/-- The ramifier candidate above `3` in the trace-one convention. -/
def eisensteinRamifier : EisensteinInt := 1 + eisensteinTau

/-- The ramifier candidate has norm `3`. -/
theorem eisenstein_ramifier_norm : norm eisensteinRamifier = 3 := by
  change norm (eisensteinCoord 1 1) = 3
  rw [eisenstein_norm_coords]
  norm_num

/-- The ramifier square identity `lambda^2 = 3 * tau`. -/
theorem eisenstein_ramifier_sq :
    eisensteinRamifier ^ 2 = 3 * eisensteinTau := by
  change (⟨1, 1⟩ : TraceOneInt (-1)) ^ 2 =
    (⟨3, 0⟩ : TraceOneInt (-1)) * ⟨0, 1⟩
  ext <;> norm_num [pow_two, DkMath.NumberTheory.TraceOneQuadratic.mul]

/-- The embedded norm identity `lambda * conjugate lambda = 3`. -/
theorem eisenstein_ramifier_mul_conj :
    eisensteinRamifier * conj eisensteinRamifier = 3 := by
  rw [traceOne_mul_conj, eisenstein_ramifier_norm]
  rfl

/-- Cubing coordinates in the trace-one basis. -/
theorem eisenstein_cube_coords (r s : ℤ) :
    (eisensteinCoord r s) ^ 3 =
      eisensteinCoord
        (r ^ 3 - 3 * r * s ^ 2 - s ^ 3)
        (3 * r * s * (r + s)) := by
  change (⟨r, s⟩ : TraceOneInt (-1)) ^ 3 =
    ⟨r ^ 3 - 3 * r * s ^ 2 - s ^ 3, 3 * r * s * (r + s)⟩
  ext <;>
    simp [pow_succ] <;>
    ring

/-- The second coordinate of a cube, in the exact sign convention used here. -/
theorem eisenstein_cube_snd (r s : ℤ) :
    ((eisensteinCoord r s) ^ 3).snd = 3 * r * s * (r + s) := by
  rw [eisenstein_cube_coords]
  rfl

/-- The natural FLT3 quadratic form is the norm of `c + b * tau`. -/
theorem eisenstein_norm_nat_coords (c b : ℕ) :
    norm (eisensteinCoord (c : ℤ) (b : ℤ)) =
      (DkMath.FLT.PetalDetect.S0_nat c b : ℤ) := by
  rw [eisenstein_norm_coords]
  simp [DkMath.FLT.PetalDetect.S0_nat]

private lemma GN_three_sub_eq_S0_nat_of_le
    {c b : ℕ} (hbc : b ≤ c) :
    DkMath.CosmicFormulaBinom.GN 3 (c - b) b =
      DkMath.FLT.PetalDetect.S0_nat c b := by
  by_cases hneq : b = c
  · subst c
    rw [GN_three_explicit]
    simp [DkMath.FLT.PetalDetect.S0_nat]
    ring
  · exact GN_three_sub_eq_S0_nat (lt_of_le_of_ne hbc hneq)

/-- The cubic GN shell is the same integer as the Eisenstein norm. -/
theorem gn_three_sub_eq_eisenstein_norm_nat_coords
    {c b : ℕ} (hbc : b ≤ c) :
    ((DkMath.CosmicFormulaBinom.GN 3 (c - b) b : ℕ) : ℤ) =
      norm (eisensteinCoord (c : ℤ) (b : ℤ)) := by
  have hGN : DkMath.CosmicFormulaBinom.GN 3 (c - b) b =
      DkMath.FLT.PetalDetect.S0_nat c b :=
    GN_three_sub_eq_S0_nat_of_le hbc
  calc
    ((DkMath.CosmicFormulaBinom.GN 3 (c - b) b : ℕ) : ℤ) =
        (DkMath.FLT.PetalDetect.S0_nat c b : ℤ) := by rw [hGN]
    _ = norm (eisensteinCoord (c : ℤ) (b : ℤ)) :=
      (eisenstein_norm_nat_coords c b).symm

end DkMath.FLT.Three
