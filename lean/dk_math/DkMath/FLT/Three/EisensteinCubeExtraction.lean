/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Three.EisensteinEuclidean

#print "file: DkMath.FLT.Three.EisensteinCubeExtraction"

namespace DkMath.FLT.Three

open DkMath.NumberTheory.TraceOneQuadratic

/-!
# Coprime cube extraction in the Eisenstein order

The Euclidean structure from the preceding checkpoint supplies a concrete
GCDMonoid.  The element-wise conjugate relative-prime certificate then feeds
Mathlib's generic coprime-power extraction theorem.  Units are retained
explicitly; no unit-sector classification is attempted here.
-/

noncomputable instance traceOneNegOneGCDMonoid :
    GCDMonoid EisensteinInt :=
  EuclideanDomain.gcdMonoid EisensteinInt

/-- Element-wise relative primality makes the concrete gcd a unit. -/
theorem isUnit_gcd_of_eisensteinRelPrime
    {x y : EisensteinInt}
    (h : EisensteinRelPrime x y) :
    IsUnit (gcd x y) := by
  exact h (gcd x y) (gcd_dvd_left x y) (gcd_dvd_right x y)

/-- The stripped beta times its conjugate is the integral cube `B^3`. -/
theorem EisensteinRamifierStrippedPacket.beta_mul_conj_eq_cube
    {a b c : ℕ} (p : EisensteinRamifierStrippedPacket a b c) :
    p.beta * conj p.beta =
      (p.powerSplit.B : EisensteinInt) ^ 3 := by
  rw [traceOne_mul_conj, p.beta_norm]
  change (⟨(p.powerSplit.B : ℤ) ^ 3, 0⟩ : EisensteinInt) =
    (⟨(p.powerSplit.B : ℤ), 0⟩ : EisensteinInt) ^ 3
  ext <;> simp [pow_succ]

/-- Associated-cube extraction with the orientation exposed by Mathlib. -/
theorem associated_cube_of_coprime_mul_eq_cube
    {x y z : EisensteinInt}
    (hcop : IsUnit (gcd x y)) (hpow : x * y = z ^ 3) :
    ∃ gamma : EisensteinInt, Associated x (gamma ^ 3) := by
  rcases exists_associated_pow_of_mul_eq_pow hcop hpow with
    ⟨gamma, hgamma⟩
  exact ⟨gamma, hgamma.symm⟩

/-- Extract an explicit unit times a cube from coprime factors of a cube. -/
theorem exists_unit_mul_cube_of_coprime_mul_eq_cube
    {x y z : EisensteinInt}
    (hcop : IsUnit (gcd x y)) (hpow : x * y = z ^ 3) :
    ∃ epsilon : EisensteinIntˣ,
      ∃ gamma : EisensteinInt,
        x = (epsilon : EisensteinInt) * gamma ^ 3 := by
  rcases exists_associated_pow_of_mul_eq_pow hcop hpow with
    ⟨gamma, u, hu⟩
  refine ⟨u, gamma, ?_⟩
  simpa [mul_comm] using hu.symm

/-- A stripped packet together with its unit-times-cube factorization. -/
structure EisensteinCubeUpToUnitPacket
    (a b c : ℕ) : Type where
  conjugateCoprime : EisensteinConjugateCoprimePacket a b c
  epsilon : EisensteinIntˣ
  gamma : EisensteinInt
  beta_eq :
    conjugateCoprime.stripped.beta =
      (epsilon : EisensteinInt) * gamma ^ 3

/-- Construct the cube-up-to-unit packet from conjugate coprimality. -/
noncomputable def eisensteinCubeUpToUnitPacket_of_conjugateCoprime
    {a b c : ℕ} (p : EisensteinConjugateCoprimePacket a b c) :
    EisensteinCubeUpToUnitPacket a b c := by
  classical
  let hFact :=
    exists_unit_mul_cube_of_coprime_mul_eq_cube
      (x := p.stripped.beta)
      (y := conj p.stripped.beta)
      (z := (p.stripped.powerSplit.B : EisensteinInt))
      (isUnit_gcd_of_eisensteinRelPrime p.relPrime)
      p.stripped.beta_mul_conj_eq_cube
  let epsilon := Classical.choose hFact
  have hEpsilon := Classical.choose_spec hFact
  let gamma := Classical.choose hEpsilon
  have hEq := Classical.choose_spec hEpsilon
  exact ⟨p, epsilon, gamma, hEq⟩

/-- Construct the cube-up-to-unit packet directly from a primitive solution. -/
noncomputable def eisensteinCubeUpToUnitPacket_of_primitive_solution
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b) (hEq : a ^ 3 + b ^ 3 = c ^ 3) :
    EisensteinCubeUpToUnitPacket a b c :=
  eisensteinCubeUpToUnitPacket_of_conjugateCoprime
    (eisensteinConjugateCoprimePacket_of_primitive_solution ha hb hc hab hEq)

end DkMath.FLT.Three
