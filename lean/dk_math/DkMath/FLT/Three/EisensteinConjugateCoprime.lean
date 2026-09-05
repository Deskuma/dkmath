/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Three.EisensteinRamifierStripped

#print "file: DkMath.FLT.Three.EisensteinConjugateCoprime"

namespace DkMath.FLT.Three

open DkMath.NumberTheory.TraceOneQuadratic

/-!
# Eisenstein conjugate coprimality

This module records the element-wise common-divisor certificate for a stripped
Eisenstein factor.  It uses only the explicit norm and conjugation formulas;
no GCDMonoid, PID, or UFD structure is introduced.
-/

/-- Every common divisor in the trace-one Eisenstein ring is a unit. -/
def EisensteinRelPrime (x y : EisensteinInt) : Prop :=
  ∀ d : EisensteinInt, d ∣ x → d ∣ y → IsUnit d

/-- Norm carries ordinary Eisenstein divisibility to integer divisibility. -/
theorem eisenstein_norm_dvd_of_dvd {d x : EisensteinInt} (h : d ∣ x) :
    norm d ∣ norm x := by
  rcases h with ⟨k, hk⟩
  rw [hk, eisenstein_norm_mul]
  exact dvd_mul_right _ _

/-- A norm-one Eisenstein element is a ring unit, with conjugate as inverse. -/
theorem eisenstein_isUnit_of_norm_eq_one {d : EisensteinInt}
    (h : norm d = 1) : IsUnit d := by
  rw [isUnit_iff_dvd_one]
  refine ⟨conj d, ?_⟩
  change (⟨1, 0⟩ : EisensteinInt) = d * conj d
  simpa [h, ofInt] using (traceOne_mul_conj d).symm

/-- A norm minus-one Eisenstein element is a ring unit. -/
theorem eisenstein_isUnit_of_norm_eq_neg_one {d : EisensteinInt}
    (h : norm d = -1) : IsUnit d := by
  rw [isUnit_iff_dvd_one]
  refine ⟨-conj d, ?_⟩
  have hm : d * (-conj d) = -(d * conj d) := mul_neg _ _
  rw [hm, traceOne_mul_conj, h]
  rfl

/-- Norm `1` or `-1` is sufficient for being a unit. -/
theorem eisenstein_isUnit_of_norm_eq_one_or_neg_one {d : EisensteinInt}
    (h : norm d = 1 ∨ norm d = -1) : IsUnit d :=
  h.elim eisenstein_isUnit_of_norm_eq_one eisenstein_isUnit_of_norm_eq_neg_one

/-- The norm of every trace-one Eisenstein integer is nonnegative. -/
theorem eisenstein_norm_nonneg (d : EisensteinInt) : 0 ≤ norm d := by
  rcases d with ⟨r, s⟩
  change 0 ≤ norm (eisensteinCoord r s)
  rw [eisenstein_norm_coords]
  nlinarith [sq_nonneg r, sq_nonneg (r + s), sq_nonneg s]

/-- Subtracting the conjugate isolates the second coordinate. -/
theorem eisenstein_sub_conj_coords (x : EisensteinInt) :
    x - conj x = eisensteinCoord (-x.snd) (2 * x.snd) := by
  rcases x with ⟨r, s⟩
  apply traceOne_ext
  · simp [eisensteinCoord, conj]
  · simp [eisensteinCoord, conj]
    ring

/-- The norm of the conjugate difference is three times the square coordinate. -/
theorem eisenstein_norm_sub_conj (x : EisensteinInt) :
    norm (x - conj x) = 3 * x.snd ^ 2 := by
  rw [eisenstein_sub_conj_coords, eisenstein_norm_coords]
  ring

/-- For a stripped packet, the conjugate-difference norm is `27*A^6`. -/
theorem EisensteinRamifierStrippedPacket.norm_sub_conj_eq
    {a b c : ℕ} (p : EisensteinRamifierStrippedPacket a b c) :
    norm (p.beta - conj p.beta) =
      27 * (p.powerSplit.A : ℤ) ^ 6 := by
  rw [eisenstein_norm_sub_conj, p.beta_snd]
  ring

/-- The two integer masses supplied by a power split are coprime. -/
theorem powerSplit_coprime_B3_threeCube_A6
    {a b c : ℕ} (s : SignedThreeAdicPowerSplit a b c) :
    Nat.Coprime (s.B ^ 3) (3 ^ 3 * s.A ^ 6) := by
  have hB3 : Nat.Coprime s.B 3 := by
    exact (Nat.prime_three.coprime_iff_not_dvd.mpr s.three_not_dvd_B).symm
  have hB3_three : Nat.Coprime (s.B ^ 3) (3 ^ 3) := by
    exact (Nat.Coprime.pow_left 3 hB3).pow_right 3
  have hBA : Nat.Coprime s.B s.A := s.coprime_A_B.symm
  have hB3_A6 : Nat.Coprime (s.B ^ 3) (s.A ^ 6) := by
    exact (Nat.Coprime.pow_left 3 hBA).pow_right 6
  exact hB3_three.mul_right hB3_A6

private theorem norm_eq_one_of_natAbs_eq_one
    {d : EisensteinInt} (h : (norm d).natAbs = 1) : norm d = 1 := by
  have hnonneg : 0 ≤ norm d := eisenstein_norm_nonneg d
  have hcast : ((norm d).natAbs : ℤ) = norm d :=
    Int.natAbs_of_nonneg hnonneg
  rw [← hcast]
  exact_mod_cast h

/-- Every common divisor of a stripped beta and its conjugate is a unit. -/
theorem beta_relPrime_conj
    {a b c : ℕ} (p : EisensteinRamifierStrippedPacket a b c) :
    EisensteinRelPrime p.beta (conj p.beta) := by
  intro d hdbeta hdconj
  have hddiff : d ∣ p.beta - conj p.beta := dvd_sub hdbeta hdconj
  have hnormBeta : norm d ∣ norm p.beta :=
    eisenstein_norm_dvd_of_dvd hdbeta
  have hnormDiff : norm d ∣ norm (p.beta - conj p.beta) :=
    eisenstein_norm_dvd_of_dvd hddiff
  have hdB : (norm d).natAbs ∣ p.powerSplit.B ^ 3 := by
    apply Int.dvd_natCast.mp
    simpa [p.beta_norm] using hnormBeta
  have hdA : (norm d).natAbs ∣ 27 * p.powerSplit.A ^ 6 := by
    apply Int.dvd_natCast.mp
    simpa [p.norm_sub_conj_eq] using hnormDiff
  have hcop := powerSplit_coprime_B3_threeCube_A6 p.powerSplit
  have hone : (norm d).natAbs = 1 := by
    exact Nat.eq_one_of_dvd_coprimes hcop hdB hdA
  exact eisenstein_isUnit_of_norm_eq_one (norm_eq_one_of_natAbs_eq_one hone)

/-- A stripped packet carrying its certified conjugate relative primality. -/
structure EisensteinConjugateCoprimePacket
    (a b c : ℕ) : Type where
  stripped : EisensteinRamifierStrippedPacket a b c
  relPrime : EisensteinRelPrime stripped.beta (conj stripped.beta)

/-- Construct the conjugate-coprime packet from a stripped packet. -/
def eisensteinConjugateCoprimePacket_of_stripped
    {a b c : ℕ} (p : EisensteinRamifierStrippedPacket a b c) :
    EisensteinConjugateCoprimePacket a b c :=
  ⟨p, beta_relPrime_conj p⟩

/-- Construct the conjugate-coprime packet directly from a primitive solution. -/
noncomputable def eisensteinConjugateCoprimePacket_of_primitive_solution
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b) (hEq : a ^ 3 + b ^ 3 = c ^ 3) :
    EisensteinConjugateCoprimePacket a b c :=
  eisensteinConjugateCoprimePacket_of_stripped
    (eisensteinRamifierStrippedPacket_of_primitive_solution ha hb hc hab hEq)

end DkMath.FLT.Three
