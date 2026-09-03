/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Data.Nat.Prime.Basic
import DkMath.NumberTheory.GNRepresentationBounds

#print "file: DkMath.NumberTheory.GNDegreeFactorization"

namespace DkMath.NumberTheory

open DkMath.CosmicFormulaBinom

/-!
## Composite-degree factorization of GN

The cosmic-formula identity makes the GN value at a composite degree
factor through the two degree factors.  In the positive region both factors
are nontrivial, so a prime GN value can only occur at a prime degree.

This is a necessary-condition API.  It does not assert that prime degree is
sufficient for primality of a GN value.
-/

/-- The GN value at a product degree factors by applying the cosmic identity twice. -/
theorem GN_mul_degree
    {a b x u : ℕ}
    (hx : 0 < x) :
    DkMath.CosmicFormulaBinom.GN (a * b) x u =
      DkMath.CosmicFormulaBinom.GN a x u *
        DkMath.CosmicFormulaBinom.GN b
          (x * DkMath.CosmicFormulaBinom.GN a x u) (u ^ a) := by
  let A := DkMath.CosmicFormulaBinom.GN a x u
  let B := DkMath.CosmicFormulaBinom.GN b (x * A) (u ^ a)
  have ha : (x + u) ^ a = x * A + u ^ a := by
    simpa [A] using
      (DkMath.CosmicFormulaBinom.cosmic_id_csr' (R := ℕ) a x u)
  have hb : (x * A + u ^ a) ^ b = (x * A) * B + (u ^ a) ^ b := by
    simpa [B] using
      (DkMath.CosmicFormulaBinom.cosmic_id_csr' (R := ℕ) b (x * A) (u ^ a))
  have hab : (x + u) ^ (a * b) =
      x * DkMath.CosmicFormulaBinom.GN (a * b) x u + u ^ (a * b) := by
    exact DkMath.CosmicFormulaBinom.cosmic_id_csr' (R := ℕ) (a * b) x u
  have hsum :
      x * DkMath.CosmicFormulaBinom.GN (a * b) x u + u ^ (a * b) =
        (x * A) * B + u ^ (a * b) := by
    calc
      x * DkMath.CosmicFormulaBinom.GN (a * b) x u + u ^ (a * b) =
          (x + u) ^ (a * b) := hab.symm
      _ = ((x + u) ^ a) ^ b := by rw [pow_mul]
      _ = (x * A + u ^ a) ^ b := by rw [ha]
      _ = (x * A) * B + (u ^ a) ^ b := hb
      _ = (x * A) * B + u ^ (a * b) := by rw [pow_mul]
  have hfactor :
      x * DkMath.CosmicFormulaBinom.GN (a * b) x u = (x * A) * B :=
    Nat.add_right_cancel hsum
  have hfactor' :
      x * DkMath.CosmicFormulaBinom.GN (a * b) x u = x * (A * B) := by
    simpa [Nat.mul_assoc] using hfactor
  have hcancel :
      DkMath.CosmicFormulaBinom.GN (a * b) x u = A * B :=
    Nat.eq_of_mul_eq_mul_left hx hfactor'
  simpa [A, B] using hcancel

private lemma one_lt_GN_of_two_le
    {d x u : ℕ}
    (hd : 2 ≤ d) (hx : 0 < x) (hu : 0 < u) :
    1 < DkMath.CosmicFormulaBinom.GN d x u := by
  have hfloor := two_pow_sub_one_le_GN (d := d) (x := x) (u := u) hx hu
  have hpow : 4 ≤ 2 ^ d := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
  omega

/-- At a composite degree, both positive GN factors are strictly greater than one. -/
theorem one_lt_factors_of_composite_degree
    {a b x u : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hx : 0 < x) (hu : 0 < u) :
    1 < DkMath.CosmicFormulaBinom.GN a x u ∧
      1 < DkMath.CosmicFormulaBinom.GN b
        (x * DkMath.CosmicFormulaBinom.GN a x u) (u ^ a) := by
  have hA : 1 < DkMath.CosmicFormulaBinom.GN a x u :=
    one_lt_GN_of_two_le ha hx hu
  have hApos : 0 < DkMath.CosmicFormulaBinom.GN a x u := by omega
  have hxA : 0 < x * DkMath.CosmicFormulaBinom.GN a x u :=
    Nat.mul_pos hx hApos
  have hua : 0 < u ^ a := Nat.pow_pos hu
  exact ⟨hA, one_lt_GN_of_two_le hb hxA hua⟩

/-- A positive GN value at a genuinely composite degree is not prime. -/
theorem not_prime_GN_of_mul_degree
    {a b x u : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hx : 0 < x) (hu : 0 < u) :
    ¬ Nat.Prime (DkMath.CosmicFormulaBinom.GN (a * b) x u) := by
  rcases one_lt_factors_of_composite_degree ha hb hx hu with ⟨hA, hB⟩
  rw [GN_mul_degree hx]
  exact Nat.not_prime_mul (Nat.ne_of_gt hA) (Nat.ne_of_gt hB)

/-- If a positive GN value is prime, its degree is prime. -/
theorem prime_degree_of_prime_GN
    {d x u : ℕ}
    (hd : 2 ≤ d)
    (hx : 0 < x) (hu : 0 < u)
    (hGN : Nat.Prime (DkMath.CosmicFormulaBinom.GN d x u)) :
    Nat.Prime d := by
  by_contra hdp
  rcases (Nat.not_prime_iff_exists_mul_eq hd).mp hdp with
    ⟨a, b, ha_lt, hb_lt, hab⟩
  have ha0 : a ≠ 0 := by
    intro ha0
    subst a
    simp at hab
    omega
  have hb0 : b ≠ 0 := by
    intro hb0
    subst b
    simp at hab
    omega
  have ha1 : a ≠ 1 := by
    intro ha1
    subst a
    simp at hab
    omega
  have hb1 : b ≠ 1 := by
    intro hb1
    subst b
    simp at hab
    omega
  have ha2 : 2 ≤ a := by omega
  have hb2 : 2 ≤ b := by omega
  have htarget :
      Nat.Prime (DkMath.CosmicFormulaBinom.GN (a * b) x u) := by
    rw [hab]
    exact hGN
  exact (not_prime_GN_of_mul_degree ha2 hb2 hx hu) htarget

/-- A positive representation of a prime target has prime degree. -/
theorem GNPositiveRepresentation.degree_prime_of_target_prime
    {p d x u : ℕ}
    (hrep : GNPositiveRepresentation p d x u)
    (hp : Nat.Prime p) :
    Nat.Prime d := by
  rcases hrep with ⟨hd, hx, hu, hvalue⟩
  have hGN : Nat.Prime (DkMath.CosmicFormulaBinom.GN d x u) := by
    rw [hvalue]
    exact hp
  exact prime_degree_of_prime_GN hd hx hu hGN

/-! ### Lightweight regression anchors -/

example :
    DkMath.CosmicFormulaBinom.GN (2 * 3) 1 1 =
      DkMath.CosmicFormulaBinom.GN 2 1 1 *
        DkMath.CosmicFormulaBinom.GN 3
          (1 * DkMath.CosmicFormulaBinom.GN 2 1 1) (1 ^ 2) := by
  simpa using (GN_mul_degree (a := 2) (b := 3) (x := 1) (u := 1) (by norm_num))

example :
    ¬ Nat.Prime (DkMath.CosmicFormulaBinom.GN (2 * 3) 1 1) := by
  exact not_prime_GN_of_mul_degree (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end DkMath.NumberTheory
