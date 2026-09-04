/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Data.Nat.Prime.Basic
import DkMath.CosmicFormula.CosmicFormulaBinom
import DkMath.NumberTheory.Primitive.FinitePrimeWorld

#print "file: DkMath.NumberTheory.Primitive.SquareBody"

/-!
## The natural-number square Body

This file records the generic arithmetic closure used by the Legendre entry
route.  It does not define a Legendre provider: it only says that a point
before the next square is prime when all prime directions up to the anchor
are absent.

The identity at the algebraic source layer is reused through
`CosmicFormulaBinom.cosmic_id_csr'`.  The order and primality arguments begin
only in the natural-number theorems below.
-/

namespace DkMath.NumberTheory.Primitive

open DkMath.CosmicFormulaBinom
open DkMath.NumberTheory.StructuralArithmetic

/-- The unit-one square Body, written in its natural-number normal form. -/
def squareBody (P : ℕ) : ℕ := P ^ 2 + 2 * P

theorem unitSquare_body_eq (P : ℕ) :
    BodyN 2 P 1 = squareBody P := by
  simp only [BodyN]
  rw [GN_eq_sum]
  norm_num [Finset.sum_range_succ, squareBody]
  ring

/-- The square Body ends immediately before the next consecutive square. -/
theorem squareBody_add_one_eq (P : ℕ) :
    squareBody P + 1 = (P + 1) ^ 2 := by
  simp [squareBody]
  ring

/-- The natural square Body is monotone in its anchor. -/
theorem squareBody_mono {q P : ℕ} (h : q ≤ P) :
    squareBody q ≤ squareBody P := by
  calc
    squareBody q = q * (q + 2) := by
      simp [squareBody]
      ring
    _ ≤ P * (P + 2) := by
      exact Nat.mul_le_mul h (Nat.add_le_add_right h 2)
    _ = squareBody P := by
      simp [squareBody]
      ring

/--
Any composite point in the square Body has a prime divisor at most the
anchor.  This is the reusable arithmetic theorem; it does not mention
Legendre's conjecture or a finite prime set.
-/
theorem exists_prime_dvd_le_of_not_prime_of_le_squareBody
    {P m : ℕ} (hm : 1 < m) (hmUpper : m ≤ squareBody P)
    (hmPrime : ¬ Nat.Prime m) :
    ∃ q, Nat.Prime q ∧ q ∣ m ∧ q ≤ P := by
  have hminSq : m.minFac ^ 2 ≤ m :=
    Nat.minFac_sq_le_self (by omega : 0 < m) hmPrime
  have hltNext : m < (P + 1) ^ 2 := by
    calc
      m ≤ squareBody P := hmUpper
      _ < (P + 1) ^ 2 := by rw [← squareBody_add_one_eq P]; omega
  have hminLt : m.minFac < P + 1 := by
    nlinarith [hminSq, hltNext]
  refine ⟨m.minFac, Nat.minFac_prime (by omega : m ≠ 1),
    Nat.minFac_dvd m, ?_⟩
  omega

/--
Inside the square Body, excluding every prime direction up to `P` forces a
prime witness.
-/
theorem prime_of_supportDisjointFrom_le_squareBody
    {P m : ℕ} (hm : 1 < m) (hmUpper : m ≤ squareBody P)
    (hdisj : ∀ ⦃q : ℕ⦄, Nat.Prime q → q ≤ P → ¬ q ∣ m) :
    Nat.Prime m := by
  by_contra hmPrime
  obtain ⟨q, hq, hqd, hqle⟩ :=
    exists_prime_dvd_le_of_not_prime_of_le_squareBody hm hmUpper hmPrime
  exact (hdisj hq hqle) hqd

/--
The canonical bounded prime world supplies the support condition for the
generic square-Body closure theorem.
-/
theorem prime_of_supportDisjointFrom_primeScalesUpTo_le_squareBody
    {P m : ℕ}
    (hm : 1 < m)
    (hmUpper : m ≤ squareBody P)
    (hdisj : SupportDisjointFrom (primeScalesUpTo P) m) :
    Nat.Prime m := by
  exact prime_of_supportDisjointFrom_le_squareBody hm hmUpper
    (supportDisjointFrom_primeScalesUpTo_iff.mp hdisj)

/--
A complete prime support at a coarse anchor P certifies every fine
square-Body world whose anchor q satisfies q ≤ P.
-/
theorem prime_of_supportDisjointFrom_primeScalesUpTo_coarse_of_le_fine_squareBody
    {q P m : ℕ}
    (hqP : q ≤ P)
    (hm : 1 < m)
    (hmUpper : m ≤ squareBody q)
    (hdisj : SupportDisjointFrom (primeScalesUpTo P) m) :
    Nat.Prime m := by
  have hmUpperCoarse : m ≤ squareBody P :=
    hmUpper.trans (squareBody_mono hqP)
  exact prime_of_supportDisjointFrom_primeScalesUpTo_le_squareBody
    hm hmUpperCoarse hdisj

/--
A support-disjoint point in a certified fine square world is not merely
carrying some fresh prime divisor: square certification makes the point
itself prime, hence the point itself is the fresh direction relative to the
complete coarse world.
-/
theorem freshPrimeDirection_self_of_supportDisjointFrom_primeScalesUpTo_coarse_of_le_fine_squareBody
    {q P m : ℕ}
    (hqP : q ≤ P)
    (hm : 1 < m)
    (hmUpper : m ≤ squareBody q)
    (hdisj : SupportDisjointFrom (primeScalesUpTo P) m) :
    FreshPrimeDirection (primeScalesUpTo P) m m := by
  have hmPrime : Nat.Prime m :=
    prime_of_supportDisjointFrom_primeScalesUpTo_coarse_of_le_fine_squareBody
      hqP hm hmUpper hdisj
  have hmNotMem : m ∉ primeScalesUpTo P :=
    hdisj hmPrime (dvd_refl m)
  exact freshPrimeDirection_of_prime_dvd_not_mem
    hmPrime (dvd_refl m) hmNotMem

/-! ### PRIM-C001: the old-times-one-fresh square-Body decomposition -/

/--
A prime strictly above the anchor cannot occur twice in a positive square-Body
point.  The proof uses only the exact endpoint
`squareBody P + 1 = (P + 1)^2`; it is a generic finite arithmetic statement,
not a primitive-origin or Legendre assertion.
-/
theorem not_prime_sq_dvd_of_anchor_lt_of_le_squareBody
    {P m p : ℕ}
    (hm : 0 < m)
    (hmUpper : m ≤ squareBody P)
    (_hp : Nat.Prime p)
    (hlarge : P < p) :
    ¬ p ^ 2 ∣ m := by
  intro hsq
  have hsq_le : p ^ 2 ≤ m := Nat.le_of_dvd hm hsq
  have hanchor : P + 1 ≤ p := by omega
  have hpow : (P + 1) ^ 2 ≤ p ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul hanchor hanchor
  have hbody_lt : squareBody P < (P + 1) ^ 2 := by
    rw [← squareBody_add_one_eq P]
    omega
  omega

/--
Two prime divisors above the anchor must coincide inside a positive
square-Body point.  Thus the square bound controls the number of fresh
directions without enumerating a factorization.
-/
theorem eq_of_large_primes_dvd_le_squareBody
    {P m p q : ℕ}
    (hm : 0 < m)
    (hmUpper : m ≤ squareBody P)
    (hp : Nat.Prime p)
    (hq : Nat.Prime q)
    (hpLarge : P < p)
    (hqLarge : P < q)
    (hpd : p ∣ m)
    (hqd : q ∣ m) :
    p = q := by
  by_contra hne
  have hprod : p * q ∣ m :=
    hp.dvd_mul_of_dvd_ne hne hq hpd hqd
  have hprod_le : p * q ≤ m := Nat.le_of_dvd hm hprod
  have hpAnchor : P + 1 ≤ p := by omega
  have hqAnchor : P + 1 ≤ q := by omega
  have hprod_lower : (P + 1) ^ 2 ≤ p * q := by
    simpa [pow_two] using Nat.mul_le_mul hpAnchor hqAnchor
  have hbody_lt : squareBody P < (P + 1) ^ 2 := by
    rw [← squareBody_add_one_eq P]
    omega
  omega

/--
A prime above `P` dividing `m` is fresh relative to the canonical finite
world `primeScalesUpTo P`.  Here freshness is finite-world membership only;
it does not mean first occurrence in the Zsigmondy or `PrimitiveBeam` sense.
-/
theorem freshPrimeDirection_of_anchor_lt_prime_dvd
    {P m p : ℕ}
    (hp : Nat.Prime p)
    (hlarge : P < p)
    (hpd : p ∣ m) :
    FreshPrimeDirection (primeScalesUpTo P) m p := by
  apply freshPrimeDirection_of_prime_dvd_not_mem hp hpd
  intro hpMem
  have hpLe : p ≤ P := (mem_primeScalesUpTo.mp hpMem).2
  omega

/--
The quotient by a large prime divisor reconstructs the original point,
contains no second copy of that prime, and is coprime to it.  The square-body
hypothesis is used precisely for the depth-one conclusion.
-/
theorem large_prime_cofactor_properties_of_le_squareBody
    {P m p : ℕ}
    (hm : 0 < m)
    (hmUpper : m ≤ squareBody P)
    (hp : Nat.Prime p)
    (hpLarge : P < p)
    (hpd : p ∣ m) :
    p * (m / p) = m ∧
      ¬ p ∣ m / p ∧
      Nat.Coprime p (m / p) := by
  have hprod : p * (m / p) = m := Nat.mul_div_cancel' hpd
  have hnot : ¬ p ∣ m / p := by
    intro hpk
    have hsq : p ^ 2 ∣ p * (m / p) := by
      simpa [pow_two] using Nat.mul_dvd_mul_left p hpk
    rw [hprod] at hsq
    exact not_prime_sq_dvd_of_anchor_lt_of_le_squareBody
      hm hmUpper hp hpLarge hsq
  exact ⟨hprod, hnot, hp.coprime_iff_not_dvd.mpr hnot⟩

/--
After removing a large prime from a positive square-Body point, every prime
in the cofactor belongs to the old finite world.  `PrimeScaleGeneratedBy`
records this prime support only; it does not claim that the cofactor is
squarefree or that its exponents are bounded.
-/
theorem primeScaleGeneratedBy_div_of_large_prime_dvd_le_squareBody
    {P m p : ℕ}
    (hm : 0 < m)
    (hmUpper : m ≤ squareBody P)
    (hp : Nat.Prime p)
    (hpLarge : P < p)
    (hpd : p ∣ m) :
    PrimeScaleGeneratedBy (primeScalesUpTo P) (m / p) := by
  have hprod : p * (m / p) = m := Nat.mul_div_cancel' hpd
  have hk0 : m / p ≠ 0 := by
    intro hk0
    have hm0 : m = 0 := by simpa [hk0] using hprod.symm
    exact (Nat.ne_of_gt hm) hm0
  have hnot : ¬ p ∣ m / p :=
    (large_prime_cofactor_properties_of_le_squareBody
      hm hmUpper hp hpLarge hpd).2.1
  refine ⟨hk0, ?_⟩
  intro q hq hqk
  have hqm : q ∣ m := by
    rw [← hprod]
    exact dvd_mul_of_dvd_right hqk p
  by_cases hqLarge : P < q
  · have hqp : q = p := eq_of_large_primes_dvd_le_squareBody
      hm hmUpper hq hp hqLarge hpLarge hqm hpd
    have hpk : p ∣ m / p := by simpa [hqp] using hqk
    exact False.elim (hnot hpk)
  · have hqLe : q ≤ P := by omega
    exact (mem_primeScalesUpTo).2 ⟨hq, hqLe⟩

/--
Package the generic square-Body split for a specified large prime divisor:
the quotient is old-generated and coprime to the unique fresh direction, and
every other fresh direction is equal to `p`.
-/
theorem squareBody_large_prime_split
    {P m p : ℕ}
    (hm : 0 < m)
    (hmUpper : m ≤ squareBody P)
    (hp : Nat.Prime p)
    (hpLarge : P < p)
    (hpd : p ∣ m) :
    let k := m / p
    p * k = m ∧
    PrimeScaleGeneratedBy (primeScalesUpTo P) k ∧
    Nat.Coprime p k ∧
    FreshPrimeDirection (primeScalesUpTo P) m p ∧
    ∀ ⦃q : ℕ⦄,
      FreshPrimeDirection (primeScalesUpTo P) m q → q = p := by
  have hcof := large_prime_cofactor_properties_of_le_squareBody
    hm hmUpper hp hpLarge hpd
  have hfresh := freshPrimeDirection_of_anchor_lt_prime_dvd hp hpLarge hpd
  have hgen := primeScaleGeneratedBy_div_of_large_prime_dvd_le_squareBody
    hm hmUpper hp hpLarge hpd
  have huniq : ∀ ⦃q : ℕ⦄,
      FreshPrimeDirection (primeScalesUpTo P) m q → q = p := by
    intro q hq
    have hqLarge : P < q := by
      by_contra hqNotLarge
      have hqLe : q ≤ P := by omega
      exact hq.2.2 ((mem_primeScalesUpTo).2 ⟨hq.1, hqLe⟩)
    exact (eq_of_large_primes_dvd_le_squareBody
      hm hmUpper hp hq.1 hpLarge hqLarge hpd hq.2.1).symm
  dsimp
  exact ⟨hcof.1, hgen, hcof.2.2, hfresh, huniq⟩

/--
Every positive point in the square Body is either generated entirely by the
old finite prime world or is old-generated times one unique fresh prime.
Freshness here is relative only to `primeScalesUpTo P`; the theorem does not
assert that a fresh factor exists, nor does it assert primitive origin.
-/
theorem primeScaleGeneratedBy_or_uniqueFresh_split_of_le_squareBody
    {P m : ℕ}
    (hm : 0 < m)
    (hmUpper : m ≤ squareBody P) :
    PrimeScaleGeneratedBy (primeScalesUpTo P) m ∨
      ∃ p k,
        Nat.Prime p ∧
        P < p ∧
        FreshPrimeDirection (primeScalesUpTo P) m p ∧
        p * k = m ∧
        PrimeScaleGeneratedBy (primeScalesUpTo P) k ∧
        Nat.Coprime p k ∧
        (∀ ⦃q : ℕ⦄,
          FreshPrimeDirection (primeScalesUpTo P) m q → q = p) := by
  classical
  by_cases hex : ∃ p, Nat.Prime p ∧ p ∣ m ∧
      p ∉ primeScalesUpTo P
  · obtain ⟨p, hp, hpd, hpNotMem⟩ := hex
    have hpLarge : P < p := by
      by_contra hpNotLarge
      have hpLe : p ≤ P := by omega
      exact hpNotMem ((mem_primeScalesUpTo).2 ⟨hp, hpLe⟩)
    rcases squareBody_large_prime_split hm hmUpper hp hpLarge hpd with
      ⟨hprod, hgen, hcop, hfresh, huniq⟩
    exact Or.inr ⟨p, m / p, hp, hpLarge, hfresh, hprod, hgen, hcop, huniq⟩
  · apply Or.inl
    refine ⟨Nat.ne_of_gt hm, ?_⟩
    intro q hq hqd
    by_contra hqNotMem
    exact hex ⟨q, hq, hqd, hqNotMem⟩

/-! ### PRIM-C002: bounded fresh cofactors -/

/--
The cofactor left after removing a prime `p > P` from a positive square-Body
point is at most the anchor.  This is the strict-boundary statement behind
the small-old-factor normal form: both factors cannot exceed `P` because
`m < (P + 1)^2`.
-/
theorem div_le_anchor_of_large_prime_dvd_le_squareBody
    {P m p : ℕ}
    (_hm : 0 < m)
    (hmUpper : m ≤ squareBody P)
    (_hp : Nat.Prime p)
    (hpLarge : P < p)
    (hpd : p ∣ m) :
    m / p ≤ P := by
  have hprod : p * (m / p) = m := Nat.mul_div_cancel' hpd
  by_contra hkNot
  have hpAnchor : P + 1 ≤ p := by omega
  have hkAnchor : P + 1 ≤ m / p := by omega
  have hprodLower : (P + 1) ^ 2 ≤ p * (m / p) := by
    simpa [pow_two] using Nat.mul_le_mul hpAnchor hkAnchor
  have hbody_lt : squareBody P < (P + 1) ^ 2 := by
    rw [← squareBody_add_one_eq P]
    omega
  omega

/--
Under a specified large-prime split, the complementary cofactor is positive.
The proof uses `p * (m / p) = m`, so no factorization or valuation API is
needed.
-/
theorem positive_div_of_large_prime_dvd_le_squareBody
    {P m p : ℕ}
    (hm : 0 < m)
    (_hmUpper : m ≤ squareBody P)
    (_hp : Nat.Prime p)
    (_hpLarge : P < p)
    (hpd : p ∣ m) :
    0 < m / p := by
  have hprod : p * (m / p) = m := Nat.mul_div_cancel' hpd
  have hk0 : m / p ≠ 0 := by
    intro hk0
    have hm0 : m = 0 := by simpa [hk0] using hprod.symm
    exact (Nat.ne_of_gt hm) hm0
  exact Nat.pos_of_ne_zero hk0

/--
For an old prime `q ≤ P`, divisibility is preserved exactly when the unique
large prime factor is removed.  Thus the small cofactor has precisely the
old prime support of the original point; its old prime exponents may still
be arbitrary.
-/
theorem old_prime_dvd_iff_dvd_large_prime_cofactor
    {P m p q : ℕ}
    (_hm : 0 < m)
    (_hmUpper : m ≤ squareBody P)
    (hp : Nat.Prime p)
    (hpLarge : P < p)
    (hpd : p ∣ m)
    (hq : Nat.Prime q)
    (hqLe : q ≤ P) :
    q ∣ m ↔ q ∣ m / p := by
  have hprod : p * (m / p) = m := Nat.mul_div_cancel' hpd
  have hqp : q ≠ p := by omega
  constructor
  · intro hqm
    have hqm' : q ∣ p * (m / p) := by
      rw [hprod]
      exact hqm
    rcases (Nat.Prime.dvd_mul hq).mp hqm' with hqpdiv | hqk
    · have hqeqp : q = p :=
        ((Nat.dvd_prime hp).mp hqpdiv).resolve_left hq.ne_one
      exact False.elim (hqp hqeqp)
    · exact hqk
  · intro hqk
    rw [← hprod]
    exact dvd_mul_of_dvd_right hqk p

/--
The PRIM-C001 specified split with the stronger information that its
old-generated cofactor satisfies `0 < k ≤ P`.  This remains a finite-world
freshness theorem, not a Zsigmondy or Legendre theorem.
-/
theorem squareBody_large_prime_small_cofactor_split
    {P m p : ℕ}
    (hm : 0 < m)
    (hmUpper : m ≤ squareBody P)
    (hp : Nat.Prime p)
    (hpLarge : P < p)
    (hpd : p ∣ m) :
    let k := m / p
    p * k = m ∧
    0 < k ∧
    k ≤ P ∧
    PrimeScaleGeneratedBy (primeScalesUpTo P) k ∧
    Nat.Coprime p k ∧
    FreshPrimeDirection (primeScalesUpTo P) m p ∧
    (∀ ⦃q : ℕ⦄,
      FreshPrimeDirection (primeScalesUpTo P) m q → q = p) := by
  rcases squareBody_large_prime_split hm hmUpper hp hpLarge hpd with
    ⟨hprod, hgen, hcop, hfresh, huniq⟩
  have hkpos := positive_div_of_large_prime_dvd_le_squareBody
    hm hmUpper hp hpLarge hpd
  have hkLe := div_le_anchor_of_large_prime_dvd_le_squareBody
    hm hmUpper hp hpLarge hpd
  dsimp
  exact ⟨hprod, hkpos, hkLe, hgen, hcop, hfresh, huniq⟩

/--
For a specified fresh split, the point is prime exactly when the bounded
cofactor is `1`.  The forward implication uses that a prime has no proper
prime divisor; the reverse implication is the reconstruction equation.
-/
theorem prime_iff_large_prime_cofactor_eq_one
    {P m p : ℕ}
    (_hm : 0 < m)
    (_hmUpper : m ≤ squareBody P)
    (hp : Nat.Prime p)
    (_hpLarge : P < p)
    (hpd : p ∣ m) :
    Nat.Prime m ↔ m / p = 1 := by
  have hprod : p * (m / p) = m := Nat.mul_div_cancel' hpd
  constructor
  · intro hmPrime
    have hpm : p = m :=
      ((Nat.dvd_prime hmPrime).mp hpd).resolve_left hp.ne_one
    simpa [hpm] using Nat.div_self hmPrime.pos
  · intro hk
    have hmp : m = p := by simpa [hk] using hprod.symm
    simpa [hmp] using hp

/--
If a positive square-Body point with a specified fresh divisor is composite,
its cofactor is genuinely nontrivial: `2 ≤ m / p ≤ P`.
-/
theorem two_le_large_prime_cofactor_of_not_prime
    {P m p : ℕ}
    (hm : 0 < m)
    (hmUpper : m ≤ squareBody P)
    (hp : Nat.Prime p)
    (hpLarge : P < p)
    (hpd : p ∣ m)
    (hmPrime : ¬ Nat.Prime m) :
    2 ≤ m / p := by
  have hkpos := positive_div_of_large_prime_dvd_le_squareBody
    hm hmUpper hp hpLarge hpd
  have hkOne : m / p ≠ 1 := by
    intro hk
    exact hmPrime ((prime_iff_large_prime_cofactor_eq_one
      hm hmUpper hp hpLarge hpd).2 hk)
  omega

/--
The global PRIM-C001 dichotomy with the sharper small-cofactor normal form:
either `m` is entirely old-generated, or `m = p * k` with `0 < k ≤ P`,
old-generated `k`, and one unique fresh prime `p > P`.  The theorem is
generic Primitive structure and makes no assertion of fresh-prime existence
beyond the second branch of this disjunction.
-/
theorem primeScaleGeneratedBy_or_uniqueFresh_small_split_of_le_squareBody
    {P m : ℕ}
    (hm : 0 < m)
    (hmUpper : m ≤ squareBody P) :
    PrimeScaleGeneratedBy (primeScalesUpTo P) m ∨
      ∃ p k,
        Nat.Prime p ∧
        P < p ∧
        0 < k ∧
        k ≤ P ∧
        FreshPrimeDirection (primeScalesUpTo P) m p ∧
        p * k = m ∧
        PrimeScaleGeneratedBy (primeScalesUpTo P) k ∧
        Nat.Coprime p k ∧
        (∀ ⦃q : ℕ⦄,
          FreshPrimeDirection (primeScalesUpTo P) m q → q = p) := by
  rcases primeScaleGeneratedBy_or_uniqueFresh_split_of_le_squareBody
      hm hmUpper with hgen | ⟨p, k, hp, hpLarge, hfresh, hprod, hkgen, hcop, huniq⟩
  · exact Or.inl hgen
  · have hpd : p ∣ m := by
      rw [← hprod]
      exact dvd_mul_right p k
    have hkEq : k = m / p :=
      Nat.eq_of_mul_eq_mul_left hp.pos
        (hprod.trans (Nat.mul_div_cancel' hpd).symm)
    have hkpos := positive_div_of_large_prime_dvd_le_squareBody
      hm hmUpper hp hpLarge hpd
    have hkLe := div_le_anchor_of_large_prime_dvd_le_squareBody
      hm hmUpper hp hpLarge hpd
    have hkpos' : 0 < k := by simpa [hkEq] using hkpos
    have hkLe' : k ≤ P := by simpa [hkEq] using hkLe
    exact Or.inr ⟨p, k, hp, hpLarge, hkpos', hkLe', hfresh, hprod,
      hkgen, hcop, huniq⟩

end DkMath.NumberTheory.Primitive
