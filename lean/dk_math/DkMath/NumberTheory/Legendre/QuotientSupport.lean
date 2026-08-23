/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.NumberTheory.Legendre.Quotient

#print "file: DkMath.NumberTheory.Legendre.QuotientSupport"

/-!
## QuotientSupport

Quotient co-support, direction/depth dichotomy, and Primitive-direction bridges.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open scoped BigOperators

/-!
### PRIM-L015: quotient co-support and direction/depth dichotomy

Dividing an anchored point `n^2 + r` by one selected old support prime `p`
preserves every other old prime direction.  The selected direction is the only
exception: it remains in the quotient exactly when one further `p`-factor was
present.  The finite support sets below record distinct prime directions, not
prime-power exponents.  The resulting direction/depth decomposition is
elementary and does not assert quotient primality, primitive origin, descent,
or Legendre's conjecture.
-/

/-! ### PRIM-L015.1: old directions in one quotient -/

/--
The old nondivisor prime directions dividing a selected complementary quotient.

This is a direction set: membership records one prime divisor, without
recording its multiplicity.
-/
noncomputable def squareQuotientAnchorNondivisorSupport
    (n p r : ℕ) : Finset ℕ := by
  classical
  exact (squareAnchorNondivisorPrimes n).filter
    (fun q => q ∣ squareOffsetSupportQuotient n p r)

/-- Exact finite semantics of old directions in a complementary quotient. -/
@[simp] theorem mem_squareQuotientAnchorNondivisorSupport
    {n p r q : ℕ} :
    q ∈ squareQuotientAnchorNondivisorSupport n p r ↔
      Nat.Prime q ∧ q ≤ n ∧ ¬ q ∣ n ∧
        q ∣ squareOffsetSupportQuotient n p r := by
  simp [squareQuotientAnchorNondivisorSupport, and_assoc]

/-! ### PRIM-L015.2: support transfer -/

/-- Every old direction in the quotient already divides the anchored point. -/
theorem squareQuotientAnchorNondivisorSupport_subset_offsetSupport
    {n p r : ℕ}
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r) :
    squareQuotientAnchorNondivisorSupport n p r ⊆
      squareOffsetAnchorNondivisorSupport n r := by
  intro q hq
  have hq' := mem_squareQuotientAnchorNondivisorSupport.mp hq
  have hp' := mem_squareOffsetAnchorNondivisorSupport.mp hp
  have hqpoint : q ∣ n ^ 2 + r := by
    rw [← mul_squareOffsetSupportQuotient_eq hp'.2.2.2]
    exact dvd_mul_of_dvd_right hq'.2.2.2 p
  exact mem_squareOffsetAnchorNondivisorSupport.mpr
    ⟨hq'.1, hq'.2.1, hq'.2.2.1, hqpoint⟩

/-- Every off-diagonal old direction survives division by the selected prime. -/
theorem mem_quotientSupport_iff_mem_offsetSupport_of_ne
    {n p q r : ℕ}
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r)
    (hqp : q ≠ p) :
    q ∈ squareQuotientAnchorNondivisorSupport n p r ↔
      q ∈ squareOffsetAnchorNondivisorSupport n r := by
  constructor
  · apply squareQuotientAnchorNondivisorSupport_subset_offsetSupport hp
  · intro hq
    have hp' := mem_squareOffsetAnchorNondivisorSupport.mp hp
    have hq' := mem_squareOffsetAnchorNondivisorSupport.mp hq
    have hqprod : q ∣ p * squareOffsetSupportQuotient n p r := by
      rw [mul_squareOffsetSupportQuotient_eq hp'.2.2.2]
      exact hq'.2.2.2
    rcases (Nat.Prime.dvd_mul hq'.1).mp hqprod with hqpdiv | hqdiv
    · have hqeqp : q = p :=
        ((Nat.dvd_prime hp'.1).mp hqpdiv).resolve_left hq'.1.ne_one
      exact False.elim (hqp hqeqp)
    · exact mem_squareQuotientAnchorNondivisorSupport.mpr
        ⟨hq'.1, hq'.2.1, hq'.2.2.1, hqdiv⟩

/-- Erasing the selected direction gives exact off-diagonal support equality. -/
theorem erase_squareQuotientSupport_eq_erase_offsetSupport
    {n p r : ℕ}
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r) :
    (squareQuotientAnchorNondivisorSupport n p r).erase p =
      (squareOffsetAnchorNondivisorSupport n r).erase p := by
  ext q
  by_cases hqp : q = p
  · simp [hqp]
  · simp only [Finset.mem_erase]
    rw [mem_quotientSupport_iff_mem_offsetSupport_of_ne hp hqp]

/-! ### PRIM-L015.3: cardinality and selected-direction depth -/

/-- Quotient support loses at most the selected prime direction. -/
theorem offsetSupport_card_sub_one_le_quotientSupport_card
    {n p r : ℕ}
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r) :
    (squareOffsetAnchorNondivisorSupport n r).card - 1 ≤
      (squareQuotientAnchorNondivisorSupport n p r).card := by
  have hsub :
      (squareOffsetAnchorNondivisorSupport n r).erase p ⊆
        squareQuotientAnchorNondivisorSupport n p r := by
    rw [← erase_squareQuotientSupport_eq_erase_offsetSupport hp]
    exact Finset.erase_subset _ _
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hp] at hcard
  exact hcard

/-- Quotient support is contained in the original support. -/
theorem quotientSupport_card_le_offsetSupport_card
    {n p r : ℕ}
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r) :
    (squareQuotientAnchorNondivisorSupport n p r).card ≤
      (squareOffsetAnchorNondivisorSupport n r).card := by
  exact Finset.card_le_card
    (squareQuotientAnchorNondivisorSupport_subset_offsetSupport hp)

/-- The selected direction persists exactly when a second `p`-factor remains. -/
theorem selectedPrime_mem_quotientSupport_iff_square_dvd
    {n p r : ℕ}
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r) :
    p ∈ squareQuotientAnchorNondivisorSupport n p r ↔
      p ^ 2 ∣ n ^ 2 + r := by
  have hp' := mem_squareOffsetAnchorNondivisorSupport.mp hp
  constructor
  · intro hq
    have hq' := mem_squareQuotientAnchorNondivisorSupport.mp hq
    have hmuldiv : p * p ∣ p * squareOffsetSupportQuotient n p r :=
      Nat.mul_dvd_mul_left p hq'.2.2.2
    rw [mul_squareOffsetSupportQuotient_eq hp'.2.2.2] at hmuldiv
    simpa [pow_two] using hmuldiv
  · intro hsq
    have hsq' : p * p ∣ p * squareOffsetSupportQuotient n p r := by
      rw [mul_squareOffsetSupportQuotient_eq hp'.2.2.2]
      simpa [pow_two] using hsq
    have hpquot : p ∣ squareOffsetSupportQuotient n p r :=
      (Nat.mul_dvd_mul_iff_left hp'.1.pos).mp hsq'
    exact mem_squareQuotientAnchorNondivisorSupport.mpr
      ⟨hp'.1, hp'.2.1, hp'.2.2.1, hpquot⟩

/-! ### PRIM-L015.4: square-Body closure and direction/depth dichotomy -/

/-- A complementary quotient remains inside the certified square Body. -/
theorem squareOffsetSupportQuotient_le_squareBody
    {n p r : ℕ}
    (hr : SquareOffset n r)
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r) :
    squareOffsetSupportQuotient n p r ≤ squareBody n := by
  have hp' := mem_squareOffsetAnchorNondivisorSupport.mp hp
  have hfactor := mul_squareOffsetSupportQuotient_eq hp'.2.2.2
  have hpoint : n ^ 2 + r ≤ squareBody n := by
    dsimp [SquareOffset] at hr
    dsimp [squareBody]
    omega
  have hfactor_le : p * squareOffsetSupportQuotient n p r ≤
      squareBody n := by
    rw [hfactor]
    exact hpoint
  have hpone : 1 ≤ p := hp'.1.one_le
  have hquot_le : squareOffsetSupportQuotient n p r ≤
      p * squareOffsetSupportQuotient n p r := by
    simpa using Nat.mul_le_mul_right (squareOffsetSupportQuotient n p r)
      hpone
  exact hquot_le.trans hfactor_le

/-- A non-prime quotient in the square Body exposes an old nondivisor prime. -/
theorem exists_old_prime_dvd_quotient_of_not_prime
    {n p r : ℕ}
    (hn : 0 < n)
    (hr : r ∈ squareAnchorCoprimeOffsets n)
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r)
    (hnotprime : ¬ Nat.Prime (squareOffsetSupportQuotient n p r)) :
    ∃ q, q ∈ squareQuotientAnchorNondivisorSupport n p r := by
  have hr' := mem_squareAnchorCoprimeOffsets.mp hr
  have hp' := mem_squareOffsetAnchorNondivisorSupport.mp hp
  have hlarge : n < squareOffsetSupportQuotient n p r :=
    anchor_lt_squareOffsetSupportQuotient hr'.1 hp'.2.1 hp'.2.2.2
  have hupper : squareOffsetSupportQuotient n p r ≤ squareBody n :=
    squareOffsetSupportQuotient_le_squareBody hr'.1 hp
  have hquot_one : 1 < squareOffsetSupportQuotient n p r := by
    omega
  obtain ⟨q, hqprime, hqdiv, hqle⟩ :=
    exists_prime_dvd_le_of_not_prime_of_le_squareBody hquot_one hupper
      hnotprime
  have hcop : Nat.Coprime n (squareOffsetSupportQuotient n p r) :=
    (coprime_anchor_squareOffsetSupportQuotient_iff hp'.1 hp'.2.2.1
      hp'.2.2.2).mpr hr'.2
  have hqnotn : ¬ q ∣ n := by
    intro hqn
    have hqgcd : q ∣ Nat.gcd n (squareOffsetSupportQuotient n p r) :=
      Nat.dvd_gcd hqn hqdiv
    rw [hcop.gcd_eq_one] at hqgcd
    exact hqprime.ne_one (Nat.dvd_one.mp hqgcd)
  exact ⟨q, mem_squareQuotientAnchorNondivisorSupport.mpr
    ⟨hqprime, hqle, hqnotn, hqdiv⟩⟩

/-- Quotient non-primality splits into selected depth or another old direction. -/
theorem not_prime_quotient_iff_self_depth_or_distinct_support
    {n p r : ℕ}
    (hn : 0 < n)
    (hr : r ∈ squareAnchorCoprimeOffsets n)
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r) :
    ¬ Nat.Prime (squareOffsetSupportQuotient n p r) ↔
      p ∣ squareOffsetSupportQuotient n p r ∨
      ∃ q,
        q ≠ p ∧ q ∈ squareOffsetAnchorNondivisorSupport n r := by
  have hp' := mem_squareOffsetAnchorNondivisorSupport.mp hp
  have hlarge : n < squareOffsetSupportQuotient n p r :=
    anchor_lt_squareOffsetSupportQuotient
      (mem_squareAnchorCoprimeOffsets.mp hr).1 hp'.2.1 hp'.2.2.2
  constructor
  · intro hnotprime
    obtain ⟨q, hq⟩ := exists_old_prime_dvd_quotient_of_not_prime
      hn hr hp hnotprime
    have hq' := mem_squareQuotientAnchorNondivisorSupport.mp hq
    by_cases hqp : q = p
    · left
      simpa [hqp] using hq'.2.2.2
    · right
      exact ⟨q, hqp,
        squareQuotientAnchorNondivisorSupport_subset_offsetSupport hp hq⟩
  · rintro (hself | ⟨q, hqp, hqoff⟩)
    · intro hprime
      rcases (Nat.dvd_prime hprime).mp hself with hone | heq
      · exact hp'.1.ne_one hone
      · have hplt : p < squareOffsetSupportQuotient n p r :=
          lt_of_le_of_lt hp'.2.1 hlarge
        omega
    · have hqquot : q ∈ squareQuotientAnchorNondivisorSupport n p r :=
        (mem_quotientSupport_iff_mem_offsetSupport_of_ne hp hqp).mpr hqoff
      have hq' := mem_squareQuotientAnchorNondivisorSupport.mp hqquot
      have hqoff' := mem_squareOffsetAnchorNondivisorSupport.mp hqoff
      intro hprime
      rcases (Nat.dvd_prime hprime).mp hq'.2.2.2 with hone | heq
      · exact hqoff'.1.ne_one hone
      · have hqlt : q < squareOffsetSupportQuotient n p r :=
          lt_of_le_of_lt hqoff'.2.1 hlarge
        omega

/-!
### PRIM-L016: simple support and a fresh quotient direction

PRIM-L015 classified quotient non-primality by two finite old-world
obstructions: persistence of the selected direction, or another old support
direction.  This checkpoint formalizes the complementary case.  Singleton
support means one distinct old direction, while depth one is the elementary
condition `p^2 ∤ n^2 + r`; no general valuation API is introduced.

Under these hypotheses the quotient is prime, lies above the anchor, and is
fresh relative to `primeScalesUpTo n`.  This is finite-world freshness only:
it is not a Zsigmondy, PrimitiveBeam, or Legendre theorem.
-/

/-! ### PRIM-L016.1: singleton support and depth one -/

/-- No old support direction other than `p` is equivalent to singleton support. -/
theorem no_distinct_anchorNondivisorSupport_iff_eq_singleton
    {n p r : ℕ}
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r) :
    (¬ ∃ q,
        q ≠ p ∧ q ∈ squareOffsetAnchorNondivisorSupport n r) ↔
      squareOffsetAnchorNondivisorSupport n r = {p} := by
  constructor
  · intro hnodist
    ext q
    constructor
    · intro hq
      by_cases hqp : q = p
      · simp [hqp]
      · exact False.elim (hnodist ⟨q, hqp, hq⟩)
    · intro hq
      simp only [Finset.mem_singleton] at hq
      simpa [hq] using hp
  · intro hsingle hex
    rcases hex with ⟨q, hqp, hq⟩
    have hq' : q ∈ ({p} : Finset ℕ) := by
      rw [← hsingle]
      exact hq
    exact hqp (by simpa using hq')

/-- Depth one is the negated selected-direction persistence condition. -/
theorem selectedPrime_not_dvd_quotient_iff_not_square_dvd
    {n p r : ℕ}
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r) :
    ¬ p ∣ squareOffsetSupportQuotient n p r ↔
      ¬ p ^ 2 ∣ n ^ 2 + r := by
  constructor
  · intro hnot hsq
    have hqmem : p ∈ squareQuotientAnchorNondivisorSupport n p r :=
      (selectedPrime_mem_quotientSupport_iff_square_dvd hp).mpr hsq
    exact hnot (mem_squareQuotientAnchorNondivisorSupport.mp hqmem).2.2.2
  · intro hnot hpdvd
    apply hnot
    exact (selectedPrime_mem_quotientSupport_iff_square_dvd hp).mp
      (mem_squareQuotientAnchorNondivisorSupport.mpr
        ⟨(mem_squareOffsetAnchorNondivisorSupport.mp hp).1,
          (mem_squareOffsetAnchorNondivisorSupport.mp hp).2.1,
          (mem_squareOffsetAnchorNondivisorSupport.mp hp).2.2.1,
          hpdvd⟩)

/-- Exact criterion for a simple-support, depth-one quotient to be prime. -/
theorem prime_squareOffsetSupportQuotient_iff_singleton_support_and_depth_one
    {n p r : ℕ}
    (hn : 0 < n)
    (hr : r ∈ squareAnchorCoprimeOffsets n)
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r) :
    Nat.Prime (squareOffsetSupportQuotient n p r) ↔
      squareOffsetAnchorNondivisorSupport n r = {p} ∧
      ¬ p ^ 2 ∣ n ^ 2 + r := by
  have hdich := not_prime_quotient_iff_self_depth_or_distinct_support
    hn hr hp
  constructor
  · intro hprime
    have hnodist : ¬ ∃ q,
        q ≠ p ∧ q ∈ squareOffsetAnchorNondivisorSupport n r := by
      intro hother
      exact (hdich.mpr (Or.inr hother)) hprime
    have hsingle :=
      (no_distinct_anchorNondivisorSupport_iff_eq_singleton hp).mp hnodist
    have hdepth : ¬ p ^ 2 ∣ n ^ 2 + r := by
      apply (selectedPrime_not_dvd_quotient_iff_not_square_dvd hp).mp
      intro hpdvd
      exact (hdich.mpr (Or.inl hpdvd)) hprime
    exact ⟨hsingle, hdepth⟩
  · rintro ⟨hsingle, hdepth⟩
    by_contra hnotprime
    rcases hdich.mp hnotprime with hself | hother
    · exact (selectedPrime_not_dvd_quotient_iff_not_square_dvd hp).mpr
        hdepth hself
    · exact (no_distinct_anchorNondivisorSupport_iff_eq_singleton hp).mpr
        hsingle hother

/-- Convenient constructor for a prime quotient from the simple hypotheses. -/
theorem prime_squareOffsetSupportQuotient_of_singleton_support_of_not_square_dvd
    {n p r : ℕ}
    (hn : 0 < n)
    (hr : r ∈ squareAnchorCoprimeOffsets n)
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r)
    (hsingle : squareOffsetAnchorNondivisorSupport n r = {p})
    (hdepth : ¬ p ^ 2 ∣ n ^ 2 + r) :
    Nat.Prime (squareOffsetSupportQuotient n p r) :=
  (prime_squareOffsetSupportQuotient_iff_singleton_support_and_depth_one
    hn hr hp).mpr ⟨hsingle, hdepth⟩

/-! ### PRIM-L016.2: finite-world freshness -/

/-- A complementary quotient lies outside the old bounded prime world. -/
theorem squareOffsetSupportQuotient_not_mem_primeScalesUpTo
    {n p r : ℕ}
    (hr : SquareOffset n r)
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r) :
    squareOffsetSupportQuotient n p r ∉ primeScalesUpTo n := by
  intro hk
  have hk' := mem_primeScalesUpTo.mp hk
  have hlarge : n < squareOffsetSupportQuotient n p r :=
    anchor_lt_squareOffsetSupportQuotient hr
      (mem_squareOffsetAnchorNondivisorSupport.mp hp).2.1
      (mem_squareOffsetAnchorNondivisorSupport.mp hp).2.2.2
  omega

/-- The simple quotient is fresh relative to the finite old prime world. -/
theorem freshPrimeDirection_squareOffsetSupportQuotient_of_singleton_support_of_depth_one
    {n p r : ℕ}
    (hn : 0 < n)
    (hr : r ∈ squareAnchorCoprimeOffsets n)
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r)
    (hsingle : squareOffsetAnchorNondivisorSupport n r = {p})
    (hdepth : ¬ p ^ 2 ∣ n ^ 2 + r) :
    FreshPrimeDirection
      (primeScalesUpTo n)
      (squareOffsetSupportQuotient n p r)
      (squareOffsetSupportQuotient n p r) := by
  let k := squareOffsetSupportQuotient n p r
  have hkprime : Nat.Prime k := by
    dsimp [k]
    exact prime_squareOffsetSupportQuotient_of_singleton_support_of_not_square_dvd
      hn hr hp hsingle hdepth
  have hknotmem : k ∉ primeScalesUpTo n := by
    dsimp [k]
    exact squareOffsetSupportQuotient_not_mem_primeScalesUpTo
      (mem_squareAnchorCoprimeOffsets.mp hr).1 hp
  exact ⟨hkprime, dvd_refl k, hknotmem⟩

/-- The simple quotient has no prime divisor from the old finite world. -/
theorem supportDisjointFrom_squareOffsetSupportQuotient_of_singleton_support_of_depth_one
    {n p r : ℕ}
    (hn : 0 < n)
    (hr : r ∈ squareAnchorCoprimeOffsets n)
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r)
    (hsingle : squareOffsetAnchorNondivisorSupport n r = {p})
    (hdepth : ¬ p ^ 2 ∣ n ^ 2 + r) :
    SupportDisjointFrom
      (primeScalesUpTo n)
      (squareOffsetSupportQuotient n p r) := by
  have hprime := prime_squareOffsetSupportQuotient_of_singleton_support_of_not_square_dvd
    hn hr hp hsingle hdepth
  have hnotmem := squareOffsetSupportQuotient_not_mem_primeScalesUpTo
    (mem_squareAnchorCoprimeOffsets.mp hr).1 hp
  intro q hqprime hqdiv hqmem
  rcases (Nat.dvd_prime hprime).mp hqdiv with hqone | hqeq
  · exact hqprime.ne_one hqone
  · exact hnotmem (by simpa [hqeq] using hqmem)

/-! ### PRIM-L016.3: the simple old-prime times fresh-prime factorization -/

/-- The simple incidence factors as one old prime and one large fresh prime. -/
theorem simple_support_depth_one_factorization
    {n p r : ℕ}
    (hn : 0 < n)
    (hr : r ∈ squareAnchorCoprimeOffsets n)
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r)
    (hsingle : squareOffsetAnchorNondivisorSupport n r = {p})
    (hdepth : ¬ p ^ 2 ∣ n ^ 2 + r) :
    let k := squareOffsetSupportQuotient n p r
    Nat.Prime p ∧ p ≤ n ∧ ¬ p ∣ n ∧
    Nat.Prime k ∧ n < k ∧ Nat.Coprime n k ∧
    p * k = n ^ 2 + r := by
  dsimp
  have hp' := mem_squareOffsetAnchorNondivisorSupport.mp hp
  have hr' := mem_squareAnchorCoprimeOffsets.mp hr
  have hkprime := prime_squareOffsetSupportQuotient_of_singleton_support_of_not_square_dvd
    hn hr hp hsingle hdepth
  have hklarge := anchor_lt_squareOffsetSupportQuotient hr'.1 hp'.2.1 hp'.2.2.2
  have hkcop :=
    (coprime_anchor_squareOffsetSupportQuotient_iff hp'.1 hp'.2.2.1
      hp'.2.2.2).mpr hr'.2
  have hkfactor := mul_squareOffsetSupportQuotient_eq hp'.2.2.2
  exact ⟨hp'.1, hp'.2.1, hp'.2.2.1, hkprime, hklarge, hkcop, hkfactor⟩

/-! ### PRIM-L016.4: fresh-or-obstructed trichotomy -/

/-- Every selected coprime incidence is simple or has an old-world obstruction. -/
theorem quotient_prime_or_self_depth_or_distinct_support
    {n p r : ℕ}
    (hn : 0 < n)
    (hr : r ∈ squareAnchorCoprimeOffsets n)
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r) :
    Nat.Prime (squareOffsetSupportQuotient n p r) ∨
      p ^ 2 ∣ n ^ 2 + r ∨
      ∃ q,
        q ≠ p ∧ q ∈ squareOffsetAnchorNondivisorSupport n r := by
  by_cases hprime : Nat.Prime (squareOffsetSupportQuotient n p r)
  · exact Or.inl hprime
  · rcases (not_prime_quotient_iff_self_depth_or_distinct_support hn hr hp).mp
      hprime with hself | hother
    · exact Or.inr (Or.inl ((selectedPrime_mem_quotientSupport_iff_square_dvd hp).mp
        (mem_squareQuotientAnchorNondivisorSupport.mpr
          ⟨(mem_squareOffsetAnchorNondivisorSupport.mp hp).1,
            (mem_squareOffsetAnchorNondivisorSupport.mp hp).2.1,
            (mem_squareOffsetAnchorNondivisorSupport.mp hp).2.2.1,
            hself⟩)))
    · exact Or.inr (Or.inr hother)

end DkMath.NumberTheory.Legendre

