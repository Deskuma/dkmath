/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.NumberTheory.Legendre.CoprimePacket

#print "file: DkMath.NumberTheory.Legendre.Quotient"

/-!
## Quotient

Coprime quotient coordinates, factorization, collision rigidity, and global quotient frontiers.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open scoped BigOperators

/-!
### PRIM-L013: coprime quotient lift and packet factorization

PRIM-L012 separated the coprime square window into packets `(r, n + r)` and
showed that full cover supplies distinct nondivisor prime directions on the
two seats.  This checkpoint attaches the complementary factor
`k = (n ^ 2 + r) / q` to each such finite incidence.  The factor equation is
exact, and the square-window bounds force `k > n` when `q ≤ n`.

For an anchor-nondivisor prime, coprimality with `n` transfers from the offset
to its complementary factor.  The quotient image is only a coordinate change
for existing finite support incidences: no primality, primitivity, uniqueness
of factorization, or contradiction is asserted for the quotient.  In
particular, the packet equation exposed below is a structural frontier rather
than a proof of Legendre's conjecture.
-/

/-! ### PRIM-L013.1: complementary factors -/

/-- The complementary factor attached to a known support divisor. -/
def squareOffsetSupportQuotient (n q r : ℕ) : ℕ :=
  (n ^ 2 + r) / q

/-- Exact reconstruction of an anchored point from its support quotient. -/
theorem mul_squareOffsetSupportQuotient_eq
    {n q r : ℕ}
    (hdiv : q ∣ n ^ 2 + r) :
    q * squareOffsetSupportQuotient n q r = n ^ 2 + r := by
  exact Nat.mul_div_cancel' hdiv

/-- A square-window support factor has a complementary factor larger than `n`. -/
theorem anchor_lt_squareOffsetSupportQuotient
    {n q r : ℕ}
    (hr : SquareOffset n r)
    (hqle : q ≤ n)
    (hdiv : q ∣ n ^ 2 + r) :
    n < squareOffsetSupportQuotient n q r := by
  have hpoint : n ^ 2 < n ^ 2 + r := by
    dsimp [SquareOffset] at hr
    omega
  have hfactor := mul_squareOffsetSupportQuotient_eq hdiv
  by_contra hnot
  have hkle : squareOffsetSupportQuotient n q r ≤ n := by omega
  have hbound : q * squareOffsetSupportQuotient n q r ≤ n ^ 2 := by
    calc
      q * squareOffsetSupportQuotient n q r ≤ q * n :=
        Nat.mul_le_mul_left q hkle
      _ ≤ n * n := Nat.mul_le_mul_right n hqle
      _ = n ^ 2 := by simp [pow_two]
  omega

/-- A nondivisor support incidence has a complementary factor above the anchor. -/
theorem anchor_lt_squareOffsetSupportQuotient_of_mem_nondivisorSupport
    {n q r : ℕ}
    (hr : SquareOffset n r)
    (hq : q ∈ squareOffsetAnchorNondivisorSupport n r) :
    n < squareOffsetSupportQuotient n q r := by
  have hq' := mem_squareOffsetAnchorNondivisorSupport.mp hq
  exact anchor_lt_squareOffsetSupportQuotient hr hq'.2.1 hq'.2.2.2

/-- Coprimality transfers between a coprime offset and its support quotient. -/
theorem coprime_anchor_squareOffsetSupportQuotient_iff
    {n q r : ℕ}
    (hq : Nat.Prime q)
    (hqn : ¬ q ∣ n)
    (hdiv : q ∣ n ^ 2 + r) :
    Nat.Coprime n (squareOffsetSupportQuotient n q r) ↔
      Nat.Coprime n r := by
  have hqcop : Nat.Coprime n q :=
    (hq.coprime_iff_not_dvd.mpr hqn).symm
  have hmul :
      Nat.Coprime n (q * squareOffsetSupportQuotient n q r) ↔
        Nat.Coprime n (squareOffsetSupportQuotient n q r) := by
    constructor
    · intro h
      exact (Nat.coprime_mul_iff_right.mp h).2
    · intro h
      exact hqcop.mul_right h
  have hpoint : Nat.Coprime n (n ^ 2 + r) ↔ Nat.Coprime n r := by
    simpa only [pow_two] using Nat.coprime_mul_left_add_right n r n
  calc
    Nat.Coprime n (squareOffsetSupportQuotient n q r) ↔
        Nat.Coprime n (q * squareOffsetSupportQuotient n q r) := hmul.symm
    _ ↔ Nat.Coprime n (n ^ 2 + r) := by
      rw [mul_squareOffsetSupportQuotient_eq hdiv]
    _ ↔ Nat.Coprime n r := hpoint

/-! ### PRIM-L013.2: finite coprime wave quotient images -/

/-- Coprime square seats hit by one old nondivisor prime wave. -/
noncomputable def squareAnchorCoprimeWaveOffsets (n q : ℕ) : Finset ℕ := by
  classical
  exact (squareAnchorCoprimeOffsets n).filter
    (fun r => SquareOffsetForbiddenBy n q r)

/-- Exact membership in a coprime nondivisor wave. -/
@[simp] theorem mem_squareAnchorCoprimeWaveOffsets
    {n q r : ℕ} :
    r ∈ squareAnchorCoprimeWaveOffsets n q ↔
      SquareOffset n r ∧ Nat.Coprime n r ∧
        SquareOffsetForbiddenBy n q r := by
  simp [squareAnchorCoprimeWaveOffsets, and_assoc]

/-- A nondivisor coprime-wave seat carries a large coprime quotient factor. -/
theorem squareAnchorCoprimeWaveOffsets_quotient_properties
    {n q r : ℕ}
    (hq : q ∈ squareAnchorNondivisorPrimes n)
    (hr : r ∈ squareAnchorCoprimeWaveOffsets n q) :
    n < squareOffsetSupportQuotient n q r ∧
      Nat.Coprime n (squareOffsetSupportQuotient n q r) ∧
      q * squareOffsetSupportQuotient n q r = n ^ 2 + r := by
  have hq' := mem_squareAnchorNondivisorPrimes.mp hq
  have hr' := mem_squareAnchorCoprimeWaveOffsets.mp hr
  refine ⟨anchor_lt_squareOffsetSupportQuotient hr'.1 hq'.2.1 hr'.2.2,
    (coprime_anchor_squareOffsetSupportQuotient_iff hq'.1 hq'.2.2
      hr'.2.2).mpr hr'.2.1, ?_⟩
  exact mul_squareOffsetSupportQuotient_eq hr'.2.2

/-- Complementary factors carried by a coprime wave are represented finitely. -/
noncomputable def squareAnchorCoprimeSupportQuotients (n q : ℕ) : Finset ℕ :=
  (squareAnchorCoprimeWaveOffsets n q).image
    (fun r => squareOffsetSupportQuotient n q r)

/-- Membership in the finite complementary-factor image. -/
@[simp] theorem mem_squareAnchorCoprimeSupportQuotients
    {n q k : ℕ} :
    k ∈ squareAnchorCoprimeSupportQuotients n q ↔
      ∃ r, r ∈ squareAnchorCoprimeWaveOffsets n q ∧
        squareOffsetSupportQuotient n q r = k := by
  simp [squareAnchorCoprimeSupportQuotients]

/-- A quotient-image member recovers its large, coprime factorization data. -/
theorem squareAnchorCoprimeSupportQuotients_mem_properties
    {n q k : ℕ}
    (hq : q ∈ squareAnchorNondivisorPrimes n)
    (hk : k ∈ squareAnchorCoprimeSupportQuotients n q) :
    ∃ r, r ∈ squareAnchorCoprimeWaveOffsets n q ∧
      n < k ∧ Nat.Coprime n k ∧ q * k = n ^ 2 + r := by
  rcases mem_squareAnchorCoprimeSupportQuotients.mp hk with ⟨r, hr, hrk⟩
  have hprops := squareAnchorCoprimeWaveOffsets_quotient_properties hq hr
  refine ⟨r, hr, ?_, ?_, ?_⟩
  · simpa [hrk] using hprops.1
  · simpa [hrk] using hprops.2.1
  · rw [← hrk]
    exact hprops.2.2

/-- The quotient map is injective on the seats of a positive prime wave. -/
theorem card_squareAnchorCoprimeSupportQuotients
    {n q : ℕ}
    (hq : q ∈ squareAnchorNondivisorPrimes n) :
    (squareAnchorCoprimeSupportQuotients n q).card =
      (squareAnchorCoprimeWaveOffsets n q).card := by
  classical
  apply (Finset.card_image_iff).2
  intro r₁ hr₁ r₂ hr₂ heq
  have hq' := mem_squareAnchorNondivisorPrimes.mp hq
  have h₁ := mem_squareAnchorCoprimeWaveOffsets.mp hr₁
  have h₂ := mem_squareAnchorCoprimeWaveOffsets.mp hr₂
  have hf₁ := mul_squareOffsetSupportQuotient_eq h₁.2.2
  have hf₂ := mul_squareOffsetSupportQuotient_eq h₂.2.2
  have heq' : squareOffsetSupportQuotient n q r₁ =
      squareOffsetSupportQuotient n q r₂ := heq
  have hpoint : n ^ 2 + r₁ = n ^ 2 + r₂ := by
    calc
      n ^ 2 + r₁ = q * squareOffsetSupportQuotient n q r₁ := hf₁.symm
      _ = q * squareOffsetSupportQuotient n q r₂ := by rw [heq']
      _ = n ^ 2 + r₂ := hf₂
  omega

/-! ### PRIM-L013.3: quotient-coordinate incidence -/

/-- Restricted coprime incidence transposed to one-prime coprime waves. -/
theorem squareAnchorCoprimeNondivisorIncidence_eq_sum_coprimeWave_cards
    (n : ℕ) :
    squareAnchorCoprimeNondivisorIncidence n =
      ∑ q ∈ squareAnchorNondivisorPrimes n,
        (squareAnchorCoprimeWaveOffsets n q).card := by
  classical
  unfold squareAnchorCoprimeNondivisorIncidence
  calc
    (∑ r ∈ squareAnchorCoprimeOffsets n,
        (squareOffsetAnchorNondivisorSupport n r).card) =
        ∑ r ∈ squareAnchorCoprimeOffsets n,
          ∑ q ∈ squareAnchorNondivisorPrimes n,
            if SquareOffsetForbiddenBy n q r then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro r hr
      simp [squareOffsetAnchorNondivisorSupport]
    _ = ∑ q ∈ squareAnchorNondivisorPrimes n,
          ∑ r ∈ squareAnchorCoprimeOffsets n,
            if SquareOffsetForbiddenBy n q r then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ q ∈ squareAnchorNondivisorPrimes n,
          (squareAnchorCoprimeWaveOffsets n q).card := by
      apply Finset.sum_congr rfl
      intro q hq
      simp [squareAnchorCoprimeWaveOffsets]

/-- Restricted coprime incidence transposed to quotient-image cardinalities. -/
theorem squareAnchorCoprimeNondivisorIncidence_eq_sum_quotient_cards
    (n : ℕ) :
    squareAnchorCoprimeNondivisorIncidence n =
      ∑ q ∈ squareAnchorNondivisorPrimes n,
        (squareAnchorCoprimeSupportQuotients n q).card := by
  rw [squareAnchorCoprimeNondivisorIncidence_eq_sum_coprimeWave_cards]
  apply Finset.sum_congr rfl
  intro q hq
  exact (card_squareAnchorCoprimeSupportQuotients hq).symm

/-! ### PRIM-L013.4: full-cover packet factorization -/

/-- A fully covered coprime packet yields two distinct small primes and two
large anchor-coprime complementary factors. -/
theorem exists_distinct_prime_large_cofactor_packet_of_fullyCovered
    {n r : ℕ}
    (hn : 0 < n)
    (hr : r ∈ squareAnchorCoprimeBaseOffsets n)
    (hfull : SquareOffsetsFullyCovered n) :
    ∃ p q a b,
      p ≠ q ∧
      p ∈ squareAnchorNondivisorPrimes n ∧
      q ∈ squareAnchorNondivisorPrimes n ∧
      n < a ∧ n < b ∧
      Nat.Coprime n a ∧ Nat.Coprime n b ∧
      p * a = n ^ 2 + r ∧
      q * b = n ^ 2 + (n + r) ∧
      p * a + n = q * b := by
  rcases exists_distinct_anchorNondivisor_cover_pair_of_fullyCovered
      hn hr hfull with ⟨p, q, hpq, hp, hq⟩
  have hp' := mem_squareOffsetAnchorNondivisorSupport.mp hp
  have hq' := mem_squareOffsetAnchorNondivisorSupport.mp hq
  have hpmem : p ∈ squareAnchorNondivisorPrimes n :=
    mem_squareAnchorNondivisorPrimes.mpr
      ⟨hp'.1, hp'.2.1, hp'.2.2.1⟩
  have hqmem : q ∈ squareAnchorNondivisorPrimes n :=
    mem_squareAnchorNondivisorPrimes.mpr
      ⟨hq'.1, hq'.2.1, hq'.2.2.1⟩
  have hr' := mem_squareAnchorCoprimeBaseOffsets.mp hr
  have hrbaseSquare : SquareOffset n r := ⟨hr'.1, by omega⟩
  have hrshiftmem : n + r ∈ squareAnchorCoprimeOffsets n :=
    mem_squareAnchorCoprimeBaseOffsets_shift_mem_coprimeOffsets hr
  have hrshift' := mem_squareAnchorCoprimeOffsets.mp hrshiftmem
  have hrshift : Nat.Coprime n (n + r) := coprime_anchor_add_iff.mpr hr'.2.2
  have hpa : n < squareOffsetSupportQuotient n p r :=
    anchor_lt_squareOffsetSupportQuotient hrbaseSquare hp'.2.1 hp'.2.2.2
  have hqb : n < squareOffsetSupportQuotient n q (n + r) :=
    anchor_lt_squareOffsetSupportQuotient hrshift'.1 hq'.2.1 hq'.2.2.2
  have hpa' : Nat.Coprime n (squareOffsetSupportQuotient n p r) :=
    (coprime_anchor_squareOffsetSupportQuotient_iff hp'.1 hp'.2.2.1
      hp'.2.2.2).mpr hr'.2.2
  have hqb' : Nat.Coprime n (squareOffsetSupportQuotient n q (n + r)) :=
    (coprime_anchor_squareOffsetSupportQuotient_iff hq'.1 hq'.2.2.1
      hq'.2.2.2).mpr hrshift
  have hpaeq := mul_squareOffsetSupportQuotient_eq hp'.2.2.2
  have hqbeq := mul_squareOffsetSupportQuotient_eq hq'.2.2.2
  refine ⟨p, q, squareOffsetSupportQuotient n p r,
    squareOffsetSupportQuotient n q (n + r), hpq, hpmem, hqmem,
    hpa, hqb, hpa', hqb', hpaeq, hqbeq, ?_⟩
  omega

/-!
### PRIM-L014: quotient collision rigidity and global injectivity

PRIM-L013 attached a complementary factor to each coprime nondivisor support
incidence.  This checkpoint exposes all such incidences as one finite set of
pairs `(q, r)` and studies the quotient projection on that set.  A collision
within one prime wave was already excluded by the exact factor equation.  The
new point is that a collision across distinct prime waves would force the
prime pair `2, 3` and then `n < 4`; hence for `4 ≤ n` the quotient projection
is globally injective.

The resulting quotient values are large and coprime to the anchor, but they
are not asserted to be prime, primitive, or fresh.  This is a finite
collision-rigidity statement, not a density estimate, matching argument, or
proof of Legendre's conjecture.
-/

/-! ### PRIM-L014.1: the global incidence domain -/

/-- Coprime nondivisor support incidences `(q, r)`. -/
noncomputable def squareAnchorCoprimeSupportIncidences
    (n : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((squareAnchorNondivisorPrimes n).product
    (squareAnchorCoprimeOffsets n)).filter
      (fun qr => SquareOffsetForbiddenBy n qr.1 qr.2)

/-- Exact membership in the global coprime-support incidence domain. -/
@[simp] theorem mem_squareAnchorCoprimeSupportIncidences
    {n q r : ℕ} :
    (q, r) ∈ squareAnchorCoprimeSupportIncidences n ↔
      q ∈ squareAnchorNondivisorPrimes n ∧
      r ∈ squareAnchorCoprimeOffsets n ∧
      SquareOffsetForbiddenBy n q r := by
  simp [squareAnchorCoprimeSupportIncidences, and_assoc]

/-- The global incidence set has exactly the restricted-ledger cardinality. -/
theorem card_squareAnchorCoprimeSupportIncidences
    (n : ℕ) :
    (squareAnchorCoprimeSupportIncidences n).card =
      squareAnchorCoprimeNondivisorIncidence n := by
  classical
  unfold squareAnchorCoprimeSupportIncidences
    squareAnchorCoprimeNondivisorIncidence
  calc
    (((squareAnchorNondivisorPrimes n).product
        (squareAnchorCoprimeOffsets n)).filter
        (fun qr => SquareOffsetForbiddenBy n qr.1 qr.2)).card =
        ∑ qr ∈ (squareAnchorNondivisorPrimes n).product
          (squareAnchorCoprimeOffsets n),
          if SquareOffsetForbiddenBy n qr.1 qr.2 then 1 else 0 := by
      simp
    _ = ∑ q ∈ squareAnchorNondivisorPrimes n,
          ∑ r ∈ squareAnchorCoprimeOffsets n,
            if SquareOffsetForbiddenBy n q r then 1 else 0 := by
      change
        (∑ qr ∈ (squareAnchorNondivisorPrimes n ×ˢ
          squareAnchorCoprimeOffsets n),
          if SquareOffsetForbiddenBy n qr.1 qr.2 then 1 else 0) = _
      rw [Finset.sum_product]
    _ = ∑ r ∈ squareAnchorCoprimeOffsets n,
          ∑ q ∈ squareAnchorNondivisorPrimes n,
            if SquareOffsetForbiddenBy n q r then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ r ∈ squareAnchorCoprimeOffsets n,
          (squareOffsetAnchorNondivisorSupport n r).card := by
      apply Finset.sum_congr rfl
      intro r hr
      simp [squareOffsetAnchorNondivisorSupport]

/-! ### PRIM-L014.2: global quotient projection -/

/-- The quotient attached to one global support incidence pair. -/
def squareAnchorIncidenceQuotient
    (n : ℕ) (qr : ℕ × ℕ) : ℕ :=
  squareOffsetSupportQuotient n qr.1 qr.2

/-- All complementary quotients arising from coprime support incidences. -/
noncomputable def squareAnchorCoprimeGlobalQuotients (n : ℕ) : Finset ℕ :=
  (squareAnchorCoprimeSupportIncidences n).image
    (squareAnchorIncidenceQuotient n)

/-- Membership in the global quotient image remembers an incidence source. -/
@[simp] theorem mem_squareAnchorCoprimeGlobalQuotients
    {n k : ℕ} :
    k ∈ squareAnchorCoprimeGlobalQuotients n ↔
      ∃ q r, (q, r) ∈ squareAnchorCoprimeSupportIncidences n ∧
        squareOffsetSupportQuotient n q r = k := by
  simp [squareAnchorCoprimeGlobalQuotients, squareAnchorIncidenceQuotient]

/-! ### PRIM-L014.3: collision rigidity -/

private theorem eq_of_same_prime_same_support_quotient
    {n q r s : ℕ}
    (hr : q ∣ n ^ 2 + r)
    (hs : q ∣ n ^ 2 + s)
    (hquot : squareOffsetSupportQuotient n q r =
      squareOffsetSupportQuotient n q s) :
    r = s := by
  have hfr := mul_squareOffsetSupportQuotient_eq hr
  have hfs := mul_squareOffsetSupportQuotient_eq hs
  have hsum : n ^ 2 + r = n ^ 2 + s := by
    calc
      n ^ 2 + r = q * squareOffsetSupportQuotient n q r := hfr.symm
      _ = q * squareOffsetSupportQuotient n q s := by rw [hquot]
      _ = n ^ 2 + s := hfs
  omega

private theorem eq_two_eq_three_of_primes_of_sub_lt_two
    {p q : ℕ}
    (hp : Nat.Prime p)
    (hq : Nat.Prime q)
    (hpq : p < q)
    (hgap : q - p < 2) :
    p = 2 ∧ q = 3 := by
  have hsucc : q = p + 1 := by omega
  rcases hp.eq_two_or_odd' with hp_two | hp_odd
  · subst p
    constructor
    · rfl
    · omega
  · have hq_even : Even q := by
      rw [hsucc]
      exact hp_odd.add_one
    have hq_two : q = 2 := hq.even_iff.mp hq_even
    have hp_two_le : 2 ≤ p := hp.two_le
    omega

private theorem anchor_lt_four_of_ordered_distinct_prime_quotient_collision
    {n p q r s : ℕ}
    (hp : (p, r) ∈ squareAnchorCoprimeSupportIncidences n)
    (hq : (q, s) ∈ squareAnchorCoprimeSupportIncidences n)
    (hpq : p < q)
    (hquot : squareOffsetSupportQuotient n p r =
      squareOffsetSupportQuotient n q s) :
    n < 4 := by
  have hp' := mem_squareAnchorCoprimeSupportIncidences.mp hp
  have hq' := mem_squareAnchorCoprimeSupportIncidences.mp hq
  have hpp := mem_squareAnchorNondivisorPrimes.mp hp'.1
  have hqq := mem_squareAnchorNondivisorPrimes.mp hq'.1
  have hr' := mem_squareAnchorCoprimeOffsets.mp hp'.2.1
  have hs' := mem_squareAnchorCoprimeOffsets.mp hq'.2.1
  have hkp : n < squareOffsetSupportQuotient n p r :=
    anchor_lt_squareOffsetSupportQuotient hr'.1 hpp.2.1 hp'.2.2
  have hkp' : n < squareOffsetSupportQuotient n q s := by
    simpa [hquot] using hkp
  let k := squareOffsetSupportQuotient n p r
  have hpfactor : p * k = n ^ 2 + r := by
    simpa [k] using mul_squareOffsetSupportQuotient_eq hp'.2.2
  have hqfactor : q * k = n ^ 2 + s := by
    simpa [k, hquot] using mul_squareOffsetSupportQuotient_eq hq'.2.2
  have hdiff : (q - p) * k = s - r := by
    rw [Nat.sub_mul]
    rw [hpfactor, hqfactor]
    omega
  have hr_one : 1 ≤ r := hr'.1.1
  have hs_two_n : s ≤ 2 * n := hs'.1.2
  have hk_pos : 0 < k := by
    dsimp [k]
    omega
  have hqp_pos : 0 < q - p := by omega
  have hprod_pos : 0 < (q - p) * k := Nat.mul_pos hqp_pos hk_pos
  have hsr : r ≤ s := by
    omega
  have hdiff_lt : s - r < 2 * n := by
    omega
  by_cases hgap : q - p < 2
  · have hpq23 := eq_two_eq_three_of_primes_of_sub_lt_two hpp.1 hqq.1
      hpq hgap
    rcases hpq23 with ⟨rfl, rfl⟩
    have hk_eq : k = s - r := by
      simpa using hdiff
    have hk_lt : k < 2 * n := by
      rw [hk_eq]
      exact hdiff_lt
    have hn_sq_lt : n ^ 2 < 2 * k := by
      omega
    have hn_sq_lt_four : n ^ 2 < 4 * n := by
      omega
    by_contra hn
    have hn_four : 4 ≤ n := by omega
    have hfour_mul : 4 * n ≤ n ^ 2 := by
      calc
        4 * n ≤ n * n := Nat.mul_le_mul_right n hn_four
        _ = n ^ 2 := by simp [pow_two]
    omega
  · have hgap_two : 2 ≤ q - p := by omega
    have htwo_mul : 2 * k ≤ (q - p) * k := by
      exact Nat.mul_le_mul_right k hgap_two
    omega

/-- A collision between distinct prime waves forces the anchor below `4`. -/
theorem anchor_lt_four_of_distinct_prime_quotient_collision
    {n p q r s : ℕ}
    (hp : (p, r) ∈ squareAnchorCoprimeSupportIncidences n)
    (hq : (q, s) ∈ squareAnchorCoprimeSupportIncidences n)
    (hpq : p ≠ q)
    (hquot : squareOffsetSupportQuotient n p r =
      squareOffsetSupportQuotient n q s) :
    n < 4 := by
  rcases lt_or_gt_of_ne hpq with hpq_lt | hqp_lt
  · exact anchor_lt_four_of_ordered_distinct_prime_quotient_collision
      hp hq hpq_lt hquot
  · exact anchor_lt_four_of_ordered_distinct_prime_quotient_collision
      hq hp hqp_lt hquot.symm

/-! ### PRIM-L014.4: global injectivity and image cardinality -/

/-- A quotient collision at an anchor `n ≥ 4` has the same prime and offset. -/
theorem squareAnchorIncidenceQuotient_eq_imp_eq_of_four_le
    {n : ℕ} (hn : 4 ≤ n) {x y : ℕ × ℕ}
    (hx : x ∈ squareAnchorCoprimeSupportIncidences n)
    (hy : y ∈ squareAnchorCoprimeSupportIncidences n)
    (hxy : squareAnchorIncidenceQuotient n x =
      squareAnchorIncidenceQuotient n y) :
    x = y := by
  rcases x with ⟨p, r⟩
  rcases y with ⟨q, s⟩
  change squareOffsetSupportQuotient n p r =
    squareOffsetSupportQuotient n q s at hxy
  by_cases hpq : p = q
  · subst q
    have hxs := mem_squareAnchorCoprimeSupportIncidences.mp hx
    have hys := mem_squareAnchorCoprimeSupportIncidences.mp hy
    have hrs := eq_of_same_prime_same_support_quotient hxs.2.2 hys.2.2 hxy
    cases hrs
    rfl
  · have hnlt := anchor_lt_four_of_distinct_prime_quotient_collision
      hx hy hpq hxy
    omega

theorem squareAnchorIncidenceQuotient_injective_of_four_le
    {n : ℕ} (hn : 4 ≤ n) :
    Set.InjOn (squareAnchorIncidenceQuotient n)
      (squareAnchorCoprimeSupportIncidences n : Set (ℕ × ℕ)) := by
  intro x hx y hy hxy
  exact squareAnchorIncidenceQuotient_eq_imp_eq_of_four_le hn hx hy hxy

/-- At `4 ≤ n`, the global quotient image preserves the incidence cardinality. -/
theorem card_squareAnchorCoprimeGlobalQuotients_of_four_le
    {n : ℕ} (hn : 4 ≤ n) :
    (squareAnchorCoprimeGlobalQuotients n).card =
      squareAnchorCoprimeNondivisorIncidence n := by
  calc
    (squareAnchorCoprimeGlobalQuotients n).card =
        (squareAnchorCoprimeSupportIncidences n).card := by
      unfold squareAnchorCoprimeGlobalQuotients
      exact (Finset.card_image_iff).2
        (squareAnchorIncidenceQuotient_injective_of_four_le hn)
    _ = squareAnchorCoprimeNondivisorIncidence n :=
      card_squareAnchorCoprimeSupportIncidences n

/-! ### PRIM-L014.5: quotient properties and the full-cover frontier -/

/-- Every global quotient lies above the anchor and is coprime to it. -/
theorem squareAnchorCoprimeGlobalQuotients_properties
    {n k : ℕ}
    (hk : k ∈ squareAnchorCoprimeGlobalQuotients n) :
    n < k ∧ Nat.Coprime n k := by
  rcases mem_squareAnchorCoprimeGlobalQuotients.mp hk with
    ⟨q, r, hqr, hqk⟩
  have hqr' := mem_squareAnchorCoprimeSupportIncidences.mp hqr
  have hq' := mem_squareAnchorNondivisorPrimes.mp hqr'.1
  have hr' := mem_squareAnchorCoprimeOffsets.mp hqr'.2.1
  have hlarge : n < squareOffsetSupportQuotient n q r :=
    anchor_lt_squareOffsetSupportQuotient hr'.1 hq'.2.1 hqr'.2.2
  have hcop : Nat.Coprime n (squareOffsetSupportQuotient n q r) :=
    (coprime_anchor_squareOffsetSupportQuotient_iff hq'.1 hq'.2.2
      hqr'.2.2).mpr hr'.2
  constructor
  · rw [← hqk]
    exact hlarge
  · rw [← hqk]
    exact hcop

/-- Preferred singular spelling for the global quotient property theorem. -/
theorem squareAnchorCoprimeGlobalQuotient_properties
    {n k : ℕ}
    (hk : k ∈ squareAnchorCoprimeGlobalQuotients n) :
    n < k ∧ Nat.Coprime n k :=
  squareAnchorCoprimeGlobalQuotients_properties hk

/-- Full cover gives the totient lower bound on the global quotient image. -/
theorem two_mul_totient_le_squareAnchorCoprimeGlobalQuotients_of_four_le_of_fullyCovered
    {n : ℕ}
    (hn : 4 ≤ n)
    (hfull : SquareOffsetsFullyCovered n) :
    2 * Nat.totient n ≤ (squareAnchorCoprimeGlobalQuotients n).card := by
  have hnpos : 0 < n := by omega
  calc
    2 * Nat.totient n ≤ squareAnchorCoprimeNondivisorIncidence n :=
      two_mul_totient_le_coprimeNondivisorIncidence_of_fullyCovered hnpos hfull
    _ = (squareAnchorCoprimeGlobalQuotients n).card :=
      (card_squareAnchorCoprimeGlobalQuotients_of_four_le hn).symm

/-- Preferred short name for the full-cover distinct-quotient frontier. -/
theorem two_mul_totient_le_card_globalQuotients_of_fullyCovered
    {n : ℕ}
    (hn : 4 ≤ n)
    (hfull : SquareOffsetsFullyCovered n) :
    2 * Nat.totient n ≤ (squareAnchorCoprimeGlobalQuotients n).card :=
  two_mul_totient_le_squareAnchorCoprimeGlobalQuotients_of_four_le_of_fullyCovered
    hn hfull

end DkMath.NumberTheory.Legendre

