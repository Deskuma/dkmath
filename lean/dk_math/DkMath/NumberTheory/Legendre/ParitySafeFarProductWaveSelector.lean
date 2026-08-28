/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeFarCofactorWave

#print "file: DkMath.NumberTheory.Legendre.ParitySafeFarProductWaveSelector"

/-!
## ParitySafeFarProductWaveSelector

PRIM-L047 returns the reduced cofactor information of PRIM-L046 to the
far product-wave universe of PRIM-L042.  A product-wave hit is selected by
two finite ownership conditions: its complementary quotient is reduced modulo
`2 * n`, and its first factor is the canonical support prime at the seat.

The module proves an exact finite selector model for actual far residual
incidences.  It does not introduce a sieve, a hypergraph, a prime-counting
estimate, or a smaller-anchor descent.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open DkMath.NumberTheory.Legendre.Internal
open scoped BigOperators

/-! ### PRIM-L047.1: far product-wave quotient -/

/-- The quotient complementary to a far product-wave key at seat `r`. -/
noncomputable def paritySafeFarProductWaveCofactor
    (n : ℕ) (key : ℕ × (ℕ × ℕ)) (r : ℕ) : ℕ :=
  (n ^ 2 + r) / paritySafeTripleProductModulus key

/-- A far product-wave hit has a positive, half-scale complementary quotient. -/
theorem paritySafeFarProductWaveCofactor_packet
    {n p q s r : ℕ}
    (hkey : (p, (q, s)) ∈ paritySafeTripleGateFarTriples n)
    (hr : r ∈ squareWaveOffsets n (p * q * s)) :
    let t := paritySafeFarProductWaveCofactor n (p, (q, s)) r
    0 < t ∧
      p * q * s * t = n ^ 2 + r ∧
      2 * t < n + 2 := by
  dsimp [paritySafeFarProductWaveCofactor]
  have hfar := (Finset.mem_filter.mp hkey).2
  have hgate := mem_paritySafeTripleGateTriples.mp
    (Finset.mem_filter.mp hkey).1
  rcases hgate with ⟨hp, hq, hs, hpq, hqs⟩
  have hpactive := (mem_paritySafeTripleGatePrimes.mp hp).1
  have hqprime := (mem_squareAnchorOddActivePrimes.mp hq).1
  have hsprime := (mem_squareAnchorOddActivePrimes.mp hs).1
  have hmpos : 0 < p * q * s := by
    exact Nat.mul_pos
      (Nat.mul_pos
        (mem_squareAnchorOddActivePrimes.mp hpactive).1.pos
        hqprime.pos) hsprime.pos
  have hdiv : p * q * s ∣ n ^ 2 + r := by
    simpa using (mem_squareWaveOffsets.mp hr).2
  have hoff := (mem_squareWaveOffsets.mp hr).1
  have hpointpos : 0 < n ^ 2 + r := by
    dsimp [SquareOffset] at hoff
    omega
  have hfactor : p * q * s * ((n ^ 2 + r) / (p * q * s)) = n ^ 2 + r :=
    Nat.mul_div_cancel' hdiv
  have htpos : 0 < (n ^ 2 + r) / (p * q * s) := by
    by_contra ht
    have htzero : (n ^ 2 + r) / (p * q * s) = 0 :=
      Nat.eq_zero_of_not_pos ht
    rw [htzero] at hfactor
    omega
  have hpointle : n ^ 2 + r ≤ n * (n + 2) := by
    dsimp [SquareOffset] at hoff
    nlinarith
  have hscaled :
      (2 * n) * ((n ^ 2 + r) / (p * q * s)) < n * (n + 2) := by
    calc
      (2 * n) * ((n ^ 2 + r) / (p * q * s)) <
          (p * q * s) * ((n ^ 2 + r) / (p * q * s)) :=
        Nat.mul_lt_mul_of_pos_right hfar htpos
      _ = n ^ 2 + r := hfactor
      _ ≤ n * (n + 2) := hpointle
  have hhalf : 2 * ((n ^ 2 + r) / (p * q * s)) < n + 2 := by
    nlinarith
  exact ⟨htpos, hfactor, hhalf⟩

/-! ### PRIM-L047.2: reduced product modulus -/

/-- A far triple product is coprime to the even anchor modulus. -/
theorem paritySafeTripleGateFarProductModulus_coprime_two_mul
    {n p q s : ℕ}
    (hkey : (p, (q, s)) ∈ paritySafeTripleGateFarTriples n) :
    Nat.Coprime (2 * n) (p * q * s) := by
  have hgate := mem_paritySafeTripleGateTriples.mp
    (Finset.mem_filter.mp hkey).1
  rcases hgate with ⟨hp, hq, hs, hpq, hqs⟩
  have hpcop := (activePrime_reducedResidue_packet
    (mem_paritySafeTripleGatePrimes.mp hp).1).2.2.2.2
  have hqcop := (activePrime_reducedResidue_packet hq).2.2.2.2
  have hscop := (activePrime_reducedResidue_packet hs).2.2.2.2
  rw [Nat.coprime_mul_iff_right, Nat.coprime_mul_iff_right]
  exact ⟨⟨hpcop, hqcop⟩, hscop⟩

/-! ### PRIM-L047.3: reduced-cofactor selector equivalence -/

/-- A product-wave seat is a parity-safe candidate exactly when its quotient is
reduced modulo `2 * n`. -/
theorem paritySafeFarProductWave_mem_candidate_iff_cofactor_coprime
    {n p q s r : ℕ}
    (hkey : (p, (q, s)) ∈ paritySafeTripleGateFarTriples n)
    (hr : r ∈ squareWaveOffsets n (p * q * s)) :
    r ∈ squareAnchorOddPointCoprimeOffsets n ↔
      Nat.Coprime (2 * n)
        (paritySafeFarProductWaveCofactor n (p, (q, s)) r) := by
  have hpacket := paritySafeFarProductWaveCofactor_packet hkey hr
  rcases hpacket with ⟨htpos, hfactor, hhalf⟩
  have hcopm := paritySafeTripleGateFarProductModulus_coprime_two_mul hkey
  have hmul :
      Nat.Coprime (2 * n)
          (paritySafeTripleProductModulus (p, (q, s)) *
            paritySafeFarProductWaveCofactor n (p, (q, s)) r) ↔
        Nat.Coprime (2 * n)
          (paritySafeFarProductWaveCofactor n (p, (q, s)) r) := by
    constructor
    · intro h
      exact (Nat.coprime_mul_iff_right.mp h).2
    · intro h
      exact hcopm.mul_right h
  rw [mem_squareAnchorOddPointCoprimeOffsets_iff_reducedResidue]
  constructor
  · intro h
    have hprod : Nat.Coprime (2 * n)
        (paritySafeTripleProductModulus (p, (q, s)) *
          paritySafeFarProductWaveCofactor n (p, (q, s)) r) := by
      have hprod' : Nat.Coprime (2 * n)
          (p * q * s * paritySafeFarProductWaveCofactor n (p, (q, s)) r) := by
        rw [hfactor]
        exact h.2
      simpa [paritySafeTripleProductModulus] using hprod'
    exact hmul.mp hprod
  · intro h
    refine ⟨(mem_squareWaveOffsets.mp hr).1, ?_⟩
    have hprod := hmul.mpr h
    have hprod' : Nat.Coprime (2 * n)
        (p * q * s * paritySafeFarProductWaveCofactor n (p, (q, s)) r) := by
      simpa [paritySafeTripleProductModulus] using hprod
    rw [hfactor] at hprod'
    exact hprod'

/-! ### PRIM-L047.4: exact selected offsets -/

/-- Far product-wave seats selected by reduced cofactor and canonical ownership. -/
noncomputable def paritySafeCanonicalFarProductWaveOffsets
    (n : ℕ) (key : ℕ × (ℕ × ℕ)) : Finset ℕ :=
  (squareWaveOffsets n (paritySafeTripleProductModulus key)).filter
    (fun r =>
      Nat.Coprime (2 * n)
        (paritySafeFarProductWaveCofactor n key r) ∧
      key.1 = paritySafeCanonicalSupportPrime n r)

/-- Membership in the selector exposes its wave, reduced-cofactor, and
canonical-ownership conditions. -/
@[simp] theorem mem_paritySafeCanonicalFarProductWaveOffsets
    {n : ℕ} {key : ℕ × (ℕ × ℕ)} {r : ℕ} :
    r ∈ paritySafeCanonicalFarProductWaveOffsets n key ↔
      r ∈ squareWaveOffsets n (paritySafeTripleProductModulus key) ∧
        Nat.Coprime (2 * n)
          (paritySafeFarProductWaveCofactor n key r) ∧
        key.1 = paritySafeCanonicalSupportPrime n r := by
  simp [paritySafeCanonicalFarProductWaveOffsets]

/-! ### PRIM-L047.5: selector to actual residual incidence -/

private theorem paritySafeCovered_of_candidate_of_canonical_eq
    {n r p : ℕ}
    (hr : r ∈ squareAnchorOddPointCoprimeOffsets n)
    (hpactive : p ∈ squareAnchorOddActivePrimes n)
    (hcanonical : p = paritySafeCanonicalSupportPrime n r) :
    r ∈ paritySafeCoveredCandidates n := by
  have hnonempty : (paritySafeActiveSupport n r).Nonempty := by
    by_contra hne
    have hzero : paritySafeCanonicalSupportPrime n r = 0 := by
      unfold paritySafeCanonicalSupportPrime
      rw [dif_neg hne]
    have hpne : p ≠ 0 := (mem_squareAnchorOddActivePrimes.mp hpactive).1.ne_zero
    exact hpne (hcanonical.trans hzero)
  exact mem_paritySafeCoveredCandidates.mpr ⟨hr, hnonempty⟩

/-- A selected far product-wave seat reconstructs the actual far residual pair. -/
theorem paritySafeCanonicalFarProductWaveOffset_mem_farResidual
    {n p q s r : ℕ}
    (hkey : (p, (q, s)) ∈ paritySafeTripleGateFarTriples n)
    (hr : r ∈ paritySafeCanonicalFarProductWaveOffsets n (p, (q, s))) :
    (r, (q, s)) ∈ paritySafeCanonicalFarResidualTripleIncidences n := by
  have hr' := mem_paritySafeCanonicalFarProductWaveOffsets.mp hr
  have hgate := mem_paritySafeTripleGateTriples.mp
    (Finset.mem_filter.mp hkey).1
  rcases hgate with ⟨hp, hq, hs, hpq, hqs⟩
  have hcanonical := hr'.2.2
  have hcandidate := (paritySafeFarProductWave_mem_candidate_iff_cofactor_coprime
    hkey hr'.1).mpr hr'.2.1
  have hcovered := paritySafeCovered_of_candidate_of_canonical_eq hcandidate
    (mem_paritySafeTripleGatePrimes.mp hp).1 hcanonical
  have hdiv : p * q * s ∣ n ^ 2 + r := by
    simpa [paritySafeTripleProductModulus] using (mem_squareWaveOffsets.mp hr'.1).2
  have hqdiv : q ∣ n ^ 2 + r := by
    apply dvd_trans (dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_right (dvd_refl q) _) _) hdiv
  have hsdiv : s ∣ n ^ 2 + r := by
    apply dvd_trans (dvd_mul_of_dvd_right (dvd_refl s) _) hdiv
  have hqpack := mem_squareAnchorOddActivePrimes.mp hq
  have hspack := mem_squareAnchorOddActivePrimes.mp hs
  have hqquot : q ∈ squareOffsetAnchorNondivisorSupport n r :=
    mem_squareOffsetAnchorNondivisorSupport.mpr
      ⟨hqpack.1, hqpack.2.1, hqpack.2.2.1, hqdiv⟩
  have hsquot : s ∈ squareOffsetAnchorNondivisorSupport n r :=
    mem_squareOffsetAnchorNondivisorSupport.mpr
      ⟨hspack.1, hspack.2.1, hspack.2.2.1, hsdiv⟩
  have hqerase : q ∈
      (squareQuotientAnchorNondivisorSupport n
        (paritySafeCanonicalSupportPrime n r) r).erase
          (paritySafeCanonicalSupportPrime n r) := by
    apply Finset.mem_erase.mpr
    refine ⟨?_, ?_⟩
    · intro heq
      subst q
      omega
    · have hpoff := (paritySafeCanonicalSupportPrime_packet hcovered).2.2.1
      have hqne : q ≠ paritySafeCanonicalSupportPrime n r := by
        intro heq
        subst q
        omega
      exact (mem_quotientSupport_iff_mem_offsetSupport_of_ne hpoff hqne).mpr hqquot
  have hserase : s ∈
      (squareQuotientAnchorNondivisorSupport n
        (paritySafeCanonicalSupportPrime n r) r).erase
          (paritySafeCanonicalSupportPrime n r) := by
    apply Finset.mem_erase.mpr
    refine ⟨?_, ?_⟩
    · intro heq
      subst s
      omega
    · have hpoff := (paritySafeCanonicalSupportPrime_packet hcovered).2.2.1
      have hsne : s ≠ paritySafeCanonicalSupportPrime n r := by
        intro heq
        subst s
        omega
      exact (mem_quotientSupport_iff_mem_offsetSupport_of_ne hpoff hsne).mpr hsquot
  apply mem_paritySafeCanonicalFarResidualTripleIncidences.mpr
  refine ⟨?_, ?_⟩
  · apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr
      ⟨hcovered, Finset.mem_product.mpr ⟨hq, hs⟩⟩,
      hqs, hqerase, hserase⟩
  · rw [← hcanonical]
    exact hkey

/-! ### PRIM-L047.6: actual residual incidence to selector -/

/-- The product-wave quotient agrees with the L046 far-triple cofactor. -/
theorem paritySafeFarProductWaveCofactor_eq_farTripleCofactor
    {n r q s : ℕ} :
    paritySafeFarProductWaveCofactor n
        (paritySafeCanonicalSupportPrime n r, (q, s)) r =
      paritySafeFarTripleCofactor n r q s := rfl

/-- Every actual far residual incidence is selected in its product wave. -/
theorem paritySafeCanonicalFarResidual_mem_productWaveSelector
    {n r q s : ℕ}
    (hfar : (r, (q, s)) ∈
      paritySafeCanonicalFarResidualTripleIncidences n) :
    r ∈ paritySafeCanonicalFarProductWaveOffsets n
      (paritySafeCanonicalSupportPrime n r, (q, s)) := by
  have hpacket := mem_paritySafeCanonicalFarResidualTripleIncidences.mp hfar
  have hinc := hpacket.1
  have hgate := hpacket.2
  have hwave := paritySafeCanonicalResidualTripleIncidence_mem_productWave hinc
  have hcofactor := (paritySafeFarTripleCofactor_packet hinc hgate).2.2.2.2
  apply mem_paritySafeCanonicalFarProductWaveOffsets.mpr
  exact ⟨hwave, by
    simpa [paritySafeFarProductWaveCofactor_eq_farTripleCofactor] using hcofactor,
    rfl⟩

/-! ### PRIM-L047.7: exact incidence model -/

/-- Selected product-wave incidences, with the key and seat retained. -/
noncomputable def paritySafeCanonicalFarProductWaveIncidences
    (n : ℕ) : Finset ((ℕ × (ℕ × ℕ)) × ℕ) :=
  ((paritySafeTripleGateFarTriples n).product (squareOffsets n)).filter
    (fun hit => hit.2 ∈ paritySafeCanonicalFarProductWaveOffsets n hit.1)

set_option maxHeartbeats 800000 in
-- The finite bijection proof unfolds two nested product/filter layers.
/-- The selected product-wave incidence set has the actual far-residual card. -/
theorem paritySafeCanonicalFarProductWaveIncidences_card_eq_farResidual
    (n : ℕ) :
    (paritySafeCanonicalFarProductWaveIncidences n).card =
      (paritySafeCanonicalFarResidualTripleIncidences n).card := by
  classical
  unfold paritySafeCanonicalFarProductWaveIncidences
  apply Eq.symm
  apply Finset.card_bij (fun triple _ =>
    ((paritySafeCanonicalSupportPrime n triple.1, triple.2), triple.1))
  · intro triple htriple
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨
      (mem_paritySafeCanonicalFarResidualTripleIncidences.mp htriple).2,
      mem_squareOffsets.mpr (mem_squareWaveOffsets.mp
        (paritySafeCanonicalResidualTripleIncidence_mem_productWave
          (mem_paritySafeCanonicalFarResidualTripleIncidences.mp htriple).1)).1⟩,
      paritySafeCanonicalFarResidual_mem_productWaveSelector htriple⟩
  · intro a ha b hb heq
    have hr : a.1 = b.1 := congrArg Prod.snd heq
    have hpair : a.2 = b.2 := congrArg (fun z => z.1.2) heq
    exact Prod.ext hr hpair
  · intro hit hhit
    rcases hit with ⟨⟨p, ⟨q, s⟩⟩, r⟩
    have hhit' := Finset.mem_filter.mp hhit
    have hkey : (p, (q, s)) ∈ paritySafeTripleGateFarTriples n :=
      (Finset.mem_product.mp hhit'.1).1
    have hactual := paritySafeCanonicalFarProductWaveOffset_mem_farResidual
      hkey hhit'.2
    have hp0 := (mem_paritySafeCanonicalFarProductWaveOffsets.mp hhit'.2).2.2
    have hp : p = paritySafeCanonicalSupportPrime n r := by
      simpa using hp0
    refine ⟨(r, (q, s)), hactual, ?_⟩
    change ((paritySafeCanonicalSupportPrime n r, (q, s)), r) =
      ((p, (q, s)), r)
    rw [hp]

/-- The actual far-residual card is the exact sum of selector fiber cards. -/
theorem paritySafeCanonicalFarResidual_card_eq_productWaveSelector_sum
    (n : ℕ) :
    (paritySafeCanonicalFarResidualTripleIncidences n).card =
      ∑ key ∈ paritySafeTripleGateFarTriples n,
        (paritySafeCanonicalFarProductWaveOffsets n key).card := by
  classical
  have hcard := paritySafeCanonicalFarProductWaveIncidences_card_eq_farResidual n
  rw [← hcard]
  unfold paritySafeCanonicalFarProductWaveIncidences
  calc
    (((paritySafeTripleGateFarTriples n).product (squareOffsets n)).filter
        (fun hit => hit.2 ∈ paritySafeCanonicalFarProductWaveOffsets n hit.1)).card =
      ∑ hit ∈ (paritySafeTripleGateFarTriples n).product (squareOffsets n),
        if hit.2 ∈ paritySafeCanonicalFarProductWaveOffsets n hit.1 then 1 else 0 := by
      simp
    _ = ∑ key ∈ paritySafeTripleGateFarTriples n,
        ∑ r ∈ squareOffsets n,
          if r ∈ paritySafeCanonicalFarProductWaveOffsets n key then 1 else 0 := by
      exact Finset.sum_product' (paritySafeTripleGateFarTriples n) (squareOffsets n)
        (fun key r => if r ∈ paritySafeCanonicalFarProductWaveOffsets n key then 1 else 0)
    _ = ∑ key ∈ paritySafeTripleGateFarTriples n,
        (paritySafeCanonicalFarProductWaveOffsets n key).card := by
      apply Finset.sum_congr rfl
      intro key hkey
      rw [Finset.sum_boole]
      apply congrArg Finset.card
      apply Finset.Subset.antisymm
      · intro r hr
        exact (Finset.mem_filter.mp hr).2
      · intro r hr
        exact Finset.mem_filter.mpr ⟨mem_squareOffsets.mpr (mem_squareWaveOffsets.mp
          (Finset.mem_filter.mp hr).1).1, hr⟩

end DkMath.NumberTheory.Legendre
