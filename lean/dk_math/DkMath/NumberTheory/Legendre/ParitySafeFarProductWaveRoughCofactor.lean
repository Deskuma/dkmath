/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeFarProductWaveSelector

#print "file: DkMath.NumberTheory.Legendre.ParitySafeFarProductWaveRoughCofactor"

/-!
## ParitySafeFarProductWaveRoughCofactor

PRIM-L048 removes the explicit canonical-minimum field from the L047 far
product-wave selector.  Below the first product prime `p`, an active prime
direction divides the complete point exactly when it divides the complementary
cofactor.  Thus canonical ownership is equivalent to a finite roughness
condition on that cofactor.

This is a finite exclusion rewrite.  It does not introduce a rough-number
estimate, an analytic sieve, or a smaller-anchor descent.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open DkMath.NumberTheory.Legendre.Internal
open scoped BigOperators

/-! ### PRIM-L048.1: smaller active direction and cofactor divisor -/

/-- Below the first far product prime, active support is exactly cofactor
divisibility. -/
theorem paritySafeFarProductWave_smallerActive_mem_support_iff_dvd_cofactor
    {n p q s r a : ℕ}
    (hkey : (p, (q, s)) ∈ paritySafeTripleGateFarTriples n)
    (hr : r ∈ squareWaveOffsets n (p * q * s))
    (ha : a ∈ squareAnchorOddActivePrimes n)
    (hap : a < p) :
    a ∈ paritySafeActiveSupport n r ↔
      a ∣ paritySafeFarProductWaveCofactor n (p, (q, s)) r := by
  classical
  have hpacket := paritySafeFarProductWaveCofactor_packet hkey hr
  rcases hpacket with ⟨htpos, hfactor, hhalf⟩
  have hgate := mem_paritySafeTripleGateTriples.mp
    (Finset.mem_filter.mp hkey).1
  rcases hgate with ⟨hp, hq, hs, hpq, hqs⟩
  have hpactive := (mem_paritySafeTripleGatePrimes.mp hp).1
  have hpprime := (mem_squareAnchorOddActivePrimes.mp hpactive).1
  have hqprime := (mem_squareAnchorOddActivePrimes.mp hq).1
  have hsprime := (mem_squareAnchorOddActivePrimes.mp hs).1
  have haprime := (mem_squareAnchorOddActivePrimes.mp ha).1
  constructor
  · intro has
    have hpointdiv : a ∣ n ^ 2 + r := by
      simpa [paritySafeActiveSupport, SquareOffsetForbiddenBy] using
        (Finset.mem_filter.mp has).2
    have hmul : a ∣ p * q * s *
        paritySafeFarProductWaveCofactor n (p, (q, s)) r := by
      rw [hfactor]
      exact hpointdiv
    rcases (haprime.dvd_mul).mp hmul with hprod | hat
    · rcases (haprime.dvd_mul).mp hprod with hpq' | hs'
      · rcases (haprime.dvd_mul).mp hpq' with hp' | hq'
        · have hae : a = p :=
            ((Nat.dvd_prime hpprime).mp hp').resolve_left haprime.ne_one
          exfalso
          omega
        · have hae : a = q :=
            ((Nat.dvd_prime hqprime).mp hq').resolve_left haprime.ne_one
          exfalso
          omega
      · have hae : a = s :=
          ((Nat.dvd_prime hsprime).mp hs').resolve_left haprime.ne_one
        exfalso
        omega
    · exact hat
  · intro hat
    have hpointdiv : a ∣ n ^ 2 + r := by
      rw [← hfactor]
      exact dvd_mul_of_dvd_right hat (p * q * s)
    rw [paritySafeActiveSupport]
    exact Finset.mem_filter.mpr ⟨ha, by
      simpa [SquareOffsetForbiddenBy] using hpointdiv⟩

/-! ### PRIM-L048.2: canonical minimum and roughness -/

private theorem paritySafeFarProductWave_canonical_support_packet
    {n p q s r : ℕ}
    (hkey : (p, (q, s)) ∈ paritySafeTripleGateFarTriples n)
    (hr : r ∈ squareWaveOffsets n (p * q * s)) :
    p ∈ paritySafeActiveSupport n r ∧
      (paritySafeActiveSupport n r).Nonempty := by
  classical
  have hgate := mem_paritySafeTripleGateTriples.mp
    (Finset.mem_filter.mp hkey).1
  rcases hgate with ⟨hp, hq, hs, hpq, hqs⟩
  have hpactive := (mem_paritySafeTripleGatePrimes.mp hp).1
  have hdiv : p ∣ n ^ 2 + r := by
    have hwave := (mem_squareWaveOffsets.mp hr).2
    have hpmul : p ∣ p * q * s := by
      exact dvd_mul_of_dvd_left (dvd_mul_right p q) s
    exact dvd_trans hpmul (by
      simpa [paritySafeTripleProductModulus] using hwave)
  have hpsupport : p ∈ paritySafeActiveSupport n r := by
    rw [paritySafeActiveSupport]
    exact Finset.mem_filter.mpr ⟨hpactive, by
      simpa [SquareOffsetForbiddenBy] using hdiv⟩
  exact ⟨hpsupport, ⟨p, hpsupport⟩⟩

/-- Canonical ownership is equivalent to having no smaller active prime
divisor in the complementary cofactor. -/
theorem paritySafeFarProductWave_canonical_eq_iff_no_smaller_active_dvd_cofactor
    {n p q s r : ℕ}
    (hkey : (p, (q, s)) ∈ paritySafeTripleGateFarTriples n)
    (hr : r ∈ squareWaveOffsets n (p * q * s)) :
    p = paritySafeCanonicalSupportPrime n r ↔
      ∀ a ∈ squareAnchorOddActivePrimes n,
        a < p →
          ¬ a ∣ paritySafeFarProductWaveCofactor n (p, (q, s)) r := by
  classical
  have hsupport := paritySafeFarProductWave_canonical_support_packet hkey hr
  rcases hsupport with ⟨hpsupport, hnonempty⟩
  constructor
  · intro hcanonical a ha hap hdiv
    have hminCanonical : p = (paritySafeActiveSupport n r).min' hnonempty := by
      unfold paritySafeCanonicalSupportPrime at hcanonical
      rw [dif_pos hnonempty] at hcanonical
      exact hcanonical
    have hasupport :=
      (paritySafeFarProductWave_smallerActive_mem_support_iff_dvd_cofactor
        hkey hr ha hap).mpr hdiv
    have hmin : paritySafeCanonicalSupportPrime n r ≤ a := by
      calc
        paritySafeCanonicalSupportPrime n r = p := hcanonical.symm
        _ = (paritySafeActiveSupport n r).min' hnonempty := hminCanonical
        _ ≤ a := Finset.min'_le _ _ hasupport
    omega
  · intro hrough
    have hmin : p = (paritySafeActiveSupport n r).min' hnonempty := by
      have hmp : (paritySafeActiveSupport n r).min' hnonempty = p := by
        apply (Finset.min'_eq_iff
          (s := paritySafeActiveSupport n r) (H := hnonempty) p).2
        constructor
        · exact hpsupport
        · intro a ha
          by_cases hap : a < p
          · exact False.elim (hrough a
              ((Finset.mem_filter.mp ha).1) hap
              ((paritySafeFarProductWave_smallerActive_mem_support_iff_dvd_cofactor
                hkey hr ((Finset.mem_filter.mp ha).1) hap).mp ha))
          · omega
      exact hmp.symm
    unfold paritySafeCanonicalSupportPrime
    rw [dif_pos hnonempty]
    exact hmin

/-! ### PRIM-L048.3: rough selector -/

/-- Product-wave seats selected by a reduced cofactor with no smaller active
prime divisor. -/
noncomputable def paritySafeFarProductWaveRoughOffsets
    (n : ℕ) (key : ℕ × (ℕ × ℕ)) : Finset ℕ :=
  (squareWaveOffsets n (paritySafeTripleProductModulus key)).filter
    (fun r =>
      Nat.Coprime (2 * n)
        (paritySafeFarProductWaveCofactor n key r) ∧
      ∀ a ∈ squareAnchorOddActivePrimes n,
        a < key.1 →
          ¬ a ∣ paritySafeFarProductWaveCofactor n key r)

/-- Membership in the rough selector exposes its reduced and exclusion
conditions. -/
@[simp] theorem mem_paritySafeFarProductWaveRoughOffsets
    {n : ℕ} {key : ℕ × (ℕ × ℕ)} {r : ℕ} :
    r ∈ paritySafeFarProductWaveRoughOffsets n key ↔
      r ∈ squareWaveOffsets n (paritySafeTripleProductModulus key) ∧
        Nat.Coprime (2 * n)
          (paritySafeFarProductWaveCofactor n key r) ∧
        ∀ a ∈ squareAnchorOddActivePrimes n,
          a < key.1 →
            ¬ a ∣ paritySafeFarProductWaveCofactor n key r := by
  simp [paritySafeFarProductWaveRoughOffsets]

/-- On a far key, the rough selector is exactly the L047 canonical selector. -/
theorem paritySafeFarProductWaveRoughOffsets_eq_canonicalSelector
    {n p q s : ℕ}
    (hkey : (p, (q, s)) ∈ paritySafeTripleGateFarTriples n) :
    paritySafeFarProductWaveRoughOffsets n (p, (q, s)) =
      paritySafeCanonicalFarProductWaveOffsets n (p, (q, s)) := by
  ext r
  by_cases hwave : r ∈ squareWaveOffsets n (p * q * s)
  · have hcanon :=
      paritySafeFarProductWave_canonical_eq_iff_no_smaller_active_dvd_cofactor
        hkey hwave
    simp only [mem_paritySafeFarProductWaveRoughOffsets,
      mem_paritySafeCanonicalFarProductWaveOffsets]
    constructor
    · rintro ⟨_, hcop, hrough⟩
      exact ⟨hwave, hcop, hcanon.mpr hrough⟩
    · rintro ⟨_, hcop, hcanonical⟩
      exact ⟨hwave, hcop, hcanon.mp hcanonical⟩
  · simp only [mem_paritySafeFarProductWaveRoughOffsets,
      mem_paritySafeCanonicalFarProductWaveOffsets]
    have hwave' : r ∉ squareWaveOffsets n
        (paritySafeTripleProductModulus (p, (q, s))) := by
      simpa [paritySafeTripleProductModulus] using hwave
    simp [hwave']

/-! ### PRIM-L048.4: exact rough-fiber sum and 0/1 fibers -/

/-- The actual far-residual card is the exact sum of rough selector fibers. -/
theorem paritySafeCanonicalFarResidual_card_eq_roughProductWaveSelector_sum
    (n : ℕ) :
    (paritySafeCanonicalFarResidualTripleIncidences n).card =
      ∑ key ∈ paritySafeTripleGateFarTriples n,
        (paritySafeFarProductWaveRoughOffsets n key).card := by
  rw [paritySafeCanonicalFarResidual_card_eq_productWaveSelector_sum]
  apply Finset.sum_congr rfl
  intro key hkey
  rcases key with ⟨p, q, s⟩
  rw [paritySafeFarProductWaveRoughOffsets_eq_canonicalSelector hkey]

/-- Each far rough selector fiber contains at most one seat. -/
theorem paritySafeFarProductWaveRoughOffsets_card_le_one
    {n p q s : ℕ}
    (hkey : (p, (q, s)) ∈ paritySafeTripleGateFarTriples n) :
    (paritySafeFarProductWaveRoughOffsets n (p, (q, s))).card ≤ 1 := by
  rw [paritySafeFarProductWaveRoughOffsets_eq_canonicalSelector hkey]
  exact (Finset.card_le_card (by
    intro r hr
    exact (mem_paritySafeCanonicalFarProductWaveOffsets.mp hr).1)).trans
      (paritySafeTripleGateFar_wave_card_le_one hkey)

/-! ### PRIM-L048.5: prime-floor consumer -/

/-- A prime divisor of a rough cofactor cannot lie below the key's first
product prime. -/
theorem paritySafeFarProductWaveRough_primeFactor_ge_key
    {n p q s r u : ℕ}
    (hkey : (p, (q, s)) ∈ paritySafeTripleGateFarTriples n)
    (hr : r ∈ paritySafeFarProductWaveRoughOffsets n (p, (q, s)))
    (huprime : Nat.Prime u)
    (hudvd : u ∣ paritySafeFarProductWaveCofactor n (p, (q, s)) r) :
    p ≤ u := by
  have hrough := mem_paritySafeFarProductWaveRoughOffsets.mp hr
  have hcanonical : r ∈ paritySafeCanonicalFarProductWaveOffsets n (p, (q, s)) := by
    rw [← paritySafeFarProductWaveRoughOffsets_eq_canonicalSelector hkey]
    exact hr
  have hinc := paritySafeCanonicalFarProductWaveOffset_mem_farResidual hkey hcanonical
  have hgate : (paritySafeCanonicalSupportPrime n r, (q, s)) ∈
      paritySafeTripleGateFarTriples n :=
    (mem_paritySafeCanonicalFarResidualTripleIncidences.mp hinc).2
  have hpcan : p = paritySafeCanonicalSupportPrime n r :=
    (mem_paritySafeCanonicalFarProductWaveOffsets.mp hcanonical).2.2
  have hudvd0 : u ∣ paritySafeFarProductWaveCofactor n
      (paritySafeCanonicalSupportPrime n r, (q, s)) r := by
    simpa [hpcan] using hudvd
  have hudvd' : u ∣ paritySafeFarTripleCofactor n r q s := by
    simpa [paritySafeFarProductWaveCofactor_eq_farTripleCofactor] using hudvd0
  have hreturn := paritySafeFarTripleCofactor_prime_divisor_return
    (mem_paritySafeCanonicalFarResidualTripleIncidences.mp hinc).1 hgate huprime hudvd'
  by_contra hpu
  have hup : u < p := by omega
  exact hrough.2.2 u hreturn.1 hup hudvd

/-- A nontrivial rough cofactor is at least the first product prime. -/
theorem paritySafeFarProductWaveRough_nontrivial_cofactor_ge_key
    {n p q s r : ℕ}
    (hkey : (p, (q, s)) ∈ paritySafeTripleGateFarTriples n)
    (hr : r ∈ paritySafeFarProductWaveRoughOffsets n (p, (q, s)))
    (ht : 1 < paritySafeFarProductWaveCofactor n (p, (q, s)) r) :
    p ≤ paritySafeFarProductWaveCofactor n (p, (q, s)) r := by
  obtain ⟨u, huprime, hudvd⟩ :=
    Nat.exists_prime_and_dvd (Nat.ne_of_gt ht)
  have hup := paritySafeFarProductWaveRough_primeFactor_ge_key hkey hr huprime hudvd
  exact hup.trans (Nat.le_of_dvd (by omega) hudvd)

/-! ### PRIM-L048.6: arithmetic false beam -/

/-- The cofactor may contain the canonical prime itself; roughness only
excludes smaller active primes. -/
theorem paritySafeFarProductWaveRough_depth_false_beam_17_26 :
    17 ^ 2 + 26 = 3 * 5 * 7 * 3 ∧
      2 * 17 < 3 * 5 * 7 ∧
      (17 ^ 2 + 26) / (3 * 5 * 7) = 3 := by
  norm_num

end DkMath.NumberTheory.Legendre
