/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeFarProductWaveRoughCofactor

#print "file: DkMath.NumberTheory.Legendre.ParitySafeFarProductWaveSurvival"

/-!
## ParitySafeFarProductWaveSurvival

PRIM-L049 identifies the unique possible far product-wave seat in the square
shell.  For a far key with modulus `m`, the first multiple of `m` above
`n ^ 2` has quotient `n ^ 2 / m + 1` and seat `m * t - n ^ 2`.  Consequently,
the rough selector from PRIM-L048 is either this singleton or empty, and the
far residual card is the number of surviving far keys.

This is a finite shell-representative calculation.  It does not count
surviving keys asymptotically, introduce an analytic sieve, or prove a global
Legendre or RH statement.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open DkMath.NumberTheory.Legendre.Internal
noncomputable section
local instance classicalDecidable (p : Prop) : Decidable p := Classical.propDecidable p
open scoped BigOperators

/-! ### PRIM-L049.1: next quotient, seat, and shell fit -/

/-- The quotient of the first product multiple strictly above `n ^ 2`. -/
def paritySafeFarProductWaveNextQuotient
    (n : ℕ) (key : ℕ × (ℕ × ℕ)) : ℕ :=
  n ^ 2 / paritySafeTripleProductModulus key + 1

/-- The shell offset belonging to the first product multiple above `n ^ 2`. -/
def paritySafeFarProductWaveNextSeat
    (n : ℕ) (key : ℕ × (ℕ × ℕ)) : ℕ :=
  paritySafeTripleProductModulus key *
      paritySafeFarProductWaveNextQuotient n key - n ^ 2

/-- Whether the first multiple above `n ^ 2` lies in the square shell. -/
def ParitySafeFarProductKeyFitsShell
    (n : ℕ) (key : ℕ × (ℕ × ℕ)) : Prop :=
  paritySafeTripleProductModulus key *
      paritySafeFarProductWaveNextQuotient n key ≤
    n ^ 2 + 2 * n

private theorem eq_div_add_one_of_mul_in_next_window
    {N m t : ℕ}
    (hm : 0 < m)
    (hlo : N < m * t)
    (hhi : m * t < N + m) :
    t = N / m + 1 := by
  have hdecomp : m * (N / m) + N % m = N := Nat.div_add_mod N m
  have hrem : N % m < m := Nat.mod_lt N hm
  have hmul_lo : m * (N / m) < m * t := by
    exact lt_of_le_of_lt (by
      simpa [Nat.mul_comm] using Nat.div_mul_le_self N m) hlo
  have hquot_lo : N / m < t := (Nat.mul_lt_mul_left hm).mp hmul_lo
  have hmul_hi : m * t < m * (N / m + 2) := by
    nlinarith
  have hquot_hi : t < N / m + 2 := (Nat.mul_lt_mul_left hm).mp hmul_hi
  omega

private theorem next_multiple_above_anchor
    {N m : ℕ}
    (hm : 0 < m) :
    N < m * (N / m + 1) := by
  have hdecomp : m * (N / m) + N % m = N := Nat.div_add_mod N m
  have hrem : N % m < m := Nat.mod_lt N hm
  nlinarith

/-! ### PRIM-L049.2: unique far-wave representative -/

/-- A far product-wave hit has exactly the next quotient. -/
theorem paritySafeFarProductWaveCofactor_eq_nextQuotient
    {n p q s r : ℕ}
    (hkey : (p, (q, s)) ∈ paritySafeTripleGateFarTriples n)
    (hr : r ∈ squareWaveOffsets n (p * q * s)) :
    paritySafeFarProductWaveCofactor n (p, (q, s)) r =
      paritySafeFarProductWaveNextQuotient n (p, (q, s)) := by
  have hpacket := paritySafeFarProductWaveCofactor_packet hkey hr
  rcases hpacket with ⟨htpos, hfactor, hhalf⟩
  have hfar := (Finset.mem_filter.mp hkey).2
  have hgate := mem_paritySafeTripleGateTriples.mp
    (Finset.mem_filter.mp hkey).1
  rcases hgate with ⟨hp, hq, hs, hpq, hqs⟩
  have hmpos : 0 < p * q * s := by
    exact Nat.mul_pos
      (Nat.mul_pos
        (mem_squareAnchorOddActivePrimes.mp
          (mem_paritySafeTripleGatePrimes.mp hp).1).1.pos
        (mem_squareAnchorOddActivePrimes.mp hq).1.pos)
      (mem_squareAnchorOddActivePrimes.mp hs).1.pos
  have hoff := (mem_squareWaveOffsets.mp hr).1
  have hlt : n ^ 2 <
      p * q * s * paritySafeFarProductWaveCofactor n (p, (q, s)) r := by
    rw [hfactor]
    dsimp [SquareOffset] at hoff
    omega
  have hseat_lt :
      p * q * s * paritySafeFarProductWaveCofactor n (p, (q, s)) r <
        n ^ 2 + p * q * s := by
    rw [hfactor]
    exact Nat.add_lt_add_left
      (lt_of_le_of_lt hoff.2 hfar) (n ^ 2)
  unfold paritySafeFarProductWaveNextQuotient
  exact eq_div_add_one_of_mul_in_next_window hmpos hlt hseat_lt

/-- In a far wave, membership is exactly fit of the next multiple and equality
with its explicit shell seat. -/
theorem mem_squareWaveOffsets_farKey_iff_eq_nextSeat
    {n p q s r : ℕ}
    (hkey : (p, (q, s)) ∈ paritySafeTripleGateFarTriples n) :
    r ∈ squareWaveOffsets n (p * q * s) ↔
      ParitySafeFarProductKeyFitsShell n (p, (q, s)) ∧
        r = paritySafeFarProductWaveNextSeat n (p, (q, s)) := by
  classical
  have hfar := (Finset.mem_filter.mp hkey).2
  have hgate := mem_paritySafeTripleGateTriples.mp
    (Finset.mem_filter.mp hkey).1
  rcases hgate with ⟨hp, hq, hs, hpq, hqs⟩
  have hmpos : 0 < p * q * s := by
    exact Nat.mul_pos
      (Nat.mul_pos
        (mem_squareAnchorOddActivePrimes.mp
          (mem_paritySafeTripleGatePrimes.mp hp).1).1.pos
        (mem_squareAnchorOddActivePrimes.mp hq).1.pos)
      (mem_squareAnchorOddActivePrimes.mp hs).1.pos
  constructor
  · intro hr
    have hpacket := paritySafeFarProductWaveCofactor_packet hkey hr
    rcases hpacket with ⟨htpos, hfactor, hhalf⟩
    have hquot := paritySafeFarProductWaveCofactor_eq_nextQuotient hkey hr
    have hoff := (mem_squareWaveOffsets.mp hr).1
    have hfit : ParitySafeFarProductKeyFitsShell n (p, (q, s)) := by
      unfold ParitySafeFarProductKeyFitsShell
      simp only [paritySafeTripleProductModulus]
      rw [← hquot, hfactor]
      exact Nat.add_le_add_left hoff.2 (n ^ 2)
    have hseat : r = paritySafeFarProductWaveNextSeat n (p, (q, s)) := by
      unfold paritySafeFarProductWaveNextSeat
      change r = p * q * s *
        paritySafeFarProductWaveNextQuotient n (p, (q, s)) - n ^ 2
      rw [← hquot]
      omega
    exact ⟨hfit, hseat⟩
  · rintro ⟨hfit, rfl⟩
    have hnext : n ^ 2 <
        p * q * s * paritySafeFarProductWaveNextQuotient n (p, (q, s)) := by
      exact next_multiple_above_anchor hmpos
    have hupper : p * q * s *
        paritySafeFarProductWaveNextQuotient n (p, (q, s)) ≤
        n ^ 2 + 2 * n := by
      exact hfit
    apply mem_squareWaveOffsets.mpr
    constructor
    · unfold paritySafeFarProductWaveNextSeat
      simp only [paritySafeTripleProductModulus]
      dsimp [SquareOffset]
      omega
    · unfold paritySafeFarProductWaveNextSeat
      change p * q * s ∣ n ^ 2 +
        (p * q * s * paritySafeFarProductWaveNextQuotient n (p, (q, s)) - n ^ 2)
      have hpoint : n ^ 2 +
          (p * q * s * paritySafeFarProductWaveNextQuotient n (p, (q, s)) -
            n ^ 2) =
          p * q * s * paritySafeFarProductWaveNextQuotient n (p, (q, s)) := by
        omega
      rw [hpoint]
      exact dvd_mul_right (p * q * s)
        (paritySafeFarProductWaveNextQuotient n (p, (q, s)))

/-- The far wave is the explicit singleton when it fits, and empty otherwise. -/
theorem squareWaveOffsets_farKey_eq_if_singleton
    {n p q s : ℕ}
    (hkey : (p, (q, s)) ∈ paritySafeTripleGateFarTriples n) :
    squareWaveOffsets n (p * q * s) =
      if ParitySafeFarProductKeyFitsShell n (p, (q, s)) then
        {paritySafeFarProductWaveNextSeat n (p, (q, s))}
      else ∅ := by
  classical
  ext r
  by_cases hfit : ParitySafeFarProductKeyFitsShell n (p, (q, s))
  · simp [hfit, mem_squareWaveOffsets_farKey_iff_eq_nextSeat hkey]
  · simp [hfit, mem_squareWaveOffsets_farKey_iff_eq_nextSeat hkey]

/-! ### PRIM-L049.3: next-seat cofactor -/

/-- At the explicit next seat, the L047 cofactor is the next quotient. -/
theorem paritySafeFarProductWaveCofactor_nextSeat_eq_nextQuotient
    {n p q s : ℕ}
    (hkey : (p, (q, s)) ∈ paritySafeTripleGateFarTriples n)
    (hfit : ParitySafeFarProductKeyFitsShell n (p, (q, s))) :
    paritySafeFarProductWaveCofactor n (p, (q, s))
        (paritySafeFarProductWaveNextSeat n (p, (q, s))) =
      paritySafeFarProductWaveNextQuotient n (p, (q, s)) := by
  apply paritySafeFarProductWaveCofactor_eq_nextQuotient hkey
  exact (mem_squareWaveOffsets_farKey_iff_eq_nextSeat hkey).mpr
    ⟨hfit, rfl⟩

/-! ### PRIM-L049.4: explicit survival predicate -/

/-- The finite conditions for the unique far product-wave seat to survive. -/
def ParitySafeFarProductKeySurvives
    (n : ℕ) (key : ℕ × (ℕ × ℕ)) : Prop :=
  ParitySafeFarProductKeyFitsShell n key ∧
    Nat.Coprime (2 * n) (paritySafeFarProductWaveNextQuotient n key) ∧
    ∀ a ∈ squareAnchorOddActivePrimes n,
      a < key.1 →
        ¬ a ∣ paritySafeFarProductWaveNextQuotient n key

@[simp] theorem paritySafeFarProductKeySurvives_iff
    {n : ℕ} {key : ℕ × (ℕ × ℕ)} :
    ParitySafeFarProductKeySurvives n key ↔
      ParitySafeFarProductKeyFitsShell n key ∧
        Nat.Coprime (2 * n) (paritySafeFarProductWaveNextQuotient n key) ∧
        ∀ a ∈ squareAnchorOddActivePrimes n,
          a < key.1 →
            ¬ a ∣ paritySafeFarProductWaveNextQuotient n key := by
  rfl

/-! ### PRIM-L049.5: rough fiber singleton/empty law -/

/-- Rough selector membership is the survival predicate plus the unique seat. -/
theorem mem_paritySafeFarProductWaveRoughOffsets_iff_survives_and_eq_nextSeat
    {n p q s r : ℕ}
    (hkey : (p, (q, s)) ∈ paritySafeTripleGateFarTriples n) :
    r ∈ paritySafeFarProductWaveRoughOffsets n (p, (q, s)) ↔
      ParitySafeFarProductKeySurvives n (p, (q, s)) ∧
        r = paritySafeFarProductWaveNextSeat n (p, (q, s)) := by
  constructor
  · intro hr
    have hrough := mem_paritySafeFarProductWaveRoughOffsets.mp hr
    have hwave := hrough.1
    have hquot := paritySafeFarProductWaveCofactor_eq_nextQuotient hkey hwave
    have hseat := (mem_squareWaveOffsets_farKey_iff_eq_nextSeat hkey).mp hwave
    rcases hseat with ⟨hfit, hEq⟩
    refine ⟨?_, hEq⟩
    refine ⟨hfit, ?_, ?_⟩
    · simpa [hquot] using hrough.2.1
    · intro a ha hap hadiv
      apply hrough.2.2 a ha hap
      simpa [hquot] using hadiv
  · rintro ⟨hsurv, rfl⟩
    apply mem_paritySafeFarProductWaveRoughOffsets.mpr
    have hwave := (mem_squareWaveOffsets_farKey_iff_eq_nextSeat hkey).mpr
      ⟨hsurv.1, rfl⟩
    refine ⟨hwave, ?_, ?_⟩
    · have hcofactor := paritySafeFarProductWaveCofactor_nextSeat_eq_nextQuotient
        hkey hsurv.1
      simpa [hcofactor] using hsurv.2.1
    · have hcofactor := paritySafeFarProductWaveCofactor_nextSeat_eq_nextQuotient
        hkey hsurv.1
      intro a ha hap hadiv
      apply hsurv.2.2 a ha hap
      simpa [hcofactor] using hadiv

/-- The rough selector is the singleton of its next seat exactly when the key
survives, and is empty otherwise. -/
theorem paritySafeFarProductWaveRoughOffsets_eq_if_survives
    {n p q s : ℕ}
    (hkey : (p, (q, s)) ∈ paritySafeTripleGateFarTriples n) :
    paritySafeFarProductWaveRoughOffsets n (p, (q, s)) =
      if ParitySafeFarProductKeySurvives n (p, (q, s)) then
        {paritySafeFarProductWaveNextSeat n (p, (q, s))}
      else ∅ := by
  classical
  ext r
  by_cases hsurv : ParitySafeFarProductKeySurvives n (p, (q, s))
  · rw [ite_eq_left hsurv]
    constructor
    · intro hr
      exact Finset.mem_singleton.mpr
        ((mem_paritySafeFarProductWaveRoughOffsets_iff_survives_and_eq_nextSeat
          hkey).mp hr).2
    · intro hr
      exact (mem_paritySafeFarProductWaveRoughOffsets_iff_survives_and_eq_nextSeat
        hkey).mpr ⟨hsurv, Finset.mem_singleton.mp hr⟩
  · rw [ite_eq_right hsurv]
    constructor
    · intro hr
      exact False.elim (hsurv
        ((mem_paritySafeFarProductWaveRoughOffsets_iff_survives_and_eq_nextSeat
          hkey).mp hr).1)
    · intro hr
      simp at hr

/-- The rough selector fiber has exact cardinality `1` or `0`. -/
theorem paritySafeFarProductWaveRoughOffsets_card_eq_if_survives
    {n p q s : ℕ}
    (hkey : (p, (q, s)) ∈ paritySafeTripleGateFarTriples n) :
    (paritySafeFarProductWaveRoughOffsets n (p, (q, s))).card =
      if ParitySafeFarProductKeySurvives n (p, (q, s)) then 1 else 0 := by
  rw [paritySafeFarProductWaveRoughOffsets_eq_if_survives hkey]
  split <;> simp [*]

/-! ### PRIM-L049.6: surviving keys and exact global count -/

/-- Far keys whose explicit next seat passes all L048 survival conditions. -/
noncomputable def paritySafeSurvivingFarProductKeys (n : ℕ) :
    Finset (ℕ × (ℕ × ℕ)) :=
  (paritySafeTripleGateFarTriples n).filter
    (ParitySafeFarProductKeySurvives n)

@[simp] theorem mem_paritySafeSurvivingFarProductKeys
    {n : ℕ} {key : ℕ × (ℕ × ℕ)} :
    key ∈ paritySafeSurvivingFarProductKeys n ↔
      key ∈ paritySafeTripleGateFarTriples n ∧
        ParitySafeFarProductKeySurvives n key := by
  simp [paritySafeSurvivingFarProductKeys]

/-- The actual far residual card is exactly the number of surviving far keys. -/
theorem paritySafeCanonicalFarResidual_card_eq_survivingFarProductKeys_card
    (n : ℕ) :
    (paritySafeCanonicalFarResidualTripleIncidences n).card =
      (paritySafeSurvivingFarProductKeys n).card := by
  rw [paritySafeCanonicalFarResidual_card_eq_roughProductWaveSelector_sum]
  change (∑ key ∈ paritySafeTripleGateFarTriples n,
      (paritySafeFarProductWaveRoughOffsets n key).card) =
    ((paritySafeTripleGateFarTriples n).filter
      (fun key => ParitySafeFarProductKeySurvives n key)).card
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro key hkey
  rcases key with ⟨p, q, s⟩
  rw [paritySafeFarProductWaveRoughOffsets_card_eq_if_survives hkey]

/-! ### PRIM-L049.7: half-scale consumer -/

/-- A surviving key has quotient `1`, or its first prime is below half scale. -/
theorem paritySafeFarProductKeySurvives_nextQuotient_one_or_key_halfScale
    {n p q s : ℕ}
    (hkey : (p, (q, s)) ∈ paritySafeTripleGateFarTriples n)
    (hsurv : ParitySafeFarProductKeySurvives n (p, (q, s))) :
    paritySafeFarProductWaveNextQuotient n (p, (q, s)) = 1 ∨
      2 * p < n + 2 := by
  by_cases ht : paritySafeFarProductWaveNextQuotient n (p, (q, s)) = 1
  · exact Or.inl ht
  · right
    have htpos : 0 < paritySafeFarProductWaveNextQuotient n (p, (q, s)) := by
      unfold paritySafeFarProductWaveNextQuotient
      exact Nat.zero_lt_succ _
    have htgt : 1 < paritySafeFarProductWaveNextQuotient n (p, (q, s)) := by
      omega
    have hwave := (mem_squareWaveOffsets_farKey_iff_eq_nextSeat hkey).mpr
      ⟨hsurv.1, rfl⟩
    have hrough : paritySafeFarProductWaveNextSeat n (p, (q, s)) ∈
        paritySafeFarProductWaveRoughOffsets n (p, (q, s)) := by
      exact (mem_paritySafeFarProductWaveRoughOffsets_iff_survives_and_eq_nextSeat
        hkey).mpr ⟨hsurv, rfl⟩
    have hcofactor := paritySafeFarProductWaveCofactor_nextSeat_eq_nextQuotient
      hkey hsurv.1
    have htgt' : 1 < paritySafeFarProductWaveCofactor n (p, (q, s))
        (paritySafeFarProductWaveNextSeat n (p, (q, s))) := by
      rw [hcofactor]
      exact htgt
    have hfloor := paritySafeFarProductWaveRough_nontrivial_cofactor_ge_key
      hkey hrough htgt'
    have hhalf := (paritySafeFarProductWaveCofactor_packet hkey hwave).2.2
    rw [hcofactor] at hfloor hhalf
    nlinarith

/-! ### PRIM-L049.8: arithmetic sanity witnesses -/

/-- Numeric checks for the next quotient and seat formulas used by L049. -/
theorem paritySafeFarProductWave_nextSeat_sanity_witnesses :
    paritySafeFarProductWaveNextQuotient 16 (3, (7, 13)) = 1 ∧
      paritySafeFarProductWaveNextSeat 16 (3, (7, 13)) = 17 ∧
      paritySafeFarProductWaveNextQuotient 62 (3, (5, 37)) = 7 ∧
      paritySafeFarProductWaveNextSeat 62 (3, (5, 37)) = 41 ∧
      paritySafeFarProductWaveNextQuotient 62 (3, (11, 17)) = 7 ∧
      paritySafeFarProductWaveNextSeat 62 (3, (11, 17)) = 83 ∧
      paritySafeFarProductWaveNextQuotient 17 (3, (5, 7)) = 3 ∧
      paritySafeFarProductWaveNextSeat 17 (3, (5, 7)) = 26 := by
  norm_num [paritySafeFarProductWaveNextQuotient,
    paritySafeFarProductWaveNextSeat, paritySafeTripleProductModulus]

end
end DkMath.NumberTheory.Legendre
