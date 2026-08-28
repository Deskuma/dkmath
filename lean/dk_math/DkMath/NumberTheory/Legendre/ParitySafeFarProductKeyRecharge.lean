/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeFarProductWaveSurvival

#print "file: DkMath.NumberTheory.Legendre.ParitySafeFarProductKeyRecharge"

/-!
## ParitySafeFarProductKeyRecharge

PRIM-L050 splits the surviving far product keys by the explicit next quotient:
terminal keys have quotient `1`, while recharge keys have quotient greater than
`1`.  Terminal survival is exactly the condition that the product modulus lies
in the square shell.  Recharge keys force their first prime into the same-anchor
finite sqrt-scale active-prime subworld.

This is a finite scale gate.  It does not create a smaller anchor, a descent,
an injective recharge charge, or an analytic estimate.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open DkMath.NumberTheory.Legendre.Internal
noncomputable section
local instance classicalDecidableRecharge (p : Prop) : Decidable p :=
  Classical.propDecidable p
open scoped BigOperators

/-! ### PRIM-L050.1: terminal/recharge surviving-key partition -/

/-- Surviving far keys whose next quotient is the terminal value `1`. -/
noncomputable def paritySafeTerminalSurvivingFarProductKeys
    (n : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  (paritySafeSurvivingFarProductKeys n).filter
    (fun key => paritySafeFarProductWaveNextQuotient n key = 1)

/-- Surviving far keys whose next quotient is genuinely rechargeable. -/
noncomputable def paritySafeRechargeSurvivingFarProductKeys
    (n : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  (paritySafeSurvivingFarProductKeys n).filter
    (fun key => 1 < paritySafeFarProductWaveNextQuotient n key)

@[simp] theorem mem_paritySafeTerminalSurvivingFarProductKeys
    {n : ℕ} {key : ℕ × (ℕ × ℕ)} :
    key ∈ paritySafeTerminalSurvivingFarProductKeys n ↔
      key ∈ paritySafeSurvivingFarProductKeys n ∧
        paritySafeFarProductWaveNextQuotient n key = 1 := by
  simp [paritySafeTerminalSurvivingFarProductKeys]

@[simp] theorem mem_paritySafeRechargeSurvivingFarProductKeys
    {n : ℕ} {key : ℕ × (ℕ × ℕ)} :
    key ∈ paritySafeRechargeSurvivingFarProductKeys n ↔
      key ∈ paritySafeSurvivingFarProductKeys n ∧
        1 < paritySafeFarProductWaveNextQuotient n key := by
  simp [paritySafeRechargeSurvivingFarProductKeys]

private theorem paritySafeFarProductWaveNextQuotient_pos
    (n : ℕ) (key : ℕ × (ℕ × ℕ)) :
    0 < paritySafeFarProductWaveNextQuotient n key := by
  unfold paritySafeFarProductWaveNextQuotient
  exact Nat.zero_lt_succ _

/-- Terminal and recharge surviving keys are disjoint. -/
theorem paritySafeTerminalRechargeSurvivingFarProductKeys_disjoint
    (n : ℕ) :
    Disjoint (paritySafeTerminalSurvivingFarProductKeys n)
      (paritySafeRechargeSurvivingFarProductKeys n) := by
  rw [Finset.disjoint_left]
  intro key hterminal hrecharge
  have hterminal' :=
    mem_paritySafeTerminalSurvivingFarProductKeys.mp hterminal
  have hrecharge' :=
    mem_paritySafeRechargeSurvivingFarProductKeys.mp hrecharge
  omega

/-- Terminal and recharge surviving keys partition all surviving far keys. -/
theorem paritySafeTerminalRechargeSurvivingFarProductKeys_union
    (n : ℕ) :
    paritySafeTerminalSurvivingFarProductKeys n ∪
        paritySafeRechargeSurvivingFarProductKeys n =
      paritySafeSurvivingFarProductKeys n := by
  ext key
  constructor
  · intro h
    rcases Finset.mem_union.mp h with hterminal | hrecharge
    · exact (mem_paritySafeTerminalSurvivingFarProductKeys.mp hterminal).1
    · exact (mem_paritySafeRechargeSurvivingFarProductKeys.mp hrecharge).1
  · intro hsurv
    have htpos := paritySafeFarProductWaveNextQuotient_pos n key
    by_cases hterminal : paritySafeFarProductWaveNextQuotient n key = 1
    · exact Finset.mem_union.mpr (Or.inl
        (mem_paritySafeTerminalSurvivingFarProductKeys.mpr
          ⟨hsurv, hterminal⟩))
    · have hrecharge : 1 < paritySafeFarProductWaveNextQuotient n key := by
        omega
      exact Finset.mem_union.mpr (Or.inr
        (mem_paritySafeRechargeSurvivingFarProductKeys.mpr
          ⟨hsurv, hrecharge⟩))

/-! ### PRIM-L050.2: exact residual-card split -/

/-- The far residual card splits exactly into terminal and recharge keys. -/
theorem paritySafeCanonicalFarResidual_card_eq_terminal_add_recharge
    (n : ℕ) :
    (paritySafeCanonicalFarResidualTripleIncidences n).card =
      (paritySafeTerminalSurvivingFarProductKeys n).card +
      (paritySafeRechargeSurvivingFarProductKeys n).card := by
  rw [paritySafeCanonicalFarResidual_card_eq_survivingFarProductKeys_card]
  rw [← paritySafeTerminalRechargeSurvivingFarProductKeys_union n]
  exact Finset.card_union_of_disjoint
    (paritySafeTerminalRechargeSurvivingFarProductKeys_disjoint n)

/-! ### PRIM-L050.3: terminal quotient and shell characterization -/

private theorem paritySafeFarProductWave_modulus_pos
    {n p q s : ℕ}
    (hkey : (p, (q, s)) ∈ paritySafeTripleGateFarTriples n) :
    0 < p * q * s := by
  have hgate := mem_paritySafeTripleGateTriples.mp
    (Finset.mem_filter.mp hkey).1
  rcases hgate with ⟨hp, hq, hs, hpq, hqs⟩
  exact Nat.mul_pos
    (Nat.mul_pos
      (mem_squareAnchorOddActivePrimes.mp
        (mem_paritySafeTripleGatePrimes.mp hp).1).1.pos
      (mem_squareAnchorOddActivePrimes.mp hq).1.pos)
    (mem_squareAnchorOddActivePrimes.mp hs).1.pos

/-- The terminal quotient is `1` exactly when the product modulus exceeds the
square anchor. -/
theorem paritySafeFarProductWaveNextQuotient_eq_one_iff_anchor_sq_lt_modulus
    {n p q s : ℕ}
    (hkey : (p, (q, s)) ∈ paritySafeTripleGateFarTriples n) :
    paritySafeFarProductWaveNextQuotient n (p, (q, s)) = 1 ↔
      n ^ 2 < p * q * s := by
  have hmpos := paritySafeFarProductWave_modulus_pos hkey
  constructor
  · intro hterminal
    have hzero : n ^ 2 / (p * q * s) = 0 := by
      unfold paritySafeFarProductWaveNextQuotient at hterminal
      have hterminal' : n ^ 2 / (p * q * s) + 1 = 1 := by
        simpa [paritySafeTripleProductModulus] using hterminal
      omega
    exact (Nat.div_eq_zero_iff_lt hmpos).mp hzero
  · intro hlarge
    unfold paritySafeFarProductWaveNextQuotient
    have hzero : n ^ 2 / (p * q * s) = 0 :=
      (Nat.div_eq_zero_iff_lt hmpos).mpr hlarge
    simp [paritySafeTripleProductModulus, hzero]

/-- A terminal surviving key is exactly a far key whose product modulus lies in
the square shell. -/
theorem mem_paritySafeTerminalSurvivingFarProductKeys_iff_product_in_shell
    {n p q s : ℕ} :
    (p, (q, s)) ∈ paritySafeTerminalSurvivingFarProductKeys n ↔
      (p, (q, s)) ∈ paritySafeTripleGateFarTriples n ∧
        n ^ 2 < p * q * s ∧
        p * q * s ≤ n ^ 2 + 2 * n := by
  constructor
  · intro hterminal
    have hterminal' :=
      mem_paritySafeTerminalSurvivingFarProductKeys.mp hterminal
    have hsurv := mem_paritySafeSurvivingFarProductKeys.mp hterminal'.1
    have hquot :=
      paritySafeFarProductWaveNextQuotient_eq_one_iff_anchor_sq_lt_modulus
        hsurv.1
    refine ⟨hsurv.1, hquot.mp hterminal'.2, ?_⟩
    have hfit := hsurv.2.1
    unfold ParitySafeFarProductKeyFitsShell at hfit
    simpa [hterminal'.2, paritySafeTripleProductModulus] using hfit
  · rintro ⟨hkey, hlarge, hupper⟩
    have hquot :=
      paritySafeFarProductWaveNextQuotient_eq_one_iff_anchor_sq_lt_modulus
        hkey
    have hterminal :
        paritySafeFarProductWaveNextQuotient n (p, (q, s)) = 1 := hquot.mpr hlarge
    apply mem_paritySafeTerminalSurvivingFarProductKeys.mpr
    refine ⟨?_, hterminal⟩
    apply mem_paritySafeSurvivingFarProductKeys.mpr
    refine ⟨hkey, ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · unfold ParitySafeFarProductKeyFitsShell
      simpa [paritySafeTripleProductModulus, hterminal] using hupper
    · simp [hterminal]
    · intro a ha hap hadiv
      have hprime := (mem_squareAnchorOddActivePrimes.mp ha).1
      exact hprime.ne_one (Nat.dvd_one.mp (by simpa [hterminal] using hadiv))

/-! ### PRIM-L050.4: same-anchor sqrt-scale active-prime world -/

/-- Active primes whose square is at most the same anchor `n`. -/
noncomputable def paritySafeSqrtScaleActivePrimes (n : ℕ) : Finset ℕ :=
  (squareAnchorOddActivePrimes n).filter (fun p => p ^ 2 ≤ n)

@[simp] theorem mem_paritySafeSqrtScaleActivePrimes
    {n p : ℕ} :
    p ∈ paritySafeSqrtScaleActivePrimes n ↔
      p ∈ squareAnchorOddActivePrimes n ∧ p ^ 2 ≤ n := by
  simp [paritySafeSqrtScaleActivePrimes]

/-! ### PRIM-L050.5: recharge first-prime sqrt gate -/

/-- The first prime of a recharge key lies at sqrt scale of the same anchor. -/
theorem paritySafeRechargeSurvivingFarProductKey_firstPrime_sq_le_anchor
    {n p q s : ℕ}
    (hkey : (p, (q, s)) ∈ paritySafeRechargeSurvivingFarProductKeys n) :
    p ^ 2 ≤ n := by
  have hrecharge := mem_paritySafeRechargeSurvivingFarProductKeys.mp hkey
  have hsurv := mem_paritySafeSurvivingFarProductKeys.mp hrecharge.1
  have hgate := hsurv.1
  have htgt := hrecharge.2
  have hwave := (mem_squareWaveOffsets_farKey_iff_eq_nextSeat hgate).mpr
    ⟨hsurv.2.1, rfl⟩
  have hrough : paritySafeFarProductWaveNextSeat n (p, (q, s)) ∈
      paritySafeFarProductWaveRoughOffsets n (p, (q, s)) := by
    exact (mem_paritySafeFarProductWaveRoughOffsets_iff_survives_and_eq_nextSeat
      hgate).mpr ⟨hsurv.2, rfl⟩
  have hcofactor := paritySafeFarProductWaveCofactor_nextSeat_eq_nextQuotient
    hgate hsurv.2.1
  have htgt' : 1 < paritySafeFarProductWaveCofactor n (p, (q, s))
      (paritySafeFarProductWaveNextSeat n (p, (q, s))) := by
    rw [hcofactor]
    exact htgt
  have hfloor := paritySafeFarProductWaveRough_nontrivial_cofactor_ge_key
    hgate hrough htgt'
  rw [hcofactor] at hfloor
  have hgate' := mem_paritySafeTripleGateTriples.mp
    (Finset.mem_filter.mp hgate).1
  rcases hgate' with ⟨hp, hq, hs, hpq, hqs⟩
  have hpactive := (mem_paritySafeTripleGatePrimes.mp hp).1
  have hpprime := (mem_squareAnchorOddActivePrimes.mp hpactive).1
  have hqprime := (mem_squareAnchorOddActivePrimes.mp hq).1
  have hsprime := (mem_squareAnchorOddActivePrimes.mp hs).1
  have hppos := hpprime.pos
  have hqpos := hqprime.pos
  have hps : p < s := lt_trans hpq hqs
  have hp3lt : p ^ 3 < p * q * s := by
    have hppq : p * p < p * q :=
      Nat.mul_lt_mul_left hppos |>.mpr hpq
    have hppqp : p * p * p < p * q * p :=
      Nat.mul_lt_mul_right hppos |>.mpr hppq
    have hpqps : p * q * p < p * q * s :=
      (Nat.mul_lt_mul_left (Nat.mul_pos hppos hqpos)).2 hps
    calc
      p ^ 3 = p * p * p := by ring
      _ < p * q * p := hppqp
      _ < p * q * s := hpqps
  have hpow4lt : p ^ 4 <
      (p * q * s) * paritySafeFarProductWaveNextQuotient n (p, (q, s)) := by
    calc
      p ^ 4 = (p ^ 3) * p := by ring
      _ < (p * q * s) * p :=
        (Nat.mul_lt_mul_right hppos).2 hp3lt
      _ ≤ (p * q * s) *
          paritySafeFarProductWaveNextQuotient n (p, (q, s)) :=
        Nat.mul_le_mul_left _ hfloor
  have hupper :
      (p * q * s) * paritySafeFarProductWaveNextQuotient n (p, (q, s)) ≤
        n ^ 2 + 2 * n := by
    have hfit := hsurv.2.1
    unfold ParitySafeFarProductKeyFitsShell at hfit
    simpa [paritySafeTripleProductModulus] using hfit
  have hpow4lt_succ : p ^ 4 < (n + 1) ^ 2 := by
    nlinarith
  by_contra hpn
  have hnp : n < p ^ 2 := Nat.lt_of_not_ge hpn
  have hnplus : n + 1 ≤ p ^ 2 := by omega
  have hsq := Nat.mul_self_le_mul_self hnplus
  nlinarith

/-- The first prime of a recharge key belongs to the same-anchor sqrt-scale
active-prime Finset. -/
theorem paritySafeRechargeSurvivingFarProductKey_firstPrime_mem_sqrtScale
    {n p q s : ℕ}
    (hkey : (p, (q, s)) ∈ paritySafeRechargeSurvivingFarProductKeys n) :
    p ∈ paritySafeSqrtScaleActivePrimes n := by
  have hrecharge := mem_paritySafeRechargeSurvivingFarProductKeys.mp hkey
  have hsurv := mem_paritySafeSurvivingFarProductKeys.mp hrecharge.1
  have hgate := mem_paritySafeTripleGateTriples.mp
    (Finset.mem_filter.mp hsurv.1).1
  have hpactive := (mem_paritySafeTripleGatePrimes.mp hgate.1).1
  exact mem_paritySafeSqrtScaleActivePrimes.mpr
    ⟨hpactive,
      paritySafeRechargeSurvivingFarProductKey_firstPrime_sq_le_anchor hkey⟩

/-! ### PRIM-L050.6: sqrt-scale first-prime fibers -/

/-- Recharge surviving keys with a fixed first prime. -/
noncomputable def paritySafeRechargeFarProductKeysAtPrime
    (n p : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  (paritySafeRechargeSurvivingFarProductKeys n).filter
    (fun key => key.1 = p)

@[simp] theorem mem_paritySafeRechargeFarProductKeysAtPrime
    {n p : ℕ} {key : ℕ × (ℕ × ℕ)} :
    key ∈ paritySafeRechargeFarProductKeysAtPrime n p ↔
      key ∈ paritySafeRechargeSurvivingFarProductKeys n ∧ key.1 = p := by
  simp [paritySafeRechargeFarProductKeysAtPrime]

/-- A recharge first-prime fiber outside sqrt scale is empty. -/
theorem paritySafeRechargeFarProductKeysAtPrime_eq_empty_of_not_mem_sqrtScale
    {n p : ℕ}
    (hp : p ∉ paritySafeSqrtScaleActivePrimes n) :
    paritySafeRechargeFarProductKeysAtPrime n p = ∅ := by
  ext key
  constructor
  · intro hkey
    have hfiber := mem_paritySafeRechargeFarProductKeysAtPrime.mp hkey
    have hsqrt := paritySafeRechargeSurvivingFarProductKey_firstPrime_mem_sqrtScale
      hfiber.1
    exact False.elim (hp (by simpa [hfiber.2] using hsqrt))
  · intro hkey
    simp at hkey

/-- Recharge keys partition exactly by their first prime over the sqrt-scale
active-prime Finset. -/
theorem paritySafeRechargeSurvivingFarProductKeys_card_eq_sqrtScale_fiber_sum
    (n : ℕ) :
    (paritySafeRechargeSurvivingFarProductKeys n).card =
      ∑ p ∈ paritySafeSqrtScaleActivePrimes n,
        (paritySafeRechargeFarProductKeysAtPrime n p).card := by
  have hfilter :
      (paritySafeRechargeSurvivingFarProductKeys n).filter
          (fun key => key.1 ∈ paritySafeSqrtScaleActivePrimes n) =
        paritySafeRechargeSurvivingFarProductKeys n := by
    ext key
    constructor
    · intro hkey
      exact (Finset.mem_filter.mp hkey).1
    · intro hkey
      apply Finset.mem_filter.mpr
      refine ⟨hkey, ?_⟩
      exact paritySafeRechargeSurvivingFarProductKey_firstPrime_mem_sqrtScale hkey
  rw [← hfilter]
  simpa [paritySafeRechargeFarProductKeysAtPrime] using
    (Finset.sum_card_fiberwise_eq_card_filter
      (paritySafeRechargeSurvivingFarProductKeys n)
      (paritySafeSqrtScaleActivePrimes n)
      (fun key => key.1)).symm

/-! ### PRIM-L050.7: arithmetic sanity witnesses -/

/-- Numeric next-quotient checks for one terminal and two recharge examples. -/
theorem paritySafeFarProductKeyRecharge_sanity_witnesses :
    paritySafeFarProductWaveNextQuotient 16 (3, (7, 13)) = 1 ∧
      paritySafeFarProductWaveNextQuotient 62 (3, (5, 37)) = 7 ∧
      paritySafeFarProductWaveNextQuotient 17 (3, (5, 7)) = 3 ∧
      3 ^ 2 ≤ 62 ∧ 3 ^ 2 ≤ 17 := by
  norm_num [paritySafeFarProductWaveNextQuotient,
    paritySafeTripleProductModulus]

end
end DkMath.NumberTheory.Legendre
