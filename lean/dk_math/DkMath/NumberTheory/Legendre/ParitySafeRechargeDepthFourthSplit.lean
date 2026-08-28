/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeRechargeExactDualBase
import DkMath.NumberTheory.Legendre.ParitySafeFarTripleRecharge

#print "file: DkMath.NumberTheory.Legendre.ParitySafeRechargeDepthFourthSplit"

/-!
## ParitySafeRechargeDepthFourthSplit

PRIM-L055 partitions the exact L054 recharge coordinates into selected-prime
depth and a complementary canonical fourth direction.  The depth predicate
records whether one of the selected shell primes divides the cofactor.  On
the complement, `Nat.minFac t` is the canonical fourth prime.

The module is coordinate-level and finite.  It does not make the fourth prime
an injective coordinate, introduce a generic four-hypergraph, or pass to a
smaller anchor or an analytic counting argument.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open DkMath.NumberTheory.Legendre.Internal
noncomputable section
local instance classicalDecidableDepthFourth (p : Prop) : Decidable p :=
  Classical.propDecidable p
open scoped BigOperators

/-! ### PRIM-L055.1: exact cofactor packet -/

/-- Every exact recharge cofactor is nonterminal and lies at half scale. -/
theorem paritySafeRechargeExactDualBasePair_cofactor_packet
    {n b t : ℕ}
    (hbt : (b, t) ∈ paritySafeRechargeExactDualBasePairs n) :
    1 < t ∧ 2 * t < n + 2 := by
  have hprime := (mem_paritySafeRechargeExactDualBasePairs.mp hbt).1
  have hover := (mem_paritySafeRechargePrimeAdmissibleDualBasePairs.mp hprime).1
  have hbase := mem_paritySafeRechargeOverAnchorDualBasePairs.mp hover
  have htbase := mem_paritySafeFarCofactorBaseOffsets.mp hbase.2.1
  have hbtprod := hbase.2.2
  have hble : b ≤ n :=
    (mem_paritySafeFarCofactorBaseOffsets.mp hbase.1).2.1
  have htpos : 0 < t := by omega
  have htgt : 1 < t := by
    by_contra hnot
    have htle : t ≤ 1 := by omega
    have hmul : b * t ≤ b := by
      simpa using Nat.mul_le_mul_left b htle
    omega
  rcases mem_paritySafeRechargePrimeAdmissibleDualBasePairs.mp hprime with
    ⟨_, hsactive, hslower, hsupper, hfar⟩
  let s := paritySafeRechargeOddShellQuotient n b t
  have hscaled : (2 * n) * t < n * (n + 2) := by
    calc
      (2 * n) * t < (b * s) * t :=
        Nat.mul_lt_mul_of_pos_right hfar htpos
      _ = (b * t) * s := by
        simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      _ ≤ n ^ 2 + 2 * n := by
        simpa [s] using hsupper
      _ = n * (n + 2) := by ring
  have hnpos : 0 < n := by
    have hsprime := (mem_squareAnchorOddActivePrimes.mp hsactive).1
    have hsge : 2 ≤ s := hsprime.two_le
    omega
  have hhalf : 2 * t < n + 2 := by
    nlinarith
  exact ⟨htgt, hhalf⟩

/-! ### PRIM-L055.2: selected depth and complementary fourth Finsets -/

/-- Whether a selected shell prime contributes a depth divisor of `t`. -/
def ParitySafeRechargeSelectedDepth
    (n b t p q : ℕ) : Prop :=
  let s := paritySafeRechargeOddShellQuotient n b t
  p ∣ t ∨ q ∣ t ∨ s ∣ t

/-- Exact recharge coordinates with at least one selected-prime depth divisor. -/
noncomputable def paritySafeRechargeExactDepthDualBasePairs
    (n : ℕ) : Finset (ℕ × ℕ) :=
  (paritySafeRechargeExactDualBasePairs n).filter
    (fun bt =>
      ∃ p q,
        ParitySafeRechargeExactPairWitness n bt.1 bt.2 p q ∧
        ParitySafeRechargeSelectedDepth n bt.1 bt.2 p q)

/-- Exact recharge coordinates on the complementary canonical-fourth branch. -/
noncomputable def paritySafeRechargeExactFourthDirectionPairs
    (n : ℕ) : Finset (ℕ × ℕ) :=
  (paritySafeRechargeExactDualBasePairs n).filter
    (fun bt =>
      ¬ ∃ p q,
        ParitySafeRechargeExactPairWitness n bt.1 bt.2 p q ∧
        ParitySafeRechargeSelectedDepth n bt.1 bt.2 p q)

@[simp] theorem mem_paritySafeRechargeExactDepthDualBasePairs
    {n b t : ℕ} :
    (b, t) ∈ paritySafeRechargeExactDepthDualBasePairs n ↔
      (b, t) ∈ paritySafeRechargeExactDualBasePairs n ∧
      ∃ p q,
        ParitySafeRechargeExactPairWitness n b t p q ∧
        ParitySafeRechargeSelectedDepth n b t p q := by
  simp [paritySafeRechargeExactDepthDualBasePairs]

@[simp] theorem mem_paritySafeRechargeExactFourthDirectionPairs
    {n b t : ℕ} :
    (b, t) ∈ paritySafeRechargeExactFourthDirectionPairs n ↔
      (b, t) ∈ paritySafeRechargeExactDualBasePairs n ∧
      ¬ ∃ p q,
        ParitySafeRechargeExactPairWitness n b t p q ∧
        ParitySafeRechargeSelectedDepth n b t p q := by
  simp [paritySafeRechargeExactFourthDirectionPairs]

/-! ### PRIM-L055.3: exact partition and card split -/

/-- The depth and fourth-direction exact Finsets are disjoint. -/
theorem paritySafeRechargeExactDepthFourth_disjoint
    (n : ℕ) :
    Disjoint
      (paritySafeRechargeExactDepthDualBasePairs n)
      (paritySafeRechargeExactFourthDirectionPairs n) := by
  rw [Finset.disjoint_left]
  intro bt hdepth hfourth
  exact (mem_paritySafeRechargeExactFourthDirectionPairs.mp hfourth).2
    (mem_paritySafeRechargeExactDepthDualBasePairs.mp hdepth).2

/-- Depth and fourth-direction branches partition the exact recharge universe. -/
theorem paritySafeRechargeExactDepthFourth_union
    (n : ℕ) :
    paritySafeRechargeExactDepthDualBasePairs n ∪
        paritySafeRechargeExactFourthDirectionPairs n =
      paritySafeRechargeExactDualBasePairs n := by
  ext bt
  constructor
  · intro h
    rcases Finset.mem_union.mp h with hdepth | hfourth
    · exact (mem_paritySafeRechargeExactDepthDualBasePairs.mp hdepth).1
    · exact (mem_paritySafeRechargeExactFourthDirectionPairs.mp hfourth).1
  · intro hexact
    by_cases hdepth : ∃ p q,
        ParitySafeRechargeExactPairWitness n bt.1 bt.2 p q ∧
        ParitySafeRechargeSelectedDepth n bt.1 bt.2 p q
    · exact Finset.mem_union.mpr (Or.inl
        (mem_paritySafeRechargeExactDepthDualBasePairs.mpr ⟨hexact, hdepth⟩))
    · exact Finset.mem_union.mpr (Or.inr
        (mem_paritySafeRechargeExactFourthDirectionPairs.mpr ⟨hexact, hdepth⟩))

/-- Exact recharge cardinality splits into selected depth and fourth direction. -/
theorem paritySafeRechargeExactDualBasePairs_card_eq_depth_add_fourth
    (n : ℕ) :
    (paritySafeRechargeExactDualBasePairs n).card =
      (paritySafeRechargeExactDepthDualBasePairs n).card +
      (paritySafeRechargeExactFourthDirectionPairs n).card := by
  calc
    (paritySafeRechargeExactDualBasePairs n).card =
        (paritySafeRechargeExactDepthDualBasePairs n ∪
          paritySafeRechargeExactFourthDirectionPairs n).card := by
      rw [paritySafeRechargeExactDepthFourth_union]
    _ = (paritySafeRechargeExactDepthDualBasePairs n).card +
        (paritySafeRechargeExactFourthDirectionPairs n).card :=
      Finset.card_union_of_disjoint
        (paritySafeRechargeExactDepthFourth_disjoint n)

/-- The L054 terminal split refines to terminal, depth, and fourth branches. -/
theorem paritySafeCanonicalFarResidual_card_eq_terminal_add_depth_add_fourth
    (n : ℕ) :
    (paritySafeCanonicalFarResidualTripleIncidences n).card =
      (paritySafeTerminalSurvivingFarProductKeys n).card +
      (paritySafeRechargeExactDepthDualBasePairs n).card +
      (paritySafeRechargeExactFourthDirectionPairs n).card := by
  rw [paritySafeCanonicalFarResidual_card_eq_terminal_add_exactDualBase]
  rw [paritySafeRechargeExactDualBasePairs_card_eq_depth_add_fourth]
  simp [Nat.add_assoc]

/-! ### PRIM-L055.4: selected-depth square packet -/

/-- The exact shell point represented by a dual-base coordinate. -/
def paritySafeRechargeExactShellPoint
    (n b t : ℕ) : ℕ :=
  (b * t) * paritySafeRechargeOddShellQuotient n b t

/-- A selected-prime depth divisor produces a square divisibility seat. -/
theorem paritySafeRechargeExactDepth_selected_square_dvd_shellPoint
    {n b t : ℕ}
    (hbt : (b, t) ∈ paritySafeRechargeExactDepthDualBasePairs n) :
    ∃ p q,
      ParitySafeRechargeExactPairWitness n b t p q ∧
      let s := paritySafeRechargeOddShellQuotient n b t
      p ^ 2 ∣ paritySafeRechargeExactShellPoint n b t ∨
      q ^ 2 ∣ paritySafeRechargeExactShellPoint n b t ∨
      s ^ 2 ∣ paritySafeRechargeExactShellPoint n b t := by
  rcases (mem_paritySafeRechargeExactDepthDualBasePairs.mp hbt).2 with
    ⟨p, q, hwitness, hdepth⟩
  refine ⟨p, q, hwitness, ?_⟩
  rcases hwitness with ⟨hp, hq, hpq, hprod, hqs, hrough⟩
  dsimp [ParitySafeRechargeSelectedDepth] at hdepth
  let s := paritySafeRechargeOddShellQuotient n b t
  change p ^ 2 ∣ (b * t) * s ∨
    q ^ 2 ∣ (b * t) * s ∨ s ^ 2 ∣ (b * t) * s
  have hpoint : (b * t) * s = (p * q * t) * s := by
    rw [hprod]
  rcases hdepth with hpdiv | hqdiv | hsdiv
  · left
    rcases hpdiv with ⟨k, hk⟩
    refine ⟨q * k * paritySafeRechargeOddShellQuotient n b t, ?_⟩
    calc
      (b * t) * s = (p * q * t) * s := hpoint
      _ = (p * q * (p * k)) * s := by
        exact congrArg (fun x => (p * q * x) * s) hk
      _ = p ^ 2 * (q * k * paritySafeRechargeOddShellQuotient n b t) := by
        dsimp [s]
        ring
  · right; left
    rcases hqdiv with ⟨k, hk⟩
    refine ⟨p * k * paritySafeRechargeOddShellQuotient n b t, ?_⟩
    calc
      (b * t) * s = (p * q * t) * s := hpoint
      _ = (p * q * (q * k)) * s := by
        exact congrArg (fun x => (p * q * x) * s) hk
      _ = q ^ 2 * (p * k * paritySafeRechargeOddShellQuotient n b t) := by
        dsimp [s]
        ring
  · right; right
    have hsdiv' : s ∣ t := by simpa [s] using hsdiv
    rcases hsdiv' with ⟨k, hk⟩
    refine ⟨p * q * k, ?_⟩
    calc
      (b * t) * s = (p * q * t) * s := hpoint
      _ = (p * q * (s * k)) * s := by
        exact congrArg (fun x => (p * q * x) * s) hk
      _ = s ^ 2 * (p * q * k) := by
        simp [pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

/-! ### PRIM-L055.5: canonical fourth prime -/

/-- The canonical fourth direction selected from a nontrivial cofactor. -/
def paritySafeRechargeExactFourthPrime (t : ℕ) : ℕ := Nat.minFac t

/-- The canonical fourth prime is active, half-scale, and distinct from `q,s`. -/
theorem paritySafeRechargeExactFourthPrime_packet
    {n b t p q : ℕ}
    (hbt : (b, t) ∈ paritySafeRechargeExactFourthDirectionPairs n)
    (hwitness : ParitySafeRechargeExactPairWitness n b t p q) :
    let s := paritySafeRechargeOddShellQuotient n b t
    let u := paritySafeRechargeExactFourthPrime t
    Nat.Prime u ∧
      u ∣ t ∧
      u ∈ paritySafeHalfScaleActivePrimes n ∧
      p < u ∧
      u ≠ q ∧
      u ≠ s ∧
      p * q * s * u ∣ paritySafeRechargeExactShellPoint n b t := by
  let s := paritySafeRechargeOddShellQuotient n b t
  let u := paritySafeRechargeExactFourthPrime t
  have hcofactor := paritySafeRechargeExactDualBasePair_cofactor_packet
    (mem_paritySafeRechargeExactFourthDirectionPairs.mp hbt).1
  have htpos : 0 < t := by omega
  have huprime : Nat.Prime u := by
    exact Nat.minFac_prime (by simpa [u] using hcofactor.1.ne')
  have hut : u ∣ t := by
    exact Nat.minFac_dvd t
  have hprime := (mem_paritySafeRechargeExactDualBasePairs.mp
    (mem_paritySafeRechargeExactFourthDirectionPairs.mp hbt).1).1
  have hover := (mem_paritySafeRechargePrimeAdmissibleDualBasePairs.mp hprime).1
  have hbase := mem_paritySafeRechargeOverAnchorDualBasePairs.mp hover
  have htpacket := mem_paritySafeFarCofactorBaseOffsets.mp hbase.2.1
  have hcop : Nat.Coprime (2 * n) t := htpacket.2.2
  have prime_dvd_t_active : ∀ {r : ℕ}, Nat.Prime r → r ∣ t →
      r ∈ squareAnchorOddActivePrimes n := by
    intro r hr hrt
    have hrtle : r ≤ t := Nat.le_of_dvd htpos hrt
    have hrle : r ≤ n := hrtle.trans htpacket.2.1
    have hcopr : Nat.Coprime r (2 * n) :=
      (Nat.Coprime.coprime_dvd_right hrt hcop).symm
    have hrn : ¬ r ∣ n := by
      intro hrd
      exact (Nat.Prime.coprime_iff_not_dvd hr).mp hcopr
        (dvd_mul_of_dvd_right hrd 2)
    have hr2 : r ≠ 2 := by
      intro hr2
      apply (Nat.Prime.coprime_iff_not_dvd hr).mp hcopr
      rw [hr2]
      exact dvd_mul_right 2 n
    exact mem_squareAnchorOddActivePrimes.mpr ⟨hr, hrle, hrn, hr2⟩
  have hutle : u ≤ t := Nat.le_of_dvd htpos hut
  have huhalf : 2 * u < n + 2 := by omega
  have hcopu : Nat.Coprime u (2 * n) :=
    (Nat.Coprime.coprime_dvd_right hut hcop).symm
  have hunle : u ≤ n := hutle.trans htpacket.2.1
  have hun : ¬ u ∣ n := by
    intro hud
    have : u ∣ 2 * n := dvd_mul_of_dvd_right hud 2
    exact (Nat.Prime.coprime_iff_not_dvd huprime).mp hcopu this
  have hu2 : u ≠ 2 := by
    intro hu
    apply (Nat.Prime.coprime_iff_not_dvd huprime).mp hcopu
    rw [hu]
    exact dvd_mul_right 2 n
  have huactive : u ∈ squareAnchorOddActivePrimes n :=
    mem_squareAnchorOddActivePrimes.mpr ⟨huprime, hunle, hun, hu2⟩
  have huhalfactive : u ∈ paritySafeHalfScaleActivePrimes n :=
    mem_paritySafeHalfScaleActivePrimes.mpr ⟨huactive, huhalf⟩
  have hfourth := (mem_paritySafeRechargeExactFourthDirectionPairs.mp hbt).2
  have hdepthnot : ¬ ParitySafeRechargeSelectedDepth n b t p q := by
    intro hdepth
    apply hfourth
    exact ⟨p, q, hwitness, hdepth⟩
  dsimp [ParitySafeRechargeSelectedDepth, s] at hdepthnot
  have hpnot : ¬ p ∣ t := fun hdiv => hdepthnot (Or.inl hdiv)
  have hqnot : ¬ q ∣ t := fun hdiv => hdepthnot (Or.inr (Or.inl hdiv))
  have hsnot : ¬ s ∣ t := fun hdiv => hdepthnot (Or.inr (Or.inr hdiv))
  have hpactive := (mem_paritySafeTripleGatePrimes.mp hwitness.1).1
  have hppos : 2 ≤ p :=
    (mem_squareAnchorOddActivePrimes.mp hpactive).1.two_le
  have hple : p ≤ u := by
    have hple' : t = 1 ∨ p ≤ Nat.minFac t := by
      apply (Nat.le_minFac (m := p) (n := t)).mpr
      intro r hr hrt
      by_contra hnot
      have hrlt : r < p := by omega
      exact (hwitness.2.2.2.2.2 r (prime_dvd_t_active hr hrt) hrlt) hrt
    have hple'' : p ≤ Nat.minFac t := hple'.resolve_left (by omega)
    simpa [u, paritySafeRechargeExactFourthPrime] using hple''
  have hpu : p ≠ u := by
    intro hpu
    apply hpnot
    rw [hpu]
    exact hut
  have hpu_lt : p < u := lt_of_le_of_ne hple hpu
  have huq : u ≠ q := by
    intro huq
    apply hqnot
    rw [← huq]
    exact hut
  have hus : u ≠ s := by
    intro hus
    apply hsnot
    rw [← hus]
    exact hut
  have hquad : p * q * s * u ∣ paritySafeRechargeExactShellPoint n b t := by
    unfold paritySafeRechargeExactShellPoint
    rcases hut with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have hpoint : (b * t) * s = (p * q * t) * s := by
      rw [hwitness.2.2.2.1]
    calc
      (b * t) * paritySafeRechargeOddShellQuotient n b t =
          (p * q * t) * s := by simpa [s] using hpoint
      _ = p * q * s * u * k := by
        rw [hk]
        simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  exact ⟨huprime, hut, huhalfactive, hpu_lt, huq, hus, hquad⟩

/-! ### PRIM-L055.6: coordinate-level consumer and false beams -/

/-- Every exact recharge coordinate is either depth or canonical fourth. -/
theorem paritySafeRechargeExactDualBase_depth_or_canonicalFourth
    {n b t : ℕ}
    (hbt : (b, t) ∈ paritySafeRechargeExactDualBasePairs n) :
    (b, t) ∈ paritySafeRechargeExactDepthDualBasePairs n ∨
      (b, t) ∈ paritySafeRechargeExactFourthDirectionPairs n := by
  rw [← Finset.mem_union]
  rw [paritySafeRechargeExactDepthFourth_union]
  exact hbt

/-- A concrete selected-prime depth square packet. -/
theorem paritySafeRechargeExactDepth_false_beam :
    17 ^ 2 + 26 = 3 * 5 * 7 * 3 ∧
      3 ∣ 3 ∧
      3 ^ 2 ∣ (15 * 3) * 7 := by
  norm_num

/-- The canonical fourth prime need not identify a recharge pair globally. -/
theorem paritySafeRechargeExactFourth_false_beam :
    Nat.minFac 7 = 7 ∧
      3 * 5 * 37 * 7 = 62 ^ 2 + 41 ∧
      3 * 11 * 17 * 7 = 62 ^ 2 + 83 := by
  norm_num

end
end DkMath.NumberTheory.Legendre
