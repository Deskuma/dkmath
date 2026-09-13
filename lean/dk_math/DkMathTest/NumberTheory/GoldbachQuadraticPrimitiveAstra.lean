/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/
import DkMath.NumberTheory.Goldbach
import DkMath.Lib.Cosmic.GTailBoundary

/-!
# Quadratic primitive Goldbach fiber — research scratch

This file is an audit of normalization, not a universal escape provider.
Production owners retain the finite obstruction and capacity theorems.
All declarations below are scratch observations; the production facade does
not import this target. Reports QP-000 through QP-005 record their interpretation.
-/
namespace DkMathTest.GoldbachQuadraticPrimitiveAstra

open DkMath.NumberTheory DkMath.CosmicFormula
open scoped BigOperators

/-- QP-001: this is precisely Mathlib's bounded subtraction equivalence. -/
theorem coordinate_coprime {n u : ℕ} (hu : u ≤ n) :
    Nat.Coprime n u ↔ Nat.Coprime (n - u) u :=
  (Nat.coprime_sub_self_left hu).symm

/-- Right-coordinate transport does not need a subtraction bound. -/
theorem right_coordinate_coprime (n u : ℕ) :
    Nat.Coprime (n + u) u ↔ Nat.Coprime n u := Nat.coprime_add_self_left

/-- Canonical quadratic tail, with the natural subtraction bound explicit. -/
theorem quadratic_tail {n u : ℕ} (hu : u ≤ n) :
    GTail 2 1 (n - u) u = n + u := by
  rw [GTail_rec 2 1 (n - u) u (by omega)]
  simp only [Nat.choose_one_right, Nat.reduceSub, pow_one, GTail_self_eq_one, mul_one]
  omega

/-- The exact reflected gcd follows from the canonical boundary theorem. -/
theorem quadratic_boundary {n u : ℕ} (hu : u ≤ n) (hc : Nat.Coprime n u) :
    Nat.gcd (n - u) (n + u) = Nat.gcd (n - u) 2 := by
  rw [← quadratic_tail hu]
  exact gcd_GN_eq_gcd_of_one_le (by omega) ((coordinate_coprime hu).mp hc)

/-- Opposite coordinate parity is exactly oddness of either endpoint. -/
theorem parity_iff_odd_left {n u : ℕ} (hu : u ≤ n) :
    n % 2 ≠ u % 2 ↔ Odd (n - u) := by
  rw [Nat.odd_iff]
  omega

/-- Under primitivity, opposite parity is necessary and sufficient. -/
theorem endpoints_coprime_iff {n u : ℕ} (hu : u ≤ n) (hc : Nat.Coprime n u) :
    Nat.Coprime (n - u) (n + u) ↔ n % 2 ≠ u % 2 := by
  change Nat.gcd (n - u) (n + u) = 1 ↔ _
  rw [quadratic_boundary hu hc]
  change Nat.Coprime (n - u) 2 ↔ _
  rw [Nat.coprime_two_right, ← parity_iff_odd_left hu]

/-- Distinct reflected primes force primitive coordinates; positivity suffices
because primality itself supplies the natural subtraction bound. -/
theorem positive_pair_primitive {n u : ℕ} (hu : 0 < u)
    (hl : Nat.Prime (n - u)) (hr : Nat.Prime (n + u)) : Nat.Coprime n u := by
  have hb := hl.two_le
  have he : n - u ≠ n + u := by omega
  have hc := (Nat.coprime_primes hl hr).mpr he
  have hd₁ : Nat.gcd n u ∣ n - u := Nat.dvd_sub (Nat.gcd_dvd_left n u) (Nat.gcd_dvd_right n u)
  have hd₂ : Nat.gcd n u ∣ n + u := dvd_add (Nat.gcd_dvd_left n u) (Nat.gcd_dvd_right n u)
  have hd := Nat.dvd_gcd hd₁ hd₂
  rw [hc.gcd_eq_one] at hd
  exact Nat.dvd_one.mp hd

/-- Positive prime pairs are automatically odd on both ends. -/
theorem positive_pair_parity {n u : ℕ} (hu : 0 < u)
    (hl : Nat.Prime (n - u)) (hr : Nat.Prime (n + u)) : n % 2 ≠ u % 2 := by
  have hb := hl.two_le
  have hc := (Nat.coprime_primes hl hr).mpr (show n - u ≠ n + u by omega)
  exact (endpoints_coprime_iff (by omega) (positive_pair_primitive hu hl hr)).mp hc

/-- Diagonal survival is precisely center primality and is not primitive at n≥2. -/
theorem diagonal_pair (n : ℕ) :
    (Nat.Prime (n - 0) ∧ Nat.Prime (n + 0)) ↔ Nat.Prime n := by simp

/-- Keep the diagonal as a separate branch when normalizing the search. -/
theorem pair_of_center_prime {n : ℕ} (hn : Nat.Prime n) : GoldbachPairAt n :=
  ⟨n, n, hn, hn, by omega⟩

/-- Scratch candidate set, retaining the production admissible interval. -/
def primitiveOffsets (n : ℕ) : Finset ℕ :=
  (goldbachOffsets n).filter (Nat.Coprime n)

/-- Scratch positive primitive candidate set. -/
def primitivePositiveOffsets (n : ℕ) : Finset ℕ :=
  (primitiveOffsets n).filter (fun u => 0 < u)

/-- Scratch positive primitive fiber with opposite coordinate parity. -/
def primitiveParityOffsets (n : ℕ) : Finset ℕ :=
  (primitivePositiveOffsets n).filter (fun u => n % 2 ≠ u % 2)

@[simp] theorem mem_primitiveOffsets {n u : ℕ} :
    u ∈ primitiveOffsets n ↔ u ∈ goldbachOffsets n ∧ Nat.Coprime n u := by
  simp [primitiveOffsets]

@[simp] theorem mem_primitivePositiveOffsets {n u : ℕ} :
    u ∈ primitivePositiveOffsets n ↔
      u ∈ goldbachOffsets n ∧ Nat.Coprime n u ∧ 0 < u := by
  simp [primitivePositiveOffsets, and_assoc]

@[simp] theorem mem_primitiveParityOffsets {n u : ℕ} :
    u ∈ primitiveParityOffsets n ↔
      u ∈ goldbachOffsets n ∧ Nat.Coprime n u ∧ 0 < u ∧ n % 2 ≠ u % 2 := by
  simp [primitiveParityOffsets, and_assoc]

/-- Without parity, primitive coordinates can have gcd two. Smallest positive
admissible example (lexicographic n,u) is (3,1). -/
example : Nat.Coprime 3 1 ∧ Nat.gcd (3 - 1) (3 + 1) = 2 := by decide

/-- The subtraction bound cannot be dropped: (1,2) is primitive/opposite parity. -/
example : Nat.Coprime 1 2 ∧ 1 % 2 ≠ 2 % 2 ∧
    Nat.gcd (1 - 2) (1 + 2) ≠ Nat.gcd (1 - 2) 2 := by decide

/-- Small centers and the lost diagonal. -/
example : primitiveParityOffsets 0 = ∅ ∧ primitiveParityOffsets 1 = ∅ ∧
    primitiveParityOffsets 2 = ∅ ∧ GoldbachPairAt 2 ∧ ¬ Nat.Coprime 2 0 := by
  refine ⟨by decide, by decide, by decide, pair_of_center_prime (by decide), by decide⟩

/-- Bounded zero-offset primitive endpoint edge. -/
example : Nat.Coprime 1 0 ∧ Nat.gcd (1 - 0) (1 + 0) = 1 ∧
    ¬ Nat.Coprime 0 0 := by decide

/-- QP-002: any nonunit divisor of the center is absent from both raw
supports on a bounded primitive fiber; primality is unnecessary. -/
theorem center_divisor_absent {n u r : ℕ} (hu : u ≤ n)
    (hc : Nat.Coprime n u) (hr : 1 < r) (hd : r ∣ n) :
    ¬ r ∣ n - u ∧ ¬ r ∣ n + u := by
  have hcu : Nat.Coprime r u := hc.of_dvd_left hd
  constructor
  · intro hl
    have hh := Nat.dvd_sub hd hl
    rw [Nat.sub_sub_self hu] at hh
    have := hcu.eq_one_of_dvd hh
    omega
  · intro hright
    have hh := Nat.dvd_sub hright hd
    have hdu : r ∣ u := by simpa using hh
    have := hcu.eq_one_of_dvd hdu
    omega

/-- Opposite parity alone removes two from both raw supports. -/
theorem two_absent {n u : ℕ} (hu : u ≤ n) (hp : n % 2 ≠ u % 2) :
    ¬ 2 ∣ n - u ∧ ¬ 2 ∣ n + u := by
  simp only [Nat.dvd_iff_mod_eq_zero]
  omega

/-- Scratch left proper support uses precisely the production cutoff. -/
def leftSupport (n u : ℕ) : Finset ℕ :=
  (goldbachSmallPrimes n).filter (fun r => r ∣ n - u ∧ n - u ≠ r)

/-- Scratch right proper support uses precisely the production cutoff. -/
def rightSupport (n u : ℕ) : Finset ℕ :=
  (goldbachSmallPrimes n).filter (fun r => r ∣ n + u ∧ n + u ≠ r)

/-- The split support always recombines to the existing union support. -/
theorem support_union (n u : ℕ) :
    leftSupport n u ∪ rightSupport n u = goldbachObstructionSupport n u := by
  ext r
  simp [leftSupport, rightSupport, goldbachObstructionSupport,
    GoldbachProperObstructed, or_and_left]
  tauto

/-- Endpoint coprimality alone suffices, without coordinate or order assumptions. -/
theorem support_disjoint_of_coprime {n u : ℕ}
    (hc : Nat.Coprime (n - u) (n + u)) :
    Disjoint (leftSupport n u) (rightSupport n u) := by
  apply Finset.disjoint_left.mpr
  intro r hl hr
  have hl' := Finset.mem_filter.mp hl
  have hr' := Finset.mem_filter.mp hr
  have hprime := (mem_goldbachSmallPrimes.mp hl'.1).1
  have hd := Nat.dvd_gcd hl'.2.1 hr'.2.1
  rw [hc.gcd_eq_one] at hd
  exact hprime.ne_one (Nat.dvd_one.mp hd)

/-- On a primitive bounded fiber, only prime two can be shared. -/
theorem shared_support_eq_two {n u r : ℕ} (hu : u ≤ n) (hc : Nat.Coprime n u)
    (hl : r ∈ leftSupport n u) (hr : r ∈ rightSupport n u) : r = 2 := by
  have hl' := Finset.mem_filter.mp hl
  have hr' := Finset.mem_filter.mp hr
  have hp := (mem_goldbachSmallPrimes.mp hl'.1).1
  have hd := Nat.dvd_gcd hl'.2.1 hr'.2.1
  rw [quadratic_boundary hu hc] at hd
  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
    (dvd_trans hd (Nat.gcd_dvd_right _ _))

/-- Exact weakest condition within the bounded primitive regime: two must
not be a proper obstruction on both sides. Oddness is sufficient, not necessary. -/
theorem support_disjoint_iff_not_shared_two {n u : ℕ}
    (hu : u ≤ n) (hc : Nat.Coprime n u) :
    Disjoint (leftSupport n u) (rightSupport n u) ↔
      ¬ (2 ∈ leftSupport n u ∧ 2 ∈ rightSupport n u) := by
  rw [Finset.disjoint_left]
  constructor
  · intro h hh
    exact h hh.1 hh.2
  · intro h r hl hr
    have he := shared_support_eq_two hu hc hl hr
    subst r
    exact h ⟨hl, hr⟩

/-- Scratch parity fiber has disjoint proper supports. -/
theorem primitive_support_disjoint {n u : ℕ} (hu : u ∈ primitiveParityOffsets n) :
    Disjoint (leftSupport n u) (rightSupport n u) := by
  obtain ⟨hb, hc, _, hp⟩ := mem_primitiveParityOffsets.mp hu
  exact support_disjoint_of_coprime
    ((endpoints_coprime_iff (goldbachOffset_bounds hb).1 hc).mpr hp)

/-- Reduced prime world only removes directions already impossible on this fiber. -/
def reducedWorld (n : ℕ) : Finset ℕ :=
  (goldbachSmallPrimes n).filter (fun r => r ≠ 2 ∧ ¬ r ∣ n)

/-- Exact equality of proper-obstruction predicates on each retained candidate. -/
theorem survives_reduced_iff {n u : ℕ} (hu : u ∈ primitiveParityOffsets n) :
    GoldbachSurvives n (reducedWorld n) u ↔
      GoldbachSurvives n (goldbachSmallPrimes n) u := by
  obtain ⟨hb, hc, _, hp⟩ := mem_primitiveParityOffsets.mp hu
  have hbound := (goldbachOffset_bounds hb).1
  constructor
  · intro hs r hr ho
    have hnraw : r ∣ n - u ∨ r ∣ n + u := ho.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
    have hne : r ≠ 2 := by
      intro he
      subst r
      exact hnraw.elim (two_absent hbound hp).1 (two_absent hbound hp).2
    have hnd : ¬ r ∣ n := by
      intro hd
      have hh := center_divisor_absent hbound hc
        (mem_goldbachSmallPrimes.mp hr).1.one_lt hd
      exact hnraw.elim hh.1 hh.2
    exact hs r (Finset.mem_filter.mpr ⟨hr, hne, hnd⟩) ho
  · intro hs r hr
    exact hs r (Finset.mem_filter.mp hr).1

/-- Primitivity without parity does not separate proper supports. -/
example : Nat.Coprime 5 1 ∧ 2 ∈ leftSupport 5 1 ∧ 2 ∈ rightSupport 5 1 := by decide +kernel

/-- Endpoint equality can separate proper supports even with reflected gcd two. -/
example : Nat.gcd (3 - 1) (3 + 1) = 2 ∧
    Disjoint (leftSupport 3 1) (rightSupport 3 1) := by decide +kernel

/-- Dropping primitivity permits a shared odd proper factor even with odd endpoints. -/
example : 12 % 2 ≠ 3 % 2 ∧ 3 ∈ leftSupport 12 3 ∧ 3 ∈ rightSupport 12 3 := by decide +kernel

/-- QP-003: the degree-two Vandermonde identity includes empty supports. -/
theorem choose_two_add (L R : ℕ) :
    Nat.choose (L + R) 2 = Nat.choose L 2 + L * R + Nat.choose R 2 := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Nat.succ_add, Nat.choose_succ_succ, Nat.choose_succ_succ]
    simp only [Nat.choose_one_right]
    rw [ih]
    ring

/-- LL is the unordered pair count within the left support. -/
def localLL (n u : ℕ) : ℕ := Nat.choose (leftSupport n u).card 2
/-- LR counts the Cartesian product of the two disjoint supports. -/
def localLR (n u : ℕ) : ℕ := (leftSupport n u).card * (rightSupport n u).card
/-- RR is the unordered pair count within the right support. -/
def localRR (n u : ℕ) : ℕ := Nat.choose (rightSupport n u).card 2

/-- Split the existing local pair multiplicity, conditional only on disjointness. -/
theorem local_pair_split {n u : ℕ}
    (hd : Disjoint (leftSupport n u) (rightSupport n u)) :
    goldbachOffsetPrimePairMultiplicity n u = localLL n u + localLR n u + localRR n u := by
  unfold goldbachOffsetPrimePairMultiplicity localLL localLR localRR
  rw [← support_union, Finset.card_union_of_disjoint hd]
  exact choose_two_add _ _

/-- Restricted ledger: same local terms, summed over the normalized fiber. -/
theorem primitive_pair_split (n : ℕ) :
    (∑ u ∈ primitiveParityOffsets n, goldbachOffsetPrimePairMultiplicity n u) =
      (∑ u ∈ primitiveParityOffsets n, localLL n u) +
      (∑ u ∈ primitiveParityOffsets n, localLR n u) +
      (∑ u ∈ primitiveParityOffsets n, localRR n u) := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  exact local_pair_split (primitive_support_disjoint hu)

/-- Exact reconciliation with the original full pair ledger. Removed offsets
retain their unsplit contribution; no global disjointness is assumed. -/
theorem full_pair_split (n : ℕ) :
    goldbachPrimePairOverlapCount n =
      ((∑ u ∈ primitiveParityOffsets n, localLL n u) +
       (∑ u ∈ primitiveParityOffsets n, localLR n u) +
       (∑ u ∈ primitiveParityOffsets n, localRR n u)) +
      ∑ u ∈ (goldbachOffsets n).filter (fun u => u ∉ primitiveParityOffsets n),
        goldbachOffsetPrimePairMultiplicity n u := by
  rw [← primitive_pair_split, goldbachPrimePairOverlapCount_eq_sum_local_pairMultiplicity]
  have hs : (goldbachOffsets n).filter (fun u => u ∈ primitiveParityOffsets n) =
      primitiveParityOffsets n := by
    ext u
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun h => ⟨(mem_primitiveParityOffsets.mp h).1, h⟩⟩
  have hsum := Finset.sum_filter_add_sum_filter_not (goldbachOffsets n)
    (fun u => u ∈ primitiveParityOffsets n) (goldbachOffsetPrimePairMultiplicity n)
  rw [hs] at hsum
  exact hsum.symm

/-- Higher overlap survives primitive/parity normalization: 27 and 35 have
three distinct proper obstructions, with one on the left and two on the right. -/
theorem higher_overlap_regression :
    4 ∈ primitiveParityOffsets 31 ∧ leftSupport 31 4 = {3} ∧
    rightSupport 31 4 = {5, 7} ∧ localLL 31 4 = 0 ∧ localLR 31 4 = 2 ∧
    localRR 31 4 = 1 ∧ goldbachLocalPairOverlapResidual 31 4 = 1 := by
  decide +kernel

/-- QP-004: oriented raw residue observer, globally periodic even where
natural subtraction would truncate. Within u≤n it is the raw LR pattern. -/
def orientedResidue (n p q u : ℕ) : Prop :=
  (u : ZMod p) = (n : ZMod p) ∧ (u : ZMod q) = -(n : ZMod q)

instance (n p q u : ℕ) : Decidable (orientedResidue n p q u) := by
  unfold orientedResidue
  infer_instance

/-- This is exactly the pair of production raw congruence theorems. -/
theorem oriented_iff_raw {n p q u : ℕ} (hu : u ≤ n) :
    orientedResidue n p q u ↔ p ∣ n - u ∧ q ∣ n + u := by
  exact and_congr (goldbach_left_obstructed_iff hu).symm
    (goldbach_right_obstructed_iff n q u).symm

/-- Coprime moduli, not prime moduli, suffice for oriented uniqueness. -/
theorem oriented_modEq {n p q u v : ℕ} (hc : Nat.Coprime p q)
    (hu : orientedResidue n p q u) (hv : orientedResidue n p q v) :
    Nat.ModEq (p * q) u v := by
  apply (Nat.modEq_and_modEq_iff_modEq_mul hc).mp
  exact ⟨(ZMod.natCast_eq_natCast_iff u v p).mp (hu.1.trans hv.1.symm),
    (ZMod.natCast_eq_natCast_iff u v q).mp (hu.2.trans hv.2.symm)⟩

/-- Explicit CRT residue: CRT(n, val(-n)); unique in one product period. -/
theorem oriented_crt (n p q : ℕ) (hp : p ≠ 0) (hq : q ≠ 0)
    (hc : Nat.Coprime p q) :
    ∃! u : ℕ, u < p * q ∧ orientedResidue n p q u := by
  letI : NeZero q := ⟨hq⟩
  let a := Nat.chineseRemainder hc n (-(n : ZMod q)).val
  have ha : orientedResidue n p q a.val := by
    constructor
    · exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr a.property.1
    · have hh := (ZMod.natCast_eq_natCast_iff _ _ _).mpr a.property.2
      simpa only [ZMod.natCast_zmod_val] using hh
  refine ⟨a.val, ⟨Nat.chineseRemainder_lt_mul hc _ _ hp hq, ha⟩, ?_⟩
  intro v hv
  exact (oriented_modEq hc hv.2 ha).eq_of_lt_of_lt hv.1
    (Nat.chineseRemainder_lt_mul hc _ _ hp hq)

/-- The reverse orientation is reflection of both residue signs. If even one
modulus does not divide 2*n, no seat can have both orientations. -/
theorem orientations_exclusive {n p q u : ℕ} (hp : ¬ p ∣ 2 * n)
    (hu : orientedResidue n p q u) : ¬ orientedResidue n q p u := by
  intro hv
  apply hp
  apply (goldbach_residue_eq_neg_iff n p).mp
  exact hu.1.symm.trans hv.2

/-- Any two seats in one orientation are separated by at least the product. -/
theorem oriented_spacing {n p q u v : ℕ} (hc : Nat.Coprime p q)
    (hu : orientedResidue n p q u) (hv : orientedResidue n p q v) (hlt : u < v) :
    p * q ≤ v - u := by
  exact Nat.le_of_dvd (Nat.sub_pos_of_lt hlt)
    ((Nat.modEq_iff_dvd' (Nat.le_of_lt hlt)).mp (oriented_modEq hc hu hv))

/-- If the actual interval is shorter than the modulus, one orientation has
at most one seat. No primitive hypothesis is used. -/
theorem oriented_at_most_one {n p q u v : ℕ} (hc : Nat.Coprime p q)
    (hsize : n - 1 ≤ p * q) (hu : u ∈ goldbachOffsets n) (hv : v ∈ goldbachOffsets n)
    (hlu : orientedResidue n p q u) (hlv : orientedResidue n p q v) : u = v := by
  apply (oriented_modEq hc hlu hlv).eq_of_lt_of_lt
  · exact lt_of_lt_of_le (Finset.mem_range.mp hu) hsize
  · exact lt_of_lt_of_le (Finset.mem_range.mp hv) hsize

/-- Parity adds the ordinary CRT modulus two; this strengthens spacing to 2pq
for odd p,q, but follows from the existing parity coordinate. -/
theorem oriented_parity_spacing {n p q u v : ℕ} (hc : Nat.Coprime p q)
    (hodd : Nat.Coprime 2 (p * q)) (hu : orientedResidue n p q u)
    (hv : orientedResidue n p q v) (hpu : n % 2 ≠ u % 2)
    (hpv : n % 2 ≠ v % 2) (hlt : u < v) : 2 * (p * q) ≤ v - u := by
  have htwo : Nat.ModEq 2 u v := by
    change u % 2 = v % 2
    omega
  have hmod := (Nat.modEq_and_modEq_iff_modEq_mul hodd).mp
    ⟨htwo, oriented_modEq hc hu hv⟩
  exact Nat.le_of_dvd (Nat.sub_pos_of_lt hlt)
    ((Nat.modEq_iff_dvd' (Nat.le_of_lt hlt)).mp hmod)

/-- Primitivity and parity are not predicates on a residue modulo pq alone:
adding the odd product changes the parity coordinate. -/
example : orientedResidue 34 3 5 1 ∧ orientedResidue 34 3 5 16 ∧
    34 % 2 ≠ 1 % 2 ∧ ¬ (34 % 2 ≠ 16 % 2) := by decide +kernel

/-- Endpoint exceptions remain even when a raw LR seat has coprime odd ends. -/
example : 2 ∈ primitiveParityOffsets 5 ∧ 3 ∣ 5 - 2 ∧
    ¬ (3 ∣ 5 - 2 ∧ 5 - 2 ≠ 3) := by decide +kernel

/-- The parity spacing 2pq is sharp even for proper obstructions on the
primitive fiber. Therefore normalization cannot universally demand a larger gap. -/
theorem sharp_spacing_regression :
    8 ∈ primitiveParityOffsets 47 ∧ 38 ∈ primitiveParityOffsets 47 ∧
    3 ∈ leftSupport 47 8 ∧ 5 ∈ rightSupport 47 8 ∧
    3 ∈ leftSupport 47 38 ∧ 5 ∈ rightSupport 47 38 ∧ 38 - 8 = 2 * (3 * 5) := by
  decide +kernel

/-- Candidate cardinality is not geometric interval width: fewer than pq
normalized seats can still include two positions of the same orientation. -/
theorem cardinality_not_width_regression :
    (primitiveParityOffsets 50).card = 19 ∧ 19 < 7 * 3 ∧
    1 ∈ primitiveParityOffsets 50 ∧ 43 ∈ primitiveParityOffsets 50 ∧
    orientedResidue 50 7 3 1 ∧ orientedResidue 50 7 3 43 := by
  decide +kernel

/-- QP-005: normalized survivors use the reduced world, with proper exceptions. -/
def normalizedSurvivors (n : ℕ) : Finset ℕ :=
  (primitiveParityOffsets n).filter (GoldbachSurvives n (reducedWorld n))

/-- Covered candidates in exactly the same normalized finite fiber. -/
def normalizedCovered (n : ℕ) : Finset ℕ :=
  (primitiveParityOffsets n).filter (fun u => ¬ GoldbachSurvives n (reducedWorld n) u)

/-- The omitted diagonal is present precisely at prime centers. -/
def diagonalSeats (n : ℕ) : Finset ℕ := if Nat.Prime n then {0} else ∅

/-- Reduced-world normalized survival is exactly positive original survival. -/
theorem normalized_survivors_eq_positive (n : ℕ) :
    normalizedSurvivors n =
      (goldbachSurvivors n (goldbachSmallPrimes n)).filter (fun u => 0 < u) := by
  ext u
  constructor
  · intro h
    obtain ⟨hu, hs⟩ := Finset.mem_filter.mp h
    have hm := mem_primitiveParityOffsets.mp hu
    exact Finset.mem_filter.mpr ⟨mem_goldbachSurvivors.mpr
      ⟨hm.1, (survives_reduced_iff hu).mp hs⟩, hm.2.2.1⟩
  · intro h
    obtain ⟨hs, hpos⟩ := Finset.mem_filter.mp h
    obtain ⟨hb, hs⟩ := mem_goldbachSurvivors.mp hs
    obtain ⟨hl, hr⟩ := (goldbach_survives_iff_prime_pair hb).mp hs
    have hm := mem_primitiveParityOffsets.mpr
      ⟨hb, positive_pair_primitive hpos hl hr, hpos, positive_pair_parity hpos hl hr⟩
    exact Finset.mem_filter.mpr ⟨hm, (survives_reduced_iff hm).mpr hs⟩

/-- Exact original zero-seat criterion, including the empty small-center fibers. -/
theorem zero_survivor_iff (n : ℕ) :
    0 ∈ goldbachSurvivors n (goldbachSmallPrimes n) ↔ Nat.Prime n := by
  constructor
  · intro h
    obtain ⟨hb, hs⟩ := mem_goldbachSurvivors.mp h
    have hh := (goldbach_survives_iff_prime_pair hb).mp hs
    simpa using hh.1
  · intro hn
    have hb : 0 ∈ goldbachOffsets n := Finset.mem_range.mpr (by have := hn.two_le; omega)
    exact mem_goldbachSurvivors.mpr
      ⟨hb, (goldbach_survives_iff_prime_pair hb).mpr (by simpa using And.intro hn hn)⟩

/-- Set-level accounting: every original solution is either the prime diagonal
or a normalized survivor; no new solution is created by removing directions. -/
theorem survivors_exact_split (n : ℕ) :
    goldbachSurvivors n (goldbachSmallPrimes n) =
      normalizedSurvivors n ∪ diagonalSeats n := by
  rw [normalized_survivors_eq_positive]
  ext u
  have hdiag : u ∈ diagonalSeats n ↔ u = 0 ∧ Nat.Prime n := by
    by_cases hp : Nat.Prime n <;> simp [diagonalSeats, hp]
  simp only [Finset.mem_union, Finset.mem_filter, hdiag]
  by_cases hz : u = 0
  · subst u
    rw [zero_survivor_iff]
    simp only [Nat.lt_irrefl, and_false, false_or, true_and]
  · simp only [Nat.pos_of_ne_zero hz, and_true, hz, false_and, or_false]

/-- Exact solution-count loss is one at prime centers and zero otherwise. -/
theorem survivor_card_exact (n : ℕ) :
    (goldbachSurvivors n (goldbachSmallPrimes n)).card =
      (normalizedSurvivors n).card + if Nat.Prime n then 1 else 0 := by
  have hd : Disjoint (normalizedSurvivors n) (diagonalSeats n) := by
    apply Finset.disjoint_left.mpr
    intro u hu hv
    have hpos : 0 < u := (Finset.mem_filter.mp (normalized_survivors_eq_positive n ▸ hu)).2
    by_cases hn : Nat.Prime n
    · have hz : u = 0 := by simpa [diagonalSeats, hn] using hv
      omega
    · simp [diagonalSeats, hn] at hv
  rw [survivors_exact_split, Finset.card_union_of_disjoint hd]
  by_cases hp : Nat.Prime n <;> simp [diagonalSeats, hp]

/-- The normalized candidate partition has the same exact finite capacity law. -/
theorem normalized_conservation (n : ℕ) :
    (normalizedSurvivors n).card + (normalizedCovered n).card =
      (primitiveParityOffsets n).card := by
  exact Finset.card_filter_add_card_filter_not (GoldbachSurvives n (reducedWorld n))

/-- Quantitative comparison without truncated differences: removed-candidate
and removed-cover counts compensate, except for the prime-center diagonal. -/
theorem capacity_balance (n : ℕ) :
    (n - 1) + (normalizedCovered n).card =
      (primitiveParityOffsets n).card +
      (goldbachCoveredSeats n (goldbachSmallPrimes n)).card +
      if Nat.Prime n then 1 else 0 := by
  have ho := goldbach_survivors_add_covered n (goldbachSmallPrimes n)
  have hn := normalized_conservation n
  have hs := survivor_card_exact n
  omega

/-- Restoring the diagonal gives exactly the existing fixed-center capacity
criterion, not a stronger sufficient estimate. -/
theorem pair_iff_normalized_capacity (n : ℕ) :
    GoldbachPairAt n ↔ Nat.Prime n ∨
      (normalizedCovered n).card < (primitiveParityOffsets n).card := by
  rw [goldbachPairAt_iff_survivors_nonempty, ← Finset.card_pos, survivor_card_exact]
  have hn := normalized_conservation n
  by_cases hp : Nat.Prime n
  · rw [if_pos hp]
    exact ⟨fun _ => Or.inl hp, fun _ => by omega⟩
  · rw [if_neg hp, Nat.add_zero, or_iff_right hp]
    omega

/-- Exact universal equivalence classifies the normalized criterion as a
reformulation. This theorem supplies no proof of either side. -/
theorem strongGoldbach_iff_normalized_capacity :
    StrongGoldbach ↔ ∀ n : ℕ, 2 ≤ n → Nat.Prime n ∨
      (normalizedCovered n).card < (primitiveParityOffsets n).card := by
  unfold StrongGoldbach
  exact forall_congr' fun n => forall_congr' fun _ => pair_iff_normalized_capacity n

/-- Direct comparison to the production provider, with the diagonal restored. -/
theorem capacityEscape_iff_normalized_capacity :
    GoldbachCapacityEscape ↔ ∀ n : ℕ, 2 ≤ n → Nat.Prime n ∨
      (normalizedCovered n).card < (primitiveParityOffsets n).card :=
  strongGoldbach_iff_capacityEscape.symm.trans strongGoldbach_iff_normalized_capacity

/-- The naive strict incidence bound still fails after normalization: n=19
has eight candidates, seven covered seats, one survivor, and incidence eight. -/
theorem normalized_incidence_counterexample :
    (primitiveParityOffsets 19).card = 8 ∧ (normalizedCovered 19).card = 7 ∧
    (normalizedSurvivors 19).card = 1 ∧
    (∑ u ∈ primitiveParityOffsets 19, (goldbachObstructionSupport 19 u).card) = 8 := by
  decide +kernel

/-- The candidate-cardinality shortcut also fails for proper LR occupancy:
53 candidates < 65, yet both offsets carry the same proper 5-left/13-right wave. -/
theorem proper_cardinality_not_width_regression :
    (primitiveParityOffsets 162).card = 53 ∧ 53 < 5 * 13 ∧
    7 ∈ primitiveParityOffsets 162 ∧ 137 ∈ primitiveParityOffsets 162 ∧
    5 ∈ leftSupport 162 7 ∧ 13 ∈ rightSupport 162 7 ∧
    5 ∈ leftSupport 162 137 ∧ 13 ∈ rightSupport 162 137 := by
  decide +kernel

/-- Minimal unbounded-subtraction failure found in QP-002. -/
example : Nat.Coprime 0 1 ∧ 0 % 2 ≠ 1 % 2 ∧
    Nat.gcd (0 - 1) (0 + 1) ≠ Nat.gcd (0 - 1) 2 := by decide

/-- The smallest parity-only shared odd factor is a composite diagonal. -/
example : 9 % 2 ≠ 0 % 2 ∧ 3 ∈ leftSupport 9 0 ∧ 3 ∈ rightSupport 9 0 := by
  decide +kernel

end DkMathTest.GoldbachQuadraticPrimitiveAstra
