/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Primitive.PrimeWorldResidues
import DkMath.NumberTheory.Legendre.PacketUnitResidue
import DkMath.NumberTheory.Legendre.PrimorialWheelBridge
import DkMath.NumberTheory.Legendre.CenteredFoldGcdAggregate

#print "file: DkMath.NumberTheory.Legendre.PrimeWorldPacketBridge"

/-! Exact finite-world, packet, and phased square-shell dictionaries. -/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open DkMath.NumberTheory.PrimorialUniverse

/-- The two representative conventions agree precisely away from modulus one. -/
theorem primeWorldResidues_eq_packetBase {S : Finset ℕ}
    (hM : 1 < primeWorldModulus S) :
    primeWorldResidues S = squareAnchorCoprimeBaseOffsets (primeWorldModulus S) := by
  ext r
  rw [mem_primeWorldResidues, mem_squareAnchorCoprimeBaseOffsets]
  constructor
  · rintro ⟨hr, hc⟩
    have hr0 : r ≠ 0 := by
      intro hz
      subst r
      simp only [Nat.coprime_zero_left] at hc
      omega
    exact ⟨by omega, by omega, hc.symm⟩
  · rintro ⟨hr0, hr, hc⟩
    have hne : r ≠ primeWorldModulus S := by
      intro he
      rw [he, Nat.coprime_self] at hc
      omega
    exact ⟨by omega, hc.symm⟩

/-- Cardinality is inherited from the existing packet API. -/
theorem card_primeWorldResidues_eq_totient {S : Finset ℕ}
    (hM : 1 < primeWorldModulus S) :
    (primeWorldResidues S).card = Nat.totient (primeWorldModulus S) := by
  rw [primeWorldResidues_eq_packetBase hM]
  exact card_squareAnchorCoprimeBaseOffsets (by omega)

/-- The dictionary exposes the existing fresh-prime recurrence in totient notation. -/
theorem primeWorld_totient_insert {S : Finset ℕ} (hS : KnownPrimeScales S)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S)
    (hM : 1 < primeWorldModulus S) :
    Nat.totient (primeWorldModulus (insert q S)) =
      Nat.totient (primeWorldModulus S) * (q - 1) := by
  have hnew : 1 < primeWorldModulus (insert q S) := by
    rw [primeWorldModulus_insert hqS]
    nlinarith [hq.two_le]
  rw [← card_primeWorldResidues_eq_totient hnew,
    card_primeWorldResidues_insert hS hq hqS, card_primeWorldResidues_eq_totient hM]

/-- Empty worlds demonstrate the modulus-one boundary in the kernel. -/
theorem primeWorld_packet_modulus_one_mismatch :
    primeWorldModulus ∅ = 1 ∧ primeWorldResidues ∅ = {0} ∧
      squareAnchorCoprimeBaseOffsets 1 = {1} ∧
      primeWorldResidues ∅ ≠ squareAnchorCoprimeBaseOffsets 1 := by
  decide +kernel

/-- The odd-gap world is the already certified radical support from checkpoint 018. -/
abbrev centeredOddGapPrimeWorld (n : ℕ) : Finset ℕ :=
  (primeScalesUpTo (2 * n - 1)).erase 2

theorem knownPrimeScales_centeredOddGapPrimeWorld (n : ℕ) :
    KnownPrimeScales (centeredOddGapPrimeWorld n) := by
  intro p hp
  exact (mem_primeScalesUpTo.mp (Finset.mem_of_mem_erase hp)).1

theorem centeredOddGapPrimeWorld_eq_primeFactors (n : ℕ) :
    centeredOddGapPrimeWorld n = (centeredOddGapProduct n).primeFactors :=
  (centeredOddGapProduct_primeFactors n).symm

theorem centeredOddGapPrimeWorld_modulus_eq_radical (n : ℕ) :
    primeWorldModulus (centeredOddGapPrimeWorld n) =
      (centeredOddGapProduct n).primeFactors.prod id := by
  rw [← centeredOddGapPrimeWorld_eq_primeFactors]
  rfl

/-- The square-shell address is the existing projection, including its anchor phase. -/
theorem supportDisjointFrom_iff_squareShell_address {S : Finset ℕ}
    (hS : KnownPrimeScales S) (n r : ℕ) :
    SupportDisjointFrom S (n ^ 2 + r) ↔
      squareShellWheelProjection S n r ∈ primeWorldResidues S := by
  have hpos : 0 < primeWorldModulus S := by
    exact Finset.prod_pos (fun p hp => (hS hp).pos)
  change SupportDisjointFrom S (n ^ 2 + r) ↔
    (n ^ 2 + r) % primeWorldModulus S ∈ primeWorldResidues S
  rw [mem_primeWorldResidues_iff_supportDisjointFrom hS]
  exact ⟨fun h => ⟨Nat.mod_lt _ hpos,
    supportDisjointFrom_mod_primeWorldModulus_iff.mpr h⟩, fun h =>
    supportDisjointFrom_mod_primeWorldModulus_iff.mp h.2⟩

/-- The first coarse street uses square-point coprimality, not offset coprimality. -/
def coarsePrimeWorldBase (S : Finset ℕ) (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (primeWorldModulus S)).filter
    (fun r => Nat.Coprime (n ^ 2 + r) (primeWorldModulus S))

@[simp] theorem mem_coarsePrimeWorldBase {S : Finset ℕ} {n r : ℕ} :
    r ∈ coarsePrimeWorldBase S n ↔
      1 ≤ r ∧ r ≤ primeWorldModulus S ∧
        Nat.Coprime (n ^ 2 + r) (primeWorldModulus S) := by
  simp [coarsePrimeWorldBase, and_assoc]

theorem mem_coarsePrimeWorldBase_iff_survivor {S : Finset ℕ}
    (hS : KnownPrimeScales S) {n r : ℕ} :
    r ∈ coarsePrimeWorldBase S n ↔
      1 ≤ r ∧ r ≤ primeWorldModulus S ∧ SupportDisjointFrom S (n ^ 2 + r) := by
  rw [mem_coarsePrimeWorldBase, supportDisjointFrom_iff_coprime_primeWorldModulus hS]

/-- A translated complete period has the same cardinality, for every anchor phase. -/
theorem card_coarsePrimeWorldBase (S : Finset ℕ) (n : ℕ) :
    (coarsePrimeWorldBase S n).card = Nat.totient (primeWorldModulus S) := by
  classical
  let M := primeWorldModulus S
  have hbij : (coarsePrimeWorldBase S n).card =
      ((Finset.Ico (n ^ 2 + 1) (n ^ 2 + 1 + M)).filter
        (fun x => Nat.Coprime M x)).card := by
    apply Finset.card_bij (fun r _ => n ^ 2 + r)
    · intro r hr
      rcases mem_coarsePrimeWorldBase.mp hr with ⟨h1, h2, hc⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, hc.symm⟩
    · intro r hr s hs he
      omega
    · intro x hx
      rcases Finset.mem_filter.mp hx with ⟨hb, hc⟩
      rcases Finset.mem_Ico.mp hb with ⟨h1, h2⟩
      refine ⟨x - n ^ 2, mem_coarsePrimeWorldBase.mpr ⟨by omega, by omega, ?_⟩, by omega⟩
      (convert hc.symm using 1; omega)
  rw [hbij]
  exact Nat.filter_coprime_Ico_eq_totient M (n ^ 2 + 1)

private theorem phase_injective_on_period {M a r s : ℕ}
    (hr : 1 ≤ r ∧ r ≤ M) (hs : 1 ≤ s ∧ s ≤ M)
    (he : (a + r) % M = (a + s) % M) : r = s := by
  have hmod : Nat.ModEq M r s := Nat.ModEq.add_left_cancel' a he
  by_cases hrs : r ≤ s
  · have hd := hmod.dvd'
    have hlt : s - r < M := by omega
    have hz := Nat.eq_zero_of_dvd_of_lt hd hlt
    omega
  · have hd := hmod.symm.dvd'
    have hlt : r - s < M := by omega
    have hz := Nat.eq_zero_of_dvd_of_lt hd hlt
    omega

/-- Projection enumerates every canonical world residue once. -/
theorem image_coarsePrimeWorldBase_address {S : Finset ℕ}
    (hS : KnownPrimeScales S) (hM : 1 < primeWorldModulus S) (n : ℕ) :
    (coarsePrimeWorldBase S n).image (squareShellWheelProjection S n) =
      primeWorldResidues S := by
  apply Finset.eq_of_subset_of_card_le
  · intro a ha
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp ha
    exact (supportDisjointFrom_iff_squareShell_address hS n r).mp
      ((mem_coarsePrimeWorldBase_iff_survivor hS).mp hr).2.2
  · rw [Finset.card_image_iff.mpr]
    · rw [card_coarsePrimeWorldBase, card_primeWorldResidues_eq_totient hM]
    · intro r hr s hs he
      have hr' := mem_coarsePrimeWorldBase.mp hr
      have hs' := mem_coarsePrimeWorldBase.mp hs
      exact phase_injective_on_period ⟨hr'.1, hr'.2.1⟩ ⟨hs'.1, hs'.2.1⟩ he

theorem existsUnique_coarsePrimeWorldBase_address {S : Finset ℕ}
    (hS : KnownPrimeScales S) (hM : 1 < primeWorldModulus S) (n : ℕ)
    {a : ℕ} (ha : a ∈ primeWorldResidues S) :
    ∃! r, r ∈ coarsePrimeWorldBase S n ∧ squareShellWheelProjection S n r = a := by
  rw [← image_coarsePrimeWorldBase_address hS hM n] at ha
  obtain ⟨r, hr, he⟩ := Finset.mem_image.mp ha
  refine ⟨r, ⟨hr, he⟩, ?_⟩
  intro s hs
  have hr' := mem_coarsePrimeWorldBase.mp hr
  have hs' := mem_coarsePrimeWorldBase.mp hs.1
  exact phase_injective_on_period ⟨hs'.1, hs'.2.1⟩ ⟨hr'.1, hr'.2.1⟩
    (hs.2.trans he.symm)

/-- The same-anchor odd-gap dictionary inherits the nontrivial-modulus guard. -/
theorem centeredOddGapPrimeWorld_residues_eq_packet (n : ℕ)
    (hM : 1 < primeWorldModulus (centeredOddGapPrimeWorld n)) :
    primeWorldResidues (centeredOddGapPrimeWorld n) =
      squareAnchorCoprimeBaseOffsets (primeWorldModulus (centeredOddGapPrimeWorld n)) :=
  primeWorldResidues_eq_packetBase hM

/-- Only an explicit anchor-divisibility premise removes the square-point phase. -/
theorem coarsePrimeWorldBase_eq_packet_of_modulus_dvd_anchor {S : Finset ℕ} {n : ℕ}
    (hn : primeWorldModulus S ∣ n) :
    coarsePrimeWorldBase S n = squareAnchorCoprimeBaseOffsets (primeWorldModulus S) := by
  have hd : primeWorldModulus S ∣ n ^ 2 := by
    rw [pow_two]
    exact dvd_mul_of_dvd_left hn n
  ext r
  rw [mem_coarsePrimeWorldBase, mem_squareAnchorCoprimeBaseOffsets,
    Nat.coprime_comm, Nat.coprime_add_iff_right hd]

theorem card_coarsePrimeWorldBase_eq_residues {S : Finset ℕ}
    (hM : 1 < primeWorldModulus S) (n : ℕ) :
    (coarsePrimeWorldBase S n).card = (primeWorldResidues S).card := by
  rw [card_coarsePrimeWorldBase, card_primeWorldResidues_eq_totient hM]

end DkMath.NumberTheory.Legendre
