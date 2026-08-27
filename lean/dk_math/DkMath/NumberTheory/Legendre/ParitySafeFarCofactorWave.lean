/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeFarTripleCofactorSupport

#print "file: DkMath.NumberTheory.Legendre.ParitySafeFarCofactorWave"

/-!
## ParitySafeFarCofactorWave

PRIM-L046 separates the actual parity-safe residual triple incidences into
near and far parts and charges far cofactor reuse by the local square wave of
the cofactor value.  A far incidence is mapped to `(t,r)`, where `t` is its
complementary cofactor and `r` is its seat.  The map is locally injective even
when the same cofactor value occurs at different seats.

This is a finite multiplicity budget.  It does not make `t` globally
injective, does not estimate the resulting sum harmonically, and does not
prove a smaller-anchor cover or Legendre's conjecture.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open DkMath.NumberTheory.Legendre.Internal
open scoped BigOperators

/-! ### PRIM-L046.1: actual near/far residual split -/

/-- Actual residual triples whose canonical triple key is in the far gate. -/
noncomputable def paritySafeCanonicalFarResidualTripleIncidences
    (n : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  (paritySafeCanonicalResidualTripleIncidences n).filter
    (fun triple =>
      (paritySafeCanonicalSupportPrime n triple.1, triple.2) ∈
        paritySafeTripleGateFarTriples n)

/-- Actual residual triples whose canonical triple key is in the near gate. -/
noncomputable def paritySafeCanonicalNearResidualTripleIncidences
    (n : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  (paritySafeCanonicalResidualTripleIncidences n).filter
    (fun triple =>
      (paritySafeCanonicalSupportPrime n triple.1, triple.2) ∈
        paritySafeTripleGateNearTriples n)

@[simp] theorem mem_paritySafeCanonicalFarResidualTripleIncidences
    {n : ℕ} {triple : ℕ × (ℕ × ℕ)} :
    triple ∈ paritySafeCanonicalFarResidualTripleIncidences n ↔
      triple ∈ paritySafeCanonicalResidualTripleIncidences n ∧
        (paritySafeCanonicalSupportPrime n triple.1, triple.2) ∈
          paritySafeTripleGateFarTriples n := by
  simp [paritySafeCanonicalFarResidualTripleIncidences]

@[simp] theorem mem_paritySafeCanonicalNearResidualTripleIncidences
    {n : ℕ} {triple : ℕ × (ℕ × ℕ)} :
    triple ∈ paritySafeCanonicalNearResidualTripleIncidences n ↔
      triple ∈ paritySafeCanonicalResidualTripleIncidences n ∧
        (paritySafeCanonicalSupportPrime n triple.1, triple.2) ∈
          paritySafeTripleGateNearTriples n := by
  simp [paritySafeCanonicalNearResidualTripleIncidences]

theorem paritySafeCanonicalNearFarResidual_disjoint (n : ℕ) :
    Disjoint (paritySafeCanonicalNearResidualTripleIncidences n)
      (paritySafeCanonicalFarResidualTripleIncidences n) := by
  rw [Finset.disjoint_left]
  intro triple hnear hfar
  exact Finset.disjoint_left.mp (paritySafeTripleGateNearFar_disjoint n)
    (mem_paritySafeCanonicalNearResidualTripleIncidences.mp hnear).2
    (mem_paritySafeCanonicalFarResidualTripleIncidences.mp hfar).2

theorem paritySafeCanonicalNearFarResidual_union (n : ℕ) :
    paritySafeCanonicalNearResidualTripleIncidences n ∪
        paritySafeCanonicalFarResidualTripleIncidences n =
      paritySafeCanonicalResidualTripleIncidences n := by
  ext triple
  constructor
  · intro h
    rcases Finset.mem_union.mp h with hnear | hfar
    · exact (mem_paritySafeCanonicalNearResidualTripleIncidences.mp hnear).1
    · exact (mem_paritySafeCanonicalFarResidualTripleIncidences.mp hfar).1
  · intro hres
    have hkey := paritySafeCanonicalResidualTripleIncidence_mem_tripleGateTriples hres
    have hnf :
        (paritySafeCanonicalSupportPrime n triple.1, triple.2) ∈
            paritySafeTripleGateNearTriples n ∨
          (paritySafeCanonicalSupportPrime n triple.1, triple.2) ∈
            paritySafeTripleGateFarTriples n := by
      have hmem := show
          (paritySafeCanonicalSupportPrime n triple.1, triple.2) ∈
            paritySafeTripleGateNearTriples n ∪
              paritySafeTripleGateFarTriples n by
        rw [paritySafeTripleGateNearFar_union n]
        exact hkey
      exact Finset.mem_union.mp hmem
    rcases hnf with hnear | hfar
    · exact Finset.mem_union.mpr (Or.inl
        (mem_paritySafeCanonicalNearResidualTripleIncidences.mpr ⟨hres, hnear⟩))
    · exact Finset.mem_union.mpr (Or.inr
        (mem_paritySafeCanonicalFarResidualTripleIncidences.mpr ⟨hres, hfar⟩))

theorem paritySafeResidualPairMass_eq_near_add_far_card (n : ℕ) :
    paritySafeResidualPairMass n =
      (paritySafeCanonicalNearResidualTripleIncidences n).card +
      (paritySafeCanonicalFarResidualTripleIncidences n).card := by
  calc
    paritySafeResidualPairMass n =
        (paritySafeCanonicalResidualTripleIncidences n).card :=
      (paritySafeCanonicalResidualTripleIncidences_card_eq_residual n).symm
    _ = (paritySafeCanonicalNearResidualTripleIncidences n ∪
        paritySafeCanonicalFarResidualTripleIncidences n).card := by
      rw [paritySafeCanonicalNearFarResidual_union]
    _ = _ := Finset.card_union_of_disjoint
      (paritySafeCanonicalNearFarResidual_disjoint n)

/-! ### PRIM-L046.2: fixed-seat cofactor-value injectivity -/

private theorem ordered_prime_pair_eq_of_mul_eq
    {q₁ s₁ q₂ s₂ : ℕ}
    (hq₁ : Nat.Prime q₁)
    (hq₂ : Nat.Prime q₂) (hs₂ : Nat.Prime s₂)
    (hlt₁ : q₁ < s₁) (hlt₂ : q₂ < s₂)
    (hmul : q₁ * s₁ = q₂ * s₂) :
    q₁ = q₂ ∧ s₁ = s₂ := by
  have hdiv : q₁ ∣ q₂ * s₂ := by
    rw [← hmul]
    exact dvd_mul_right q₁ s₁
  rcases (hq₁.dvd_mul).mp hdiv with hqeq | hseq
  · have hqeq' := ((Nat.dvd_prime hq₂).mp hqeq).resolve_left hq₁.ne_one
    subst q₁
    have hse : s₁ = s₂ := by
      exact Nat.mul_left_cancel hq₂.pos hmul
    exact ⟨rfl, hse⟩
  · have hseq' := ((Nat.dvd_prime hs₂).mp hseq).resolve_left hq₁.ne_one
    subst q₁
    have hse : s₁ = q₂ := by
      apply Nat.mul_right_cancel hs₂.pos
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
    omega

/-- At a fixed seat, equal positive cofactor values determine the ordered
residual pair without any no-depth hypothesis. -/
theorem paritySafeFarTripleCofactor_value_local_injective
    {n r q₁ s₁ q₂ s₂ : ℕ}
    (hinc₁ : (r, (q₁, s₁)) ∈ paritySafeCanonicalResidualTripleIncidences n)
    (hfar₁ : (paritySafeCanonicalSupportPrime n r, (q₁, s₁)) ∈
      paritySafeTripleGateFarTriples n)
    (hinc₂ : (r, (q₂, s₂)) ∈ paritySafeCanonicalResidualTripleIncidences n)
    (hfar₂ : (paritySafeCanonicalSupportPrime n r, (q₂, s₂)) ∈
      paritySafeTripleGateFarTriples n)
    (ht : paritySafeFarTripleCofactor n r q₁ s₁ =
      paritySafeFarTripleCofactor n r q₂ s₂) :
    q₁ = q₂ ∧ s₁ = s₂ := by
  have hfac₁ := (paritySafeFarTripleCofactor_packet hinc₁ hfar₁).2.1
  have hfac₂ := (paritySafeFarTripleCofactor_packet hinc₂ hfar₂).2.1
  have htpos₂ := (paritySafeFarTripleCofactor_packet hinc₂ hfar₂).1
  have hmul :
      paritySafeCanonicalSupportPrime n r * (q₁ * s₁) =
        paritySafeCanonicalSupportPrime n r * (q₂ * s₂) := by
    have hprod :
        paritySafeCanonicalSupportPrime n r * q₁ * s₁ *
              paritySafeFarTripleCofactor n r q₁ s₁ =
          paritySafeCanonicalSupportPrime n r * q₂ * s₂ *
              paritySafeFarTripleCofactor n r q₂ s₂ := by
      rw [hfac₁, hfac₂]
    have hprod' := hprod
    rw [ht] at hprod'
    have hcancel := Nat.mul_right_cancel htpos₂ hprod'
    simpa [Nat.mul_assoc] using hcancel
  have hqs : q₁ * s₁ = q₂ * s₂ :=
    Nat.mul_left_cancel
      (mem_squareAnchorOddActivePrimes.mp
        (paritySafeCanonicalResidualTripleIncidence_packet hinc₁).2.1).1.pos hmul
  rcases paritySafeCanonicalResidualTripleIncidence_packet hinc₁ with
    ⟨_, _, hq₁active, hs₁active, _, _, _, _, _⟩
  rcases paritySafeCanonicalResidualTripleIncidence_packet hinc₂ with
    ⟨_, _, hq₂active, hs₂active, _, _, _, _, _⟩
  have hq₁prime := (mem_squareAnchorOddActivePrimes.mp hq₁active).1
  have hs₁prime := (mem_squareAnchorOddActivePrimes.mp hs₁active).1
  have hq₂prime := (mem_squareAnchorOddActivePrimes.mp hq₂active).1
  have hs₂prime := (mem_squareAnchorOddActivePrimes.mp hs₂active).1
  exact ordered_prime_pair_eq_of_mul_eq hq₁prime hq₂prime hs₂prime
    (Finset.mem_filter.mp hinc₁).2.1 (Finset.mem_filter.mp hinc₂).2.1 hqs

/-! ### PRIM-L046.3: finite cofactor world -/

/-- Positive first-half coprime cofactors at the original anchor. -/
noncomputable def paritySafeFarCofactorBaseOffsets (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter (fun t => Nat.Coprime (2 * n) t)

@[simp] theorem mem_paritySafeFarCofactorBaseOffsets
    {n t : ℕ} :
    t ∈ paritySafeFarCofactorBaseOffsets n ↔
      1 ≤ t ∧ t ≤ n ∧ Nat.Coprime (2 * n) t := by
  simp [paritySafeFarCofactorBaseOffsets, and_assoc]

/-- Every far cofactor belongs to the finite same-anchor cofactor world. -/
theorem paritySafeFarTripleCofactor_mem_farCofactorBaseOffsets
    {n r q s : ℕ}
    (hinc : (r, (q, s)) ∈ paritySafeCanonicalResidualTripleIncidences n)
    (hfar : (paritySafeCanonicalSupportPrime n r, (q, s)) ∈
      paritySafeTripleGateFarTriples n) :
    paritySafeFarTripleCofactor n r q s ∈
      paritySafeFarCofactorBaseOffsets n := by
  have hp := paritySafeFarTripleCofactor_packet hinc hfar
  rcases hp with ⟨htpos, _, _, htsmall, htcop⟩
  exact mem_paritySafeFarCofactorBaseOffsets.mpr ⟨by omega, htsmall.le, htcop⟩

/-! ### PRIM-L046.4: cofactor wave upper budget -/

/-- Upper incidences `(t,r)` for finite cofactor waves. -/
noncomputable def paritySafeFarCofactorWaveUpperIncidences
    (n : ℕ) : Finset (ℕ × ℕ) :=
  ((paritySafeFarCofactorBaseOffsets n).product (squareOffsets n)).filter
    (fun hit => hit.2 ∈ squareWaveOffsets n hit.1)

/-- The finite budget obtained by summing the cofactor wave occupancies. -/
noncomputable def paritySafeFarCofactorWaveBudget (n : ℕ) : ℕ :=
  ∑ t ∈ paritySafeFarCofactorBaseOffsets n,
    (squareWaveOffsets n t).card

theorem paritySafeFarCofactorWaveUpperIncidences_card_eq_budget (n : ℕ) :
    (paritySafeFarCofactorWaveUpperIncidences n).card =
      paritySafeFarCofactorWaveBudget n := by
  classical
  unfold paritySafeFarCofactorWaveUpperIncidences
  calc
    (((paritySafeFarCofactorBaseOffsets n).product (squareOffsets n)).filter
        (fun hit => hit.2 ∈ squareWaveOffsets n hit.1)).card =
      ∑ hit ∈ (paritySafeFarCofactorBaseOffsets n).product (squareOffsets n),
        if hit.2 ∈ squareWaveOffsets n hit.1 then 1 else 0 := by simp
    _ = ∑ t ∈ paritySafeFarCofactorBaseOffsets n,
        ∑ r ∈ squareOffsets n,
          if r ∈ squareWaveOffsets n t then 1 else 0 := by
      exact Finset.sum_product'
        (paritySafeFarCofactorBaseOffsets n) (squareOffsets n)
        (fun t r => if r ∈ squareWaveOffsets n t then 1 else 0)
    _ = ∑ t ∈ paritySafeFarCofactorBaseOffsets n,
        (squareWaveOffsets n t).card := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.sum_boole]
      apply congrArg Finset.card
      ext r
      simp only [Finset.mem_filter]
      constructor
      · exact And.right
      · intro hr
        exact ⟨mem_squareOffsets.mpr (mem_squareWaveOffsets.mp hr).1, hr⟩
    _ = paritySafeFarCofactorWaveBudget n := rfl

/-! ### PRIM-L046.5: far incidence to cofactor-wave key -/

/-- The seat-local cofactor-wave key. -/
noncomputable def paritySafeFarCofactorWaveKey
    (n : ℕ) (triple : ℕ × (ℕ × ℕ)) : ℕ × ℕ :=
  (paritySafeFarTripleCofactor n triple.1 triple.2.1 triple.2.2, triple.1)

theorem paritySafeCanonicalFarResidualTripleIncidences_card_le_cofactorWaveBudget
    (n : ℕ) :
    (paritySafeCanonicalFarResidualTripleIncidences n).card ≤
      paritySafeFarCofactorWaveBudget n := by
  classical
  let f : ℕ × (ℕ × ℕ) → ℕ × ℕ := paritySafeFarCofactorWaveKey n
  have hinj : Set.InjOn f
      (paritySafeCanonicalFarResidualTripleIncidences n : Set (ℕ × (ℕ × ℕ))) := by
    intro a ha b hb hab
    rcases a with ⟨ra, qa, sa⟩
    rcases b with ⟨rb, qb, sb⟩
    dsimp [f, paritySafeFarCofactorWaveKey] at hab
    have hra : ra = rb := congrArg Prod.snd hab
    have hta : paritySafeFarTripleCofactor n ra qa sa =
        paritySafeFarTripleCofactor n rb qb sb := congrArg Prod.fst hab
    have ha' := mem_paritySafeCanonicalFarResidualTripleIncidences.mp ha
    have hb' := mem_paritySafeCanonicalFarResidualTripleIncidences.mp hb
    subst rb
    have hp := paritySafeFarTripleCofactor_value_local_injective
      ha'.1 ha'.2 hb'.1 hb'.2 hta
    exact Prod.ext rfl (Prod.ext hp.1 hp.2)
  have hcard :
      (paritySafeCanonicalFarResidualTripleIncidences n).card =
        ((paritySafeCanonicalFarResidualTripleIncidences n).image f).card := by
    exact (Finset.card_image_of_injOn hinj).symm
  have hsubset :
      (paritySafeCanonicalFarResidualTripleIncidences n).image f ⊆
        paritySafeFarCofactorWaveUpperIncidences n := by
    intro hit hhit
    rcases Finset.mem_image.mp hhit with ⟨triple, htriple, rfl⟩
    have hfar := mem_paritySafeCanonicalFarResidualTripleIncidences.mp htriple
    have hbase := paritySafeFarTripleCofactor_mem_farCofactorBaseOffsets
      hfar.1 hfar.2
    have hseat := squareOffset_of_mem_squareAnchorOddPointCoprimeOffsets
      (paritySafeCanonicalResidualTripleIncidence_packet hfar.1).1
    have hfactor := (paritySafeFarTripleCofactor_packet hfar.1 hfar.2).2.1
    have htdiv : paritySafeFarTripleCofactor n triple.1 triple.2.1 triple.2.2 ∣
        n ^ 2 + triple.1 := by
      refine ⟨paritySafeCanonicalSupportPrime n triple.1 * triple.2.1 * triple.2.2, ?_⟩
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hfactor.symm
    have hwave : triple.1 ∈ squareWaveOffsets n
        (paritySafeFarTripleCofactor n triple.1 triple.2.1 triple.2.2) :=
      mem_squareWaveOffsets.mpr ⟨hseat, htdiv⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨hbase, mem_squareOffsets.mpr hseat⟩, hwave⟩
  have hupper := Finset.card_le_card hsubset
  rw [← hcard] at hupper
  rw [paritySafeFarCofactorWaveUpperIncidences_card_eq_budget] at hupper
  exact hupper

/-! ### PRIM-L046.6: exact wave arithmetic -/

/-- The cofactor wave budget splits into complete local periods and carries. -/
theorem paritySafeFarCofactorWaveBudget_eq_div_add_carry (n : ℕ) :
    paritySafeFarCofactorWaveBudget n =
      ∑ t ∈ paritySafeFarCofactorBaseOffsets n,
        ((2 * n) / t + squareWaveCarry n t) := by
  unfold paritySafeFarCofactorWaveBudget
  apply Finset.sum_congr rfl
  intro t ht
  rw [card_squareWaveOffsets_eq_div_add_carry]
  have htpos : 0 < t := by
    have htmem := mem_paritySafeFarCofactorBaseOffsets.mp ht
    omega
  exact htpos

/-! ### PRIM-L046.7: the L044 false beam as positive wave occupancy -/

/-- The two L044 seats with cofactor `7` lie on the same arithmetic wave. -/
theorem paritySafeFarCofactorWave_false_beam_62_7 :
    7 ∈ paritySafeFarCofactorBaseOffsets 62 ∧
      41 ∈ squareWaveOffsets 62 7 ∧
      83 ∈ squareWaveOffsets 62 7 := by
  norm_num [paritySafeFarCofactorBaseOffsets, squareWaveOffsets,
    mem_squareOffsets, SquareOffset, SquareOffsetForbiddenBy]

end DkMath.NumberTheory.Legendre
