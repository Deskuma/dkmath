/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicCubeDefect
import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicSquareGaloisSupport
import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicSquareIdealSupport
import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicSquareTwistObstruction

#print "file: DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicPrimeAllocation"

namespace DkMath.FLT.Seven

noncomputable section

open SevenRealCubicInt
open scoped NumberField Pointwise

set_option linter.style.longLine false
set_option linter.style.setOption false

namespace SevenRealCubic

def gapSquareIdeal
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) : Ideal O :=
  Ideal.span {modelEquivRingOfIntegers t.gapSquareRoot}

def quotientSquareIdeal
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) : Ideal O :=
  Ideal.span {modelEquivRingOfIntegers t.quotientSquareRoot}

private theorem principal_span_mul_eq_of_unit_mul
    {A : Type*} [CommRing A] {r s a : A} {u : Aˣ}
    (hu : IsUnit (u : A)) (h : r * s = (u : A) * a) :
    Ideal.span ({r} : Set A) * Ideal.span ({s} : Set A) =
      Ideal.span ({a} : Set A) := by
  calc
    Ideal.span ({r} : Set A) * Ideal.span ({s} : Set A) =
        Ideal.span ({r * s} : Set A) :=
      Ideal.span_singleton_mul_span_singleton r s
    _ = Ideal.span ({(u : A) * a} : Set A) := by rw [h]
    _ = Ideal.span ({a} : Set A) := by
      rw [mul_comm]
      exact Ideal.span_singleton_mul_right_unit hu a

theorem directOrbitSquareRefinement_principal_ideal_scalar_split
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    Ideal.span ({modelEquivRingOfIntegers t.gapSquareRoot} : Set O) *
        Ideal.span ({modelEquivRingOfIntegers t.quotientSquareRoot} : Set O) =
      Ideal.span ({modelEquivRingOfIntegers
        (t.powerSplit.gapSplit.a : SevenRealCubicInt)} : Set O) := by
  obtain ⟨u, hu⟩ := directOrbitSquareRefinement_squareRoots_unit_split t
  let uO : Oˣ := Units.map modelEquivRingOfIntegers.toMonoidHom u
  have hmap :
      modelEquivRingOfIntegers (t.gapSquareRoot * t.quotientSquareRoot) =
        modelEquivRingOfIntegers (u : SevenRealCubicInt) *
          modelEquivRingOfIntegers
            (t.powerSplit.gapSplit.a : SevenRealCubicInt) := by
    simpa only [map_mul] using congrArg modelEquivRingOfIntegers hu
  exact principal_span_mul_eq_of_unit_mul
    (A := O)
    (r := modelEquivRingOfIntegers t.gapSquareRoot)
    (s := modelEquivRingOfIntegers t.quotientSquareRoot)
    (a := modelEquivRingOfIntegers
      (t.powerSplit.gapSplit.a : SevenRealCubicInt))
    (u := uO) uO.isUnit (by simpa [uO] using hmap)

theorem directOrbitSquareRefinement_ideal_coprime
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    IsCoprime (gapSquareIdeal t) (quotientSquareIdeal t) := by
  exact directOrbitSquareRefinement_squareRoots_isCoprime_ringOfIntegers t

theorem directOrbitSquareRefinement_common_prime_dvd_scalar
    {x y z q : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p)
    (hq : q.Prime)
    (hqR : q ∣ Int.natAbs (norm t.gapSquareRoot))
    (_hqS : q ∣ Int.natAbs (norm t.quotientSquareRoot)) :
    q ∣ t.powerSplit.gapSplit.a := by
  have hqcube : q ∣ t.powerSplit.gapSplit.a ^ 3 := by
    rw [← directOrbitSquareRefinement_squareRoots_norm_product t]
    exact dvd_mul_of_dvd_left hqR _
  exact hq.dvd_of_dvd_pow hqcube

theorem directOrbitSquareRefinement_prime_ideal_allocation_xor
    {x y z q : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p)
    (hq : q.Prime)
    (hqR : q ∣ Int.natAbs (norm t.gapSquareRoot))
    (hqS : q ∣ Int.natAbs (norm t.quotientSquareRoot))
    (P : Ideal O) (hPprime : P.IsPrime)
    (hPover : P.LiesOver (Ideal.span {(q : ℤ)})) :
    Xor (gapSquareIdeal t ≤ P) (quotientSquareIdeal t ≤ P) := by
  have hqa := directOrbitSquareRefinement_common_prime_dvd_scalar
    t hq hqR hqS
  have hqmem : (q : O) ∈ P := by
    apply (Ideal.mem_under ℤ P).mp
    rw [← hPover.over]
    exact Ideal.mem_span_singleton_self _
  have hamem :
      modelEquivRingOfIntegers
          (t.powerSplit.gapSplit.a : SevenRealCubicInt) ∈ P := by
    obtain ⟨k, hk⟩ := hqa
    have hkO : (t.powerSplit.gapSplit.a : O) = (q : O) * (k : O) := by
      exact_mod_cast hk
    rw [show modelEquivRingOfIntegers
        (t.powerSplit.gapSplit.a : SevenRealCubicInt) =
          (t.powerSplit.gapSplit.a : O) by simp, hkO]
    exact P.mul_mem_right _ hqmem
  have hprodmem :
      modelEquivRingOfIntegers t.gapSquareRoot *
          modelEquivRingOfIntegers t.quotientSquareRoot ∈ P := by
    have hspan :
        Ideal.span {modelEquivRingOfIntegers
          (t.powerSplit.gapSplit.a : SevenRealCubicInt)} ≤ P :=
      (Ideal.span_singleton_le_iff_mem P).mpr hamem
    have hprodideal : gapSquareIdeal t * quotientSquareIdeal t ≤ P := by
      change (Ideal.span ({modelEquivRingOfIntegers t.gapSquareRoot} : Set O) *
          Ideal.span ({modelEquivRingOfIntegers t.quotientSquareRoot} : Set O)) ≤ P
      rw [directOrbitSquareRefinement_principal_ideal_scalar_split t]
      exact hspan
    exact hprodideal (Ideal.mul_mem_mul
      (Ideal.mem_span_singleton_self _) (Ideal.mem_span_singleton_self _))
  rcases hPprime.mem_or_mem hprodmem with hr | hs
  · refine Or.inl ⟨(Ideal.span_singleton_le_iff_mem P).mpr hr, ?_⟩
    intro hs'
    exact hPprime.ne_top (top_unique ((directOrbitSquareRefinement_ideal_coprime t).sup_eq ▸
      sup_le ((Ideal.span_singleton_le_iff_mem P).mpr hr) hs') )
  · refine Or.inr ⟨(Ideal.span_singleton_le_iff_mem P).mpr hs, ?_⟩
    intro hr'
    exact hPprime.ne_top (top_unique ((directOrbitSquareRefinement_ideal_coprime t).sup_eq ▸
      sup_le hr' ((Ideal.span_singleton_le_iff_mem P).mpr hs)) )

/-! ## The cyclic Galois actor and its ideal-action orientation -/

abbrev directOrbitGaloisSigma : Gal(Field / ℚ) := fieldRotateEquiv

theorem directOrbitGaloisSigma_three :
    directOrbitGaloisSigma ^ 3 = 1 := by
  ext x
  change fieldRotateEquiv (fieldRotateEquiv (fieldRotateEquiv x)) = x
  exact fieldRotateEquiv_three x

theorem directOrbitGaloisSigma_ne_one :
    directOrbitGaloisSigma ≠ 1 := by
  change fieldRotateEquiv ≠ (AlgEquiv.refl : Field ≃ₐ[ℚ] Field)
  exact fieldRotateEquiv_ne_one

theorem directOrbitGaloisSigma_element_eq
    (g : Gal(Field/ℚ)) :
    g = 1 ∨ g = directOrbitGaloisSigma ∨
      g = directOrbitGaloisSigma ^ 2 := by
  classical
  have hsq : directOrbitGaloisSigma ^ 2 ≠ 1 := by
    intro h
    apply directOrbitGaloisSigma_ne_one
    calc
      directOrbitGaloisSigma = directOrbitGaloisSigma * 1 := by simp
      _ = directOrbitGaloisSigma * directOrbitGaloisSigma ^ 2 := by rw [h]
      _ = directOrbitGaloisSigma ^ 3 := by simp [pow_succ, mul_assoc]
      _ = 1 := directOrbitGaloisSigma_three
  have hrot : directOrbitGaloisSigma ≠ directOrbitGaloisSigma ^ 2 := by
    intro h
    have h' := congrArg
      (fun u : Gal(Field / ℚ) => directOrbitGaloisSigma⁻¹ * u) h
    have hone : (1 : Gal(Field / ℚ)) = directOrbitGaloisSigma := by
      simpa [pow_two, mul_assoc] using h'
    exact directOrbitGaloisSigma_ne_one hone.symm
  let s : Finset (Gal(Field / ℚ)) :=
    insert (directOrbitGaloisSigma ^ 2)
      (insert directOrbitGaloisSigma ({1} : Finset (Gal(Field / ℚ))))
  have hs : s.card = 3 := by
    simp [s, directOrbitGaloisSigma_ne_one, hsq, hrot.symm]
  have hcard : Fintype.card (Gal(Field / ℚ)) = 3 := by
    rw [← Nat.card_eq_fintype_card]
    exact galois_group_card_three
  have hs_univ : s = Finset.univ :=
    Finset.eq_univ_of_card s (hs.trans hcard.symm)
  have hg : g ∈ s := by
    rw [hs_univ]
    simp
  rcases (by simpa [s] using hg) with h | h | h
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)
  · exact Or.inl h

theorem directOrbitGaloisSigma_ringAction :
    MulSemiringAction.toRingAut (Gal(Field / ℚ)) O directOrbitGaloisSigma =
      ringOfIntegersRotateEquiv := by
  ext x
  change fieldRotateEquiv (algebraMap O Field x) =
    algebraMap O Field (ringOfIntegersRotateEquiv x)
  exact fieldRotateEquiv_algebraMap_ringOfIntegers x

theorem directOrbitGaloisSigma_model_rotate (x : SevenRealCubicInt) :
    ringOfIntegersRotateEquiv (modelEquivRingOfIntegers x) =
      modelEquivRingOfIntegers (rotateEquiv x) := by
  rw [ringOfIntegersRotateEquiv_apply,
    modelEquivRingOfIntegers.symm_apply_apply]

theorem directOrbitGaloisSigma_mem_iff (P : Ideal O) (x : O) :
    x ∈ directOrbitGaloisSigma • P ↔
      ringOfIntegersRotateEquiv.symm x ∈ P := by
  rw [Ideal.pointwise_smul_eq_comap, Ideal.mem_comap,
    directOrbitGaloisSigma_ringAction]

theorem directOrbitGaloisSigma_model_rotate_mem_iff
    (P : Ideal O) (x : SevenRealCubicInt) :
    modelEquivRingOfIntegers (rotateEquiv x) ∈
        directOrbitGaloisSigma • P ↔
      modelEquivRingOfIntegers x ∈ P := by
  rw [Ideal.pointwise_smul_eq_comap, Ideal.mem_comap,
    directOrbitGaloisSigma_ringAction]
  rw [← directOrbitGaloisSigma_model_rotate x,
    RingEquiv.symm_apply_apply]

theorem directOrbitGaloisSigma_sq_model_mem_iff
    (P : Ideal O) (x : SevenRealCubicInt) :
    modelEquivRingOfIntegers x ∈ directOrbitGaloisSigma ^ 2 • P ↔
      modelEquivRingOfIntegers (rotateEquiv x) ∈ P := by
  rw [show directOrbitGaloisSigma ^ 2 • P =
      directOrbitGaloisSigma • (directOrbitGaloisSigma • P) by
    rw [pow_two, mul_smul]]
  have hsecond :
      modelEquivRingOfIntegers x ∈
          directOrbitGaloisSigma • (directOrbitGaloisSigma • P) ↔
        modelEquivRingOfIntegers (rotateEquiv (rotateEquiv x)) ∈
          directOrbitGaloisSigma • P := by
    have hh := directOrbitGaloisSigma_model_rotate_mem_iff
      (directOrbitGaloisSigma • P) (rotateEquiv (rotateEquiv x))
    rw [SevenRealCubicInt.rotateEquiv_three] at hh
    exact hh
  have hfirst := directOrbitGaloisSigma_model_rotate_mem_iff P
    (rotateEquiv x)
  exact hsecond.trans hfirst

theorem directOrbit_two_rotated_gap_roots_mem_imp_all_three_mem
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p)
    (P : Ideal O) (hPprime : P.IsPrime)
    (h0 : modelEquivRingOfIntegers t.gapSquareRoot ∈ P)
    (h1 : modelEquivRingOfIntegers (rotateEquiv t.gapSquareRoot) ∈ P) :
    modelEquivRingOfIntegers
        (rotateEquiv (rotateEquiv t.gapSquareRoot)) ∈ P := by
  let c0 : O := modelEquivRingOfIntegers
    (directOrbitSquareTwistCoeff0 t : SevenRealCubicInt)
  let c1 : O := modelEquivRingOfIntegers
    (directOrbitSquareTwistCoeff1 t : SevenRealCubicInt)
  let c2 : O := modelEquivRingOfIntegers
    (directOrbitSquareTwistCoeff2 t : SevenRealCubicInt)
  let r0 : O := modelEquivRingOfIntegers t.gapSquareRoot
  let r1 : O := modelEquivRingOfIntegers (rotateEquiv t.gapSquareRoot)
  let r2 : O := modelEquivRingOfIntegers
    (rotateEquiv (rotateEquiv t.gapSquareRoot))
  have hEq := congrArg modelEquivRingOfIntegers
    (directOrbit_squareTwist_twisted_eq t)
  have hEqO : c0 * (r0 ^ 7) ^ 2 + c1 * (r1 ^ 7) ^ 2 +
      c2 * (r2 ^ 7) ^ 2 = 0 := by
    simpa only [c0, c1, c2, r0, r1, r2, map_add, map_mul, map_pow,
      map_zero, Units.val_mul, Units.val_pow_eq_pow_val] using hEq
  have ht0 : c0 * (r0 ^ 7) ^ 2 ∈ P := by
    apply P.mul_mem_left
    exact P.pow_mem_of_mem (P.pow_mem_of_mem h0 7 (by norm_num)) 2 (by norm_num)
  have ht1 : c1 * (r1 ^ 7) ^ 2 ∈ P := by
    apply P.mul_mem_left
    exact P.pow_mem_of_mem (P.pow_mem_of_mem h1 7 (by norm_num)) 2 (by norm_num)
  have ht2 : c2 * (r2 ^ 7) ^ 2 ∈ P := by
    have hrewrite : c2 * (r2 ^ 7) ^ 2 =
        -(c0 * (r0 ^ 7) ^ 2 + c1 * (r1 ^ 7) ^ 2) := by
      linear_combination hEqO
    rw [hrewrite]
    exact P.neg_mem (P.add_mem ht0 ht1)
  have hc2 : IsUnit c2 := by
    exact IsUnit.map modelEquivRingOfIntegers.toRingHom
      (directOrbitSquareTwistCoeff2 t).isUnit
  have hpow : (r2 ^ 7) ^ 2 ∈ P :=
    (P.unit_mul_mem_iff_mem hc2).mp ht2
  have hpow' : r2 ^ 14 ∈ P := by
    have heq : r2 ^ 14 = (r2 ^ 7) ^ 2 := by
      calc
        r2 ^ 14 = r2 ^ (7 * 2) := by norm_num
        _ = (r2 ^ 7) ^ 2 := by rw [pow_mul]
    rw [heq]
    exact hpow
  exact hPprime.mem_of_pow_mem 14 hpow'

theorem directOrbitGalois_distinct_prime_address
    {base : Ideal ℤ} {P Q : Ideal O}
    (hPprime : P.IsPrime) (hQprime : Q.IsPrime)
    (hPover : P.LiesOver base) (hQover : Q.LiesOver base)
    (hneq : P ≠ Q) :
    Q = directOrbitGaloisSigma • P ∨
      Q = directOrbitGaloisSigma ^ 2 • P := by
  classical
  let : P.IsPrime := hPprime
  let : Q.IsPrime := hQprime
  let : P.LiesOver base := hPover
  let : Q.LiesOver base := hQover
  obtain ⟨g, hg⟩ :=
    Algebra.IsInvariant.exists_smul_of_under_eq ℤ O (Gal(Field / ℚ)) P Q
      (hPover.over.symm.trans hQover.over)
  rcases directOrbitGaloisSigma_element_eq g with h | h | h
  · have hPQ : Q = P := by simpa [h] using hg
    exact (hneq hPQ.symm).elim
  · exact Or.inl (h ▸ hg)
  · exact Or.inr (h ▸ hg)

theorem directOrbit_two_gap_primes_imp_all_gap
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    {base : Ideal ℤ}
    (t : DirectOrbitSquareRefinementPacket p)
    {P Q : Ideal O} (hPprime : P.IsPrime) (hQprime : Q.IsPrime)
    (hPover : P.LiesOver base) (hQover : Q.LiesOver base)
    (hPgap : gapSquareIdeal t ≤ P) (hQgap : gapSquareIdeal t ≤ Q)
    (hneq : P ≠ Q) :
    ∀ {R : Ideal O}, R.IsPrime → R.LiesOver base → gapSquareIdeal t ≤ R := by
  have hP0 : modelEquivRingOfIntegers t.gapSquareRoot ∈ P := by
    exact (Ideal.span_singleton_le_iff_mem P).mp hPgap
  have hQ0 : modelEquivRingOfIntegers t.gapSquareRoot ∈ Q := by
    exact (Ideal.span_singleton_le_iff_mem Q).mp hQgap
  intro R hRprime hRover
  have hgap_of_all
      {T : Ideal O} (hT0 : modelEquivRingOfIntegers t.gapSquareRoot ∈ T) :
      gapSquareIdeal t ≤ T := by
    exact (Ideal.span_singleton_le_iff_mem T).mpr hT0
  rcases directOrbitGalois_distinct_prime_address
      hPprime hQprime hPover hQover hneq with hcase | hcase
  · have hQ1 :
        modelEquivRingOfIntegers (rotateEquiv t.gapSquareRoot) ∈ Q := by
      rw [hcase]
      exact (directOrbitGaloisSigma_model_rotate_mem_iff P
        t.gapSquareRoot).mpr hP0
    have hQ2 := directOrbit_two_rotated_gap_roots_mem_imp_all_three_mem
      t Q hQprime hQ0 hQ1
    by_cases hRQ : R = Q
    · exact hRQ ▸ hgap_of_all hQ0
    · rcases directOrbitGalois_distinct_prime_address
        hQprime hRprime hQover hRover (fun h => hRQ h.symm) with hRQcase | hRQcase
      · rw [hRQcase]
        have hQroot := (directOrbitGaloisSigma_model_rotate_mem_iff Q
          (rotateEquiv (rotateEquiv t.gapSquareRoot))).mpr hQ2
        rw [SevenRealCubicInt.rotateEquiv_three] at hQroot
        exact hgap_of_all hQroot
      · rw [hRQcase]
        exact hgap_of_all ((directOrbitGaloisSigma_sq_model_mem_iff Q
          t.gapSquareRoot).mpr hQ1)
  · have hP1 :
        modelEquivRingOfIntegers (rotateEquiv t.gapSquareRoot) ∈ P := by
      rw [hcase] at hQ0
      exact (directOrbitGaloisSigma_sq_model_mem_iff P
        t.gapSquareRoot).mp hQ0
    have hP2 := directOrbit_two_rotated_gap_roots_mem_imp_all_three_mem
      t P hPprime hP0 hP1
    by_cases hRP : R = P
    · exact hRP ▸ hgap_of_all hP0
    · rcases directOrbitGalois_distinct_prime_address
        hPprime hRprime hPover hRover (fun h => hRP h.symm) with hRPcase | hRPcase
      · rw [hRPcase]
        have hProot := (directOrbitGaloisSigma_model_rotate_mem_iff P
          (rotateEquiv (rotateEquiv t.gapSquareRoot))).mpr hP2
        rw [SevenRealCubicInt.rotateEquiv_three] at hProot
        exact hgap_of_all hProot
      · rw [hRPcase]
        exact hgap_of_all ((directOrbitGaloisSigma_sq_model_mem_iff P
          t.gapSquareRoot).mpr hP1)

private theorem directOrbit_common_prime_gap_set_singleton
    {x y z q : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p)
    (hq : q.Prime)
    (hqR : q ∣ Int.natAbs (norm t.gapSquareRoot))
    (hqS : q ∣ Int.natAbs (norm t.quotientSquareRoot)) :
    ∃ P0 : Ideal O,
      {P | P ∈ Ideal.primesOver (Ideal.span {(q : ℤ)}) O ∧
        gapSquareIdeal t ≤ P} = {P0} := by
  obtain ⟨P, Q, hPmax, hQmax, hPunder, hQunder, hPover, hQover,
      hPdiv, hQdiv, hne⟩ :=
    directOrbitSquareRefinement_exists_distinct_prime_ideals t hq hqR hqS
  have hPmem : P ∈ Ideal.primesOver (Ideal.span {(q : ℤ)}) O :=
    ⟨hPmax.isPrime, hPover⟩
  have hQmem : Q ∈ Ideal.primesOver (Ideal.span {(q : ℤ)}) O :=
    ⟨hQmax.isPrime, hQover⟩
  have hPgap : gapSquareIdeal t ≤ P := by
    apply (Ideal.span_singleton_le_iff_mem P).mpr
    exact directOrbitSquareRefinement_mem_of_principal_dvd hPdiv
  have hQquot : quotientSquareIdeal t ≤ Q := by
    apply (Ideal.span_singleton_le_iff_mem Q).mpr
    exact directOrbitSquareRefinement_mem_of_principal_dvd hQdiv
  have hAtMost : ∀ {A B : Ideal O},
      A ∈ Ideal.primesOver (Ideal.span {(q : ℤ)}) O →
      B ∈ Ideal.primesOver (Ideal.span {(q : ℤ)}) O →
      gapSquareIdeal t ≤ A → gapSquareIdeal t ≤ B → A = B := by
    intro A B hAmem hBmem hAgap hBgap
    by_contra hAB
    have hall : ∀ {R : Ideal O}, R.IsPrime →
        R.LiesOver (Ideal.span {(q : ℤ)}) → gapSquareIdeal t ≤ R :=
      directOrbit_two_gap_primes_imp_all_gap t
        hAmem.1 hBmem.1 hAmem.2 hBmem.2 hAgap hBgap hAB
    have hQall := hall hQmem.1 hQmem.2
    have hx := directOrbitSquareRefinement_prime_ideal_allocation_xor
      t hq hqR hqS Q hQmem.1 hQmem.2
    rcases hx with ⟨hgapQ, hnotquotQ⟩ | ⟨hquotQ, hnotgapQ⟩
    · exact (hnotquotQ hQquot).elim
    · exact (hnotgapQ hQall).elim
  refine ⟨P, ?_⟩
  ext A
  constructor
  · intro hA
    have hAP : A = P := hAtMost hA.1 hPmem hA.2 hPgap
    simp [hAP]
  · intro hA
    have hAP : A = P := by simpa using hA
    subst A
    exact ⟨hPmem, hPgap⟩

theorem directOrbitSquareRefinement_common_prime_gap_ncard
    {x y z q : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p)
    (hq : q.Prime)
    (hqR : q ∣ Int.natAbs (norm t.gapSquareRoot))
    (hqS : q ∣ Int.natAbs (norm t.quotientSquareRoot)) :
    {P ∈ Ideal.primesOver (Ideal.span {(q : ℤ)}) O |
      gapSquareIdeal t ≤ P}.ncard = 1 := by
  obtain ⟨P, hP⟩ := directOrbit_common_prime_gap_set_singleton
    t hq hqR hqS
  rw [hP, Set.ncard_singleton]

theorem directOrbitSquareRefinement_common_prime_quotient_ncard
    {x y z q : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p)
    (hq : q.Prime)
    (hqR : q ∣ Int.natAbs (norm t.gapSquareRoot))
    (hqS : q ∣ Int.natAbs (norm t.quotientSquareRoot)) :
    {P ∈ Ideal.primesOver (Ideal.span {(q : ℤ)}) O |
      quotientSquareIdeal t ≤ P}.ncard = 2 := by
  let S : Set (Ideal O) :=
    {P | P ∈ Ideal.primesOver (Ideal.span {(q : ℤ)}) O}
  let G : Set (Ideal O) :=
    {P | P ∈ S ∧ gapSquareIdeal t ≤ P}
  let H : Set (Ideal O) :=
    {P | P ∈ S ∧ quotientSquareIdeal t ≤ P}
  have hqZ : Prime (q : ℤ) := by
    exact Int.prime_iff_natAbs_prime.mpr (by simpa using hq)
  let base : Ideal ℤ := Ideal.span {(q : ℤ)}
  let : base.IsPrime := by
    dsimp [base]
    exact (Ideal.span_singleton_prime (by
      exact Int.ofNat_ne_zero.mpr (Nat.Prime.ne_zero hq))).mpr hqZ
  have hbaseMax : base.IsMaximal := by
    dsimp [base]
    exact (Ideal.span_singleton_prime (by
      exact Int.ofNat_ne_zero.mpr (Nat.Prime.ne_zero hq))).mpr hqZ |>.isMaximal
      (by simpa using hqZ.ne_zero)
  let : base.IsMaximal := hbaseMax
  have hSfinite : S.Finite := by
    dsimp [S, base]
    exact IsDedekindDomain.primesOver_finite _ _
  have hScard : S.ncard = 3 := by
    simpa [S, base] using
      (common_norm_prime_complete_split t hq hqR hqS).2.1
  obtain ⟨P, hG⟩ := directOrbit_common_prime_gap_set_singleton
    t hq hqR hqS
  have hG' : G = {P} := by
    simpa [G, S, base] using hG
  have hGcard : G.ncard = 1 := by
    rw [hG', Set.ncard_singleton]
  have hGsubset : G ⊆ S := by
    intro A hA
    exact hA.1
  have hGfinite : G.Finite := hSfinite.subset hGsubset
  have hH : H = S \ G := by
    ext A
    constructor
    · intro hA
      have hx := directOrbitSquareRefinement_prime_ideal_allocation_xor
        t hq hqR hqS A hA.1.1 hA.1.2
      rcases hx with ⟨hgap, hnotquot⟩ | ⟨hquot, hnotgap⟩
      · exact (hnotquot hA.2).elim
      · exact ⟨hA.1, fun hG => hnotgap hG.2⟩
    · intro hA
      have hnotgap : ¬ gapSquareIdeal t ≤ A := by
        intro hgap
        exact hA.2 ⟨hA.1, hgap⟩
      have hx := directOrbitSquareRefinement_prime_ideal_allocation_xor
        t hq hqR hqS A hA.1.1 hA.1.2
      rcases hx with ⟨hgap, hnotquot⟩ | ⟨hquot, hnotgap'⟩
      · exact (hnotgap hgap).elim
      · exact ⟨hA.1, hquot⟩
  change H.ncard = 2
  calc
    H.ncard = (S \ G).ncard := by rw [hH]
    _ = S.ncard - G.ncard := Set.ncard_sdiff hGsubset hGfinite
    _ = 2 := by simp [hScard, hGcard]

theorem directOrbitGalois_prime_orbit_eq_primesOver
    {base : Ideal ℤ} (P : Ideal O) (hPprime : P.IsPrime)
    (hPover : P.LiesOver base) :
    MulAction.orbit (Gal(Field / ℚ)) P = base.primesOver O := by
  let : P.IsPrime := hPprime
  let : P.LiesOver base := hPover
  exact Algebra.IsInvariant.orbit_eq_primesOver ℤ O (Gal(Field / ℚ)) base P

end SevenRealCubic
end
end DkMath.FLT.Seven
