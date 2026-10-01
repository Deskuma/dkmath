/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicSquareIdealSupport
import DkMath.FLT.Seven.SevenRealCubicAxisDrop
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Localization.FractionRing

namespace DkMath.FLT.Seven

noncomputable section

open scoped NumberField
open Polynomial

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 500000

namespace SevenRealCubic

abbrev O := 𝓞 Field

/-! ## The order-three field automorphism -/

noncomputable def fieldRotateRingEquiv : Field ≃+* Field :=
  IsFractionRing.ringEquivOfRingEquiv ringOfIntegersRotateEquiv

noncomputable def fieldRotateEquiv : Field ≃ₐ[ℚ] Field :=
  { fieldRotateRingEquiv with
    commutes' := by
      intro q
      simp [map_ratCast fieldRotateRingEquiv q] }

theorem fieldRotateEquiv_algebraMap_ringOfIntegers (x : O) :
    fieldRotateEquiv (algebraMap O Field x) =
      algebraMap O Field (ringOfIntegersRotateEquiv x) := by
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap
    ringOfIntegersRotateEquiv x

theorem fieldRotateEquiv_three (x : Field) :
    fieldRotateEquiv (fieldRotateEquiv (fieldRotateEquiv x)) = x := by
  let f : Field →+* Field :=
    fieldRotateEquiv.toRingEquiv.toRingHom.comp
      (fieldRotateEquiv.toRingEquiv.toRingHom.comp
        fieldRotateEquiv.toRingEquiv.toRingHom)
  have hf : f = RingHom.id Field := by
    apply IsFractionRing.ringHom_ext (A := O)
    intro y
    change fieldRotateEquiv (fieldRotateEquiv
      (fieldRotateEquiv (algebraMap O Field y))) = algebraMap O Field y
    rw [fieldRotateEquiv_algebraMap_ringOfIntegers,
      fieldRotateEquiv_algebraMap_ringOfIntegers,
      fieldRotateEquiv_algebraMap_ringOfIntegers,
      ringOfIntegersRotateEquiv_three]
  have hfx := congrArg (fun g : Field →+* Field => g x) hf
  simpa [f] using hfx

theorem fieldRotateEquiv_ne_one :
    fieldRotateEquiv ≠ (AlgEquiv.refl : Field ≃ₐ[ℚ] Field) := by
  intro h
  have hα : ringOfIntegersRotateEquiv alphaInteger = alphaInteger := by
    have := congrArg (fun e : Field ≃ₐ[ℚ] Field =>
      e (algebraMap O Field alphaInteger)) h
    simpa [fieldRotateEquiv_algebraMap_ringOfIntegers] using this
  rw [ringOfIntegersRotateEquiv_alpha] at hα
  have hα' := congrArg modelEquivRingOfIntegers.symm hα
  have htwo : modelEquivRingOfIntegers.symm (2 : O) =
      (2 : SevenRealCubicInt) := by
    apply modelEquivRingOfIntegers.injective
    simp
  rw [map_sub, map_pow, map_mul,
    modelEquivRingOfIntegers_symm_alphaInteger, htwo] at hα'
  have htwoInt : (2 : SevenRealCubicInt) = ⟨2, 0, 0⟩ := by rfl
  rw [htwoInt] at hα'
  have hsnd := congrArg SevenRealCubicInt.snd hα'
  norm_num [SevenRealCubicInt.alpha, pow_two, SevenRealCubicInt.mul,
    SevenRealCubicInt.fst_sub, SevenRealCubicInt.snd_sub,
    SevenRealCubicInt.thd_sub, SevenRealCubicInt.fst_mul,
    SevenRealCubicInt.snd_mul, SevenRealCubicInt.thd_mul] at hsnd

/-! ## The cubic roots and splitting -/

abbrev theta0 : Field := powerBasis.gen

abbrev theta1 : Field := fieldRotateEquiv theta0

abbrev theta2 : Field := fieldRotateEquiv theta1

theorem theta0_root :
    (polynomialQ.map (algebraMap ℚ Field)).IsRoot theta0 := by
  change (Polynomial.map (AdjoinRoot.of polynomialQ) polynomialQ).IsRoot
    (AdjoinRoot.root polynomialQ)
  exact AdjoinRoot.isRoot_root polynomialQ

theorem map_root (e : Field ≃ₐ[ℚ] Field) {x : Field}
    (hx : (polynomialQ.map (algebraMap ℚ Field)).IsRoot x) :
    (polynomialQ.map (algebraMap ℚ Field)).IsRoot (e x) := by
  rw [Polynomial.IsRoot.def] at hx ⊢
  have hm := Polynomial.IsRoot.map (f := e.toRingEquiv.toRingHom) hx
  rw [Polynomial.IsRoot.def] at hm
  rw [← Polynomial.eval₂_eq_eval_map] at hm ⊢
  rw [Polynomial.eval₂_map] at hm
  have he : e.toRingEquiv.toRingHom.comp (algebraMap ℚ Field) =
      algebraMap ℚ Field := by
    ext q
    exact e.commutes q
  rw [he] at hm
  exact hm

theorem theta1_root :
    (polynomialQ.map (algebraMap ℚ Field)).IsRoot theta1 :=
  map_root fieldRotateEquiv theta0_root

theorem theta2_root :
    (polynomialQ.map (algebraMap ℚ Field)).IsRoot theta2 :=
  map_root fieldRotateEquiv theta1_root

private theorem algEquiv_eq_refl_of_theta0_fix
    (e : Field ≃ₐ[ℚ] Field) (hfix : e theta0 = theta0) :
    e = (AlgEquiv.refl : Field ≃ₐ[ℚ] Field) := by
  apply AlgEquiv.ext
  intro x
  obtain ⟨p, rfl⟩ := powerBasis.exists_eq_aeval' x
  have he : (algebraMap ℚ Field).comp (RingHom.id ℚ) =
      e.toRingHom.comp (algebraMap ℚ Field) := by
    ext q
    exact (e.commutes q).symm
  have hm := Polynomial.map_aeval_eq_aeval_map
    (R := ℚ) (φ := RingHom.id ℚ) (ψ := e.toRingHom) he p theta0
  simp only [Polynomial.map_id] at hm
  have hfix' : e.toRingEquiv.toRingHom theta0 = theta0 := hfix
  rw [hfix'] at hm
  simpa using hm

theorem theta1_ne_theta0 : theta1 ≠ theta0 := by
  intro h
  apply fieldRotateEquiv_ne_one
  exact algEquiv_eq_refl_of_theta0_fix fieldRotateEquiv h

theorem theta2_ne_theta1 : theta2 ≠ theta1 := by
  intro h
  have h' := congrArg fieldRotateEquiv.symm h
  have hfix : fieldRotateEquiv theta0 = theta0 := by
    simpa [theta1, theta2] using h'
  exact theta1_ne_theta0 hfix

theorem theta2_ne_theta0 : theta2 ≠ theta0 := by
  intro h
  have h' := congrArg fieldRotateEquiv h
  have hfix : fieldRotateEquiv theta0 = theta0 := by
    simpa [theta2, fieldRotateEquiv_three] using h'.symm
  exact theta1_ne_theta0 hfix

theorem polynomialQ_map_splits :
    (polynomialQ.map (algebraMap ℚ Field)).Splits := by
  let p0 := polynomialQ.map (algebraMap ℚ Field)
  let l0 : Field[X] := Polynomial.X - Polynomial.C theta0
  have hp0 : p0.IsRoot theta0 := by
    simpa [p0] using theta0_root
  have hdiv0 : l0 ∣ p0 :=
    (Polynomial.dvd_iff_isRoot).mpr hp0
  obtain ⟨q1, hq1⟩ := hdiv0
  have hq1root : q1.IsRoot theta1 := by
    have hprod : p0.eval theta1 = 0 := by
      simpa [p0] using theta1_root
    rw [hq1, Polynomial.eval_mul] at hprod
    have hl0 : l0.eval theta1 ≠ 0 := by
      simpa [l0, sub_eq_zero] using theta1_ne_theta0
    exact (mul_eq_zero.mp hprod).resolve_left hl0
  have hq1monic : q1.Monic := by
    apply Polynomial.Monic.of_mul_monic_left
      (Polynomial.monic_X_sub_C theta0)
    rw [← hq1]
    exact polynomialQ_monic.map _
  have hq1deg : q1.natDegree = 2 := by
    have hdeg : p0.natDegree = 3 := by
      dsimp [p0]
      rw [Polynomial.natDegree_map]
      rw [polynomialQ,
        Polynomial.natDegree_map_eq_of_injective
          (algebraMap ℤ ℚ).injective_int]
      exact SevenRealCubicInt.eisensteinPolynomial_natDegree
    rw [hq1,
      Polynomial.natDegree_mul (Polynomial.monic_X_sub_C theta0).ne_zero
        hq1monic.ne_zero,
      Polynomial.natDegree_X_sub_C] at hdeg
    omega
  have hq1split : q1.Splits :=
    Polynomial.Splits.of_natDegree_eq_two hq1deg
      (Polynomial.IsRoot.def.mp hq1root)
  change p0.Splits
  rw [hq1]
  exact (Polynomial.Splits.X_sub_C theta0).mul hq1split

theorem theta0_root_aeval :
    (Polynomial.aeval theta0 polynomialQ) = 0 := by
  rw [Polynomial.aeval_def]
  change Polynomial.eval₂ (AdjoinRoot.of polynomialQ)
    (AdjoinRoot.root polynomialQ) polynomialQ = 0
  exact AdjoinRoot.eval₂_root polynomialQ

theorem theta0_mem_rootSet :
    theta0 ∈ polynomialQ.rootSet Field := by
  rw [Polynomial.mem_rootSet]
  exact ⟨polynomialQ_ne_zero, theta0_root_aeval⟩

noncomputable instance polynomialQ_isSplittingField :
    Polynomial.IsSplittingField ℚ Field polynomialQ where
  splits' := polynomialQ_map_splits
  adjoin_rootSet' := by
    apply le_antisymm le_top
    rw [← powerBasis.adjoin_gen_eq_top]
    apply Algebra.adjoin_le
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact Algebra.subset_adjoin theta0_mem_rootSet

noncomputable instance field_isNormal : Normal ℚ Field :=
  Normal.of_isSplittingField polynomialQ

noncomputable instance field_isGalois : IsGalois ℚ Field :=
  IsGalois.of_separable_splitting_field polynomialQ_irreducible.separable

/-! ## The unique prime above seven -/

def thetaI : O := modelEquivRingOfIntegers SevenRealCubicInt.eisensteinAxis

def P7 : Ideal O := Ideal.span {thetaI}

theorem thetaI_ne_zero : thetaI ≠ 0 := by
  intro h
  have h' := congrArg modelEquivRingOfIntegers.symm h
  apply SevenRealCubicInt.eisensteinAxis_prime.ne_zero
  simpa only [thetaI, RingEquiv.symm_apply_apply, map_zero] using h'

theorem P7_isPrime : P7.IsPrime := by
  have haxis : (Ideal.span
      ({SevenRealCubicInt.eisensteinAxis} : Set SevenRealCubicInt)).IsPrime :=
    (Ideal.span_singleton_prime
      SevenRealCubicInt.eisensteinAxis_prime.ne_zero).mpr
      SevenRealCubicInt.eisensteinAxis_prime
  have haxis0 : Ideal.span
      ({SevenRealCubicInt.eisensteinAxis} : Set SevenRealCubicInt) ≠ ⊥ := by
    intro h
    have hm := Ideal.mem_span_singleton_self SevenRealCubicInt.eisensteinAxis
    rw [h, Ideal.mem_bot] at hm
    exact SevenRealCubicInt.eisensteinAxis_prime.ne_zero hm
  have hmap := Ideal.map_prime_of_equiv modelEquivRingOfIntegers
    (Ideal.prime_of_isPrime haxis0 haxis) haxis0
  rw [Ideal.map_span] at hmap
  simpa [P7, thetaI] using
    (Ideal.isPrime_of_prime hmap)

theorem P7_isMaximal : P7.IsMaximal := by
  exact P7_isPrime.isMaximal (by
    intro h
    exact thetaI_ne_zero (by
      have := congrArg (fun I : Ideal O => thetaI ∈ I) h
      simpa [P7] using this))

private theorem P7_principal_factorization :
    Ideal.span {(7 : O)} = P7 ^ 3 := by
  let u : O := modelEquivRingOfIntegers SevenRealCubicInt.thetaSevenUnit
  have hu : IsUnit u := by
    exact IsUnit.map modelEquivRingOfIntegers
      SevenRealCubicInt.thetaSevenUnit_isUnit
  have h7 : (7 : O) = thetaI ^ 3 * u := by
    have h7' := congrArg modelEquivRingOfIntegers
      SevenRealCubicInt.seven_eq_eisensteinAxis_cube_mul_unit
    rw [map_ofNat] at h7'
    simpa [u, thetaI] using h7'
  rw [h7, Ideal.span_singleton_mul_right_unit hu]
  rw [← Ideal.span_singleton_pow]
  rfl

private theorem seven_base_isMaximal :
    (Ideal.span {(7 : ℤ)}).IsMaximal := by
  exact (Ideal.span_singleton_prime (show (7 : ℤ) ≠ 0 by norm_num)).mpr
    (by norm_num : Prime (7 : ℤ)) |>.isMaximal (by norm_num)

private theorem P7_liesOver_seven :
    P7.LiesOver (Ideal.span {(7 : ℤ)}) := by
  rw [Ideal.liesOver_iff]
  have hund_ne_top : Ideal.under ℤ P7 ≠ ⊤ := by
    intro h
    have hmem : (1 : O) ∈ P7 := by
      apply (Ideal.mem_under ℤ P7).mp
      rw [h]
      simp
    exact P7_isPrime.ne_top ((Ideal.eq_top_iff_one P7).mpr hmem)
  apply seven_base_isMaximal.eq_of_le hund_ne_top
  rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_under]
  let u : O := modelEquivRingOfIntegers SevenRealCubicInt.thetaSevenUnit
  have hu : IsUnit u := by
    exact IsUnit.map modelEquivRingOfIntegers
      SevenRealCubicInt.thetaSevenUnit_isUnit
  have h7 : (7 : O) = thetaI ^ 3 * u := by
    have h7' := congrArg modelEquivRingOfIntegers
      SevenRealCubicInt.seven_eq_eisensteinAxis_cube_mul_unit
    rw [map_ofNat] at h7'
    simpa [u, thetaI] using h7'
  have h7mem : (7 : O) ∈ P7 := by
    have htheta : thetaI ∈ P7 := by
      exact Ideal.mem_span_singleton_self _
    have htheta3 : thetaI ^ 3 ∈ P7 := by
      rw [show thetaI ^ 3 = thetaI * (thetaI * thetaI) by ring]
      exact P7.mul_mem_left _ (P7.mul_mem_left _ htheta)
    have hu := P7.mul_mem_right u htheta3
    simpa [h7] using hu
  simpa using h7mem

theorem seven_unique_prime_over
    (P : Ideal O) (hP : P.IsPrime)
    (hPover : P.LiesOver (Ideal.span {(7 : ℤ)})) : P = P7 := by
  have hP7div : P7 ^ 3 ≤ P := by
    rw [← P7_principal_factorization]
    rw [Ideal.span_singleton_le_iff_mem]
    have h7under : (7 : ℤ) ∈ Ideal.under ℤ P := by
      rw [← hPover.over]
      exact Ideal.mem_span_singleton_self _
    simpa using (Ideal.mem_under ℤ P).mp h7under
  have hle : P7 ≤ P := hP.le_of_pow_le hP7div
  exact P7_isMaximal.eq_of_le hP.ne_top hle |>.symm

theorem seven_primesOver_eq_singleton :
    Ideal.primesOver (Ideal.span {(7 : ℤ)}) O = {P7} := by
  ext P
  constructor
  · intro hP
    exact Set.mem_singleton_iff.mpr
      (seven_unique_prime_over P hP.1 hP.2)
  · intro hP
    rw [Set.mem_singleton_iff] at hP
    subst P
    exact ⟨P7_isPrime, P7_liesOver_seven⟩

theorem seven_primesOver_ncard :
    (Ideal.primesOver (Ideal.span {(7 : ℤ)}) O).ncard = 1 := by
  rw [seven_primesOver_eq_singleton, Set.ncard_singleton]

theorem seven_decomposition_product :
    (Ideal.primesOver (Ideal.span {(7 : ℤ)}) O).ncard *
        ((Ideal.span {(7 : ℤ)}).ramificationIdxIn O *
          (Ideal.span {(7 : ℤ)}).inertiaDegIn O) =
      Nat.card Gal(Field / ℚ) := by
  let : (Ideal.span {(7 : ℤ)}).IsPrime := by
    exact (Ideal.span_singleton_prime (show (7 : ℤ) ≠ 0 by norm_num)).mpr
      (by norm_num : Prime (7 : ℤ))
  exact Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (Ideal.span {(7 : ℤ)}) O Gal(Field / ℚ)

theorem galois_group_card_three : Nat.card Gal(Field / ℚ) = 3 := by
  rw [IsGalois.card_aut_eq_finrank, finrank_eq_three]

theorem common_norm_prime_complete_split
    {x y z q : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p)
    (hq : q.Prime)
    (hqR : q ∣ Int.natAbs (SevenRealCubicInt.norm t.gapSquareRoot))
    (hqS : q ∣ Int.natAbs (SevenRealCubicInt.norm t.quotientSquareRoot)) :
    q ≠ 7 ∧
      (Ideal.primesOver (Ideal.span {(q : ℤ)}) O).ncard = 3 ∧
      (Ideal.span {(q : ℤ)}).ramificationIdxIn O = 1 ∧
      (Ideal.span {(q : ℤ)}).inertiaDegIn O = 1 := by
  have hq7 : q ≠ 7 := by
    intro h
    subst q
    have htwo := directOrbitSquareRefinement_two_primes_over_common_norm_prime
      t hq hqR hqS
    have htwo' : 2 ≤
        (Ideal.primesOver (Ideal.span {(7 : ℤ)}) O).ncard := by
      simpa using htwo
    have hone' :
        (Ideal.primesOver (Ideal.span {(7 : ℤ)}) O).ncard = 1 :=
      seven_primesOver_ncard
    omega
  let base : Ideal ℤ := Ideal.span {(q : ℤ)}
  let : base.IsPrime := by
    dsimp [base]
    exact (Ideal.span_singleton_prime (by
      exact Int.ofNat_ne_zero.mpr (Nat.Prime.ne_zero hq))).mpr
      (Int.prime_iff_natAbs_prime.mpr (by simpa using hq))
  have hdecomp :=
    Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
      base O Gal(Field / ℚ)
  have hcard : Nat.card Gal(Field / ℚ) = 3 := galois_group_card_three
  have hlower : 2 ≤ (base.primesOver O).ncard := by
    dsimp [base]
    exact directOrbitSquareRefinement_two_primes_over_common_norm_prime
      t hq hqR hqS
  have hram : base.ramificationIdxIn O ≠ 0 :=
    Ideal.ramificationIdxIn_ne_zero (Gal(Field / ℚ))
  have hinertia : base.inertiaDegIn O ≠ 0 :=
    Ideal.inertiaDegIn_ne_zero (Gal(Field / ℚ))
  have hprod_pos : 0 < base.ramificationIdxIn O * base.inertiaDegIn O :=
    Nat.mul_pos (Nat.pos_of_ne_zero hram) (Nat.pos_of_ne_zero hinertia)
  have hnle : (base.primesOver O).ncard ≤ 3 := by
    have hle := Nat.le_mul_of_pos_right (base.primesOver O).ncard hprod_pos
    rw [hdecomp, hcard] at hle
    exact hle
  have hdecomp3 := hdecomp
  rw [hcard] at hdecomp3
  have hn : (base.primesOver O).ncard = 3 := by
    have hcases : (base.primesOver O).ncard = 2 ∨
        (base.primesOver O).ncard = 3 := by omega
    rcases hcases with htwo | hthree
    · rw [htwo] at hdecomp3
      omega
    · exact hthree
  have hei : base.ramificationIdxIn O * base.inertiaDegIn O = 1 := by
    rw [hn] at hdecomp
    rw [hcard] at hdecomp
    omega
  have hram_one : base.ramificationIdxIn O = 1 := by
    apply Nat.dvd_one.mp
    refine ⟨base.inertiaDegIn O, ?_⟩
    exact hei.symm
  have hinertia_one : base.inertiaDegIn O = 1 := by
    apply Nat.dvd_one.mp
    refine ⟨base.ramificationIdxIn O, ?_⟩
    simpa [Nat.mul_comm] using hei.symm
  refine ⟨hq7, ?_, hram_one, hinertia_one⟩
  simpa [base] using hn

end SevenRealCubic

/-! ## The prime seven cannot divide either current square-root norm -/

private theorem directOrbitSquareRefinement_not_seven_of_not_axis_dvd
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (_t : DirectOrbitSquareRefinementPacket p)
    {s : SevenRealCubicInt}
    (hs : ¬SevenRealCubicInt.eisensteinAxis ∣ s)
    (hnorm : 7 ∣ Int.natAbs (SevenRealCubicInt.norm s)) :
    False := by
  let I : Ideal SevenRealCubic.O :=
    Ideal.span ({SevenRealCubic.modelEquivRingOfIntegers s} :
      Set SevenRealCubic.O)
  have hI : 7 ∣ Ideal.absNorm I := by
    change 7 ∣ Ideal.absNorm
      (Ideal.span ({SevenRealCubic.modelEquivRingOfIntegers s} :
        Set SevenRealCubic.O))
    rw [directOrbitSquareRefinement_absNorm_span_model]
    exact hnorm
  obtain ⟨P, hPmax, hPunder, hPdiv⟩ :=
    Ideal.exists_isMaximal_dvd_of_dvd_absNorm' (by norm_num : Nat.Prime 7) I hI
  have hPeq : P = SevenRealCubic.P7 :=
    SevenRealCubic.seven_unique_prime_over P hPmax.isPrime
      ⟨hPunder.symm⟩
  have hmem := directOrbitSquareRefinement_mem_of_principal_dvd
    (x := s) hPdiv
  rw [hPeq] at hmem
  have hdvd : SevenRealCubic.thetaI ∣
      SevenRealCubic.modelEquivRingOfIntegers s :=
    Ideal.mem_span_singleton.mp hmem
  rcases hdvd with ⟨c, hc⟩
  apply hs
  refine ⟨SevenRealCubic.modelEquivRingOfIntegers.symm c, ?_⟩
  apply SevenRealCubic.modelEquivRingOfIntegers.injective
  rw [map_mul, SevenRealCubic.modelEquivRingOfIntegers.apply_symm_apply]
  exact hc

theorem directOrbitSquareRefinement_gapSquareRoot_not_seven_norm_dvd
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    ¬7 ∣ Int.natAbs (SevenRealCubicInt.norm t.gapSquareRoot) := by
  intro h
  exact directOrbitSquareRefinement_not_seven_of_not_axis_dvd t
    (directOrbitSquareRefinement_gapSquareRoot_not_axis_dvd t) h

theorem directOrbitSquareRefinement_quotientSquareRoot_not_seven_norm_dvd
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    ¬7 ∣ Int.natAbs (SevenRealCubicInt.norm t.quotientSquareRoot) := by
  intro h
  exact directOrbitSquareRefinement_not_seven_of_not_axis_dvd t
    (directOrbitSquareRefinement_quotientSquareRoot_not_axis_dvd t) h

end
end DkMath.FLT.Seven
