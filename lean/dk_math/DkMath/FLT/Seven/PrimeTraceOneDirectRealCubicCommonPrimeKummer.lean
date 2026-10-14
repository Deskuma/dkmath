/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicCanonicalCommonFactor
import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicResidueSupport

#print "file: DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicCommonPrimeKummer"

namespace DkMath.FLT.Seven

noncomputable section

open SevenRealCubicInt
open scoped BigOperators NumberField Pointwise

set_option linter.style.longLine false
set_option linter.style.setOption false

namespace SevenRealCubic

def directOrbitCommonPrimeEval (P : Ideal O) [P.IsPrime] :
    SevenRealCubicInt →+* P.ResidueField :=
  (algebraMap O P.ResidueField).comp
    modelEquivRingOfIntegers.toRingHom

def directOrbitCommonPrimeTwistRatio21
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) : SevenRealCubicIntˣ :=
  (-1) * directOrbitSquareTwistCoeff2 t *
    (directOrbitSquareTwistCoeff1 t)⁻¹

def directOrbitCommonPrimeKummerUnit : SevenRealCubicIntˣ :=
  alphaUnit * alphaAddOneUnit

theorem directOrbitCanonicalCommonFactor_c_eq_one_or_prime_dvd
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p) :
    h.c = 1 ∨ ∃ q, q.Prime ∧ q ∣ h.c := by
  by_cases hc : h.c = 1
  · exact Or.inl hc
  · obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hc
    exact Or.inr ⟨q, hq, hqdvd⟩

theorem directOrbitCanonicalCommonFactor_c_eq_one_arithmetic
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p) (hc : h.c = 1) :
    Int.natAbs (norm h.squareRefinement.gapSquareRoot) = h.u ^ 3 ∧
      Int.natAbs (norm h.squareRefinement.quotientSquareRoot) = h.v ^ 3 ∧
      h.squareRefinement.powerSplit.gapSplit.a = h.u * h.v ∧
      Nat.Coprime h.u h.v ∧ h.u ^ 5 < h.v := by
  exact ⟨by simpa [hc] using h.gapNorm_eq,
    by simpa [hc] using h.quotientNorm_eq,
    by simpa [hc] using h.unitPart_eq,
    h.u_v_coprime, by simpa [hc] using h.height⟩

theorem directOrbitCommonPrime_dvd_data
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p)
    (q : ℕ) (hqc : q ∣ h.c) :
    q ∣ Int.natAbs (norm h.squareRefinement.gapSquareRoot) ∧
      q ∣ Int.natAbs (norm h.squareRefinement.quotientSquareRoot) ∧
      q ∣ h.squareRefinement.powerSplit.gapSplit.a := by
  have hqg : q ∣ Nat.gcd
      (Int.natAbs (norm h.squareRefinement.gapSquareRoot))
      (Int.natAbs (norm h.squareRefinement.quotientSquareRoot)) := by
    rw [← h.c_eq_gcd]
    exact hqc
  have hqRS := Nat.dvd_gcd_iff.mp hqg
  exact ⟨hqRS.1, hqRS.2, dvd_trans hqc h.c_dvd_a⟩

theorem directOrbitCommonPrime_q_mod_seven
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p)
    (q : ℕ) (hq : q.Prime) (hqc : q ∣ h.c) :
    q % 7 = 1 ∨ q % 7 = 6 := by
  have hqg : q ∣ Nat.gcd
      (Int.natAbs (norm h.squareRefinement.gapSquareRoot))
      (Int.natAbs (norm h.squareRefinement.quotientSquareRoot)) := by
    rw [← h.c_eq_gcd]
    exact hqc
  have hqRS := Nat.dvd_gcd_iff.mp hqg
  exact common_norm_prime_mod_seven h.squareRefinement hq hqRS.1 hqRS.2

private theorem directOrbitCommonPrimeEval_mem_zero
    {P : Ideal O} [P.IsPrime] {a : SevenRealCubicInt}
    (ha : modelEquivRingOfIntegers a ∈ P) :
    directOrbitCommonPrimeEval P a = 0 := by
  have ha' : modelToRingOfIntegers a ∈ P := by
    simpa only [modelEquivRingOfIntegers_apply] using ha
  simp [directOrbitCommonPrimeEval,
    Ideal.algebraMap_residueField_eq_zero.mpr ha']

private theorem directOrbitCommonPrimeEval_mem_ne_zero
    {P : Ideal O} [P.IsPrime] {a : SevenRealCubicInt}
    (ha : modelEquivRingOfIntegers a ∉ P) :
    directOrbitCommonPrimeEval P a ≠ 0 := by
  intro hz
  apply ha
  have hz' : algebraMap O P.ResidueField
      (modelEquivRingOfIntegers a) = 0 := by
    simpa [directOrbitCommonPrimeEval] using hz
  exact Ideal.algebraMap_residueField_eq_zero.mp hz'

theorem directOrbitCommonPrimeKummerUnit_projectiveLog :
    projectiveLog (Additive.ofMul directOrbitCommonPrimeKummerUnit) = (0, 3) := by
  rw [directOrbitCommonPrimeKummerUnit, ofMul_mul, map_add,
    projectiveLog_alpha, projectiveLog_alphaAddOne]
  decide

theorem directOrbitCommonPrimeTwistRatio21_projectiveLog
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    projectiveLog (Additive.ofMul
      (directOrbitCommonPrimeTwistRatio21 t)) = (0, 3) := by
  have h := directOrbit_squareTwist_coeff_projectiveLog t
  rw [directOrbitCommonPrimeTwistRatio21, ofMul_mul, map_add,
    ofMul_mul, map_add, projectiveLog_neg_one, h.2.2,
    ofMul_inv, map_neg, h.2.1]
  decide

theorem directOrbitCommonPrime_global_seventh_correction
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    ∃ w : SevenRealCubicIntˣ,
      directOrbitCommonPrimeTwistRatio21 t =
        directOrbitCommonPrimeKummerUnit * w ^ 7 := by
  let delta := directOrbitCommonPrimeTwistRatio21 t *
    directOrbitCommonPrimeKummerUnit⁻¹
  have hdelta_log : projectiveLog (Additive.ofMul delta) = 0 := by
    rw [show delta = directOrbitCommonPrimeTwistRatio21 t *
        directOrbitCommonPrimeKummerUnit⁻¹ by rfl,
      ofMul_mul, map_add, ofMul_inv, map_neg,
      directOrbitCommonPrimeTwistRatio21_projectiveLog,
      directOrbitCommonPrimeKummerUnit_projectiveLog]
    decide
  obtain ⟨w, hw⟩ :=
    (unit_isSeventhPower_iff_projectiveLog_eq_zero delta).mpr hdelta_log
  refine ⟨w, ?_⟩
  dsimp [delta] at hw
  calc
    directOrbitCommonPrimeTwistRatio21 t =
        (directOrbitCommonPrimeTwistRatio21 t *
          directOrbitCommonPrimeKummerUnit⁻¹) *
            directOrbitCommonPrimeKummerUnit := by group
    _ = w ^ 7 * directOrbitCommonPrimeKummerUnit := by rw [hw]
    _ = directOrbitCommonPrimeKummerUnit * w ^ 7 := by ac_rfl

private theorem directOrbitCommonPrime_oriented_gap_prime_aux
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p)
    (h : DirectOrbitCanonicalCommonFactorPacket p)
    (ht : t = h.squareRefinement)
    (q : ℕ) (hq : q.Prime) (hqc : q ∣ h.c) :
    ∃ P : Ideal O,
      P.IsMaximal ∧
      P.LiesOver (Ideal.span {(q : ℤ)}) ∧
      modelEquivRingOfIntegers t.gapSquareRoot ∈ P ∧
      modelEquivRingOfIntegers (rotateEquiv t.gapSquareRoot) ∉ P ∧
      modelEquivRingOfIntegers
        (rotateEquiv (rotateEquiv t.gapSquareRoot)) ∉ P := by
  have hqg : q ∣ Nat.gcd (Int.natAbs (norm t.gapSquareRoot))
      (Int.natAbs (norm t.quotientSquareRoot)) := by
    rw [ht, ← h.c_eq_gcd]
    exact hqc
  have hqRS := Nat.dvd_gcd_iff.mp hqg
  have hqR := hqRS.1
  have hqS := hqRS.2
  let base : Ideal ℤ := Ideal.span {(q : ℤ)}
  have hqR' : q ∣ Ideal.absNorm (gapSquareIdeal t) := by
    change q ∣ Ideal.absNorm
      (Ideal.span ({modelEquivRingOfIntegers t.gapSquareRoot} : Set O))
    rw [directOrbitSquareRefinement_absNorm_span_model]
    exact hqR
  obtain ⟨P, hPmax, hPunder, hPdiv⟩ :=
    Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hq (gapSquareIdeal t) hqR'
  have hPover : P.LiesOver base := by
    refine ⟨?_⟩
    simpa [base] using hPunder.symm
  have hPgap : gapSquareIdeal t ≤ P := Ideal.dvd_iff_le.mp hPdiv
  have hPmem : P ∈
      {Q | Q ∈ Ideal.primesOver base O ∧ gapSquareIdeal t ≤ Q} := by
    exact ⟨⟨hPmax.isPrime, hPover⟩, hPgap⟩
  have hcardgap : {Q ∈ Ideal.primesOver base O | gapSquareIdeal t ≤ Q}.ncard = 1 := by
    simpa [base] using
      directOrbitSquareRefinement_common_prime_gap_ncard t hq hqR hqS
  obtain ⟨P0, hPset⟩ := Set.ncard_eq_one.mp hcardgap
  have hP_eq_P0 : P = P0 := by
    have h : P ∈ ({P0} : Set (Ideal O)) := by
      rw [← hPset]
      exact hPmem
    simpa using h
  have hunique : ∀ {Q : Ideal O},
      Q ∈ {Q | Q ∈ Ideal.primesOver base O ∧ gapSquareIdeal t ≤ Q} → Q = P := by
    intro Q hQ
    have hQ0 : Q ∈ ({P0} : Set (Ideal O)) := by
      rw [← hPset]
      exact hQ
    have hQ_eq_P0 : Q = P0 := by simpa using hQ0
    exact hQ_eq_P0.trans hP_eq_P0.symm
  have hr0 : modelEquivRingOfIntegers t.gapSquareRoot ∈ P :=
    (Ideal.span_singleton_le_iff_mem P).mp hPgap
  let : P.IsPrime := hPmax.isPrime
  let : P.LiesOver base := hPover
  have hrot1 : modelEquivRingOfIntegers (rotateEquiv t.gapSquareRoot) ∉ P := by
    intro hrot1
    let P' : Ideal O := directOrbitGaloisSigma ^ 2 • P
    have hr0' : modelEquivRingOfIntegers t.gapSquareRoot ∈ P' := by
      dsimp [P']
      exact (directOrbitGaloisSigma_sq_model_mem_iff P
        t.gapSquareRoot).mpr hrot1
    have hP'prime : P'.IsPrime := by
      dsimp [P']
      infer_instance
    have hP'over : P'.LiesOver base := by
      dsimp [P']
      infer_instance
    have hbase0 : base ≠ (⊥ : Ideal ℤ) := by
      simpa [base] using (Int.ofNat_ne_zero.mpr hq.ne_zero)
    have hP'ne : P' ≠ (⊥ : Ideal O) :=
      Ideal.ne_bot_of_liesOver_of_ne_bot hbase0 P'
    have hP'gap : gapSquareIdeal t ≤ P' :=
      (Ideal.span_singleton_le_iff_mem P').mpr hr0'
    have hP'mem : P' ∈
        {Q | Q ∈ Ideal.primesOver base O ∧ gapSquareIdeal t ≤ Q} := by
      exact ⟨⟨hP'prime, hP'over⟩, hP'gap⟩
    have hP'eq : P' = P := hunique hP'mem
    have hsqfix : directOrbitGaloisSigma ^ 2 • P = P := hP'eq
    have hfix : directOrbitGaloisSigma • P = P := by
      calc
        directOrbitGaloisSigma • P =
            directOrbitGaloisSigma • (directOrbitGaloisSigma ^ 2 • P) := by
              rw [hsqfix]
        _ = (directOrbitGaloisSigma * directOrbitGaloisSigma ^ 2) • P := by
              exact (mul_smul _ _ _).symm
        _ = directOrbitGaloisSigma ^ 3 • P := by
              have hpow : directOrbitGaloisSigma * directOrbitGaloisSigma ^ 2 =
                  directOrbitGaloisSigma ^ 3 := by group
              rw [hpow]
        _ = P := by rw [directOrbitGaloisSigma_three, one_smul]
    have horbit := directOrbitGalois_prime_orbit_eq_primesOver
      (base := base) P hPmax.isPrime hPover
    have hcard : (Ideal.primesOver base O).ncard = 3 := by
      simpa [base] using
        (common_norm_prime_complete_split t hq hqR hqS).2.1
    have hall : ∀ {Q : Ideal O}, Q ∈ Ideal.primesOver base O → Q = P := by
      intro Q hQ
      have hQorbit : Q ∈ MulAction.orbit (Gal(Field / ℚ)) P := by
        rw [horbit]
        exact hQ
      rcases hQorbit with ⟨g, hg⟩
      rcases directOrbitGaloisSigma_element_eq g with rfl | rfl | rfl
      · simpa using hg.symm
      · simpa [hfix] using hg.symm
      · simpa [hsqfix] using hg.symm
    have hsetall : Ideal.primesOver base O = {P} := by
      ext Q
      constructor
      · intro hQ
        simp [hall hQ]
      · intro hQ
        have hQP : Q = P := by simpa using hQ
        subst Q
        exact ⟨hPmax.isPrime, hPover⟩
    rw [hsetall] at hcard
    simp at hcard
  have hrot2 : modelEquivRingOfIntegers
      (rotateEquiv (rotateEquiv t.gapSquareRoot)) ∉ P := by
    intro hrot2
    let P' : Ideal O := directOrbitGaloisSigma • P
    have hr0' : modelEquivRingOfIntegers t.gapSquareRoot ∈ P' := by
      change modelEquivRingOfIntegers t.gapSquareRoot ∈
        directOrbitGaloisSigma • P
      simpa only [SevenRealCubicInt.rotateEquiv_three] using
        (directOrbitGaloisSigma_model_rotate_mem_iff P
          (rotateEquiv (rotateEquiv t.gapSquareRoot))).mpr hrot2
    have hP'prime : P'.IsPrime := by
      dsimp [P']
      infer_instance
    have hP'over : P'.LiesOver base := by
      dsimp [P']
      infer_instance
    have hP'gap : gapSquareIdeal t ≤ P' :=
      (Ideal.span_singleton_le_iff_mem P').mpr hr0'
    have hP'mem : P' ∈
        {Q | Q ∈ Ideal.primesOver base O ∧ gapSquareIdeal t ≤ Q} := by
      exact ⟨⟨hP'prime, hP'over⟩, hP'gap⟩
    have hP'eq : P' = P := hunique hP'mem
    have hfix : directOrbitGaloisSigma • P = P := hP'eq
    have hsqfix : directOrbitGaloisSigma ^ 2 • P = P := by
      calc
        directOrbitGaloisSigma ^ 2 • P =
            directOrbitGaloisSigma • (directOrbitGaloisSigma • P) := by
              rw [pow_two, mul_smul]
        _ = P := by simp [hfix]
    have horbit := directOrbitGalois_prime_orbit_eq_primesOver
      (base := base) P hPmax.isPrime hPover
    have hcard : (Ideal.primesOver base O).ncard = 3 := by
      simpa [base] using
        (common_norm_prime_complete_split t hq hqR hqS).2.1
    have hall : ∀ {Q : Ideal O}, Q ∈ Ideal.primesOver base O → Q = P := by
      intro Q hQ
      have hQorbit : Q ∈ MulAction.orbit (Gal(Field / ℚ)) P := by
        rw [horbit]
        exact hQ
      rcases hQorbit with ⟨g, hg⟩
      rcases directOrbitGaloisSigma_element_eq g with rfl | rfl | rfl
      · simpa using hg.symm
      · simpa [hfix] using hg.symm
      · simpa [hsqfix] using hg.symm
    have hsetall : Ideal.primesOver base O = {P} := by
      ext Q
      constructor
      · intro hQ
        simp [hall hQ]
      · intro hQ
        have hQP : Q = P := by simpa using hQ
        subst Q
        exact ⟨hPmax.isPrime, hPover⟩
    rw [hsetall] at hcard
    simp at hcard
  exact ⟨P, hPmax, hPover, hr0, hrot1, hrot2⟩

theorem directOrbitCommonPrime_oriented_gap_prime
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p)
    (q : ℕ) (hq : q.Prime) (hqc : q ∣ h.c) :
    ∃ P : Ideal O,
      P.IsMaximal ∧
      P.LiesOver (Ideal.span {(q : ℤ)}) ∧
      modelEquivRingOfIntegers h.squareRefinement.gapSquareRoot ∈ P ∧
      modelEquivRingOfIntegers
        (rotateEquiv h.squareRefinement.gapSquareRoot) ∉ P ∧
      modelEquivRingOfIntegers
        (rotateEquiv (rotateEquiv h.squareRefinement.gapSquareRoot)) ∉ P := by
  simpa using directOrbitCommonPrime_oriented_gap_prime_aux
    h.squareRefinement h rfl q hq hqc

theorem directOrbitCommonPrime_fourteen_power_ratio
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p)
    {P : Ideal O} (hPprime : P.IsPrime)
    (hr0 : modelEquivRingOfIntegers t.gapSquareRoot ∈ P)
    (hr1 : modelEquivRingOfIntegers (rotateEquiv t.gapSquareRoot) ∉ P)
    (hr2 : modelEquivRingOfIntegers
      (rotateEquiv (rotateEquiv t.gapSquareRoot)) ∉ P) :
    ∃ y : P.ResidueField, y ≠ 0 ∧
      y ^ 14 = directOrbitCommonPrimeEval P
        (directOrbitCommonPrimeTwistRatio21 t : SevenRealCubicInt) := by
  let : P.IsPrime := hPprime
  let evalP := directOrbitCommonPrimeEval P
  let r0 : P.ResidueField := evalP t.gapSquareRoot
  let r1 : P.ResidueField := evalP (rotateEquiv t.gapSquareRoot)
  let r2 : P.ResidueField := evalP
    (rotateEquiv (rotateEquiv t.gapSquareRoot))
  let c0 : P.ResidueField := evalP
    (directOrbitSquareTwistCoeff0 t : SevenRealCubicInt)
  let c1 : P.ResidueField := evalP
    (directOrbitSquareTwistCoeff1 t : SevenRealCubicInt)
  let c2 : P.ResidueField := evalP
    (directOrbitSquareTwistCoeff2 t : SevenRealCubicInt)
  have hr0z : r0 = 0 := directOrbitCommonPrimeEval_mem_zero hr0
  have hr1z : r1 ≠ 0 := directOrbitCommonPrimeEval_mem_ne_zero hr1
  have hr2z : r2 ≠ 0 := directOrbitCommonPrimeEval_mem_ne_zero hr2
  have hc1 : c1 ≠ 0 := by
    dsimp [c1]
    exact (IsUnit.map evalP (directOrbitSquareTwistCoeff1 t).isUnit).ne_zero
  have hEq : c0 * r0 ^ 14 + c1 * r1 ^ 14 + c2 * r2 ^ 14 = 0 := by
    have h := congrArg evalP (directOrbit_squareTwist_twisted_eq t)
    have h' : c0 * (r0 ^ 7) ^ 2 + c1 * (r1 ^ 7) ^ 2 +
        c2 * (r2 ^ 7) ^ 2 = 0 := by
      simpa only [c0, c1, c2, r0, r1, r2, map_add, map_mul, map_pow,
        Units.val_mul, Units.val_pow_eq_pow_val, map_zero] using h
    convert h' using 1
    simp only [show (14 : ℕ) = 7 * 2 by norm_num, pow_mul]
  let y : P.ResidueField := r1 * r2⁻¹
  have hy : y ≠ 0 := mul_ne_zero hr1z (inv_ne_zero hr2z)
  have hratio : y ^ 14 = (-1) * c2 * c1⁻¹ := by
    dsimp [y]
    rw [mul_pow, inv_pow]
    rw [hr0z] at hEq
    norm_num at hEq
    have hr2pow : r2 ^ 14 ≠ 0 := pow_ne_zero _ hr2z
    field_simp [hr2pow, hc1]
    linear_combination hEq
  refine ⟨y, hy, ?_⟩
  rw [hratio]
  have heval_inv (u : SevenRealCubicIntˣ) :
      evalP ((u⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt) =
        (evalP (u : SevenRealCubicInt))⁻¹ := by
    apply mul_left_cancel₀ (IsUnit.map evalP u.isUnit).ne_zero
    calc
      evalP (u : SevenRealCubicInt) *
          evalP ((u⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt) = 1 := by
        rw [← map_mul]
        simp
      _ = evalP (u : SevenRealCubicInt) *
          (evalP (u : SevenRealCubicInt))⁻¹ := by
        exact (mul_inv_cancel₀ (IsUnit.map evalP u.isUnit).ne_zero).symm
  have hratio_eval :
      evalP (directOrbitCommonPrimeTwistRatio21 t : SevenRealCubicInt) =
        (-1) * c2 * c1⁻¹ := by
    change evalP ((-1 : SevenRealCubicInt) *
      (directOrbitSquareTwistCoeff2 t : SevenRealCubicInt) *
      (((directOrbitSquareTwistCoeff1 t)⁻¹ : SevenRealCubicIntˣ) :
        SevenRealCubicInt)) = _
    rw [map_mul, map_mul, map_neg, heval_inv]
    simp [c1, c2]
  exact hratio_eval.symm

theorem directOrbitCommonPrime_kummer_residue_condition
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p)
    {P : Ideal O} (hPprime : P.IsPrime)
    (h14 : ∃ y : P.ResidueField, y ≠ 0 ∧
      y ^ 14 = directOrbitCommonPrimeEval P
        (directOrbitCommonPrimeTwistRatio21 t : SevenRealCubicInt)) :
    ∃ z : P.ResidueField, z ≠ 0 ∧
      z ^ 7 = directOrbitCommonPrimeEval P
        (directOrbitCommonPrimeKummerUnit : SevenRealCubicInt) := by
  let : P.IsPrime := hPprime
  obtain ⟨y, hy, hy14⟩ := h14
  obtain ⟨w, hw⟩ := directOrbitCommonPrime_global_seventh_correction t
  let evalP := directOrbitCommonPrimeEval P
  let ew : P.ResidueField := evalP (w : SevenRealCubicInt)
  let ec : P.ResidueField := evalP
    (directOrbitCommonPrimeKummerUnit : SevenRealCubicInt)
  have hew : ew ≠ 0 := by
    dsimp [ew]
    exact (IsUnit.map evalP w.isUnit).ne_zero
  have hwP : evalP
      (directOrbitCommonPrimeTwistRatio21 t : SevenRealCubicInt) =
      ec * ew ^ 7 := by
    have h := congrArg (fun u : SevenRealCubicIntˣ =>
      evalP (u : SevenRealCubicInt)) hw
    simpa only [ec, ew, map_mul, map_pow,
      Units.val_mul, Units.val_pow_eq_pow_val] using h
  have hpow : (y ^ 2) ^ 7 = ec * ew ^ 7 := by
    calc
      (y ^ 2) ^ 7 = y ^ (2 * 7) := by
        exact (pow_mul y 2 7).symm
      _ = y ^ 14 := by norm_num
      _ = evalP (directOrbitCommonPrimeTwistRatio21 t : SevenRealCubicInt) := hy14
      _ = ec * ew ^ 7 := hwP
  have hpow14 : y ^ 14 = ec * ew ^ 7 := by
    calc
      y ^ 14 = (y ^ 2) ^ 7 := by
        rw [show (14 : ℕ) = 2 * 7 by norm_num, pow_mul]
      _ = ec * ew ^ 7 := hpow
  let z : P.ResidueField := y ^ 2 * ew⁻¹
  have hz : z ≠ 0 := mul_ne_zero (pow_ne_zero _ hy) (inv_ne_zero hew)
  refine ⟨z, hz, ?_⟩
  dsimp [z]
  rw [mul_pow]
  field_simp [hew]
  simpa [mul_comm] using hpow14

theorem directOrbitCommonPrime_kummer_beta_form
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p)
    {P : Ideal O} (hPprime : P.IsPrime)
    (h14 : ∃ y : P.ResidueField, y ≠ 0 ∧
      y ^ 14 = directOrbitCommonPrimeEval P
        (directOrbitCommonPrimeTwistRatio21 t : SevenRealCubicInt)) :
    ∃ beta z : P.ResidueField,
      beta ^ 3 = 2 * beta ^ 2 + beta - 1 ∧
      z ≠ 0 ∧ z ^ 7 = beta * (1 + beta) := by
  let : P.IsPrime := hPprime
  obtain ⟨z, hz, hzk⟩ :=
    directOrbitCommonPrime_kummer_residue_condition t hPprime h14
  let evalP := directOrbitCommonPrimeEval P
  let beta : P.ResidueField := evalP alpha
  have hbeta : beta ^ 3 = 2 * beta ^ 2 + beta - 1 := by
    have h := congrArg evalP alpha_cube
    simpa only [beta, map_pow, map_mul, map_add, map_sub, map_one,
      map_ofNat] using h
  have hcommon : evalP
      (directOrbitCommonPrimeKummerUnit : SevenRealCubicInt) =
      beta * (1 + beta) := by
    simp [directOrbitCommonPrimeKummerUnit, beta, alphaUnit_val,
      alphaAddOneUnit_val, map_mul, map_add]
  refine ⟨beta, z, hbeta, hz, ?_⟩
  rw [← hcommon]
  exact hzk

end SevenRealCubic
end
end DkMath.FLT.Seven
