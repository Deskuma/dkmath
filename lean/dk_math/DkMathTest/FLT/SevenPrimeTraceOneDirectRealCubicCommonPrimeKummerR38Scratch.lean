import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicCanonicalCommonFactor
import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicResidueSupport

open DkMath.FLT.Seven
open DkMath.FLT.Seven.SevenRealCubicInt
open scoped BigOperators NumberField Pointwise

namespace DkMath.FLT.Seven.SevenRealCubic

noncomputable section

theorem r38_c_eq_one_or_prime_dvd
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p) :
    h.c = 1 ∨ ∃ q, q.Prime ∧ q ∣ h.c := by
  by_cases hc : h.c = 1
  · exact Or.inl hc
  · obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hc
    exact Or.inr ⟨q, hq, hqdvd⟩

theorem r38_c_eq_one_arithmetic
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

#check Set.ncard_eq_one
#check MulAction.mem_orbit
#check MulAction.orbit
#check MulAction.orbit_eq_univ
#print MulAction.orbit
#check Set.ncard_congr
#check Set.ncard_image_iff
#check Ideal.exists_isMaximal_dvd_of_dvd_absNorm'
#check Nat.Prime.factorization_pos_of_dvd
#check dvd_pow_self
#check dvd_pow
#check Ideal.dvd_iff_le

theorem r38_oriented_gap_prime
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
  have hqg : q ∣ Nat.gcd
      (Int.natAbs (norm t.gapSquareRoot))
      (Int.natAbs (norm t.quotientSquareRoot)) := by
    rw [ht, ← h.c_eq_gcd]
    exact hqc
  have hqRS := Nat.dvd_gcd_iff.mp hqg
  have hqR : q ∣ Int.natAbs (norm t.gapSquareRoot) := hqRS.1
  have hqS : q ∣ Int.natAbs (norm t.quotientSquareRoot) := hqRS.2
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

def r38_evalP (P : Ideal O) [P.IsPrime] :
    SevenRealCubicInt →+* P.ResidueField :=
  (algebraMap O P.ResidueField).comp
    SevenRealCubic.modelEquivRingOfIntegers.toRingHom

def r38_twistRatio21
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) : SevenRealCubicIntˣ :=
  (-1) * directOrbitSquareTwistCoeff2 t *
    (directOrbitSquareTwistCoeff1 t)⁻¹

theorem r38_evalP_mem_zero {P : Ideal O} [P.IsPrime]
    {a : SevenRealCubicInt}
    (ha : modelEquivRingOfIntegers a ∈ P) :
    r38_evalP P a = 0 := by
  have ha' : SevenRealCubic.modelToRingOfIntegers a ∈ P := by
    simpa only [SevenRealCubic.modelEquivRingOfIntegers_apply] using ha
  simp [r38_evalP, Ideal.algebraMap_residueField_eq_zero.mpr ha']

theorem r38_evalP_mem_ne_zero {P : Ideal O} [P.IsPrime]
    {a : SevenRealCubicInt}
    (ha : modelEquivRingOfIntegers a ∉ P) :
    r38_evalP P a ≠ 0 := by
  intro hz
  apply ha
  have hz' : algebraMap O P.ResidueField
      (modelEquivRingOfIntegers a) = 0 := by
    simpa [r38_evalP] using hz
  exact Ideal.algebraMap_residueField_eq_zero.mp hz'

theorem r38_fourteen_power_ratio
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
      y ^ 14 = r38_evalP P (r38_twistRatio21 t : SevenRealCubicInt) := by
  let : P.IsPrime := hPprime
  let evalP := r38_evalP P
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
  have hr0z : r0 = 0 := by
    exact r38_evalP_mem_zero hr0
  have hr1z : r1 ≠ 0 := by
    exact r38_evalP_mem_ne_zero hr1
  have hr2z : r2 ≠ 0 := by
    exact r38_evalP_mem_ne_zero hr2
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
  have hratio_eval : evalP (r38_twistRatio21 t : SevenRealCubicInt) =
      (-1) * c2 * c1⁻¹ := by
    change evalP ((-1 : SevenRealCubicInt) *
      (directOrbitSquareTwistCoeff2 t : SevenRealCubicInt) *
      (((directOrbitSquareTwistCoeff1 t)⁻¹ : SevenRealCubicIntˣ) :
        SevenRealCubicInt)) = _
    rw [map_mul, map_mul, map_neg, heval_inv]
    simp [c1, c2]
  exact hratio_eval.symm

def r38_commonKummerUnit : SevenRealCubicIntˣ :=
  alphaUnit * alphaAddOneUnit

theorem r38_commonKummerUnit_projectiveLog :
    projectiveLog (Additive.ofMul r38_commonKummerUnit) = (0, 3) := by
  rw [r38_commonKummerUnit, ofMul_mul, map_add,
    projectiveLog_alpha, projectiveLog_alphaAddOne]
  decide

theorem r38_twistRatio21_projectiveLog
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    projectiveLog (Additive.ofMul (r38_twistRatio21 t)) = (0, 3) := by
  have h := directOrbit_squareTwist_coeff_projectiveLog t
  rw [r38_twistRatio21, ofMul_mul, map_add, ofMul_mul, map_add,
    projectiveLog_neg_one, h.2.2, ofMul_inv, map_neg, h.2.1]
  decide

theorem r38_global_seventh_correction
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    ∃ w : SevenRealCubicIntˣ,
      r38_twistRatio21 t = r38_commonKummerUnit * w ^ 7 := by
  let delta := r38_twistRatio21 t * r38_commonKummerUnit⁻¹
  have hdelta_log : projectiveLog (Additive.ofMul delta) = 0 := by
    rw [show delta = r38_twistRatio21 t * r38_commonKummerUnit⁻¹ by rfl,
      ofMul_mul, map_add, ofMul_inv, map_neg,
      r38_twistRatio21_projectiveLog,
      r38_commonKummerUnit_projectiveLog]
    decide
  obtain ⟨w, hw⟩ :=
    (SevenRealCubic.unit_isSeventhPower_iff_projectiveLog_eq_zero delta).mpr
      hdelta_log
  refine ⟨w, ?_⟩
  dsimp [delta] at hw
  calc
    r38_twistRatio21 t =
        (r38_twistRatio21 t * r38_commonKummerUnit⁻¹) *
          r38_commonKummerUnit := by group
    _ = w ^ 7 * r38_commonKummerUnit := by rw [hw]
    _ = r38_commonKummerUnit * w ^ 7 := by ac_rfl

theorem r38_kummer_residue_condition
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p)
    {P : Ideal O} (hPprime : P.IsPrime)
    (h14 : ∃ y : P.ResidueField, y ≠ 0 ∧
      y ^ 14 = r38_evalP P (r38_twistRatio21 t : SevenRealCubicInt)) :
    ∃ z : P.ResidueField, z ≠ 0 ∧
      z ^ 7 = r38_evalP P (r38_commonKummerUnit : SevenRealCubicInt) := by
  let : P.IsPrime := hPprime
  obtain ⟨y, hy, hy14⟩ := h14
  obtain ⟨w, hw⟩ := r38_global_seventh_correction t
  let evalP := r38_evalP P
  let ew : P.ResidueField := evalP (w : SevenRealCubicInt)
  let ec : P.ResidueField := evalP
    (r38_commonKummerUnit : SevenRealCubicInt)
  have hew : ew ≠ 0 := by
    dsimp [ew]
    exact (IsUnit.map evalP w.isUnit).ne_zero
  have hwP : evalP (r38_twistRatio21 t : SevenRealCubicInt) =
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
      _ = evalP (r38_twistRatio21 t : SevenRealCubicInt) := hy14
      _ = ec * ew ^ 7 := hwP
  have hpow14 : y ^ 14 = ec * ew ^ 7 := by
    calc
      y ^ 14 = (y ^ 2) ^ 7 := by
        rw [show (14 : ℕ) = 2 * 7 by norm_num, pow_mul]
      _ = ec * ew ^ 7 := hpow
  let wres : P.ResidueField := y ^ 2 * ew⁻¹
  have hwres : wres ≠ 0 := mul_ne_zero (pow_ne_zero _ hy) (inv_ne_zero hew)
  refine ⟨wres, hwres, ?_⟩
  dsimp [wres]
  rw [mul_pow]
  field_simp [hew]
  simpa [mul_comm] using hpow14

theorem r38_kummer_beta_form
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p)
    {P : Ideal O} (hPprime : P.IsPrime)
    (h14 : ∃ y : P.ResidueField, y ≠ 0 ∧
      y ^ 14 = r38_evalP P (r38_twistRatio21 t : SevenRealCubicInt)) :
    ∃ beta z : P.ResidueField,
      beta ^ 3 = 2 * beta ^ 2 + beta - 1 ∧
      z ≠ 0 ∧ z ^ 7 = beta * (1 + beta) := by
  let : P.IsPrime := hPprime
  obtain ⟨z, hz, hzk⟩ := r38_kummer_residue_condition t hPprime h14
  let evalP := r38_evalP P
  let beta : P.ResidueField := evalP alpha
  have hbeta : beta ^ 3 = 2 * beta ^ 2 + beta - 1 := by
    have h := congrArg evalP alpha_cube
    simpa only [beta, map_pow, map_mul, map_add, map_sub, map_one,
      map_ofNat] using h
  have hcommon : evalP (r38_commonKummerUnit : SevenRealCubicInt) =
      beta * (1 + beta) := by
    simp [r38_commonKummerUnit, beta, alphaUnit_val, alphaAddOneUnit_val,
      map_mul, map_add]
  refine ⟨beta, z, hbeta, hz, ?_⟩
  rw [← hcommon]
  exact hzk

example : (4 : ZMod 29) ^ 3 = 2 * (4 : ZMod 29) ^ 2 + 4 - 1 := by
  decide

example : ¬ ∃ z : ZMod 29, z ^ 7 = (4 : ZMod 29) * (1 + 4) := by
  decide

example : (206 : ZMod 379) ^ 3 =
    2 * (206 : ZMod 379) ^ 2 + 206 - 1 := by
  decide

example : (29 : ZMod 379) ^ 7 = (206 : ZMod 379) * (1 + 206) := by
  decide

end
end DkMath.FLT.Seven.SevenRealCubic
