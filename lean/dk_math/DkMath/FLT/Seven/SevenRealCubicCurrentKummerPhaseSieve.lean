/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRealCubicCurrentOrientationRatio

#print "file: DkMath.FLT.Seven.SevenRealCubicCurrentKummerPhaseSieve"

namespace DkMath.FLT.Seven

noncomputable section

namespace SevenRealCubic

/-! # ※このモジュールは計算量、メモリ共に非常に重たい（ビルドパス済み）
このファイルへの追記をせずに、新規モジュールにて参照すること。
leanprover/lean4:v4.34.0
-/


set_option linter.style.longLine false
set_option maxRecDepth 100000
open SevenRealCubicInt

def phaseBeta {K : Type*} [_root_.Field K] (r : K) (n : ℕ) : K :=
  1 + r ^ n + (r ^ n)⁻¹

def phaseKummer {K : Type*} [_root_.Field K] (r : K) (n : ℕ) : K :=
  phaseBeta r n * (1 + phaseBeta r n)

section FieldPhase

variable {K : Type*} [_root_.Field K]

theorem phaseKummer_currentBeta
    {q : ℕ} [Fact q.Prime] (r : (ZMod q)ˣ) (n : ℕ) :
    phaseKummer (r : ZMod q) n =
      currentBeta r n * (1 + currentBeta r n) := by
  simp [phaseKummer, phaseBeta, currentBeta]

private theorem phaseKummer_identity_one
    (r : K) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) :
    phaseKummer r 2 * (1 + r) ^ 7 =
      - (phaseKummer r 1) ^ 2 := by
  have hr0 : r ≠ 0 := by
    intro h
    rw [h] at hr7
    norm_num at hr7
  have hsum : r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + r + 1 = 0 := by
    have hprod : (r - 1) *
        (r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + r + 1) = 0 := by
      linear_combination hr7
    exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hr1)
  have hr1i : r⁻¹ = r ^ 6 := by
    field_simp [hr0]
    rw [hr7]
  have hr2i : (r ^ 2)⁻¹ = r ^ 5 := by
    field_simp [hr0]
    rw [hr7]
  simp only [phaseKummer, phaseBeta, pow_one]
  rw [hr1i, hr2i]
  ring_nf
  have hp8 : r ^ 8 = r := by
    calc r ^ 8 = r ^ 7 * r := by ring
      _ = r := by rw [hr7, one_mul]
  have hp9 : r ^ 9 = r ^ 2 := by
    calc r ^ 9 = r ^ 7 * r ^ 2 := by ring
      _ = r ^ 2 := by rw [hr7, one_mul]
  have hp10 : r ^ 10 = r ^ 3 := by
    calc r ^ 10 = r ^ 7 * r ^ 3 := by ring
      _ = r ^ 3 := by rw [hr7, one_mul]
  have hp11 : r ^ 11 = r ^ 4 := by
    calc r ^ 11 = r ^ 7 * r ^ 4 := by ring
      _ = r ^ 4 := by rw [hr7, one_mul]
  have hp12 : r ^ 12 = r ^ 5 := by
    calc r ^ 12 = r ^ 7 * r ^ 5 := by ring
      _ = r ^ 5 := by rw [hr7, one_mul]
  have hp13 : r ^ 13 = r ^ 6 := by
    calc r ^ 13 = r ^ 7 * r ^ 6 := by ring
      _ = r ^ 6 := by rw [hr7, one_mul]
  have hp14 : r ^ 14 = 1 := by
    calc r ^ 14 = r ^ 7 * r ^ 7 := by ring
      _ = 1 := by simp [hr7]
  have hp15 : r ^ 15 = r := by
    calc r ^ 15 = r ^ 7 * r ^ 8 := by ring
      _ = r := by rw [hr7, hp8, one_mul]
  have hp16 : r ^ 16 = r ^ 2 := by
    calc r ^ 16 = r ^ 7 * r ^ 9 := by ring
      _ = r ^ 2 := by rw [hr7, hp9, one_mul]
  have hp17 : r ^ 17 = r ^ 3 := by
    calc r ^ 17 = r ^ 7 * r ^ 10 := by ring
      _ = r ^ 3 := by rw [hr7, hp10, one_mul]
  have hp18 : r ^ 18 = r ^ 4 := by
    calc r ^ 18 = r ^ 7 * r ^ 11 := by ring
      _ = r ^ 4 := by rw [hr7, hp11, one_mul]
  have hp19 : r ^ 19 = r ^ 5 := by
    calc r ^ 19 = r ^ 7 * r ^ 12 := by ring
      _ = r ^ 5 := by rw [hr7, hp12, one_mul]
  have hp24 : r ^ 24 = r ^ 3 := by
    calc r ^ 24 = r ^ 21 * r ^ 3 := by ring
      _ = r ^ 3 := by rw [show r ^ 21 = 1 by
        calc r ^ 21 = (r ^ 7) ^ 3 := by ring
          _ = 1 := by rw [hr7, one_pow], one_mul]
  simp only [hr7, hp8, hp9, hp10, hp11, hp12, hp13, hp14, hp15, hp16,
    hp17, hp18, hp19, hp24]
  linear_combination 240 * hsum

private theorem phaseKummer_four_eq_three
    (r : K) (hr7 : r ^ 7 = 1) :
    phaseKummer r 4 = phaseKummer r 3 := by
  have hr0 : r ≠ 0 := by
    intro h
    rw [h] at hr7
    norm_num at hr7
  have hr3i : (r ^ 3)⁻¹ = r ^ 4 := by
    field_simp [hr0]
    rw [hr7]
  have hr4i : (r ^ 4)⁻¹ = r ^ 3 := by
    field_simp [hr0]
    rw [hr7]
  simp only [phaseKummer, phaseBeta]
  rw [hr3i, hr4i]
  ring

theorem phaseKummer_identity_two
    (r : K) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) :
    phaseKummer r 3 * (1 + r ^ 2) ^ 7 =
      - (phaseKummer r 2) ^ 2 := by
  have hsq7 : (r ^ 2) ^ 7 = 1 := by
    calc (r ^ 2) ^ 7 = (r ^ 7) ^ 2 := by ring
      _ = 1 := by rw [hr7, one_pow]
  have hsq1 : r ^ 2 ≠ 1 := by
    intro hsq
    apply hr1
    calc r = r ^ 7 := by
          calc r = r * 1 := by simp
            _ = r * (r ^ 2) ^ 3 := by rw [hsq]; simp
            _ = r ^ 7 := by ring
      _ = 1 := hr7
  have h := phaseKummer_identity_one (r := r ^ 2) hsq7 hsq1
  have hleft : phaseKummer (r ^ 2) 2 = phaseKummer r 4 := by
    simp only [phaseKummer, phaseBeta]
    rw [show (r ^ 2) ^ 2 = r ^ 4 by ring]
  have hright : phaseKummer (r ^ 2) 1 = phaseKummer r 2 := by
    simp only [phaseKummer, phaseBeta]
    rw [show (r ^ 2) ^ 1 = r ^ 2 by simp]
  rw [hleft, hright] at h
  rw [phaseKummer_four_eq_three r hr7] at h
  simpa only [phaseKummer, phaseBeta, pow_one, pow_mul] using h

theorem phaseKummer_inv
    (r : K) (n : ℕ) :
    phaseKummer r⁻¹ n = phaseKummer r n := by
  simp [phaseKummer, phaseBeta, inv_pow]
  ring

theorem seventh_root_of_square_eq_seventh
    {x y : K} (hx : x ≠ 0) (hxy : x ^ 2 = y ^ 7) :
    ∃ z : K, z ^ 7 = x := by
  refine ⟨y ^ 4 / x, ?_⟩
  field_simp [hx]
  calc
    y ^ 28 = (y ^ 7) ^ 4 := by ring
    _ = (x ^ 2) ^ 4 := by rw [hxy]
    _ = x ^ 8 := by ring

private theorem one_add_root_ne_zero
    (r : K) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) :
    1 + r ≠ 0 := by
  intro hz
  apply hr1
  have hrneg : r = -1 := by linear_combination hz
  rw [hrneg] at hr7
  rcases eq_or_ne (2 : K) 0 with h2 | h2
  · calc
      r = -1 := hrneg
      _ = 1 - 2 := by ring
      _ = 1 := by rw [h2]; ring
  · exfalso
    apply h2
    have hneg : (-1 : K) = 1 := by
      calc
        (-1 : K) = (-1) ^ 7 := by norm_num
        _ = 1 := hr7
    calc
      (2 : K) = 1 - (-1) := by ring
      _ = 0 := by rw [hneg]; ring

theorem phaseKummer_one_iff_two
    (r : K) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) :
    (∃ z : K, z ^ 7 = phaseKummer r 1) ↔
      (∃ z : K, z ^ 7 = phaseKummer r 2) := by
  constructor
  · rintro ⟨z, hz⟩
    have hfac := phaseKummer_identity_one r hr7 hr1
    have hfacne : 1 + r ≠ 0 := one_add_root_ne_zero r hr7 hr1
    refine ⟨-z ^ 2 / (1 + r), ?_⟩
    field_simp [hfacne]
    calc
      -(z ^ 14) = -(z ^ 7) ^ 2 := by ring
      _ = -(phaseKummer r 1) ^ 2 := by rw [hz]
      _ = (1 + r) ^ 7 * phaseKummer r 2 := by
        rw [← hfac]
        ring
  · rintro ⟨z, hz⟩
    have hfac := phaseKummer_identity_one r hr7 hr1
    by_cases hx : phaseKummer r 1 = 0
    · exact ⟨0, by simp [hx]⟩
    · have hsq : (phaseKummer r 1) ^ 2 =
          (-(z * (1 + r))) ^ 7 := by
        calc
          _ = -(phaseKummer r 2 * (1 + r) ^ 7) := by rw [hfac]; ring
          _ = -(z ^ 7 * (1 + r) ^ 7) := by rw [hz]
          _ = (-(z * (1 + r))) ^ 7 := by ring
      exact seventh_root_of_square_eq_seventh hx hsq

theorem phaseKummer_two_iff_three
    (r : K) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) :
    (∃ z : K, z ^ 7 = phaseKummer r 2) ↔
      (∃ z : K, z ^ 7 = phaseKummer r 3) := by
  have hsq7 : (r ^ 2) ^ 7 = 1 := by
    calc (r ^ 2) ^ 7 = (r ^ 7) ^ 2 := by ring
      _ = 1 := by rw [hr7, one_pow]
  have hsq1 : r ^ 2 ≠ 1 := by
    intro h
    apply hr1
    calc r = r ^ 7 := by
          calc r = r * 1 := by simp
            _ = r * (r ^ 2) ^ 3 := by rw [h]; simp
            _ = r ^ 7 := by ring
      _ = 1 := hr7
  have h12 := phaseKummer_one_iff_two (r := r ^ 2) hsq7 hsq1
  have h1 : phaseKummer (r ^ 2) 1 = phaseKummer r 2 := by
    simp only [phaseKummer, phaseBeta]
    rw [show (r ^ 2) ^ 1 = r ^ 2 by simp]
  have h2 : phaseKummer (r ^ 2) 2 = phaseKummer r 4 := by
    simp only [phaseKummer, phaseBeta]
    rw [show (r ^ 2) ^ 2 = r ^ 4 by ring]
  have h3 : phaseKummer r 4 = phaseKummer r 3 :=
    phaseKummer_four_eq_three r hr7
  constructor
  · rintro ⟨z, hz⟩
    have hz' : z ^ 7 = phaseKummer (r ^ 2) 1 := by
      rw [h1]
      exact hz
    obtain ⟨w, hw⟩ := h12.mp ⟨z, hz'⟩
    refine ⟨w, ?_⟩
    rw [h2, h3] at hw
    exact hw
  · rintro ⟨z, hz⟩
    have hz' : z ^ 7 = phaseKummer (r ^ 2) 2 := by
      rw [h2, h3]
      exact hz
    obtain ⟨w, hw⟩ := h12.mpr ⟨z, hz'⟩
    refine ⟨w, ?_⟩
    rw [h1] at hw
    exact hw

theorem currentOrientedGap_normalized_kummer_support
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ} [Fact q.Prime]
    (a : CurrentCommonPrimeResiduePacket h q)
    (b : CurrentOrientedGapPrimeTransport h q) :
    ∃ z : ZMod q, z ≠ 0 ∧
      z ^ 7 = phaseKummer (currentGapDelta a b : ZMod q) 1 := by
  have hrot1 : modelEquivRingOfIntegers
      (rotateEquiv h.squareRefinement.gapSquareRoot) ∉ b.P := by
    intro hm
    exact b.rotate_gap_ne_zero
      ((b.f0_zero_iff (rotateEquiv h.squareRefinement.gapSquareRoot)).mpr hm)
  have hrot2 : modelEquivRingOfIntegers
      (rotateEquiv (rotateEquiv h.squareRefinement.gapSquareRoot)) ∉ b.P := by
    intro hm
    exact b.rotate2_gap_ne_zero
      ((b.f0_zero_iff
        (rotateEquiv (rotateEquiv h.squareRefinement.gapSquareRoot))).mpr hm)
  obtain ⟨y, hy, hy14⟩ := directOrbitCommonPrime_fourteen_power_ratio
    h.squareRefinement b.P_prime b.gap_mem hrot1 hrot2
  obtain ⟨zP, hzP, hzP7⟩ := directOrbitCommonPrime_kummer_residue_condition
    h.squareRefinement b.P_prime ⟨y, hy, hy14⟩
  let z : ZMod q := b.evalEquiv zP
  have hz : z ≠ 0 := by
    intro hz0
    apply hzP
    apply b.evalEquiv.injective
    simpa [z] using hz0
  have hzk : z ^ 7 = b.f0
      (directOrbitCommonPrimeKummerUnit : SevenRealCubicInt) := by
    have heq := congrArg b.evalEquiv hzP7
    simpa [z, b.f0_formula, directOrbitCommonPrimeEval] using heq
  let beta0 : ZMod q := b.f0 alpha
  have hbeta : beta0 ^ 3 - 2 * beta0 ^ 2 - beta0 + 1 = 0 := by
    have hc := congrArg b.f0 alpha_cube
    have hc' : b.f0 alpha ^ 3 =
        2 * b.f0 alpha ^ 2 + b.f0 alpha - 1 := by
      simpa only [map_pow, map_mul, map_add, map_sub, map_one,
        map_ofNat] using hc
    dsimp [beta0]
    linear_combination hc'
  have hKform : b.f0
      (directOrbitCommonPrimeKummerUnit : SevenRealCubicInt) =
      beta0 * (1 + beta0) := by
    simp [directOrbitCommonPrimeKummerUnit, beta0, alphaUnit_val,
      alphaAddOneUnit_val, map_mul, map_add]
  obtain ⟨j, hj⟩ := current_phase_alignment
    (currentGapDelta a b) (currentGapDelta_pow_seven a b)
      (currentGapDelta_ne_one a b) hbeta
  have hphase : b.f0
      (directOrbitCommonPrimeKummerUnit : SevenRealCubicInt) =
      phaseKummer (currentGapDelta a b : ZMod q) (j.val + 1) := by
    rw [hKform, hj, phaseKummer_currentBeta]
  have hsupport : ∃ z : ZMod q,
      z ^ 7 = phaseKummer (currentGapDelta a b : ZMod q) 1 := by
    have hdelta7 : (currentGapDelta a b : ZMod q) ^ 7 = 1 := by
      simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
        congrArg Units.val (currentGapDelta_pow_seven a b)
    have hdelta1 : (currentGapDelta a b : ZMod q) ≠ 1 := by
      intro heq
      apply currentGapDelta_ne_one a b
      exact Units.ext heq
    have hjSupport : ∃ z : ZMod q,
        z ^ 7 = phaseKummer (currentGapDelta a b : ZMod q) (j.val + 1) :=
      ⟨z, hzk.trans hphase⟩
    fin_cases j
    · simpa using hjSupport
    · exact (phaseKummer_one_iff_two
        (currentGapDelta a b : ZMod q)
        hdelta7
        hdelta1).mpr (by simpa using hjSupport)
    · exact (phaseKummer_one_iff_two
        (currentGapDelta a b : ZMod q)
        hdelta7
        hdelta1).mpr
        ((phaseKummer_two_iff_three
          (currentGapDelta a b : ZMod q)
          hdelta7
          hdelta1).mpr (by simpa using hjSupport))
  obtain ⟨z, hz7⟩ := hsupport
  refine ⟨z, ?_, hz7⟩
  intro hz0
  have hzero : phaseKummer (currentGapDelta a b : ZMod q) 1 = 0 := by
    rw [← hz7, hz0]
    simp
  have hunit : b.f0
      (directOrbitCommonPrimeKummerUnit : SevenRealCubicInt) ≠ 0 :=
    (IsUnit.map b.f0 directOrbitCommonPrimeKummerUnit.isUnit).ne_zero
  have hdelta7 : (currentGapDelta a b : ZMod q) ^ 7 = 1 := by
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
      congrArg Units.val (currentGapDelta_pow_seven a b)
  have hdelta1 : (currentGapDelta a b : ZMod q) ≠ 1 := by
    intro heq
    apply currentGapDelta_ne_one a b
    exact Units.ext heq
  have hfac1 : 1 + (currentGapDelta a b : ZMod q) ≠ 0 :=
    one_add_root_ne_zero _ hdelta7 hdelta1
  have hdelta2 : ((currentGapDelta a b : ZMod q) ^ 2) ^ 7 = 1 := by
    calc
      ((currentGapDelta a b : ZMod q) ^ 2) ^ 7 =
          ((currentGapDelta a b : ZMod q) ^ 7) ^ 2 := by ring
      _ = 1 := by rw [hdelta7, one_pow]
  have hdelta2ne : (currentGapDelta a b : ZMod q) ^ 2 ≠ 1 := by
    intro heq
    have heq' : (currentGapDelta a b) ^ 2 = 1 := Units.ext heq
    have hdvd := orderOf_dvd_of_pow_eq_one heq'
    rw [currentGapDelta_orderOf a b] at hdvd
    norm_num at hdvd
  have hfac2 : 1 + (currentGapDelta a b : ZMod q) ^ 2 ≠ 0 :=
    one_add_root_ne_zero _ hdelta2 hdelta2ne
  have hzero2 : phaseKummer (currentGapDelta a b : ZMod q) 2 = 0 := by
    have hid := phaseKummer_identity_one
      (currentGapDelta a b : ZMod q) hdelta7 hdelta1
    rw [hzero] at hid
    have hid' : phaseKummer (currentGapDelta a b : ZMod q) 2 *
        (1 + (currentGapDelta a b : ZMod q)) ^ 7 = 0 := by
      simpa using hid
    exact (mul_eq_zero.mp hid').resolve_right (pow_ne_zero 7 hfac1)
  have hzero3 : phaseKummer (currentGapDelta a b : ZMod q) 3 = 0 := by
    have hid := phaseKummer_identity_two
      (currentGapDelta a b : ZMod q) hdelta7 hdelta1
    rw [hzero2] at hid
    have hid' : phaseKummer (currentGapDelta a b : ZMod q) 3 *
        (1 + (currentGapDelta a b : ZMod q) ^ 2) ^ 7 = 0 := by
      simpa using hid
    exact (mul_eq_zero.mp hid').resolve_right (pow_ne_zero 7 hfac2)
  have hKzero : b.f0
      (directOrbitCommonPrimeKummerUnit : SevenRealCubicInt) = 0 := by
    rw [hphase]
    fin_cases j
    · exact hzero
    · exact hzero2
    · exact hzero3
  exact hunit hKzero

def phaseKummerZMod (q : ℕ) (r : (ZMod q)ˣ) (n : ℕ) : ZMod q :=
  (1 + ((r ^ n : (ZMod q)ˣ) : ZMod q) +
      (((r ^ n : (ZMod q)ˣ)⁻¹ : (ZMod q)ˣ) : ZMod q)) *
    (1 + (1 + ((r ^ n : (ZMod q)ˣ) : ZMod q) +
      (((r ^ n : (ZMod q)ˣ)⁻¹ : (ZMod q)ˣ) : ZMod q)))

def SevenKummerCompatiblePrime (q : ℕ) : Prop :=
  q.Prime ∧ ∃ r : (ZMod q)ˣ,
    r ^ 7 = 1 ∧ r ≠ 1 ∧ ∃ z : ZMod q,
      z ≠ 0 ∧ z ^ 7 = phaseKummerZMod q r 1

theorem currentOrientedGap_sevenKummerCompatiblePrime
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ} [Fact q.Prime]
    (a : CurrentCommonPrimeResiduePacket h q)
    (b : CurrentOrientedGapPrimeTransport h q) :
    SevenKummerCompatiblePrime q := by
  refine ⟨a.q_prime, currentGapDelta a b,
    currentGapDelta_pow_seven a b, currentGapDelta_ne_one a b, ?_⟩
  obtain ⟨z, hz, hz7⟩ := currentOrientedGap_normalized_kummer_support a b
  refine ⟨z, hz, ?_⟩
  simpa only [phaseKummer, phaseBeta, phaseKummerZMod, pow_one,
    Units.val_inv_eq_inv_val] using hz7

theorem sevenKummerCompatiblePrime_not_29 :
    ¬ SevenKummerCompatiblePrime 29 := by
  unfold SevenKummerCompatiblePrime
  unfold phaseKummerZMod
  decide

set_option maxHeartbeats 2000000 in
-- The finite unit-group sieve is checked by kernel reduction.
theorem sevenKummerCompatiblePrime_not_43 :
    ¬ SevenKummerCompatiblePrime 43 := by
  unfold SevenKummerCompatiblePrime
  unfold phaseKummerZMod
  decide

set_option maxHeartbeats 2000000 in
-- The finite unit-group sieve is checked by kernel reduction.
theorem sevenKummerCompatiblePrime_not_71 :
    ¬ SevenKummerCompatiblePrime 71 := by
  unfold SevenKummerCompatiblePrime
  unfold phaseKummerZMod
  decide

set_option maxHeartbeats 2000000 in
-- The finite unit-group sieve is checked by kernel reduction.
theorem sevenKummerCompatiblePrime_not_113 :
    ¬ SevenKummerCompatiblePrime 113 := by
  unfold SevenKummerCompatiblePrime
  unfold phaseKummerZMod
  decide

set_option maxHeartbeats 2000000 in
-- The finite unit-group sieve is checked by kernel reduction.
theorem sevenKummerCompatiblePrime_not_127 :
    ¬ SevenKummerCompatiblePrime 127 := by
  unfold SevenKummerCompatiblePrime
  unfold phaseKummerZMod
  decide

set_option maxHeartbeats 2000000 in
-- The finite unit-group sieve is checked by kernel reduction.
theorem sevenKummerCompatiblePrime_not_197 :
    ¬ SevenKummerCompatiblePrime 197 := by
  unfold SevenKummerCompatiblePrime
  unfold phaseKummerZMod
  decide

set_option maxHeartbeats 2000000 in
-- The finite unit-group sieve is checked by kernel reduction.
theorem sevenKummerCompatiblePrime_not_211 :
    ¬ SevenKummerCompatiblePrime 211 := by
  unfold SevenKummerCompatiblePrime
  unfold phaseKummerZMod
  decide

set_option maxHeartbeats 2000000 in
-- The finite unit-group sieve is checked by kernel reduction.
theorem sevenKummerCompatiblePrime_not_239 :
    ¬ SevenKummerCompatiblePrime 239 := by
  unfold SevenKummerCompatiblePrime
  unfold phaseKummerZMod
  decide

set_option maxHeartbeats 2000000 in
-- The finite unit-group sieve is checked by kernel reduction.
theorem sevenKummerCompatiblePrime_not_281 :
    ¬ SevenKummerCompatiblePrime 281 := by
  unfold SevenKummerCompatiblePrime
  unfold phaseKummerZMod
  decide

set_option maxHeartbeats 2000000 in
-- The finite unit-group sieve is checked by kernel reduction.
theorem sevenKummerCompatiblePrime_not_337 :
    ¬ SevenKummerCompatiblePrime 337 := by
  unfold SevenKummerCompatiblePrime
  unfold phaseKummerZMod
  decide

theorem prime_mod_seven_one_lt_379_mem
    (q : ℕ) (hq : q.Prime) (hmod : q % 7 = 1) (hlt : q < 379) :
    q = 29 ∨ q = 43 ∨ q = 71 ∨ q = 113 ∨ q = 127 ∨
      q = 197 ∨ q = 211 ∨ q = 239 ∨ q = 281 ∨ q = 337 := by
  have hqle : q ≤ 378 := Nat.le_pred_of_lt hlt
  interval_cases q <;> try norm_num at hq <;> try norm_num at hmod <;> norm_num

theorem sevenKummerCompatiblePrime_ge_379
    {q : ℕ} (hq : q.Prime) (hmod : q % 7 = 1)
    (hqc : SevenKummerCompatiblePrime q) : 379 ≤ q := by
  by_contra hlt
  have hlt' : q < 379 := Nat.lt_of_not_ge hlt
  have hcases := prime_mod_seven_one_lt_379_mem q hq hmod hlt'
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (sevenKummerCompatiblePrime_not_29 hqc).elim
  · exact (sevenKummerCompatiblePrime_not_43 hqc).elim
  · exact (sevenKummerCompatiblePrime_not_71 hqc).elim
  · exact (sevenKummerCompatiblePrime_not_113 hqc).elim
  · exact (sevenKummerCompatiblePrime_not_127 hqc).elim
  · exact (sevenKummerCompatiblePrime_not_197 hqc).elim
  · exact (sevenKummerCompatiblePrime_not_211 hqc).elim
  · exact (sevenKummerCompatiblePrime_not_239 hqc).elim
  · exact (sevenKummerCompatiblePrime_not_281 hqc).elim
  · exact (sevenKummerCompatiblePrime_not_337 hqc).elim

theorem directOrbitCommonPrime_q_ge_379
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    {h : DirectOrbitCanonicalCommonFactorPacket p}
    (q : ℕ) (hq : q.Prime) (hqc : q ∣ h.c) : 379 ≤ q := by
  let : Fact q.Prime := ⟨hq⟩
  obtain ⟨a⟩ := currentCommonPrime_residuePacket h q hq hqc
  obtain ⟨b⟩ := currentOrientedGapPrimeTransport h q hq hqc
  have hcard : 7 ∣ q - 1 := by
    have hdvd : orderOf (currentGapDelta a b) ∣
        Fintype.card (ZMod q)ˣ := orderOf_dvd_card
    simpa [currentGapDelta_orderOf a b, Fintype.card_units] using hdvd
  have hmod' : (q - 1) % 7 = 0 := Nat.mod_eq_zero_of_dvd hcard
  have hqpos : 0 < q := hq.pos
  have hmod : q % 7 = 1 := by
    calc
      q % 7 = ((q - 1) + 1) % 7 := by omega
      _ = ((q - 1) % 7 + 1 % 7) % 7 := by rw [Nat.add_mod]
      _ = 1 := by norm_num [hmod']
  have hcompat := currentOrientedGap_sevenKummerCompatiblePrime a b
  exact sevenKummerCompatiblePrime_ge_379 hq hmod hcompat

theorem directOrbitCommonFactor_c_ge_379
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p) (hc : 1 < h.c) :
    379 ≤ h.c := by
  obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd (Nat.ne_of_gt hc)
  exact le_trans (directOrbitCommonPrime_q_ge_379 q hq hqdvd)
    (Nat.le_of_dvd (lt_trans Nat.zero_lt_one hc) hqdvd)

theorem directOrbitCommonFactor_height_ge_379
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p) (hc : 1 < h.c) :
    379 * h.u ^ 5 < h.v := by
  have hcle : 379 ≤ h.c := directOrbitCommonFactor_c_ge_379 h hc
  have hmul : 379 * h.u ^ 5 ≤ h.c * h.u ^ 5 :=
    Nat.mul_le_mul_right (h.u ^ 5) hcle
  exact lt_of_le_of_lt hmul h.height

end FieldPhase

end SevenRealCubic
end
end DkMath.FLT.Seven
