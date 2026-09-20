/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicTrivialCommonFactorDeepJet

#print "file: DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicTrivialCommonFactorPairedDeepJet"

namespace DkMath.FLT.Seven

noncomputable section

open SevenRealCubicInt
open scoped NumberField Pointwise

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 2000000

namespace SevenRealCubic

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-! ## R42 fixed unit and paired quotient model -/

def directOrbitPairedDeepJetY
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p)
    (xi : SevenRealCubicIntˣ) : SevenRealCubicIntˣ :=
  h.squareRefinement.powerSplit.quotientUnit *
    (h.squareRefinement.quotientSquareUnit * xi ^ 2) ^ 7

theorem directOrbitPairedDeepJet_fixed_unit_identity :
    orbitUnit01Unit * (directOrbitDeepJetThetaUnit⁻¹) ^ (3 : ℕ) *
        directOrbitDeepJetRho⁻¹ = directOrbitDeepJetThetaUnit := by
  have horbit :
      orbitUnit01Unit = directOrbitDeepJetThetaUnit ^ 4 *
        directOrbitDeepJetRho := by
    apply Units.ext
    rw [orbitUnit01Unit_val]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    rw [directOrbitDeepJetThetaUnit_val, directOrbitDeepJetRho_val]
    change orbitUnit01 = thetaSevenUnit ^ 4 * (-alpha ^ 3)
    apply SevenRealCubicInt.ext <;>
      norm_num [orbitUnit01, pairAxisUnit_one, thetaSevenUnit,
      eisensteinAxisUnitInv, eisensteinAxisUnit, eisensteinAxis,
      alphaAddOneInv, alpha, SevenRealCubicInt.mul, pow_two, pow_succ]
  rw [horbit]
  change directOrbitDeepJetThetaUnit ^ 4 * directOrbitDeepJetRho *
      (directOrbitDeepJetThetaUnit⁻¹) ^ (3 : ℕ) *
        directOrbitDeepJetRho⁻¹ = directOrbitDeepJetThetaUnit
  rw [inv_pow]
  calc
    directOrbitDeepJetThetaUnit ^ 4 * directOrbitDeepJetRho *
          (directOrbitDeepJetThetaUnit ^ 3)⁻¹ *
          directOrbitDeepJetRho⁻¹ =
        directOrbitDeepJetThetaUnit ^ 3 *
          (directOrbitDeepJetThetaUnit ^ 3)⁻¹ *
          directOrbitDeepJetThetaUnit *
          (directOrbitDeepJetRho * directOrbitDeepJetRho⁻¹) := by
            rw [show directOrbitDeepJetThetaUnit ^ 4 =
              directOrbitDeepJetThetaUnit ^ 3 * directOrbitDeepJetThetaUnit by
                simpa using (pow_add directOrbitDeepJetThetaUnit 3 1)]
            ac_rfl
    _ = directOrbitDeepJetThetaUnit := by simp

theorem directOrbitPairedDeepJet_quotientCore_eq
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p) (_hc : h.c = 1)
    (xi : SevenRealCubicIntˣ)
    (hxi : h.squareRefinement.quotientSquareRoot =
      (xi : SevenRealCubicInt) * (h.v : SevenRealCubicInt)) :
    h.squareRefinement.powerSplit.quotientCore =
      (directOrbitPairedDeepJetY h xi : SevenRealCubicInt) *
        (h.v : SevenRealCubicInt) ^ 14 := by
  rw [h.squareRefinement.powerSplit.quotientCore_eq,
    h.squareRefinement.quotientRoot_eq, hxi]
  simp only [directOrbitPairedDeepJetY, Units.val_mul,
    Units.val_pow_eq_pow_val]
  ring

def directOrbitPairedDeepJetZ
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p)
    (v : SevenRealCubicIntˣ) : SevenRealCubicInt :=
  ((v⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt) *
    (h.v : SevenRealCubicInt) ^ 2

theorem directOrbitPairedDeepJet_quotientCore_eq_theta_mul_Z_pow_seven
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p) (hc : h.c = 1)
    (xi v : SevenRealCubicIntˣ)
    (hxi : h.squareRefinement.quotientSquareRoot =
      (xi : SevenRealCubicInt) * (h.v : SevenRealCubicInt))
    (hv : directOrbitPairedDeepJetY h xi =
      directOrbitDeepJetThetaUnit * (v⁻¹) ^ 7) :
    h.squareRefinement.powerSplit.quotientCore =
      thetaSevenUnit * (directOrbitPairedDeepJetZ h v) ^ 7 := by
  rw [directOrbitPairedDeepJet_quotientCore_eq h hc xi hxi, hv]
  simp only [directOrbitPairedDeepJetZ, Units.val_mul,
    Units.val_pow_eq_pow_val]
  change (thetaSevenUnit : SevenRealCubicInt) *
      ((v⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt) ^ 7 *
        (h.v : SevenRealCubicInt) ^ 14 = _
  rw [show (14 : ℕ) = 2 * 7 by norm_num, pow_mul]
  ring

theorem directOrbitPairedDeepJet_gapCore_eq
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p) (_hc : h.c = 1)
    (eta : SevenRealCubicIntˣ)
    (heta : h.squareRefinement.gapSquareRoot =
      (eta : SevenRealCubicInt) * (h.u : SevenRealCubicInt)) :
    h.squareRefinement.powerSplit.gapCore =
      (directOrbitDeepJetXUnit h.squareRefinement eta : SevenRealCubicInt) *
        (h.u : SevenRealCubicInt) ^ 14 := by
  rw [h.squareRefinement.powerSplit.gapCore_eq,
    h.squareRefinement.gapRoot_eq, heta]
  simp only [directOrbitDeepJetXUnit, directOrbitDeepJetRootUnit,
    Units.val_mul, Units.val_pow_eq_pow_val]
  ring

theorem directOrbitPairedDeepJet_cores_product_unit_eq
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p) (hc : h.c = 1)
    (eta xi : SevenRealCubicIntˣ)
    (heta : h.squareRefinement.gapSquareRoot =
      (eta : SevenRealCubicInt) * (h.u : SevenRealCubicInt))
    (hxi : h.squareRefinement.quotientSquareRoot =
      (xi : SevenRealCubicInt) * (h.v : SevenRealCubicInt)) :
    directOrbitDeepJetXUnit h.squareRefinement eta *
        directOrbitPairedDeepJetY h xi =
      orbitUnit01Unit * directOrbitDeepJetThetaUnit ^
        (7 * (1 + 2 * h.squareRefinement.powerSplit.gapSplit.k)) := by
  have ha : h.squareRefinement.powerSplit.gapSplit.a = h.u * h.v := by
    simpa [hc] using h.unitPart_eq
  have huv : ((h.u * h.v : ℕ) : SevenRealCubicInt) ≠ 0 := by
    intro hz
    have hfst := congrArg SevenRealCubicInt.fst hz
    change (h.u * h.v : ℤ) = 0 at hfst
    have hnat : (h.u * h.v : ℤ) ≠ 0 := by
      exact_mod_cast (Nat.mul_pos h.u_pos h.v_pos).ne'
    exact hnat hfst
  have hcancel :
      ((h.u * h.v : ℕ) : SevenRealCubicInt) ^ 14 ≠ 0 :=
    pow_ne_zero _ huv
  apply Units.ext
  simp only [Units.val_mul, Units.val_pow_eq_pow_val,
    directOrbitPairedDeepJetY, orbitUnit01Unit_val,
    directOrbitDeepJetThetaUnit_val]
  have hxy :
      ((directOrbitDeepJetXUnit h.squareRefinement eta : SevenRealCubicInt) *
          (directOrbitPairedDeepJetY h xi : SevenRealCubicInt)) *
          ((h.u * h.v : ℕ) : SevenRealCubicInt) ^ 14 =
        orbitUnit01 * thetaSevenUnit ^
            (7 * (1 + 2 * h.squareRefinement.powerSplit.gapSplit.k)) *
          ((h.u * h.v : ℕ) : SevenRealCubicInt) ^ 14 := by
    calc
      _ = h.squareRefinement.powerSplit.gapCore *
          h.squareRefinement.powerSplit.quotientCore := by
        rw [directOrbitPairedDeepJet_gapCore_eq h hc eta heta,
          directOrbitPairedDeepJet_quotientCore_eq h hc xi hxi]
        norm_num [Nat.cast_mul]
        ring
      _ = orbitUnit01 *
          (thetaSevenUnit ^
            (1 + 2 * h.squareRefinement.powerSplit.gapSplit.k) *
            (h.squareRefinement.powerSplit.gapSplit.a : SevenRealCubicInt) ^ 2) ^ 7 :=
        h.squareRefinement.powerSplit.cores_product_eq
      _ = _ := by
        rw [ha]
        ring
  exact mul_right_cancel₀ hcancel hxy

theorem directOrbitPairedDeepJet_same_v_unit_identity
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p) (hc : h.c = 1)
    (eta xi v : SevenRealCubicIntˣ)
    (heta : h.squareRefinement.gapSquareRoot =
      (eta : SevenRealCubicInt) * (h.u : SevenRealCubicInt))
    (hxi : h.squareRefinement.quotientSquareRoot =
      (xi : SevenRealCubicInt) * (h.v : SevenRealCubicInt))
    (hv : directOrbitDeepJetWUnit h.squareRefinement eta =
      directOrbitDeepJetRho * v ^ 7) :
    directOrbitPairedDeepJetY h xi =
      directOrbitDeepJetThetaUnit * (v⁻¹) ^ 7 := by
  let t := h.squareRefinement
  let n := directOrbitDeepJetExponent t
  have hprod := directOrbitPairedDeepJet_cores_product_unit_eq
    h hc eta xi heta hxi
  have hX : directOrbitDeepJetXUnit t eta =
      directOrbitDeepJetThetaUnit ^ n *
        (directOrbitDeepJetRho * v ^ 7) := by
    calc
      directOrbitDeepJetXUnit t eta =
          directOrbitDeepJetThetaUnit ^ n *
            (directOrbitDeepJetThetaUnit⁻¹ ^ n *
              directOrbitDeepJetXUnit t eta) := by group
      _ = directOrbitDeepJetThetaUnit ^ n *
          directOrbitDeepJetWUnit t eta := by rfl
      _ = directOrbitDeepJetThetaUnit ^ n *
          (directOrbitDeepJetRho * v ^ 7) := by
        rw [hv]
  have hn : n = 7 * (1 + 2 * t.powerSplit.gapSplit.k) + 3 := by
    simp [n, t, directOrbitDeepJetExponent]
    ring
  have hpow : directOrbitDeepJetThetaUnit ^ n =
      directOrbitDeepJetThetaUnit ^
          (7 * (1 + 2 * t.powerSplit.gapSplit.k)) *
        directOrbitDeepJetThetaUnit ^ 3 := by
    rw [hn, pow_add]
  have hfix := directOrbitPairedDeepJet_fixed_unit_identity
  calc
    directOrbitPairedDeepJetY h xi =
        (directOrbitDeepJetXUnit t eta)⁻¹ *
          (directOrbitDeepJetXUnit t eta *
            directOrbitPairedDeepJetY h xi) := by group
    _ = (directOrbitDeepJetThetaUnit ^ n *
          (directOrbitDeepJetRho * v ^ 7))⁻¹ *
          (orbitUnit01Unit * directOrbitDeepJetThetaUnit ^
            (7 * (1 + 2 * t.powerSplit.gapSplit.k))) := by
      rw [hprod, hX]
    _ = (v⁻¹) ^ 7 *
          (orbitUnit01Unit * (directOrbitDeepJetThetaUnit⁻¹) ^ 3 *
            directOrbitDeepJetRho⁻¹) := by
      rw [hpow]
      simp [mul_inv_rev, inv_pow, mul_assoc, mul_comm, mul_left_comm]
    _ = directOrbitDeepJetThetaUnit * (v⁻¹) ^ 7 := by
      rw [hfix]
      ac_rfl

theorem directOrbitPairedDeepJet_quotientCore_eq_canonical_depth32
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (s : DirectOrbitPowerSplitPacket p) :
    ∃ d : SevenRealCubicInt,
      eisensteinAxis ^ 31 ∣ d ∧
        s.quotientCore = directOrbitQuotientCoreCanonical p d := by
  rcases directOrbit_gap_axis_pow32_dvd p with ⟨t, ht⟩
  let d := eisensteinAxis ^ 31 * t
  have hd : eisensteinAxis ^ 31 ∣ d := by
    exact ⟨t, rfl⟩
  have hgap : directOrbitGap p = eisensteinAxis * d := by
    dsimp [d]
    rw [ht]
    ring
  have hcanonical := directOrbitQuotient_eq_axis_cube_mul_canonical p d hgap
  refine ⟨d, hd, ?_⟩
  exact directOrbitQuotientCore_unique p s.quotientCore
    (directOrbitQuotientCoreCanonical p d) s.quotient_eq hcanonical

theorem directOrbitPairedDeepJet_quotientCore_sub_leading_axis_pow32_dvd
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (s : DirectOrbitPowerSplitPacket p) :
    eisensteinAxis ^ 32 ∣
      s.quotientCore - thetaSevenUnit * p.rho ^ 6 := by
  rcases directOrbitPairedDeepJet_quotientCore_eq_canonical_depth32 s with
    ⟨d, hd, hcore⟩
  rcases hd with ⟨e, rfl⟩
  rw [hcore]
  refine ⟨
    3 * thetaSevenUnit * p.rho ^ 5 * e +
      5 * thetaSevenUnit * p.rho ^ 4 * eisensteinAxis ^ 32 * e ^ 2 +
      5 * thetaSevenUnit * p.rho ^ 3 * eisensteinAxis ^ 64 * e ^ 3 +
      3 * thetaSevenUnit * p.rho ^ 2 * eisensteinAxis ^ 96 * e ^ 4 +
      thetaSevenUnit * p.rho * eisensteinAxis ^ 128 * e ^ 5 +
      eisensteinAxis ^ 157 * e ^ 6, ?_⟩
  simp only [directOrbitQuotientCoreCanonical, sub_eq_add_neg, mul_pow]
  ring_nf

theorem directOrbitPairedDeepJet_rotate_gap_theta_coordinates
    (A B C : ℤ) :
    thetaConstInt
        (SevenRealCubicInt.rotateEquiv (ofThetaCoordinates A B C) -
          ofThetaCoordinates A B C) = -7 * C ∧
      thetaLinearInt
        (SevenRealCubicInt.rotateEquiv (ofThetaCoordinates A B C) -
          ofThetaCoordinates A B C) = 3 * B - 21 * C ∧
      thetaSquareInt
        (SevenRealCubicInt.rotateEquiv (ofThetaCoordinates A B C) -
          ofThetaCoordinates A B C) = B - 6 * C := by
  norm_num [thetaConstInt, thetaLinearInt, thetaSquareInt,
    ofThetaCoordinates, rotateEquiv, rotateHom,
    eisensteinAxis_sq_coordinates]
  constructor
  · ring
  constructor <;> ring

theorem directOrbitPairedDeepJet_ofInt_dvd_theta_coordinates
    {n : ℤ} {x : SevenRealCubicInt}
    (hx : ofInt n ∣ x) :
    n ∣ thetaConstInt x ∧
      n ∣ thetaLinearInt x ∧
        n ∣ thetaSquareInt x := by
  rcases hx with ⟨y, rfl⟩
  rcases y with ⟨a, b, c⟩
  constructor
  · refine ⟨a + 3 * b + 9 * c, ?_⟩
    norm_num [thetaConstInt, thetaLinearInt, thetaSquareInt,
      ofInt, SevenRealCubicInt.mul]
    ring
  constructor
  · refine ⟨b + 6 * c, ?_⟩
    norm_num [thetaConstInt, thetaLinearInt, thetaSquareInt,
      ofInt, SevenRealCubicInt.mul]
    ring
  · refine ⟨c, ?_⟩
    norm_num [thetaConstInt, thetaLinearInt, thetaSquareInt,
      ofInt, SevenRealCubicInt.mul]

theorem directOrbit_axis_pow_six_dvd_imp_natCast49
    {x : SevenRealCubicInt} (hx : eisensteinAxis ^ 6 ∣ x) :
    (49 : SevenRealCubicInt) ∣ x := by
  rcases hx with ⟨c, hc⟩
  let t : SevenRealCubicIntˣ := thetaSevenUnit_isUnit.unit
  have hseven : (7 : SevenRealCubicInt) =
      eisensteinAxis ^ 3 * (t : SevenRealCubicInt) := by
    simpa [t] using seven_eq_eisensteinAxis_cube_mul_unit
  have h49 : (49 : SevenRealCubicInt) =
      eisensteinAxis ^ 6 * (t : SevenRealCubicInt) ^ 2 := by
    rw [show (49 : SevenRealCubicInt) = (7 : SevenRealCubicInt) ^ 2 by norm_num,
      hseven]
    rw [mul_pow, ← pow_mul]
  have hinv : (t : SevenRealCubicInt) ^ 2 *
      ((t⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt) ^ 2 = 1 := by
    rw [← mul_pow, ← Units.val_mul]
    simp
  refine ⟨((t⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt) ^ 2 * c, ?_⟩
  rw [h49, hc]
  calc
    eisensteinAxis ^ 6 * c = eisensteinAxis ^ 6 * 1 * c := by simp
    _ = eisensteinAxis ^ 6 *
        ((t : SevenRealCubicInt) ^ 2 *
          (((t⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt) ^ 2)) * c := by
      rw [hinv]
    _ = eisensteinAxis ^ 6 *
        (((t : SevenRealCubicInt) ^ 2 *
          (((t⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt) ^ 2)) * c) := by
      rw [mul_assoc (eisensteinAxis ^ 6)
        ((t : SevenRealCubicInt) ^ 2 *
          (((t⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt) ^ 2)) c]
    _ = eisensteinAxis ^ 6 *
        ((t : SevenRealCubicInt) ^ 2 *
          (((t⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt) ^ 2 * c)) := by
      rw [mul_assoc ((t : SevenRealCubicInt) ^ 2)
        (((t⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt) ^ 2) c]
    _ = eisensteinAxis ^ 6 * (t : SevenRealCubicInt) ^ 2 *
        (((t⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt) ^ 2 * c) := by
      rw [mul_assoc (eisensteinAxis ^ 6) ((t : SevenRealCubicInt) ^ 2)
        (((t⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt) ^ 2 * c)]

theorem directOrbit_axis_pow_nine_dvd_imp_natCast343
    {x : SevenRealCubicInt} (hx : eisensteinAxis ^ 9 ∣ x) :
    (343 : SevenRealCubicInt) ∣ x := by
  rcases hx with ⟨c, hc⟩
  let t : SevenRealCubicIntˣ := thetaSevenUnit_isUnit.unit
  have hseven : (7 : SevenRealCubicInt) =
      eisensteinAxis ^ 3 * (t : SevenRealCubicInt) := by
    simpa [t] using seven_eq_eisensteinAxis_cube_mul_unit
  have h343 : (343 : SevenRealCubicInt) =
      eisensteinAxis ^ 9 * (t : SevenRealCubicInt) ^ 3 := by
    rw [show (343 : SevenRealCubicInt) = (7 : SevenRealCubicInt) ^ 3 by norm_num,
      hseven]
    rw [mul_pow, ← pow_mul]
  have hinv : (t : SevenRealCubicInt) ^ 3 *
      ((t⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt) ^ 3 = 1 := by
    rw [← mul_pow, ← Units.val_mul]
    simp
  refine ⟨((t⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt) ^ 3 * c, ?_⟩
  rw [h343, hc]
  calc
    eisensteinAxis ^ 9 * c = eisensteinAxis ^ 9 * 1 * c := by simp
    _ = eisensteinAxis ^ 9 *
        ((t : SevenRealCubicInt) ^ 3 *
          (((t⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt) ^ 3)) * c := by
      rw [hinv]
    _ = eisensteinAxis ^ 9 *
        (((t : SevenRealCubicInt) ^ 3 *
          (((t⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt) ^ 3)) * c) := by
      rw [mul_assoc (eisensteinAxis ^ 9)
        ((t : SevenRealCubicInt) ^ 3 *
          (((t⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt) ^ 3)) c]
    _ = eisensteinAxis ^ 9 *
        ((t : SevenRealCubicInt) ^ 3 *
          (((t⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt) ^ 3 * c)) := by
      rw [mul_assoc ((t : SevenRealCubicInt) ^ 3)
        (((t⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt) ^ 3) c]
    _ = eisensteinAxis ^ 9 * (t : SevenRealCubicInt) ^ 3 *
        (((t⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt) ^ 3 * c) := by
      rw [mul_assoc (eisensteinAxis ^ 9) ((t : SevenRealCubicInt) ^ 3)
        (((t⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt) ^ 3 * c)]

theorem directOrbitPairedDeepJet_source_root_mod49_scalar
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectRealCubicRootPacket source r) :
    (49 : ℤ) ∣ thetaLinearInt p.rho ∧
      (49 : ℤ) ∣ thetaSquareInt p.rho := by
  have hpow : eisensteinAxis ^ 9 ∣ directOrbitGap p := by
    apply dvd_trans (show eisensteinAxis ^ 9 ∣ eisensteinAxis ^ 32 by
      refine ⟨eisensteinAxis ^ 23, ?_⟩
      rw [← pow_add])
    exact directOrbit_gap_axis_pow32_dvd p
  have h343 := directOrbit_axis_pow_nine_dvd_imp_natCast343 hpow
  have h343' : ofInt (343 : ℤ) = (343 : SevenRealCubicInt) := by
    change (⟨343, 0, 0⟩ : SevenRealCubicInt) = ⟨343, 0, 0⟩
    rfl
  have hcoords := directOrbitPairedDeepJet_ofInt_dvd_theta_coordinates
    (n := (343 : ℤ)) (x := directOrbitGap p) (by
      rw [h343']
      exact h343)
  let A : ℤ := thetaConstInt p.rho
  let B : ℤ := thetaLinearInt p.rho
  let C : ℤ := thetaSquareInt p.rho
  have hrho : p.rho = ofThetaCoordinates A B C := by
    exact theta_coordinate_decomposition p.rho
  have hrot := directOrbitPairedDeepJet_rotate_gap_theta_coordinates A B C
  have hcoords' :
      (343 : ℤ) ∣ -7 * C ∧
        (343 : ℤ) ∣ 3 * B - 21 * C ∧
          (343 : ℤ) ∣ B - 6 * C := by
    rw [directOrbitGap, hrho] at hcoords
    simpa only [hrot.1, hrot.2.1, hrot.2.2, A, B, C] using hcoords
  have hC : (49 : ℤ) ∣ C := by
    rcases hcoords'.1 with ⟨q, hq⟩
    refine ⟨-q, ?_⟩
    nlinarith
  have hB : (49 : ℤ) ∣ B := by
    rcases hcoords'.2.2 with ⟨q, hq⟩
    rcases hC with ⟨c, hc⟩
    refine ⟨7 * q + 6 * c, ?_⟩
    nlinarith
  exact ⟨by simpa [B] using hB, by simpa [C] using hC⟩

end SevenRealCubic
end
end DkMath.FLT.Seven
