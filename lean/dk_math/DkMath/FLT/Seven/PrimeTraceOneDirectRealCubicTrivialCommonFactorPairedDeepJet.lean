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

theorem directOrbitPairedDeepJet_source_root_sub_scalar_dvd49
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectRealCubicRootPacket source r) :
    (49 : SevenRealCubicInt) ∣
      p.rho - ofInt (thetaConstInt p.rho) := by
  let A : ℤ := thetaConstInt p.rho
  let B : ℤ := thetaLinearInt p.rho
  let C : ℤ := thetaSquareInt p.rho
  have hrho : p.rho = ofThetaCoordinates A B C := by
    exact theta_coordinate_decomposition p.rho
  have hBC := directOrbitPairedDeepJet_source_root_mod49_scalar p
  have hB : (49 : ℤ) ∣ B := by simpa [B] using hBC.1
  have hC : (49 : ℤ) ∣ C := by simpa [C] using hBC.2
  rcases hB with ⟨b, hb⟩
  rcases hC with ⟨c, hc⟩
  have h49O : (49 : SevenRealCubicInt) = ofInt (49 : ℤ) := by
    rfl
  refine ⟨ofInt b * eisensteinAxis + ofInt c * eisensteinAxis ^ 2, ?_⟩
  rw [hrho, hb, hc, h49O]
  norm_num [ofThetaCoordinates, thetaConstInt, ofInt,
    eisensteinAxis_sq_coordinates, SevenRealCubicInt.mul]
  apply SevenRealCubicInt.ext <;>
    norm_num [ofInt, SevenRealCubicInt.fst_natCast,
      SevenRealCubicInt.snd_natCast, SevenRealCubicInt.thd_natCast,
      SevenRealCubicInt.fst_intCast, SevenRealCubicInt.snd_intCast,
      SevenRealCubicInt.thd_intCast,
      eisensteinAxis_sq_coordinates,
      SevenRealCubicInt.mul, pow_two, pow_succ] <;> ring

theorem directOrbitPairedDeepJet_source_root_pow_six_mod49_scalar
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectRealCubicRootPacket source r) :
    (49 : SevenRealCubicInt) ∣
        p.rho ^ 6 - (ofInt (thetaConstInt p.rho)) ^ 6 ∧
      (49 : ℤ) ∣ thetaLinearInt (p.rho ^ 6) ∧
      (49 : ℤ) ∣ thetaSquareInt (p.rho ^ 6) := by
  have hscalar := directOrbitPairedDeepJet_source_root_sub_scalar_dvd49 p
  rcases hscalar with ⟨q, hq⟩
  have hrho : p.rho = ofInt (thetaConstInt p.rho) +
      (49 : SevenRealCubicInt) * q := by
    linear_combination hq
  let a : SevenRealCubicInt := ofInt (thetaConstInt p.rho)
  have hrho' : p.rho = a + (49 : SevenRealCubicInt) * q := by
    simpa [a] using hrho
  have hpows : p.rho ^ 6 = (a + (49 : SevenRealCubicInt) * q) ^ 6 := by
    rw [hrho']
  have h49 : (49 : SevenRealCubicInt) ∣ p.rho ^ 6 -
      (ofInt (thetaConstInt p.rho)) ^ 6 := by
    refine ⟨q * (6 * a ^ 5 + 15 * (49 : SevenRealCubicInt) * a ^ 4 * q +
        20 * (49 : SevenRealCubicInt) ^ 2 * a ^ 3 * q ^ 2 +
        15 * (49 : SevenRealCubicInt) ^ 3 * a ^ 2 * q ^ 3 +
        6 * (49 : SevenRealCubicInt) ^ 4 * a * q ^ 4 +
        (49 : SevenRealCubicInt) ^ 5 * q ^ 5), ?_⟩
    calc
      p.rho ^ 6 - (ofInt (thetaConstInt p.rho)) ^ 6 =
          (a + (49 : SevenRealCubicInt) * q) ^ 6 - a ^ 6 := by
        rw [hpows]
      _ = (49 : SevenRealCubicInt) *
          (q * (6 * a ^ 5 + 15 * (49 : SevenRealCubicInt) * a ^ 4 * q +
            20 * (49 : SevenRealCubicInt) ^ 2 * a ^ 3 * q ^ 2 +
            15 * (49 : SevenRealCubicInt) ^ 3 * a ^ 2 * q ^ 3 +
            6 * (49 : SevenRealCubicInt) ^ 4 * a * q ^ 4 +
            (49 : SevenRealCubicInt) ^ 5 * q ^ 5)) := by ring
  have h49' : ofInt (49 : ℤ) = (49 : SevenRealCubicInt) := by
    change (⟨49, 0, 0⟩ : SevenRealCubicInt) = ⟨49, 0, 0⟩
    rfl
  have hcoords := directOrbitPairedDeepJet_ofInt_dvd_theta_coordinates
    (n := (49 : ℤ))
    (x := p.rho ^ 6 - (ofInt (thetaConstInt p.rho)) ^ 6) (by
      rw [h49']
      exact h49)
  have hlinearScalar :
      thetaLinearInt ((ofInt (thetaConstInt p.rho)) ^ 6) = 0 := by
    norm_num [thetaLinearInt, ofInt, SevenRealCubicInt.mul,
      pow_two, pow_succ]
  have hsquareScalar :
      thetaSquareInt ((ofInt (thetaConstInt p.rho)) ^ 6) = 0 := by
    norm_num [thetaSquareInt, ofInt, SevenRealCubicInt.mul,
      pow_two, pow_succ]
  rcases hcoords.2.1 with ⟨q₁, hq₁⟩
  rcases hcoords.2.2 with ⟨q₂, hq₂⟩
  refine ⟨h49, ?_, ?_⟩
  · refine ⟨q₁, ?_⟩
    simpa [thetaLinearInt, hlinearScalar] using hq₁
  · refine ⟨q₂, ?_⟩
    simpa [thetaSquareInt, hsquareScalar] using hq₂

theorem directOrbitPairedDeepJet_quotient_remainder_cancel_theta
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p) (hc : h.c = 1)
    (xi v : SevenRealCubicIntˣ)
    (hxi : h.squareRefinement.quotientSquareRoot =
      (xi : SevenRealCubicInt) * (h.v : SevenRealCubicInt))
    (hv : directOrbitPairedDeepJetY h xi =
      directOrbitDeepJetThetaUnit * (v⁻¹) ^ 7) :
    eisensteinAxis ^ 32 ∣
      (directOrbitPairedDeepJetZ h v) ^ 7 - p.rho ^ 6 := by
  have hdepth := directOrbitPairedDeepJet_quotientCore_sub_leading_axis_pow32_dvd
    h.squareRefinement.powerSplit
  have hquot := directOrbitPairedDeepJet_quotientCore_eq_theta_mul_Z_pow_seven
    h hc xi v hxi hv
  rw [hquot] at hdepth
  have hfactor :
      thetaSevenUnit * (directOrbitPairedDeepJetZ h v) ^ 7 -
          thetaSevenUnit * p.rho ^ 6 =
        thetaSevenUnit *
          ((directOrbitPairedDeepJetZ h v) ^ 7 - p.rho ^ 6) := by ring
  rw [hfactor] at hdepth
  let t : SevenRealCubicIntˣ := thetaSevenUnit_isUnit.unit
  have ht : (t : SevenRealCubicInt) = thetaSevenUnit := by
    rfl
  have hinv : (t : SevenRealCubicInt) *
      ((t⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt) = 1 := by
    rw [← Units.val_mul]
    simp
  rcases hdepth with ⟨q, hq⟩
  refine ⟨((t⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt) * q, ?_⟩
  calc
    (directOrbitPairedDeepJetZ h v) ^ 7 - p.rho ^ 6 =
        1 * ((directOrbitPairedDeepJetZ h v) ^ 7 - p.rho ^ 6) := by simp
    _ = (((t⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt) *
        (t : SevenRealCubicInt)) *
          ((directOrbitPairedDeepJetZ h v) ^ 7 - p.rho ^ 6) := by
      rw [← Units.val_mul]
      simp
    _ = ((t⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt) *
        (thetaSevenUnit *
          ((directOrbitPairedDeepJetZ h v) ^ 7 - p.rho ^ 6)) := by
      rw [ht]
      ring
    _ = ((t⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt) *
        (eisensteinAxis ^ 32 * q) := by rw [← hq]
    _ = eisensteinAxis ^ 32 *
        (((t⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt) * q) := by ring

theorem directOrbitPairedDeepJet_z_pow_seven_square_mod49
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p) (hc : h.c = 1)
    (xi v : SevenRealCubicIntˣ)
    (hxi : h.squareRefinement.quotientSquareRoot =
      (xi : SevenRealCubicInt) * (h.v : SevenRealCubicInt))
    (hv : directOrbitPairedDeepJetY h xi =
      directOrbitDeepJetThetaUnit * (v⁻¹) ^ 7) :
    (49 : ℤ) ∣ thetaSquareInt ((directOrbitPairedDeepJetZ h v) ^ 7) := by
  have h32 := directOrbitPairedDeepJet_quotient_remainder_cancel_theta
    h hc xi v hxi hv
  have h6 : eisensteinAxis ^ 6 ∣
      (directOrbitPairedDeepJetZ h v) ^ 7 - p.rho ^ 6 := by
    exact dvd_trans (by
      refine ⟨eisensteinAxis ^ 26, ?_⟩
      rw [← pow_add]) h32
  have h49 := directOrbit_axis_pow_six_dvd_imp_natCast49 h6
  have h49' : ofInt (49 : ℤ) = (49 : SevenRealCubicInt) := by
    change (⟨49, 0, 0⟩ : SevenRealCubicInt) = ⟨49, 0, 0⟩
    rfl
  have hcoords := directOrbitPairedDeepJet_ofInt_dvd_theta_coordinates
    (n := (49 : ℤ)) (x := (directOrbitPairedDeepJetZ h v) ^ 7 - p.rho ^ 6) (by
      rw [h49']
      exact h49)
  have hsource := directOrbitPairedDeepJet_source_root_pow_six_mod49_scalar p
  rcases hcoords.2.2 with ⟨q, hq⟩
  rcases hsource.2.2 with ⟨r₀, hr₀⟩
  refine ⟨q + r₀, ?_⟩
  dsimp [thetaSquareInt] at hq hr₀ ⊢
  nlinarith

theorem directOrbitPairedDeepJet_not_seven_v
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p)
    (xi : SevenRealCubicIntˣ)
    (hxi : h.squareRefinement.quotientSquareRoot =
      (xi : SevenRealCubicInt) * (h.v : SevenRealCubicInt)) :
    ¬7 ∣ h.v := by
  intro hV
  rcases hV with ⟨m, hm⟩
  have haxis7 : eisensteinAxis ∣ (7 : SevenRealCubicInt) := by
    have hseven : (7 : SevenRealCubicInt) =
        eisensteinAxis ^ 3 *
          (thetaSevenUnit_isUnit.unit : SevenRealCubicInt) := by
      simpa using seven_eq_eisensteinAxis_cube_mul_unit
    refine ⟨eisensteinAxis ^ 2 *
      (thetaSevenUnit_isUnit.unit : SevenRealCubicInt), ?_⟩
    calc
      (7 : SevenRealCubicInt) = eisensteinAxis ^ 3 *
          (thetaSevenUnit_isUnit.unit : SevenRealCubicInt) := hseven
      _ = eisensteinAxis *
          (eisensteinAxis ^ 2 *
            (thetaSevenUnit_isUnit.unit : SevenRealCubicInt)) := by ring
  have hVcast : (h.v : SevenRealCubicInt) =
      (7 : SevenRealCubicInt) * (m : SevenRealCubicInt) := by
    rw [hm]
    norm_num [Nat.cast_mul]
  have haxisV : eisensteinAxis ∣ (h.v : SevenRealCubicInt) := by
    rw [hVcast]
    exact dvd_mul_of_dvd_left haxis7 _
  have haxisQ : eisensteinAxis ∣ h.squareRefinement.quotientSquareRoot := by
    rcases haxisV with ⟨q, hq⟩
    refine ⟨(xi : SevenRealCubicInt) * q, ?_⟩
    rw [hxi, hq]
    ring
  exact directOrbitSquareRefinement_quotientSquareRoot_not_axis_dvd
    h.squareRefinement haxisQ

theorem directOrbitPairedDeepJet_z_local_unit_and_linear
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p)
    (xi v : SevenRealCubicIntˣ)
    (hxi : h.squareRefinement.quotientSquareRoot =
      (xi : SevenRealCubicInt) * (h.v : SevenRealCubicInt))
    (hlin : thetaLinearModSeven (v : SevenRealCubicInt) = 0) :
    (thetaConstInt (directOrbitPairedDeepJetZ h v) : ZMod 7) ≠ 0 ∧
      thetaLinearModSeven (directOrbitPairedDeepJetZ h v) = 0 := by
  have hnot : ¬7 ∣ h.v := directOrbitPairedDeepJet_not_seven_v h xi hxi
  have hVmod : (h.v : ZMod 7) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact hnot
  have hconstInv :
      thetaConstModSeven ((v⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt) ≠ 0 :=
    thetaConstModSeven_unit_ne_zero (v⁻¹)
  have hconstV2 :
      thetaConstModSeven ((h.v : SevenRealCubicInt) ^ 2) =
        (h.v : ZMod 7) ^ 2 := by
    rw [pow_two, thetaConstModSeven_mul]
    norm_num [thetaConstModSeven]
    ring
  have hlinV2 : thetaLinearModSeven ((h.v : SevenRealCubicInt) ^ 2) = 0 := by
    rw [pow_two, thetaLinearModSeven_mul]
    norm_num [thetaConstModSeven, thetaLinearModSeven]
  have hconstZ :
      thetaConstModSeven (directOrbitPairedDeepJetZ h v) ≠ 0 := by
    rw [directOrbitPairedDeepJetZ, thetaConstModSeven_mul,
      hconstV2]
    exact mul_ne_zero hconstInv (pow_ne_zero 2 hVmod)
  have hlinInv :
      thetaLinearModSeven
        ((v⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt) = 0 := by
    have hprod : thetaLinearModSeven
        (((v : SevenRealCubicIntˣ) : SevenRealCubicInt) *
          ((v⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt)) = 0 := by
      rw [← Units.val_mul]
      simp
    rw [thetaLinearModSeven_mul, hlin, zero_mul, add_zero] at hprod
    rcases mul_eq_zero.mp hprod with hzero | hzero
    · exact False.elim ((thetaConstModSeven_unit_ne_zero v) hzero)
    · exact hzero
  have hlinZ : thetaLinearModSeven (directOrbitPairedDeepJetZ h v) = 0 := by
    rw [directOrbitPairedDeepJetZ, thetaLinearModSeven_mul,
      hlinInv, hlinV2]
    simp
  constructor
  · change thetaConstModSeven (directOrbitPairedDeepJetZ h v) ≠ 0
    exact hconstZ
  · exact hlinZ

theorem directOrbitPairedDeepJet_z_square_mod_seven
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p) (hc : h.c = 1)
    (xi v : SevenRealCubicIntˣ)
    (hxi : h.squareRefinement.quotientSquareRoot =
      (xi : SevenRealCubicInt) * (h.v : SevenRealCubicInt))
    (hv : directOrbitPairedDeepJetY h xi =
      directOrbitDeepJetThetaUnit * (v⁻¹) ^ 7)
    (hlin : thetaLinearModSeven (v : SevenRealCubicInt) = 0) :
    thetaSquareModSeven (directOrbitPairedDeepJetZ h v) = 0 := by
  have hjet := directOrbitPairedDeepJet_z_pow_seven_square_mod49
    h hc xi v hxi hv
  let A : ℤ := thetaConstInt (directOrbitPairedDeepJetZ h v)
  let B : ℤ := thetaLinearInt (directOrbitPairedDeepJetZ h v)
  let C : ℤ := thetaSquareInt (directOrbitPairedDeepJetZ h v)
  have hz : directOrbitPairedDeepJetZ h v = ofThetaCoordinates A B C := by
    exact theta_coordinate_decomposition _
  have hsq := thetaSquare_pow_seven_mod49_neutral A B C
  rw [← hz] at hsq
  rcases hjet with ⟨q₁, hq₁⟩
  rcases hsq with ⟨q₂, hq₂⟩
  have h49 : (49 : ℤ) ∣ 7 * (C * A ^ 6 + 3 * B ^ 2 * A ^ 5) := by
    refine ⟨q₁ - q₂, ?_⟩
    dsimp [A, B, C] at hq₁ hq₂ ⊢
    linarith
  rcases h49 with ⟨q, hq⟩
  have h7 : (7 : ℤ) ∣ C * A ^ 6 + 3 * B ^ 2 * A ^ 5 := by
    refine ⟨q, ?_⟩
    nlinarith [hq]
  have hmod :
      (C : ZMod 7) * (A : ZMod 7) ^ 6 +
          3 * (B : ZMod 7) ^ 2 * (A : ZMod 7) ^ 5 = 0 := by
    have hzmod :
        ((C * A ^ 6 + 3 * B ^ 2 * A ^ 5 : ℤ) : ZMod 7) = 0 := by
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mpr h7
    simpa [Int.cast_add, Int.cast_mul, Int.cast_pow] using hzmod
  have hlocal := directOrbitPairedDeepJet_z_local_unit_and_linear
    h xi v hxi hlin
  have hA : (A : ZMod 7) ≠ 0 := by
    exact hlocal.1
  have hB : (B : ZMod 7) = 0 := by
    exact hlocal.2
  rw [hB] at hmod
  norm_num at hmod
  have hC : (C : ZMod 7) = 0 := by
    rcases hmod with hC | hA0
    · exact hC
    · exact False.elim (hA hA0)
  change ((thetaSquareInt (directOrbitPairedDeepJetZ h v) : ℤ) : ZMod 7) = 0
  exact hC

theorem directOrbitPairedDeepJet_inverse_linear_mod_seven
    (v : SevenRealCubicIntˣ)
    (hlin : thetaLinearModSeven (v : SevenRealCubicInt) = 0) :
    thetaLinearModSeven
        ((v⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt) = 0 := by
  have hprod : thetaLinearModSeven
      (((v : SevenRealCubicIntˣ) : SevenRealCubicInt) *
        ((v⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt)) = 0 := by
    rw [← Units.val_mul]
    simp
  rw [thetaLinearModSeven_mul, hlin, zero_mul, add_zero] at hprod
  rcases mul_eq_zero.mp hprod with hzero | hzero
  · exact False.elim ((thetaConstModSeven_unit_ne_zero v) hzero)
  · exact hzero

theorem directOrbitPairedDeepJet_inverse_square_mod_seven
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p)
    (xi v : SevenRealCubicIntˣ)
    (hxi : h.squareRefinement.quotientSquareRoot =
      (xi : SevenRealCubicInt) * (h.v : SevenRealCubicInt))
    (hlin : thetaLinearModSeven (v : SevenRealCubicInt) = 0)
    (hzsq : thetaSquareModSeven (directOrbitPairedDeepJetZ h v) = 0) :
    thetaSquareModSeven
        ((v⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt) = 0 := by
  have hnot : ¬7 ∣ h.v := directOrbitPairedDeepJet_not_seven_v h xi hxi
  have hVmod : (h.v : ZMod 7) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact hnot
  have hlinInv := directOrbitPairedDeepJet_inverse_linear_mod_seven v hlin
  have hconstV2 :
      thetaConstModSeven ((h.v : SevenRealCubicInt) ^ 2) =
        (h.v : ZMod 7) ^ 2 := by
    rw [pow_two, thetaConstModSeven_mul]
    norm_num [thetaConstModSeven]
    ring
  have hlinV2 : thetaLinearModSeven ((h.v : SevenRealCubicInt) ^ 2) = 0 := by
    rw [pow_two, thetaLinearModSeven_mul]
    norm_num [thetaConstModSeven, thetaLinearModSeven]
  have hsqV2 : thetaSquareModSeven ((h.v : SevenRealCubicInt) ^ 2) = 0 := by
    rw [pow_two]
    norm_num [thetaSquareModSeven, SevenRealCubicInt.mul]
  have hprod :
      thetaSquareModSeven
          ((v⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt) *
        thetaConstModSeven ((h.v : SevenRealCubicInt) ^ 2) = 0 := by
    have htmp := hzsq
    rw [directOrbitPairedDeepJetZ, thetaSquareModSeven_mul,
      hlinInv, hlinV2, hsqV2] at htmp
    simpa using htmp
  rw [hconstV2] at hprod
  exact (mul_eq_zero.mp hprod).resolve_right (pow_ne_zero 2 hVmod)

theorem directOrbitPairedDeepJet_v_square_mod_seven
    (v : SevenRealCubicIntˣ)
    (hlin : thetaLinearModSeven (v : SevenRealCubicInt) = 0)
    (hinvsq : thetaSquareModSeven
      ((v⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt) = 0) :
    thetaSquareModSeven (v : SevenRealCubicInt) = 0 := by
  have hprod :
      thetaSquareModSeven (v : SevenRealCubicInt) *
        thetaConstModSeven
          ((v⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt) = 0 := by
    have htmp : thetaSquareModSeven
        (((v : SevenRealCubicIntˣ) : SevenRealCubicInt) *
          ((v⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt)) = 0 := by
      rw [← Units.val_mul]
      simp
    rw [thetaSquareModSeven_mul, hlin,
      directOrbitPairedDeepJet_inverse_linear_mod_seven v hlin,
      hinvsq] at htmp
    simpa using htmp
  exact (mul_eq_zero.mp hprod).resolve_right
    (thetaConstModSeven_unit_ne_zero v⁻¹)

theorem directOrbitPairedDeepJet_v_projective_log_zero
    (v : SevenRealCubicIntˣ)
    (hlin : thetaLinearModSeven (v : SevenRealCubicInt) = 0)
    (hsq : thetaSquareModSeven (v : SevenRealCubicInt) = 0) :
    projectiveLog (Additive.ofMul v) = 0 := by
  have hx : unitNilpotentX v = 0 := by
    simp [unitNilpotentX, hlin]
  have hy : unitNilpotentY v = 0 := by
    simp [unitNilpotentY, hsq]
  rw [projectiveLog_apply]
  simp [hx, hy]

theorem directOrbitPairedDeepJet_v_seventh_power
    (v : SevenRealCubicIntˣ)
    (hlin : thetaLinearModSeven (v : SevenRealCubicInt) = 0)
    (hsq : thetaSquareModSeven (v : SevenRealCubicInt) = 0) :
    ∃ w : SevenRealCubicIntˣ, v = w ^ 7 := by
  apply (unit_isSeventhPower_iff_projectiveLog_eq_zero v).mpr
  exact directOrbitPairedDeepJet_v_projective_log_zero v hlin hsq

theorem directOrbitPairedDeepJet_49th_power_correction
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
      directOrbitDeepJetRho * v ^ 7)
    (hlin : thetaLinearModSeven (v : SevenRealCubicInt) = 0) :
    ∃ w : SevenRealCubicIntˣ,
      directOrbitDeepJetWUnit h.squareRefinement eta =
          directOrbitDeepJetRho * v ^ 7 ∧
      thetaLinearModSeven (v : SevenRealCubicInt) = 0 ∧
      thetaSquareModSeven (v : SevenRealCubicInt) = 0 ∧
      projectiveLog (Additive.ofMul v) = 0 ∧
      v = w ^ 7 ∧
      directOrbitDeepJetWUnit h.squareRefinement eta =
        directOrbitDeepJetRho * w ^ 49 ∧
      h.squareRefinement.powerSplit.quotientCore =
        thetaSevenUnit * (directOrbitPairedDeepJetZ h v) ^ 7 := by
  have hvY := directOrbitPairedDeepJet_same_v_unit_identity
    h hc eta xi v heta hxi hv
  have hZsq := directOrbitPairedDeepJet_z_square_mod_seven
    h hc xi v hxi hvY hlin
  have hinvsq := directOrbitPairedDeepJet_inverse_square_mod_seven
    h xi v hxi hlin hZsq
  have hvsq := directOrbitPairedDeepJet_v_square_mod_seven
    v hlin hinvsq
  have hlog := directOrbitPairedDeepJet_v_projective_log_zero v hlin hvsq
  obtain ⟨w, hw⟩ := directOrbitPairedDeepJet_v_seventh_power v hlin hvsq
  have hquot := directOrbitPairedDeepJet_quotientCore_eq_theta_mul_Z_pow_seven
    h hc xi v hxi hvY
  refine ⟨w, hv, hlin, hvsq, hlog, hw, ?_, hquot⟩
  rw [hv, hw, ← pow_mul]

end SevenRealCubic
end
end DkMath.FLT.Seven
