/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicOrbitGapHeight

#print "file: DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicSuccessorAudit"

namespace DkMath.FLT.Seven

noncomputable section

open SevenRealCubicInt

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 2000000

/-! ## Exact norm complement -/

theorem directOrbit_natAbs_norm_gapCore_root_eq
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (s : DirectOrbitPowerSplitPacket p) :
    Int.natAbs (norm s.gapCore) = Int.natAbs (norm s.gapRoot) ^ 7 := by
  rw [s.gapCore_eq, SevenRealCubicInt.norm_mul,
    SevenRealCubicInt.norm_pow, Int.natAbs_mul,
    gapHeight_natAbs_norm_unit, one_mul, Int.natAbs_pow]

theorem directOrbit_natAbs_norm_quotientCore_root_eq
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (s : DirectOrbitPowerSplitPacket p) :
    Int.natAbs (norm s.quotientCore) =
      Int.natAbs (norm s.quotientRoot) ^ 7 := by
  rw [s.quotientCore_eq, SevenRealCubicInt.norm_mul,
    SevenRealCubicInt.norm_pow, Int.natAbs_mul,
    gapHeight_natAbs_norm_unit, one_mul, Int.natAbs_pow]

theorem directOrbit_natAbs_norm_thetaSevenUnit_eq_one :
    Int.natAbs (norm thetaSevenUnit) = 1 := by
  simpa only [thetaSevenUnit_isUnit.unit_spec] using
    (gapHeight_natAbs_norm_unit thetaSevenUnit_isUnit.unit)

theorem directOrbit_natAbs_norm_orbitUnit01_eq_one :
    Int.natAbs (norm orbitUnit01) = 1 := by
  simpa only [orbitUnit01Unit_val] using
    (gapHeight_natAbs_norm_unit orbitUnit01Unit)

theorem directOrbit_norm_complement_pow_eq
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (s : DirectOrbitPowerSplitPacket p) :
    (Int.natAbs (norm s.gapRoot) *
        Int.natAbs (norm s.quotientRoot)) ^ 7 =
      s.gapSplit.a ^ 42 := by
  have h := congrArg (fun t : SevenRealCubicInt =>
      Int.natAbs (norm t)) s.cores_product_eq
  rw [SevenRealCubicInt.norm_mul, Int.natAbs_mul,
    directOrbit_natAbs_norm_gapCore_root_eq s,
    directOrbit_natAbs_norm_quotientCore_root_eq s] at h
  rw [SevenRealCubicInt.norm_mul, Int.natAbs_mul,
    directOrbit_natAbs_norm_orbitUnit01_eq_one, one_mul,
    SevenRealCubicInt.norm_pow, Int.natAbs_pow] at h
  simp only [SevenRealCubicInt.norm_mul, Int.natAbs_mul,
    SevenRealCubicInt.norm_pow, Int.natAbs_pow,
    directOrbit_natAbs_norm_thetaSevenUnit_eq_one] at h
  have hnorma :
      Int.natAbs (norm (s.gapSplit.a : SevenRealCubicInt)) ^ 2 =
        s.gapSplit.a ^ 6 := by
    have hnorm :
        norm (s.gapSplit.a : SevenRealCubicInt) =
          (s.gapSplit.a : ℤ) ^ 3 := by
      exact norm_intCast s.gapSplit.a
    rw [hnorm, Int.natAbs_pow, Int.natAbs_natCast]
    ring
  rw [hnorma] at h
  simp only [one_pow] at h
  calc
    (Int.natAbs (norm s.gapRoot) * Int.natAbs (norm s.quotientRoot)) ^ 7 =
        (s.gapSplit.a ^ 6) ^ 7 := by simpa [Nat.mul_pow] using h
    _ = s.gapSplit.a ^ 42 := by rw [← pow_mul]

theorem directOrbit_norm_complement_eq
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (s : DirectOrbitPowerSplitPacket p) :
    Int.natAbs (norm s.gapRoot) * Int.natAbs (norm s.quotientRoot) =
      s.gapSplit.a ^ 6 := by
  apply Nat.pow_left_injective (n := 7) (by decide : 7 ≠ 0)
  change (Int.natAbs (norm s.gapRoot) *
      Int.natAbs (norm s.quotientRoot)) ^ 7 =
    (s.gapSplit.a ^ 6) ^ 7
  calc
    _ = s.gapSplit.a ^ 42 := directOrbit_norm_complement_pow_eq s
    _ = (s.gapSplit.a ^ 6) ^ 7 := by rw [← pow_mul]

/-! ## Rotation of the exact gap split -/

noncomputable def directOrbitRotateUnit
    (u : SevenRealCubicIntˣ) : SevenRealCubicIntˣ :=
  Units.map rotateEquiv.toRingHom u

@[simp] theorem directOrbitRotateUnit_val (u : SevenRealCubicIntˣ) :
    (directOrbitRotateUnit u : SevenRealCubicInt) =
      rotateEquiv (u : SevenRealCubicInt) := by
  rfl

noncomputable def directOrbitPairAxisUnitOne : SevenRealCubicIntˣ :=
  alphaAddOne_isUnit.unit

@[simp] theorem directOrbitPairAxisUnitOne_val :
    (directOrbitPairAxisUnitOne : SevenRealCubicInt) = pairAxisUnit 1 := by
  rw [pairAxisUnit_one]
  exact alphaAddOne_isUnit.unit_spec

theorem directOrbit_rotate_axis_pow (e : ℕ) :
    rotateEquiv (eisensteinAxis ^ e) =
      eisensteinAxis ^ e *
        (directOrbitPairAxisUnitOne : SevenRealCubicInt) ^ e := by
  rw [map_pow, rotateEquiv_eisensteinAxis_mul_pairAxisUnit_one,
    directOrbitPairAxisUnitOne_val, mul_pow]

theorem directOrbit_rotate_axis_pow_hom (e : ℕ) :
    rotateHom (eisensteinAxis ^ e) =
      eisensteinAxis ^ e *
        (directOrbitPairAxisUnitOne : SevenRealCubicInt) ^ e := by
  simpa only [rotateEquiv_apply] using directOrbit_rotate_axis_pow e

theorem directOrbit_rotate_unit_hom_val (u : SevenRealCubicIntˣ) :
    rotateHom (u : SevenRealCubicInt) =
      (directOrbitRotateUnit u : SevenRealCubicInt) := by
  rfl

theorem directOrbit_rotate_twice_axis_pow (e : ℕ) :
    rotateEquiv (rotateEquiv (eisensteinAxis ^ e)) =
      eisensteinAxis ^ e *
        (directOrbitPairAxisUnitOne : SevenRealCubicInt) ^ e *
        (directOrbitRotateUnit directOrbitPairAxisUnitOne :
          SevenRealCubicInt) ^ e := by
  calc
    rotateEquiv (rotateEquiv (eisensteinAxis ^ e)) =
        rotateEquiv (eisensteinAxis ^ e *
          (directOrbitPairAxisUnitOne : SevenRealCubicInt) ^ e) := by
      rw [directOrbit_rotate_axis_pow]
    _ = rotateEquiv (eisensteinAxis ^ e) *
        rotateEquiv ((directOrbitPairAxisUnitOne : SevenRealCubicInt) ^ e) := by
      rw [map_mul]
    _ = eisensteinAxis ^ e *
        (directOrbitPairAxisUnitOne : SevenRealCubicInt) ^ e *
        (directOrbitRotateUnit directOrbitPairAxisUnitOne :
          SevenRealCubicInt) ^ e := by
      rw [directOrbit_rotate_axis_pow, map_pow,
        directOrbitRotateUnit_val]

noncomputable def directOrbitTwistedCoeff0
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (s : DirectOrbitPowerSplitPacket p) : SevenRealCubicIntˣ :=
  s.gapUnit

noncomputable def directOrbitTwistedCoeff1
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (s : DirectOrbitPowerSplitPacket p) : SevenRealCubicIntˣ :=
  directOrbitPairAxisUnitOne ^ (32 + 42 * s.gapSplit.k) *
    directOrbitRotateUnit s.gapUnit

noncomputable def directOrbitTwistedCoeff2
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (s : DirectOrbitPowerSplitPacket p) : SevenRealCubicIntˣ :=
  directOrbitPairAxisUnitOne ^ (32 + 42 * s.gapSplit.k) *
    directOrbitRotateUnit (directOrbitTwistedCoeff1 s)

theorem directOrbit_gap_split_eq
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (s : DirectOrbitPowerSplitPacket p) :
    directOrbitGap p =
      eisensteinAxis ^ (32 + 42 * s.gapSplit.k) *
        (directOrbitTwistedCoeff0 s : SevenRealCubicInt) * s.gapRoot ^ 7 := by
  rw [s.gap_eq, s.gapCore_eq]
  dsimp [directOrbitTwistedCoeff0]
  ring

theorem directOrbit_rotated_gap_split_one
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (s : DirectOrbitPowerSplitPacket p) :
    rotateEquiv p.rho - p.rho =
      eisensteinAxis ^ (32 + 42 * s.gapSplit.k) *
        (directOrbitTwistedCoeff0 s : SevenRealCubicInt) * s.gapRoot ^ 7 := by
  exact directOrbit_gap_split_eq s

theorem directOrbit_rotated_gap_split_two
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (s : DirectOrbitPowerSplitPacket p) :
    rotateEquiv (rotateEquiv p.rho) - rotateEquiv p.rho =
      eisensteinAxis ^ (32 + 42 * s.gapSplit.k) *
        (directOrbitTwistedCoeff1 s : SevenRealCubicInt) *
          (rotateEquiv s.gapRoot) ^ 7 := by
  let e := 32 + 42 * s.gapSplit.k
  have h := directOrbit_rotated_gap_split_one s
  have hr := congrArg rotateEquiv h
  calc
    rotateEquiv (rotateEquiv p.rho) - rotateEquiv p.rho =
        rotateEquiv (rotateEquiv p.rho - p.rho) := by
      rw [map_sub]
    _ = rotateEquiv (eisensteinAxis ^ e *
        (directOrbitTwistedCoeff0 s : SevenRealCubicInt) * s.gapRoot ^ 7) := hr
    _ = eisensteinAxis ^ e *
        (directOrbitTwistedCoeff1 s : SevenRealCubicInt) *
          (rotateEquiv s.gapRoot) ^ 7 := by
      dsimp [directOrbitTwistedCoeff0, directOrbitTwistedCoeff1]
      simp only [map_mul]
      change rotateEquiv (eisensteinAxis ^ e) *
        rotateEquiv (s.gapUnit : SevenRealCubicInt) *
          rotateEquiv (s.gapRoot ^ 7) = _
      rw [directOrbit_rotate_axis_pow, map_pow,
        directOrbitRotateUnit_val]
      have hk : e = 32 + s.gapSplit.k * 42 := by
        dsimp [e]
        ring
      have hepow :
          (directOrbitPairAxisUnitOne : SevenRealCubicInt) ^ e =
            (directOrbitPairAxisUnitOne : SevenRealCubicInt) ^ 32 *
              (directOrbitPairAxisUnitOne : SevenRealCubicInt) ^
                (s.gapSplit.k * 42) := by
        rw [hk, pow_add]
      rw [hepow]
      simp only [rotateEquiv_apply]
      ring

theorem directOrbit_rotated_gap_split_three
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (s : DirectOrbitPowerSplitPacket p) :
    p.rho - rotateEquiv (rotateEquiv p.rho) =
      eisensteinAxis ^ (32 + 42 * s.gapSplit.k) *
        (directOrbitTwistedCoeff2 s : SevenRealCubicInt) *
          (rotateEquiv (rotateEquiv s.gapRoot)) ^ 7 := by
  let e := 32 + 42 * s.gapSplit.k
  have h := directOrbit_rotated_gap_split_two s
  have hr := congrArg rotateEquiv h
  calc
    p.rho - rotateEquiv (rotateEquiv p.rho) =
        rotateEquiv (rotateEquiv (rotateEquiv p.rho) -
          rotateEquiv p.rho) := by
      rw [map_sub, rotateEquiv_three]
    _ = rotateEquiv (eisensteinAxis ^ e *
        (directOrbitTwistedCoeff1 s : SevenRealCubicInt) *
          (rotateEquiv s.gapRoot) ^ 7) := hr
    _ = eisensteinAxis ^ e *
        (directOrbitTwistedCoeff2 s : SevenRealCubicInt) *
          (rotateEquiv (rotateEquiv s.gapRoot)) ^ 7 := by
      dsimp [directOrbitTwistedCoeff2]
      simp only [map_mul]
      rw [directOrbit_rotate_axis_pow_hom, map_pow,
        directOrbit_rotate_unit_hom_val,
        directOrbitRotateUnit_val]
      have he : e = 32 + 42 * s.gapSplit.k := by rfl
      rw [he]
      ring

/-! ## Cyclic twisted seventh-power state -/

structure DirectRealCubicTwistedSeventhState where
  root : SevenRealCubicInt
  root1 : SevenRealCubicInt
  root2 : SevenRealCubicInt
  coeff0 : SevenRealCubicIntˣ
  coeff1 : SevenRealCubicIntˣ
  coeff2 : SevenRealCubicIntˣ
  root1_eq_rotate : root1 = rotateEquiv root
  root2_eq_rotate : root2 = rotateEquiv root1
  twisted_eq :
    (coeff0 : SevenRealCubicInt) * root ^ 7 +
      (coeff1 : SevenRealCubicInt) * root1 ^ 7 +
      (coeff2 : SevenRealCubicInt) * root2 ^ 7 = 0
  root_norm_pos : 0 < Int.natAbs (norm root)

theorem directOrbit_twisted_eq
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (s : DirectOrbitPowerSplitPacket p) :
    (directOrbitTwistedCoeff0 s : SevenRealCubicInt) * s.gapRoot ^ 7 +
      (directOrbitTwistedCoeff1 s : SevenRealCubicInt) *
          (rotateEquiv s.gapRoot) ^ 7 +
      (directOrbitTwistedCoeff2 s : SevenRealCubicInt) *
          (rotateEquiv (rotateEquiv s.gapRoot)) ^ 7 = 0 := by
  have h0 := directOrbit_rotated_gap_split_one s
  have h1 := directOrbit_rotated_gap_split_two s
  have h2 := directOrbit_rotated_gap_split_three s
  have ht :
      (rotateEquiv p.rho - p.rho) +
        (rotateEquiv (rotateEquiv p.rho) - rotateEquiv p.rho) +
        (p.rho - rotateEquiv (rotateEquiv p.rho)) = 0 := by ring
  have he : eisensteinAxis ^ (32 + 42 * s.gapSplit.k) ≠ 0 :=
    pow_ne_zero _ eisensteinAxis_prime.ne_zero
  apply (mul_left_cancel₀ he)
  rw [mul_zero]
  calc
    eisensteinAxis ^ (32 + 42 * s.gapSplit.k) *
        ((directOrbitTwistedCoeff0 s : SevenRealCubicInt) * s.gapRoot ^ 7 +
          (directOrbitTwistedCoeff1 s : SevenRealCubicInt) *
            (rotateEquiv s.gapRoot) ^ 7 +
          (directOrbitTwistedCoeff2 s : SevenRealCubicInt) *
            (rotateEquiv (rotateEquiv s.gapRoot)) ^ 7) =
        (rotateEquiv p.rho - p.rho) +
          (rotateEquiv (rotateEquiv p.rho) - rotateEquiv p.rho) +
          (p.rho - rotateEquiv (rotateEquiv p.rho)) := by
            rw [h0, h1, h2]
            ring
    _ = 0 := ht

theorem directOrbit_twisted_state_nonempty
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectRealCubicRootPacket source r) :
    Nonempty (DirectRealCubicTwistedSeventhState) := by
  let s := directOrbitPowerSplit p
  refine ⟨{
    root := s.gapRoot
    root1 := rotateEquiv s.gapRoot
    root2 := rotateEquiv (rotateEquiv s.gapRoot)
    coeff0 := directOrbitTwistedCoeff0 s
    coeff1 := directOrbitTwistedCoeff1 s
    coeff2 := directOrbitTwistedCoeff2 s
    root1_eq_rotate := rfl
    root2_eq_rotate := rfl
    twisted_eq := directOrbit_twisted_eq s
    root_norm_pos := directOrbit_gapRoot_norm_pos p s }⟩

noncomputable def directOrbitTwistedState
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectRealCubicRootPacket source r) :
    DirectRealCubicTwistedSeventhState :=
  let s := directOrbitPowerSplit p
  {
    root := s.gapRoot
    root1 := rotateEquiv s.gapRoot
    root2 := rotateEquiv (rotateEquiv s.gapRoot)
    coeff0 := directOrbitTwistedCoeff0 s
    coeff1 := directOrbitTwistedCoeff1 s
    coeff2 := directOrbitTwistedCoeff2 s
    root1_eq_rotate := rfl
    root2_eq_rotate := rfl
    twisted_eq := directOrbit_twisted_eq s
    root_norm_pos := directOrbit_gapRoot_norm_pos p s }

theorem directOrbit_twisted_state_measure_lt
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectRealCubicRootPacket source r) :
    Int.natAbs (norm (directOrbitTwistedState p).root) <
      r.summit.gapRoot := by
  let s := directOrbitPowerSplit p
  change Int.natAbs (norm s.gapRoot) < r.summit.gapRoot
  apply (directOrbit_gapRoot_norm_lt p s).trans_le
  rw [s.gapSplit.gap_eq]
  exact Nat.le_mul_of_pos_left _ (by positivity)

end
end DkMath.FLT.Seven
