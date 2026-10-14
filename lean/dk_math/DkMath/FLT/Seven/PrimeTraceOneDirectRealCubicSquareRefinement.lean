/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicWeightedGapObstruction
import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicSuccessorAudit

#print "file: DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicSquareRefinement"

namespace DkMath.FLT.Seven

noncomputable section

open SevenRealCubicInt
open scoped NumberField

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 200000

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-! ## Coprime roots and the scalar-square product -/

theorem directOrbitPowerSplit_roots_isCoprime
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (s : DirectOrbitPowerSplitPacket p) :
    IsCoprime s.gapRoot s.quotientRoot := by
  have hcores :
      IsCoprime
        ((s.gapUnit : SevenRealCubicInt) * s.gapRoot ^ 7)
        ((s.quotientUnit : SevenRealCubicInt) * s.quotientRoot ^ 7) := by
    simpa [s.gapCore_eq, s.quotientCore_eq] using s.cores_isCoprime
  have hpow : IsCoprime (s.gapRoot ^ 7) (s.quotientRoot ^ 7) :=
    (isCoprime_mul_units_left s.gapUnit.isUnit s.quotientUnit.isUnit
      (s.gapRoot ^ 7) (s.quotientRoot ^ 7)).mp hcores
  exact
    (IsCoprime.pow_iff (m := 7) (n := 7)
      (by norm_num) (by norm_num)).mp hpow

theorem directOrbitPowerSplit_rootProduct_isAssociated_scalarSquare
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (s : DirectOrbitPowerSplitPacket p) :
    ∃ u : SevenRealCubicIntˣ,
      s.gapRoot * s.quotientRoot =
        (u : SevenRealCubicInt) *
          (s.gapSplit.a : SevenRealCubicInt) ^ 2 := by
  let delta : SevenRealCubicIntˣ :=
    orbitUnit01Unit * (s.gapUnit * s.quotientUnit)⁻¹
  have hdelta_log :
      projectiveLog (Additive.ofMul delta) = 0 := by
    rw [show delta = orbitUnit01Unit *
        (s.gapUnit * s.quotientUnit)⁻¹ by rfl,
      ofMul_mul, map_add, ofMul_inv, map_neg, ofMul_mul, map_add,
      orbitUnit01_projectiveLog,
      directOrbitPowerSplit_gapUnit_projectiveLog s,
      directOrbitPowerSplit_quotientUnit_projectiveLog s]
    decide
  obtain ⟨w, hw⟩ :=
    (SevenRealCubic.unit_isSeventhPower_iff_projectiveLog_eq_zero delta).mpr
      hdelta_log
  let scalarSquare : SevenRealCubicInt :=
    thetaSevenUnit ^ (1 + 2 * s.gapSplit.k) *
      (s.gapSplit.a : SevenRealCubicInt) ^ 2
  have hcore_product :
      ((s.gapUnit * s.quotientUnit : SevenRealCubicInt) : SevenRealCubicInt) *
          (s.gapRoot * s.quotientRoot) ^ 7 =
        (orbitUnit01Unit : SevenRealCubicInt) * scalarSquare ^ 7 := by
    calc
      ((s.gapUnit * s.quotientUnit : SevenRealCubicInt) : SevenRealCubicInt) *
            (s.gapRoot * s.quotientRoot) ^ 7 =
          s.gapCore * s.quotientCore := by
            rw [s.gapCore_eq, s.quotientCore_eq]
            ring
      _ = (orbitUnit01Unit : SevenRealCubicInt) * scalarSquare ^ 7 := by
        simpa [scalarSquare, orbitUnit01Unit_val] using s.cores_product_eq
  have hdelta_rearrange :
      orbitUnit01Unit = delta * (s.gapUnit * s.quotientUnit) := by
    dsimp [delta]
    group
  have horbit :
      (orbitUnit01Unit : SevenRealCubicInt) =
        (w : SevenRealCubicInt) ^ 7 *
          ((s.gapUnit * s.quotientUnit : SevenRealCubicInt) : SevenRealCubicInt) := by
    rw [hdelta_rearrange, hw, Units.val_mul, Units.val_pow_eq_pow_val,
      Units.val_mul]
  have hpow :
      (s.gapRoot * s.quotientRoot) ^ 7 =
        ((w : SevenRealCubicInt) * scalarSquare) ^ 7 := by
    have hcancel :
        ((s.gapUnit * s.quotientUnit : SevenRealCubicInt) : SevenRealCubicInt) *
            (s.gapRoot * s.quotientRoot) ^ 7 =
          ((s.gapUnit * s.quotientUnit : SevenRealCubicInt) : SevenRealCubicInt) *
            ((w : SevenRealCubicInt) * scalarSquare) ^ 7 := by
      rw [hcore_product, horbit]
      ring
    have hu : IsUnit
        ((s.gapUnit * s.quotientUnit : SevenRealCubicInt) : SevenRealCubicInt) :=
      (s.gapUnit * s.quotientUnit).isUnit
    exact mul_left_cancel₀ hu.ne_zero hcancel
  let rootProductUnit : SevenRealCubicIntˣ :=
    w * thetaSevenUnit_isUnit.unit ^ (1 + 2 * s.gapSplit.k)
  have hbase :
      s.gapRoot * s.quotientRoot =
        (rootProductUnit : SevenRealCubicInt) *
          (s.gapSplit.a : SevenRealCubicInt) ^ 2 := by
    have hpow' :
        (s.gapRoot * s.quotientRoot) ^ 7 =
          ((rootProductUnit : SevenRealCubicInt) *
            (s.gapSplit.a : SevenRealCubicInt) ^ 2) ^ 7 := by
      simpa [rootProductUnit, scalarSquare,
        thetaSevenUnit_isUnit.unit_spec, Units.val_mul,
        Units.val_pow_eq_pow_val, mul_assoc, mul_left_comm, mul_comm] using hpow
    have hreal_inj : Function.Injective realEval := by
      intro a b hab
      have hfield :
          algebraMap (𝓞 SevenRealCubic.Field) SevenRealCubic.Field
              (SevenRealCubic.modelToRingOfIntegers a) =
            algebraMap (𝓞 SevenRealCubic.Field) SevenRealCubic.Field
              (SevenRealCubic.modelToRingOfIntegers b) := by
        apply realEmbedding.injective
        exact hab
      apply SevenRealCubic.modelToRingOfIntegers_injective
      exact NumberField.RingOfIntegers.coe_injective hfield
    apply hreal_inj
    apply (show Odd 7 by norm_num).pow_injective
    simpa only [map_pow] using congrArg realEval hpow'
  exact ⟨rootProductUnit, hbase⟩

private theorem directOrbit_associated_square_eq_unit_mul
    {a g : SevenRealCubicInt}
    (h : Associated (g ^ 2) a) :
    ∃ u : SevenRealCubicIntˣ, a = (u : SevenRealCubicInt) * g ^ 2 := by
  rcases h with ⟨u, hu⟩
  refine ⟨u, ?_⟩
  simpa [mul_comm] using hu.symm

/-! ## The square-refined current-provenance packet -/

structure DirectOrbitSquareRefinementPacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (base : DirectRealCubicRootPacket source r) where
  powerSplit : DirectOrbitPowerSplitPacket base
  roots_isCoprime :
    IsCoprime powerSplit.gapRoot powerSplit.quotientRoot
  rootProductUnit : SevenRealCubicIntˣ
  rootProduct_eq :
    powerSplit.gapRoot * powerSplit.quotientRoot =
      (rootProductUnit : SevenRealCubicInt) *
        (powerSplit.gapSplit.a : SevenRealCubicInt) ^ 2
  gapSquareRoot : SevenRealCubicInt
  quotientSquareRoot : SevenRealCubicInt
  gapSquareUnit : SevenRealCubicIntˣ
  quotientSquareUnit : SevenRealCubicIntˣ
  gapRoot_eq :
    powerSplit.gapRoot =
      (gapSquareUnit : SevenRealCubicInt) * gapSquareRoot ^ 2
  quotientRoot_eq :
    powerSplit.quotientRoot =
      (quotientSquareUnit : SevenRealCubicInt) * quotientSquareRoot ^ 2

theorem directOrbitSquareRefinement_nonempty
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectRealCubicRootPacket source r) :
    Nonempty (DirectOrbitSquareRefinementPacket p) := by
  let s := directOrbitPowerSplit p
  have hroots : IsCoprime s.gapRoot s.quotientRoot :=
    directOrbitPowerSplit_roots_isCoprime s
  obtain ⟨rootProductUnit, hrootProductEq⟩ :=
    directOrbitPowerSplit_rootProduct_isAssociated_scalarSquare s
  have hrootProductAssoc :
      Associated
        ((s.gapSplit.a : SevenRealCubicInt) ^ 2)
        (s.gapRoot * s.quotientRoot) := by
    rw [hrootProductEq]
    exact
      (associated_unit_mul_left ((s.gapSplit.a : SevenRealCubicInt) ^ 2)
        rootProductUnit rootProductUnit.isUnit).symm
  have hgapAssoc :
      ∃ g : SevenRealCubicInt, Associated (g ^ 2) s.gapRoot := by
    exact exists_associated_pow_of_associated_pow_mul
      (R := SevenRealCubicInt) (a := s.gapRoot) (b := s.quotientRoot)
      (c := s.gapSplit.a) (k := 2) hroots hrootProductAssoc
  have hquotAssoc :
      ∃ g : SevenRealCubicInt, Associated (g ^ 2) s.quotientRoot := by
    apply exists_associated_pow_of_associated_pow_mul
      (R := SevenRealCubicInt) (a := s.quotientRoot) (b := s.gapRoot)
      (c := s.gapSplit.a) (k := 2) hroots.symm
    simpa [mul_comm] using hrootProductAssoc
  obtain ⟨gapSquareRoot, hgap⟩ := hgapAssoc
  obtain ⟨quotientSquareRoot, hquotient⟩ := hquotAssoc
  obtain ⟨gapSquareUnit, hgapEq⟩ :=
    directOrbit_associated_square_eq_unit_mul hgap
  obtain ⟨quotientSquareUnit, hquotientEq⟩ :=
    directOrbit_associated_square_eq_unit_mul hquotient
  exact ⟨{
    powerSplit := s
    roots_isCoprime := hroots
    rootProductUnit := rootProductUnit
    rootProduct_eq := hrootProductEq
    gapSquareRoot := gapSquareRoot
    quotientSquareRoot := quotientSquareRoot
    gapSquareUnit := gapSquareUnit
    quotientSquareUnit := quotientSquareUnit
    gapRoot_eq := hgapEq
    quotientRoot_eq := hquotientEq }⟩

noncomputable def directOrbitSquareRefinement
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectRealCubicRootPacket source r) :
    DirectOrbitSquareRefinementPacket p :=
  Classical.choice (directOrbitSquareRefinement_nonempty p)

/-! ## Norm-square consequences -/

theorem directOrbitSquareRefinement_gap_norm_eq_square
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    Int.natAbs (norm t.powerSplit.gapRoot) =
      Int.natAbs (norm t.gapSquareRoot) ^ 2 := by
  rw [t.gapRoot_eq, SevenRealCubicInt.norm_mul,
    SevenRealCubicInt.norm_pow, Int.natAbs_mul,
    gapHeight_natAbs_norm_unit, one_mul, Int.natAbs_pow]

theorem directOrbitSquareRefinement_quotient_norm_eq_square
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    Int.natAbs (norm t.powerSplit.quotientRoot) =
      Int.natAbs (norm t.quotientSquareRoot) ^ 2 := by
  rw [t.quotientRoot_eq, SevenRealCubicInt.norm_mul,
    SevenRealCubicInt.norm_pow, Int.natAbs_mul,
    gapHeight_natAbs_norm_unit, one_mul, Int.natAbs_pow]

theorem directOrbitSquareRefinement_squareRoots_norm_mul_eq_cube
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    Int.natAbs (norm t.gapSquareRoot) *
        Int.natAbs (norm t.quotientSquareRoot) =
      t.powerSplit.gapSplit.a ^ 3 := by
  apply Nat.pow_left_injective (n := 2) (by decide : 2 ≠ 0)
  change
    (Int.natAbs (norm t.gapSquareRoot) *
        Int.natAbs (norm t.quotientSquareRoot)) ^ 2 =
      (t.powerSplit.gapSplit.a ^ 3) ^ 2
  calc
    (Int.natAbs (norm t.gapSquareRoot) *
        Int.natAbs (norm t.quotientSquareRoot)) ^ 2 =
        Int.natAbs (norm t.gapSquareRoot) ^ 2 *
          Int.natAbs (norm t.quotientSquareRoot) ^ 2 := by
            rw [Nat.mul_pow]
    _ = Int.natAbs (norm t.powerSplit.gapRoot) *
          Int.natAbs (norm t.powerSplit.quotientRoot) := by
            rw [directOrbitSquareRefinement_gap_norm_eq_square t,
              directOrbitSquareRefinement_quotient_norm_eq_square t]
    _ = t.powerSplit.gapSplit.a ^ 6 :=
      directOrbit_norm_complement_eq t.powerSplit
    _ = (t.powerSplit.gapSplit.a ^ 3) ^ 2 := by ring

theorem directOrbitSquareRefinement_gap_square_norm_pos
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    0 < Int.natAbs (norm t.gapSquareRoot) := by
  have hpos : 0 < Int.natAbs (norm t.powerSplit.gapRoot) :=
    directOrbit_gapRoot_norm_pos _ t.powerSplit
  rw [directOrbitSquareRefinement_gap_norm_eq_square t] at hpos
  by_contra hnot
  have hzero : Int.natAbs (norm t.gapSquareRoot) = 0 :=
    Nat.eq_zero_of_not_pos hnot
  rw [hzero] at hpos
  simp at hpos

theorem directOrbitSquareRefinement_gap_square_norm_lt_base
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    Int.natAbs (norm t.gapSquareRoot) ^ 2 < t.powerSplit.gapSplit.a := by
  calc
    Int.natAbs (norm t.gapSquareRoot) ^ 2 =
        Int.natAbs (norm t.powerSplit.gapRoot) :=
      (directOrbitSquareRefinement_gap_norm_eq_square t).symm
    _ < t.powerSplit.gapSplit.a :=
      directOrbit_gapRoot_norm_lt _ t.powerSplit

end
end DkMath.FLT.Seven
