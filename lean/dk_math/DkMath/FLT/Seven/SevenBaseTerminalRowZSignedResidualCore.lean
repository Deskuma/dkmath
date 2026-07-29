/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenBaseTerminalRowZAlternatingPowerSplit

#print "file: DkMath.FLT.Seven.SevenBaseTerminalRowZSignedResidualCore"

namespace DkMath.FLT.Seven

open DkMath.NumberTheory.TraceOneQuadratic

local notation "tqNorm" => DkMath.NumberTheory.TraceOneQuadratic.norm

/-- A prime dividing both signed Row-Z cubic coordinates divides both original
positive endpoints. -/
theorem prime_dvd_both_rowZ_signed_cyclotomicSeven_coordinates
    {x y q : ℕ} (hq : Nat.Prime q)
    (hA : (q : ℤ) ∣ cyclotomicSevenFst (x : ℤ) (-(y : ℤ)))
    (hB : (q : ℤ) ∣ cyclotomicSevenSnd (x : ℤ) (-(y : ℤ))) :
    q ∣ x ∧ q ∣ y := by
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  have hAZ :
      (cyclotomicSevenFst (x : ℤ) (-(y : ℤ)) : ZMod q) = 0 :=
    (CharP.intCast_eq_zero_iff (ZMod q) q _).2 hA
  have hBZ :
      (cyclotomicSevenSnd (x : ℤ) (-(y : ℤ)) : ZMod q) = 0 :=
    (CharP.intCast_eq_zero_iff (ZMod q) q _).2 hB
  have hApoly :
      (x : ZMod q) ^ 3 - (x : ZMod q) ^ 2 * (y : ZMod q) +
        (y : ZMod q) ^ 3 = 0 := by
    calc
      (x : ZMod q) ^ 3 - (x : ZMod q) ^ 2 * (y : ZMod q) +
          (y : ZMod q) ^ 3 =
          (cyclotomicSevenFst (x : ℤ) (-(y : ℤ)) : ZMod q) := by
            simp [cyclotomicSevenFst]
            ring
      _ = 0 := hAZ
  have hBpoly :
      (x : ZMod q) * (y : ZMod q) *
        ((x : ZMod q) - (y : ZMod q)) = 0 := by
    calc
      (x : ZMod q) * (y : ZMod q) *
          ((x : ZMod q) - (y : ZMod q)) =
          (cyclotomicSevenSnd (x : ℤ) (-(y : ℤ)) : ZMod q) := by
            simp [cyclotomicSevenSnd]
            ring
      _ = 0 := hBZ
  have hXY : (x : ZMod q) = 0 ∧ (y : ZMod q) = 0 := by
    rcases mul_eq_zero.mp hBpoly with hxy | hdiff
    · rcases mul_eq_zero.mp hxy with hx | hy
      · rw [hx] at hApoly
        have hy3 : (y : ZMod q) ^ 3 = 0 := by simpa using hApoly
        exact ⟨hx, eq_zero_of_pow_eq_zero hy3⟩
      · rw [hy] at hApoly
        have hx3 : (x : ZMod q) ^ 3 = 0 := by simpa using hApoly
        exact ⟨eq_zero_of_pow_eq_zero hx3, hy⟩
    · have hxyEq : (x : ZMod q) = (y : ZMod q) := sub_eq_zero.mp hdiff
      rw [hxyEq] at hApoly
      have hy3 : (y : ZMod q) ^ 3 = 0 := by
        ring_nf at hApoly
        exact hApoly
      have hy : (y : ZMod q) = 0 := eq_zero_of_pow_eq_zero hy3
      exact ⟨hxyEq.trans hy, hy⟩
  exact ⟨(ZMod.natCast_eq_zero_iff x q).1 hXY.1,
    (ZMod.natCast_eq_zero_iff y q).1 hXY.2⟩

/-- Primitive natural endpoints give coprime signed Row-Z cubic coordinates.
-/
theorem rowZ_signed_cyclotomicSeven_coordinates_isCoprime
    {x y : ℕ} (hcop : Nat.Coprime x y) :
    IsCoprime
      (cyclotomicSevenFst (x : ℤ) (-(y : ℤ)))
      (cyclotomicSevenSnd (x : ℤ) (-(y : ℤ))) := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  by_contra hg
  rcases Nat.exists_prime_and_dvd hg with ⟨q, hq, hqgcd⟩
  have hqgcdInt : (q : ℤ) ∣
      (Int.gcd
        (cyclotomicSevenFst (x : ℤ) (-(y : ℤ)))
        (cyclotomicSevenSnd (x : ℤ) (-(y : ℤ))) : ℤ) :=
    Int.natCast_dvd_natCast.mpr hqgcd
  have hqA : (q : ℤ) ∣
      cyclotomicSevenFst (x : ℤ) (-(y : ℤ)) :=
    hqgcdInt.trans (Int.gcd_dvd_left _ _)
  have hqB : (q : ℤ) ∣
      cyclotomicSevenSnd (x : ℤ) (-(y : ℤ)) :=
    hqgcdInt.trans (Int.gcd_dvd_right _ _)
  rcases prime_dvd_both_rowZ_signed_cyclotomicSeven_coordinates
      hq hqA hqB with ⟨hqx, hqy⟩
  exact (Nat.not_coprime_of_dvd_of_dvd hq.one_lt hqx hqy) hcop

/-- The signed Row-Z cyclotomic coordinate after peeling its unique axis
factor, together with the exact natural seventh-power norm source. -/
structure AwaySevenBaseTerminalRowZSignedResidualCore
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {terminal : AwaySevenBaseTerminalUnitSectorPacket source r p}
    (hz : AwaySevenBaseTerminalRowZProfile terminal) : Type where
  powerSplit : AwaySevenBaseTerminalRowZAlternatingPowerSplit hz
  residualCore : TraceOneInt (-2)
  coordinate_eq :
    cyclotomicSevenToTraceOne (x : ℤ) (-(y : ℤ)) =
      sevenAxis * residualCore
  residual_ne_zero : residualCore ≠ 0
  residual_terminal : ¬ sevenAxis ∣ residualCore
  residual_norm_not_seven_dvd : ¬ (7 : ℤ) ∣ tqNorm residualCore
  residual_norm_eq : tqNorm residualCore = (powerSplit.b : ℤ) ^ 7
  residual_norm_pos : 1 ≤ tqNorm residualCore

/-- Construct the terminal signed residual core and identify its norm with the
alternating natural seventh-power split. -/
theorem nonempty_rowZSignedResidualCore
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {terminal : AwaySevenBaseTerminalUnitSectorPacket source r p}
    (hz : AwaySevenBaseTerminalRowZProfile terminal) :
    Nonempty (AwaySevenBaseTerminalRowZSignedResidualCore hz) := by
  let split := hz.alternatingPowerSplit
  have hyInt : ¬ (7 : ℤ) ∣ -(y : ℤ) := by
    simpa only [dvd_neg] using
      (show ¬ (7 : ℤ) ∣ (y : ℤ) by
        intro h
        exact hz.seven_not_dvd_y (Int.ofNat_dvd.mp h))
  rcases exists_cyclotomicSeven_terminal_core
      hz.seven_dvd_signed_gap hyInt with
    ⟨core, hcoordinate, hcore0, hterminal, hnorm7,
      hcycloNorm, hnormPos⟩
  have hAltInt :
      (alternatingCyclotomicSeven x y : ℤ) =
        7 * (split.b : ℤ) ^ 7 := by
    exact_mod_cast split.residual_eq
  have hnorm : tqNorm core = (split.b : ℤ) ^ 7 := by
    apply mul_left_cancel₀ (by norm_num : (7 : ℤ) ≠ 0)
    calc
      7 * tqNorm core =
          cyclotomicSeven (x : ℤ) (-(y : ℤ)) := hcycloNorm.symm
      _ = (alternatingCyclotomicSeven x y : ℤ) :=
        (alternatingCyclotomicSeven_intCast x y).symm
      _ = 7 * (split.b : ℤ) ^ 7 := hAltInt
  exact ⟨{
    powerSplit := split
    residualCore := core
    coordinate_eq := hcoordinate
    residual_ne_zero := hcore0
    residual_terminal := hterminal
    residual_norm_not_seven_dvd := hnorm7
    residual_norm_eq := hnorm
    residual_norm_pos := hnormPos }⟩

noncomputable def AwaySevenBaseTerminalRowZProfile.signedResidualCore
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {terminal : AwaySevenBaseTerminalUnitSectorPacket source r p}
    (hz : AwaySevenBaseTerminalRowZProfile terminal) :
    AwaySevenBaseTerminalRowZSignedResidualCore hz :=
  Classical.choice (nonempty_rowZSignedResidualCore hz)

/-- The signed Row-Z residual core is coprime to its conjugate. -/
theorem AwaySevenBaseTerminalRowZSignedResidualCore.gcd_conj_isUnit
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {terminal : AwaySevenBaseTerminalUnitSectorPacket source r p}
    {hz : AwaySevenBaseTerminalRowZProfile terminal}
    (q : AwaySevenBaseTerminalRowZSignedResidualCore hz) :
    IsUnit (gcd q.residualCore (conj q.residualCore)) := by
  let d := gcd q.residualCore (conj q.residualCore)
  let C := cyclotomicSevenToTraceOne (x : ℤ) (-(y : ℤ))
  have hdr : d ∣ q.residualCore := gcd_dvd_left _ _
  have hdrc : d ∣ conj q.residualCore := gcd_dvd_right _ _
  have hdC : d ∣ C := by
    dsimp [C]
    rw [q.coordinate_eq]
    exact dvd_mul_of_dvd_right hdr sevenAxis
  have hdConjC : d ∣ conj C := by
    dsimp [C]
    rw [q.coordinate_eq, traceOne_conj_mul, conj_sevenAxis]
    exact dvd_mul_of_dvd_right hdrc (-sevenAxis)
  have hcoords : IsCoprime C.fst C.snd := by
    simpa [C, cyclotomicSevenToTraceOne] using
      (rowZ_signed_cyclotomicSeven_coordinates_isCoprime source.hxy)
  have hdAxis : d ∣ sevenAxis :=
    common_divisor_dvd_sevenAxis_of_coordinate_coprime
      hcoords hdC hdConjC
  exact isUnit_of_dvd_sevenAxis_of_dvd_terminal
    hdAxis hdr q.residual_terminal

/-- The signed Row-Z terminal residual core is itself a seventh power in the
discriminant-minus-seven quadratic order. -/
theorem AwaySevenBaseTerminalRowZSignedResidualCore.exists_residualCore_eq_seventh_power
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {terminal : AwaySevenBaseTerminalUnitSectorPacket source r p}
    {hz : AwaySevenBaseTerminalRowZProfile terminal}
    (q : AwaySevenBaseTerminalRowZSignedResidualCore hz) :
    ∃ root : TraceOneInt (-2), q.residualCore = root ^ 7 := by
  have hmul : q.residualCore * conj q.residualCore =
      (q.powerSplit.b : TraceOneInt (-2)) ^ 7 := by
    rw [traceOne_mul_conj]
    rw [q.residual_norm_eq]
    change ((((q.powerSplit.b : ℤ) ^ 7 : ℤ)) : TraceOneInt (-2)) =
      ((q.powerSplit.b : ℤ) : TraceOneInt (-2)) ^ 7
    exact Int.cast_pow q.powerSplit.b 7
  exact exists_eq_seventh_power_of_coprime_mul_eq_pow
    q.gcd_conj_isUnit hmul

/-- TERM-010 endpoint: the Row-Z signed ramified arithmetic receiver isolated
by TERM-009 is inhabited. -/
theorem AwaySevenBaseTerminalRowZProfile.nonempty_signedRamifiedArithmeticObligation
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {terminal : AwaySevenBaseTerminalUnitSectorPacket source r p}
    (hz : AwaySevenBaseTerminalRowZProfile terminal) :
    Nonempty
      (AwaySevenBaseTerminalRowZSignedRamifiedArithmeticObligation hz) := by
  let q := hz.signedResidualCore
  rcases q.exists_residualCore_eq_seventh_power with ⟨root, hroot⟩
  exact ⟨⟨root, by rw [q.coordinate_eq, hroot]⟩⟩

/-- Canonical inhabitant of the TERM-009 Row-Z arithmetic receiver. -/
noncomputable def AwaySevenBaseTerminalRowZProfile.signedRamifiedArithmeticObligation
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {terminal : AwaySevenBaseTerminalUnitSectorPacket source r p}
    (hz : AwaySevenBaseTerminalRowZProfile terminal) :
    AwaySevenBaseTerminalRowZSignedRamifiedArithmeticObligation hz :=
  Classical.choice hz.nonempty_signedRamifiedArithmeticObligation

/-- TERM-010 closes the signed Row-Z chart all the way to its ramified
quadratic normal form. -/
noncomputable def AwaySevenBaseTerminalRowZProfile.signedRamified
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {terminal : AwaySevenBaseTerminalUnitSectorPacket source r p}
    (hz : AwaySevenBaseTerminalRowZProfile terminal) :
    SignedRamifiedCoordinateNormalForm
      (z : ℤ) (-(y : ℤ)) (x : ℤ) :=
  hz.to_signed_ramified hz.signedRamifiedArithmeticObligation

/-- After TERM-010 every surviving terminal away row reaches a ramified
quadratic chart, natural for Row Y and signed for Row Z. -/
inductive AwaySevenBaseTerminalRamifiedChartResolution
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (terminal : AwaySevenBaseTerminalUnitSectorPacket source r p) : Type
  | natural (packet : RamifiedCoordinateNormalForm y x z)
  | signed
      (packet :
        SignedRamifiedCoordinateNormalForm
          (z : ℤ) (-(y : ℤ)) (x : ℤ))

/-- TERM-010 terminal endpoint: the terminal away packet is normalized into
one of the two ramified quadratic charts. -/
noncomputable def
    AwaySevenBaseTerminalUnitSectorPacket.ramifiedChartResolution
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (terminal : AwaySevenBaseTerminalUnitSectorPacket source r p) :
    AwaySevenBaseTerminalRamifiedChartResolution terminal := by
  let resolution := Classical.choice terminal.fermatChartResolution
  cases resolution with
  | rowYRamified packet => exact .natural packet
  | rowZSigned packet => exact .signed packet.profile.signedRamified

end DkMath.FLT.Seven
