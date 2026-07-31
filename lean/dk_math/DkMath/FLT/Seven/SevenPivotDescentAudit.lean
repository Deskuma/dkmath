/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenPivotPrimePowerSystem

#print "file: DkMath.FLT.Seven.SevenPivotDescentAudit"

namespace DkMath.FLT.Seven

inductive AwaySevenPivotLayerKind {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (p : AwaySevenPivotDepthPacket r) : Type
  | base (exponent_eq_one : p.exponent = 1)
  | lifted (one_lt_exponent : 1 < p.exponent)

def awaySevenPivotLayerKind {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (p : AwaySevenPivotDepthPacket r) : AwaySevenPivotLayerKind p := by
  by_cases h : p.exponent = 1
  · exact .base h
  · exact .lifted (by have := p.exponent_pos; omega)

structure AwaySevenBaseLayerPacket {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (p : AwaySevenPivotDepthPacket r) : Type where
  exponent_eq_one : p.exponent = 1
  solution : AwaySevenPivotPrimePowerSolution p.exponent p.row
  residueSector : AwayRootResidueSector x y z r.cubic.rootTriple.normal

def AwaySevenPivotDepthPacket.toBaseLayerPacket {x y z : ℕ}
    {r : AwayCubicRoutingPacket x y z} (p : AwaySevenPivotDepthPacket r)
    (h : p.exponent = 1) : AwaySevenBaseLayerPacket p where
  exponent_eq_one := h
  solution := p.toPrimePowerSolution
  residueSector := awayRootResidueSector_of_packet r.cubic.rootTriple.normal

private theorem seven_dvd_rootSnd_of_lifted {x y z : ℕ}
    {r : AwayCubicRoutingPacket x y z} (p : AwaySevenPivotDepthPacket r)
    (h : 1 < p.exponent) :
    (7 : ℤ) ∣ r.cubic.rootTriple.normal.root.snd := by
  have h7 : 7 ∣ p.lowerModulus := by
    refine dvd_pow_self 7 ?_
    have : 0 < p.exponent - 1 := by omega
    exact this.ne'
  exact (Int.natCast_dvd_natCast.mpr h7).trans (by
    apply intCast_dvd_of_dvd_natAbs
    simpa [← r.cubic.rootTriple.vPart_eq] using p.lowerModulus_dvd_vPart)

theorem AwaySevenPivotDepthPacket.rootFst_isUnit_of_lifted {x y z : ℕ}
    {r : AwayCubicRoutingPacket x y z} (p : AwaySevenPivotDepthPacket r)
    (h : 1 < p.exponent) :
    IsUnit (r.cubic.rootTriple.normal.root.fst : ZMod p.upperModulus) := by
  have hv := seven_dvd_rootSnd_of_lifted p h
  have hlin : ¬ (7 : ℤ) ∣
      r.cubic.rootTriple.normal.root.fst +
        4 * r.cubic.rootTriple.normal.root.snd := by
    apply seven_not_dvd_int_of_modSeven_ne_zero
    simpa [awayRootLinearModSeven] using
      r.cubic.rootTriple.normal.rootLinear_ne_zero
  have hu : ¬ (7 : ℤ) ∣ r.cubic.rootTriple.normal.root.fst := by
    intro hu
    exact hlin (hu.add (dvd_mul_of_dvd_right hv 4))
  change IsUnit ((r.cubic.rootTriple.normal.root.fst : ℤ) :
    ZMod (7 ^ p.exponent))
  exact intCast_isUnit_zmod_sevenPower (k := p.exponent) hu

private theorem rootSnd_seventh_dvd_upper {x y z : ℕ}
    {r : AwayCubicRoutingPacket x y z} (p : AwaySevenPivotDepthPacket r)
    (h : 1 < p.exponent) :
    (p.upperModulus : ℤ) ∣ r.cubic.rootTriple.normal.root.snd ^ 7 := by
  rcases p.lowerModulus_dvd_vPart with ⟨c, hc⟩
  have hsigned : (p.lowerModulus : ℤ) ∣
      r.cubic.rootTriple.normal.root.snd := by
    apply intCast_dvd_of_dvd_natAbs
    simpa [← r.cubic.rootTriple.vPart_eq] using ⟨c, hc⟩
  rcases hsigned with ⟨d, hd⟩
  obtain ⟨n, hn⟩ : ∃ n, p.exponent = n + 2 := by
    exact ⟨p.exponent - 2, by omega⟩
  refine ⟨(7 : ℤ) ^ (6*n + 5) * d^7, ?_⟩
  simp only [AwaySevenPivotDepthPacket.upperModulus,
    AwaySevenPivotDepthPacket.lowerModulus,
    AwaySevenPivotDepthPacket.lowerExponent] at hd ⊢
  rw [hn] at hd ⊢
  rw [hd, mul_pow]
  push_cast
  rw [← pow_mul]
  rw [show (n + 1) * 7 = (n + 2) + (6*n + 5) by omega, pow_add]
  ring

theorem AwaySevenPivotDepthPacket.rootSnd_seventh_eq_zero_of_lifted
    {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (p : AwaySevenPivotDepthPacket r) (h : 1 < p.exponent) :
    (r.cubic.rootTriple.normal.root.snd : ZMod p.upperModulus) ^ 7 = 0 := by
  simpa only [Int.cast_pow] using
    intCast_zero_of_dvd (rootSnd_seventh_dvd_upper p h)

inductive AwaySevenLiftedUnitOrbitClassification (M : ℕ)
    (row : EndpointRoutingRow) (u y z : ZMod M) : Type
  | y (row_eq : row = .y) (parametrization :
      Nonempty (ThreeSevenUnitParametrization (1 : ZMod M) u z)) :
      AwaySevenLiftedUnitOrbitClassification M row u y z
  | z (row_eq : row = .z) (parametrization :
      Nonempty (ThreeSevenUnitParametrization (1 : ZMod M) (-u) y)) :
      AwaySevenLiftedUnitOrbitClassification M row u y z
  | sum (row_eq : row = .sum) (parametrization :
      Nonempty (ThreeSevenUnitParametrization (1 : ZMod M) (-u) y)) :
      AwaySevenLiftedUnitOrbitClassification M row u y z

structure AwaySevenLiftedUnitOrbitPacket {x y z : ℕ}
    {r : AwayCubicRoutingPacket x y z} (p : AwaySevenPivotDepthPacket r) : Type where
  one_lt_exponent : 1 < p.exponent
  solution : AwaySevenPivotPrimePowerSolution p.exponent p.row
  rootSnd_seventh_eq_zero : solution.v ^ 7 = 0
  rootFst_isUnit : IsUnit solution.u
  classification : AwaySevenLiftedUnitOrbitClassification p.upperModulus p.row
    solution.u solution.y solution.z

def AwaySevenPivotDepthPacket.toLiftedUnitOrbitPacket {x y z : ℕ}
    {r : AwayCubicRoutingPacket x y z} (p : AwaySevenPivotDepthPacket r)
    (h : 1 < p.exponent) : AwaySevenLiftedUnitOrbitPacket p := by
  let s := p.toPrimePowerSolution
  have hv7 : s.v ^ 7 = 0 := p.rootSnd_seventh_eq_zero_of_lifted h
  have hu : IsUnit s.u := p.rootFst_isUnit_of_lifted h
  refine ⟨h, s, hv7, hu, ?_⟩
  have heq := s.first_coordinate_equation
  by_cases hy : p.row = .y
  · have hw : IsUnit s.z := by
      simpa [AwayEndpointPrimePowerNondegenerate, AwayEndpointLocalNondegenerate,
        hy] using s.endpoint_nondegenerate
    have heq' : s.u^7 + 4*s.v^7 - s.z^3 = 0 := by
      simpa [AwaySevenPivotFirstCoordinateEquation, hy] using heq
    have horbit : s.z^3 = s.u^7 := by
      rw [hv7] at heq'
      have hsub : s.u^7 - s.z^3 = 0 := by simpa using heq'
      exact (sub_eq_zero.mp hsub).symm
    exact .y hy (by
      convert unit_three_seven_parametrization (isUnit_one) hu hw
        (by simpa only [one_mul] using horbit) using 1; rfl)
  · by_cases hz : p.row = .z
    · have hw : IsUnit s.y := by
        simpa [AwayEndpointPrimePowerNondegenerate, AwayEndpointLocalNondegenerate,
          hy, hz] using s.endpoint_nondegenerate
      have heq' : s.u^7 + 4*s.v^7 + s.y^3 = 0 := by
        simpa [AwaySevenPivotFirstCoordinateEquation, hy, hz] using heq
      have horbit : s.y^3 = (-s.u)^7 := by
        rw [hv7] at heq'
        rw [show (-s.u)^7 = -s.u^7 by ring]
        linear_combination heq'
      exact .z hz (by
        convert unit_three_seven_parametrization (isUnit_one) hu.neg hw
          (by simpa only [one_mul] using horbit) using 1; rfl)
    · have hs : p.row = .sum := by
        cases hrow : p.row with
        | y => exact False.elim (hy hrow)
        | z => exact False.elim (hz hrow)
        | sum => exact rfl
      have hw : IsUnit s.y := by
        have hp : IsUnit s.y ∧ IsUnit s.z := by
          simpa [AwayEndpointPrimePowerNondegenerate, AwayEndpointLocalNondegenerate,
            hy, hz, hs] using s.endpoint_nondegenerate
        exact hp.1
      have heq' : s.u^7 + 4*s.v^7 + s.y^3 = 0 := by
        simpa [AwaySevenPivotFirstCoordinateEquation, hy, hz, hs] using heq
      have horbit : s.y^3 = (-s.u)^7 := by
        rw [hv7] at heq'
        rw [show (-s.u)^7 = -s.u^7 by ring]
        linear_combination heq'
      exact .sum hs (by
        convert unit_three_seven_parametrization (isUnit_one) hu.neg hw
          (by simpa only [one_mul] using horbit) using 1; rfl)

structure AwaySevenRamifiedKernelPacket {x y z : ℕ}
    {r : AwayCubicRoutingPacket x y z} (p : AwaySevenPivotDepthPacket r) : Type where
  unitPart : ℤ
  unitPart_not_seven_dvd : ¬ (7 : ℤ) ∣ unitPart
  rootSnd_eq : r.cubic.rootTriple.normal.root.snd =
    (7 ^ (p.exponent - 1) : ℤ) * unitPart
  unitPart_isUnit : IsUnit (unitPart : ZMod p.upperModulus)

theorem nonempty_awaySevenRamifiedKernelPacket {x y z : ℕ}
    {r : AwayCubicRoutingPacket x y z} (p : AwaySevenPivotDepthPacket r) :
    Nonempty (AwaySevenRamifiedKernelPacket p) := by
  have hd : (p.lowerModulus : ℤ) ∣ r.cubic.rootTriple.normal.root.snd := by
    apply intCast_dvd_of_dvd_natAbs
    simpa [← r.cubic.rootTriple.vPart_eq] using p.lowerModulus_dvd_vPart
  rcases hd with ⟨eta, heta⟩
  have hn : ¬ (7 : ℤ) ∣ eta := by
    intro h7
    apply p.upperModulus_not_dvd_vPart
    rw [r.cubic.rootTriple.vPart_eq]
    apply Int.natCast_dvd.mp
    rcases h7 with ⟨b, rfl⟩
    rw [heta]
    rw [p.upperModulus_eq_seven_mul_lowerModulus]
    push_cast
    exact ⟨b, by ring⟩
  refine ⟨⟨eta, hn, ?_, ?_⟩⟩
  · simpa [AwaySevenPivotDepthPacket.lowerModulus,
      AwaySevenPivotDepthPacket.lowerExponent] using heta
  · change IsUnit ((eta : ℤ) : ZMod (7 ^ p.exponent))
    exact intCast_isUnit_zmod_sevenPower (k := p.exponent) hn

structure AwaySevenTerminalExclusionStatement {x y z : ℕ}
    (source : CounterexamplePack x y z) {r : AwayCubicRoutingPacket x y z}
    (p : AwaySevenPivotDepthPacket r) : Type where
  depth_eq_one : p.exponent = 1
  exclusionObligation : Prop
  exclusionObligation_eq : exclusionObligation = ¬ Nonempty (CounterexamplePack x y z)

def awaySevenTerminalExclusionStatement {x y z : ℕ}
    (source : CounterexamplePack x y z) {r : AwayCubicRoutingPacket x y z}
    (p : AwaySevenPivotDepthPacket r) (h : p.exponent = 1) :
    AwaySevenTerminalExclusionStatement source p where
  depth_eq_one := h
  exclusionObligation := ¬ Nonempty (CounterexamplePack x y z)
  exclusionObligation_eq := rfl

structure AwaySevenLiftedReconstructionStatement {x y z : ℕ}
    (source : CounterexamplePack x y z) {r : AwayCubicRoutingPacket x y z}
    (p : AwaySevenPivotDepthPacket r) : Type where
  one_lt_depth : 1 < p.exponent
  targetCarrier : ℕ
  targetCarrier_eq : targetCarrier = Int.natAbs r.cubic.rootTriple.normal.root.snd
  reconstructionObligation : Prop
  reconstructionObligation_eq : reconstructionObligation =
    Nonempty (AwayDescentClosureProvider x y z r.cubic.transfer)

def awaySevenLiftedReconstructionStatement {x y z : ℕ}
    (source : CounterexamplePack x y z) {r : AwayCubicRoutingPacket x y z}
    (p : AwaySevenPivotDepthPacket r) (h : 1 < p.exponent) :
    AwaySevenLiftedReconstructionStatement source p where
  one_lt_depth := h
  targetCarrier := Int.natAbs r.cubic.rootTriple.normal.root.snd
  targetCarrier_eq := rfl
  reconstructionObligation := Nonempty
    (AwayDescentClosureProvider x y z r.cubic.transfer)
  reconstructionObligation_eq := rfl

inductive AwaySevenPivotDescentAuditResult {x y z : ℕ}
    (source : CounterexamplePack x y z) {r : AwayCubicRoutingPacket x y z}
    (p : AwaySevenPivotDepthPacket r) : Type
  | terminalOpen (layer : AwaySevenBaseLayerPacket p)
      (missing : AwaySevenTerminalExclusionStatement source p)
  | liftedClosed (provider : AwayDescentClosureProvider x y z r.cubic.transfer)
  | liftedOpen (layer : AwaySevenLiftedUnitOrbitPacket p)
      (kernel : AwaySevenRamifiedKernelPacket p)
      (missing : AwaySevenLiftedReconstructionStatement source p)

theorem nonempty_awaySevenPivotDescentAuditResult {x y z : ℕ}
    (source : CounterexamplePack x y z) {r : AwayCubicRoutingPacket x y z}
    (p : AwaySevenPivotDepthPacket r) :
    Nonempty (AwaySevenPivotDescentAuditResult source p) := by
  cases awaySevenPivotLayerKind p with
  | base h => exact ⟨.terminalOpen (p.toBaseLayerPacket h)
      (awaySevenTerminalExclusionStatement source p h)⟩
  | lifted h =>
      rcases nonempty_awaySevenRamifiedKernelPacket p with ⟨kernel⟩
      exact ⟨.liftedOpen (p.toLiftedUnitOrbitPacket h) kernel
        (awaySevenLiftedReconstructionStatement source p h)⟩

inductive SevenPivotSummitRoute (x y z : ℕ) : Type
  | ramified (packet : RamifiedCoordinateNormalForm x y z)
  | away (source : CounterexamplePack x y z)
      (routing : AwayCubicRoutingPacket x y z)
      (nonSevenClassification : ∀ p : AwayNonSevenPrimeDepthPacket routing,
        Nonempty (AwayNonSevenPrimePowerOrbitSource p p.column))
      (pivot : AwaySevenPivotDepthPacket routing)
      (solution : AwaySevenPivotPrimePowerSolution pivot.exponent pivot.row)
      (audit : AwaySevenPivotDescentAuditResult source pivot)

theorem sevenPivotSummitRoute_of_pack {x y z : ℕ}
    (source : CounterexamplePack x y z) : Nonempty (SevenPivotSummitRoute x y z) := by
  rcases coordinateCounterexampleRoute_of_pack source with ⟨route⟩
  cases route with
  | ramified packet => exact ⟨.ramified packet⟩
  | away packet =>
      rcases nonempty_awayCubicRoutingPacket packet with ⟨routing⟩
      rcases AwaySevenPivotDepthPacket.nonempty_awaySevenPivotDepthPacket routing with ⟨pivot⟩
      rcases nonempty_awaySevenPivotDescentAuditResult source pivot with ⟨audit⟩
      exact ⟨.away source routing (fun p => primePowerOrbitSource_of_depthPacket p)
        pivot pivot.toPrimePowerSolution audit⟩

end DkMath.FLT.Seven
