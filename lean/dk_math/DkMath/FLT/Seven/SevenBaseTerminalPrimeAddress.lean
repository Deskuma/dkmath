/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenBaseTerminalFixedRouting

#print "file: DkMath.FLT.Seven.SevenBaseTerminalPrimeAddress"

namespace DkMath.FLT.Seven

/-- The three endpoint-side factor rows of the fixed terminal routing board. -/
inductive AwaySevenBaseTerminalFactorRow : Type
  | carrier
  | unselected
  | companion
  deriving DecidableEq, Repr

/-- The endpoint-side factor represented by a fixed terminal routing row. -/
def awaySevenBaseTerminalFactorRowValue
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p)
    (row : AwaySevenBaseTerminalFactorRow) : ℕ :=
  match row with
  | .carrier => packet.core.carrier.carrierUnit
  | .unselected => awaySevenBaseTerminalUnselectedEndpointNat p.row y z
  | .companion => awaySevenBaseTerminalCompanionEndpointNat p.row y z

/-- A prime address on one fixed terminal routing board.  The source factor row
is explicit, while the disjunction records its unique cell inside that row and
the corresponding cubic root-load column. -/
def AwaySevenBaseTerminalFixedPrimeAddress
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p)
    (row : AwaySevenBaseTerminalFactorRow) (q : ℕ) : Prop :=
  match row with
  | .carrier =>
      (q ∣ packet.routing.c11 ∧ ¬ q ∣ packet.routing.c12 ∧
          ¬ q ∣ packet.routing.c13 ∧ q ∣ r.cubic.rootTriple.vPart) ∨
        (q ∣ packet.routing.c12 ∧ ¬ q ∣ packet.routing.c11 ∧
          ¬ q ∣ packet.routing.c13 ∧ q ∣ r.cubic.rootTriple.leftPart) ∨
        (q ∣ packet.routing.c13 ∧ ¬ q ∣ packet.routing.c11 ∧
          ¬ q ∣ packet.routing.c12 ∧ q ∣ r.cubic.rootTriple.rightPart)
  | .unselected =>
      (q ∣ packet.routing.c21 ∧ ¬ q ∣ packet.routing.c22 ∧
          ¬ q ∣ packet.routing.c23 ∧ q ∣ r.cubic.rootTriple.vPart) ∨
        (q ∣ packet.routing.c22 ∧ ¬ q ∣ packet.routing.c21 ∧
          ¬ q ∣ packet.routing.c23 ∧ q ∣ r.cubic.rootTriple.leftPart) ∨
        (q ∣ packet.routing.c23 ∧ ¬ q ∣ packet.routing.c21 ∧
          ¬ q ∣ packet.routing.c22 ∧ q ∣ r.cubic.rootTriple.rightPart)
  | .companion =>
      (q ∣ packet.routing.c31 ∧ ¬ q ∣ packet.routing.c32 ∧
          ¬ q ∣ packet.routing.c33 ∧ q ∣ r.cubic.rootTriple.vPart) ∨
        (q ∣ packet.routing.c32 ∧ ¬ q ∣ packet.routing.c31 ∧
          ¬ q ∣ packet.routing.c33 ∧ q ∣ r.cubic.rootTriple.leftPart) ∨
        (q ∣ packet.routing.c33 ∧ ¬ q ∣ packet.routing.c31 ∧
          ¬ q ∣ packet.routing.c32 ∧ q ∣ r.cubic.rootTriple.rightPart)

/-- Every prime carried by an explicitly selected endpoint-side factor row is
non-seven and has a unique cell address on the same fixed terminal board. -/
theorem AwaySevenBaseTerminalRoutingPacket.prime_dvd_factor_row_unique_address
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p)
    (row : AwaySevenBaseTerminalFactorRow)
    {q : ℕ} (hq : Nat.Prime q)
    (hqRow : q ∣ awaySevenBaseTerminalFactorRowValue packet row) :
    q ≠ 7 ∧ AwaySevenBaseTerminalFixedPrimeAddress packet row q := by
  cases row with
  | carrier =>
      simpa [awaySevenBaseTerminalFactorRowValue,
        AwaySevenBaseTerminalFixedPrimeAddress] using
        packet.prime_dvd_carrierUnit_unique_cell hq hqRow
  | unselected =>
      simpa [awaySevenBaseTerminalFactorRowValue,
        AwaySevenBaseTerminalFixedPrimeAddress] using
        packet.prime_dvd_unselected_endpoint_unique_cell hq hqRow
  | companion =>
      simpa [awaySevenBaseTerminalFactorRowValue,
        AwaySevenBaseTerminalFixedPrimeAddress] using
        packet.prime_dvd_companion_endpoint_unique_cell hq hqRow

/-- The complete endpoint-side product attached to one fixed terminal routing
board.  It is equal to the cubic root load by the terminal normal form. -/
def awaySevenBaseTerminalFactorProduct
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p) : ℕ :=
  packet.core.carrier.carrierUnit *
    awaySevenBaseTerminalUnselectedEndpointNat p.row y z *
    awaySevenBaseTerminalCompanionEndpointNat p.row y z

/-- A global prime address records that there is exactly one endpoint-side
factor row carrying the prime, and that this row gives its fixed cell and cubic
column address on the common terminal routing board. -/
def AwaySevenBaseTerminalGlobalPrimeAddress
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p)
    (q : ℕ) : Prop :=
  ∃! row : AwaySevenBaseTerminalFactorRow,
    q ∣ awaySevenBaseTerminalFactorRowValue packet row ∧
      AwaySevenBaseTerminalFixedPrimeAddress packet row q

/-- Every prime dividing the complete endpoint-side terminal product is
non-seven and has one globally unique row/cell/column address on the fixed
routing board. -/
theorem AwaySevenBaseTerminalRoutingPacket.prime_dvd_factorProduct_unique_global_address
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p)
    {q : ℕ} (hq : Nat.Prime q)
    (hqProduct : q ∣ awaySevenBaseTerminalFactorProduct packet) :
    q ≠ 7 ∧ AwaySevenBaseTerminalGlobalPrimeAddress packet q := by
  change q ∣ packet.core.carrier.carrierUnit *
    awaySevenBaseTerminalUnselectedEndpointNat p.row y z *
    awaySevenBaseTerminalCompanionEndpointNat p.row y z at hqProduct
  have hqRows :
      q ∣ packet.core.carrier.carrierUnit ∨
        q ∣ awaySevenBaseTerminalUnselectedEndpointNat p.row y z ∨
        q ∣ awaySevenBaseTerminalCompanionEndpointNat p.row y z := by
    rcases (Nat.Prime.dvd_mul hq).mp hqProduct with hqFirstTwo | hqCompanion
    · rcases (Nat.Prime.dvd_mul hq).mp hqFirstTwo with hqCarrier | hqUnselected
      · exact Or.inl hqCarrier
      · exact Or.inr (Or.inl hqUnselected)
    · exact Or.inr (Or.inr hqCompanion)
  have hnormal := packet.core.endpoint_carrier_root_load_normal_form
  have hcopUnselectedCompanion := hnormal.2.1
  have hcopUnselectedCarrier := hnormal.2.2.1
  have hcopCompanionCarrier := hnormal.2.2.2
  rcases hqRows with hqCarrier | hqUnselected | hqCompanion
  · have haddress :=
      packet.prime_dvd_factor_row_unique_address .carrier hq hqCarrier
    refine ⟨haddress.1, ?_⟩
    refine ⟨.carrier, ⟨hqCarrier, haddress.2⟩, ?_⟩
    intro row hrow
    cases row with
    | carrier => rfl
    | unselected =>
        exfalso
        have hqOther :
            q ∣ awaySevenBaseTerminalUnselectedEndpointNat p.row y z := by
          simpa [awaySevenBaseTerminalFactorRowValue] using hrow.1
        have hgcd := Nat.dvd_gcd hqOther hqCarrier
        rw [hcopUnselectedCarrier] at hgcd
        exact hq.not_dvd_one hgcd
    | companion =>
        exfalso
        have hqOther :
            q ∣ awaySevenBaseTerminalCompanionEndpointNat p.row y z := by
          simpa [awaySevenBaseTerminalFactorRowValue] using hrow.1
        have hgcd := Nat.dvd_gcd hqOther hqCarrier
        rw [hcopCompanionCarrier] at hgcd
        exact hq.not_dvd_one hgcd
  · have haddress :=
      packet.prime_dvd_factor_row_unique_address .unselected hq hqUnselected
    refine ⟨haddress.1, ?_⟩
    refine ⟨.unselected, ⟨hqUnselected, haddress.2⟩, ?_⟩
    intro row hrow
    cases row with
    | carrier =>
        exfalso
        have hqOther : q ∣ packet.core.carrier.carrierUnit := by
          simpa [awaySevenBaseTerminalFactorRowValue] using hrow.1
        have hgcd := Nat.dvd_gcd hqUnselected hqOther
        rw [hcopUnselectedCarrier] at hgcd
        exact hq.not_dvd_one hgcd
    | unselected => rfl
    | companion =>
        exfalso
        have hqOther :
            q ∣ awaySevenBaseTerminalCompanionEndpointNat p.row y z := by
          simpa [awaySevenBaseTerminalFactorRowValue] using hrow.1
        have hgcd := Nat.dvd_gcd hqUnselected hqOther
        rw [hcopUnselectedCompanion] at hgcd
        exact hq.not_dvd_one hgcd
  · have haddress :=
      packet.prime_dvd_factor_row_unique_address .companion hq hqCompanion
    refine ⟨haddress.1, ?_⟩
    refine ⟨.companion, ⟨hqCompanion, haddress.2⟩, ?_⟩
    intro row hrow
    cases row with
    | carrier =>
        exfalso
        have hqOther : q ∣ packet.core.carrier.carrierUnit := by
          simpa [awaySevenBaseTerminalFactorRowValue] using hrow.1
        have hgcd := Nat.dvd_gcd hqCompanion hqOther
        rw [hcopCompanionCarrier] at hgcd
        exact hq.not_dvd_one hgcd
    | unselected =>
        exfalso
        have hqOther :
            q ∣ awaySevenBaseTerminalUnselectedEndpointNat p.row y z := by
          simpa [awaySevenBaseTerminalFactorRowValue] using hrow.1
        have hgcd := Nat.dvd_gcd hqOther hqCompanion
        rw [hcopUnselectedCompanion] at hgcd
        exact hq.not_dvd_one hgcd
    | companion => rfl

end DkMath.FLT.Seven