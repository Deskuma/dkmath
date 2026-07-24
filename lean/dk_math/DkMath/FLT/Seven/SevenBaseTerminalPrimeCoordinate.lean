/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenBaseTerminalRootLoadAddress

#print "file: DkMath.FLT.Seven.SevenBaseTerminalPrimeCoordinate"

namespace DkMath.FLT.Seven

/-- The three cubic root-load columns of the fixed terminal routing board. -/
inductive AwaySevenBaseTerminalRootColumn : Type
  | vPart
  | leftPart
  | rightPart
  deriving DecidableEq, Repr

/-- An explicit row/column prime coordinate on one fixed terminal routing board. -/
def AwaySevenBaseTerminalFixedPrimeCoordinate
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p)
    (row : AwaySevenBaseTerminalFactorRow)
    (column : AwaySevenBaseTerminalRootColumn) (q : ℕ) : Prop :=
  match row, column with
  | .carrier, .vPart =>
      q ∣ packet.routing.c11 ∧ ¬ q ∣ packet.routing.c12 ∧
        ¬ q ∣ packet.routing.c13 ∧ q ∣ r.cubic.rootTriple.vPart
  | .carrier, .leftPart =>
      q ∣ packet.routing.c12 ∧ ¬ q ∣ packet.routing.c11 ∧
        ¬ q ∣ packet.routing.c13 ∧ q ∣ r.cubic.rootTriple.leftPart
  | .carrier, .rightPart =>
      q ∣ packet.routing.c13 ∧ ¬ q ∣ packet.routing.c11 ∧
        ¬ q ∣ packet.routing.c12 ∧ q ∣ r.cubic.rootTriple.rightPart
  | .unselected, .vPart =>
      q ∣ packet.routing.c21 ∧ ¬ q ∣ packet.routing.c22 ∧
        ¬ q ∣ packet.routing.c23 ∧ q ∣ r.cubic.rootTriple.vPart
  | .unselected, .leftPart =>
      q ∣ packet.routing.c22 ∧ ¬ q ∣ packet.routing.c21 ∧
        ¬ q ∣ packet.routing.c23 ∧ q ∣ r.cubic.rootTriple.leftPart
  | .unselected, .rightPart =>
      q ∣ packet.routing.c23 ∧ ¬ q ∣ packet.routing.c21 ∧
        ¬ q ∣ packet.routing.c22 ∧ q ∣ r.cubic.rootTriple.rightPart
  | .companion, .vPart =>
      q ∣ packet.routing.c31 ∧ ¬ q ∣ packet.routing.c32 ∧
        ¬ q ∣ packet.routing.c33 ∧ q ∣ r.cubic.rootTriple.vPart
  | .companion, .leftPart =>
      q ∣ packet.routing.c32 ∧ ¬ q ∣ packet.routing.c31 ∧
        ¬ q ∣ packet.routing.c33 ∧ q ∣ r.cubic.rootTriple.leftPart
  | .companion, .rightPart =>
      q ∣ packet.routing.c33 ∧ ¬ q ∣ packet.routing.c31 ∧
        ¬ q ∣ packet.routing.c32 ∧ q ∣ r.cubic.rootTriple.rightPart

/-- A global prime coordinate exposes both the unique endpoint-side row and the
unique cubic root-load column of a prime on one fixed terminal board. -/
def AwaySevenBaseTerminalGlobalPrimeCoordinate
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p)
    (q : ℕ) : Prop :=
  ∃! row : AwaySevenBaseTerminalFactorRow,
    q ∣ awaySevenBaseTerminalFactorRowValue packet row ∧
      AwaySevenBaseTerminalFixedPrimeAddress packet row q ∧
      ∃! column : AwaySevenBaseTerminalRootColumn,
        AwaySevenBaseTerminalFixedPrimeCoordinate packet row column q

private theorem existsUnique_rootColumn_of_routed_prime
    {q c1 c2 c3 b1 b2 b3 : ℕ}
    (h :
      (q ∣ c1 ∧ ¬ q ∣ c2 ∧ ¬ q ∣ c3 ∧ q ∣ b1) ∨
      (q ∣ c2 ∧ ¬ q ∣ c1 ∧ ¬ q ∣ c3 ∧ q ∣ b2) ∨
      (q ∣ c3 ∧ ¬ q ∣ c1 ∧ ¬ q ∣ c2 ∧ q ∣ b3)) :
    ∃! column : AwaySevenBaseTerminalRootColumn,
      match column with
      | .vPart => q ∣ c1 ∧ ¬ q ∣ c2 ∧ ¬ q ∣ c3 ∧ q ∣ b1
      | .leftPart => q ∣ c2 ∧ ¬ q ∣ c1 ∧ ¬ q ∣ c3 ∧ q ∣ b2
      | .rightPart => q ∣ c3 ∧ ¬ q ∣ c1 ∧ ¬ q ∣ c2 ∧ q ∣ b3 := by
  rcases h with h1 | h2 | h3
  · refine ⟨.vPart, h1, ?_⟩
    intro column hcolumn
    cases column with
    | vPart => rfl
    | leftPart =>
        exfalso
        exact h1.2.1 hcolumn.1
    | rightPart =>
        exfalso
        exact h1.2.2.1 hcolumn.1
  · refine ⟨.leftPart, h2, ?_⟩
    intro column hcolumn
    cases column with
    | vPart =>
        exfalso
        exact h2.2.1 hcolumn.1
    | leftPart => rfl
    | rightPart =>
        exfalso
        exact h2.2.2.1 hcolumn.1
  · refine ⟨.rightPart, h3, ?_⟩
    intro column hcolumn
    cases column with
    | vPart =>
        exfalso
        exact h3.2.1 hcolumn.1
    | leftPart =>
        exfalso
        exact h3.2.2.1 hcolumn.1
    | rightPart => rfl

/-- The row-local disjunctive address determines one unique explicit cubic
column on the same fixed routing board. -/
theorem AwaySevenBaseTerminalRoutingPacket.existsUnique_rootColumn_of_fixedPrimeAddress
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p)
    (row : AwaySevenBaseTerminalFactorRow) {q : ℕ}
    (haddress : AwaySevenBaseTerminalFixedPrimeAddress packet row q) :
    ∃! column : AwaySevenBaseTerminalRootColumn,
      AwaySevenBaseTerminalFixedPrimeCoordinate packet row column q := by
  cases row with
  | carrier =>
      have h := haddress
      simp only [AwaySevenBaseTerminalFixedPrimeAddress] at h
      simpa [AwaySevenBaseTerminalFixedPrimeCoordinate] using
        existsUnique_rootColumn_of_routed_prime h
  | unselected =>
      have h := haddress
      simp only [AwaySevenBaseTerminalFixedPrimeAddress] at h
      simpa [AwaySevenBaseTerminalFixedPrimeCoordinate] using
        existsUnique_rootColumn_of_routed_prime h
  | companion =>
      have h := haddress
      simp only [AwaySevenBaseTerminalFixedPrimeAddress] at h
      simpa [AwaySevenBaseTerminalFixedPrimeCoordinate] using
        existsUnique_rootColumn_of_routed_prime h

/-- Every prime dividing the terminal cubic root load has one unique explicit
row/column coordinate on the fixed terminal routing board. -/
theorem AwaySevenBaseTerminalRoutingPacket.prime_dvd_cubicRootLoad_unique_global_coordinate
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p)
    {q : ℕ} (hq : Nat.Prime q)
    (hqLoad : q ∣ awaySevenBaseTerminalCubicRootLoad r) :
    q ≠ 7 ∧ AwaySevenBaseTerminalGlobalPrimeCoordinate packet q := by
  have hglobal := packet.prime_dvd_cubicRootLoad_unique_global_address hq hqLoad
  refine ⟨hglobal.1, ?_⟩
  rcases hglobal.2 with ⟨row, hrow, hrowUnique⟩
  refine ⟨row, ⟨hrow.1, hrow.2,
    packet.existsUnique_rootColumn_of_fixedPrimeAddress row hrow.2⟩, ?_⟩
  intro other hother
  exact hrowUnique other ⟨hother.1, hother.2.1⟩

end DkMath.FLT.Seven
