/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.RoutingLocalSolubility

#print "file: DkMath.FLT.Seven.LocalObstructionAudit"

namespace DkMath.FLT.Seven

inductive AwayNonSevenLocalSolubilitySource
    (q : ℕ) (row : EndpointRoutingRow) :
    RootRoutingColumn → Type
  | sevenV (solution : AwayRoutingLocalSolution q row .sevenV) :
      AwayNonSevenLocalSolubilitySource q row .sevenV
  | leftCubic (t : ZMod q) (root : leftCubicNormalizedZMod t = 0)
      (solution : AwayRoutingLocalSolution q row .leftCubic) :
      AwayNonSevenLocalSolubilitySource q row .leftCubic
  | rightCubic (t : ZMod q) (root : rightCubicNormalizedZMod t = 0)
      (solution : AwayRoutingLocalSolution q row .rightCubic) :
      AwayNonSevenLocalSolubilitySource q row .rightCubic

private theorem left_normalized_root_of_solution {q : ℕ} [Fact (Nat.Prime q)]
    {row : EndpointRoutingRow}
    (s : AwayRoutingLocalSolution q row .leftCubic) :
    leftCubicNormalizedZMod (s.u / s.v) = 0 := by
  have hv : s.v ≠ 0 := s.root_nonzero
  have hp : leftCubicZMod s.u s.v = 0 := s.root_equation
  rw [show leftCubicNormalizedZMod (s.u / s.v) =
      s.v⁻¹ ^ 3 * leftCubicZMod s.u s.v by
    simp [leftCubicNormalizedZMod, leftCubicZMod, div_eq_mul_inv]
    field_simp]
  rw [hp, mul_zero]

private theorem right_normalized_root_of_solution {q : ℕ} [Fact (Nat.Prime q)]
    {row : EndpointRoutingRow}
    (s : AwayRoutingLocalSolution q row .rightCubic) :
    rightCubicNormalizedZMod (s.u / s.v) = 0 := by
  have hv : s.v ≠ 0 := s.root_nonzero
  have hq : rightCubicZMod s.u s.v = 0 := s.root_equation
  rw [show rightCubicNormalizedZMod (s.u / s.v) =
      s.v⁻¹ ^ 3 * rightCubicZMod s.u s.v by
    simp [rightCubicNormalizedZMod, rightCubicZMod, div_eq_mul_inv]
    field_simp]
  rw [hq, mul_zero]

theorem localSolubilitySource_of_primeWitness {x y z : ℕ}
    {r : AwayCubicRoutingPacket x y z} (w : AwayRoutingPrimeWitness r)
    (hq7 : w.q ≠ 7) :
    Nonempty (AwayNonSevenLocalSolubilitySource w.q w.row w.column) := by
  let : Fact (Nat.Prime w.q) := ⟨w.q_prime⟩
  let actual := w.toLocalSolution hq7
  cases hc : w.column with
  | sevenV =>
      rcases nonempty_localSolution_sevenV (q := w.q) w.row with ⟨model⟩
      exact ⟨.sevenV model⟩
  | leftCubic =>
      have actualL : AwayRoutingLocalSolution w.q w.row .leftCubic := by
        simpa [hc] using actual
      let t := actualL.u / actualL.v
      have ht : leftCubicNormalizedZMod t = 0 :=
        left_normalized_root_of_solution actualL
      rcases nonempty_localSolution_leftCubic_of_root hq7 t ht w.row with ⟨model⟩
      exact ⟨.leftCubic t ht model⟩
  | rightCubic =>
      have actualR : AwayRoutingLocalSolution w.q w.row .rightCubic := by
        simpa [hc] using actual
      let t := actualR.u / actualR.v
      have ht : rightCubicNormalizedZMod t = 0 :=
        right_normalized_root_of_solution actualR
      rcases nonempty_localSolution_rightCubic_of_root hq7 t ht w.row with ⟨model⟩
      exact ⟨.rightCubic t ht model⟩

inductive FirstResidueLocalAuditResult (x y z : ℕ) : Type
  | ramified (packet : RamifiedCoordinateNormalForm x y z)
  | awayLocallySoluble
      (routing : AwayCubicRoutingPacket x y z)
      (constraints : AwayFirstCoordinateRoutingConstraints routing)
      (classification : ∀ w : AwayRoutingPrimeWitness routing, w.q ≠ 7 →
        Nonempty (AwayNonSevenLocalSolubilitySource w.q w.row w.column))

theorem firstResidueLocalAuditResult_of_pack {x y z : ℕ}
    (hPack : CounterexamplePack x y z) :
    Nonempty (FirstResidueLocalAuditResult x y z) := by
  rcases coordinateCounterexampleRoute_of_pack hPack with ⟨route⟩
  cases route with
  | ramified p => exact ⟨.ramified p⟩
  | away p =>
      rcases nonempty_awayCubicRoutingPacket p with ⟨routing⟩
      rcases nonempty_awayFirstCoordinateRoutingConstraints routing with ⟨constraints⟩
      exact ⟨.awayLocallySoluble routing constraints
        (fun w hq7 => localSolubilitySource_of_primeWitness w hq7)⟩

end DkMath.FLT.Seven
