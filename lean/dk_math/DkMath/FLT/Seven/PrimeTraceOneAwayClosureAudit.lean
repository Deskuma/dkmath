/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Prime.CounterexampleRouting
import DkMath.FLT.Seven.AwayValuationTransfer
import DkMath.FLT.Seven.DescentClosureAudit

#print "file: DkMath.FLT.Seven.PrimeTraceOneAwayClosureAudit"

namespace DkMath.FLT.Seven

open DkMath.CosmicFormula
open DkMath.CosmicFormulaBinom

/-- The existing specialized positive primitive packet, viewed through the
generic odd-prime p = 7 front door.  No endpoint or equation is changed. -/
theorem CounterexamplePack.toPrimitivePrimeCounterexample
    {x y z : ℕ} (hPack : CounterexamplePack x y z) :
    DkMath.FLT.Prime.PrimitivePrimeCounterexample 7 x y z :=
  { prime := by norm_num
    odd := by norm_num
    x_pos := hPack.hx
    y_pos := hPack.hy
    z_pos := hPack.hz
    coprime_x_y := hPack.hxy
    equation := by
      have h := hPack.hEq
      unfold Fermat7Equation at h
      exact h }

/-- The generic p = 7 away split, expressed with the promoted `GTail` API. -/
theorem CounterexamplePack.away_branch_power_factor_split_gtail
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hgap : ¬ 7 ∣ z - y) :
    (∃ a : ℕ, z - y = a ^ 7) ∧
      (∃ b : ℕ, GTail 7 1 (z - y) y = b ^ 7) := by
  exact DkMath.FLT.Prime.away_branch_power_factor_split
    hPack.toPrimitivePrimeCounterexample hgap

/-- At p = 7 the promoted `GTail` and legacy specialized `GN` split
propositions are definitionally the same proposition. -/
theorem counterexamplePack_away_split_gtail_iff_gn
    {y z : ℕ} :
    ((∃ a : ℕ, z - y = a ^ 7) ∧
      (∃ b : ℕ, GTail 7 1 (z - y) y = b ^ 7)) ↔
    ((∃ a : ℕ, z - y = a ^ 7) ∧
      (∃ b : ℕ, DkMath.CosmicFormulaBinom.GN 7 (z - y) y = b ^ 7)) := by
  rfl

/-- The generic and specialized away split theorems have the same
proposition-level content.  This does not identify independently chosen
existential witnesses. -/
theorem CounterexamplePack.away_branch_power_factor_split_iff_specialized
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hgap : ¬ 7 ∣ z - y) :
    ((∃ a : ℕ, z - y = a ^ 7) ∧
      (∃ b : ℕ, GTail 7 1 (z - y) y = b ^ 7)) ↔
    ((∃ a : ℕ, z - y = a ^ 7) ∧
      (∃ b : ℕ, DkMath.CosmicFormulaBinom.GN 7 (z - y) y = b ^ 7)) := by
  constructor
  · intro h
    exact branchAway_seventh_power_factor_split hPack hgap
  · intro h
    exact hPack.away_branch_power_factor_split_gtail hgap

/-- The existing element-level away normal form already implies the same
natural factor split; this is only an audit convenience, not a replacement
for its coordinate/root equalities. -/
theorem AwayCoordinateNormalForm.away_factor_split_gtail
    {x y z : ℕ} (p : AwayCoordinateNormalForm x y z) :
    (∃ a : ℕ, z - y = a ^ 7) ∧
      (∃ b : ℕ, GTail 7 1 (z - y) y = b ^ 7) := by
  exact p.counterexample.away_branch_power_factor_split_gtail
    p.seven_not_dvd_gap

end DkMath.FLT.Seven
