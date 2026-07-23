/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenBaseTerminalWeightedBridge

#print "file: DkMath.FLT.Seven.SevenBaseTerminalLoadDivisibility"

namespace DkMath.FLT.Seven

/-- The residual quotient bridge and pairwise endpoint coprimality force the
unselected endpoint factor to divide the cubic root load.  The positive `Y`
row contributes `z`, while the two negative rows contribute `y`. -/
theorem AwaySevenBaseTerminalUnitSectorPacket.row_resolved_terminal_load_divisibility
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalUnitSectorPacket source r p) :
    (p.row = .y ∧
      (z : ℤ) ∣
        (r.cubic.rootTriple.vPart : ℤ) *
          (r.cubic.rootTriple.leftPart : ℤ) *
          (r.cubic.rootTriple.rightPart : ℤ)) ∨
    (p.row = .z ∧
      (y : ℤ) ∣
        (r.cubic.rootTriple.vPart : ℤ) *
          (r.cubic.rootTriple.leftPart : ℤ) *
          (r.cubic.rootTriple.rightPart : ℤ)) ∨
    (p.row = .sum ∧
      (y : ℤ) ∣
        (r.cubic.rootTriple.vPart : ℤ) *
          (r.cubic.rootTriple.leftPart : ℤ) *
          (r.cubic.rootTriple.rightPart : ℤ)) := by
  rcases packet.row_resolved_terminal_residual_quotient_bridge with
    ⟨q, _hq, hrows⟩
  have hcopYZ : IsCoprime (y : ℤ) (z : ℤ) := by
    rw [Int.isCoprime_iff_nat_coprime]
    simpa using r.cubic.endpointTriple.coprime_first_second
  rcases hrows with hy | hz | hs
  · left
    refine ⟨hy.1, ?_⟩
    have hcopZDiff : IsCoprime (z : ℤ) ((z : ℤ) - (y : ℤ)) := by
      rcases hcopYZ.symm with ⟨a, b, hab⟩
      refine ⟨a + b, -b, ?_⟩
      calc
        (a + b) * (z : ℤ) + (-b) * ((z : ℤ) - (y : ℤ)) =
            a * (z : ℤ) + b * (y : ℤ) := by ring
        _ = 1 := hab
    have hdiv :
        (z : ℤ) ∣ ((z : ℤ) - (y : ℤ)) *
          ((r.cubic.rootTriple.vPart : ℤ) *
            (r.cubic.rootTriple.leftPart : ℤ) *
            (r.cubic.rootTriple.rightPart : ℤ)) := by
      exact ⟨q, hy.2.symm⟩
    exact hcopZDiff.dvd_of_dvd_mul_left hdiv
  · right
    left
    refine ⟨hz.1, ?_⟩
    have hdiv :
        (y : ℤ) ∣ (z : ℤ) *
          ((r.cubic.rootTriple.vPart : ℤ) *
            (r.cubic.rootTriple.leftPart : ℤ) *
            (r.cubic.rootTriple.rightPart : ℤ)) := by
      exact ⟨q, hz.2.symm⟩
    exact hcopYZ.dvd_of_dvd_mul_left hdiv
  · right
    right
    refine ⟨hs.1, ?_⟩
    have hdiv :
        (y : ℤ) ∣ (z : ℤ) *
          ((r.cubic.rootTriple.vPart : ℤ) *
            (r.cubic.rootTriple.leftPart : ℤ) *
            (r.cubic.rootTriple.rightPart : ℤ)) := by
      exact ⟨q, hs.2.symm⟩
    exact hcopYZ.dvd_of_dvd_mul_left hdiv

end DkMath.FLT.Seven
