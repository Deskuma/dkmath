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

/-- At terminal depth one, the cubic root load remaining after removal of the
unique visible factor seven is itself a seven-adic unit. -/
theorem AwaySevenBaseTerminalQuotientCorePacket.seven_not_dvd_cubic_root_load
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalQuotientCorePacket source r p) :
    ¬ 7 ∣ r.cubic.rootTriple.vPart * r.cubic.rootTriple.leftPart *
      r.cubic.rootTriple.rightPart := by
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hvDepth : padicValNat 7 r.cubic.rootTriple.vPart = 0 := by
    calc
      padicValNat 7 r.cubic.rootTriple.vPart = p.exponent - 1 := p.root_depth_eq
      _ = 0 := by simp [packet.depth_eq_one]
  have hvNot : ¬ 7 ∣ r.cubic.rootTriple.vPart := by
    intro hv
    have hvne : r.cubic.rootTriple.vPart ≠ 0 :=
      Nat.ne_of_gt r.cubic.rootTriple.vPart_pos
    have hle : 1 ≤ padicValNat 7 r.cubic.rootTriple.vPart :=
      one_le_padicValNat_of_dvd hvne hv
    omega
  have hLRNot :
      ¬ 7 ∣ r.cubic.rootTriple.leftPart * r.cubic.rootTriple.rightPart := by
    rw [r.cubic.rootTriple.leftPart_eq, r.cubic.rootTriple.rightPart_eq,
      ← Int.natAbs_mul, ← seventhPowerSndCore_factor]
    exact r.cubic.rootTriple.normal.seven_not_dvd_natAbs_sndCore
  intro hload
  have hload' :
      7 ∣ r.cubic.rootTriple.vPart *
        (r.cubic.rootTriple.leftPart * r.cubic.rootTriple.rightPart) := by
    simpa only [mul_assoc] using hload
  rcases (by norm_num : Nat.Prime 7).dvd_mul.mp hload' with hv | hLR
  · exact hvNot hv
  · exact hLRNot hLR

end DkMath.FLT.Seven
