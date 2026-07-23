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

/-- The selected endpoint factor contains the unique visible factor seven, so it
cannot divide the seven-adic-unit cubic root load. -/
theorem AwaySevenBaseTerminalQuotientCorePacket.selected_endpoint_not_dvd_cubic_root_load
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalQuotientCorePacket source r p) :
    ¬ endpointRoutingFactorNat y z p.row ∣
      r.cubic.rootTriple.vPart * r.cubic.rootTriple.leftPart *
        r.cubic.rootTriple.rightPart := by
  intro hselected
  have hseven : 7 ∣ endpointRoutingFactorNat y z p.row :=
    ⟨packet.carrier.carrierUnit, packet.carrier.carrier_eq⟩
  exact packet.seven_not_dvd_cubic_root_load (hseven.trans hselected)

/-- The terminal row completely separates endpoint divisibility of the cubic
root load: the indicated unselected endpoint divides the load, while the
seven-bearing selected endpoint does not. -/
theorem AwaySevenBaseTerminalUnitSectorPacket.row_resolved_terminal_load_routing_normal_form
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalUnitSectorPacket source r p) :
    (p.row = .y ∧
      z ∣ r.cubic.rootTriple.vPart * r.cubic.rootTriple.leftPart *
        r.cubic.rootTriple.rightPart ∧
      ¬ y ∣ r.cubic.rootTriple.vPart * r.cubic.rootTriple.leftPart *
        r.cubic.rootTriple.rightPart) ∨
    (p.row = .z ∧
      y ∣ r.cubic.rootTriple.vPart * r.cubic.rootTriple.leftPart *
        r.cubic.rootTriple.rightPart ∧
      ¬ z ∣ r.cubic.rootTriple.vPart * r.cubic.rootTriple.leftPart *
        r.cubic.rootTriple.rightPart) ∨
    (p.row = .sum ∧
      y ∣ r.cubic.rootTriple.vPart * r.cubic.rootTriple.leftPart *
        r.cubic.rootTriple.rightPart ∧
      ¬ y + z ∣ r.cubic.rootTriple.vPart * r.cubic.rootTriple.leftPart *
        r.cubic.rootTriple.rightPart) := by
  rcases packet.row_resolved_terminal_load_divisibility with hy | hz | hs
  · left
    refine ⟨hy.1, ?_, ?_⟩
    · exact_mod_cast hy.2
    · have hselected := packet.core.selected_endpoint_not_dvd_cubic_root_load
      simpa [endpointRoutingFactorNat, hy.1] using hselected
  · right
    left
    refine ⟨hz.1, ?_, ?_⟩
    · exact_mod_cast hz.2
    · have hselected := packet.core.selected_endpoint_not_dvd_cubic_root_load
      simpa [endpointRoutingFactorNat, hz.1] using hselected
  · right
    right
    refine ⟨hs.1, ?_, ?_⟩
    · exact_mod_cast hs.2
    · have hselected := packet.core.selected_endpoint_not_dvd_cubic_root_load
      simpa [endpointRoutingFactorNat, hs.1] using hselected

/-- The row-sensitive endpoint whose divisibility is forced into the cubic root
load by the terminal weighted bridge. -/
def awaySevenBaseTerminalUnselectedEndpointNat
    (row : EndpointRoutingRow) (y z : ℕ) : ℕ :=
  match row with
  | .y => z
  | .z | .sum => y

/-- Every prime carried by the unselected endpoint enters exactly one of the
three pairwise-coprime cubic root channels. -/
theorem AwaySevenBaseTerminalUnitSectorPacket.prime_dvd_unselected_endpoint_unique_cubic_channel
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalUnitSectorPacket source r p)
    {q : ℕ} (hq : Nat.Prime q)
    (hqunselected : q ∣ awaySevenBaseTerminalUnselectedEndpointNat p.row y z) :
    (q ∣ r.cubic.rootTriple.vPart ∧
      ¬ q ∣ r.cubic.rootTriple.leftPart ∧
      ¬ q ∣ r.cubic.rootTriple.rightPart) ∨
    (q ∣ r.cubic.rootTriple.leftPart ∧
      ¬ q ∣ r.cubic.rootTriple.vPart ∧
      ¬ q ∣ r.cubic.rootTriple.rightPart) ∨
    (q ∣ r.cubic.rootTriple.rightPart ∧
      ¬ q ∣ r.cubic.rootTriple.vPart ∧
      ¬ q ∣ r.cubic.rootTriple.leftPart) := by
  have hunselected :
      awaySevenBaseTerminalUnselectedEndpointNat p.row y z ∣
        r.cubic.rootTriple.vPart * r.cubic.rootTriple.leftPart *
          r.cubic.rootTriple.rightPart := by
    rcases packet.row_resolved_terminal_load_routing_normal_form with hy | hz | hs
    · simpa [awaySevenBaseTerminalUnselectedEndpointNat, hy.1] using hy.2.1
    · simpa [awaySevenBaseTerminalUnselectedEndpointNat, hz.1] using hz.2.1
    · simpa [awaySevenBaseTerminalUnselectedEndpointNat, hs.1] using hs.2.1
  have hqload :
      q ∣ r.cubic.rootTriple.vPart * r.cubic.rootTriple.leftPart *
        r.cubic.rootTriple.rightPart :=
    hqunselected.trans hunselected
  have hvl :
      ¬ (q ∣ r.cubic.rootTriple.vPart ∧ q ∣ r.cubic.rootTriple.leftPart) := by
    rintro ⟨hqv, hql⟩
    have hgcd := Nat.dvd_gcd hqv hql
    rw [r.cubic.rootTriple.coprime_v_left] at hgcd
    exact hq.not_dvd_one hgcd
  have hvr :
      ¬ (q ∣ r.cubic.rootTriple.vPart ∧ q ∣ r.cubic.rootTriple.rightPart) := by
    rintro ⟨hqv, hqr⟩
    have hgcd := Nat.dvd_gcd hqv hqr
    rw [r.cubic.rootTriple.coprime_v_right] at hgcd
    exact hq.not_dvd_one hgcd
  have hlr :
      ¬ (q ∣ r.cubic.rootTriple.leftPart ∧ q ∣ r.cubic.rootTriple.rightPart) := by
    rintro ⟨hql, hqr⟩
    have hgcd := Nat.dvd_gcd hql hqr
    rw [r.cubic.rootTriple.coprime_left_right] at hgcd
    exact hq.not_dvd_one hgcd
  rcases (Nat.Prime.dvd_mul hq).mp hqload with hqvl | hqr
  · rcases (Nat.Prime.dvd_mul hq).mp hqvl with hqv | hql
    · left
      exact ⟨hqv, fun h => hvl ⟨hqv, h⟩, fun h => hvr ⟨hqv, h⟩⟩
    · right
      left
      exact ⟨hql, fun h => hvl ⟨h, hql⟩, fun h => hlr ⟨hql, h⟩⟩
  · right
    right
    exact ⟨hqr, fun h => hvr ⟨h, hqr⟩, fun h => hlr ⟨h, hqr⟩⟩

end DkMath.FLT.Seven
