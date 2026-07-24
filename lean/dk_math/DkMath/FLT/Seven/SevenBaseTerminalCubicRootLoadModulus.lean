/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenBaseTerminalPrimePowerFiniteScaleReduction

#print "file: DkMath.FLT.Seven.SevenBaseTerminalCubicRootLoadModulus"

namespace DkMath.FLT.Seven

namespace AwayNonSevenPrimeDepthPacket

/-- The exact exponent of a non-seven original routing cell is also the exact
adic exponent of its prime in the complete cubic-root load. -/
theorem exponent_eq_padicValNat_cubicRootLoad
    {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (depth : AwayNonSevenPrimeDepthPacket r) :
    depth.exponent =
      padicValNat depth.q (awaySevenBaseTerminalCubicRootLoad r) := by
  letI : Fact (Nat.Prime depth.q) := ⟨depth.q_prime⟩
  have hv0 : r.cubic.rootTriple.vPart ≠ 0 :=
    r.cubic.rootTriple.vPart_pos.ne'
  have hl0 : r.cubic.rootTriple.leftPart ≠ 0 :=
    r.cubic.rootTriple.leftPart_pos.ne'
  have hr0 : r.cubic.rootTriple.rightPart ≠ 0 :=
    r.cubic.rootTriple.rightPart_pos.ne'
  have hq7 : ¬ depth.q ∣ 7 := by
    intro h
    apply depth.q_ne_seven
    exact ((Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp h).resolve_left
      depth.q_prime.ne_one
  have hroot := depth.depth.root_depth_eq
  change padicValNat depth.q (rootRoutingFactorNat r depth.column) =
    depth.exponent at hroot
  cases hcolumn : depth.column with
  | sevenV =>
      have hqroot : depth.q ∣ 7 * r.cubic.rootTriple.vPart := by
        simpa [rootRoutingFactorNat, hcolumn] using depth.q_dvd_root
      have hqv : depth.q ∣ r.cubic.rootTriple.vPart :=
        (depth.q_prime.dvd_mul.mp hqroot).resolve_left hq7
      have hql : ¬ depth.q ∣ r.cubic.rootTriple.leftPart := by
        intro h
        exact depth.q_prime.ne_one
          (Nat.eq_one_of_dvd_coprimes
            r.cubic.rootTriple.coprime_v_left hqv h)
      have hqr : ¬ depth.q ∣ r.cubic.rootTriple.rightPart := by
        intro h
        exact depth.q_prime.ne_one
          (Nat.eq_one_of_dvd_coprimes
            r.cubic.rootTriple.coprime_v_right hqv h)
      have hvDepth :
          padicValNat depth.q r.cubic.rootTriple.vPart = depth.exponent := by
        rw [hcolumn, rootRoutingFactorNat,
          padicValNat.mul (by norm_num : 7 ≠ 0) hv0,
          padicValNat.eq_zero_of_not_dvd hq7] at hroot
        omega
      rw [awaySevenBaseTerminalCubicRootLoad,
        padicValNat.mul (mul_ne_zero hv0 hl0) hr0,
        padicValNat.mul hv0 hl0,
        padicValNat.eq_zero_of_not_dvd hql,
        padicValNat.eq_zero_of_not_dvd hqr, ← hvDepth]
      omega
  | leftCubic =>
      have hql : depth.q ∣ r.cubic.rootTriple.leftPart := by
        simpa [rootRoutingFactorNat, hcolumn] using depth.q_dvd_root
      have hqv : ¬ depth.q ∣ r.cubic.rootTriple.vPart := by
        intro h
        exact depth.q_prime.ne_one
          (Nat.eq_one_of_dvd_coprimes
            r.cubic.rootTriple.coprime_v_left h hql)
      have hqr : ¬ depth.q ∣ r.cubic.rootTriple.rightPart := by
        intro h
        exact depth.q_prime.ne_one
          (Nat.eq_one_of_dvd_coprimes
            r.cubic.rootTriple.coprime_left_right hql h)
      have hlDepth :
          padicValNat depth.q r.cubic.rootTriple.leftPart = depth.exponent := by
        simpa [hcolumn, rootRoutingFactorNat] using hroot
      rw [awaySevenBaseTerminalCubicRootLoad,
        padicValNat.mul (mul_ne_zero hv0 hl0) hr0,
        padicValNat.mul hv0 hl0,
        padicValNat.eq_zero_of_not_dvd hqv,
        padicValNat.eq_zero_of_not_dvd hqr, ← hlDepth]
      omega
  | rightCubic =>
      have hqr : depth.q ∣ r.cubic.rootTriple.rightPart := by
        simpa [rootRoutingFactorNat, hcolumn] using depth.q_dvd_root
      have hqv : ¬ depth.q ∣ r.cubic.rootTriple.vPart := by
        intro h
        exact depth.q_prime.ne_one
          (Nat.eq_one_of_dvd_coprimes
            r.cubic.rootTriple.coprime_v_right h hqr)
      have hql : ¬ depth.q ∣ r.cubic.rootTriple.leftPart := by
        intro h
        exact depth.q_prime.ne_one
          (Nat.eq_one_of_dvd_coprimes
            r.cubic.rootTriple.coprime_left_right h hqr)
      have hrDepth :
          padicValNat depth.q r.cubic.rootTriple.rightPart = depth.exponent := by
        simpa [hcolumn, rootRoutingFactorNat] using hroot
      rw [awaySevenBaseTerminalCubicRootLoad,
        padicValNat.mul (mul_ne_zero hv0 hl0) hr0,
        padicValNat.mul hv0 hl0,
        padicValNat.eq_zero_of_not_dvd hqv,
        padicValNat.eq_zero_of_not_dvd hql, ← hrDepth]
      omega

end AwayNonSevenPrimeDepthPacket

/-- The complete original-cell exponent attached to a terminal prime equals
its adic exponent in the full terminal cubic-root load. -/
theorem AwaySevenBaseTerminalOriginalPrimeDepthPacket.exponent_eq_padicValNat_cubicRootLoad
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {q : ℕ} (depthPacket :
      AwaySevenBaseTerminalOriginalPrimeDepthPacket packet q) :
    depthPacket.depth.exponent =
      padicValNat q (awaySevenBaseTerminalCubicRootLoad r) := by
  exact depthPacket.depth.exponent_eq_padicValNat_cubicRootLoad.trans
    (congrArg
      (fun prime =>
        padicValNat prime (awaySevenBaseTerminalCubicRootLoad r))
      depthPacket.depth_q_eq)

/-- Family-level exponent transport from the selected original routing cell to
the complete terminal cubic-root load. -/
theorem AwaySevenBaseTerminalPrimeScaleFamily.localExponent_eq_padicValNat_cubicRootLoad
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    (family : AwaySevenBaseTerminalPrimeScaleFamily packet)
    (q : AwaySevenBaseTerminalPrimeIndex r) :
    (family.localDepth q).exponent =
      padicValNat q.1 (awaySevenBaseTerminalCubicRootLoad r) :=
  AwaySevenBaseTerminalOriginalPrimeDepthPacket.exponent_eq_padicValNat_cubicRootLoad
    (family.localPacket q).orbitPacket.depthPacket

/-- Consequently each local modulus is the full prime-power contribution of
its terminal prime to the cubic-root load. -/
theorem AwaySevenBaseTerminalPrimeScaleFamily.localModulus_eq_primePower_cubicRootLoad
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    (family : AwaySevenBaseTerminalPrimeScaleFamily packet)
    (q : AwaySevenBaseTerminalPrimeIndex r) :
    family.localModulus q =
      q.1 ^ padicValNat q.1 (awaySevenBaseTerminalCubicRootLoad r) := by
  calc
    family.localModulus q =
        (family.localDepth q).q ^ (family.localDepth q).exponent := rfl
    _ = q.1 ^ (family.localDepth q).exponent := by
      exact congrArg
        (fun prime => prime ^ (family.localDepth q).exponent)
        (family.localPacket q).orbitPacket.depthPacket.depth_q_eq
    _ = q.1 ^ padicValNat q.1 (awaySevenBaseTerminalCubicRootLoad r) := by
      rw [family.localExponent_eq_padicValNat_cubicRootLoad q]

/-- The product of all complete terminal local moduli reconstructs the entire
terminal cubic-root load exactly. -/
theorem AwaySevenBaseTerminalPrimeScaleFamily.combinedModulus_eq_cubicRootLoad
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    (family : AwaySevenBaseTerminalPrimeScaleFamily packet) :
    family.combinedModulus = awaySevenBaseTerminalCubicRootLoad r := by
  rw [combinedModulus]
  simp_rw [family.localModulus_eq_primePower_cubicRootLoad]
  change
    (∏ q : (awaySevenBaseTerminalCubicRootLoad r).primeFactors,
      q.1 ^ padicValNat q.1 (awaySevenBaseTerminalCubicRootLoad r)) =
        awaySevenBaseTerminalCubicRootLoad r
  calc
    _ = ∏ q : (awaySevenBaseTerminalCubicRootLoad r).primeFactors,
        q.1 ^ (awaySevenBaseTerminalCubicRootLoad r).factorization q.1 := by
      apply Fintype.prod_congr
      intro q
      rw [Nat.factorization_def _
        (Nat.prime_of_mem_primeFactors q.2)]
    _ = awaySevenBaseTerminalCubicRootLoad r :=
      (Nat.prod_pow_primeFactors_factorization
        (awaySevenBaseTerminalCubicRootLoad_ne_zero r)).symm

end DkMath.FLT.Seven
