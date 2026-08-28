/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenBaseTerminalRamifiedCanonicalSplit
import DkMath.FLT.Seven.QuadraticConjugateCoprime

#print "file: DkMath.FLT.Seven.SevenBaseTerminalRamifiedQuadraticInnerRoot"

namespace DkMath.FLT.Seven

open DkMath.NumberTheory.TraceOneQuadratic

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- A primitive quadratic integer of seven-unit norm is coprime to its
conjugate. -/
theorem PrimitiveRamifiedSummitPacket.root_gcd_conj_isUnit
    (p : PrimitiveRamifiedSummitPacket) :
    IsUnit (gcd p.root (conj p.root)) := by
  let d := gcd p.root (conj p.root)
  have hdr : d ∣ p.root := gcd_dvd_left _ _
  have hdrc : d ∣ conj p.root := gcd_dvd_right _ _
  have hdAxis : d ∣ sevenAxis :=
    common_divisor_dvd_sevenAxis_of_coordinate_coprime
      p.root_coordinates_isCoprime hdr hdrc
  exact isUnit_of_dvd_sevenAxis_of_dvd_terminal hdAxis hdr (by
    intro haxis
    exact p.root_norm_not_seven_dvd
      ((sevenAxis_dvd_iff_seven_dvd_norm p.root).mp haxis))

/-- Primitivity of the coordinates of a seventh power descends to its root. -/
theorem coordinates_isCoprime_of_pow_seven_coordinates_isCoprime
    (root : TraceOneInt (-2))
    (hpow : IsCoprime (root ^ 7).fst (root ^ 7).snd) :
    IsCoprime root.fst root.snd := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  by_contra hg
  rcases Nat.exists_prime_and_dvd hg with ⟨q, hq, hqg⟩
  have hqu : (q : ℤ) ∣ root.fst :=
    (Int.natCast_dvd_natCast.mpr hqg).trans (Int.gcd_dvd_left _ _)
  have hqv : (q : ℤ) ∣ root.snd :=
    (Int.natCast_dvd_natCast.mpr hqg).trans (Int.gcd_dvd_right _ _)
  rcases hqu with ⟨u, hu⟩
  rcases hqv with ⟨v, hv⟩
  have hqfst : (q : ℤ) ∣ seventhPowerFst root.fst root.snd := by
    refine ⟨q ^ 6 * (u ^ 7 - 42 * u ^ 5 * v ^ 2 -
      70 * u ^ 4 * v ^ 3 + 70 * u ^ 3 * v ^ 4 +
      126 * u ^ 2 * v ^ 5 + 14 * u * v ^ 6 - 10 * v ^ 7), ?_⟩
    simp [hu, hv, seventhPowerFst]
    ring
  have hqsnd : (q : ℤ) ∣ seventhPowerSnd root.fst root.snd := by
    refine ⟨q ^ 6 * (7 * u ^ 6 * v + 21 * u ^ 5 * v ^ 2 -
      35 * u ^ 4 * v ^ 3 - 105 * u ^ 3 * v ^ 4 -
      21 * u ^ 2 * v ^ 5 + 35 * u * v ^ 6 + 7 * v ^ 7), ?_⟩
    simp [hu, hv, seventhPowerSnd]
    ring
  have hunit : IsUnit (q : ℤ) := hpow.isUnit_of_dvd'
    (by
      simpa [show (root ^ 7).fst =
          seventhPowerFst root.fst root.snd by
        rcases root with ⟨a, b⟩
        exact traceOne_pow_seven_fst a b] using hqfst)
    (by
      simpa [show (root ^ 7).snd =
          seventhPowerSnd root.fst root.snd by
        rcases root with ⟨a, b⟩
        exact traceOne_pow_seven_snd a b] using hqsnd)
  rcases Int.isUnit_iff.mp hunit with hq1 | hqneg
  · exact hq.ne_one (by exact_mod_cast hq1)
  · have hqnonneg : (0 : ℤ) ≤ q := by positivity
    omega

/-- The second coordinate and the seventh-power second-coordinate core are
coprime for every primitive quadratic integer. -/
theorem rootSnd_sndCore_coprime_of_coordinates_isCoprime
    (root : TraceOneInt (-2))
    (hcoords : IsCoprime root.fst root.snd) :
    Nat.Coprime
      (Int.natAbs root.snd)
      (Int.natAbs (seventhPowerSndCore root.fst root.snd)) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hg
  rcases Nat.exists_prime_and_dvd hg with ⟨q, hq, hqg⟩
  have hqv : (q : ℤ) ∣ root.snd :=
    Int.natAbs_dvd_natAbs.mp
      (hqg.trans (Nat.gcd_dvd_left _ _))
  have hqS : (q : ℤ) ∣ seventhPowerSndCore root.fst root.snd :=
    Int.natAbs_dvd_natAbs.mp
      (hqg.trans (Nat.gcd_dvd_right _ _))
  have hrest : (q : ℤ) ∣
      seventhPowerSndCore root.fst root.snd - root.fst ^ 6 := by
    rcases hqv with ⟨k, hk⟩
    use
      3 * root.fst ^ 5 * k -
      5 * root.fst ^ 4 * (q : ℤ) * k ^ 2 -
      15 * root.fst ^ 3 * (q : ℤ) ^ 2 * k ^ 3 -
      3 * root.fst ^ 2 * (q : ℤ) ^ 3 * k ^ 4 +
      5 * root.fst * (q : ℤ) ^ 4 * k ^ 5 +
      (q : ℤ) ^ 5 * k ^ 6
    simp [seventhPowerSndCore, hk]
    ring
  have hqu6 : (q : ℤ) ∣ root.fst ^ 6 := by
    have := dvd_sub hqS hrest
    convert this using 1
    all_goals first | rfl | ring
  have hqu : (q : ℤ) ∣ root.fst :=
    (Nat.prime_iff_prime_int.mp hq).dvd_of_dvd_pow hqu6
  exact (Nat.prime_iff_prime_int.mp hq).not_unit
    (hcoords.isUnit_of_dvd' hqu hqv)

/-- The two cubic factors of the seventh-power second-coordinate core are
coprime for primitive coordinates of seven-unit norm. -/
theorem sndCore_cubic_factors_coprime
    (root : TraceOneInt (-2))
    (hcoords : IsCoprime root.fst root.snd)
    (hnorm : ¬ (7 : ℤ) ∣ norm root) :
    Nat.Coprime
      (Int.natAbs
        (seventhPowerSndLeftCubic root.fst root.snd))
      (Int.natAbs
        (seventhPowerSndRightCubic root.fst root.snd)) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hg
  rcases Nat.exists_prime_and_dvd hg with ⟨q, hq, hqg⟩
  let : Fact (Nat.Prime q) := ⟨hq⟩
  let u : ZMod q := root.fst
  let v : ZMod q := root.snd
  have hqL : (q : ℤ) ∣
      seventhPowerSndLeftCubic root.fst root.snd :=
    Int.natAbs_dvd_natAbs.mp
      (hqg.trans (Nat.gcd_dvd_left _ _))
  have hqR : (q : ℤ) ∣
      seventhPowerSndRightCubic root.fst root.snd :=
    Int.natAbs_dvd_natAbs.mp
      (hqg.trans (Nat.gcd_dvd_right _ _))
  have hL :
      u ^ 3 - 2 * u ^ 2 * v - u * v ^ 2 + v ^ 3 = 0 := by
    simpa [u, v, seventhPowerSndLeftCubic] using
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hqL
  have hR :
      u ^ 3 + 5 * u ^ 2 * v + 6 * u * v ^ 2 + v ^ 3 = 0 := by
    simpa [u, v, seventhPowerSndRightCubic] using
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hqR
  have hprimitive : ¬ (u = 0 ∧ v = 0) := by
    rintro ⟨hu, hv⟩
    rcases hcoords with ⟨a, b, hab⟩
    have hc := congrArg (fun n : ℤ => (n : ZMod q)) hab
    push_cast at hc
    simp [u, v, hu, hv] at hc
  have hfactor : (7 : ZMod q) * u * v * (u + v) = 0 := by
    linear_combination hR - hL
  have hqeq : q = 7 := by
    rcases mul_eq_zero.mp hfactor with huv | hsum
    · rcases mul_eq_zero.mp huv with h7u | hv
      · rcases mul_eq_zero.mp h7u with h7 | hu
        · have hq7 : q ∣ 7 :=
            (ZMod.natCast_eq_zero_iff 7 q).1 (by simpa using h7)
          exact (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hq7
            |>.resolve_left hq.ne_one
        · have hv0 : v = 0 := by
            rw [hu] at hL
            have hv3 : v ^ 3 = 0 := by simpa using hL
            exact eq_zero_of_pow_eq_zero hv3
          exact False.elim (hprimitive ⟨hu, hv0⟩)
      · have hu0 : u = 0 := by
          rw [hv] at hL
          simpa using eq_zero_of_pow_eq_zero
            (by simpa using hL : u ^ 3 = 0)
        exact False.elim (hprimitive ⟨hu0, hv⟩)
    · have hu : u = -v := eq_neg_of_add_eq_zero_left hsum
      have hv0 : v = 0 := by
        rw [hu] at hL
        ring_nf at hL
        exact eq_zero_of_pow_eq_zero (neg_eq_zero.mp hL)
      exact False.elim (hprimitive ⟨by simp [hu, hv0], hv0⟩)
  subst q
  let : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hnorm0 : (norm root : ZMod 7) = 0 := by
    have hadd :
        ((2 : ZMod 7) * u + v) * (norm root : ZMod 7) = 0 := by
      have hc := congrArg (fun n : ℤ => (n : ZMod 7))
        (seventhPowerSnd_cubic_add root.fst root.snd)
      push_cast at hc
      rw [(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hqL,
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hqR] at hc
      simpa [u, v] using hc
    rcases mul_eq_zero.mp hadd with hlin | hn
    · have hlinear :
          (root.fst : ZMod 7) + 4 * (root.snd : ZMod 7) = 0 := by
        dsimp [u, v] at hlin
        calc
          _ = (8 : ZMod 7) * (root.fst : ZMod 7) +
              4 * (root.snd : ZMod 7) := by
            rw [show (8 : ZMod 7) = 1 by decide]
            ring
          _ = 4 * (2 * (root.fst : ZMod 7) +
              (root.snd : ZMod 7)) := by ring
          _ = 0 := by rw [hlin]; ring
      rw [traceOneNorm_mod_seven_eq_linear_sq, hlinear]
      norm_num
    · exact hn
  exact hnorm ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hnorm0)

/-- Arithmetic kernel for the depth-four split: the prime-power load is
forced into the first of two coprime factors, after which the remaining
seventh power splits uniquely up to witnesses. -/
theorem seventh_power_split_after_seven_pow_four
    {N S M : ℕ}
    (hcop : Nat.Coprime N S)
    (hS7 : ¬ 7 ∣ S)
    (hEq : N * S = 7 ^ 4 * M ^ 7) :
    ∃ vertical horizontal : ℕ,
      N = 7 ^ 4 * vertical ^ 7 ∧
      S = horizontal ^ 7 := by
  have h7S : Nat.Coprime (7 ^ 4) S :=
    ((by norm_num : Nat.Prime 7).coprime_iff_not_dvd.mpr hS7).pow_left 4
  have hdivProd : 7 ^ 4 ∣ N * S := by
    rw [hEq]
    exact dvd_mul_right _ _
  rcases h7S.dvd_of_dvd_mul_right hdivProd with ⟨N₀, hN⟩
  have hReduced : N₀ * S = M ^ 7 := by
    apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 7 ^ 4)
    calc
      7 ^ 4 * (N₀ * S) = (7 ^ 4 * N₀) * S := by ring
      _ = N * S := by rw [hN]
      _ = 7 ^ 4 * M ^ 7 := hEq
  have hN₀dvd : N₀ ∣ N := by
    refine ⟨7 ^ 4, ?_⟩
    rw [hN]
    ring
  rcases seventh_power_factor_split
      (hcop.of_dvd_left hN₀dvd) hReduced with
    ⟨⟨vertical, hvertical⟩, ⟨horizontal, hhorizontal⟩⟩
  exact ⟨vertical, horizontal, by rw [hN, hvertical], hhorizontal⟩

/-- The receiver branch opens the quadratic root itself: the residual norm
key supplies a seventh-power norm, and primitive conjugate coprimality then
extracts an element-level seventh root. -/
structure RamifiedQuadraticInnerRootPacket : Type where
  canonical : RamifiedSecondCoordinateCanonicalSplit
  receiver : canonical.terminal.RamifiedCubicGapSeventhShapeReceiver
  compensationRoot : ℕ
  residualNormRoot : ℕ
  compensationCore_eq :
    canonical.compensationCore = compensationRoot ^ 7
  residualRoot_eq :
    canonical.terminal.summit.residualRoot = residualNormRoot ^ 7
  innerRoot : TraceOneInt (-2)
  root_eq :
    canonical.terminal.summit.root = innerRoot ^ 7

namespace RamifiedSecondCoordinateCanonicalSplit

/-- RAMIFIED-008 quadratic extraction packet for an inhabited receiver. -/
theorem nonempty_quadraticInnerRoot
    (p : RamifiedSecondCoordinateCanonicalSplit)
    (receiver : p.terminal.RamifiedCubicGapSeventhShapeReceiver) :
    Nonempty RamifiedQuadraticInnerRootPacket := by
  rcases (p.receiver_iff_independent_seventh_powers.mp receiver) with
    ⟨⟨c, hc⟩, ⟨b, hb⟩⟩
  have hmul :
      p.terminal.summit.root * conj p.terminal.summit.root =
        (b : TraceOneInt (-2)) ^ 7 := by
    rw [traceOne_mul_conj, p.terminal.summit.root_norm_eq, hb]
    change ((((b : ℤ) ^ 7 : ℤ)) : TraceOneInt (-2)) =
      (b : TraceOneInt (-2)) ^ 7
    norm_cast
  rcases exists_eq_seventh_power_of_coprime_mul_eq_pow
      p.terminal.summit.root_gcd_conj_isUnit hmul with
    ⟨innerRoot, hroot⟩
  exact ⟨{
    canonical := p
    receiver := receiver
    compensationRoot := c
    residualNormRoot := b
    compensationCore_eq := hc
    residualRoot_eq := hb
    innerRoot := innerRoot
    root_eq := hroot }⟩

end RamifiedSecondCoordinateCanonicalSplit

namespace RamifiedQuadraticInnerRootPacket

/-- The outer cyclotomic coordinate lies on a genuine forty-ninth-power
quadratic layer. -/
theorem coordinate_eq_fortyNine
    (p : RamifiedQuadraticInnerRootPacket) :
    cyclotomicSevenToTraceOne
        p.canonical.terminal.summit.endpointLeft
        p.canonical.terminal.summit.endpointRight =
      sevenAxis * p.innerRoot ^ 49 := by
  calc
    _ = sevenAxis * p.canonical.terminal.summit.root ^ 7 :=
      p.canonical.terminal.summit.coordinate_eq
    _ = sevenAxis * (p.innerRoot ^ 7) ^ 7 := by rw [p.root_eq]
    _ = sevenAxis * p.innerRoot ^ 49 := by
      rw [← pow_mul]

/-- The extracted quadratic root retains primitive integer coordinates. -/
theorem innerRoot_coordinates_isCoprime
    (p : RamifiedQuadraticInnerRootPacket) :
    IsCoprime p.innerRoot.fst p.innerRoot.snd := by
  apply coordinates_isCoprime_of_pow_seven_coordinates_isCoprime
  rw [← p.root_eq]
  exact p.canonical.terminal.summit.root_coordinates_isCoprime

/-- The extracted root has exactly the receiver's residual norm root as its
positive norm. -/
theorem innerRoot_norm_eq
    (p : RamifiedQuadraticInnerRootPacket) :
    norm p.innerRoot = p.residualNormRoot := by
  have hpows :
      norm p.innerRoot ^ 7 = (p.residualNormRoot : ℤ) ^ 7 := by
    calc
      _ = norm (p.innerRoot ^ 7) :=
        (traceOne_norm_pow_ramified p.innerRoot 7).symm
      _ = norm p.canonical.terminal.summit.root := by rw [← p.root_eq]
      _ = p.canonical.terminal.summit.residualRoot :=
        p.canonical.terminal.summit.root_norm_eq
      _ = _ := by rw [p.residualRoot_eq]; norm_num
  have hnonneg : 0 ≤ norm p.innerRoot :=
    traceOneNegTwo_norm_nonneg p.innerRoot
  have habspows :
      Int.natAbs (norm p.innerRoot) ^ 7 = p.residualNormRoot ^ 7 := by
    rw [← Int.natAbs_pow, hpows]
    simp
  have habs :
      Int.natAbs (norm p.innerRoot) = p.residualNormRoot :=
    Nat.pow_left_injective (by decide : 7 ≠ 0) habspows
  calc
    norm p.innerRoot = (Int.natAbs (norm p.innerRoot) : ℤ) :=
      (Int.natAbs_of_nonneg hnonneg).symm
    _ = p.residualNormRoot := congrArg Nat.cast habs

/-- The inner norm remains a seven-unit. -/
theorem innerRoot_norm_not_seven_dvd
    (p : RamifiedQuadraticInnerRootPacket) :
    ¬ (7 : ℤ) ∣ norm p.innerRoot := by
  rw [p.innerRoot_norm_eq]
  intro h
  apply p.canonical.terminal.summit.residualRoot_not_seven_dvd
  rw [p.residualRoot_eq]
  exact dvd_pow (Int.ofNat_dvd.mp h) (by norm_num)

/-- The outer second coordinate is the seventh-power second coordinate of
the extracted inner root. -/
theorem rootSnd_eq_seventhPowerSnd
    (p : RamifiedQuadraticInnerRootPacket) :
    p.canonical.terminal.summit.root.snd =
      seventhPowerSnd p.innerRoot.fst p.innerRoot.snd := by
  have h := congrArg TraceOneInt.snd p.root_eq
  simpa [show (p.innerRoot ^ 7).snd =
      seventhPowerSnd p.innerRoot.fst p.innerRoot.snd by
    rcases p.innerRoot with ⟨a, b⟩
    exact traceOne_pow_seven_snd a b] using h

/-- Receiver normalization of the outer second coordinate, with its two
seventh-power factors merged. -/
theorem rootSnd_natAbs_eq
    (p : RamifiedQuadraticInnerRootPacket) :
    Int.natAbs p.canonical.terminal.summit.root.snd =
      7 ^ 5 *
        (p.canonical.verticalGapRoot * p.compensationRoot) ^ 7 := by
  calc
    _ = 7 ^ 5 * p.canonical.verticalGapRoot ^ 7 *
        p.canonical.compensationCore := p.canonical.rootSnd_eq
    _ = _ := by rw [p.compensationCore_eq]; ring

theorem innerRoot_snd_ne_zero
    (p : RamifiedQuadraticInnerRootPacket) :
    p.innerRoot.snd ≠ 0 := by
  intro hv
  apply p.canonical.terminal.summit.root_snd_ne_zero
  rw [p.rootSnd_eq_seventhPowerSnd, hv]
  simp [seventhPowerSnd]

theorem innerSndCore_not_seven_dvd
    (p : RamifiedQuadraticInnerRootPacket) :
    ¬ (7 : ℤ) ∣
      seventhPowerSndCore p.innerRoot.fst p.innerRoot.snd :=
  seven_not_dvd_seventhPowerSndCore_of_norm
    p.innerRoot_norm_not_seven_dvd

theorem innerSndCore_ne_zero
    (p : RamifiedQuadraticInnerRootPacket) :
    seventhPowerSndCore p.innerRoot.fst p.innerRoot.snd ≠ 0 := by
  intro h
  exact p.innerSndCore_not_seven_dvd (by rw [h]; exact dvd_zero 7)

theorem innerRootSnd_innerSndCore_coprime
    (p : RamifiedQuadraticInnerRootPacket) :
    Nat.Coprime
      (Int.natAbs p.innerRoot.snd)
      (Int.natAbs
        (seventhPowerSndCore p.innerRoot.fst p.innerRoot.snd)) :=
  rootSnd_sndCore_coprime_of_coordinates_isCoprime
    p.innerRoot p.innerRoot_coordinates_isCoprime

/-- Exact inner second-coordinate product after cancelling the visible
factor seven. -/
theorem inner_secondCoordinate_product_eq
    (p : RamifiedQuadraticInnerRootPacket) :
    Int.natAbs p.innerRoot.snd *
        Int.natAbs
          (seventhPowerSndCore p.innerRoot.fst p.innerRoot.snd) =
      7 ^ 4 *
        (p.canonical.verticalGapRoot * p.compensationRoot) ^ 7 := by
  apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 7)
  calc
    7 * (Int.natAbs p.innerRoot.snd *
        Int.natAbs
          (seventhPowerSndCore p.innerRoot.fst p.innerRoot.snd)) =
      Int.natAbs
        (seventhPowerSnd p.innerRoot.fst p.innerRoot.snd) := by
          rw [seventhPowerSnd_eq_seven_mul, Int.natAbs_mul,
            Int.natAbs_mul]
          norm_num
          ring
    _ = Int.natAbs p.canonical.terminal.summit.root.snd := by
      rw [p.rootSnd_eq_seventhPowerSnd]
    _ = 7 ^ 5 *
        (p.canonical.verticalGapRoot * p.compensationRoot) ^ 7 :=
      p.rootSnd_natAbs_eq
    _ = 7 * (7 ^ 4 *
        (p.canonical.verticalGapRoot * p.compensationRoot) ^ 7) := by
      ring

/-- The receiver produces a strict internal depth drop from five to four. -/
theorem innerRootSnd_depth_eq_four
    (p : RamifiedQuadraticInnerRootPacket) :
    padicValNat 7 (Int.natAbs p.innerRoot.snd) = 4 := by
  have hload :
      padicValNat 7
          (Int.natAbs p.canonical.terminal.summit.root.snd) =
        1 + padicValNat 7 (Int.natAbs p.innerRoot.snd) := by
    rw [p.rootSnd_eq_seventhPowerSnd, seventhPowerSnd_eq_seven_mul,
      Int.natAbs_mul, Int.natAbs_mul]
    norm_num
    exact padicValNat_seven_mul_of_core_not_dvd
      (Int.natAbs_ne_zero.mpr p.innerRoot_snd_ne_zero)
      (Int.natAbs_ne_zero.mpr p.innerSndCore_ne_zero)
      (fun h => p.innerSndCore_not_seven_dvd
        (Int.natCast_dvd.mpr h))
  rw [p.canonical.terminal.rootSnd_depth_eq_five] at hload
  omega

/-- Complete depth-four seventh-power split of the inner second coordinate
and its core. -/
theorem exists_inner_secondCoordinate_split
    (p : RamifiedQuadraticInnerRootPacket) :
    ∃ innerVerticalRoot innerHorizontalRoot : ℕ,
      Int.natAbs p.innerRoot.snd =
        7 ^ 4 * innerVerticalRoot ^ 7 ∧
      Int.natAbs
          (seventhPowerSndCore p.innerRoot.fst p.innerRoot.snd) =
        innerHorizontalRoot ^ 7 := by
  apply seventh_power_split_after_seven_pow_four
    p.innerRootSnd_innerSndCore_coprime
  · intro h
    exact p.innerSndCore_not_seven_dvd (Int.natCast_dvd.mpr h)
  · exact p.inner_secondCoordinate_product_eq

/-- The depth-four core split immediately separates the two classical cubic
factors into natural seventh powers. -/
theorem exists_inner_cubic_factor_seventh_powers
    (p : RamifiedQuadraticInnerRootPacket) :
    ∃ leftRoot rightRoot : ℕ,
      Int.natAbs
          (seventhPowerSndLeftCubic
            p.innerRoot.fst p.innerRoot.snd) =
        leftRoot ^ 7 ∧
      Int.natAbs
          (seventhPowerSndRightCubic
            p.innerRoot.fst p.innerRoot.snd) =
        rightRoot ^ 7 := by
  rcases p.exists_inner_secondCoordinate_split with
    ⟨innerVerticalRoot, innerHorizontalRoot, hsnd, hcore⟩
  have hproduct :
      Int.natAbs
          (seventhPowerSndLeftCubic
            p.innerRoot.fst p.innerRoot.snd) *
        Int.natAbs
          (seventhPowerSndRightCubic
            p.innerRoot.fst p.innerRoot.snd) =
      innerHorizontalRoot ^ 7 := by
    rw [← Int.natAbs_mul, ← seventhPowerSndCore_factor, hcore]
  rcases seventh_power_factor_split
      (sndCore_cubic_factors_coprime p.innerRoot
        p.innerRoot_coordinates_isCoprime
        p.innerRoot_norm_not_seven_dvd)
      hproduct with
    ⟨⟨leftRoot, hleft⟩, ⟨rightRoot, hright⟩⟩
  exact ⟨leftRoot, rightRoot, hleft, hright⟩

/-- An odd natural-power representation of an integer absolute value absorbs
the sign into an integer root. -/
theorem exists_int_seventh_root_of_natAbs_eq
    {x : ℤ} {root : ℕ} (h : Int.natAbs x = root ^ 7) :
    ∃ signedRoot : ℤ, x = signedRoot ^ 7 := by
  by_cases hx : 0 ≤ x
  · refine ⟨root, ?_⟩
    calc
      x = (Int.natAbs x : ℤ) := (Int.natAbs_of_nonneg hx).symm
      _ = (root ^ 7 : ℕ) := congrArg Nat.cast h
      _ = (root : ℤ) ^ 7 := by norm_num
  · refine ⟨-(root : ℤ), ?_⟩
    have hneg : 0 ≤ -x := by omega
    have habsNeg :
        (Int.natAbs x : ℤ) = -x := by
      rw [← Int.natAbs_neg]
      exact Int.natAbs_of_nonneg hneg
    calc
      x = -(Int.natAbs x : ℤ) := by omega
      _ = -((root ^ 7 : ℕ) : ℤ) := by rw [h]
      _ = -((root : ℤ) ^ 7) := by norm_cast
      _ = (-(root : ℤ)) ^ 7 := by ring

/-- Signed form needed by the next real-cubic norm checkpoint. -/
theorem exists_inner_cubic_factor_signed_seventh_powers
    (p : RamifiedQuadraticInnerRootPacket) :
    (∃ leftRoot : ℤ,
      seventhPowerSndLeftCubic p.innerRoot.fst p.innerRoot.snd =
        leftRoot ^ 7) ∧
    (∃ rightRoot : ℤ,
      seventhPowerSndRightCubic p.innerRoot.fst p.innerRoot.snd =
        rightRoot ^ 7) := by
  rcases p.exists_inner_cubic_factor_seventh_powers with
    ⟨leftRoot, rightRoot, hleft, hright⟩
  exact ⟨exists_int_seventh_root_of_natAbs_eq hleft,
    exists_int_seventh_root_of_natAbs_eq hright⟩


end RamifiedQuadraticInnerRootPacket

end DkMath.FLT.Seven
