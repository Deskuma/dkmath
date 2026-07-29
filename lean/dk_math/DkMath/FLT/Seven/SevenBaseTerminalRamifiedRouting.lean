/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenBaseTerminalRamifiedDepth
import DkMath.FLT.Seven.CoprimeTripleRouting

#print "file: DkMath.FLT.Seven.SevenBaseTerminalRamifiedRouting"

namespace DkMath.FLT.Seven

open DkMath.NumberTheory.TraceOneQuadratic

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

private theorem seven_not_isUnit : ¬ IsUnit (7 : ℤ) := by
  intro h
  rcases Int.isUnit_iff.mp h with h | h <;> norm_num at h

theorem PrimitiveRamifiedSummitPacket.fst_eq
    (p : PrimitiveRamifiedSummitPacket) :
    cyclotomicSevenFst p.endpointLeft p.endpointRight =
      ramifiedSeventhFst p.root.fst p.root.snd := by
  have h := congrArg TraceOneInt.fst p.coordinate_eq
  rw [show
      (cyclotomicSevenToTraceOne p.endpointLeft p.endpointRight).fst =
        cyclotomicSevenFst p.endpointLeft p.endpointRight by rfl] at h
  rw [show
      (sevenAxis * p.root ^ 7).fst =
        ramifiedSeventhFst p.root.fst p.root.snd by
          rcases p.root with ⟨u, v⟩
          exact congrArg TraceOneInt.fst
            (sevenAxis_mul_pow_seven_eq u v)] at h
  exact h

theorem PrimitiveRamifiedSummitPacket.snd_eq
    (p : PrimitiveRamifiedSummitPacket) :
    cyclotomicSevenSnd p.endpointLeft p.endpointRight =
      ramifiedSeventhSnd p.root.fst p.root.snd := by
  have h := congrArg TraceOneInt.snd p.coordinate_eq
  rw [show
      (cyclotomicSevenToTraceOne p.endpointLeft p.endpointRight).snd =
        cyclotomicSevenSnd p.endpointLeft p.endpointRight by rfl] at h
  rw [show
      (sevenAxis * p.root ^ 7).snd =
        ramifiedSeventhSnd p.root.fst p.root.snd by
          rcases p.root with ⟨u, v⟩
          exact congrArg TraceOneInt.snd
            (sevenAxis_mul_pow_seven_eq u v)] at h
  exact h

theorem PrimitiveRamifiedSummitPacket.root_coordinates_isCoprime
    (p : PrimitiveRamifiedSummitPacket) :
    IsCoprime p.root.fst p.root.snd := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  by_contra hg
  rcases Nat.exists_prime_and_dvd hg with ⟨q, hq, hqg⟩
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  have hqu : (q : ℤ) ∣ p.root.fst :=
    (Int.natCast_dvd_natCast.mpr hqg).trans (Int.gcd_dvd_left _ _)
  have hqv : (q : ℤ) ∣ p.root.snd :=
    (Int.natCast_dvd_natCast.mpr hqg).trans (Int.gcd_dvd_right _ _)
  have hu0 : (p.root.fst : ZMod q) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hqu
  have hv0 : (p.root.snd : ZMod q) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hqv
  have hqfst : (q : ℤ) ∣
      ramifiedSeventhFst p.root.fst p.root.snd := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1
    simp [ramifiedSeventhFst, hu0, hv0]
  have hqsnd : (q : ℤ) ∣
      ramifiedSeventhSnd p.root.fst p.root.snd := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1
    simp [ramifiedSeventhSnd, hu0, hv0]
  have hunit : IsUnit (q : ℤ) :=
    p.coordinate_coprime.isUnit_of_dvd'
      (p.fst_eq ▸ hqfst) (p.snd_eq ▸ hqsnd)
  rcases Int.isUnit_iff.mp hunit with hq1 | hqneg
  · exact hq.ne_one (by exact_mod_cast hq1)
  · have hqnonneg : (0 : ℤ) ≤ q := by positivity
    omega

theorem PrimitiveRamifiedSummitPacket.root_coordinates_natAbs_coprime
    (p : PrimitiveRamifiedSummitPacket) :
    Nat.Coprime (Int.natAbs p.root.fst) (Int.natAbs p.root.snd) :=
  Int.isCoprime_iff_nat_coprime.mp p.root_coordinates_isCoprime

theorem PrimitiveRamifiedSummitPacket.seven_dvd_root_snd
    (p : PrimitiveRamifiedSummitPacket) : (7 : ℤ) ∣ p.root.snd := by
  have hv0 : Int.natAbs p.root.snd ≠ 0 :=
    Int.natAbs_ne_zero.mpr p.root_snd_ne_zero
  have hdepth : 1 ≤ padicValNat 7 (Int.natAbs p.root.snd) := by
    rw [p.rootSnd_padicValNat]
    omega
  have habs : 7 ∣ Int.natAbs p.root.snd :=
    (@padicValNat_dvd_iff_le 7 inferInstance _ 1 hv0).mpr hdepth
  exact Int.natCast_dvd.mpr habs

theorem PrimitiveRamifiedSummitPacket.ramifiedLinear_not_seven_dvd
    (p : PrimitiveRamifiedSummitPacket) :
    ¬ (7 : ℤ) ∣ ramifiedLinear p.root.fst p.root.snd := by
  intro hT
  have hv := p.seven_dvd_root_snd
  have h2u : (7 : ℤ) ∣ 2 * p.root.fst := by
    have := dvd_sub hT hv
    simpa [ramifiedLinear] using this
  have hu : (7 : ℤ) ∣ p.root.fst :=
    (show Prime (7 : ℤ) by norm_num).dvd_mul.mp h2u |>.resolve_left (by norm_num)
  exact seven_not_isUnit
    (p.root_coordinates_isCoprime.isUnit_of_dvd' hu hv)

theorem PrimitiveRamifiedSummitPacket.ramifiedLeftCubic_not_seven_dvd
    (p : PrimitiveRamifiedSummitPacket) :
    ¬ (7 : ℤ) ∣ ramifiedLeftCubic p.root.fst p.root.snd := by
  intro hL
  have hv := p.seven_dvd_root_snd
  have hu3 : (7 : ℤ) ∣ p.root.fst ^ 3 := by
    have hrest : (7 : ℤ) ∣
        -2 * p.root.fst ^ 2 * p.root.snd -
          15 * p.root.fst * p.root.snd ^ 2 -
          13 * p.root.snd ^ 3 := by
      rcases hv with ⟨k, hk⟩
      use -2 * p.root.fst ^ 2 * k -
        15 * p.root.fst * 7 * k ^ 2 - 13 * 7 ^ 2 * k ^ 3
      simp [hk]
      ring
    have := dvd_sub hL hrest
    simpa [ramifiedLeftCubic] using this
  have hu := (show Prime (7 : ℤ) by norm_num).dvd_of_dvd_pow hu3
  exact seven_not_isUnit
    (p.root_coordinates_isCoprime.isUnit_of_dvd'
      hu p.seven_dvd_root_snd)

theorem PrimitiveRamifiedSummitPacket.ramifiedRightCubic_not_seven_dvd
    (p : PrimitiveRamifiedSummitPacket) :
    ¬ (7 : ℤ) ∣ ramifiedRightCubic p.root.fst p.root.snd := by
  intro hR
  have hv := p.seven_dvd_root_snd
  have hu3 : (7 : ℤ) ∣ p.root.fst ^ 3 := by
    have hrest : (7 : ℤ) ∣
        5 * p.root.fst ^ 2 * p.root.snd -
          8 * p.root.fst * p.root.snd ^ 2 +
          p.root.snd ^ 3 := by
      rcases hv with ⟨k, hk⟩
      use 5 * p.root.fst ^ 2 * k -
        8 * p.root.fst * 7 * k ^ 2 + 7 ^ 2 * k ^ 3
      simp [hk]
      ring
    have := dvd_sub hR hrest
    simpa [ramifiedRightCubic] using this
  have hu := (show Prime (7 : ℤ) by norm_num).dvd_of_dvd_pow hu3
  exact seven_not_isUnit
    (p.root_coordinates_isCoprime.isUnit_of_dvd'
      hu p.seven_dvd_root_snd)

private theorem prime_dvd_root_v_implies_root_u
    {q : ℕ} (hq : Nat.Prime q) {u v : ℤ}
    (hprimitive : IsCoprime u v) (hv : (q : ℤ) ∣ v)
    (hL : (q : ℤ) ∣ ramifiedLeftCubic u v) : False := by
  have hrest : (q : ℤ) ∣
      -2 * u ^ 2 * v - 15 * u * v ^ 2 - 13 * v ^ 3 := by
    have h1 := dvd_mul_of_dvd_right hv (-2 * u ^ 2)
    have h2 := dvd_mul_of_dvd_right
      (dvd_pow hv (by decide : 2 ≠ 0)) (-15 * u)
    have h3 := dvd_mul_of_dvd_right
      (dvd_pow hv (by decide : 3 ≠ 0)) (-13)
    convert dvd_add (dvd_add h1 h2) h3 using 1 <;> ring
  have hu3 : (q : ℤ) ∣ u ^ 3 := by
    have := dvd_sub hL hrest
    simpa [ramifiedLeftCubic] using this
  have hu := (Nat.prime_iff_prime_int.mp hq).dvd_of_dvd_pow hu3
  exact (Nat.prime_iff_prime_int.mp hq).not_unit
    (hprimitive.isUnit_of_dvd' hu hv)

theorem PrimitiveRamifiedSummitPacket.coprime_linear_left
    (p : PrimitiveRamifiedSummitPacket) :
    Nat.Coprime
      (Int.natAbs (ramifiedLinear p.root.fst p.root.snd))
      (Int.natAbs (ramifiedLeftCubic p.root.fst p.root.snd)) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hg
  rcases Nat.exists_prime_and_dvd hg with ⟨q, hq, hqg⟩
  have hT : (q : ℤ) ∣ ramifiedLinear p.root.fst p.root.snd :=
    Int.natAbs_dvd_natAbs.mp (hqg.trans (Nat.gcd_dvd_left _ _))
  have hL : (q : ℤ) ∣ ramifiedLeftCubic p.root.fst p.root.snd :=
    Int.natAbs_dvd_natAbs.mp (hqg.trans (Nat.gcd_dvd_right _ _))
  have h49v3 : (q : ℤ) ∣ 49 * p.root.snd ^ 3 := by
    have hidentity :
        8 * ramifiedLeftCubic p.root.fst p.root.snd +
            49 * p.root.snd ^ 3 =
          ramifiedLinear p.root.fst p.root.snd *
            (4 * p.root.fst ^ 2 - 10 * p.root.fst * p.root.snd -
              55 * p.root.snd ^ 2) := by
      simp [ramifiedLeftCubic, ramifiedLinear]
      ring
    have hd := dvd_sub
      (dvd_mul_of_dvd_left hT
        (4 * p.root.fst ^ 2 - 10 * p.root.fst * p.root.snd -
          55 * p.root.snd ^ 2))
      (dvd_mul_of_dvd_right hL 8)
    convert hd using 1
    nlinarith [hidentity]
  rcases (Nat.prime_iff_prime_int.mp hq).dvd_mul.mp h49v3 with hq49 | hqv3
  · have hq49Nat : q ∣ 49 := by exact_mod_cast hq49
    have hq7 : q ∣ 7 := hq.dvd_of_dvd_pow (n := 2) (by
      simpa [pow_two] using hq49Nat)
    have hqeq := (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hq7
    have hqeq7 : q = 7 := hqeq.resolve_left hq.ne_one
    subst q
    exact p.ramifiedLinear_not_seven_dvd hT
  · have hqv := (Nat.prime_iff_prime_int.mp hq).dvd_of_dvd_pow hqv3
    exact prime_dvd_root_v_implies_root_u hq
      p.root_coordinates_isCoprime hqv hL

theorem PrimitiveRamifiedSummitPacket.coprime_linear_right
    (p : PrimitiveRamifiedSummitPacket) :
    Nat.Coprime
      (Int.natAbs (ramifiedLinear p.root.fst p.root.snd))
      (Int.natAbs (ramifiedRightCubic p.root.fst p.root.snd)) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hg
  rcases Nat.exists_prime_and_dvd hg with ⟨q, hq, hqg⟩
  have hT : (q : ℤ) ∣ ramifiedLinear p.root.fst p.root.snd :=
    Int.natAbs_dvd_natAbs.mp (hqg.trans (Nat.gcd_dvd_left _ _))
  have hR : (q : ℤ) ∣ ramifiedRightCubic p.root.fst p.root.snd :=
    Int.natAbs_dvd_natAbs.mp (hqg.trans (Nat.gcd_dvd_right _ _))
  have h49v3 : (q : ℤ) ∣ 49 * p.root.snd ^ 3 := by
    have hidentity :
        8 * ramifiedRightCubic p.root.fst p.root.snd -
            49 * p.root.snd ^ 3 =
          ramifiedLinear p.root.fst p.root.snd *
            (4 * p.root.fst ^ 2 + 18 * p.root.fst * p.root.snd -
              41 * p.root.snd ^ 2) := by
      simp [ramifiedRightCubic, ramifiedLinear]
      ring
    have hd := dvd_sub
      (dvd_mul_of_dvd_left hT
        (4 * p.root.fst ^ 2 + 18 * p.root.fst * p.root.snd -
          41 * p.root.snd ^ 2))
      (dvd_mul_of_dvd_right hR 8)
    have hdneg : (q : ℤ) ∣ -(49 * p.root.snd ^ 3) := by
      convert hd using 1
      nlinarith [hidentity]
    simpa only [dvd_neg] using hdneg
  rcases (Nat.prime_iff_prime_int.mp hq).dvd_mul.mp h49v3 with hq49 | hqv3
  · have hq49Nat : q ∣ 49 := by exact_mod_cast hq49
    have hq7 : q ∣ 7 := hq.dvd_of_dvd_pow (n := 2) (by
      simpa [pow_two] using hq49Nat)
    have hqeq := (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hq7
    have hqeq7 : q = 7 := hqeq.resolve_left hq.ne_one
    subst q
    exact p.ramifiedLinear_not_seven_dvd hT
  · have hqv := (Nat.prime_iff_prime_int.mp hq).dvd_of_dvd_pow hqv3
    have hLfromR : (q : ℤ) ∣ ramifiedLeftCubic p.root.fst p.root.snd := by
      have hdiff : (q : ℤ) ∣
          ramifiedRightCubic p.root.fst p.root.snd -
            ramifiedLeftCubic p.root.fst p.root.snd := by
        rw [ramifiedRightCubic_sub_left]
        exact dvd_mul_of_dvd_left
          (dvd_mul_of_dvd_right hqv 7) _
      have hd := dvd_sub hR hdiff
      convert hd using 1 <;> ring
    exact prime_dvd_root_v_implies_root_u hq
      p.root_coordinates_isCoprime hqv hLfromR

theorem PrimitiveRamifiedSummitPacket.coprime_left_right
    (p : PrimitiveRamifiedSummitPacket) :
    Nat.Coprime
      (Int.natAbs (ramifiedLeftCubic p.root.fst p.root.snd))
      (Int.natAbs (ramifiedRightCubic p.root.fst p.root.snd)) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hg
  rcases Nat.exists_prime_and_dvd hg with ⟨q, hq, hqg⟩
  have hL : (q : ℤ) ∣ ramifiedLeftCubic p.root.fst p.root.snd :=
    Int.natAbs_dvd_natAbs.mp (hqg.trans (Nat.gcd_dvd_left _ _))
  have hR : (q : ℤ) ∣ ramifiedRightCubic p.root.fst p.root.snd :=
    Int.natAbs_dvd_natAbs.mp (hqg.trans (Nat.gcd_dvd_right _ _))
  have hdiff : (q : ℤ) ∣
      7 * p.root.snd * norm p.root := by
    rw [← ramifiedRightCubic_sub_left]
    exact dvd_sub hR hL
  rcases (Nat.prime_iff_prime_int.mp hq).dvd_mul.mp hdiff with hq7v | hqN
  · rcases (Nat.prime_iff_prime_int.mp hq).dvd_mul.mp hq7v with hq7 | hqv
    · have : q = 7 := by
        have : q ∣ 7 := by exact_mod_cast hq7
        exact (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp this
          |>.resolve_left hq.ne_one
      subst q
      exact p.ramifiedLeftCubic_not_seven_dvd hL
    · exact prime_dvd_root_v_implies_root_u hq
        p.root_coordinates_isCoprime hqv hL
  · have h49v4 : (q : ℤ) ∣ 49 * p.root.snd ^ 4 := by
      have hidentity :
          -(2 * p.root.fst ^ 2 - 5 * p.root.fst * p.root.snd -
              31 * p.root.snd ^ 2) * norm p.root +
            ramifiedLinear p.root.fst p.root.snd *
              ramifiedLeftCubic p.root.fst p.root.snd =
            49 * p.root.snd ^ 4 := by
        simp [DkMath.NumberTheory.TraceOneQuadratic.norm,
          ramifiedLinear, ramifiedLeftCubic]
        ring
      rw [← hidentity]
      exact dvd_add (dvd_mul_of_dvd_right hqN _)
        (dvd_mul_of_dvd_right hL _)
    rcases (Nat.prime_iff_prime_int.mp hq).dvd_mul.mp h49v4 with hq49 | hqv4
    · have hq49Nat : q ∣ 49 := by exact_mod_cast hq49
      have hq7 : q ∣ 7 := hq.dvd_of_dvd_pow (n := 2) (by
        simpa [pow_two] using hq49Nat)
      have hqeq := (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hq7
      have hqeq7 : q = 7 := hqeq.resolve_left hq.ne_one
      subst q
      exact p.ramifiedLeftCubic_not_seven_dvd hL
    · have hqv := (Nat.prime_iff_prime_int.mp hq).dvd_of_dvd_pow hqv4
      exact prime_dvd_root_v_implies_root_u hq
        p.root_coordinates_isCoprime hqv hL

theorem PrimitiveRamifiedSummitPacket.endpoint_coprime_left_sum
    (p : PrimitiveRamifiedSummitPacket) :
    Nat.Coprime (Int.natAbs p.endpointLeft)
      (Int.natAbs (p.endpointLeft + p.endpointRight)) := by
  apply Int.isCoprime_iff_nat_coprime.mp
  rcases p.endpoint_coprime with ⟨a, b, hab⟩
  refine ⟨a - b, b, ?_⟩
  calc
    (a - b) * p.endpointLeft +
        b * (p.endpointLeft + p.endpointRight) =
      a * p.endpointLeft + b * p.endpointRight := by ring
    _ = 1 := hab

theorem PrimitiveRamifiedSummitPacket.endpoint_coprime_right_sum
    (p : PrimitiveRamifiedSummitPacket) :
    Nat.Coprime (Int.natAbs p.endpointRight)
      (Int.natAbs (p.endpointLeft + p.endpointRight)) := by
  apply Int.isCoprime_iff_nat_coprime.mp
  rcases p.endpoint_coprime with ⟨a, b, hab⟩
  refine ⟨b - a, a, ?_⟩
  calc
    (b - a) * p.endpointRight +
        a * (p.endpointLeft + p.endpointRight) =
      a * p.endpointLeft + b * p.endpointRight := by ring
    _ = 1 := hab

/-- The formal ramified `3 x 3` routing packet. -/
structure RamifiedCubicRoutingPacket : Type where
  summit : PrimitiveRamifiedSummitPacket
  routing : CoprimeTripleRouting
    (Int.natAbs summit.endpointLeft)
    (Int.natAbs summit.endpointRight)
    (Int.natAbs (summit.endpointLeft + summit.endpointRight))
    (Int.natAbs
      (ramifiedLinear summit.root.fst summit.root.snd))
    (Int.natAbs
      (ramifiedLeftCubic summit.root.fst summit.root.snd))
    (Int.natAbs
      (ramifiedRightCubic summit.root.fst summit.root.snd))

theorem PrimitiveRamifiedSummitPacket.nonempty_cubicRouting
    (p : PrimitiveRamifiedSummitPacket) :
    Nonempty RamifiedCubicRoutingPacket := by
  have hprod :
      Int.natAbs p.endpointLeft *
          Int.natAbs p.endpointRight *
          Int.natAbs (p.endpointLeft + p.endpointRight) =
        Int.natAbs (ramifiedLinear p.root.fst p.root.snd) *
          Int.natAbs (ramifiedLeftCubic p.root.fst p.root.snd) *
          Int.natAbs (ramifiedRightCubic p.root.fst p.root.snd) := by
    have h := congrArg Int.natAbs p.endpoint_product_eq
    simpa only [Int.natAbs_neg, Int.natAbs_mul] using h
  have hT0 : ramifiedLinear p.root.fst p.root.snd ≠ 0 :=
    fun h => p.ramifiedLinear_not_seven_dvd (by rw [h]; exact dvd_zero 7)
  have hL0 : ramifiedLeftCubic p.root.fst p.root.snd ≠ 0 :=
    fun h => p.ramifiedLeftCubic_not_seven_dvd
      (by rw [h]; exact dvd_zero 7)
  have hR0 : ramifiedRightCubic p.root.fst p.root.snd ≠ 0 :=
    fun h => p.ramifiedRightCubic_not_seven_dvd
      (by rw [h]; exact dvd_zero 7)
  rcases nonempty_coprimeTripleRouting
      ⟨Int.natAbs_pos.mpr p.endpointLeft_ne_zero,
        Int.natAbs_pos.mpr p.endpointRight_ne_zero,
        Int.natAbs_pos.mpr p.endpointSum_ne_zero⟩
      ⟨Int.natAbs_pos.mpr hT0, Int.natAbs_pos.mpr hL0,
        Int.natAbs_pos.mpr hR0⟩
      (Int.isCoprime_iff_nat_coprime.mp p.endpoint_coprime)
      p.endpoint_coprime_left_sum p.endpoint_coprime_right_sum
      p.coprime_linear_left p.coprime_linear_right p.coprime_left_right
      hprod with ⟨routing⟩
  exact ⟨⟨p, routing⟩⟩

noncomputable def PrimitiveRamifiedSummitPacket.cubicRouting
    (p : PrimitiveRamifiedSummitPacket) :
    RamifiedCubicRoutingPacket :=
  Classical.choice p.nonempty_cubicRouting

noncomputable def
    AwaySevenBaseTerminalUnitSectorPacket.ramifiedCubicRouting
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (terminal : AwaySevenBaseTerminalUnitSectorPacket source r p) :
    RamifiedCubicRoutingPacket :=
  terminal.ramifiedSummit.cubicRouting

private theorem padicValInt_norm_root_eq_zero
    (p : PrimitiveRamifiedSummitPacket) :
    padicValInt 7 (norm p.root) = 0 := by
  rw [padicValInt.eq_zero_iff]
  exact Or.inr (Or.inr p.root_norm_not_seven_dvd)

theorem PrimitiveRamifiedSummitPacket.cubicGap_padicValNat
    (p : PrimitiveRamifiedSummitPacket) :
    padicValNat 7
        (Int.natAbs
          (ramifiedRightCubic p.root.fst p.root.snd -
            ramifiedLeftCubic p.root.fst p.root.snd)) =
      6 + 7 * padicValNat 7 p.gapRoot := by
  rw [ramifiedRightCubic_sub_left]
  have hv0 := p.root_snd_ne_zero
  have hn0 : norm p.root ≠ 0 := by
    rw [p.root_norm_eq]
    exact_mod_cast p.residualRoot_pos.ne'
  rw [Int.natAbs_mul, Int.natAbs_mul,
    padicValNat.mul
      (mul_ne_zero (by norm_num)
        (Int.natAbs_ne_zero.mpr hv0))
      (Int.natAbs_ne_zero.mpr hn0),
    padicValNat.mul (by norm_num) (Int.natAbs_ne_zero.mpr hv0)]
  have h7abs : Int.natAbs (7 : ℤ) = 7 := rfl
  rw [h7abs, padicValNat.self (by norm_num)]
  have hnorm : padicValNat 7 (Int.natAbs (norm p.root)) = 0 :=
    padicValInt_norm_root_eq_zero p
  rw [hnorm, p.rootSnd_padicValNat]
  omega

theorem PrimitiveRamifiedSummitPacket.endpointGap_padicValNat
    (p : PrimitiveRamifiedSummitPacket) :
    padicValNat 7 (Int.natAbs (p.endpointLeft - p.endpointRight)) =
      6 + 7 * padicValNat 7 p.gapRoot := by
  rw [p.gap_eq, Int.natAbs_mul, Int.natAbs_pow]
  have h7abs : Int.natAbs (7 : ℤ) = 7 := rfl
  have hAabs :
      Int.natAbs ((p.gapRoot : ℤ) ^ 7) = p.gapRoot ^ 7 := by simp
  rw [h7abs, hAabs]
  rw [padicValNat.mul
      (by positivity : 7 ^ 6 ≠ 0)
      (pow_ne_zero 7 p.gapRoot_pos.ne'),
    padicValNat.prime_pow 6,
    padicValNat.pow 7 p.gapRoot_pos.ne']

/-- RAMIFIED-002 exact self-similarity: the endpoint gap and the root-cubic
gap have the same complete seven-adic depth. -/
theorem
    PrimitiveRamifiedSummitPacket.cubicGap_depth_eq_endpointGap_depth
    (p : PrimitiveRamifiedSummitPacket) :
    padicValNat 7
        (Int.natAbs
          (ramifiedRightCubic p.root.fst p.root.snd -
            ramifiedLeftCubic p.root.fst p.root.snd)) =
      padicValNat 7
        (Int.natAbs (p.endpointLeft - p.endpointRight)) := by
  rw [p.cubicGap_padicValNat, p.endpointGap_padicValNat]

#print axioms AwaySevenBaseTerminalUnitSectorPacket.ramifiedCubicRouting
#print axioms
  PrimitiveRamifiedSummitPacket.cubicGap_depth_eq_endpointGap_depth

end DkMath.FLT.Seven
