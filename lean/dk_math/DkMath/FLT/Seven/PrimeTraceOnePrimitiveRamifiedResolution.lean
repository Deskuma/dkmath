/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.PrimeTraceOneReconstructionRamifiedResolution

#print "file: DkMath.FLT.Seven.PrimeTraceOnePrimitiveRamifiedResolution"

namespace DkMath.FLT.Seven

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- The primitive second-case classification at exponent seven.  The three
constructors retain the unique seven-divisible original endpoint. -/
inductive PrimitiveSevenDivisibleEndpoint (x y z : ℕ) : Prop
  | xOnly (hx : 7 ∣ x) (hy : ¬ 7 ∣ y) (hz : ¬ 7 ∣ z)
  | yOnly (hy : 7 ∣ y) (hx : ¬ 7 ∣ x) (hz : ¬ 7 ∣ z)
  | zOnly (hz : 7 ∣ z) (hx : ¬ 7 ∣ x) (hy : ¬ 7 ∣ y)

/-- The existing mod-seven endpoint sectors give the complete primitive
second-case classification.  The putative sum sector is eliminated by the
already public primitive counterexample contradiction. -/
theorem primitiveSevenDivisibleEndpoint_of_counterexample
    {x y z : ℕ} (source : CounterexamplePack x y z) :
    PrimitiveSevenDivisibleEndpoint x y z := by
  rcases sevenEndpointResidueSector_of_counterexample source with
      ⟨t, ht, hx, hy, hz⟩ |
      ⟨t, ht, hx, hy, hz⟩ |
      ⟨t, ht, hx, hy, hz⟩ |
      ⟨t, ht, hx, hy, hz⟩
  · refine .xOnly ?_ ?_ ?_
    · exact (ZMod.natCast_eq_zero_iff x 7).1 hx
    · intro hy7
      have hy0 : (y : ModSeven) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).2 hy7
      rw [hy] at hy0
      exact ht hy0
    · intro hz7
      have hz0 : (z : ModSeven) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).2 hz7
      rw [hz] at hz0
      exact ht hz0
  · refine .yOnly ?_ ?_ ?_
    · exact (ZMod.natCast_eq_zero_iff y 7).1 hy
    · intro hx7
      have hx0 : (x : ModSeven) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).2 hx7
      rw [hx] at hx0
      exact ht hx0
    · intro hz7
      have hz0 : (z : ModSeven) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).2 hz7
      rw [hz] at hz0
      exact ht hz0
  · refine .zOnly ?_ ?_ ?_
    · exact (ZMod.natCast_eq_zero_iff z 7).1 hz
    · intro hx7
      have hx0 : (x : ModSeven) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).2 hx7
      rw [hx] at hx0
      exact ht (neg_eq_zero.mp hx0)
    · intro hy7
      have hy0 : (y : ModSeven) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).2 hy7
      rw [hy] at hy0
      exact ht hy0
  · exfalso
    apply no_counterexample_of_seven_dvd_y_add_z source
    apply (ZMod.natCast_eq_zero_iff _ _).1
    push_cast
    rw [hy, hz]
    ring

theorem seven_dvd_some_endpoint_of_counterexample
    {x y z : ℕ} (source : CounterexamplePack x y z) :
    7 ∣ x ∨ 7 ∣ y ∨ 7 ∣ z := by
  cases primitiveSevenDivisibleEndpoint_of_counterexample source with
  | xOnly hx _ _ => exact .inl hx
  | yOnly hy _ _ => exact .inr (.inl hy)
  | zOnly hz _ _ => exact .inr (.inr hz)

/-- The original ramified gap is forced when the first primitive endpoint is
seven-divisible. -/
theorem seven_dvd_gap_of_seven_dvd_first
    {x y z : ℕ} (source : CounterexamplePack x y z) (hx : 7 ∣ x) :
    7 ∣ z - y := by
  have hx0 : (x : ModSeven) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2 hx
  have hlin := fermat7Equation_modSeven_linear source.hEq
  have hyz : (y : ModSeven) = (z : ModSeven) := by
    rw [hx0] at hlin
    simpa using hlin
  have hyle : y ≤ z :=
    (right_lt_of_fermat7Equation source.hx source.hEq).le
  apply (Nat.modEq_iff_dvd' hyle).1
  exact (ZMod.natCast_eq_natCast_iff _ _ _).1 hyz

/-- A provenance-preserving normalization of an original primitive
counterexample into the common ramified summit surface. -/
inductive PrimitiveCounterexampleRamifiedResolution
    {x y z : ℕ} (source : CounterexamplePack x y z) : Type
  | xCase (seven_dvd : 7 ∣ x) (summit : PrimitiveRamifiedSummitPacket)
      (distinguished_eq : summit.distinguished = (x : ℤ))
  | yCase (seven_dvd : 7 ∣ y) (summit : PrimitiveRamifiedSummitPacket)
      (distinguished_eq : summit.distinguished = (y : ℤ))
  | zCase (seven_dvd : 7 ∣ z) (summit : PrimitiveRamifiedSummitPacket)
      (distinguished_eq : summit.distinguished = (z : ℤ))

namespace PrimitiveCounterexampleRamifiedResolution

def summit {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedResolution source) :
    PrimitiveRamifiedSummitPacket := by
  cases r with
  | xCase _ q _ => exact q
  | yCase _ q _ => exact q
  | zCase _ q _ => exact q

def distinguishedEndpoint {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedResolution source) : ℕ := by
  cases r with
  | xCase _ _ _ => exact x
  | yCase _ _ _ => exact y
  | zCase _ _ _ => exact z

theorem rootSnd_padicValNat_add_two_eq_seven_mul_endpoint_depth
    {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedResolution source) :
    padicValNat 7 (Int.natAbs r.summit.root.snd) + 2 =
      7 * padicValNat 7 r.distinguishedEndpoint := by
  cases r with
  | xCase _ q hq =>
      dsimp [summit, distinguishedEndpoint]
      have hendpoint :
          padicValNat 7 (Int.natAbs q.distinguished) = padicValNat 7 x := by
        rw [hq]
        simp
      calc
        _ = 7 * padicValNat 7 (Int.natAbs q.distinguished) :=
          q.rootSnd_padicValNat_add_two_eq
        _ = _ := by rw [hendpoint]
  | yCase _ q hq =>
      dsimp [summit, distinguishedEndpoint]
      have hendpoint :
          padicValNat 7 (Int.natAbs q.distinguished) = padicValNat 7 y := by
        rw [hq]
        simp
      calc
        _ = 7 * padicValNat 7 (Int.natAbs q.distinguished) :=
          q.rootSnd_padicValNat_add_two_eq
        _ = _ := by rw [hendpoint]
  | zCase _ q hq =>
      dsimp [summit, distinguishedEndpoint]
      have hendpoint :
          padicValNat 7 (Int.natAbs q.distinguished) = padicValNat 7 z := by
        rw [hq]
        simp
      calc
        _ = 7 * padicValNat 7 (Int.natAbs q.distinguished) :=
          q.rootSnd_padicValNat_add_two_eq
        _ = _ := by rw [hendpoint]

end PrimitiveCounterexampleRamifiedResolution

theorem nonempty_primitiveCounterexampleRamifiedResolution
    {x y z : ℕ} (source : CounterexamplePack x y z) :
    Nonempty (PrimitiveCounterexampleRamifiedResolution source) := by
  cases primitiveSevenDivisibleEndpoint_of_counterexample source with
  | xOnly hx _ _ =>
      let packet := sevenQuadraticSeventhPowerPacket_of_counterexample source
        (seven_dvd_gap_of_seven_dvd_first source hx)
      exact ⟨.xCase hx packet.toPrimitiveRamifiedSummitPacket rfl⟩
  | yOnly hy _ _ =>
      rcases nonempty_prescribedCarrierRamifiedSummit_of_right_chart source hy with
        ⟨q⟩
      exact ⟨.yCase hy q.summit q.distinguished_eq⟩
  | zOnly hz _ _ =>
      rcases nonempty_prescribedCarrierRamifiedSummit_of_left_chart source hz with
        ⟨q⟩
      exact ⟨.zCase hz q.summit q.distinguished_eq⟩

theorem nonempty_primitiveCounterexampleRamifiedSummit
    {x y z : ℕ} (source : CounterexamplePack x y z) :
    Nonempty PrimitiveRamifiedSummitPacket := by
  rcases nonempty_primitiveCounterexampleRamifiedResolution source with ⟨r⟩
  exact ⟨r.summit⟩

end DkMath.FLT.Seven
