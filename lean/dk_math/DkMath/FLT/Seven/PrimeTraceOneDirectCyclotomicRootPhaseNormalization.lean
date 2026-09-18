/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.PrimeTraceOneDirectCyclotomicCMTorsionPhase

#print "file: DkMath.FLT.Seven.PrimeTraceOneDirectCyclotomicRootPhaseNormalization"

namespace DkMath.FLT.Seven

noncomputable section

set_option linter.style.longLine false

open SevenRealCubicInt
open SevenCyclotomicDegreeSixInt


namespace SevenCyclotomicDegreeSixInt


local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩


/-- The current-route seventh root together with the identities that retain
its provenance.  The norm field is an integer equality, so it retains the
sign of the residual root rather than replacing it by an absolute value. -/
structure DirectCyclotomicExactRootPacket
    {x y z : ℕ} (source : CounterexamplePack x y z)
    (r : PrimitiveCounterexampleRamifiedProvenance source) where
  gamma : Ring
  quotient_eq : directCyclotomicPhaseQuotient r 1 = gamma ^ 7
  factor_eq : directLinearFactor r = ramifiedUniformizer * gamma ^ 7
  gamma_not_mem_ramifiedPrime : gamma ∉ ramifiedPrime
  norm_eq_residualRoot : cyclotomicNormHom gamma = (r.summit.residualRoot : ℤ)

theorem cyclotomicNormHom_gamma_pow_eq_residualRoot_pow
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {gamma : Ring}
    (hfactor : directLinearFactor r = ramifiedUniformizer * gamma ^ 7) :
    (cyclotomicNormHom gamma) ^ 7 =
      (r.summit.residualRoot : ℤ) ^ 7 := by
  have hn := congrArg cyclotomicNormHom hfactor
  rw [map_mul, map_pow, cyclotomicNormHom_directLinearFactor,
    directCyclotomicNorm_eq_seven_mul_residual_pow,
    cyclotomicNormHom_ramifiedUniformizer] at hn
  apply (mul_left_cancel₀ (show (7 : ℤ) ≠ 0 by norm_num))
  simpa [mul_pow] using hn.symm

theorem cyclotomicNormHom_eq_residualRoot_of_pow_eq
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {gamma : Ring}
    (hfactor : directLinearFactor r = ramifiedUniformizer * gamma ^ 7) :
    cyclotomicNormHom gamma = (r.summit.residualRoot : ℤ) := by
  apply (Odd.strictMono_pow (R := ℤ) (by norm_num : Odd 7)).injective
  exact cyclotomicNormHom_gamma_pow_eq_residualRoot_pow hfactor

theorem exactRootPacket_of_chosenQuotientPowerPacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectCyclotomicChosenQuotientPowerPacket source r) :
    ∃ _q : DirectCyclotomicExactRootPacket source r, True := by
  obtain ⟨gamma, hgamma⟩ :=
    _root_.DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt.DirectCyclotomicChosenQuotientPowerPacket.exists_directLinearFactor_seventhPower_unconditional p
  have hquotient : directCyclotomicPhaseQuotient r 1 = gamma ^ 7 := by
    have hgamma' := hgamma
    rw [directLinearFactor_eq_uniformizer_mul_quotient r] at hgamma'
    apply sub_eq_zero.mp
    have hdiff :
        ramifiedUniformizer * directCyclotomicPhaseQuotient r 1 -
            ramifiedUniformizer * gamma ^ 7 = 0 := by
      rw [directCyclotomicPhaseQuotient_one r]
      rw [hgamma']
      simp
    have hmul : ramifiedUniformizer *
        (directCyclotomicPhaseQuotient r 1 - gamma ^ 7) = 0 := by
      simpa [mul_sub] using hdiff
    exact (mul_eq_zero.mp hmul).resolve_left ramifiedUniformizer_ne_zero
  have hnot : gamma ∉ ramifiedPrime := by
    intro hmem
    apply directCyclotomicPhaseQuotient_not_mem_ramifiedPrime_of_lt_seven
      (j := 1) r (by norm_num) (by norm_num)
    change ramifiedEval (directCyclotomicPhaseQuotient r 1) = 0
    rw [hquotient, map_pow]
    rw [show ramifiedEval gamma = 0 by exact hmem]
    simp
  refine ⟨({
    gamma := gamma
    quotient_eq := hquotient
    factor_eq := hgamma
    gamma_not_mem_ramifiedPrime := hnot
    norm_eq_residualRoot :=
      cyclotomicNormHom_eq_residualRoot_of_pow_eq hgamma } :
        DirectCyclotomicExactRootPacket source r), trivial⟩

/-- The canonical integer representative of the ramified residue of an
element. -/
def scalarLift (g : Ring) : ℤ := Int.ofNat (ramifiedEval g).val

theorem ramifiedEval_scalarLift (g : Ring) :
    ramifiedEval (scalarLift g : Ring) = ramifiedEval g := by
  simp [scalarLift]

theorem sub_scalarLift_mem_ramifiedPrime (g : Ring) :
    g - (scalarLift g : Ring) ∈ ramifiedPrime := by
  change ramifiedEval (g - (scalarLift g : Ring)) = 0
  rw [map_sub, ramifiedEval_scalarLift, sub_self]

theorem scalarLift_not_seven_dvd {g : Ring} (hg : g ∉ ramifiedPrime) :
    ¬ (7 : ℤ) ∣ scalarLift g := by
  intro hdiv
  apply hg
  change ramifiedEval g = 0
  have hz : (scalarLift g : ZMod 7) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (scalarLift g) 7).mpr hdiv
  calc
    ramifiedEval g = ramifiedEval (scalarLift g : Ring) :=
      (ramifiedEval_scalarLift g).symm
    _ = (scalarLift g : ZMod 7) := by simp
    _ = 0 := hz

/-- The direct first-order phase condition.  The scalar is the canonical
integer lift of the residue, and `k` is represented by `Fin 7`. -/
def FirstOrderPhaseNormalized (g : Ring) (k : Fin 7) : Prop :=
  zeta ^ (k : ℕ) * g - (scalarLift g : Ring) ∈ ramifiedPrime ^ 2

def firstOrderPhaseSum (k : Fin 7) : Ring :=
  ∑ i ∈ Finset.range (k : ℕ), zeta ^ i

theorem one_sub_zeta_fin_eq_uniformizer_mul_firstOrderPhaseSum
    (k : Fin 7) :
    1 - zeta ^ (k : ℕ) =
      ramifiedUniformizer * firstOrderPhaseSum k := by
  simpa only [firstOrderPhaseSum, directCyclotomicPhaseSum] using
    (one_sub_zeta_pow_eq_uniformizer_mul_phaseSum (k : ℕ))

theorem ramifiedEval_firstOrderPhaseSum (k : Fin 7) :
    ramifiedEval (firstOrderPhaseSum k) = (k.val : ZMod 7) := by
  simp [firstOrderPhaseSum, map_sum, map_pow, ramifiedEval_zeta]

theorem exists_firstOrderCoefficient {g : Ring} (_hg : g ∉ ramifiedPrime) :
    ∃ t : Ring, ramifiedUniformizer * t =
      g - (scalarLift g : Ring) := by
  have hmem := sub_scalarLift_mem_ramifiedPrime g
  rw [ramifiedPrime_eq_span_uniformizer,
    Ideal.mem_span_singleton] at hmem
  rcases hmem with ⟨t, ht⟩
  exact ⟨t, ht.symm⟩

noncomputable def firstOrderCoefficient (g : Ring) (hg : g ∉ ramifiedPrime) :
    Ring :=
  Classical.choose (exists_firstOrderCoefficient hg)

theorem firstOrderCoefficient_spec {g : Ring} (hg : g ∉ ramifiedPrime) :
    ramifiedUniformizer * firstOrderCoefficient g hg =
      g - (scalarLift g : Ring) := by
  exact Classical.choose_spec (exists_firstOrderCoefficient hg)

theorem uniformizer_mul_mem_ramifiedPrime_sq_iff (a : Ring) :
    ramifiedUniformizer * a ∈ ramifiedPrime ^ 2 ↔
      a ∈ ramifiedPrime := by
  constructor
  · intro h
    rw [ramifiedPrime_eq_span_uniformizer,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
    rcases h with ⟨b, hb⟩
    rw [ramifiedPrime_eq_span_uniformizer, Ideal.mem_span_singleton]
    refine ⟨b, ?_⟩
    have hba : ramifiedUniformizer *
        (ramifiedUniformizer * b - a) = 0 := by
      have hba' : ramifiedUniformizer ^ 2 * b -
          ramifiedUniformizer * a = 0 := sub_eq_zero.mpr hb.symm
      calc
        ramifiedUniformizer *
            (ramifiedUniformizer * b - a) =
          ramifiedUniformizer ^ 2 * b - ramifiedUniformizer * a := by ring
        _ = 0 := hba'
    have hzero := (mul_eq_zero.mp hba).resolve_left ramifiedUniformizer_ne_zero
    exact sub_eq_zero.mp hzero |>.symm
  · intro h
    rw [ramifiedPrime_eq_span_uniformizer, Ideal.mem_span_singleton] at h
    rcases h with ⟨b, hb⟩
    rw [ramifiedPrime_eq_span_uniformizer,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    refine ⟨b, ?_⟩
    rw [hb, pow_two]
    ring

theorem firstOrderPhaseIndex_scalar_ne_zero {g : Ring}
    (hg : g ∉ ramifiedPrime) :
    ramifiedEval (scalarLift g : Ring) ≠ 0 := by
  rw [ramifiedEval_scalarLift]
  exact hg

noncomputable def firstOrderPhaseIndex (g : Ring) (hg : g ∉ ramifiedPrime) :
    Fin 7 := by
  let c : ZMod 7 := ramifiedEval (scalarLift g : Ring)
  let t : ZMod 7 := ramifiedEval (firstOrderCoefficient g hg)
  exact ⟨(t / c).val, ZMod.val_lt _⟩

theorem firstOrderPhaseIndex_cast {g : Ring} (hg : g ∉ ramifiedPrime) :
    ((firstOrderPhaseIndex g hg).val : ZMod 7) =
      ramifiedEval (firstOrderCoefficient g hg) /
      ramifiedEval (scalarLift g : Ring) := by
  simp [firstOrderPhaseIndex]

theorem firstOrderPhaseIndex_mul_scalar_eq_coefficient {g : Ring}
    (hg : g ∉ ramifiedPrime) :
    (firstOrderPhaseIndex g hg).val *
          ramifiedEval (scalarLift g : Ring) =
      ramifiedEval (firstOrderCoefficient g hg) := by
  have hc : ramifiedEval (scalarLift g : Ring) ≠ 0 :=
    firstOrderPhaseIndex_scalar_ne_zero hg
  have h := firstOrderPhaseIndex_cast hg
  calc
    (firstOrderPhaseIndex g hg).val *
          ramifiedEval (scalarLift g : Ring) =
        (ramifiedEval (firstOrderCoefficient g hg) /
          ramifiedEval (scalarLift g : Ring)) *
            ramifiedEval (scalarLift g : Ring) := by rw [h]
    _ = ramifiedEval (firstOrderCoefficient g hg) :=
      div_mul_cancel₀ _ hc

theorem zeta_fin_pow_eq_one_sub_uniformizer_mul_firstOrderPhaseSum
    (k : Fin 7) :
    zeta ^ (k : ℕ) =
      1 - ramifiedUniformizer * firstOrderPhaseSum k := by
  have h := one_sub_zeta_fin_eq_uniformizer_mul_firstOrderPhaseSum k
  linear_combination -h

theorem firstOrderPhaseIndex_normalized {g : Ring}
    (hg : g ∉ ramifiedPrime) :
    FirstOrderPhaseNormalized g (firstOrderPhaseIndex g hg) := by
  let k := firstOrderPhaseIndex g hg
  let c : Ring := scalarLift g
  let t : Ring := firstOrderCoefficient g hg
  let s : Ring := firstOrderPhaseSum k
  have hcoeff : ramifiedEval (t - s * c) = 0 := by
    rw [map_sub, map_mul, ramifiedEval_firstOrderPhaseSum,
      firstOrderPhaseIndex_mul_scalar_eq_coefficient hg]
    simp [t]
  have hcoeff_mem : t - s * c ∈ ramifiedPrime := by
    change ramifiedEval (t - s * c) = 0
    exact hcoeff
  rw [ramifiedPrime_eq_span_uniformizer,
    Ideal.mem_span_singleton] at hcoeff_mem
  rcases hcoeff_mem with ⟨u, hu⟩
  have hg_eq : g = c + ramifiedUniformizer * t := by
    have ht := firstOrderCoefficient_spec hg
    dsimp [c, t] at ht ⊢
    calc
      g = (g - (scalarLift g : Ring)) +
          (scalarLift g : Ring) := by ring
      _ = ramifiedUniformizer * firstOrderCoefficient g hg +
          (scalarLift g : Ring) := by rw [← ht]
      _ = c + ramifiedUniformizer * t := by ring
  have hzeta : zeta ^ (k : ℕ) =
      1 - ramifiedUniformizer * s := by
    dsimp [s]
    exact zeta_fin_pow_eq_one_sub_uniformizer_mul_firstOrderPhaseSum k
  have hpow : zeta ^ (k : ℕ) * g - c =
      ramifiedUniformizer ^ 2 * (u - s * t) := by
    rw [hzeta, hg_eq]
    calc
      (1 - ramifiedUniformizer * s) *
            (c + ramifiedUniformizer * t) - c =
          ramifiedUniformizer * (t - s * c) -
            ramifiedUniformizer ^ 2 * s * t := by ring
      _ = ramifiedUniformizer * (ramifiedUniformizer * u) -
            ramifiedUniformizer ^ 2 * s * t := by rw [hu]
      _ = ramifiedUniformizer ^ 2 * (u - s * t) := by ring
  change zeta ^ (k : ℕ) * g - (scalarLift g : Ring) ∈
    ramifiedPrime ^ 2
  rw [ramifiedPrime_eq_span_uniformizer,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  refine ⟨u - s * t, ?_⟩
  simp [c, hpow]

theorem firstOrderPhaseNormalized_iff {g : Ring} (hg : g ∉ ramifiedPrime)
    (k : Fin 7) :
    FirstOrderPhaseNormalized g k ↔
      (k.val : ZMod 7) * ramifiedEval (scalarLift g : Ring) =
        ramifiedEval (firstOrderCoefficient g hg) := by
  let c : Ring := scalarLift g
  let t : Ring := firstOrderCoefficient g hg
  let s : Ring := firstOrderPhaseSum k
  have hg_eq : g = c + ramifiedUniformizer * t := by
    have ht := firstOrderCoefficient_spec hg
    dsimp [c, t] at ht ⊢
    calc
      g = (g - (scalarLift g : Ring)) +
          (scalarLift g : Ring) := by ring
      _ = ramifiedUniformizer * firstOrderCoefficient g hg +
          (scalarLift g : Ring) := by rw [← ht]
      _ = c + ramifiedUniformizer * t := by ring
  have hzeta : zeta ^ (k : ℕ) =
      1 - ramifiedUniformizer * s := by
    dsimp [s]
    exact zeta_fin_pow_eq_one_sub_uniformizer_mul_firstOrderPhaseSum k
  have hexpr : zeta ^ (k : ℕ) * g - c =
      ramifiedUniformizer * (t - s * c) -
        ramifiedUniformizer ^ 2 * s * t := by
    rw [hzeta, hg_eq]
    ring
  have hsecond : ramifiedUniformizer ^ 2 * s * t ∈
      ramifiedPrime ^ 2 := by
    rw [ramifiedPrime_eq_span_uniformizer,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact ⟨s * t, by ring⟩
  constructor
  · intro hnorm
    change zeta ^ (k : ℕ) * g - c ∈ ramifiedPrime ^ 2 at hnorm
    rw [hexpr] at hnorm
    have hfirst : ramifiedUniformizer * (t - s * c) ∈
        ramifiedPrime ^ 2 := by
      have hadd := (ramifiedPrime ^ 2).add_mem hnorm hsecond
      convert hadd using 1; ring
    have hcoeff : t - s * c ∈ ramifiedPrime :=
      (uniformizer_mul_mem_ramifiedPrime_sq_iff _).mp hfirst
    change ramifiedEval (t - s * c) = 0 at hcoeff
    rw [map_sub, map_mul, ramifiedEval_firstOrderPhaseSum] at hcoeff
    exact sub_eq_zero.mp hcoeff |>.symm
  · intro hcoeff
    have hcoeff_mem : t - s * c ∈ ramifiedPrime := by
      change ramifiedEval (t - s * c) = 0
      rw [map_sub, map_mul, ramifiedEval_firstOrderPhaseSum]
      exact sub_eq_zero.mpr hcoeff.symm
    rw [ramifiedPrime_eq_span_uniformizer,
      Ideal.mem_span_singleton] at hcoeff_mem
    rcases hcoeff_mem with ⟨u, hu⟩
    have hpow : zeta ^ (k : ℕ) * g - c =
        ramifiedUniformizer ^ 2 * (u - s * t) := by
      rw [hexpr]
      calc
        ramifiedUniformizer * (t - s * c) -
              ramifiedUniformizer ^ 2 * s * t =
            ramifiedUniformizer * (ramifiedUniformizer * u) -
              ramifiedUniformizer ^ 2 * s * t := by rw [hu]
        _ = ramifiedUniformizer ^ 2 * (u - s * t) := by ring
    change zeta ^ (k : ℕ) * g - (scalarLift g : Ring) ∈
      ramifiedPrime ^ 2
    rw [ramifiedPrime_eq_span_uniformizer,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    refine ⟨u - s * t, ?_⟩
    simp [c, hpow]

theorem exists_unique_firstOrderPhaseNormalized {g : Ring}
    (hg : g ∉ ramifiedPrime) :
    ∃! k : Fin 7, FirstOrderPhaseNormalized g k := by
  refine ⟨firstOrderPhaseIndex g hg,
    firstOrderPhaseIndex_normalized hg, ?_⟩
  intro k hk
  have hindex := firstOrderPhaseIndex_mul_scalar_eq_coefficient hg
  have hk' := (firstOrderPhaseNormalized_iff hg k).mp hk
  have hscalar : ramifiedEval (scalarLift g : Ring) ≠ 0 :=
    firstOrderPhaseIndex_scalar_ne_zero hg
  have hkl : (k.val : ZMod 7) =
      (firstOrderPhaseIndex g hg).val := by
    apply mul_right_cancel₀ hscalar
    calc
      (k.val : ZMod 7) * ramifiedEval (scalarLift g : Ring) =
          ramifiedEval (firstOrderCoefficient g hg) := hk'
      _ = (firstOrderPhaseIndex g hg).val *
          ramifiedEval (scalarLift g : Ring) := hindex.symm
  apply Fin.ext
  have hmod :=
    (ZMod.natCast_eq_natCast_iff' k.val
      (firstOrderPhaseIndex g hg).val 7).mp hkl
  rw [Nat.mod_eq_of_lt k.isLt,
    Nat.mod_eq_of_lt (firstOrderPhaseIndex g hg).isLt] at hmod
  exact hmod

theorem cyclotomicNormHom_zeta : cyclotomicNormHom zeta = 1 := by
  rw [cyclotomicNormHom_apply]
  norm_num [zeta, QuadraticAlgebra.norm, SevenRealCubicInt.norm,
    SevenRealCubicInt.mul]

theorem zeta_fin_pow_pow_seven (k : Fin 7) :
    (zeta ^ (k : ℕ)) ^ 7 = 1 := by
  rw [← pow_mul, Nat.mul_comm, pow_mul, zeta_pow_seven, one_pow]

structure DirectCyclotomicNormalizedRootPacket
    {x y z : ℕ} (source : CounterexamplePack x y z)
    (r : PrimitiveCounterexampleRamifiedProvenance source) where
  exactRoot : DirectCyclotomicExactRootPacket source r
  phase : Fin 7
  gammaNorm : Ring
  gammaNorm_eq : gammaNorm =
    zeta ^ (phase : ℕ) * exactRoot.gamma
  phase_normalized :
    FirstOrderPhaseNormalized exactRoot.gamma phase
  gammaNorm_pow_eq_quotient :
    gammaNorm ^ 7 = directCyclotomicPhaseQuotient r 1
  gammaNorm_norm_eq_residualRoot :
    cyclotomicNormHom gammaNorm = (r.summit.residualRoot : ℤ)

theorem normalizedRootPacket_of_exactRootPacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (q : DirectCyclotomicExactRootPacket source r) :
    ∃ _p : DirectCyclotomicNormalizedRootPacket source r, True := by
  let k := firstOrderPhaseIndex q.gamma q.gamma_not_mem_ramifiedPrime
  let gammaNorm : Ring := zeta ^ (k : ℕ) * q.gamma
  refine ⟨({
    exactRoot := q
    phase := k
    gammaNorm := gammaNorm
    gammaNorm_eq := rfl
    phase_normalized := ?_
    gammaNorm_pow_eq_quotient := ?_
    gammaNorm_norm_eq_residualRoot := ?_ } :
      DirectCyclotomicNormalizedRootPacket source r), ?_⟩
  · exact firstOrderPhaseIndex_normalized q.gamma_not_mem_ramifiedPrime
  · have hz : (zeta ^ (k : ℕ)) ^ 7 = 1 :=
      zeta_fin_pow_pow_seven k
    change (zeta ^ (k : ℕ) * q.gamma) ^ 7 =
      directCyclotomicPhaseQuotient r 1
    calc
      (zeta ^ (k : ℕ) * q.gamma) ^ 7 =
          (zeta ^ (k : ℕ)) ^ 7 * q.gamma ^ 7 := by
        rw [mul_pow]
      _ = q.gamma ^ 7 := by rw [hz, one_mul]
      _ = directCyclotomicPhaseQuotient r 1 := q.quotient_eq.symm
  · change cyclotomicNormHom
      (zeta ^ (k : ℕ) * q.gamma) =
        (r.summit.residualRoot : ℤ)
    rw [map_mul, map_pow, cyclotomicNormHom_zeta, one_pow,
      q.norm_eq_residualRoot, one_mul]
  · trivial

theorem seventhPower_gain_of_ramifiedPrime_sq
    {x c : Ring} (h : x - c ∈ ramifiedPrime ^ 2) :
    x ^ 7 - c ^ 7 ∈ ramifiedPrime ^ 8 := by
  rw [ramifiedPrime_eq_span_uniformizer,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h ⊢
  rcases h with ⟨a, ha⟩
  have hseven : (7 : Ring) =
      ramifiedUniformizer ^ 6 * ramifiedSevenUnit := by
    exact ofReal_seven_eq_uniformizer_pow_six_mul_unit
  let b : Ring :=
    ramifiedSevenUnit * c ^ 6 * a +
      3 * ramifiedSevenUnit * c ^ 5 * ramifiedUniformizer ^ 2 * a ^ 2 +
      5 * ramifiedSevenUnit * c ^ 4 * ramifiedUniformizer ^ 4 * a ^ 3 +
      5 * ramifiedSevenUnit * c ^ 3 * ramifiedUniformizer ^ 6 * a ^ 4 +
      3 * ramifiedSevenUnit * c ^ 2 * ramifiedUniformizer ^ 8 * a ^ 5 +
      ramifiedSevenUnit * c * ramifiedUniformizer ^ 10 * a ^ 6 +
      ramifiedUniformizer ^ 6 * a ^ 7
  refine ⟨b, ?_⟩
  have hxc : x = c + ramifiedUniformizer ^ 2 * a := by
    linear_combination ha
  rw [hxc]
  dsimp [b]
  ring_nf
  rw [show (21 : Ring) = 3 * 7 by norm_num,
    show (35 : Ring) = 5 * 7 by norm_num]
  rw [hseven]
  ring

theorem normalizedRoot_sub_scalarLift_mem_ramifiedPrime_sq
    {x y z : ℕ} {source : CounterexamplePack x y z}
  {r : PrimitiveCounterexampleRamifiedProvenance source}
    (q : DirectCyclotomicNormalizedRootPacket source r) :
    q.gammaNorm -
        (scalarLift q.exactRoot.gamma : Ring) ∈ ramifiedPrime ^ 2 := by
  rw [q.gammaNorm_eq]
  exact q.phase_normalized

theorem normalizedRoot_seventhPower_gain
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (q : DirectCyclotomicNormalizedRootPacket source r) :
    q.gammaNorm ^ 7 -
        (scalarLift q.exactRoot.gamma : Ring) ^ 7 ∈ ramifiedPrime ^ 8 := by
  exact seventhPower_gain_of_ramifiedPrime_sq
    (normalizedRoot_sub_scalarLift_mem_ramifiedPrime_sq q)

theorem directRamifiedGapTail_mem_ramifiedPrime_pow_eight
    {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    directRamifiedGapTail r ∈ ramifiedPrime ^ 8 := by
  rw [ramifiedPrime_eq_span_uniformizer,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  refine ⟨ramifiedUniformizer ^ 27 * ramifiedSevenUnit ^ 6 *
      ofReal (r.summit.gapRoot : SevenRealCubicInt) ^ 7, ?_⟩
  simp [directRamifiedGapTail]
  ring

theorem normalizedRoot_endpointRight_sub_scalarLift_pow_mem_ramifiedPrime_pow_eight
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (q : DirectCyclotomicNormalizedRootPacket source r) :
    (r.summit.endpointRight : Ring) -
        (scalarLift q.exactRoot.gamma : Ring) ^ 7 ∈ ramifiedPrime ^ 8 := by
  have htail := directRamifiedGapTail_mem_ramifiedPrime_pow_eight r
  have hgain := normalizedRoot_seventhPower_gain q
  have hquotient :
      directCyclotomicPhaseQuotient r 1 -
          (r.summit.endpointRight : Ring) = directRamifiedGapTail r := by
    rw [directCyclotomicPhaseQuotient_one, directRamifiedQuotient]
    change (r.summit.endpointRight : Ring) + directRamifiedGapTail r -
      (r.summit.endpointRight : Ring) = directRamifiedGapTail r
    ring
  have hmid :
      directCyclotomicPhaseQuotient r 1 - q.gammaNorm ^ 7 ∈
        ramifiedPrime ^ 8 := by
    rw [q.gammaNorm_pow_eq_quotient]
    simpa only [sub_self] using (ramifiedPrime ^ 8).zero_mem
  have hsum1 := (ramifiedPrime ^ 8).add_mem
    ((ramifiedPrime ^ 8).neg_mem htail) hmid
  have hsum := (ramifiedPrime ^ 8).add_mem hsum1 hgain
  convert hsum using 1
  rw [← hquotient]
  ring

theorem cyclotomicNormHom_intCast (n : ℤ) :
    cyclotomicNormHom (n : Ring) = n ^ 6 := by
  rw [cyclotomicNormHom_apply]
  simp [QuadraticAlgebra.norm, SevenRealCubicInt.norm]
  ring

theorem fortyNine_dvd_of_intCast_mem_ramifiedPrime_pow_eight
    (n : ℤ) (h : (n : Ring) ∈ ramifiedPrime ^ 8) :
    (49 : ℤ) ∣ n := by
  rw [ramifiedPrime_eq_span_uniformizer,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
  rcases h with ⟨a, ha⟩
  have hn := congrArg cyclotomicNormHom ha
  rw [map_mul, map_pow, cyclotomicNormHom_intCast,
    cyclotomicNormHom_ramifiedUniformizer] at hn
  have hdiv8 : (7 : ℤ) ^ 8 ∣ n ^ 6 := by
    refine ⟨cyclotomicNormHom a, ?_⟩
    exact hn
  have hp : Nat.Prime 7 := by norm_num
  have hdiv1 : (7 : ℤ) ∣ n ^ 6 :=
    dvd_trans (by norm_num) hdiv8
  have h7n : (7 : ℤ) ∣ n := Int.Prime.dvd_pow' hp hdiv1
  rcases h7n with ⟨m, hm⟩
  have hdiv8m : (7 : ℤ) ^ 8 ∣ (7 * m) ^ 6 := by
    simpa [hm] using hdiv8
  rcases hdiv8m with ⟨k, hk⟩
  have hdiv2m : (7 : ℤ) ^ 2 ∣ m ^ 6 := by
    refine ⟨k, ?_⟩
    apply mul_left_cancel₀ (a := (7 : ℤ) ^ 6)
      (by norm_num)
    calc
      (7 : ℤ) ^ 6 * m ^ 6 = (7 * m) ^ 6 := by ring
      _ = (7 : ℤ) ^ 8 * k := hk
      _ = (7 : ℤ) ^ 6 * ((7 : ℤ) ^ 2 * k) := by ring
  have hdiv1m : (7 : ℤ) ∣ m ^ 6 :=
    dvd_trans (by norm_num) hdiv2m
  have h7m : (7 : ℤ) ∣ m := Int.Prime.dvd_pow' hp hdiv1m
  rcases h7m with ⟨l, hl⟩
  refine ⟨l, ?_⟩
  calc
    n = 7 * m := hm
    _ = 7 * (7 * l) := by rw [hl]
    _ = 49 * l := by ring

theorem fortyNine_dvd_endpointRight_sub_scalarLift_pow
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (q : DirectCyclotomicNormalizedRootPacket source r) :
    (49 : ℤ) ∣
      (r.summit.endpointRight : ℤ) -
        scalarLift q.exactRoot.gamma ^ 7 := by
  have hmem := normalizedRoot_endpointRight_sub_scalarLift_pow_mem_ramifiedPrime_pow_eight q
  have hcast :
      ((r.summit.endpointRight : ℤ) -
          scalarLift q.exactRoot.gamma ^ 7 : Ring) =
        (r.summit.endpointRight : Ring) -
          (scalarLift q.exactRoot.gamma : Ring) ^ 7 := by
    norm_num
  rw [hcast] at hmem
  apply fortyNine_dvd_of_intCast_mem_ramifiedPrime_pow_eight
    ((r.summit.endpointRight : ℤ) -
      scalarLift q.exactRoot.gamma ^ 7)
  simpa only [Int.cast_sub, Int.cast_pow] using hmem

theorem endpointRight_eq_scalarLift_pow_mod_fortyNine
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (q : DirectCyclotomicNormalizedRootPacket source r) :
    ((r.summit.endpointRight : ℤ) : ZMod 49) =
      (scalarLift q.exactRoot.gamma : ZMod 49) ^ 7 := by
  have hdvd := fortyNine_dvd_endpointRight_sub_scalarLift_pow q
  have hz :
      (((r.summit.endpointRight : ℤ) -
          scalarLift q.exactRoot.gamma ^ 7 : ℤ) : ZMod 49) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 49).mpr hdvd
  rw [Int.cast_sub, Int.cast_pow] at hz
  exact sub_eq_zero.mp hz

end SevenCyclotomicDegreeSixInt

end

end DkMath.FLT.Seven
