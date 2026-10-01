/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.Seven.PrimeTraceOneDirectCyclotomicCMUnitPhase

#print "file: DkMath.FLT.Seven.PrimeTraceOneDirectCyclotomicCMTorsionPhase"

namespace DkMath.FLT.Seven

noncomputable section

set_option linter.style.longLine false

open scoped NumberField
open scoped BigOperators
open NumberField
open SevenCyclotomicDegreeSixInt

local notation "K" => CyclotomicField 7 ℚ

local instance cyclotomicExtension :
    IsCyclotomicExtension ({7} : Set ℕ) ℚ K :=
  CyclotomicField.isCyclotomicExtension 7 ℚ

local instance cmField : NumberField.IsCMField K :=
  IsCyclotomicExtension.Rat.isCMField K
    ⟨7, Set.mem_singleton 7, by norm_num⟩

namespace SevenCyclotomicDegreeSixInt

noncomputable def starAlgHom : Ring →ₐ[ℤ] Ring where
  toFun := star
  map_one' := by simp
  map_mul' := by intro x y; simp
  map_zero' := by simp
  map_add' := by intro x y; simp
  commutes' := by intro n; simp

theorem abstractZeta_complexConj :
    NumberField.IsCMField.complexConj K
        (IsCyclotomicExtension.zeta 7 ℚ K) =
      (IsCyclotomicExtension.zeta 7 ℚ K)⁻¹ := by
  let hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta 7 ℚ K) 7 :=
    IsCyclotomicExtension.zeta_spec 7 ℚ K
  let u : (𝓞 K)ˣ :=
    (hζ.toInteger_isPrimitiveRoot.isUnit (by norm_num)).unit
  have hu_prim_unit : IsPrimitiveRoot u 7 :=
    hζ.toInteger_isPrimitiveRoot.isUnit_unit (by norm_num)
  have hu_prim : IsPrimitiveRoot (u : 𝓞 K) 7 :=
    (IsPrimitiveRoot.coe_units_iff (M := 𝓞 K) (ζ := u)).mpr hu_prim_unit
  have hu_pow : u ^ 7 = 1 := by
    apply Units.ext
    change (u : 𝓞 K) ^ 7 = 1
    exact hu_prim.pow_eq_one
  have hu_torsion : u ∈ NumberField.Units.torsion K := by
    rw [NumberField.Units.torsion, CommGroup.mem_torsion,
      isOfFinOrder_iff_pow_eq_one]
    exact ⟨7, by norm_num, hu_pow⟩
  have h := NumberField.IsCMField.complexConj_torsion K
    (⟨u, hu_torsion⟩ : NumberField.Units.torsion K)
  have hu_coe : (u : 𝓞 K) = hζ.toInteger :=
    (hζ.toInteger_isPrimitiveRoot.isUnit (by norm_num)).unit_spec
  rw [← NumberField.RingOfIntegers.coe_eq_algebraMap] at h
  change NumberField.IsCMField.complexConj K ((u : 𝓞 K) : K) =
    ((u : 𝓞 K) : K)⁻¹ at h
  rw [hu_coe] at h
  change NumberField.IsCMField.complexConj K (hζ.toInteger : K) =
    (hζ.toInteger : K)⁻¹ at h
  have hfield : (hζ.toInteger : K) =
      IsCyclotomicExtension.zeta 7 ℚ K := hζ.coe_toInteger
  calc
    NumberField.IsCMField.complexConj K
          (IsCyclotomicExtension.zeta 7 ℚ K) =
        NumberField.IsCMField.complexConj K (hζ.toInteger : K) := by
          rw [hfield]
    _ = (hζ.toInteger : K)⁻¹ := h
    _ = (IsCyclotomicExtension.zeta 7 ℚ K)⁻¹ := by rw [hfield]

private theorem abstractZeta_inv_eq_pow_six :
    (IsCyclotomicExtension.zeta 7 ℚ K)⁻¹ =
      (IsCyclotomicExtension.zeta 7 ℚ K) ^ 6 := by
  let hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta 7 ℚ K) 7 :=
    IsCyclotomicExtension.zeta_spec 7 ℚ K
  have hzeta0 : IsCyclotomicExtension.zeta 7 ℚ K ≠ 0 :=
    hζ.ne_zero (by norm_num)
  apply mul_left_cancel₀ hzeta0
  rw [mul_inv_cancel₀ hzeta0, mul_comm, ← pow_succ, hζ.pow_eq_one]

theorem cyclotomicIntegralGenerator_complexConj :
    NumberField.IsCMField.ringOfIntegersComplexConj K
        cyclotomicIntegralGenerator =
      cyclotomicIntegralGenerator ^ 6 := by
  apply NumberField.RingOfIntegers.ext
  rw [NumberField.IsCMField.coe_ringOfIntegersComplexConj,
    cyclotomicIntegralGenerator_coe, abstractZeta_complexConj,
    abstractZeta_inv_eq_pow_six]
  simp [cyclotomicIntegralGenerator_coe]

theorem ringOfIntegersToRing_complexConj_coherence :
    ∀ x : 𝓞 K,
      ringOfIntegersToRingEquiv
          (NumberField.IsCMField.ringOfIntegersComplexConj K x) =
        star (ringOfIntegersToRingEquiv x) := by
  intro x
  let f : (𝓞 K) →ₐ[ℤ] Ring :=
    ringOfIntegersToRingEquiv.toAlgHom.comp
      (AlgEquiv.restrictScalars ℤ
        (NumberField.IsCMField.ringOfIntegersComplexConj K)).toAlgHom
  let g : (𝓞 K) →ₐ[ℤ] Ring :=
    starAlgHom.comp ringOfIntegersToRingEquiv.toAlgHom
  have hfg : f = g := by
    apply AlgHom.ext_of_adjoin_eq_top
      adjoin_cyclotomicIntegralGenerator_eq_top
    intro y hy
    rw [Set.mem_singleton_iff.mp hy]
    dsimp [f, g]
    rw [cyclotomicIntegralGenerator_complexConj,
      map_pow, ringOfIntegersToRing_cyclotomicIntegralGenerator]
    change zeta ^ 6 = star zeta
    rw [star_zeta, zetaInv_eq_pow_six]
  have hx := congrArg (fun h : (𝓞 K) →ₐ[ℤ] Ring => h x) hfg
  simpa [f, g, starAlgHom] using hx

theorem cyclotomicTorsionOrder_eq :
    NumberField.Units.torsionOrder K = 14 := by
  rw [IsCyclotomicExtension.Rat.torsionOrder_eq (n := 7)]
  norm_num

noncomputable def ringOfIntegersUnitsEquiv :
    (𝓞 K)ˣ ≃* Ringˣ :=
  Units.mapEquiv ringOfIntegersToRingEquiv.toRingEquiv.toMulEquiv

@[simp] theorem ringOfIntegersUnitsEquiv_apply (u : (𝓞 K)ˣ) :
    ringOfIntegersUnitsEquiv u = Units.map ringOfIntegersToRingEquiv.toRingHom u :=
  rfl

theorem unitsComplexConj_coherence (u : (𝓞 K)ˣ) :
    ringOfIntegersUnitsEquiv (NumberField.IsCMField.unitsComplexConj K u) =
      starUnit (ringOfIntegersUnitsEquiv u) := by
  have hconj :
      (RingOfIntegers.mapRingEquiv (NumberField.IsCMField.complexConj K).toRingEquiv)
          (u : 𝓞 K) =
        NumberField.IsCMField.ringOfIntegersComplexConj K (u : 𝓞 K) := by
    apply NumberField.RingOfIntegers.ext
    rfl
  apply Units.ext
  change ringOfIntegersToRingEquiv
      ((NumberField.IsCMField.unitsComplexConj K u : (𝓞 K)ˣ) : 𝓞 K) =
    star (ringOfIntegersToRingEquiv (u : 𝓞 K))
  rw [show (NumberField.IsCMField.unitsComplexConj K u : (𝓞 K)ˣ) =
      Units.map (RingOfIntegers.mapRingEquiv
        (NumberField.IsCMField.complexConj K).toRingEquiv).toMonoidHom u by rfl]
  change ringOfIntegersToRingEquiv
      (RingOfIntegers.mapRingEquiv
        (NumberField.IsCMField.complexConj K).toRingEquiv (u : 𝓞 K)) =
    star (ringOfIntegersToRingEquiv (u : 𝓞 K))
  rw [hconj]
  exact ringOfIntegersToRing_complexConj_coherence (u : 𝓞 K)

theorem quadraticNormUnit_mul_starUnit (delta : Ringˣ) :
    delta * starUnit delta =
      ofRealUnit (quadraticNormUnit delta) := by
  apply Units.ext
  change (delta : Ring) * star (delta : Ring) =
    ofReal (quadraticNormUnit delta : SevenRealCubicInt)
  rw [quadraticNormUnit_apply]
  symm
  exact QuadraticAlgebra.algebraMap_norm_eq_mul_star (delta : Ring)

theorem starUnit_eq_inv_of_quadraticNormUnit_eq_one
    (delta : Ringˣ)
  (hnorm : quadraticNormUnit delta = 1) :
    starUnit delta = delta⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [quadraticNormUnit_mul_starUnit, hnorm]
  simp [ofRealUnit]

theorem unitsComplexConj_eq_inv_of_concrete_norm_one
    (delta : Ringˣ)
    (hnorm : quadraticNormUnit delta = 1) :
    NumberField.IsCMField.unitsComplexConj K
        (ringOfIntegersUnitsEquiv.symm delta) =
      (ringOfIntegersUnitsEquiv.symm delta)⁻¹ := by
  apply ringOfIntegersUnitsEquiv.injective
  rw [unitsComplexConj_coherence]
  simp [map_inv, starUnit_eq_inv_of_quadraticNormUnit_eq_one delta hnorm]

theorem concrete_norm_one_pow_twentyEight
    (delta : Ringˣ)
    (hnorm : quadraticNormUnit delta = 1) :
    delta ^ 28 = 1 := by
  let Delta : (𝓞 K)ˣ := ringOfIntegersUnitsEquiv.symm delta
  have hconj : NumberField.IsCMField.unitsComplexConj K Delta = Delta⁻¹ :=
    unitsComplexConj_eq_inv_of_concrete_norm_one delta hnorm
  have ht := NumberField.Units.pow_torsionOrder_eq_one K
    (NumberField.IsCMField.unitsMulComplexConjInv K Delta).property
  have ht' :
      (Delta * (NumberField.IsCMField.unitsComplexConj K Delta)⁻¹) ^ 14 = 1 := by
    simpa [cyclotomicTorsionOrder_eq,
      NumberField.IsCMField.unitsMulComplexConjInv_apply] using ht
  rw [hconj] at ht'
  have hDelta : Delta ^ 28 = 1 := by
    calc
      Delta ^ 28 = (Delta ^ 2) ^ 14 := by
        rw [← pow_mul]
      _ = 1 := by simpa [pow_two] using ht'
  calc
    delta ^ 28 = (ringOfIntegersUnitsEquiv Delta) ^ 28 := by
      rw [ringOfIntegersUnitsEquiv.apply_symm_apply]
    _ = ringOfIntegersUnitsEquiv (Delta ^ 28) := by
      rw [map_pow]
    _ = 1 := by rw [hDelta]; simp

theorem concrete_phase_pow_fourteen
    (delta : Ringˣ) :
    (delta / starUnit delta) ^ 14 = 1 := by
  let Delta : (𝓞 K)ˣ := ringOfIntegersUnitsEquiv.symm delta
  have ht := NumberField.Units.pow_torsionOrder_eq_one K
    (NumberField.IsCMField.unitsMulComplexConjInv K Delta).property
  have ht' :
      (Delta * (NumberField.IsCMField.unitsComplexConj K Delta)⁻¹) ^ 14 = 1 := by
    simpa [cyclotomicTorsionOrder_eq,
      NumberField.IsCMField.unitsMulComplexConjInv_apply] using ht
  have ht14 :
      (↑(NumberField.IsCMField.unitsMulComplexConjInv K Delta) : (𝓞 K)ˣ) ^ 14 = 1 := by
    simpa [cyclotomicTorsionOrder_eq] using ht
  have hmap :
      ringOfIntegersUnitsEquiv
          (↑(NumberField.IsCMField.unitsMulComplexConjInv K Delta) : (𝓞 K)ˣ) =
        delta / starUnit delta := by
    rw [NumberField.IsCMField.unitsMulComplexConjInv_apply]
    change ringOfIntegersUnitsEquiv
        (Delta * (NumberField.IsCMField.unitsComplexConj K Delta)⁻¹) =
      delta / starUnit delta
    rw [map_mul, map_inv, unitsComplexConj_coherence]
    simp [Delta, div_eq_mul_inv]
  rw [← hmap, ← map_pow]
  rw [ht14]
  simp

theorem unit_eq_one_of_pow_twentyEight_eq_one_of_sub_one_mem_sevenIdeal
    (delta : Ringˣ)
    (hpow : delta ^ 28 = 1)
    (hcong : ((delta : Ring) - 1) ∈ sevenIdeal) :
    delta = 1 := by
  let J : Ideal Ring := Ideal.span ({(49 : Ring)} : Set Ring)
  rw [sevenIdeal, Ideal.mem_span_singleton] at hcong
  rcases hcong with ⟨a, ha⟩
  have hdelta : (delta : Ring) = 1 + (7 : Ring) * a := by
    linear_combination ha
  have hlin : ∀ n : ℕ,
      (delta : Ring) ^ n - (1 + (7 : Ring) * (n : Ring) * a) ∈ J := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hmul :
            ((delta : Ring) ^ n -
                (1 + (7 : Ring) * (n : Ring) * a)) * (delta : Ring) ∈ J :=
          J.mul_mem_right (delta : Ring) ih
        have hrem :
            (1 + (7 : Ring) * (n : Ring) * a) * (delta : Ring) -
                (1 + (7 : Ring) * ((n + 1 : ℕ) : Ring) * a) ∈ J := by
          rw [hdelta]
          have h49 : (49 : Ring) ∈ J := by
            exact Ideal.subset_span (by simp)
          convert J.mul_mem_right ((n : Ring) * a ^ 2) h49 using 1
          norm_num [Nat.cast_add, Nat.cast_one]
          ring
        rw [pow_succ]
        convert J.add_mem hmul hrem using 1
        ring
  have hbase :
      (Finset.sum (Finset.range 28) (fun n =>
        (1 + (7 : Ring) * (n : Ring) * a)) - 28) ∈ J := by
    have h49 : (49 : Ring) ∈ J := by
      exact Ideal.subset_span (by simp)
    convert J.mul_mem_right (54 * a) h49 using 1
    norm_num [Finset.sum_range_succ]
    ring
  have hsumdiff :
      (Finset.sum (Finset.range 28) (fun n => (delta : Ring) ^ n)) -
          (Finset.sum (Finset.range 28) (fun n =>
            (1 + (7 : Ring) * (n : Ring) * a))) ∈ J := by
    simpa only [Finset.sum_sub_distrib] using
      J.sum_mem (fun n _ => hlin n)
  have hsum :
      (Finset.sum (Finset.range 28) (fun n => (delta : Ring) ^ n)) - 28 ∈ J := by
    convert J.add_mem hsumdiff hbase using 1
    ring
  have hgeom : ∀ x : Ring, ∀ n : ℕ,
      x ^ n - 1 = (x - 1) * Finset.sum (Finset.range n) (fun k => x ^ k) := by
    intro x n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, Finset.sum_range_succ]
        calc
          x ^ n * x - 1 = (x ^ n - 1) + x ^ n * (x - 1) := by ring
          _ = (x - 1) * (Finset.sum (Finset.range n) (fun k => x ^ k) + x ^ n) := by
            rw [ih]
            ring
  have hprod :
      ((delta : Ring) - 1) *
          Finset.sum (Finset.range 28) (fun n => (delta : Ring) ^ n) = 0 := by
    have h := hgeom (delta : Ring) 28
    have hpow' : (delta : Ring) ^ 28 = 1 := by
      rw [← Units.val_pow_eq_pow_val]
      simpa only [Units.val_one] using congrArg Units.val hpow
    rw [hpow'] at h
    simpa using h.symm
  by_contra hne
  have hneVal : (delta : Ring) ≠ 1 := by
    intro h
    apply hne
    exact Units.ext h
  have hsumzero :
      Finset.sum (Finset.range 28) (fun n => (delta : Ring) ^ n) = 0 := by
    exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hneVal)
  have h28 : (28 : Ring) ∈ J := by
    have hneg := J.neg_mem hsum
    simpa [hsumzero] using hneg
  have hnot : (28 : Ring) ∉ J := by
    change (28 : Ring) ∉ Ideal.span ({(49 : Ring)} : Set Ring)
    intro h
    rw [Ideal.mem_span_singleton] at h
    rcases h with ⟨k, hk⟩
    have hcoord := congrArg (fun x : Ring => x.re.fst) hk
    have h49re : ((49 : Ring) * k).re.fst = 49 * k.re.fst := by
      rw [QuadraticAlgebra.re_mul]
      change ((49 : SevenRealCubicInt) * k.re +
          (-1 : SevenRealCubicInt) * (0 : SevenRealCubicInt) * k.im).fst =
        49 * k.re.fst
      have h49 : (49 : SevenRealCubicInt) = ⟨(49 : ℤ), 0, 0⟩ := rfl
      rw [h49]
      norm_num [SevenRealCubicInt.fst_mul, SevenRealCubicInt.fst_add,
        SevenRealCubicInt.fst_neg]
    have hcoord' : (28 : ℤ) = 49 * k.re.fst := by
      calc
        (28 : ℤ) = ((28 : Ring).re.fst) := by
          change (28 : ℤ) = (28 : SevenRealCubicInt).fst
          rfl
        _ = ((49 : Ring) * k).re.fst := hcoord
        _ = 49 * k.re.fst := h49re
    omega
  exact hnot h28

theorem relativeNormOneScalarUnitAtSeven_unconditional :
    RelativeNormOneScalarUnitAtSeven := by
  intro delta hnorm hcong
  apply unit_eq_one_of_pow_twentyEight_eq_one_of_sub_one_mem_sevenIdeal delta
  · exact concrete_norm_one_pow_twentyEight delta hnorm
  · exact hcong

theorem DirectCyclotomicChosenQuotientPowerPacket.unit_isSeventhPower_unconditional
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectCyclotomicChosenQuotientPowerPacket source r) :
    ∃ w : Ringˣ, p.unit_isUnit.unit = w ^ 7 :=
  p.unit_isSeventhPower_of_phase_target
    relativeNormOneScalarUnitAtSeven_unconditional

theorem DirectCyclotomicChosenQuotientPowerPacket.exists_quotient_seventhPower_unconditional
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectCyclotomicChosenQuotientPowerPacket source r) :
    ∃ gamma : Ring, directCyclotomicPhaseQuotient r 1 = gamma ^ 7 :=
  p.exists_quotient_seventhPower_of_phase_target
    relativeNormOneScalarUnitAtSeven_unconditional

theorem DirectCyclotomicChosenQuotientPowerPacket.exists_directLinearFactor_seventhPower_unconditional
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectCyclotomicChosenQuotientPowerPacket source r) :
    ∃ gamma : Ring,
      directLinearFactor r = ramifiedUniformizer * gamma ^ 7 :=
  p.exists_directLinearFactor_seventhPower_of_phase_target
    relativeNormOneScalarUnitAtSeven_unconditional

end SevenCyclotomicDegreeSixInt

end

end DkMath.FLT.Seven
