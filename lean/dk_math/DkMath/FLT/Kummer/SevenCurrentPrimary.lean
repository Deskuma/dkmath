/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.SevenRealPrimaryGap

/-!
# 現在の carrier の一次合同：必要条件の検査と根の選択

現在の gap は実三次軸の32乗、従って円分分岐因子の64乗で割れる。
提案された 7*(zeta^j-1)∣gap は満たされ、排除条件にはならない。
receiver の同じ因子表示を T_j で補正し、根を剰余1に正規化してから
実三次 PrimaryPacket を構成する。元の根・単元・正規化単元を保持する。
-/

open DkMath.FLT.Seven DkMath.FLT.Kummer.SevenPrimaryNorm
open DkMath.FLT.Seven.SevenRealCubic
open DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierRamification
open DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierPower
open DkMath.Lib.Algebra

namespace DkMath.FLT.Kummer.SevenRealGN

noncomputable section
open SevenCyclotomicDegreeSixInt

variable {a b d : ℕ} {source : CounterexamplePack a b d}
variable {r : PrimitiveCounterexampleRamifiedProvenance source}
variable {p : DirectRealCubicRootPacket source r}
variable {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}

/-- 現在の gap の深度。単なる lambda^2 ではなく lambda^64 の可除性を供給する。 -/
theorem current_gap_uniformizer_pow64 (p : DirectRealCubicRootPacket source r) :
    ramifiedUniformizer ^ 64 ∣ ofReal (SevenRealCubicInt.rotateEquiv p.rho - p.rho) := by
  obtain ⟨w, hw⟩ := directOrbit_gap_axis_pow32_dvd p
  refine ⟨zetaInv ^ 32 * ofReal w, ?_⟩
  change ofReal (directOrbitGap p) = _
  rw [hw, map_mul, map_pow, ofReal_eisensteinAxis_eq]
  ring

/-- 非自明位相の分岐因子は lambda と同伴なので、lambda を割る。 -/
theorem phaseRamifier_dvd_uniformizer {i : ℕ} (hi : i ∈ (Finset.range 7).erase 0) :
    zeta ^ i - 1 ∣ ramifiedUniformizer := by
  refine ⟨(↑(GNRamifierTwist hi)⁻¹ : C), ?_⟩
  rw [← GNRamifierTwist_spec hi]
  have hc : (GNRamifierTwist hi : C) * (↑(GNRamifierTwist hi)⁻¹ : C) = 1 :=
    (GNRamifierTwist hi).val_inv
  calc
    ramifiedUniformizer = ramifiedUniformizer *
        ((GNRamifierTwist hi : C) * (↑(GNRamifierTwist hi)⁻¹ : C)) := by rw [hc, mul_one]
    _ = _ := by ring

/-- 提案された必要条件は現在の gap に対して既に成立する。一次合同は仮定しない。
これは gap 条件による現在の source の排除ができないことを意味する。 -/
theorem current_gap_seven_phase_dvd (p : DirectRealCubicRootPacket source r) {i : ℕ}
    (hi : i ∈ (Finset.range 7).erase 0) :
    (7 : C) * (zeta ^ i - 1) ∣ ofReal (SevenRealCubicInt.rotateEquiv p.rho - p.rho) := by
  have hd : (7 : C) * (zeta ^ i - 1) ∣ ramifiedUniformizer ^ 7 := by
    simpa only [← pow_succ] using mul_dvd_mul seven_dvd_uniformizer_six (phaseRamifier_dvd_uniformizer hi)
  exact hd.trans ((pow_dvd_pow ramifiedUniformizer (by decide : 7 ≤ 64)).trans
    (current_gap_uniformizer_pow64 p))

/-- 現在の非零 source。二乗分岐素イデアルに属さない定理から直接得る。 -/
theorem current_source_ne_zero (c : CurrentCommonPrimeCyclotomicPacket h q) :
    currentLinearCarrier c ≠ 0 := by
  intro hz
  apply currentLinearCarrier_not_mem_ramifiedPrime_sq c
  rw [hz]
  exact Ideal.zero_mem _

/-- receiver のどの剥離根も非分岐。単元や根を選び直す前に証明できる。 -/
theorem current_root_away (c : CurrentCommonPrimeCyclotomicPacket h q)
    (epsilon : Cˣ) (beta : C)
    (hf : currentLinearCarrier c = ramifiedUniformizer * ((epsilon : C) * beta ^ 7)) :
    ¬ ramifiedUniformizer ∣ beta := by
  rintro ⟨w, hw⟩
  apply currentLinearCarrier_not_mem_ramifiedPrime_sq c
  rw [ramifiedPrime_eq_span_uniformizer, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  refine ⟨(epsilon : C) * ramifiedUniformizer ^ 6 * w ^ 7, ?_⟩
  rw [hf, hw]
  ring

/-- receiver の補正単元が一次になるのは、同じ剥離根の剰余が1のときに限る。
元の選択に無条件な一次合同を課すことはできない。 -/
theorem current_primary_iff_root_residue_one (c : CurrentCommonPrimeCyclotomicPacket h q)
    (epsilon : Cˣ) (beta : C)
    (hf : currentLinearCarrier c = ramifiedUniformizer * ((epsilon : C) * beta ^ 7)) :
    RealPrimary (epsilon * (GNRamifierTwist (current_phase_index_mem c.phase))⁻¹) (-p.rho) ↔
      ramifiedEval beta = 1 := by
  have hsource : realGNSource (SevenRealCubicInt.rotateEquiv p.rho - p.rho) p.rho
      (phaseInverseExponent c.phase) = ramifiedUniformizer * ((epsilon : C) * beta ^ 7) :=
    (currentLinearCarrier_eq_realGNSource c).symm.trans hf
  exact primary_iff_root_residue_one (current_phase_index_mem c.phase) _ _
    ((pow_dvd_pow ramifiedUniformizer (by decide : 2 ≤ 64)).trans (current_gap_uniformizer_pow64 p))
    (current_gap_seven_phase_dvd p (current_phase_index_mem c.phase)) p.thetaResidue_ne_zero
    (factor_after_ramifier_twist (current_phase_index_mem c.phase) epsilon beta hsource)

/-- 与えられた receiver の根と単元を保管して、同じ source の一次パケットへ拡張する。
初期正規化の t は任意の単元でよく、正規化後の許容遷移と混同しない。
出力の gamma=t*beta と delta=(epsilon*T_j^-1)*t^-7 を同じ t で保証する。 -/
theorem exists_current_primary_extension (c : CurrentCommonPrimeCyclotomicPacket h q)
    (epsilon : Cˣ) (beta : C)
    (hf : currentLinearCarrier c = ramifiedUniformizer * ((epsilon : C) * beta ^ 7)) :
    ∃ t : Cˣ, ∃ Q : PrimaryPacket,
      Q.gap = SevenRealCubicInt.rotateEquiv p.rho - p.rho ∧ Q.parameter = p.rho ∧
      Q.phase = phaseInverseExponent c.phase ∧ Q.source = currentLinearCarrier c ∧
      Q.gamma = (t : C) * beta ∧
      Q.delta = (epsilon * (GNRamifierTwist (current_phase_index_mem c.phase))⁻¹) * t⁻¹ ^ 7 ∧
      ramifiedEval Q.gamma = 1 ∧ Ideal.span ({Q.gamma} : Set C) = Ideal.span ({beta} : Set C) := by
  have hb := current_root_away c epsilon beta hf
  obtain ⟨t, ht⟩ := exists_root_residue_normalizer beta hb
  let delta := epsilon * (GNRamifierTwist (current_phase_index_mem c.phase))⁻¹
  have hsource : realGNSource (SevenRealCubicInt.rotateEquiv p.rho - p.rho) p.rho
      (phaseInverseExponent c.phase) = ramifiedUniformizer * ((epsilon : C) * beta ^ 7) :=
    (currentLinearCarrier_eq_realGNSource c).symm.trans hf
  have hfac := (factor_after_ramifier_twist (current_phase_index_mem c.phase) epsilon beta hsource).trans
    (root_unit_gauge_identity (zeta ^ phaseInverseExponent c.phase - 1) beta delta t 7)
  let Q : PrimaryPacket := {
    gap := SevenRealCubicInt.rotateEquiv p.rho - p.rho
    parameter := p.rho
    phase := phaseInverseExponent c.phase
    phase_mem := current_phase_index_mem c.phase
    delta := delta * t⁻¹ ^ 7
    gamma := (t : C) * beta
    source_ne_zero := by rw [← currentLinearCarrier_eq_realGNSource c]; exact current_source_ne_zero c
    factor := hfac
    primary := primary_of_root_residue_one (current_phase_index_mem c.phase) _ _
      (current_gap_seven_phase_dvd p (current_phase_index_mem c.phase)) hfac ht
    root_away := by
      intro hd
      apply hb
      have hm := dvd_mul_of_dvd_right hd (↑t⁻¹ : C)
      have hc : (↑t⁻¹ : C) * (t : C) = 1 := t.inv_val
      simpa only [← mul_assoc, hc, one_mul] using hm }
  exact ⟨t, Q, rfl, rfl, rfl, (currentLinearCarrier_eq_realGNSource c).symm, rfl, rfl,
    ht, Ideal.span_singleton_mul_left_unit t.isUnit beta⟩

/-- 既存 receiver を実際に呼び、現在の source の一次パケットを供給する。
元の epsilon,beta とその因子表示、同じ t による補正、元の Fermat 方程式を残す。
FLT7 の矛盾や小さい次の解は、この構成の結論ではない。 -/
theorem currentCarrier_primary_packet_receiver (c : CurrentCommonPrimeCyclotomicPacket h q) :
    ∃ epsilon : Cˣ, ∃ beta : C,
      currentLinearCarrier c = ramifiedUniformizer * ((epsilon : C) * beta ^ 7) ∧
      (∃ t : Cˣ, ∃ Q : PrimaryPacket,
        Q.gap = SevenRealCubicInt.rotateEquiv p.rho - p.rho ∧ Q.parameter = p.rho ∧
        Q.phase = phaseInverseExponent c.phase ∧ Q.source = currentLinearCarrier c ∧
        Q.gamma = (t : C) * beta ∧
        Q.delta = (epsilon * (GNRamifierTwist (current_phase_index_mem c.phase))⁻¹) * t⁻¹ ^ 7 ∧
        ramifiedEval Q.gamma = 1 ∧ Ideal.span ({Q.gamma} : Set C) = Ideal.span ({beta} : Set C)) ∧
      Fermat7Equation a b d := by
  obtain ⟨w, beta, hw, hfactor, hFermat⟩ := currentCarrier_ramified_element_receiver c
  have hf : currentLinearCarrier c = ramifiedUniformizer * ((hw.unit : C) * beta ^ 7) := by
    rw [IsUnit.unit_spec]
    exact hfactor.trans (mul_assoc _ _ _)
  exact ⟨hw.unit, beta, hf, exists_current_primary_extension c hw.unit beta hf, hFermat⟩

end

end DkMath.FLT.Kummer.SevenRealGN
