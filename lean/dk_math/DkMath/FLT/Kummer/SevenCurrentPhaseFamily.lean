/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.SevenCurrentUnitSeventh

#print "file: DkMath.FLT.Kummer.SevenCurrentPhaseFamily"

/-! # 同じ current 二端点の六因子の同時七乗表示

既存の全六位相のイデアル冪抽出に、各位相の一次合同と整数合同を供給する。
Galois 回転で係数を動かさず、同じ rotate(rho),rho の因子族を構成する。
既に選んだ current 根をそのまま含む族への拡張も可能。
新しい FLT 反例や厳密減少は、これらの因子表示の結論ではない。
-/

namespace DkMath.FLT.Kummer.SevenRealGN

open DkMath.FLT.Seven DkMath.FLT.Kummer.SevenPrimaryNorm
open DkMath.FLT.Seven.SevenRealCubic
open DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierRamification
open DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierPower
open DkMath.Lib.Algebra
open SevenCyclotomicDegreeSixInt

noncomputable section

variable {a b d : ℕ} {source : CounterexamplePack a b d}
variable {r : PrimitiveCounterexampleRamifiedProvenance source}
variable {p : DirectRealCubicRootPacket source r}

/-- 非自明位相 j の範囲から、素数7で割れないことを取り出す。 -/
theorem phase_index_not_seven_dvd {j : ℕ} (hj : j ∈ (Finset.range 7).erase 0) : ¬ 7 ∣ j := by
  have h := Finset.mem_erase.mp hj
  have hlt := Finset.mem_range.mp h.2
  exact Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero h.1) hlt

/-- 任意の非自明位相について、剥離根は非分岐。選択素数の剰余アドレスを使わない。 -/
theorem phase_root_away_of_factor {j : ℕ} (hj : j ∈ (Finset.range 7).erase 0)
    (epsilon : Cˣ) (beta : C)
    (hf : phaseCarrier p j = ramifiedUniformizer * ((epsilon : C) * beta ^ 7)) :
    ¬ ramifiedUniformizer ∣ beta := by
  rintro ⟨w, hw⟩
  apply phaseCarrier_not_mem_ramifiedPrime_sq p j (phase_index_not_seven_dvd hj)
  rw [ramifiedPrime_eq_span_uniformizer, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  refine ⟨(epsilon : C) * ramifiedUniformizer ^ 6 * w ^ 7, ?_⟩
  rw [hf, hw]
  ring

/-- 全位相のイデアル七乗性から、任意の位相の元の分解を取り出す。
類数1による主イデアル化を使い、未解析単元 epsilon はこの段階では保持する。 -/
theorem phase_ramified_element_receiver (h : DirectOrbitCanonicalCommonFactorPacket p)
    {j : ℕ} (hj : j ∈ (Finset.range 7).erase 0) :
    ∃ (epsilon : Cˣ) (beta : C),
      phaseCarrier p j = ramifiedUniformizer * ((epsilon : C) * beta ^ 7) := by
  have hm := Finset.mem_erase.mp hj
  obtain ⟨J, hJ⟩ := normalizedPhaseIdeal_seventh_power h j
    (Nat.pos_of_ne_zero hm.1) (Finset.mem_range.mp hm.2)
  obtain ⟨u, hu, he⟩ := unitMulPowOfSpanEqPow hJ
  refine ⟨hu.unit, Submodule.IsPrincipal.generator J, ?_⟩
  rw [phaseCarrier_eq_uniformizer_mul_quotient, he, IsUnit.unit_spec]

/-- 同じ二端点の任意の非自明位相を、単元を残さない七乗表示にする。
深い gap、根の剰余正規化、回転固定性、整数合同版単元補題を各位相で適用する。 -/
theorem exists_phase_unit_free_root (h : DirectOrbitCanonicalCommonFactorPacket p)
    {j : ℕ} (hj : j ∈ (Finset.range 7).erase 0) :
    ∃ theta : C, phaseCarrier p j = (zeta ^ j - 1) * theta ^ 7 ∧
      ¬ ramifiedUniformizer ∣ theta := by
  obtain ⟨epsilon, beta, hf⟩ := phase_ramified_element_receiver h hj
  have hb := phase_root_away_of_factor hj epsilon beta hf
  have hs : realGNSource (SevenRealCubicInt.rotateEquiv p.rho - p.rho) p.rho j =
      ramifiedUniformizer * ((epsilon : C) * beta ^ 7) :=
    (realGNSource_sub_coordinates _ _ _).trans hf
  let delta := epsilon * (GNRamifierTwist hj)⁻¹
  have hfac := factor_after_ramifier_twist hj epsilon beta hs
  obtain ⟨t, ht⟩ := exists_root_residue_normalizer beta hb
  have hgauge := hfac.trans (root_unit_gauge_identity (zeta ^ j - 1) beta delta t 7)
  have hprimary := primary_of_root_residue_one hj _ _ (current_gap_seven_phase_dvd p hj) hgauge ht
  obtain ⟨kappa, hkappa⟩ := realPrimary_seventh_of_rotation_fixed p.rho
    (current_rotation_gap_seven_dvd p) (delta * t⁻¹ ^ 7) hprimary
  refine ⟨(kappa : C) * ((t : C) * beta), ?_, ?_⟩
  · rw [phaseCarrier, ← realGNSource_sub_coordinates (SevenRealCubicInt.rotateEquiv p.rho) p.rho j,
      hgauge, hkappa]
    change (zeta ^ j - 1) * ((kappa : C) ^ 7 * ((t : C) * beta) ^ 7) = _
    simp only [mul_pow]
  · intro hd
    have hm := dvd_mul_of_dvd_right hd (↑(kappa * t)⁻¹ : C)
    have hc : (↑(kappa * t)⁻¹ : C) * (↑(kappa * t) : C) = 1 := (kappa * t).inv_val
    have he : (↑(kappa * t)⁻¹ : C) * ((kappa : C) * ((t : C) * beta)) = beta := by
      calc
        _ = (↑(kappa * t)⁻¹ : C) * ((↑(kappa * t) : C) * beta) := by
          simp only [Units.val_mul, mul_assoc]
        _ = beta := by rw [← mul_assoc, hc, one_mul]
    apply hb
    simpa only [he] using hm

/-- 同じ二端点の六因子の同時表示。添字 i は実際の位相 i.val+1 に対応する。
個別の存在命題を、同じ関数 root を使う一つの証人へ束ねる。 -/
structure CurrentPhaseSeventhFamily (p : DirectRealCubicRootPacket source r) where
  root : Fin 6 → C
  factor : ∀ i, phaseCarrier p (i.val + 1) = (zeta ^ (i.val + 1) - 1) * root i ^ 7
  root_away : ∀ i, ¬ ramifiedUniformizer ∣ root i

/-- 既存の共通因子パケットから六因子すべての同時表示を実際に供給する。
特定位相の receiver や三つの表示を追加仮定として受け取らない。 -/
theorem exists_current_phase_seventh_family (h : DirectOrbitCanonicalCommonFactorPacket p) :
    Nonempty (CurrentPhaseSeventhFamily p) := by
  have hall : ∀ i : Fin 6, ∃ theta : C,
      phaseCarrier p (i.val + 1) = (zeta ^ (i.val + 1) - 1) * theta ^ 7 ∧
        ¬ ramifiedUniformizer ∣ theta := by
    intro i
    apply exists_phase_unit_free_root h
    simp only [Finset.mem_erase, Finset.mem_range]
    exact ⟨by omega, by omega⟩
  choose theta htheta using hall
  exact ⟨⟨theta, fun i => (htheta i).1, fun i => (htheta i).2⟩⟩

/-- 族の各根は零でない。非分岐性を保持していることの直接の帰結。 -/
theorem CurrentPhaseSeventhFamily.root_ne_zero (F : CurrentPhaseSeventhFamily p) (i : Fin 6) :
    F.root i ≠ 0 := by
  intro hz
  exact F.root_away i (hz ▸ dvd_zero ramifiedUniformizer)

/-- 各根の主イデアルの七乗は、元の同じ位相の剥離イデアルに等しい。 -/
theorem CurrentPhaseSeventhFamily.root_ideal_power (F : CurrentPhaseSeventhFamily p) (i : Fin 6) :
    Ideal.span ({phaseCarrierQuotient p (i.val + 1)} : Set C) =
      Ideal.span ({F.root i} : Set C) ^ 7 := by
  have hi : i.val + 1 ∈ (Finset.range 7).erase 0 := by
    simp only [Finset.mem_erase, Finset.mem_range]
    exact ⟨by omega, by omega⟩
  have he : phaseCarrierQuotient p (i.val + 1) = (GNRamifierTwist hi : C) * F.root i ^ 7 := by
    apply mul_left_cancel₀ ramifiedUniformizer_ne_zero
    rw [← phaseCarrier_eq_uniformizer_mul_quotient, F.factor, ← GNRamifierTwist_spec hi]
    ring
  rw [he, Ideal.span_singleton_mul_left_unit (GNRamifierTwist hi).isUnit,
    Ideal.span_singleton_pow]

/-- 同時に選んだ根の主イデアルは対ごとに互いに素。全位相の既存の原始性を輸送する。 -/
theorem CurrentPhaseSeventhFamily.root_ideals_pairwise (F : CurrentPhaseSeventhFamily p) :
    Pairwise fun i j : Fin 6 =>
      IsCoprime (Ideal.span ({F.root i} : Set C)) (Ideal.span ({F.root j} : Set C)) := by
  intro i j hij
  have hc := normalizedPhaseIdeals_pairwise p (Finset.mem_range.mpr i.isLt)
    (Finset.mem_range.mpr j.isLt) (fun he => hij (Fin.ext he))
  change IsCoprime (Ideal.span ({phaseCarrierQuotient p (i.val + 1)} : Set C))
    (Ideal.span ({phaseCarrierQuotient p (j.val + 1)} : Set C)) at hc
  rw [F.root_ideal_power i, F.root_ideal_power j] at hc
  exact (IsCoprime.pow_iff (by decide : 0 < 7) (by decide : 0 < 7)).mp hc

/-- 族内の一つの根を、同じ位相の別の正確な七乗根で取り替える。
source と他の位相の根を動かさず、既存 receiver の根を族へ保存するために使う。 -/
def CurrentPhaseSeventhFamily.replaceRoot (F : CurrentPhaseSeventhFamily p) (i : Fin 6)
    (theta : C) (hf : phaseCarrier p (i.val + 1) = (zeta ^ (i.val + 1) - 1) * theta ^ 7)
    (ha : ¬ ramifiedUniformizer ∣ theta) : CurrentPhaseSeventhFamily p where
  root := Function.update F.root i theta
  factor := by
    intro j
    by_cases hj : j = i
    · subst j; simpa using hf
    · simpa only [Function.update_of_ne hj] using F.factor j
  root_away := by
    intro j
    by_cases hj : j = i
    · subst j; simpa using ha
    · simpa only [Function.update_of_ne hj] using F.root_away j

/-- 取り替えた同じ証人の、指定位置の根の等式。 -/
theorem CurrentPhaseSeventhFamily.replaceRoot_at (F : CurrentPhaseSeventhFamily p) (i : Fin 6)
    (theta : C) (hf) (ha) : (F.replaceRoot i theta hf ha).root i = theta :=
  Function.update_self _ _ _

/-- 現在の位相を、六因子族の添字へ戻す。 -/
def currentPhaseSlot (i : Fin 3) : Fin 6 :=
  ⟨phaseInverseExponent i - 1, by
    have hm := Finset.mem_erase.mp (current_phase_index_mem i)
    have hlt := Finset.mem_range.mp hm.2
    omega⟩

/-- current の位相添字と族の実際の位相が一致する。 -/
theorem currentPhaseSlot_spec (i : Fin 3) : (currentPhaseSlot i).val + 1 = phaseInverseExponent i := by
  have hm := (Finset.mem_erase.mp (current_phase_index_mem i)).1
  simp only [currentPhaseSlot]
  omega

variable {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}

/-- 既に選択した current 根を、同じ値のまま六因子族へ拡張する。
新しい族と古い根の間を、七乗の等式だけでなく元の等式で結ぶ。 -/
theorem current_phase_family_extending_root (c : CurrentCommonPrimeCyclotomicPacket h q)
    (theta : C)
    (hf : currentLinearCarrier c = (zeta ^ phaseInverseExponent c.phase - 1) * theta ^ 7)
    (ha : ¬ ramifiedUniformizer ∣ theta) :
    ∃ F : CurrentPhaseSeventhFamily p, F.root (currentPhaseSlot c.phase) = theta := by
  obtain ⟨F⟩ := exists_current_phase_seventh_family h
  have hf' : phaseCarrier p ((currentPhaseSlot c.phase).val + 1) =
      (zeta ^ ((currentPhaseSlot c.phase).val + 1) - 1) * theta ^ 7 := by
    rw [currentPhaseSlot_spec]
    exact hf
  exact ⟨F.replaceRoot (currentPhaseSlot c.phase) theta hf' ha, F.replaceRoot_at _ _ _ _⟩

/-- 実際の current receiver の同じ Q,kappa,gamma を保存した六因子族。
元の Fermat 方程式と根の主イデアルを保持するが、次の反例の存在は結論しない。 -/
theorem current_phase_family_receiver (c : CurrentCommonPrimeCyclotomicPacket h q) :
    ∃ (Q : PrimaryPacket) (kappa : Cˣ) (F : CurrentPhaseSeventhFamily p),
      Q.gap = SevenRealCubicInt.rotateEquiv p.rho - p.rho ∧ Q.parameter = p.rho ∧
      Q.phase = phaseInverseExponent c.phase ∧ Q.source = currentLinearCarrier c ∧
      Q.delta = kappa ^ 7 ∧ F.root (currentPhaseSlot c.phase) = (kappa : C) * Q.gamma ∧
      Ideal.span ({F.root (currentPhaseSlot c.phase)} : Set C) = Ideal.span ({Q.gamma} : Set C) ∧
      Fermat7Equation a b d := by
  obtain ⟨Q, kappa, theta, hgap, hp, hj, hs, hd, ht, hf, hi, ha, hF⟩ :=
    currentCarrier_unit_free_factor_receiver c
  obtain ⟨F, hroot⟩ := current_phase_family_extending_root c theta hf ha
  exact ⟨Q, kappa, F, hgap, hp, hj, hs, hd, hroot.trans ht, hroot ▸ hi, hF⟩

end
end DkMath.FLT.Kummer.SevenRealGN
