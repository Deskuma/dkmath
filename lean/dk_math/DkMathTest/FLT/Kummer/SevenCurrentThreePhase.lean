/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.SevenCurrentThreePhase

#print "file: DkMathTest.FLT.Kummer.SevenCurrentThreePhase"

/-! 三因子の加法関係、全六因子の同時供給、選択根の保存、残留単元障害の回帰例。 -/

open DkMath.Lib.Cosmic DkMath.FLT.Seven DkMath.FLT.Kummer.SevenPrimaryNorm
open DkMath.FLT.Kummer.SevenRealGN DkMath.FLT.Seven.SevenRealCubic
open DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierRamification
open SevenCyclotomicDegreeSixInt

-- 三因子の冪表示を実際の整数で供給する局所例。FLT 反例ではない。
example : (2 : ℤ) * 3 ^ 7 + 7 * 3 ^ 7 = 9 * 3 ^ 7 := by
  have h := phaseSource_three_consecutive_power_relation (2 : ℤ) 0 (-(3 ^ 7)) 3 3 3 7
    (by decide) (by decide) (by unfold phaseSource; ring)
    (by unfold phaseSource; ring) (by unfold phaseSource; ring)
  simpa only [show 1 + (2 : ℤ) + 2 ^ 2 = 7 by norm_num,
    show (1 + (2 : ℤ)) ^ 2 = 9 by norm_num] using h

-- 重み付き式には全根1の局所例もある。単元係数の七乗性はそこからは従わない。
example : (1 : C) ^ 7 + ofReal SevenRealCubicInt.alpha * 1 ^ 7 =
    ofReal (1 + SevenRealCubicInt.alpha) * 1 ^ 7 := by
  simp only [one_pow, mul_one, map_add, map_one]

-- 六因子族の添字は選択位相 1,4,5 と正確に対応する。
example : (currentPhaseSlot 0).val = 0 ∧ (currentPhaseSlot 1).val = 3 ∧
    (currentPhaseSlot 2).val = 4 := by decide

variable {a b d : ℕ} {source : CounterexamplePack a b d}
variable {r : PrimitiveCounterexampleRamifiedProvenance source}
variable {p : DirectRealCubicRootPacket source r}
variable {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}

-- 単一の関数 root が六つすべての表示と原始性を同時に満たす。
example (h : DirectOrbitCanonicalCommonFactorPacket p) :
    ∃ F : CurrentPhaseSeventhFamily p,
      (∀ i, phaseCarrier p (i.val + 1) = (zeta ^ (i.val + 1) - 1) * F.root i ^ 7) ∧
      (∀ i, F.root i ≠ 0) ∧
      (Pairwise fun i j : Fin 6 =>
        IsCoprime (Ideal.span ({F.root i} : Set C)) (Ideal.span ({F.root j} : Set C))) := by
  obtain ⟨F⟩ := exists_current_phase_seventh_family h
  exact ⟨F, F.factor, F.root_ne_zero, F.root_ideals_pairwise⟩

-- 非自明な根の取り替えでも同じ族として使える。他の五つの根は保つ。
example (F : CurrentPhaseSeventhFamily p) :
    ∃ G : CurrentPhaseSeventhFamily p,
      G.root 0 = zeta * F.root 0 ∧ G.root 0 ≠ F.root 0 ∧
      (∀ i : Fin 6, i ≠ 0 → G.root i = F.root i) ∧
      G.root 0 ^ 7 + ofReal SevenRealCubicInt.alpha * G.root 2 ^ 7 =
        ofReal (1 + SevenRealCubicInt.alpha) * G.root 1 ^ 7 := by
  have hf : phaseCarrier p ((0 : Fin 6).val + 1) =
      (zeta ^ ((0 : Fin 6).val + 1) - 1) * (zeta * F.root 0) ^ 7 := by
    rw [mul_pow, zeta_pow_seven, one_mul]
    exact F.factor 0
  have ha : ¬ ramifiedUniformizer ∣ zeta * F.root 0 := by
    intro hd
    have hm := dvd_mul_of_dvd_right hd zetaInv
    apply F.root_away 0
    simpa only [← mul_assoc, zetaInv_mul_zeta, one_mul] using hm
  let G := F.replaceRoot 0 (zeta * F.root 0) hf ha
  have hG : G.root 0 = zeta * F.root 0 := F.replaceRoot_at _ _ _ _
  refine ⟨G, hG, ?_, ?_, G.real_weighted_seventh_equation⟩
  · rw [hG]
    intro he
    apply zeta_ne_one
    apply mul_right_cancel₀ (F.root_ne_zero 0)
    simpa only [one_mul] using he
  · intro i hi
    exact Function.update_of_ne hi _ _

-- 与えられた選択根の同じ値を保存し、その同じ族について加法式と原始性を得る。
example (c : CurrentCommonPrimeCyclotomicPacket h q) (theta : C)
    (hf : currentLinearCarrier c = (zeta ^ phaseInverseExponent c.phase - 1) * theta ^ 7)
    (ha : ¬ ramifiedUniformizer ∣ theta) :
    ∃ F : CurrentPhaseSeventhFamily p,
      F.root (currentPhaseSlot c.phase) = theta ∧
      F.root 0 ^ 7 + ofReal SevenRealCubicInt.alpha * F.root 2 ^ 7 =
        ofReal (1 + SevenRealCubicInt.alpha) * F.root 1 ^ 7 ∧
      (Pairwise fun i j : Fin 6 =>
        IsCoprime (Ideal.span ({F.root i} : Set C)) (Ideal.span ({F.root j} : Set C))) := by
  obtain ⟨F, he⟩ := current_phase_family_extending_root c theta hf ha
  exact ⟨F, he, F.real_weighted_seventh_equation, F.root_ideals_pairwise⟩

-- 実 receiver の Q,kappa と元の Fermat 方程式を保持する。同じ族の全根は非実。
example (c : CurrentCommonPrimeCyclotomicPacket h q) :
    ∃ (F : CurrentPhaseSeventhFamily p) (Q : PrimaryPacket) (kappa : Cˣ),
      Q.source = currentLinearCarrier c ∧ Q.delta = kappa ^ 7 ∧
      F.root (currentPhaseSlot c.phase) = (kappa : C) * Q.gamma ∧
      (F.root 0 ^ 7 + ofReal SevenRealCubicInt.alpha * F.root 2 ^ 7 =
        ofReal (1 + SevenRealCubicInt.alpha) * F.root 1 ^ 7) ∧
      (∀ i, ¬ ∃ v : R, F.root i = ofReal v) ∧ Fermat7Equation a b d := by
  obtain ⟨F, ⟨Q, kappa, _, _, _, hs, hd, hroot, _⟩, heq, _, _, hF⟩ :=
    current_three_phase_data_receiver c
  exact ⟨F, Q, kappa, hs, hd, hroot, heq, fun i => F.root_not_real c i, hF⟩

-- 係数 alpha は、六次環の単元としても七乗に吸収できない。
example : ¬ ∃ kappa : Cˣ, (kappa : C) ^ 7 = ofReal SevenRealCubicInt.alpha := by
  rintro ⟨kappa, hk⟩
  apply alphaEmbeddedUnit_not_seventh
  refine ⟨kappa, Units.ext ?_⟩
  exact hk.symm

-- 共通単元も許した係数消去の排除は、仮想的な current packet なしで成立する。
example (s u v w : Cˣ) (hu : s = u ^ 7) (hv : s * alphaEmbeddedUnit = v ^ 7)
    (hw : s * Units.map ofReal.toMonoidHom SevenRealCubicInt.alphaAddOneUnit = w ^ 7) : False :=
  no_common_unit_clears_three_phase_coefficients ⟨s, u, v, w, hu, hv, hw⟩
