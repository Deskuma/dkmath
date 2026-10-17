/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.SevenCurrentRootDepth

#print "file: DkMathTest.FLT.Kummer.SevenCurrentRootDepth"

/-! 六根の深い七乗合同、共通剰余、補正項の保存、根の枝の境界を検査する。 -/

open DkMath.FLT.Seven DkMath.FLT.Kummer.SevenPrimaryNorm
open DkMath.FLT.Kummer.SevenRealGN DkMath.FLT.Seven.SevenRealCubic
open DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierRamification
open SevenCyclotomicDegreeSixInt

variable {a b d : ℕ} {source : CounterexamplePack a b d}
variable {r : PrimitiveCounterexampleRamifiedProvenance source}
variable {p : DirectRealCubicRootPacket source r}
variable {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}

-- 深さ6へ落とすと、整数7を法とする七乗合同にも接続できる。
example (F : CurrentPhaseSeventhFamily p) (i : Fin 6) :
    ramifiedUniformizer ^ 63 ∣ F.root i ^ 7 + ofReal p.rho ∧
      (7 : C) ∣ F.root i ^ 7 + ofReal p.rho :=
  ⟨phase_root_seventh_deep F i,
    seven_dvd_uniformizer_six.trans (phase_root_seventh_deep_of_le F i (by decide : 6 ≤ 63))⟩

-- 最初と最後の位相の七乗差と、根自身の一段合同を同じ族で保持する。
example (F : CurrentPhaseSeventhFamily p) :
    ramifiedUniformizer ^ 63 ∣ F.root 0 ^ 7 - F.root 5 ^ 7 ∧
      ramifiedUniformizer ∣ F.root 0 - F.root 5 :=
  ⟨phase_roots_seventh_sub_deep F 0 5, phase_roots_sub_uniformizer_dvd F 0 5⟩

-- 同じ非零剰余、根の互いに素性、補正項の主イデアルの等しさは両立する。
example (F : CurrentPhaseSeventhFamily p) :
    ramifiedEval (F.root 0) = ramifiedEval (F.root 5) ∧ ramifiedEval (F.root 0) ≠ 0 ∧
      IsCoprime (Ideal.span ({F.root 0} : Set C)) (Ideal.span ({F.root 5} : Set C)) ∧
      Ideal.span ({F.root 0 ^ 7 + ofReal p.rho} : Set C) =
        Ideal.span ({F.root 5 ^ 7 + ofReal p.rho} : Set C) :=
  ⟨phase_roots_same_residue F 0 5, phase_root_residue_ne_zero F 0,
    F.root_ideals_pairwise (by decide), phase_root_correction_ideals_eq F 0 5⟩

-- 補正項の整数ノルムの絶対値が等しいことを、同じ共通商の式から得る。
example (F : CurrentPhaseSeventhFamily p) (i j : Fin 6) :
    Int.natAbs (cyclotomicNormHom (F.root i ^ 7 + ofReal p.rho)) =
      Int.natAbs (cyclotomicNormHom (F.root j ^ 7 + ofReal p.rho)) := by
  obtain ⟨w, _, _, hn⟩ := exists_common_phase_root_correction_norm F
  exact (hn i).trans (hn j).symm

-- 七乗を変えずに根を zeta 倍した別の族でも、全位相の合同は成立する。
-- しかし、取り替えた根との差には lambda² 可除性さえない。
example (F : CurrentPhaseSeventhFamily p) :
    ∃ G : CurrentPhaseSeventhFamily p,
      G.root 0 ^ 7 = F.root 0 ^ 7 ∧
      ¬ ramifiedUniformizer ^ 2 ∣ G.root 0 - F.root 0 ∧
      (∀ i, ramifiedEval (G.root i) = ramifiedEval (F.root i)) ∧
      (∀ i, ramifiedUniformizer ^ 63 ∣ G.root i ^ 7 + ofReal p.rho) := by
  have hf : phaseCarrier p ((0 : Fin 6).val + 1) =
      (zeta ^ ((0 : Fin 6).val + 1) - 1) * (zeta * F.root 0) ^ 7 := by
    rw [phase_root_zeta_seventh_eq F 0]
    exact F.factor 0
  have ha : ¬ ramifiedUniformizer ∣ zeta * F.root 0 := by
    intro hd
    have hm := dvd_mul_of_dvd_right hd zetaInv
    apply F.root_away 0
    simpa only [← mul_assoc, zetaInv_mul_zeta, one_mul] using hm
  let G := F.replaceRoot 0 (zeta * F.root 0) hf ha
  have he : G.root 0 = zeta * F.root 0 := F.replaceRoot_at _ _ _ _
  refine ⟨G, ?_, ?_, ?_, phase_root_seventh_deep G⟩
  · rw [he, phase_root_zeta_seventh_eq]
  · rw [he]
    exact phase_root_zeta_difference_not_dvd_sq F 0
  · intro i
    exact (phase_root_residue G i).trans (phase_root_residue F i).symm

-- 共通中心の相殺は任意の深さで成立する。これは current packet の局所例ではない。
example (n : ℕ) :
    (∀ _i : Fin 6, ramifiedUniformizer ^ n ∣ (1 : C) ^ 7 + (-1)) ∧
      ((1 : C) ^ 7 + ofReal SevenRealCubicInt.alpha * 1 ^ 7 =
        ofReal (1 + SevenRealCubicInt.alpha) * 1 ^ 7) ∧
      ¬ ramifiedUniformizer ∣ (1 : C) := by
  refine ⟨fun _ => by simp, ?_, ?_⟩
  · simp only [one_pow, mul_one, map_add, map_one]
  · intro hd
    have hz := (ramifiedEval_eq_zero_iff_dvd (1 : C)).mpr hd
    have h10 : (1 : ZMod 7) = 0 := by simpa only [map_one] using hz
    exact (by decide : (1 : ZMod 7) ≠ 0) h10

-- 与えられた共通中心合同だけから、重み付き式が消えることを使う。
example (u x y z : C) (hx : ramifiedUniformizer ^ 63 ∣ x + u)
    (hy : ramifiedUniformizer ^ 63 ∣ y + u) (hz : ramifiedUniformizer ^ 63 ∣ z + u) :
    ramifiedUniformizer ^ 63 ∣ x + ofReal SevenRealCubicInt.alpha * z -
      ofReal (1 + SevenRealCubicInt.alpha) * y :=
  weighted_common_center_congruence 63 u x y z hx hy hz

-- current packet では補正項も共通商 w も非零。同じ w のノルム式を保持する。
example (F : CurrentPhaseSeventhFamily p) (c : CurrentCommonPrimeCyclotomicPacket h q) :
    ∃ w : C, w ≠ 0 ∧
      ofReal (SevenRealCubicInt.rotateEquiv p.rho - p.rho) = ramifiedUniformizer ^ 64 * w ∧
      (∀ i : Fin 6, F.root i ^ 7 + ofReal p.rho =
        ramifiedUniformizer ^ 63 * ((↑((phaseRootTwist i)⁻¹) : C) * w)) ∧
      ∀ i : Fin 6, Int.natAbs (cyclotomicNormHom (F.root i ^ 7 + ofReal p.rho)) =
        7 ^ 63 * Int.natAbs (cyclotomicNormHom w) := by
  obtain ⟨w, hg, hw, hn⟩ := exists_common_phase_root_correction_norm F
  refine ⟨w, ?_, hg, hw, hn⟩
  intro hz
  apply phase_root_correction_ne_zero F c 0
  rw [hw 0, hz, mul_zero, mul_zero]

-- 実 receiver の同じ Q,kappa,F に、今回の深い合同を供給する。
example (c : CurrentCommonPrimeCyclotomicPacket h q) :
    ∃ (Q : PrimaryPacket) (kappa : Cˣ) (F : CurrentPhaseSeventhFamily p),
      Q.source = currentLinearCarrier c ∧ Q.delta = kappa ^ 7 ∧
      F.root (currentPhaseSlot c.phase) = (kappa : C) * Q.gamma ∧
      ramifiedUniformizer ^ 63 ∣ ((kappa : C) * Q.gamma) ^ 7 + ofReal p.rho ∧
      (∀ i, ramifiedEval (F.root i) = -SevenRealCubicInt.thetaResidue p.rho) ∧
      Fermat7Equation a b d := by
  obtain ⟨Q, kappa, F, _, _, _, hs, hd, hroot, _, hF⟩ := current_phase_family_receiver c
  have hdeep := phase_root_seventh_deep F (currentPhaseSlot c.phase)
  rw [hroot] at hdeep
  exact ⟨Q, kappa, F, hs, hd, hroot, hdeep, phase_root_residue F, hF⟩
