/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.SevenCurrentThreePhase
import DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicAdditiveChartBoundary

/-! # 六因子の七乗差と共通の深い補正項

同じ gap の lambda^64 可除性から、各根の七乗の lambda^63 合同を得る。
六つの補正項を同じ剥離商 w で表示し、分岐剰余の一致と大域的な互いに素性を保持する。
重み付き式の合同は共通中心だけから導き、既存の厳密な加法式を使わない。
これらは反例再構成や厳密降下を供給しない。63は可除性の下界である。
-/

open DkMath.FLT.Seven DkMath.FLT.Kummer.SevenPrimaryNorm
open DkMath.FLT.Seven.SevenRealCubic
open DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierRamification

namespace DkMath.FLT.Kummer.SevenRealGN

noncomputable section
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
open SevenCyclotomicDegreeSixInt

variable {a b d : ℕ} {source : CounterexamplePack a b d}
variable {r : PrimitiveCounterexampleRamifiedProvenance source}
variable {p : DirectRealCubicRootPacket source r}

/-- 六因子族の添字に対応する分岐補正単元 T_j。実際の位相は i.val+1 である。 -/
def phaseRootTwist (i : Fin 6) : Cˣ :=
  GNRamifierTwist (by
    simp only [Finset.mem_erase, Finset.mem_range]
    exact ⟨by omega, by omega⟩ : i.val + 1 ∈ (Finset.range 7).erase 0)

/-- 全六位相の分岐因子は、同じ lambda の単元倍である。 -/
theorem phaseRootTwist_spec (i : Fin 6) :
    (phaseRootTwist i : C) * ramifiedUniformizer = zeta ^ (i.val + 1) - 1 :=
  GNRamifierTwist_spec _

/-- 六つの七乗を、同じ gap と parameter に接続する正確な等式。
加法的な三項関係より前の、一因子ごとの保存情報を残す。 -/
theorem phase_root_gap_identity (F : CurrentPhaseSeventhFamily p) (i : Fin 6) :
    ofReal (SevenRealCubicInt.rotateEquiv p.rho - p.rho) =
      (zeta ^ (i.val + 1) - 1) * (F.root i ^ 7 + ofReal p.rho) := by
  have hf := F.factor i
  rw [phaseCarrier] at hf
  rw [map_sub]
  linear_combination hf

/-- 一つの剥離商 w を六因子すべてで共有する。
根ごとに無関係な商を選ばず、gap=lambda^64*w と各七乗の補正項の来歴を固定する。 -/
theorem exists_common_phase_root_correction (F : CurrentPhaseSeventhFamily p) :
    ∃ w : C,
      ofReal (SevenRealCubicInt.rotateEquiv p.rho - p.rho) = ramifiedUniformizer ^ 64 * w ∧
      ∀ i : Fin 6, F.root i ^ 7 + ofReal p.rho =
        ramifiedUniformizer ^ 63 * ((↑((phaseRootTwist i)⁻¹) : C) * w) := by
  obtain ⟨w, hw⟩ := current_gap_uniformizer_pow64 p
  refine ⟨w, hw, ?_⟩
  intro i
  have hg := phase_root_gap_identity F i
  rw [← phaseRootTwist_spec i] at hg
  have he : (phaseRootTwist i : C) * (F.root i ^ 7 + ofReal p.rho) =
      ramifiedUniformizer ^ 63 * w := by
    apply mul_left_cancel₀ ramifiedUniformizer_ne_zero
    calc
      _ = ofReal (SevenRealCubicInt.rotateEquiv p.rho - p.rho) := by rw [hg]; ring
      _ = ramifiedUniformizer * (ramifiedUniformizer ^ 63 * w) := by rw [hw]; ring
  have hc : (↑((phaseRootTwist i)⁻¹) : C) * (phaseRootTwist i : C) = 1 :=
    (phaseRootTwist i).inv_val
  calc
    F.root i ^ 7 + ofReal p.rho = (↑((phaseRootTwist i)⁻¹) : C) *
        ((phaseRootTwist i : C) * (F.root i ^ 7 + ofReal p.rho)) := by
      rw [← mul_assoc, hc, one_mul]
    _ = ramifiedUniformizer ^ 63 * ((↑((phaseRootTwist i)⁻¹) : C) * w) := by rw [he]; ring

/-- 各根の七乗は -ofReal(rho) と少なくとも lambda^63 を法として合同する。
正確な付値63や、根そのものの63段合同は結論しない。 -/
theorem phase_root_seventh_deep (F : CurrentPhaseSeventhFamily p) (i : Fin 6) :
    ramifiedUniformizer ^ 63 ∣ F.root i ^ 7 + ofReal p.rho := by
  obtain ⟨w, _, hw⟩ := exists_common_phase_root_correction F
  exact ⟨(↑((phaseRootTwist i)⁻¹) : C) * w, hw i⟩

/-- 同じ七乗合同を、任意の n≤63 の深さへ落とす。 -/
theorem phase_root_seventh_deep_of_le (F : CurrentPhaseSeventhFamily p) (i : Fin 6)
    {n : ℕ} (hn : n ≤ 63) :
    ramifiedUniformizer ^ n ∣ F.root i ^ 7 + ofReal p.rho :=
  (pow_dvd_pow ramifiedUniformizer hn).trans (phase_root_seventh_deep F i)

/-- 任意の二位相の七乗差も lambda^63 で割れる。二つの根は同じ族 F に属する。 -/
theorem phase_roots_seventh_sub_deep (F : CurrentPhaseSeventhFamily p) (i j : Fin 6) :
    ramifiedUniformizer ^ 63 ∣ F.root i ^ 7 - F.root j ^ 7 := by
  convert dvd_sub (phase_root_seventh_deep F i) (phase_root_seventh_deep F j) using 1
  ring

/-- 七乗差の可除性を、任意の n≤63 の深さへ落とす。 -/
theorem phase_roots_seventh_sub_deep_of_le (F : CurrentPhaseSeventhFamily p) (i j : Fin 6)
    {n : ℕ} (hn : n ≤ 63) : ramifiedUniformizer ^ n ∣ F.root i ^ 7 - F.root j ^ 7 :=
  (pow_dvd_pow ramifiedUniformizer hn).trans (phase_roots_seventh_sub_deep F i j)

/-- 分岐剰余体 F_7 の Frobenius から、根そのものの共通剰余を回復する。 -/
theorem phase_root_residue (F : CurrentPhaseSeventhFamily p) (i : Fin 6) :
    ramifiedEval (F.root i) = -SevenRealCubicInt.thetaResidue p.rho := by
  have hd : ramifiedUniformizer ∣ F.root i ^ 7 + ofReal p.rho :=
    (dvd_pow_self _ (by decide : 63 ≠ 0)).trans (phase_root_seventh_deep F i)
  have hz := (ramifiedEval_eq_zero_iff_dvd _).mpr hd
  simp only [map_add, map_pow, ramifiedEval_ofReal, ZMod.pow_card] at hz
  linear_combination hz

/-- 六根は分岐素点で同じ剰余を持つ。七乗根の選択を変えても成立する。 -/
theorem phase_roots_same_residue (F : CurrentPhaseSeventhFamily p) (i j : Fin 6) :
    ramifiedEval (F.root i) = ramifiedEval (F.root j) :=
  (phase_root_residue F i).trans (phase_root_residue F j).symm

/-- 共通剰余は非零であり、六根が分岐素イデアルに属するという意味ではない。 -/
theorem phase_root_residue_ne_zero (F : CurrentPhaseSeventhFamily p) (i : Fin 6) :
    ramifiedEval (F.root i) ≠ 0 := by
  rw [phase_root_residue F i]
  exact neg_ne_zero.mpr p.thetaResidue_ne_zero

/-- 根そのものの差についても、一段の分岐可除性は得られる。 -/
theorem phase_roots_sub_uniformizer_dvd (F : CurrentPhaseSeventhFamily p) (i j : Fin 6) :
    ramifiedUniformizer ∣ F.root i - F.root j := by
  apply (ramifiedEval_eq_zero_iff_dvd _).mp
  rw [map_sub, phase_roots_same_residue F i j, sub_self]

/-- 同じ F の深い七乗合同、共通の非零剰余、大域的な互いに素性を同時に保持する。
主イデアルの相異性は非単元性の追加証明なしには結論しない。 -/
theorem phase_roots_local_global_data (F : CurrentPhaseSeventhFamily p) :
    (∀ i, ramifiedUniformizer ^ 63 ∣ F.root i ^ 7 + ofReal p.rho) ∧
      (∀ i, ramifiedEval (F.root i) = -SevenRealCubicInt.thetaResidue p.rho ∧
        ramifiedEval (F.root i) ≠ 0) ∧
      (Pairwise fun i j : Fin 6 =>
        IsCoprime (Ideal.span ({F.root i} : Set C)) (Ideal.span ({F.root j} : Set C))) :=
  ⟨phase_root_seventh_deep F, fun i => ⟨phase_root_residue F i, phase_root_residue_ne_zero F i⟩,
    F.root_ideals_pairwise⟩

/-- 七乗に parameter を加えた補正項の主イデアルは、六位相すべてで等しい。
互いに素なのは根自身の主イデアルであり、この補正項のイデアルとは区別する。 -/
theorem phase_root_correction_ideals_eq (F : CurrentPhaseSeventhFamily p) (i j : Fin 6) :
    Ideal.span ({F.root i ^ 7 + ofReal p.rho} : Set C) =
      Ideal.span ({F.root j ^ 7 + ofReal p.rho} : Set C) := by
  obtain ⟨w, _, hw⟩ := exists_common_phase_root_correction F
  have hi : F.root i ^ 7 + ofReal p.rho =
      (↑((phaseRootTwist i)⁻¹) : C) * (ramifiedUniformizer ^ 63 * w) := by rw [hw i]; ring
  have hj : F.root j ^ 7 + ofReal p.rho =
      (↑((phaseRootTwist j)⁻¹) : C) * (ramifiedUniformizer ^ 63 * w) := by rw [hw j]; ring
  rw [hi, hj, Ideal.span_singleton_mul_left_unit ((phaseRootTwist i)⁻¹).isUnit,
    Ideal.span_singleton_mul_left_unit ((phaseRootTwist j)⁻¹).isUnit]

/-- 同じ剥離商 w のもとで、各補正項の整数ノルムの絶対値も共通となる。
これは補正項の乗法的ノルム式であり、根のノルムや新しい反例の測度の減少ではない。 -/
theorem exists_common_phase_root_correction_norm (F : CurrentPhaseSeventhFamily p) :
    ∃ w : C,
      ofReal (SevenRealCubicInt.rotateEquiv p.rho - p.rho) = ramifiedUniformizer ^ 64 * w ∧
      (∀ i : Fin 6, F.root i ^ 7 + ofReal p.rho =
        ramifiedUniformizer ^ 63 * ((↑((phaseRootTwist i)⁻¹) : C) * w)) ∧
      ∀ i : Fin 6, Int.natAbs (cyclotomicNormHom (F.root i ^ 7 + ofReal p.rho)) =
        7 ^ 63 * Int.natAbs (cyclotomicNormHom w) := by
  obtain ⟨w, hg, hw⟩ := exists_common_phase_root_correction F
  refine ⟨w, hg, hw, ?_⟩
  intro i
  have hu : Int.natAbs (cyclotomicNormHom (↑((phaseRootTwist i)⁻¹) : C)) = 1 :=
    Int.natAbs_of_isUnit (((phaseRootTwist i)⁻¹).isUnit.map cyclotomicNormHom)
  rw [hw i]
  simp only [map_mul, map_pow, cyclotomicNormHom_ramifiedUniformizer,
    Int.natAbs_mul, Int.natAbs_pow, hu, show Int.natAbs (7 : ℤ) = 7 from rfl, one_mul]

/-- 三値が同じ中心 -u に合同なら、係数1,alpha,1+alphaの重み付き式は同じ法で消える。
具体的な六因子族や、その厳密な加法式を仮定しない。 -/
theorem weighted_common_center_congruence (n : ℕ) (u x y z : C)
    (hx : ramifiedUniformizer ^ n ∣ x + u)
    (hy : ramifiedUniformizer ^ n ∣ y + u)
    (hz : ramifiedUniformizer ^ n ∣ z + u) :
    ramifiedUniformizer ^ n ∣ x + ofReal SevenRealCubicInt.alpha * z -
      ofReal (1 + SevenRealCubicInt.alpha) * y := by
  have hd := dvd_sub (dvd_add hx (dvd_mul_of_dvd_right hz (ofReal SevenRealCubicInt.alpha)))
    (dvd_mul_of_dvd_right hy (ofReal (1 + SevenRealCubicInt.alpha)))
  convert hd using 1
  simp only [map_add, map_one]
  ring

/-- 共通中心をそのまま代入した時の相殺。合同式の整合性を表す有限恒等式である。 -/
theorem weighted_common_center_exact (u : C) :
    -u + ofReal SevenRealCubicInt.alpha * (-u) -
      ofReal (1 + SevenRealCubicInt.alpha) * (-u) = 0 := by
  simp only [map_add, map_one]
  ring

/-- n≤63 の範囲では、重み付き式の合同は各根の共通中心合同だけから従う。
既存の real_weighted_seventh_equation を呼んで dvd_zero にしていない。 -/
theorem phase_roots_weighted_congruence_of_le (F : CurrentPhaseSeventhFamily p)
    {n : ℕ} (hn : n ≤ 63) :
    ramifiedUniformizer ^ n ∣ F.root 0 ^ 7 + ofReal SevenRealCubicInt.alpha * F.root 2 ^ 7 -
      ofReal (1 + SevenRealCubicInt.alpha) * F.root 1 ^ 7 :=
  weighted_common_center_congruence n (ofReal p.rho) _ _ _
    (phase_root_seventh_deep_of_le F 0 hn) (phase_root_seventh_deep_of_le F 1 hn)
    (phase_root_seventh_deep_of_le F 2 hn)

/-- lambda^63 での重み付き式の相殺は、局所的な共通中心データで既に説明できる。 -/
theorem phase_roots_weighted_congruence (F : CurrentPhaseSeventhFamily p) :
    ramifiedUniformizer ^ 63 ∣ F.root 0 ^ 7 + ofReal SevenRealCubicInt.alpha * F.root 2 ^ 7 -
      ofReal (1 + SevenRealCubicInt.alpha) * F.root 1 ^ 7 :=
  phase_roots_weighted_congruence_of_le F le_rfl

/-- zeta 倍は七乗を変えない。深い七乗合同から根の枝まで固定することはできない。 -/
theorem phase_root_zeta_seventh_eq (F : CurrentPhaseSeventhFamily p) (i : Fin 6) :
    (zeta * F.root i) ^ 7 = F.root i ^ 7 := by
  rw [mul_pow, zeta_pow_seven, one_mul]

/-- 同じ七乗を持つ zeta 倍でも、根の差は lambda² で割れない。
非分岐な根について、七乗の63段合同と根自身の高次合同を区別する境界である。 -/
theorem phase_root_zeta_difference_not_dvd_sq (F : CurrentPhaseSeventhFamily p) (i : Fin 6) :
    ¬ ramifiedUniformizer ^ 2 ∣ zeta * F.root i - F.root i := by
  intro hd
  have he : zeta * F.root i - F.root i = ramifiedUniformizer * (-F.root i) := by
    simp only [ramifiedUniformizer]
    ring
  rw [he, pow_two] at hd
  have hn : ramifiedUniformizer ∣ -F.root i := (mul_dvd_mul_iff_left ramifiedUniformizer_ne_zero).mp hd
  exact F.root_away i (dvd_neg.mp hn)

variable {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}

/-- current common-prime packet のもとでは補正項は非零。
深度の下界を正確な付値に置き換えるには、さらに剥離商の非分岐性が必要である。 -/
theorem phase_root_correction_ne_zero (F : CurrentPhaseSeventhFamily p)
    (c : CurrentCommonPrimeCyclotomicPacket h q) (i : Fin 6) :
    F.root i ^ 7 + ofReal p.rho ≠ 0 := by
  intro hz
  have hg : ofReal (SevenRealCubicInt.rotateEquiv p.rho - p.rho) = 0 := by
    rw [phase_root_gap_identity F i, hz, mul_zero]
  have he : SevenRealCubicInt.rotateEquiv p.rho - p.rho = 0 :=
    ofReal_injective (by simpa only [map_zero] using hg)
  exact current_rotation_ne_self c (sub_eq_zero.mp he)

end
end DkMath.FLT.Kummer.SevenRealGN
