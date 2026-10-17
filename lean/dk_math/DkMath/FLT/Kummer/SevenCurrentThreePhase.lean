/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.SevenCurrentPhaseFamily
import DkMath.Lib.Cosmic.GNPhaseThreeTerm

#print "file: DkMath.FLT.Kummer.SevenCurrentThreePhase"

/-! # 同じ二端点の三因子から、重み付き七乗方程式へ

六因子を同時に七乗表示した族を使い、位相1,2,3の加法関係を得る。
共通分岐因子と位相単元を消すと、係数は 1,alpha,1+alpha となる。
alpha の単元七乗剰余類は非自明なので、この式を単元倍だけで通常の Fermat 式に
置き換えることはできない。次の反例への再入と厳密減少はまだ結論しない。
-/

namespace DkMath.FLT.Kummer.SevenRealGN

open DkMath.FLT.Seven DkMath.FLT.Kummer.SevenPrimaryNorm DkMath.Lib.Cosmic
open DkMath.FLT.Seven.SevenRealCubic
open DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierRamification
open SevenCyclotomicDegreeSixInt

noncomputable section

variable {a b d : ℕ} {source : CounterexamplePack a b d}
variable {r : PrimitiveCounterexampleRamifiedProvenance source}
variable {p : DirectRealCubicRootPacket source r}

/-- 族の各表示を、同じ gap と parameter の GN source の形で取り出す。 -/
theorem CurrentPhaseSeventhFamily.realGN_factor (F : CurrentPhaseSeventhFamily p) (i : Fin 6) :
    realGNSource (SevenRealCubicInt.rotateEquiv p.rho - p.rho) p.rho (i.val + 1) =
      (zeta ^ (i.val + 1) - 1) * F.root i ^ 7 :=
  (realGNSource_sub_coordinates _ _ _).trans (F.factor i)

/-- 同じ六因子族の任意の三因子が満たす加法関係。
三つの根を別々の source や別々の存在証明から取り違えない。 -/
theorem CurrentPhaseSeventhFamily.three_term_relation (F : CurrentPhaseSeventhFamily p)
    (i j k : Fin 6) :
    (zeta ^ (j.val + 1) - zeta ^ (k.val + 1)) * (zeta ^ (i.val + 1) - 1) * F.root i ^ 7 +
      (zeta ^ (k.val + 1) - zeta ^ (i.val + 1)) * (zeta ^ (j.val + 1) - 1) * F.root j ^ 7 +
      (zeta ^ (i.val + 1) - zeta ^ (j.val + 1)) * (zeta ^ (k.val + 1) - 1) * F.root k ^ 7 = 0 :=
  phaseSource_pow_three_term_relation _ _ _ _ _ _ _ _ 7
    (F.realGN_factor i) (F.realGN_factor j) (F.realGN_factor k)

/-- 位相1,2,3の三因子から、共通分岐二乗を除いた七乗方程式を取り出す。 -/
theorem CurrentPhaseSeventhFamily.consecutive_phase_relation (F : CurrentPhaseSeventhFamily p) :
    zeta * F.root 0 ^ 7 + (1 + zeta + zeta ^ 2) * F.root 2 ^ 7 =
      (1 + zeta) ^ 2 * F.root 1 ^ 7 := by
  have h1 := F.realGN_factor 0
  have h2 := F.realGN_factor 1
  have h3 := F.realGN_factor 2
  change phaseSource (zeta ^ 1) _ _ = (zeta ^ 1 - 1) * F.root 0 ^ 7 at h1
  simp only [pow_one] at h1
  exact phaseSource_three_consecutive_power_relation _ _ _ _ _ _ 7
    zetaUnit.isUnit.ne_zero zeta_ne_one h1 h2 h3

/-- 位相単元を消すと、係数は実三次単元 alpha,1+alpha に戻る。
根は六次環のままであり、整数の新しい FLT7 三つ組ではない。 -/
theorem CurrentPhaseSeventhFamily.real_weighted_seventh_equation (F : CurrentPhaseSeventhFamily p) :
    F.root 0 ^ 7 + ofReal SevenRealCubicInt.alpha * F.root 2 ^ 7 =
      ofReal (1 + SevenRealCubicInt.alpha) * F.root 1 ^ 7 := by
  have ha : zeta * ofReal SevenRealCubicInt.alpha = 1 + zeta + zeta ^ 2 := by
    rw [ofReal_alpha]
    linear_combination zeta_mul_zetaInv
  have hb : zeta * ofReal (1 + SevenRealCubicInt.alpha) = (1 + zeta) ^ 2 := by
    rw [map_add, map_one, mul_add, ha]
    ring
  apply mul_left_cancel₀ zetaUnit.isUnit.ne_zero
  calc
    zeta * (F.root 0 ^ 7 + ofReal SevenRealCubicInt.alpha * F.root 2 ^ 7) =
        zeta * F.root 0 ^ 7 + (1 + zeta + zeta ^ 2) * F.root 2 ^ 7 := by
      rw [mul_add, ← mul_assoc, ha]
    _ = (1 + zeta) ^ 2 * F.root 1 ^ 7 := F.consecutive_phase_relation
    _ = zeta * (ofReal (1 + SevenRealCubicInt.alpha) * F.root 1 ^ 7) := by
      rw [← mul_assoc, hb]

/-- 重み付き方程式の三係数はすべて単元。ただし単元であることと七乗であることは異なる。 -/
theorem three_phase_coefficients_are_units :
    IsUnit (1 : C) ∧ IsUnit (ofReal SevenRealCubicInt.alpha) ∧
      IsUnit (ofReal (1 + SevenRealCubicInt.alpha)) :=
  ⟨isUnit_one, SevenRealCubicInt.alpha_isUnit.map ofReal,
    SevenRealCubicInt.alphaAddOne_isUnit.map ofReal⟩

/-- 共通単元を掛けて三係数をすべて七乗へ吸収する方法は使えない。
係数1が共通単元自身の七乗性を強制し、次の係数から alpha の非七乗性に反する。
これはこの単元操作の排除であり、別の算術的 source 変換の不可能性ではない。 -/
theorem no_common_unit_clears_three_phase_coefficients :
    ¬ ∃ s u v w : Cˣ, s = u ^ 7 ∧ s * alphaEmbeddedUnit = v ^ 7 ∧
      s * Units.map ofReal.toMonoidHom SevenRealCubicInt.alphaAddOneUnit = w ^ 7 := by
  rintro ⟨s, u, v, w, hu, hv, _⟩
  apply alphaEmbeddedUnit_not_seventh
  refine ⟨u⁻¹ * v, ?_⟩
  calc
    alphaEmbeddedUnit = s⁻¹ * (s * alphaEmbeddedUnit) := by group
    _ = (u⁻¹ * v) ^ 7 := by rw [hv, hu, mul_pow, inv_pow]

/-- 同じ族・同じ根で、加法方程式、原始性、非分岐性を同時に保持する。
存在を束ねたことを、次の反例の再構成や測度の減少とは数えない。 -/
theorem exists_current_three_phase_data (h : DirectOrbitCanonicalCommonFactorPacket p) :
    ∃ F : CurrentPhaseSeventhFamily p,
      F.root 0 ^ 7 + ofReal SevenRealCubicInt.alpha * F.root 2 ^ 7 =
        ofReal (1 + SevenRealCubicInt.alpha) * F.root 1 ^ 7 ∧
      (∀ i, ¬ ramifiedUniformizer ∣ F.root i) ∧
      (Pairwise fun i j : Fin 6 =>
        IsCoprime (Ideal.span ({F.root i} : Set C)) (Ideal.span ({F.root j} : Set C))) := by
  obtain ⟨F⟩ := exists_current_phase_seventh_family h
  exact ⟨F, F.real_weighted_seventh_equation, F.root_away, F.root_ideals_pairwise⟩

variable {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}

/-- 現在の common-prime 状態では、六因子族のどの根もそのまま実部分へ戻せない。
係数が実三次環にあっても、根の係数環まで縮小できるとは限らない。 -/
theorem CurrentPhaseSeventhFamily.root_not_real (F : CurrentPhaseSeventhFamily p)
    (c : CurrentCommonPrimeCyclotomicPacket h q) (i : Fin 6) :
    ¬ ∃ v : R, F.root i = ofReal v := by
  rintro ⟨v, hv⟩
  have hi : i.val + 1 ∈ (Finset.range 7).erase 0 := by
    simp only [Finset.mem_erase, Finset.mem_range]
    exact ⟨by omega, by omega⟩
  have he : ofReal (SevenRealCubicInt.rotateEquiv p.rho) -
      zeta ^ (i.val + 1) * ofReal p.rho =
      ofReal (-(v ^ 7)) - zeta ^ (i.val + 1) * ofReal (-(v ^ 7)) := by
    change phaseCarrier p (i.val + 1) = _
    rw [F.factor, hv]
    simp only [map_neg, map_pow]
    ring
  obtain ⟨ha, hb⟩ := (real_phase_endpoints_unique _ _ _ _ hi).mp he
  exact current_rotation_ne_self c (ha.trans hb.symm)

/-- 実際の receiver の選択根を含む、同じ族の三因子データ。
Q,kappa,選択根の等式、加法関係、原始性、非分岐性を一つの F のもとで返す。
新反例への再入や測度減少という未供給のフィールドは追加しない。 -/
theorem current_three_phase_data_receiver (c : CurrentCommonPrimeCyclotomicPacket h q) :
    ∃ F : CurrentPhaseSeventhFamily p,
      (∃ (Q : PrimaryPacket) (kappa : Cˣ),
        Q.gap = SevenRealCubicInt.rotateEquiv p.rho - p.rho ∧ Q.parameter = p.rho ∧
        Q.phase = phaseInverseExponent c.phase ∧ Q.source = currentLinearCarrier c ∧
        Q.delta = kappa ^ 7 ∧ F.root (currentPhaseSlot c.phase) = (kappa : C) * Q.gamma ∧
        Ideal.span ({F.root (currentPhaseSlot c.phase)} : Set C) = Ideal.span ({Q.gamma} : Set C)) ∧
      (F.root 0 ^ 7 + ofReal SevenRealCubicInt.alpha * F.root 2 ^ 7 =
        ofReal (1 + SevenRealCubicInt.alpha) * F.root 1 ^ 7) ∧
      (Pairwise fun i j : Fin 6 =>
        IsCoprime (Ideal.span ({F.root i} : Set C)) (Ideal.span ({F.root j} : Set C))) ∧
      (∀ i, ¬ ramifiedUniformizer ∣ F.root i) ∧ Fermat7Equation a b d := by
  obtain ⟨Q, kappa, F, hgap, hp, hj, hs, hd, hroot, hi, hF⟩ := current_phase_family_receiver c
  exact ⟨F, ⟨Q, kappa, hgap, hp, hj, hs, hd, hroot, hi⟩,
    F.real_weighted_seventh_equation, F.root_ideals_pairwise, F.root_away, hF⟩

end
end DkMath.FLT.Kummer.SevenRealGN
