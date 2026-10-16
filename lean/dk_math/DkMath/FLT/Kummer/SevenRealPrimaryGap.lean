/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.SevenRamifiedFrobenius

/-!
# 実三次一次合同と gap 可除性

lambda^2∣gap と非零な parameter 剰余のもとで、一次単元の根は剰余1に限られる。
従って一次合同は 7*(zeta^i-1)∣gap を必要とする。
逆にこの深い gap 可除性があれば、根の剰余1から一次合同を構成できる。
-/

open DkMath.FLT.Seven DkMath.FLT.Kummer.SevenPrimaryNorm
open DkMath.Lib.Algebra

namespace DkMath.FLT.Kummer.SevenRealGN

noncomputable section
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
open SevenCyclotomicDegreeSixInt

/-- 非自明位相の分岐因子は非零。単元 T_i と lambda の積として検証する。 -/
theorem phaseRamifier_ne_zero {i : ℕ} (hi : i ∈ (Finset.range 7).erase 0) :
    zeta ^ i - 1 ≠ 0 := by
  rw [← GNRamifierTwist_spec hi]
  exact mul_ne_zero (GNRamifierTwist hi).isUnit.ne_zero ramifiedUniformizer_ne_zero

/-- lambda=1-zeta の単元を、同じ根を保って zeta^i-1 の単元へ補正する。 -/
theorem factor_after_ramifier_twist {x u : R} {i : ℕ}
    (hi : i ∈ (Finset.range 7).erase 0) (epsilon : Cˣ) (beta : C)
    (hfactor : realGNSource x u i = ramifiedUniformizer * ((epsilon : C) * beta ^ 7)) :
    realGNSource x u i = (zeta ^ i - 1) *
      (((epsilon * (GNRamifierTwist hi)⁻¹ : Cˣ) : C) * beta ^ 7) := by
  rw [hfactor, ← GNRamifierTwist_spec hi]
  change ramifiedUniformizer * ((epsilon : C) * beta ^ 7) =
    ((GNRamifierTwist hi : C) * ramifiedUniformizer) *
      (((epsilon : C) * (↑(GNRamifierTwist hi)⁻¹ : C)) * beta ^ 7)
  have hc : (GNRamifierTwist hi : C) * (↑(GNRamifierTwist hi)⁻¹ : C) = 1 :=
    (GNRamifierTwist hi).val_inv
  calc
    _ = ramifiedUniformizer * ((epsilon : C) * beta ^ 7) *
        ((GNRamifierTwist hi : C) * (↑(GNRamifierTwist hi)⁻¹ : C)) := by rw [hc, mul_one]
    _ = _ := by ring

/-- source の分解から gap の正確な等式を取り出す。係数は R のまま保つ。 -/
theorem factor_gap_identity {x u : R} {i : ℕ} (delta : Cˣ) (beta : C)
    (hfactor : realGNSource x u i = (zeta ^ i - 1) * ((delta : C) * beta ^ 7)) :
    ofReal x = (zeta ^ i - 1) * ((delta : C) * beta ^ 7 + ofReal u) := by
  change ofReal x + (1 - zeta ^ i) * ofReal u = _ at hfactor
  linear_combination hfactor

/-- 一次合同を分岐剰余へ落とす。mod 7 と mod lambda を混同しないための接続。 -/
theorem realPrimary_residue (delta : Cˣ) (b : R) (h : RealPrimary delta b) :
    ramifiedEval (delta : C) = SevenRealCubicInt.thetaResidue b := by
  obtain ⟨w, hw⟩ := h
  have he := congrArg ramifiedEval hw
  simpa only [map_sub, ramifiedEval_ofReal, map_mul, map_ofNat,
    show (7 : ZMod 7) = 0 from rfl, zero_mul, sub_eq_zero] using he

/-- gap の二段分岐性と parameter の非零剰余のもとで、一次単元の根は剰余1。
任意に選んだ根が最初からこの条件を満たすとは主張しない。 -/
theorem root_residue_one_of_primary {x u : R} {i : ℕ}
    (hi : i ∈ (Finset.range 7).erase 0) (delta : Cˣ) (beta : C)
    (hx : ramifiedUniformizer ^ 2 ∣ ofReal x)
    (hu : SevenRealCubicInt.thetaResidue u ≠ 0)
    (hfactor : realGNSource x u i = (zeta ^ i - 1) * ((delta : C) * beta ^ 7))
    (hprimary : RealPrimary delta (-u)) : ramifiedEval beta = 1 := by
  obtain ⟨w, hw⟩ := hx
  have hg := factor_gap_identity delta beta hfactor
  have hc : (GNRamifierTwist hi : C) * ((delta : C) * beta ^ 7 + ofReal u) =
      ramifiedUniformizer * w := by
    apply mul_left_cancel₀ ramifiedUniformizer_ne_zero
    rw [← mul_assoc, mul_comm ramifiedUniformizer (GNRamifierTwist hi : C),
      GNRamifierTwist_spec hi, ← hg, hw]
    ring
  have hr := congrArg ramifiedEval hc
  rw [map_mul, map_mul, ramifiedEval_uniformizer, zero_mul] at hr
  have ht : ramifiedEval (GNRamifierTwist hi : C) ≠ 0 :=
    ((GNRamifierTwist hi).isUnit.map ramifiedEval).ne_zero
  have hz := (mul_eq_zero.mp hr).resolve_left ht
  simp only [map_add, map_mul, map_pow, ramifiedEval_ofReal, ZMod.pow_card] at hz
  have hd := realPrimary_residue delta (-u) hprimary
  rw [map_neg] at hd
  rw [hd] at hz
  have he : SevenRealCubicInt.thetaResidue u * (ramifiedEval beta - 1) = 0 := by
    linear_combination -hz
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hu)

/-- 候補だった必要条件。一次合同と二段分岐 gap から 7*(zeta^i-1)∣gap を導く。 -/
theorem gap_divisible_of_primary {x u : R} {i : ℕ}
    (hi : i ∈ (Finset.range 7).erase 0) (delta : Cˣ) (beta : C)
    (hx : ramifiedUniformizer ^ 2 ∣ ofReal x)
    (hu : SevenRealCubicInt.thetaResidue u ≠ 0)
    (hfactor : realGNSource x u i = (zeta ^ i - 1) * ((delta : C) * beta ^ 7))
    (hprimary : RealPrimary delta (-u)) : (7 : C) * (zeta ^ i - 1) ∣ ofReal x := by
  have hb := seventh_sub_one_dvd_seven_of_residue_one
    (root_residue_one_of_primary hi delta beta hx hu hfactor hprimary)
  have hd : (7 : C) ∣ (delta : C) + ofReal u := by
    simpa only [RealPrimary, map_neg, sub_neg_eq_add] using hprimary
  have hs : (7 : C) ∣ (delta : C) * beta ^ 7 + ofReal u := by
    convert dvd_add (dvd_mul_of_dvd_right hb (delta : C)) hd using 1
    ring
  rw [factor_gap_identity delta beta hfactor]
  simpa only [mul_comm (7 : C) (zeta ^ i - 1)] using mul_dvd_mul_left (zeta ^ i - 1) hs

/-- 深い gap 可除性のもとでは、根の剰余1から一次合同を逆に供給できる。 -/
theorem primary_of_root_residue_one {x u : R} {i : ℕ}
    (hi : i ∈ (Finset.range 7).erase 0) (delta : Cˣ) (beta : C)
    (hx : (7 : C) * (zeta ^ i - 1) ∣ ofReal x)
    (hfactor : realGNSource x u i = (zeta ^ i - 1) * ((delta : C) * beta ^ 7))
    (hbeta : ramifiedEval beta = 1) : RealPrimary delta (-u) := by
  obtain ⟨w, hw⟩ := hx
  have he : (delta : C) * beta ^ 7 + ofReal u = 7 * w := by
    apply mul_left_cancel₀ (phaseRamifier_ne_zero hi)
    rw [← factor_gap_identity delta beta hfactor, hw]
    ring
  have hd : (7 : C) ∣ (delta : C) * beta ^ 7 + ofReal u := ⟨w, he⟩
  have hb := dvd_mul_of_dvd_right (seventh_sub_one_dvd_seven_of_residue_one hbeta) (delta : C)
  change (7 : C) ∣ (delta : C) - ofReal (-u)
  rw [map_neg, sub_neg_eq_add]
  convert dvd_sub hd hb using 1
  ring

/-- 根の選択への依存を必要十分条件で固定する。強い gap 条件がある場合でも、
任意の根ではなく、剰余1の根に対してちょうど一次合同が成立する。 -/
theorem primary_iff_root_residue_one {x u : R} {i : ℕ}
    (hi : i ∈ (Finset.range 7).erase 0) (delta : Cˣ) (beta : C)
    (hx2 : ramifiedUniformizer ^ 2 ∣ ofReal x)
    (hx7 : (7 : C) * (zeta ^ i - 1) ∣ ofReal x)
    (hu : SevenRealCubicInt.thetaResidue u ≠ 0)
    (hfactor : realGNSource x u i = (zeta ^ i - 1) * ((delta : C) * beta ^ 7)) :
    RealPrimary delta (-u) ↔ ramifiedEval beta = 1 :=
  ⟨root_residue_one_of_primary hi delta beta hx2 hu hfactor,
    primary_of_root_residue_one hi delta beta hx7 hfactor⟩

/-- 正規化後の根をさらに単元 t 倍する場合、一次合同を保つ条件は剰余 t=1。
任意の単元による初期正規化と、前章の許容正規化の違いを明示する。 -/
theorem primary_after_root_gauge_iff {x u : R} {i : ℕ}
    (hi : i ∈ (Finset.range 7).erase 0) (delta : Cˣ) (beta : C) (t : Cˣ)
    (hx2 : ramifiedUniformizer ^ 2 ∣ ofReal x)
    (hx7 : (7 : C) * (zeta ^ i - 1) ∣ ofReal x)
    (hu : SevenRealCubicInt.thetaResidue u ≠ 0)
    (hfactor : realGNSource x u i = (zeta ^ i - 1) * ((delta : C) * beta ^ 7))
    (hbeta : ramifiedEval beta = 1) :
    RealPrimary (delta * t⁻¹ ^ 7) (-u) ↔ ramifiedEval (t : C) = 1 := by
  have hf := hfactor.trans (root_unit_gauge_identity (zeta ^ i - 1) beta delta t 7)
  rw [primary_iff_root_residue_one hi _ _ hx2 hx7 hu hf, map_mul, hbeta, mul_one]

/-- 非分岐な剥離根を正規化して一次合同を作れることと、gap の必要条件は同値。
source と分岐因子を固定し、同じ単元 t で根と係数単元を同時に補正する。 -/
theorem exists_primary_root_gauge_iff_gap_divisible {x u : R} {i : ℕ}
    (hi : i ∈ (Finset.range 7).erase 0) (delta : Cˣ) (beta : C)
    (hx : ramifiedUniformizer ^ 2 ∣ ofReal x)
    (hu : SevenRealCubicInt.thetaResidue u ≠ 0)
    (hb : ¬ ramifiedUniformizer ∣ beta)
    (hfactor : realGNSource x u i = (zeta ^ i - 1) * ((delta : C) * beta ^ 7)) :
    (∃ t : Cˣ, RealPrimary (delta * t⁻¹ ^ 7) (-u)) ↔
      (7 : C) * (zeta ^ i - 1) ∣ ofReal x := by
  constructor
  · rintro ⟨t, ht⟩
    exact gap_divisible_of_primary hi _ _ hx hu
      (hfactor.trans (root_unit_gauge_identity (zeta ^ i - 1) beta delta t 7)) ht
  · intro hg
    obtain ⟨t, ht⟩ := exists_root_residue_normalizer beta hb
    exact ⟨t, primary_of_root_residue_one hi _ _ hg
      (hfactor.trans (root_unit_gauge_identity (zeta ^ i - 1) beta delta t 7)) ht⟩

end

end DkMath.FLT.Kummer.SevenRealGN
