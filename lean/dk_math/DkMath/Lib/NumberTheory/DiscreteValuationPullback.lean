/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from DkMath.Lib.NumberTheory.EllipticValuationTransport,
originally Definitions/Def_EllipticCurve_FunctionFieldPullback.lean,
blob ce8783a9e9613db1c4c0323ce93fb0d89917ee65.
Modified: arbitrary source valuation; prove positive integral scaling of local orders.
-/

import DkMath.Lib.NumberTheory.EllipticValuationTransport

#print "file: DkMath.Lib.NumberTheory.DiscreteValuationPullback"

/-!
# 中心を保つ体の埋め込みと、離散付値の倍率

[DkMath.Lib] Dedekind環の素点wにおいて、極大イデアルの元が引き戻し後も消え、
その外の元が単元なら、任意の非零有理関数の整数位数は正整数e倍になる。
e=1は仮定しない。座標の特殊化と、未分岐性の証明を分離するための一般補題。
-/
namespace DkMath.Lib.NumberTheory.DiscreteValuationPullback
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
variable {R F L : Type*} [CommRing R] [IsDedekindDomain R]
  [Field F] [Algebra R F] [IsFractionRing R F] [Field L]
  (w : HeightOneSpectrum R) (v : Valuation L ℤᵐ⁰) (ψ : F →+* L)

omit [IsDedekindDomain R] [IsFractionRing R F] in
/-- [DkMath.Lib] 素点のイデアル冪の元は、引き戻し後も対応する位数以上で消える。 -/
theorem map_le_of_mem_pow
    (h₁ : ∀ b ∈ w.asIdeal, v (ψ (algebraMap R F b)) ≤ exp (-1 : ℤ))
    (h₂ : ∀ b ∉ w.asIdeal, v (ψ (algebraMap R F b)) = 1)
    (n : ℕ) : ∀ a ∈ w.asIdeal ^ n, v (ψ (algebraMap R F a)) ≤ exp (-(n : ℤ)) := by
  have h₀ (b : R) : v (ψ (algebraMap R F b)) ≤ 1 := by
    by_cases hb : b ∈ w.asIdeal
    · exact (h₁ b hb).trans (by rw [← exp_zero, exp_le_exp]; norm_num)
    · exact (h₂ b hb).le
  induction n with
  | zero => intro a _; simpa only [Nat.cast_zero, neg_zero, exp_zero] using h₀ a
  | succ n ih =>
    intro a ha
    rw [pow_succ'] at ha
    refine Submodule.mul_induction_on ha ?_ ?_
    · intro b hb c hc
      rw [map_mul, map_mul, map_mul, Nat.cast_succ, neg_add, add_comm, exp_add]
      exact mul_le_mul' (h₁ b hb) (ih c hc)
    · intro a b ha hb
      rw [map_add, map_add]
      exact (v.map_add _ _).trans (max_le ha hb)

/-- [DkMath.Lib] 局所環の分母を素点の外に選び、位数の下界を分数体全体へ運ぶ。 -/
theorem map_le_of_le
    (h₁ : ∀ b ∈ w.asIdeal, v (ψ (algebraMap R F b)) ≤ exp (-1 : ℤ))
    (h₂ : ∀ b ∉ w.asIdeal, v (ψ (algebraMap R F b)) = 1)
    (f : F) (n : ℕ) (hf : w.valuation F f ≤ exp (-(n : ℤ))) :
    v (ψ f) ≤ exp (-(n : ℤ)) := by
  have hf₀ : w.valuation F f ≤ 1 :=
    hf.trans (by rw [← exp_zero, exp_le_exp]; omega)
  obtain ⟨a, d, had⟩ := w.exists_primeCompl_mul_eq_of_integer f hf₀
  have hd : (d : R) ∉ w.asIdeal := d.property
  have ha : w.valuation F (algebraMap R F a) ≤ exp (-(n : ℤ)) := by
    rw [← had, map_mul, (w.valuation_eq_one_iff_notMem (K := F)).mpr hd, mul_one]
    exact hf
  rw [valuation_of_algebraMap, intValuation_le_pow_iff_mem] at ha
  have hm := map_le_of_mem_pow w v ψ h₁ h₂ n a ha
  have he := congrArg (fun z => v (ψ z)) had
  simp only [map_mul, h₂ d hd, mul_one] at he
  exact he ▸ hm

/-- [DkMath.Lib] 標的の局所単元は引き戻し後も付値1。元と逆数の正則性を使う。 -/
theorem map_eq_one_of_eq_one
    (h₁ : ∀ b ∈ w.asIdeal, v (ψ (algebraMap R F b)) ≤ exp (-1 : ℤ))
    (h₂ : ∀ b ∉ w.asIdeal, v (ψ (algebraMap R F b)) = 1)
    (f : F) (hf : w.valuation F f = 1) : v (ψ f) = 1 := by
  have hf₀ : f ≠ 0 := fun h => by simp only [h, map_zero] at hf; exact zero_ne_one hf
  have hi : w.valuation F f⁻¹ = 1 := by rw [map_inv₀, hf, inv_one]
  have hl := map_le_of_le w v ψ h₁ h₂ f 0 (by simpa using hf.le)
  have hu := map_le_of_le w v ψ h₁ h₂ f⁻¹ 0 (by simpa using hi.le)
  simp only [Nat.cast_zero, neg_zero, exp_zero, map_inv₀] at hl hu
  exact le_antisymm hl ((inv_le_one₀ ((v.ne_zero_iff.mpr ((map_ne_zero ψ).mpr hf₀)).bot_lt)).mp hu)

/-- [DkMath.Lib] 中心を保つ埋め込みの局所位数は、同じ正整数e倍になる。
一様化元πに対しe=−log(v(ψπ))と置き、fπ^{log(w(f))}が単元であることから従う。
倍率1という追加条件は、この一般定理では供給しない。 -/
theorem exists_pos_order_scaling
    (h₁ : ∀ b ∈ w.asIdeal, v (ψ (algebraMap R F b)) ≤ exp (-1 : ℤ))
    (h₂ : ∀ b ∉ w.asIdeal, v (ψ (algebraMap R F b)) = 1) :
    ∃ e : ℤ, 0 < e ∧ ∀ f : F, f ≠ 0 →
      -log (v (ψ f)) = e * (-log (w.valuation F f)) := by
  obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer F
  have hπ₀ : π ≠ 0 := fun h => by simp only [h, map_zero] at hπ; exact exp_ne_zero hπ.symm
  have hvπ₀ : v (ψ π) ≠ 0 := v.ne_zero_iff.mpr ((map_ne_zero ψ).mpr hπ₀)
  have hvπ := map_le_of_le w v ψ h₁ h₂ π 1 (by simpa using hπ.le)
  have hvπ' : log (v (ψ π)) ≤ -1 := by
    rw [← exp_log hvπ₀, exp_le_exp] at hvπ
    simpa using hvπ
  refine ⟨-log (v (ψ π)), by omega, ?_⟩
  intro f hf
  let z := log (w.valuation F f)
  have hwf : w.valuation F f ≠ 0 := (w.valuation F).ne_zero_iff.mpr hf
  have hu : w.valuation F (f * π ^ z) = 1 := by
    have hn : w.valuation F (f * π ^ z) ≠ 0 :=
      (w.valuation F).ne_zero_iff.mpr (mul_ne_zero hf (zpow_ne_zero _ hπ₀))
    apply (exp_log hn).symm.trans
    suffices hz : log (w.valuation F (f * π ^ z)) = 0 by rw [hz, exp_zero]
    rw [map_mul, map_zpow₀, log_mul hwf (zpow_ne_zero _ ((w.valuation F).ne_zero_iff.mpr hπ₀)), hπ,
      log_zpow, log_exp]
    change z + z • (-1 : ℤ) = 0
    simp
  have hvu := map_eq_one_of_eq_one w v ψ h₁ h₂ (f * π ^ z) hu
  have hlog := congrArg WithZero.log hvu
  rw [map_mul, map_zpow₀, map_mul, map_zpow₀,
    log_mul (v.ne_zero_iff.mpr ((map_ne_zero ψ).mpr hf)) (zpow_ne_zero _ hvπ₀), log_zpow, log_one] at hlog
  change log (v (ψ f)) + z * log (v (ψ π)) = 0 at hlog
  change -log (v (ψ f)) = -log (v (ψ π)) * -z
  nlinarith

end DkMath.Lib.NumberTheory.DiscreteValuationPullback
