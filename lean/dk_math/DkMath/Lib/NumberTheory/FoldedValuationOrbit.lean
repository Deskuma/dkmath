/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_FreyPackage_freyCurve_rational_p_torsion_eq_zero.lean, section S04.Arith.
Upstream blob: fe61fd5d4f94d55b5a9da38d1541903c84397df0
Modified for DkMath: isolate the integer recurrence, simplify prime cancellation,
and retain a geometry-independent interface for the actual point-valuation bridge.
-/

import Mathlib.Data.Nat.Prime.Int
import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

#print "file: DkMath.Lib.NumberTheory.FoldedValuationOrbit"

/-!
# 付値の有限軌道を、合同軌道の折り返しへ翻訳する

Frey曲線の有理p-torsion排除に現れる純整数部分を切り出す。
点の加法が付値の漸化式を満たすことと、付値が1からγ−1に留まることは別の算術入力。
このファイルはその入力の帰結を証明し、幾何学を仮定なしに済ませたとは主張しない。

法が2γ=2(pv−4)の場合、奇素数pは法を割らない。従って周期pの条件を約分できる。
一般の漸化式の証明はpの素数性を使わず、約分可能性だけを使う。
-/
namespace DkMath.Lib.NumberTheory.FoldedValuationOrbit

/-- γ=pv−4の法2γは奇素数pで割れない。pで割れれば8=2³も割ってしまう。 -/
theorem prime_not_dvd_modulus (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (v : ℤ) :
    ¬ (p : ℤ) ∣ 2 * ((p : ℤ) * v - 4) := by
  intro hd
  have h8 : (p : ℤ) ∣ 8 := by
    convert dvd_sub (dvd_mul_of_dvd_right (dvd_mul_right (p : ℤ) v) 2) hd using 1; ring
  have hpint := Nat.prime_iff_prime_int.mp hp
  have hpow : (p : ℤ) ∣ (2 : ℤ) ^ 3 := by norm_num at h8 ⊢; exact h8
  have h2 : p ∣ 2 := by exact_mod_cast hpint.dvd_of_dvd_pow hpow
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)

/-- 付値軌道の周期を約分する。vの正値性は不要で、p≠2を明示する。 -/
theorem cancel_prime_modulus (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (v m : ℤ)
    (hm : 2 * ((p : ℤ) * v - 4) ∣ (p : ℤ) * m) :
    2 * ((p : ℤ) * v - 4) ∣ m := by
  obtain ⟨t, ht⟩ := hm
  have hpt : (p : ℤ) ∣ 2 * ((p : ℤ) * v - 4) * t := ⟨m, ht.symm⟩
  rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd hpt with h | h
  · exact (prime_not_dvd_modulus p hp hp2 v h).elim
  · obtain ⟨s, rfl⟩ := h
    refine ⟨s, ?_⟩
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    apply mul_left_cancel₀ hp0
    calc
      (p : ℤ) * m = 2 * ((p : ℤ) * v - 4) * ((p : ℤ) * s) := ht
      _ = (p : ℤ) * (2 * ((p : ℤ) * v - 4) * s) := by ring

/-- 長さ6γの区間にある2γの倍数は、ここでは0または−2γだけ。 -/
private lemma wrap_cases {γ t : ℤ} (hγ : 0 < γ) (hdvd : 2 * γ ∣ t) (h1 : -4 * γ < t) (h2 : t < 2 * γ) :
    t = 0 ∨ t = -(2 * γ) := by
  obtain ⟨q, hq⟩ := hdvd
  have hq1 : q < 1 := by
    by_contra h; push Not at h; nlinarith
  have hq2 : -2 < q := by
    by_contra h; push Not at h; nlinarith
  have : q = 0 ∨ q = -1 := by omega
  rcases this with rfl | rfl
  · left; rw [hq]; ring
  · right; rw [hq]; ring

/-- 絶対値が法2γより小さい倍数は零である。 -/
private lemma wrap_zero {γ t : ℤ} (hγ : 0 < γ) (hdvd : 2 * γ ∣ t) (h1 : -(2 * γ) < t) (h2 : t < 2 * γ) :
    t = 0 := by
  obtain ⟨q, hq⟩ := hdvd
  have hq1 : q < 1 := by
    by_contra h; push Not at h; nlinarith
  have hq2 : -1 < q := by
    by_contra h; push Not at h; nlinarith
  have : q = 0 := by omega
  rw [hq, this]; ring

/-- 有限軌道の付値データを折り返した合同軌道へ翻訳し、正の深さと周期pを矛盾させる。

`e k`は想定される点kQのx座標の付値、`A k`と`B k`は加法公式の分子・分母の付値に
対応する整数列である。この定理自体は整数列の定理で、実際の曲線の点は入力しない。
等しい付値での打ち消しを考慮して、min公式は非一致時の等号と一致時の下界に分ける。

ε=e(1)とおく。帰納法でθ≡kε mod 2γ、−γ<θ≤γ、e(k)=±θを示す。
両端のe(p−1)=e(1)から、e(p−2)=0または2γ∣pεが従う。前者は正の深さに反し、
後者は`hdiv`によるpの約分と0<ε<γに反する。`hbd`などを実際の曲線から供給する
証明は`WeierstrassValuationOrbit`、Frey Sourceの係数供給は`FreyRationalTorsion`に置く。
この純整数定理自体は点の存在や幾何学的な入力を供給しない。 -/
theorem no_folded_valuation_orbit (p : ℕ) (hp5 : 5 ≤ p) (γ : ℤ) (e A B : ℕ → ℤ) (A₁ : ℤ)
    (hbd : ∀ k, 1 ≤ k → k ≤ p - 1 → 1 ≤ e k ∧ e k ≤ γ - 1)
    (hA₁ : (2 * e 1 ≠ γ → A₁ = min (2 * e 1) γ) ∧ (2 * e 1 = γ → γ ≤ A₁))
    (h2 : e 2 + 2 * e 1 = 2 * A₁)
    (hA : ∀ k, 2 ≤ k → k ≤ p - 2 →
      (e k + e 1 ≠ γ → A k = min (e k + e 1) γ) ∧ (e k + e 1 = γ → γ ≤ A k))
    (hB : ∀ k, 2 ≤ k → k ≤ p - 2 →
      (e k ≠ e 1 → B k = min (e k) (e 1)) ∧ (e k = e 1 → e 1 ≤ B k))
    (hrec : ∀ k, 2 ≤ k → k ≤ p - 2 → e (k + 1) + e (k - 1) + 2 * B k = 2 * A k)
    (hend : e (p - 1) = e 1)
    (hdiv : ∀ m : ℤ, 2 * γ ∣ (p : ℤ) * m → 2 * γ ∣ m) : False := by
  set ε := e 1 with hε
  have hε1 : 1 ≤ ε ∧ ε ≤ γ - 1 := hbd 1 le_rfl (by omega)
  have hγ : 0 < γ := by omega
  have h2ne : 2 * ε ≠ γ := by
    intro h2eq
    have := hA₁.2 h2eq
    have hb2 := hbd 2 (by norm_num) (by omega)
    omega
  have hA₁' : A₁ = min (2 * ε) γ := hA₁.1 h2ne
  -- 正規化した代表θは境界を越えるたび2γを引き、付値はその絶対値になる。
  have claim : ∀ k, 1 ≤ k → k ≤ p - 1 →
      ∃ θ : ℤ, 2 * γ ∣ θ - (k : ℤ) * ε ∧ -γ < θ ∧ θ ≤ γ ∧ (e k = θ ∨ e k = -θ) := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro hk1 hkp
      rcases Nat.lt_or_ge k 3 with hk3 | hk3
      · interval_cases k
        · exact ⟨ε, by simp, by omega, by omega, Or.inl rfl⟩
        · have hb2 := hbd 2 (by norm_num) hkp
          by_cases hlt : 2 * ε < γ
          · refine ⟨2 * ε, by simp, by omega, by omega, Or.inl ?_⟩
            rw [min_eq_left hlt.le] at hA₁'
            omega
          · refine ⟨2 * ε - 2 * γ, ⟨-1, by push_cast; ring⟩, by omega, by omega, Or.inr ?_⟩
            rw [min_eq_right (by omega)] at hA₁'
            omega
      · obtain ⟨θ, hθd, hθ1, hθ2, hθe⟩ := ih (k - 1) (by omega) (by omega) (by omega)
        obtain ⟨θ', hθ'd, hθ'1, hθ'2, hθ'e⟩ := ih (k - 2) (by omega) (by omega) (by omega)
        have hbk := hbd k hk1 hkp
        have hbj := hbd (k - 1) (by omega) (by omega)
        have hbj' := hbd (k - 2) (by omega) (by omega)
        have hr := hrec (k - 1) (by omega) (by omega)
        rw [show k - 1 + 1 = k by omega, show k - 1 - 1 = k - 2 by omega] at hr
        have hAk := hA (k - 1) (by omega) (by omega)
        have hBk := hB (k - 1) (by omega) (by omega)
        have hcast : ((k - 1 : ℕ) : ℤ) = ((k - 2 : ℕ) : ℤ) + 1 := by omega
        have hdd : 2 * γ ∣ θ - θ' - ε := by
          have : θ - θ' - ε = (θ - ((k - 1 : ℕ) : ℤ) * ε) - (θ' - ((k - 2 : ℕ) : ℤ) * ε) := by
            rw [hcast]; ring
          rw [this]; exact dvd_sub hθd hθ'd
        have hwrap := wrap_cases hγ hdd (by omega) (by omega)
        have hcast' : ((k : ℕ) : ℤ) = ((k - 1 : ℕ) : ℤ) + 1 := by omega
        have hdvdp : 2 * γ ∣ (θ + ε) - (k : ℤ) * ε := by
          have : (θ + ε) - (k : ℤ) * ε = θ - ((k - 1 : ℕ) : ℤ) * ε := by rw [hcast']; ring
          rw [this]; exact hθd
        have hdvdm : 2 * γ ∣ (θ + ε - 2 * γ) - (k : ℤ) * ε := by
          have : (θ + ε - 2 * γ) - (k : ℤ) * ε = (θ - ((k - 1 : ℕ) : ℤ) * ε) - 2 * γ := by
            rw [hcast']; ring
          rw [this]; exact dvd_sub hθd (dvd_refl _)
        by_cases hdeg1 : e (k - 1) = ε
        · exfalso
          have hB' := hBk.2 hdeg1
          rcases hθe with hθe | hθe
          · by_cases hθε : θ = ε
            · rcases hwrap with hw | hw <;> omega
            · omega
          · have hθε : θ = -ε := by omega
            have hA' : A (k - 1) = min (e (k - 1) + ε) γ := hAk.1 (by omega)
            rw [hdeg1] at hA'
            rcases le_or_gt (ε + ε) γ with h | h
            · rw [min_eq_left h] at hA'
              rcases hwrap with hw | hw <;> omega
            · rw [min_eq_right h.le] at hA'
              rcases hwrap with hw | hw <;> omega
        by_cases hdeg2 : e (k - 1) + ε = γ
        · exfalso
          have hA' := hAk.2 hdeg2
          have hB' : B (k - 1) = min (e (k - 1)) ε := hBk.1 hdeg1
          rcases hθe with hθe | hθe
          · rcases le_or_gt (e (k - 1)) ε with h | h
            · rw [min_eq_left h] at hB'
              rcases hwrap with hw | hw <;> omega
            · rw [min_eq_right h.le] at hB'
              rcases hwrap with hw | hw <;> omega
          · rcases hwrap with hw | hw <;> omega
        have hA' : A (k - 1) = min (e (k - 1) + ε) γ := hAk.1 hdeg2
        have hB' : B (k - 1) = min (e (k - 1)) ε := hBk.1 hdeg1
        by_cases hup : θ + ε ≤ γ
        · refine ⟨θ + ε, hdvdp, by omega, hup, ?_⟩
          rcases le_or_gt (e (k - 1) + ε) γ with h | h <;>
            rcases le_or_gt (e (k - 1)) ε with h' | h'
          · rw [min_eq_left h] at hA'; rw [min_eq_left h'] at hB'
            rcases hθe with hθe | hθe <;> rcases hwrap with hw | hw <;> omega
          · rw [min_eq_left h] at hA'; rw [min_eq_right h'.le] at hB'
            rcases hθe with hθe | hθe <;> rcases hwrap with hw | hw <;> omega
          · rw [min_eq_right h.le] at hA'; rw [min_eq_left h'] at hB'
            rcases hθe with hθe | hθe <;> rcases hwrap with hw | hw <;> omega
          · rw [min_eq_right h.le] at hA'; rw [min_eq_right h'.le] at hB'
            rcases hθe with hθe | hθe <;> rcases hwrap with hw | hw <;> omega
        · refine ⟨θ + ε - 2 * γ, hdvdm, by omega, by omega, ?_⟩
          rcases le_or_gt (e (k - 1) + ε) γ with h | h <;>
            rcases le_or_gt (e (k - 1)) ε with h' | h'
          · rw [min_eq_left h] at hA'; rw [min_eq_left h'] at hB'
            rcases hθe with hθe | hθe <;> rcases hwrap with hw | hw <;> omega
          · rw [min_eq_left h] at hA'; rw [min_eq_right h'.le] at hB'
            rcases hθe with hθe | hθe <;> rcases hwrap with hw | hw <;> omega
          · rw [min_eq_right h.le] at hA'; rw [min_eq_left h'] at hB'
            rcases hθe with hθe | hθe <;> rcases hwrap with hw | hw <;> omega
          · rw [min_eq_right h.le] at hA'; rw [min_eq_right h'.le] at hB'
            rcases hθe with hθe | hθe <;> rcases hwrap with hw | hw <;> omega
  -- 軌道の末尾は−Qに相当するので、最初の付値に戻る。
  obtain ⟨θ, hθd, hθ1, hθ2, hθe⟩ := claim (p - 1) (by omega) le_rfl
  obtain ⟨θ'', hθ''d, hθ''1, hθ''2, hθ''e⟩ := claim (p - 2) (by omega) (by omega)
  have hbp2 := hbd (p - 2) (by omega) (by omega)
  rw [hend] at hθe
  have hcast : ((p - 1 : ℕ) : ℤ) = ((p - 2 : ℕ) : ℤ) + 1 := by omega
  have hcastp : ((p : ℕ) : ℤ) = ((p - 1 : ℕ) : ℤ) + 1 := by omega
  rcases hθe with hθe | hθe
  · have hdd : 2 * γ ∣ θ'' := by
      have : θ'' = (θ'' - ((p - 2 : ℕ) : ℤ) * ε) - (θ - ((p - 1 : ℕ) : ℤ) * ε) + (θ - ε) := by
        rw [hcast]; ring
      have h0 : θ - ε = 0 := by omega
      rw [this, h0, add_zero]
      exact dvd_sub hθ''d hθd
    have := wrap_zero hγ hdd (by omega) (by omega)
    omega
  · have hdd : 2 * γ ∣ (p : ℤ) * ε := by
      have : (p : ℤ) * ε = -(θ - ((p - 1 : ℕ) : ℤ) * ε) + (θ + ε) := by
        rw [hcastp]; ring
      rw [this, show θ + ε = 0 by omega, add_zero]
      exact (dvd_neg).mpr hθd
    have hε2 := hdiv ε hdd
    have := wrap_zero hγ hε2 (by omega) (by omega)
    omega


/-- Frey型の法γ=pv−4では、約分可能性を素数性から供給できる。
入力は付値列の上下界・min法則・漸化式・末尾条件であり、実際の点からの供給は
`WeierstrassValuationOrbit`が担当する。p≥5は整数軌道の議論に必要な範囲である。 -/
theorem no_prime_shifted_valuation_orbit (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (v γ : ℤ) (hγ : γ = (p : ℤ) * v - 4) (e A B : ℕ → ℤ) (A₁ : ℤ)
    (hbd : ∀ k, 1 ≤ k → k ≤ p - 1 → 1 ≤ e k ∧ e k ≤ γ - 1)
    (hA₁ : (2 * e 1 ≠ γ → A₁ = min (2 * e 1) γ) ∧ (2 * e 1 = γ → γ ≤ A₁))
    (h2 : e 2 + 2 * e 1 = 2 * A₁)
    (hA : ∀ k, 2 ≤ k → k ≤ p - 2 →
      (e k + e 1 ≠ γ → A k = min (e k + e 1) γ) ∧ (e k + e 1 = γ → γ ≤ A k))
    (hB : ∀ k, 2 ≤ k → k ≤ p - 2 →
      (e k ≠ e 1 → B k = min (e k) (e 1)) ∧ (e k = e 1 → e 1 ≤ B k))
    (hrec : ∀ k, 2 ≤ k → k ≤ p - 2 → e (k + 1) + e (k - 1) + 2 * B k = 2 * A k)
    (hend : e (p - 1) = e 1)
    : False := by
  apply no_folded_valuation_orbit p hp5 γ e A B A₁ hbd hA₁ h2 hA hB hrec hend
  intro m hm
  rw [hγ] at hm ⊢
  exact cancel_prime_modulus p hp (by omega) v m hm

end DkMath.Lib.NumberTheory.FoldedValuationOrbit
