import DkMath.CosmicFormula.Rotation.CF2D.IntrinsicPi

/-!
# 内在的定数と標準の円周率の比較

ここで初めて標準の三角関数と `Real.pi` を用いる。`θ_n = π / 2^(n+1)` とし、
初期値と非負の半角公式による帰納法で `u_n = (cos θ_n, sin θ_n)` を示す。
したがって `A_n = 2^(n+1) sin θ_n = π sinc θ_n` である。

`θ_n → 0` と `sinc` の 0 での連続性から `A_n → π` を得る。別途証明した
`A_n → intrinsicPi` と極限の一意性を合わせて両定数を同一視する。ここでの
三角関数の使用は比較のためであり、内在的定数の定義や有界性には使わない。
-/
namespace DkMath.CosmicFormula.Rotation.CF2D
open QuadrantUnitKernel Filter
open scoped Topology

/--
比較に使う角度 `θ_n = π / 2^(n+1)`。内在的な核列の定義には現れない。
-/
noncomputable def dyadicAngle (n : ℕ) : ℝ := Real.pi / (2 : ℝ) ^ (n + 1)

/--
各比較角は正であり、後で `sinc θ_n = sin θ_n / θ_n` を使える。
-/
private theorem dyadicAngle_pos (n : ℕ) : 0 < dyadicAngle n := by
  exact div_pos Real.pi_pos (pow_pos (by norm_num) _)

/--
比較角は π 以下であり、半角公式の符号条件を満たす。
-/
private theorem dyadicAngle_le (n : ℕ) : dyadicAngle n ≤ Real.pi := by
  unfold dyadicAngle
  apply div_le_self Real.pi_pos.le
  exact one_le_pow₀ (by norm_num)

/--
比較角の次項は前項の半分である。
-/
private theorem dyadicAngle_succ (n : ℕ) : dyadicAngle (n+1) = dyadicAngle n / 2 := by
  simp only [dyadicAngle, pow_succ, Nat.add_assoc]
  ring

/--
二分核の座標は、それぞれ角度 `θ_n` の余弦と正弦に等しい。

初期核は角度 `π/2` に対応する。帰納段階では角度の範囲を確認してから
非負平方根の半角公式を適用する。
-/
theorem sequence_trig (n : ℕ) :
    (sequence n).core = Real.cos (dyadicAngle n) ∧ (sequence n).beam = Real.sin (dyadicAngle n) := by
  induction n with
  | zero => simp [QuadrantUnitKernel.sequence, initial, core, beam, dyadicAngle]
  | succ n ih =>
    have hp := dyadicAngle_pos n
    have hl := dyadicAngle_le n
    rw [dyadicAngle_succ]
    constructor
    · change Real.sqrt ((1 + (sequence n).core) / 2) = _
      rw [ih.1, Real.cos_half (by linarith) hl]
    · change Real.sqrt ((1 - (sequence n).core) / 2) = _
      rw [ih.1, Real.sin_half_eq_sqrt hp.le (by nlinarith [Real.pi_pos])]

/--
座標の比較を面積候補に代入すると `A_n = 2^(n+1) sin(π/2^(n+1))` を得る。
-/
theorem areaApprox_eq_trig (n : ℕ) :
    areaApprox n = (2 : ℝ) ^ (n+1) * Real.sin (Real.pi / (2 : ℝ) ^ (n+1)) := by
  rw [areaApprox, (sequence_trig n).2]
  rfl


/--
`θ_n = (π/2)(1/2)^n` なので比較角は 0 に収束する。
-/
private theorem tendsto_dyadicAngle : Tendsto dyadicAngle atTop (𝓝 0) := by
  have hp : Tendsto (fun n : ℕ => ((2 : ℝ)⁻¹ ^ n)) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h := hp.const_mul (Real.pi / 2)
  convert h using 1
  · funext n
    simp only [dyadicAngle, pow_succ, div_eq_mul_inv, mul_inv_rev, inv_pow]
    ac_rfl
  · simp

/--
面積候補は標準の円周率に収束する。

各 `θ_n` は正なので `A_n = π sinc θ_n` と書ける。`θ_n → 0`、
`sinc 0 = 1`、および `sinc` の連続性から結論する。
-/
theorem tendsto_areaApprox_real_pi : Tendsto areaApprox atTop (𝓝 Real.pi) := by
  have hs : Tendsto (fun n => Real.sinc (dyadicAngle n)) atTop (𝓝 1) := by
    simpa only [Real.sinc_zero, Function.comp_def] using Real.continuous_sinc.continuousAt.tendsto.comp tendsto_dyadicAngle
  have hm := hs.const_mul Real.pi
  have he : areaApprox = fun n => Real.pi * Real.sinc (dyadicAngle n) := by
    funext n
    rw [areaApprox_eq_trig, Real.sinc_of_ne_zero (ne_of_gt (dyadicAngle_pos n))]
    unfold dyadicAngle
    have hp : (2 : ℝ) ^ (n+1) ≠ 0 := pow_ne_zero _ (by norm_num)
    have hp' : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    field_simp
  rw [he]
  simpa using hm

/--
面積候補の二つの収束先は、実数の極限の一意性により一致する。
-/
theorem intrinsicPi_eq_real_pi : intrinsicPi = Real.pi :=
  tendsto_nhds_unique tendsto_areaApprox_intrinsicPi tendsto_areaApprox_real_pi

end DkMath.CosmicFormula.Rotation.CF2D
