import DkMath.CosmicFormula.Rotation.CF2D.HalfKernel

/-!
# 二分核から作る面積・半周長の候補

`u_n = (c_n,s_n)` に対して `A_n = 2^(n+1) s_n`、
`P_n = 2^(n+1) √(2-2c_n)` を定める。これらは内接正多角形の面積と
半周長に対応する代数的候補であり、このファイルでは幾何学的な同一視は証明しない。

半分核の第２座標から `P_n = A_(n+1)` が従う。また、核の合成から
`A_n = c_(n+1) A_(n+1)` を得る。`0 ≤ c_(n+1) ≤ 1` により `A_n` は
単調非減少である。上界には `U_n = A_(n+1) / c_(n+1)` を用いる。
分母が正であることを先に示し、`U_n` の単調非増加と `U_0 = 4` から
`A_n ≤ 4` を得る。これらは平方根と順序だけを用いた議論である。
-/
namespace DkMath.CosmicFormula.Rotation.CF2D
open QuadrantUnitKernel

/--
`A_n = 2^(n+1) s_n`。面積に対応する代数的候補。
-/
noncomputable def areaApprox (n : ℕ) : ℝ := (2 : ℝ) ^ (n + 1) * (sequence n).beam
/--
`P_n = 2^(n+1) √(2-2c_n)`。半周長に対応する代数的候補。
-/
noncomputable def halfPerimeterApprox (n : ℕ) : ℝ :=
  (2 : ℝ) ^ (n + 1) * Real.sqrt (2 - 2 * (sequence n).core)

/--
半周長候補は次段階の面積候補に等しい：`P_n = A_(n+1)`。

`2-2c_n = 4((1-c_n)/2)` と平方根の非負性から、
`√(2-2c_n) = 2 s_(n+1)` を得る。
-/
theorem halfPerimeterApprox_eq_areaApprox_succ (n : ℕ) :
    halfPerimeterApprox n = areaApprox (n + 1) := by
  have h : 0 ≤ (1 - (sequence n).core) / 2 := by
    have := (sequence n).core_le_one
    linarith
  have hs := Real.sq_sqrt h
  have hr : 0 ≤ 2 - 2 * (sequence n).core := by linarith
  have ht := Real.sq_sqrt hr
  have ha := Real.sqrt_nonneg ((1 - (sequence n).core) / 2)
  have hb := Real.sqrt_nonneg (2 - 2 * (sequence n).core)
  have he : Real.sqrt (2 - 2 * (sequence n).core) =
      2 * Real.sqrt ((1 - (sequence n).core) / 2) := by nlinarith
  simp only [halfPerimeterApprox, areaApprox, QuadrantUnitKernel.sequence, half, beam, pow_succ]
  rw [he]
  ring

/--
初期核 `(0,1)` に対する面積候補は `A_0 = 2`。
-/
theorem areaApprox_zero : areaApprox 0 = 2 := by norm_num [areaApprox, QuadrantUnitKernel.sequence, initial, beam]

/--
一度二分した核に対する面積候補は `A_1 = 2√2`。
-/
theorem areaApprox_one : areaApprox 1 = 2 * Real.sqrt 2 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h' := Real.sq_sqrt (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  have hpos := Real.sqrt_nonneg 2
  have hpos' := Real.sqrt_nonneg (1 / 2)
  have he : 2 * Real.sqrt (1 / 2) = Real.sqrt 2 := by nlinarith
  change (2 : ℝ) ^ 2 * Real.sqrt ((1 - 0) / 2) = 2 * Real.sqrt 2
  norm_num only [sub_zero, pow_two]
  linarith

/--
初期段階の半周長候補は `P_0 = 2√2`。
-/
theorem halfPerimeterApprox_zero : halfPerimeterApprox 0 = 2 * Real.sqrt 2 := by
  rw [halfPerimeterApprox_eq_areaApprox_succ, areaApprox_one]

/--
二分核の合成の beam 座標から得る漸化式 `A_n = c_(n+1) A_(n+1)`。
-/
theorem areaApprox_eq_core_mul_succ (n : ℕ) :
    areaApprox n = (sequence (n + 1)).core * areaApprox (n + 1) := by
  have h := congrArg Vec.beam (sequence_star n)
  simp only [Vec.star_beam] at h
  change (sequence (n + 1)).core * (sequence (n + 1)).beam +
    (sequence (n + 1)).beam * (sequence (n + 1)).core = (sequence n).beam at h
  simp only [areaApprox, pow_succ]
  rw [← h]
  ring

/--
第一象限の beam が非負なので、面積候補も非負である。
-/
theorem areaApprox_nonneg (n : ℕ) : 0 ≤ areaApprox n := by
  exact mul_nonneg (pow_nonneg (by norm_num) _) (sequence n).beam_nonneg

/--
`c_(n+1) ≤ 1` と漸化式から、面積候補は単調非減少である。
-/
theorem areaApprox_monotone : Monotone areaApprox := by
  apply monotone_nat_of_le_succ
  intro n
  rw [areaApprox_eq_core_mul_succ]
  have hc := (sequence (n + 1)).core_le_one
  have ha := areaApprox_nonneg (n + 1)
  nlinarith


/--
二分核の定義から得る座標式 `c_(n+1)² = (1+c_n)/2`。
-/
theorem core_succ_sq (n : ℕ) :
    (sequence (n + 1)).core ^ 2 = (1 + (sequence n).core) / 2 := by
  change Real.sqrt ((1 + (sequence n).core) / 2) ^ 2 = _
  rw [Real.sq_sqrt (by have := (sequence n).core_nonneg; change 0 ≤ (sequence n).core at this; linarith)]

/--
二分後の core は正である。したがって外接候補の分母に使える。
-/
theorem core_succ_pos (n : ℕ) : 0 < (sequence (n + 1)).core := by
  have h := core_succ_sq n
  have hc := (sequence n).core_nonneg
  have hn := (sequence (n + 1)).core_nonneg
  change 0 ≤ (sequence n).core at hc
  change 0 ≤ (sequence (n + 1)).core at hn
  nlinarith

/--
上界のための代数的候補 `U_n = A_(n+1) / c_(n+1)`。分母は `core_succ_pos` により正。
-/
noncomputable def outerApprox (n : ℕ) : ℝ := areaApprox (n + 1) / (sequence (n + 1)).core

/--
外接候補 `U_n` は単調非増加。

分母の正性を使って分数の比較を積の比較に直す。漸化式と
`c_(n+2)² = (1+c_(n+1))/2` により、必要な不等式は `c_(n+1) ≤ 1` に帰着する。
-/
theorem outerApprox_antitone : Antitone outerApprox := by
  apply antitone_nat_of_succ_le
  intro n
  unfold outerApprox
  apply (div_le_div_iff₀ (core_succ_pos (n+1)) (core_succ_pos n)).2
  have hrec := areaApprox_eq_core_mul_succ (n+1)
  have hsq := core_succ_sq (n+1)
  have hc := (sequence (n+1)).core_le_one
  have ha := areaApprox_nonneg (n+2)
  have hle : (sequence (n+1)).core ≤ (sequence (n+2)).core ^ 2 := by
    convert (show (sequence (n+1)).core ≤ (1 + (sequence (n+1)).core) / 2 by linarith) using 1
  have hm := mul_le_mul_of_nonneg_left hle ha
  rw [hrec]
  nlinarith [hm]

/--
外接候補の初項は `U_0 = 4`。
-/
theorem outerApprox_zero : outerApprox 0 = 4 := by
  have hp := core_succ_pos 0
  have he : (QuadrantUnitKernel.sequence 1).beam = (QuadrantUnitKernel.sequence 1).core := by
    simp [QuadrantUnitKernel.sequence, half, core, beam, initial]
  unfold outerApprox areaApprox
  rw [he]
  have hn : (QuadrantUnitKernel.sequence 1).core ≠ 0 := ne_of_gt hp
  norm_num
  field_simp

/--
すべての `n` について `A_n ≤ 4`。

`A_n ≤ A_(n+1) ≤ U_n ≤ U_0 = 4` という純代数的な評価である。
-/
theorem areaApprox_le_four (n : ℕ) : areaApprox n ≤ 4 := by
  have ho := outerApprox_antitone (Nat.zero_le n)
  rw [outerApprox_zero] at ho
  have hp := core_succ_pos n
  have hc := (sequence (n+1)).core_le_one
  have ha := areaApprox_nonneg (n+1)
  have hrec := areaApprox_eq_core_mul_succ n
  have hdiv : areaApprox (n+1) ≤ outerApprox n := by
    unfold outerApprox
    apply (le_div_iff₀ hp).2
    nlinarith
  nlinarith

end DkMath.CosmicFormula.Rotation.CF2D
