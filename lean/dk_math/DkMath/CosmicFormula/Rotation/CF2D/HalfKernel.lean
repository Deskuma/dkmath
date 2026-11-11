import DkMath.CosmicFormula.Rotation.CF2D.Basic

/-!
# 第一象限の単位核と二分

`q2 (c,s) = c² + s² = 1` を満たし、両座標が非負である核を扱う。
初期核 `(0,1)` に対し、核 `(c,s)` の二分を
`(√((1+c)/2), √((1-c)/2))` と定める。両成分の平方の和は 1 であり、
二分核を `Vec.star` で自分自身に作用させると元の核に戻る。

第２成分の一致には符号の情報が必要である。平方だけが等しい段階では正負の枝を
区別できないため、元の beam と平方根の積が非負であることを使って等式を得る。
このファイルの構成には角度や三角関数を使わない。
-/
namespace DkMath.CosmicFormula.Rotation.CF2D

/--
`UnitKernel ℝ` に core と beam の非負性を備えた第一象限の単位核。
-/
structure QuadrantUnitKernel where
  kernel : UnitKernel ℝ
  core_nonneg : 0 ≤ kernel.val.core
  beam_nonneg : 0 ≤ kernel.val.beam

namespace QuadrantUnitKernel

/--
第一象限の単位核の第１座標。
-/
def core (u : QuadrantUnitKernel) : ℝ := u.kernel.val.core
/--
第一象限の単位核の第２座標。
-/
def beam (u : QuadrantUnitKernel) : ℝ := u.kernel.val.beam

/--
単位核の保存量を座標で書いた式 `core² + beam² = 1`。
-/
theorem norm (u : QuadrantUnitKernel) : u.core ^ 2 + u.beam ^ 2 = 1 := u.kernel.q2_eq_one

/--
第一象限の単位核では `core ≤ 1`。平方根の被開平数の非負性に用いる。
-/
theorem core_le_one (u : QuadrantUnitKernel) : u.core ≤ 1 := by
  have := u.norm
  have := u.core_nonneg
  have := sq_nonneg u.beam
  dsimp [core] at *
  nlinarith

/--
二分反復の初期核 `(0,1)`。その二乗和は 1 である。
-/
def initial : QuadrantUnitKernel :=
  ⟨⟨⟨0, 1⟩, by norm_num [Vec.q2]⟩, by norm_num, by norm_num⟩

/--
非負平方根を選んだ二分核。二つの座標の平方の和が 1 なので再び第一象限の単位核になる。
-/
noncomputable def half (u : QuadrantUnitKernel) : QuadrantUnitKernel := by
  have h : 0 ≤ (1 - u.core) / 2 := by have := u.core_le_one; linarith
  refine ⟨⟨⟨Real.sqrt ((1 + u.core) / 2), Real.sqrt ((1 - u.core) / 2)⟩, ?_⟩,
    Real.sqrt_nonneg _, Real.sqrt_nonneg _⟩
  change Real.sqrt ((1 + u.core) / 2) ^ 2 + Real.sqrt ((1 - u.core) / 2) ^ 2 = 1
  rw [Real.sq_sqrt (by have := u.core_nonneg; dsimp [core] at *; linarith), Real.sq_sqrt h]
  ring

/--
二分核を二回合成すると元の核になる。

core は平方根の平方の差から得られる。beam はまず平方が一致することを示し、
両辺の非負性から符号を確定する。第一象限という条件がここで本質的である。
-/
theorem half_star (u : QuadrantUnitKernel) :
    Vec.star (half u).kernel.val (half u).kernel.val = u.kernel.val := by
  have hc : 0 ≤ (1 + u.core) / 2 := by have := u.core_nonneg; dsimp [core] at *; linarith
  have hs : 0 ≤ (1 - u.core) / 2 := by have := u.core_le_one; linarith
  have h1 := Real.sq_sqrt hc
  have h2 := Real.sq_sqrt hs
  have hn := u.norm
  have hb := u.beam_nonneg
  have hp : 0 ≤ Real.sqrt ((1 + u.core) / 2) * Real.sqrt ((1 - u.core) / 2) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsq : (2 * (Real.sqrt ((1 + u.core) / 2) * Real.sqrt ((1 - u.core) / 2))) ^ 2 = u.beam ^ 2 := by
    calc
      _ = 4 * (Real.sqrt ((1 + u.core) / 2) ^ 2) * (Real.sqrt ((1 - u.core) / 2) ^ 2) := by ring
      _ = u.beam ^ 2 := by rw [h1, h2]; nlinarith [hn]
  have he : 2 * (Real.sqrt ((1 + u.core) / 2) * Real.sqrt ((1 - u.core) / 2)) = u.beam := by
    change 0 ≤ u.beam at hb
    nlinarith
  cases hv : u.kernel.val with
  | mk c s =>
    simp only [Vec.star, half, core, beam, hv] at *
    congr 1 <;> nlinarith

/--
`sequence 0 = initial`、`sequence (n+1) = half (sequence n)` で定まる核列。
各項は型により二乗和 1 と第一象限の条件を備える。
-/
noncomputable def sequence : ℕ → QuadrantUnitKernel
  | 0 => initial
  | n + 1 => half (sequence n)

/--
反復列の隣接項は `u_(n+1) ⋆ u_(n+1) = u_n` を満たす。
-/
theorem sequence_star (n : ℕ) :
    Vec.star (sequence (n+1)).kernel.val (sequence (n+1)).kernel.val = (sequence n).kernel.val :=
  half_star _

end QuadrantUnitKernel
end DkMath.CosmicFormula.Rotation.CF2D
