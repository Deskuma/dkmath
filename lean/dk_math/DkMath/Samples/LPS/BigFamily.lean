import Mathlib

namespace DkMath
namespace Samples
namespace BigFamily

/--
`big d x u = (x + u)^d`

Big-family の第0層。完成全体を表す。
-/
def big (d x u : ℕ) : ℕ :=
  (x + u) ^ d

/--
`gap d x u = u^d`

Big-family の第2層。単位核・余白を表す。
-/
def gap (d _x u : ℕ) : ℕ :=
  u ^ d

/--
`body d x u = big d x u - gap d x u`

Big-family の第1層。Gap を除いた本体を表す。
-/
def body (d x u : ℕ) : ℕ :=
  big d x u - gap d x u

/--
`core d x u = x^d`

Big-family の第3層。Body の主核を表す。
-/
def core (d x _u : ℕ) : ℕ :=
  x ^ d

/--
`beam d x u = body d x u - core d x u`

Big-family の第4層。Body から Core を除いた残差を表す。
-/
def beam (d x u : ℕ) : ℕ :=
  body d x u - core d x u

/-- 展開確認用。 -/
@[simp] theorem big_def (d x u : ℕ) :
    big d x u = (x + u) ^ d := rfl

/-- 展開確認用。 -/
@[simp] theorem gap_def (d x u : ℕ) :
    gap d x u = u ^ d := rfl

/-- 展開確認用。 -/
@[simp] theorem body_def (d x u : ℕ) :
    body d x u = big d x u - gap d x u := rfl

/-- 展開確認用。 -/
@[simp] theorem core_def (d x u : ℕ) :
    core d x u = x ^ d := rfl

/-- 展開確認用。 -/
@[simp] theorem beam_def (d x u : ℕ) :
    beam d x u = body d x u - core d x u := rfl

/--
`gap ≤ big`

`u ≤ x + u` から `u^d ≤ (x+u)^d` を得る基本単調性。
-/
theorem gap_le_big (d x u : ℕ) :
    gap d x u ≤ big d x u := by
  unfold gap big
  exact Nat.pow_le_pow_left (Nat.le_add_left u x) d

/--
`core ≤ big`

`x ≤ x + u` から `x^d ≤ (x+u)^d` を得る基本単調性。
-/
theorem core_le_big (d x u : ℕ) :
    core d x u ≤ big d x u := by
  unfold core big
  exact Nat.pow_le_pow_left (Nat.le_add_right x u) d

/--
`body + gap = big`

Nat の切り捨て減算が実際には切り捨てを起こしていないことを
`gap ≤ big` で保証して戻す。
-/
theorem body_add_gap_eq_big (d x u : ℕ) :
    body d x u + gap d x u = big d x u := by
  unfold body
  exact Nat.sub_add_cancel (gap_le_big d x u)

/--
`beam + core = body`

`core ≤ body` が分かっている状況で、Body を `Core + Beam` に戻す。
-/
theorem beam_add_core_eq_body (d x u : ℕ)
    (h : core d x u ≤ body d x u) :
    beam d x u + core d x u = body d x u := by
  unfold beam
  exact Nat.sub_add_cancel h

/--
`core + beam = body`

加法の順序を設計書に合わせた版。
-/
theorem core_add_beam_eq_body (d x u : ℕ)
    (h : core d x u ≤ body d x u) :
    core d x u + beam d x u = body d x u := by
  rw [Nat.add_comm]
  exact beam_add_core_eq_body d x u h

/--
`big = body + gap`

設計書の基本関係式。
-/
theorem big_eq_body_add_gap (d x u : ℕ) :
    big d x u = body d x u + gap d x u := by
  unfold body
  exact (Nat.sub_add_cancel (gap_le_big d x u)).symm

/--
`big = core + beam + gap`

`core ≤ body` が分かっている状況での Big-family 全分解。
-/
theorem big_eq_core_add_beam_add_gap (d x u : ℕ)
    (h : core d x u ≤ body d x u) :
    big d x u = core d x u + beam d x u + gap d x u := by
  rw [big_eq_body_add_gap]
  rw [core_add_beam_eq_body d x u h]

/--
`body = big - gap` の別名として residual を導入するなら、
実際には residual は gap と一致する。
ここでは簡易版として `big - body` を residual と呼ぶ。
-/
def residual (d x u : ℕ) : ℕ :=
  big d x u - body d x u

/--
`residual = gap`

`body = big - gap` より、残差はちょうど gap に戻る。
-/
theorem residual_eq_gap (d x u : ℕ) :
    residual d x u = gap d x u := by
  unfold residual body
  rw [Nat.sub_sub_self (gap_le_big d x u)]

/-! ## 小さな確認例 -/

/-- `d = 2, x = 3, u = 1` の具体例。 -/
example : big 2 3 1 = 16 := by
  norm_num [big]

example : gap 2 3 1 = 1 := by
  norm_num [gap]

example : body 2 3 1 = 15 := by
  norm_num [body, big, gap]

example : core 2 3 1 = 9 := by
  norm_num [core]

example : beam 2 3 1 = 6 := by
  norm_num [beam, body, big, gap, core]

example : big 2 3 1 = core 2 3 1 + beam 2 3 1 + gap 2 3 1 := by
  norm_num [big, body, gap, core, beam]

end BigFamily
end Samples
end DkMath
