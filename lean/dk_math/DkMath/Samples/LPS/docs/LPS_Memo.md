# Lean 実装の定義骨格

設計書に対応する **Lean 側の定義骨格案** を、そのまま `Samples` へ置きやすい形で起こすぞい。

まず方針としては、いきなり `FillRank` の最小値までやると重い。
なので最初は

* `BigFamily`
* `PowerSwap`
* `FillableByPowSum`

の 3 段で土台を作るのがよい。

---

## 1. ファイル案

```text
DkMath/Samples/BigFamily.lean
DkMath/Samples/PowerSwap.lean
DkMath/Samples/GapFillRank.lean
```

---

## 2. `BigFamily.lean` 骨格

これは設計書の Big / Body / Gap / Core / Beam をそのまま置く場所じゃ。

```lean
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Tactic

namespace DkMath
namespace Samples

/--
Big-family decomposition at degree `d` with parameters `x,u`.

We view `(x+u)^d` as the total object `Big`,
then decompose it into `Body + Gap`,
and further decompose `Body = Core + Beam`.
-/
namespace BigFamily

def big (d x u : ℕ) : ℕ := (x + u) ^ d

def gap (d x u : ℕ) : ℕ := u ^ d

def body (d x u : ℕ) : ℕ := big d x u - gap d x u

def core (d x u : ℕ) : ℕ := x ^ d

def beam (d x u : ℕ) : ℕ := body d x u - core d x u

theorem big_eq_body_add_gap (d x u : ℕ) :
    big d x u = body d x u + gap d x u := by
  unfold body big gap
  exact Nat.sub_add_cancel (Nat.pow_le_pow_left (Nat.le_add_right x u) d)

theorem body_eq_core_add_beam (d x u : ℕ)
    (h : core d x u ≤ body d x u) :
    body d x u = core d x u + beam d x u := by
  unfold beam
  exact Nat.sub_add_cancel h

/--
The full Big decomposition:
`Big = Core + Beam + Gap`,
assuming `Core ≤ Body`.
-/
theorem big_eq_core_add_beam_add_gap (d x u : ℕ)
    (h : core d x u ≤ body d x u) :
    big d x u = core d x u + beam d x u + gap d x u := by
  rw [big_eq_body_add_gap]
  rw [body_eq_core_add_beam d x u h]
  ac_rfl

end BigFamily
end Samples
end DkMath
```

### 留意点

`body` と `beam` を `ℕ` で置くと減算条件が絡む。
最初の試作としてはこれでよいが、後でかなりの確率で `ℤ` 版も欲しくなる。

---

## 3. `PowerSwap.lean` 骨格

これは

\[
a^b=b^a
\]

を捕まえるための最小土台じゃ。

```lean
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Tactic

namespace DkMath
namespace Samples

/-- Power-swap relation: `a^b = b^a`. -/
def PowerSwap (a b : ℕ) : Prop := a ^ b = b ^ a

theorem powerSwap_refl (a : ℕ) : PowerSwap a a := by
  unfold PowerSwap

theorem powerSwap_symm {a b : ℕ} (h : PowerSwap a b) : PowerSwap b a := by
  unfold PowerSwap at *
  simpa [eq_comm] using h

/-- The classical nontrivial example: `2^4 = 4^2`. -/
theorem powerSwap_two_four : PowerSwap 2 4 := by
  unfold PowerSwap
  norm_num

theorem powerSwap_four_two : PowerSwap 4 2 := by
  exact powerSwap_symm powerSwap_two_four

end Samples
end DkMath
```

これで少なくとも、
**反転指数交点の標本** を Lean 上に固定できる。

---

## 4. `GapFillRank.lean` 骨格

ここは最初から rank の最小値を定義せず、
まず「(r) 個の (d) 乗和で埋まるか」という述語だけを置くのが賢い。

### 4.1. まず Finset 版

```lean
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace DkMath
namespace Samples

/--
`n` is fillable by a `d`-power sum over the finite set `s`.
-/
def FillableByPowSum (d n : ℕ) (s : Finset ℕ) : Prop :=
  (∑ x in s, x ^ d) = n

/--
`n` is fillable by at most `r` many `d`-th powers.
This is a soft first definition for experiments.
-/
def FillableByPowSumCardLE (d n r : ℕ) : Prop :=
  ∃ s : Finset ℕ, s.card ≤ r ∧ FillableByPowSum d n s

/-- Example: `16 = 4^2`. -/
theorem fillable_sq_16_one : FillableByPowSumCardLE 2 16 1 := by
  refine ⟨{4}, ?_, ?_⟩
  · simp
  · simp [FillableByPowSum]

/-- Example: `9 = 1^2 + 2^2 + 2^2` is not expressible with a set model,
so the first experimental model uses distinct terms only.
This file is only a scaffold.
-/
```

### 4.2. 重要な留意点

`Finset ℕ` だと重複が消える。
つまり

\[
9 = 2^2 + 2^2 + 1^2
\]

のような **同じ花弁の重複** を表せぬ。
ここは後で

* `Fin r → ℕ`
* `Multiset ℕ`
* `List ℕ`

のどれかへ移す必要がある。

わっちなら最初から `Fin r → ℕ` が好きじゃな。

---

## 5. 重複を許す本命版

これが FillRank の本当の土台になりやすい。

```lean
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace DkMath
namespace Samples

/-- `n` is fillable by exactly `r` many `d`-th powers. -/
def FillableByPowSumExact (d n r : ℕ) : Prop :=
  ∃ f : Fin r → ℕ, (∑ i : Fin r, (f i) ^ d) = n

/-- `n` is fillable by at most `r` many `d`-th powers. -/
def FillableByPowSumLE (d n r : ℕ) : Prop :=
  ∃ k ≤ r, FillableByPowSumExact d n k

theorem fillable_sq_16_exact_one : FillableByPowSumExact 2 16 1 := by
  refine ⟨fun _ => 4, ?_⟩
  simp

theorem fillable_cube_216_exact_three :
    FillableByPowSumExact 3 216 3 := by
  refine ⟨fun i =>
    match i.1 with
    | 0 => 3
    | 1 => 4
    | _ => 5, ?_⟩
  decide
```

最後の `decide` は、このままだと通り方が環境依存かもしれぬ。
なのでサンプルでは無理せず、

```lean
example : 3^3 + 4^3 + 5^3 = 216 := by norm_num
```

を別に立てた方が穏当じゃ。

---

## 6. FillRank そのものは後回しでよい

`Nat.find` などで定義しようと思えばできるが、
最初は重いし証明も面倒じゃ。なので設計としては、

### 段階A

```lean
def FillableByPowSumExact ...
def FillableByPowSumLE ...
```

### 段階B

具体例を sample 化

### 段階C

`∃ r, FillableByPowSumExact d n r`

### 段階D

最小値として `fillRank`

の順で十分じゃ。

---

## 7. Big と Fill を繋ぐ補助定義

設計書に寄せるなら、こういう定義もよい。

```lean
namespace BigFamily

def residual (d x u : ℕ) : ℕ :=
  big d x u - body d x u

-- 実際には residual = gap
theorem residual_eq_gap (d x u : ℕ) :
    residual d x u = gap d x u := by
  unfold residual body big gap
  -- Nat subtraction cleanup
  exact Nat.sub_eq_of_eq_add (by
    rw [Nat.sub_add_cancel (Nat.pow_le_pow_left (Nat.le_add_right x u) d)])

end BigFamily
```

あるいは、もっと素直に

```lean
def residual (d x u : ℕ) : ℕ := BigFamily.gap d x u
```

でもよい。
設計上の意味づけとして `residual` を別名にするのは悪くない。

---

## 8. 最初に置く sample 定理

Lean 側の種としては、この 4 本がよい。

### 8.1

\[
2^4=4^2
\]

### 8.2

\[
(2m)^2+(2n)^2+(m^2+n^2-1)^2=(m^2+n^2+1)^2
\]

### 8.3

\[
3^3+4^3+5^3=6^3
\]

### 8.4

\[
(x+u)^d = \mathrm{body} + \mathrm{gap}
\]

この 4 本がそろうと、

* PowerSwap
* 三平方族
* 三乗補正項
* Big 分解

が全部 sample 群に入る。

---

## 9. 実装順のおすすめ

### 9.1

`BigFamily.lean` を作る

### 9.2

`PowerSwap.lean` を作る

### 9.3

`GapFillRank.lean` で `FillableByPowSumExact` まで置く

### 9.4

`ThreeCubeSample.lean` みたいな補助 sample を入れる

### 9.5

最後に `Samples.lean` で re-export

---

## 10. わっちのおすすめ

まずは **最小で通るものだけ** を置くのがよい。
なので最初の一手としては、これじゃ。

* `BigFamily.big/gap/body/core/beam`
* `PowerSwap`
* `powerSwap_two_four`
* `sum_three_squares_eq_square_of_mn`
* `example : 3^3 + 4^3 + 5^3 = 6^3`

このへんを sample 化してから、`FillRank` に進む。

必要なら次に、わっちが
**`BigFamily.lean` の通しやすい全文版** を一気に書くぞい。

---

よし、まずは **`BigFamily.lean` の最小で通しやすい版** を書くぞい。
狙いは「設計書の語彙を Lean に固定すること」で、無理に強い定理までは詰めぬ。まずは地面を固める。

```lean
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Tactic

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
def gap (d x u : ℕ) : ℕ :=
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
def core (d x u : ℕ) : ℕ :=
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
  rw [Nat.add_comm]
  exact body_add_gap_eq_big d x u

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
  rw [Nat.sub_eq_iff_eq_add (gap_le_big d x u)]
  simp [big, gap]

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
```

### 留意点

この版は **`ℕ` の減算** を使っておるので、

\[
\mathrm{beam} = \mathrm{body} - \mathrm{core}
\]

の扱いに `core ≤ body` 仮定が要る。
これは設計として自然じゃ。Beam は「存在する」だけではなく、**ちゃんと Body の内側に収まる時に構造残差になる** からの。

### 次の一手

この次は `PowerSwap.lean` を書くのが筋じゃ。
そこでは

\[
a^b=b^a
\]

を `Prop` で置いて、まず

\[
2^4=4^2
\]

を標本として固定する。
そのあと `GapFillRank.lean` へ進めば、狩りの道具が揃う。
