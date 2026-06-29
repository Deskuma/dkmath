# Git diff / Report / Review

## Add: Analysis.DkReal.PowBound

gch: 011c3962cbe75f5c5516ff0899943ac0b55f14a3

## Report

最新レビューの本丸まで実装しました。

新規 [PowBound.lean](/lean/dk_math/DkMath/Analysis/DkReal/PowBound.lean) に以下を追加:

- `gapGN_nonneg_of_nonneg`
- `gapGN_le_of_nonneg_of_le`
- 初期上端による base・width の評価
- `gapGN_bounded_on_nonnegative_nested`
- 無条件の計算可能冪写像 `DkReal.powNonneg`

上界には閉形式 `(2^d - 1)b₀^(d-1)` ではなく、有限和と直接対応する `gapGN d b₀ b₀` を採用しています。

検証済みです。

```text
lake build DkMath.Analysis.DkReal.PowBound
lake build DkMath.Analysis DkMath
git diff --check
```

すべて成功し、`DkReal` 側に `noncomputable` はありません。

## Review

## 1. 総評

うむ、これは **本丸突破** じゃ。
今回の `PowBound.lean` によって、前回まで条件付きだった `DkReal.powNonnegOfGapGNBounded` が、実用上の無条件写像 `DkReal.powNonneg` へ昇格しておる。

設計書では、`DkMath.Analysis` の核を Gap / Body / GN とし、第一原理を \((u+\delta)^d-u^d\) と \(\delta,GapGN_d(u,\delta)\) の対応に置いていた。さらに Route B では、標準実数全体の再構成ではなく、まず有理区間近似と幅評価を閉じる方針だった。
今回の差分は、まさにこの Route B の「非負冪写像」を閉じたものじゃ。

判定は **合格** 。
しかも、かなり綺麗に閉じておる。

## 2. 今回閉じた数学

`DkReal` は有理区間列で実数を近似する。

$$
I_n=[a_n,b_n]
$$

入れ子条件により、後の区間ほど狭くなる。

$$
I_{n+1}\subseteq I_n
$$

そして幅が 0 に近づく。

$$
w_n=b_n-a_n\to0
$$

非負の場合、冪写像は区間ごとにこう扱える。

$$
[a_n,b_n]\mapsto[a_n^d,b_n^d]
$$

問題は、新しい幅が 0 に近づくかどうかじゃ。

新しい幅は、

$$
b_n^d-a_n^d
$$

ここで \(b_n=a_n+w_n\) なので、

$$
b_n^d-a_n^d=(a_n+w_n)^d-a_n^d=w_n,gapGN_d(a_n,w_n)
$$

となる。つまり、元の幅 \(w_n\) は 0 に行くので、残りは \(gapGN_d(a_n,w_n)\) が一様に有界であればよい。

今回の実装は、この有界性を有限和の単調性で証明した。ここが大きい。

## 3. `gapGN_nonneg_of_nonneg`

```lean
theorem gapGN_nonneg_of_nonneg
    (d : ℕ) {base delta : ℚ} (hbase : 0 ≤ base) (hdelta : 0 ≤ delta) :
    0 ≤ gapGN d base delta
```

これは基礎補題として正しい。

`gapGN` は有限和展開では、非負係数と非負冪の和になる。したがって `base` と `delta` が非負なら `gapGN` も非負。
実装では `GN_eq_sum` に開いて `positivity` で閉じている。これは Lean 的にも自然じゃ。

設計書でも `gapGN` は既存 `GN` への wrapper とし、有限多項式的な差分補正核として扱う方針だった。
この補題はその有限和性を順序評価へ使う第一歩じゃ。

## 4. `gapGN_le_of_nonneg_of_le`

```lean
theorem gapGN_le_of_nonneg_of_le
    (d : ℕ) {base₁ base₂ delta₁ delta₂ : ℚ}
    (hbase₁ : 0 ≤ base₁) (hbase : base₁ ≤ base₂)
    (hdelta₁ : 0 ≤ delta₁) (hdelta : delta₁ ≤ delta₂) :
    gapGN d base₁ delta₁ ≤ gapGN d base₂ delta₂
```

これは今回の中核補題じゃ。

数学的には、非負領域では `gapGN` は `base` と `delta` の両方について単調。
なぜなら有限和の各項が、非負係数つきの単項式だからじゃ。

Lean 実装では `GN_eq_sum` に開いて、`Finset.sum_le_sum` と `gcongr` で項別比較している。これはかなり良い。
閉形式 \((2^d-1)b_0^{d-1}\) に急がず、有限和の形のまま比較した判断も良い。証明が `GN_eq_sum` と直結するからじゃ。

## 5. 初期上端による評価

今回の構造はこうじゃ。

```lean
lo_le_initial_hi
width_le_initial_hi
gapGN_le_initial_hi
```

まず、

$$
a_n\le b_0
$$

を示す。これは、\(a_n\le b_n\) と \(b_n\le b_0\) から出る。

次に、非負性から、

$$
w_n=b_n-a_n\le b_n\le b_0
$$

を示す。

すると、非負単調性により、

$$
gapGN_d(a_n,w_n)\le gapGN_d(b_0,b_0)
$$

が出る。

ここで上界を \(gapGN_d(b_0,b_0)\) にしたのは良い。
閉形式へ正規化すると、別の補題や二項和評価が必要になる。今の段階では、有限和の姿を保ったまま上界にするほうが Lean で堅い。

## 6. `gapGN_bounded_on_nonnegative_nested`

```lean
theorem gapGN_bounded_on_nonnegative_nested
    (d : ℕ) (x : DkMath.Analysis.DkReal) (hx : Nonnegative x) :
    Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (norm ∘ fun n =>
        gapGN d (x.interval n).lo (x.interval n).width)
```

これは前回残っていた壁そのものじゃ。

前回までに、powered width は

$$
w_n,gapGN_d(a_n,w_n)
$$

と分解されていた。`w_n` は 0 に収束する。
今回 `gapGN` 側が有界だと示せたので、powered width も 0 に収束する。

実装では `norm` を経由して `IsBoundedUnder` を作っている。`gapGN_nonneg_of_nonneg` によって絶対値を外し、`gapGN_le_initial_hi` へ落とす流れも正しい。

細かく見ると、

```lean
have hhi0 : 0 ≤ (x.interval 0).hi :=
  (hx 0).trans (x.interval 0).le_lo_hi
```

は `gapGN_le_initial_hi` 内では直接使っていないように見える。build 成功なら害は薄いが、linter を厳しくするなら削ってよい候補じゃ。

## 7. `DkReal.powNonneg` の完成

```lean
def powNonneg
    (d : ℕ) (x : DkMath.Analysis.DkReal) (hx : Nonnegative x) :
    DkMath.Analysis.DkReal :=
  powNonnegOfGapGNBounded d x hx
    (gapGN_bounded_on_nonnegative_nested d x hx)
```

これは素晴らしい。
前回の条件付き写像に、今回の有界性補題を差し込んで、ついに非負 `DkReal` の自然数冪写像が完成しておる。

しかも `DkReal` 側に `noncomputable` が入っていない。
これは Route B の大きな成果じゃ。

DkReal の思想は、標準実数全体を最初から持つのではなく、観測可能な近似と、その間を埋める補正核を持つ計算可能体として読むことだった。
今回の `powNonneg` は、その思想にかなり忠実じゃ。

## 8. 状況理解

今の段階を一言で言うと、こうじゃ。

$$
\boxed{\text{非負 }DkReal\text{ は自然数冪で閉じる}}
$$

もう少し構造的には、こうじゃ。

```text
DkReal x
  有理区間列 Iₙ = [aₙ, bₙ]
  幅 wₙ = bₙ - aₙ
  wₙ → 0

非負条件
  0 ≤ aₙ

冪写像
  Iₙ ↦ [aₙ^d, bₙ^d]

powered width
  bₙ^d - aₙ^d = wₙ * gapGN d aₙ wₙ

入れ子性
  powered intervals も入れ子

幅収束
  wₙ → 0
  gapGN d aₙ wₙ は有界
  よって powered width → 0

結論
  powNonneg d x hx は DkReal
```

これはかなり美しいぞい。
`gapGN` は単なる差分補正項ではなく、DkReal の演算閉性を支える **幅伝播制御核** になった。

## 9. 設計との整合性

設計書では、最初に `GapInterval` と幅評価を作り、その後 `DkReal` を入れ子区間列として定義する方針だった。さらに `DkReal → ℝ` の意味論写像は `noncomputable` になる可能性が高いため、初期実装では区間演算と幅評価を先に閉じる、とされていた。

今回の実装はその方針に完全に沿っておる。

```text
標準 ℝ へ行かない
有理区間だけで閉じる
幅評価で演算閉性を示す
GN を誤差補正核として使う
```

この四点が揃った。

## 10. 次に足すとよいもの

次は小さな API 整備が良い。

まず、非負有理数の冪について、埋め込みとの整合性が欲しい。

```lean
@[simp]
theorem powNonneg_ofRat
    (d : ℕ) {q : ℚ} (hq : 0 ≤ q) :
    powNonneg d (DkReal.ofRat q) (nonnegative_ofRat hq)
      = DkReal.ofRat (q ^ d)
```

ただし `DkReal` の等号は構造体の関数等号を要求するので、最初は interval 版が現実的じゃ。

```lean
@[simp]
theorem powNonneg_ofRat_interval
    (d : ℕ) {q : ℚ} (hq : 0 ≤ q) (n : ℕ) :
    (powNonneg d (DkReal.ofRat q) (nonnegative_ofRat hq)).interval n
      = GapInterval.singleton (q ^ d)
```

次に、指数 0 と 1 の簡約。

```lean
@[simp]
theorem powNonneg_zero_interval
@[simp]
theorem powNonneg_one_interval
```

さらに、将来の代数構造へ進むなら、`mul` と `add` の区間演算が欲しい。
ただし加算・乗算は負区間をどう扱うかで分岐が増えるので、次はまず `Nonnegative` 領域の演算に限定するのがよい。

## 11. 小さな注意点

`gapGN_le_initial_hi` の上界は \(gapGN_d(b_0,b_0)\) なので、初期上端 \(b_0\) が非負であることが暗黙に必要じゃ。`hx 0` と `le_lo_hi` からそれは出ている。
ただ、`gapGN_le_initial_hi` 内の `hhi0` が未使用なら、削るか、明示的に `gapGN_le_of_nonneg_of_le` の上側非負補助として使える形へ整理してもよい。

また、今後 `norm` 周りで証明が重くなるなら、`gapGN` が非負である区間では `norm` つき有界性を作る小補題を独立させると楽になる。

## 12. 最終判定

今回の差分は **合格、しかも節目として大きい** じゃ。

```text
PowBound.lean
  gapGN の非負性と単調性を有限和で証明

gapGN_le_initial_hi
  入れ子区間の初期上端で一様評価

gapGN_bounded_on_nonnegative_nested
  powered width 収束に必要な boundedness を解決

powNonneg
  非負 DkReal の自然数冪写像が完成
```

これで `DkReal` は、少なくとも非負領域では自然数冪に対して閉じた。
わっちの評価では、これは `DkMath.Analysis.DkReal` の第一の実質的演算成功じゃ。

次の山は、`powNonneg` の基本簡約と、非負 `DkReal` の加算・乗算じゃな。
良いぞ、D.。ここまで来ると、DkReal はもう「構想」ではない。小麦の芽が、ちゃんと演算という茎を伸ばし始めておる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index 6185d04d..da9581f0 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -7,6 +7,7 @@ Authors: D. and Wise Wolf.
 import DkMath.Analysis.DkReal.Interval
 import DkMath.Analysis.DkReal.Basic
 import DkMath.Analysis.DkReal.Pow
+import DkMath.Analysis.DkReal.PowBound
 
 #print "file: DkMath.Analysis.DkReal"
 
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/PowBound.lean b/lean/dk_math/DkMath/Analysis/DkReal/PowBound.lean
new file mode 100644
index 00000000..d4862516
--- /dev/null
+++ b/lean/dk_math/DkMath/Analysis/DkReal/PowBound.lean
@@ -0,0 +1,108 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Analysis.DkReal.Pow
+
+#print "file: DkMath.Analysis.DkReal.PowBound"
+
+/-!
+# Bounds for nonnegative DkReal power approximations
+
+This file proves that the exact `gapGN` factors occurring in a nested
+nonnegative rational interval sequence are uniformly bounded.
+
+The proof uses the finite binomial-tail expansion. It does not appeal to real
+analysis or a mean-value theorem.
+-/
+
+namespace DkMath.Analysis.DkReal
+
+/-- `gapGN` is nonnegative when both its base and increment are nonnegative. -/
+theorem gapGN_nonneg_of_nonneg
+    (d : ℕ) {base delta : ℚ} (hbase : 0 ≤ base) (hdelta : 0 ≤ delta) :
+    0 ≤ gapGN d base delta := by
+  rw [gapGN_eq_GN, DkMath.CosmicFormulaBinom.GN_eq_sum]
+  positivity
+
+/--
+On the nonnegative quadrant, `gapGN` is monotone in both the base and the
+increment.
+-/
+theorem gapGN_le_of_nonneg_of_le
+    (d : ℕ) {base₁ base₂ delta₁ delta₂ : ℚ}
+    (hbase₁ : 0 ≤ base₁) (hbase : base₁ ≤ base₂)
+    (hdelta₁ : 0 ≤ delta₁) (hdelta : delta₁ ≤ delta₂) :
+    gapGN d base₁ delta₁ ≤ gapGN d base₂ delta₂ := by
+  have hbase₂ : 0 ≤ base₂ := hbase₁.trans hbase
+  have hdelta₂ : 0 ≤ delta₂ := hdelta₁.trans hdelta
+  rw [gapGN_eq_GN, gapGN_eq_GN,
+    DkMath.CosmicFormulaBinom.GN_eq_sum,
+    DkMath.CosmicFormulaBinom.GN_eq_sum]
+  apply Finset.sum_le_sum
+  intro k hk
+  gcongr
+
+/-- Every lower endpoint is bounded above by the initial upper endpoint. -/
+theorem lo_le_initial_hi
+    (x : DkMath.Analysis.DkReal) (n : ℕ) :
+    (x.interval n).lo ≤ (x.interval 0).hi := by
+  exact (x.interval n).le_lo_hi.trans (x.hi_antitone (Nat.zero_le n))
+
+/-- Every interval width is bounded above by the initial upper endpoint when `x` is nonnegative. -/
+theorem width_le_initial_hi
+    (x : DkMath.Analysis.DkReal) (hx : Nonnegative x) (n : ℕ) :
+    (x.interval n).width ≤ (x.interval 0).hi := by
+  calc
+    (x.interval n).width
+        = (x.interval n).hi - (x.interval n).lo := rfl
+    _ ≤ (x.interval n).hi := sub_le_self _ (hx n)
+    _ ≤ (x.interval 0).hi := x.hi_antitone (Nat.zero_le n)
+
+/--
+Uniform pointwise bound for the `gapGN` factors along a nested nonnegative
+approximation.
+-/
+theorem gapGN_le_initial_hi
+    (d : ℕ) (x : DkMath.Analysis.DkReal) (hx : Nonnegative x) (n : ℕ) :
+    gapGN d (x.interval n).lo (x.interval n).width
+      ≤ gapGN d (x.interval 0).hi (x.interval 0).hi := by
+  have hhi0 : 0 ≤ (x.interval 0).hi :=
+    (hx 0).trans (x.interval 0).le_lo_hi
+  exact gapGN_le_of_nonneg_of_le d
+    (hx n) (lo_le_initial_hi x n)
+    (x.interval n).width_nonneg (width_le_initial_hi x hx n)
+
+/-- The `gapGN` sequence along a nested nonnegative approximation is uniformly bounded. -/
+theorem gapGN_bounded_on_nonnegative_nested
+    (d : ℕ) (x : DkMath.Analysis.DkReal) (hx : Nonnegative x) :
+    Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
+      (norm ∘ fun n =>
+        gapGN d (x.interval n).lo (x.interval n).width) := by
+  apply Filter.isBoundedUnder_of_eventually_le
+    (a := ((gapGN (R := ℚ) d (x.interval 0).hi (x.interval 0).hi : ℚ) : ℝ))
+  filter_upwards
+  intro n
+  have hnonneg :
+      0 ≤ gapGN d (x.interval n).lo (x.interval n).width :=
+    gapGN_nonneg_of_nonneg d (hx n) (x.interval n).width_nonneg
+  rw [Function.comp_apply, ← Rat.norm_cast_real, Real.norm_eq_abs,
+    abs_of_nonneg (Rat.cast_nonneg.mpr hnonneg)]
+  exact_mod_cast gapGN_le_initial_hi d x hx n
+
+/-- Natural powers of nonnegative `DkReal` approximations form a `DkReal`. -/
+def powNonneg
+    (d : ℕ) (x : DkMath.Analysis.DkReal) (hx : Nonnegative x) :
+    DkMath.Analysis.DkReal :=
+  powNonnegOfGapGNBounded d x hx
+    (gapGN_bounded_on_nonnegative_nested d x hx)
+
+/-- The intervals of `powNonneg` are the pointwise powered intervals. -/
+@[simp]
+theorem powNonneg_interval
+    (d : ℕ) (x : DkMath.Analysis.DkReal) (hx : Nonnegative x) (n : ℕ) :
+    (powNonneg d x hx).interval n = powNonnegApprox d x hx n := rfl
+
+end DkMath.Analysis.DkReal
diff --git a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
index bdfc8bb5..0f1f2949 100644
--- a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
+++ b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
@@ -50,6 +50,9 @@ DkMath.Analysis.DkReal.Basic
 DkMath.Analysis.DkReal.Pow
   computable pointwise power approximations for nonnegative DkReal values
 
+DkMath.Analysis.DkReal.PowBound
+  finite-sum gapGN bounds and the completed nonnegative power map
+
 DkMath.Analysis.DkReal
   public entry point for the computable approximation layer
 ```
@@ -287,16 +290,41 @@ and therefore constructs a completed powered value:
 DkReal.powNonnegOfGapGNBounded
 ```
 
-The remaining unconditional-power obligation is now isolated to one statement:
-prove that the sequence
+The finite-sum layer now proves that the sequence
 
 ```text
 gapGN d (lower endpoint at n) (width at n)
 ```
 
-is bounded for a nested nonnegative `DkReal`. This should be implemented as a
-separate finite-polynomial bound rather than folded into the interval
-construction.
+is bounded for a nested nonnegative `DkReal`.
+
+The proof proceeds through:
+
+```lean
+DkReal.gapGN_nonneg_of_nonneg
+DkReal.gapGN_le_of_nonneg_of_le
+DkReal.gapGN_le_initial_hi
+DkReal.gapGN_bounded_on_nonnegative_nested
+```
+
+The uniform upper bound is the exact rational value
+
+```text
+gapGN d initialUpperEndpoint initialUpperEndpoint
+```
+
+rather than a prematurely normalized closed form. This keeps the proof directly
+aligned with the finite `GN_eq_sum` expansion.
+
+Combining this bound with the conditional constructor yields the completed,
+computable map:
+
+```lean
+DkReal.powNonneg
+```
+
+Thus natural powers of nonnegative nested rational approximations are again
+`DkReal` values, with no `noncomputable` declaration in the DkReal layer.
 
 `TaylorBridge` and `RealBridge` may use noncomputable real-number operations.
 The `DkReal` files remain computational and use rational interval data only.
````
`````
