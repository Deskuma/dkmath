# Git diff / Report / Review

## Upd: Analysis, fix namespace

gch: f8fa5b20826ecb4a2c9432c0299ddf8c233ffa67

## Report

レビュー指摘を現環境で検証し、次の段階を実装しました。

- `GapInterval` を `DkMath.Analysis.DkReal.GapInterval` に整理
- [DkReal/Basic.lean](/lean/dk_math/DkMath/Analysis/DkReal/Basic.lean) を追加
  - 入れ子有理区間列
  - 幅のゼロ収束
  - 区間包含
  - `DkReal.ofRat`
- [DkReal.lean](/lean/dk_math/DkMath/Analysis/DkReal.lean) を公開入口として追加
- 文書に `RealBridge` は連続性までの第一段階と明記

検証結果:

```text
lake build DkMath.Analysis DkMath
git diff --check
```

すべて成功しています。次は独立した `TaylorBridge.lean` が自然です。

## Review

## 1. 総評

うむ、これは **前回レビュー指摘への良い修正** じゃ。

今回の差分は、設計書の Route B、つまり `DkReal / GapReal` 側に一歩入った実装になっておる。設計書では、まず `GapInterval` から始め、次に入れ子区間列として `DkReal` を定義し、`eval : DkReal → ℝ` は後回しにする方針だった。
今回の実装はその通り、

```lean
DkReal.GapInterval
DkReal
DkReal.ofRat
```

までを閉じておる。かなり筋が良い。

判定は **合格** じゃ。

## 2. 良い点

まず、`GapInterval` を

```lean
namespace DkMath.Analysis.DkReal
```

へ移したのは正しい。前回の懸念だった「ファイルは `DkReal/Interval.lean` なのに namespace は `DkMath.Analysis`」というズレが消えた。

これにより、名前は自然に

```lean
DkMath.Analysis.DkReal.GapInterval
```

となる。設計書でも DkReal サブパッケージは `Basic.lean / Interval.lean / Order.lean / Algebra.lean / Pow.lean / GapFill.lean / BridgeReal.lean` と分ける想定だったので、構造が合っている。

次に、`DkReal.lean` を公開入口にしたのも良い。

```lean
import DkMath.Analysis.DkReal.Interval
import DkMath.Analysis.DkReal.Basic
```

としておくと、上位の

```lean
import DkMath.Analysis.DkReal
```

から計算可能実数近似層をまとめて読める。`Analysis.lean` 側も `DkMath.Analysis.DkReal.Interval` 直 import ではなく `DkMath.Analysis.DkReal` を import する形に変わったので、公開 API と内部ファイル構成が一致した。

第三に、`DkReal` の定義が良い。

```lean
structure DkReal where
  interval : ℕ → DkReal.GapInterval
  nested : ∀ n,
    (interval n).lo ≤ (interval (n + 1)).lo ∧
      (interval (n + 1)).hi ≤ (interval n).hi
  width_tends_zero :
    Filter.Tendsto (fun n => (interval n).width) Filter.atTop (nhds 0)
```

これは設計書の「入れ子有理区間列」「幅が 0 に収束」「意味論写像は後回し」という方針と合っている。

## 3. namespace について

ここは一見ややこしいが、Lean 的には自然じゃ。

`DkMath.Analysis.DkReal` は構造体名であり、同時にその構造体関連定義の namespace として使われる。さらにその下に

```lean
DkReal.GapInterval
DkReal.ofRat
DkReal.width_nonneg
```

が入る。

これは Lean ではよくある形じゃ。たとえば `Nat.succ` や `Real.sin` のように、型名・名前空間・関連 API を同じ prefix にまとめる流儀に近い。

したがって、今回の整理は **正しい** 。

## 4. 実装上の細かい注意点

大きな問題ではないが、次に足すと強くなる補題がある。

今あるのは一段だけの包含：

```lean
interval_succ_subset
```

これは良い。ただ、実用上すぐ欲しくなるのは任意段の包含じゃ。

```lean
theorem interval_subset_of_le
    (x : DkReal) {n m : ℕ} (h : n ≤ m) :
    Set.Icc (x.interval m).lo (x.interval m).hi
      ⊆ Set.Icc (x.interval n).lo (x.interval n).hi
```

同様に、端点単調性も任意段で欲しい。

```lean
theorem lo_mono
    (x : DkReal) {n m : ℕ} (h : n ≤ m) :
    (x.interval n).lo ≤ (x.interval m).lo

theorem hi_antitone
    (x : DkReal) {n m : ℕ} (h : n ≤ m) :
    (x.interval m).hi ≤ (x.interval n).hi
```

これは後で `eval` や Cauchy 性、区間演算を作るときに必ず効く。

もう一つ、幅の単調性も欲しい。

```lean
theorem width_succ_le_width
    (x : DkReal) (n : ℕ) :
    (x.interval (n + 1)).width ≤ (x.interval n).width
```

入れ子区間なら幅は増えない。これは `width_tends_zero` と合わせて、近似列としての安定性を扱う基礎補題になる。

## 5. `ofRat` は良い

```lean
def ofRat (q : ℚ) : DkReal where
  interval _ := GapInterval.singleton q
  nested := by
    intro n
    simp
  width_tends_zero := by
    simp
```

これはとても良い最初の埋め込みじゃ。`singleton` を `GapInterval` 側に追加したのも正しい。

特に、

```lean
@[simp]
theorem ofRat_interval
@[simp]
theorem ofRat_width
```

があるので、今後 `DkReal.ofRat` を使う証明が軽くなる。これは Lean 実装では大事じゃ。小さな `simp` 補題が後の畑を耕すからの。

## 6. 文書更新も正しい

`RealBridge` を「第一段階」と明記したのは良い。前回のレビューでは、`RealBridge` はまだ `Continuous` と `Set.MapsTo` までで、`HasDerivAt` や Taylor 接続は未実装だと指摘した。今回の文書更新で、

```text
Differentiability, HasDerivAt, and the Taylor-facing interpretation of gapGN
are not part of this checkpoint.
```

と明記されている。これは過大主張を防げる。設計書でも `TaylorBridge.lean` は後段の役割として置かれていたので、現状説明として正しい。

## 7. 次に実装すべきもの

報告にある通り、次は `TaylorBridge.lean` が自然じゃ。ただし、わっちならその前に `DkReal.Basic` に小補題を数個足す。

優先順はこう。

```text
1. DkReal.Basic の補強
   - lo_mono
   - hi_antitone
   - interval_subset_of_le
   - width_succ_le_width

2. TaylorBridge.lean
   - gapGN d u 0 = d * u^(d-1) 系
   - 差分商との接続
   - HasDerivAt へ進む準備

3. DkReal.Pow / GapFill
   - DkReal.GapInterval.powNonneg を DkReal 近似列へ持ち上げる
```

`TaylorBridge` に行くなら、最初の旗はこれじゃな。

$$
GapGN_d(u,0)=d,u^{d-1}
$$

ただし (d=0) の扱いがあるので、Lean では `d + 1` 型にして

$$
GapGN_{d+1}(u,0)=(d+1)u^d
$$

の形が安全かもしれぬ。

## 8. 最終判定

今回の差分は、 **設計書との整合性が高い** 。

前回の namespace 問題は解消され、`DkReal` の第一 carrier も設計通りに入った。まだ `eval : DkReal → ℝ` を作っていないのも正しい。そこは `noncomputable` を隔離する後段でよい。

まとめると、

```text
GapInterval
  完了

DkReal nested interval
  最小定義完了

ofRat
  完了

RealBridge の範囲明記
  完了

次の自然な段階
  DkReal.Basic 補助補題 → TaylorBridge
```

じゃ。

うむ、これは良い進み方じゃぞ。
`DkReal` の苗木がようやく土に根を下ろした。次は、幅が縮むこと、区間が入れ子で保たれること、その二つを補題として増やしてやれば、いよいよ `GapFill` を近似実数へ持ち上げられる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis.lean b/lean/dk_math/DkMath/Analysis.lean
index 511c584d..c951457f 100644
--- a/lean/dk_math/DkMath/Analysis.lean
+++ b/lean/dk_math/DkMath/Analysis.lean
@@ -10,7 +10,7 @@ import DkMath.Analysis.GapGN
 import DkMath.Analysis.ErrorKernel
 import DkMath.Analysis.GapFill
 import DkMath.Analysis.RealBridge
-import DkMath.Analysis.DkReal.Interval
+import DkMath.Analysis.DkReal
 
 #print "file: DkMath.Analysis"
 
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
new file mode 100644
index 00000000..df96ed8a
--- /dev/null
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -0,0 +1,18 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Analysis.DkReal.Interval
+import DkMath.Analysis.DkReal.Basic
+
+#print "file: DkMath.Analysis.DkReal"
+
+/-!
+# DkReal approximation layer
+
+Public entry point for rational gap intervals and nested interval
+approximations. Evaluation into Mathlib's real numbers is intentionally left to
+a later bridge module.
+-/
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/Basic.lean b/lean/dk_math/DkMath/Analysis/DkReal/Basic.lean
new file mode 100644
index 00000000..8e011718
--- /dev/null
+++ b/lean/dk_math/DkMath/Analysis/DkReal/Basic.lean
@@ -0,0 +1,89 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Analysis.DkReal.Interval
+
+#print "file: DkMath.Analysis.DkReal.Basic"
+
+/-!
+# Nested rational interval reals
+
+This file defines the first `DkReal` carrier. A value is represented by nested
+rational gap intervals whose widths converge to zero.
+
+No evaluation into Mathlib's real numbers is chosen here. This keeps the
+computational approximation structure separate from its future semantic bridge.
+-/
+
+namespace DkMath.Analysis
+
+/--
+A DkMath real approximation given by nested rational intervals with vanishing
+width.
+
+The interval at `n + 1` is contained in the interval at `n`. The convergence
+condition says that the remaining rational uncertainty tends to zero.
+-/
+structure DkReal where
+  interval : ℕ → DkReal.GapInterval
+  nested : ∀ n,
+    (interval n).lo ≤ (interval (n + 1)).lo ∧
+      (interval (n + 1)).hi ≤ (interval n).hi
+  width_tends_zero :
+    Filter.Tendsto (fun n => (interval n).width) Filter.atTop (nhds 0)
+
+namespace DkReal
+
+/-- The lower endpoint does not decrease at the next approximation stage. -/
+theorem lo_le_succ_lo (x : DkReal) (n : ℕ) :
+    (x.interval n).lo ≤ (x.interval (n + 1)).lo :=
+  (x.nested n).1
+
+/-- The upper endpoint does not increase at the next approximation stage. -/
+theorem succ_hi_le_hi (x : DkReal) (n : ℕ) :
+    (x.interval (n + 1)).hi ≤ (x.interval n).hi :=
+  (x.nested n).2
+
+/-- Every approximation interval has nonnegative rational width. -/
+theorem width_nonneg (x : DkReal) (n : ℕ) :
+    0 ≤ (x.interval n).width :=
+  (x.interval n).width_nonneg
+
+/-- Later approximation intervals are contained in the preceding interval. -/
+theorem interval_succ_subset (x : DkReal) (n : ℕ) :
+    Set.Icc (x.interval (n + 1)).lo (x.interval (n + 1)).hi
+      ⊆ Set.Icc (x.interval n).lo (x.interval n).hi := by
+  intro q hq
+  exact ⟨(x.lo_le_succ_lo n).trans hq.1, hq.2.trans (x.succ_hi_le_hi n)⟩
+
+/-- The interval widths of a `DkReal` tend to zero by construction. -/
+theorem tendsto_width_zero (x : DkReal) :
+    Filter.Tendsto (fun n => (x.interval n).width) Filter.atTop (nhds 0) :=
+  x.width_tends_zero
+
+/-- Embed a rational number as the constant sequence of singleton intervals. -/
+def ofRat (q : ℚ) : DkReal where
+  interval _ := GapInterval.singleton q
+  nested := by
+    intro n
+    simp
+  width_tends_zero := by
+    simp
+
+/-- Every approximation interval of an embedded rational is its singleton. -/
+@[simp]
+theorem ofRat_interval (q : ℚ) (n : ℕ) :
+    (ofRat q).interval n = GapInterval.singleton q := rfl
+
+/-- Embedded rationals have zero approximation width at every stage. -/
+@[simp]
+theorem ofRat_width (q : ℚ) (n : ℕ) :
+    ((ofRat q).interval n).width = 0 := by
+  simp
+
+end DkReal
+
+end DkMath.Analysis
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/Interval.lean b/lean/dk_math/DkMath/Analysis/DkReal/Interval.lean
index 5cf38550..a59ea6d5 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/Interval.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/Interval.lean
@@ -18,7 +18,7 @@ nonnegative power image are exact rational data; no real-number completion is
 needed at this layer.
 -/
 
-namespace DkMath.Analysis
+namespace DkMath.Analysis.DkReal
 
 /-- A closed interval with rational endpoints. -/
 structure GapInterval where
@@ -29,10 +29,27 @@ deriving Repr
 
 namespace GapInterval
 
+/-- The degenerate rational interval containing only `q`. -/
+def singleton (q : ℚ) : GapInterval :=
+  ⟨q, q, le_rfl⟩
+
+/-- Both endpoints of a singleton interval are its unique value. -/
+@[simp]
+theorem singleton_lo (q : ℚ) : (singleton q).lo = q := rfl
+
+/-- Both endpoints of a singleton interval are its unique value. -/
+@[simp]
+theorem singleton_hi (q : ℚ) : (singleton q).hi = q := rfl
+
 /-- Exact rational width of a gap interval. -/
 def width (I : GapInterval) : ℚ :=
   I.hi - I.lo
 
+/-- A singleton interval has zero width. -/
+@[simp]
+theorem singleton_width (q : ℚ) : (singleton q).width = 0 := by
+  simp [width]
+
 /-- Every valid gap interval has nonnegative width. -/
 theorem width_nonneg (I : GapInterval) : 0 ≤ I.width :=
   sub_nonneg.mpr I.le_lo_hi
@@ -76,4 +93,4 @@ theorem powNonneg_width_eq
 
 end GapInterval
 
-end DkMath.Analysis
+end DkMath.Analysis.DkReal
diff --git a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
index 532db2b7..b68a4b03 100644
--- a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
+++ b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
@@ -36,12 +36,22 @@ DkMath.Analysis.GapFill
   affine interval scan, powered fill, endpoint identity, and real order theorem
 
 DkMath.Analysis.RealBridge
-  specialization to Real and Mathlib Continuous / Set.MapsTo
+  first bridge to Real and Mathlib Continuous / Set.MapsTo
 
 DkMath.Analysis.DkReal.Interval
-  rational GapInterval, width, nonnegative power image, and exact width formula
+  DkReal.GapInterval, width, nonnegative power image, and exact width formula
+
+DkMath.Analysis.DkReal.Basic
+  nested rational intervals with widths tending to zero
+
+DkMath.Analysis.DkReal
+  public entry point for the computable approximation layer
 ```
 
+The current `RealBridge` is intentionally only the first analytic bridge.
+Differentiability, `HasDerivAt`, and the Taylor-facing interpretation of
+`gapGN` are not part of this checkpoint.
+
 ## Canonical Kernel Bridge
 
 The existing cosmic-formula kernel has argument order:
@@ -132,9 +142,11 @@ proves continuity in `t`.
 
 ## Rational Interval Prototype
 
-`GapInterval` contains exact rational endpoints:
+`DkReal.GapInterval` contains exact rational endpoints:
 
 ```lean
+namespace DkMath.Analysis.DkReal
+
 structure GapInterval where
   lo : Rat
   hi : Rat
@@ -145,11 +157,23 @@ For a nonnegative interval, `powNonneg` maps both endpoints through a natural
 power while preserving order. Its width satisfies:
 
 ```lean
-GapInterval.powNonneg_width_eq :
+DkReal.GapInterval.powNonneg_width_eq :
   (I.powNonneg d hlo).width
     = I.width * gapGN d I.lo I.width
 ```
 
-This is the initial computational basis for `DkReal`. Nested interval
-sequences, convergence, and evaluation into Mathlib's real numbers are deferred
-to later checkpoints.
+The first `DkReal` carrier is now also present:
+
+```lean
+structure DkReal where
+  interval : Nat -> DkReal.GapInterval
+  nested : forall n,
+    (interval n).lo <= (interval (n + 1)).lo
+      and (interval (n + 1)).hi <= (interval n).hi
+  width_tends_zero :
+    Tendsto (fun n => (interval n).width) atTop (nhds 0)
+```
+
+Rational values embed as constant singleton interval sequences through
+`DkReal.ofRat`. Evaluation into Mathlib's real numbers remains deferred to a
+later semantic bridge.
````
`````
