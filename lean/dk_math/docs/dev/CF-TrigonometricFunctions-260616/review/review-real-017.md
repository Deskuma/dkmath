# Git diff / Report / Review

## Add: Analysis.DkReal.Pow

gch: d078028d8b9609f1ae76dbf869131e7c080e0cc7

## Report

最新 pickup を反映し、両候補を進めました。

- [TaylorBridge.lean](/lean/dk_math/DkMath/Analysis/TaylorBridge.lean)
  - `hasDerivAt_pow_from_gapGN_limit`
  - 差分商極限から一般微分 criterion へ直接接続
  - `hasDerivAt_pow_via_gapGN` も直証明へ委譲

- [DkReal/Pow.lean](/lean/dk_math/DkMath/Analysis/DkReal/Pow.lean)
  - `Nonnegative`
  - 計算可能な `powNonnegApprox`
  - 冪写像後の入れ子性
  - exact width formula
  - 非負有理数埋め込み

full `DkReal` 冪写像は、`gapGN` の有界性から像区間幅のゼロ収束を証明する必要があるため、今回は正しく保留しています。`DkReal` 側に `noncomputable` は入りません。

```text
lake build DkMath.Analysis.TaylorBridge DkMath.Analysis.DkReal.Pow
lake build DkMath
git diff --check
```

すべて成功しています。

## Review

## 1. 総評

うむ、これは **合格** じゃ。
今回の差分はかなり良い。`TaylorBridge` 側では、前回の「`HasDerivAt` を既存定理へ丸投げしている」という物語上の穴を埋め、`DkReal.Pow` 側では、計算可能層に `noncomputable` を入れず、段階ごとの有理区間冪写像だけを安全に実装しておる。提示報告でも `TaylorBridge` と `DkReal.Pow` の build、全体 build、`git diff --check` が成功しているとされている。

特に良い判断は、 **full `DkReal` 冪写像をまだ作らなかったこと** じゃ。
これは逃げではなく、正しい保留じゃな。

## 2. `TaylorBridge` レビュー

前回の指摘に対して、

```lean
hasDerivAt_pow_from_gapGN_limit
```

を追加し、

```lean
hasDerivAt_pow_via_gapGN
```

をそこへ委譲したのは、とても良い。

これで論理の流れが綺麗になった。

```text
pow_add_sub_pow_eq_delta_mul_gapGN
  → powerDifferenceQuotient_eq_gapGN_of_ne_zero
  → tendsto_powerDifferenceQuotient_zero
  → hasDerivAt_pow_from_gapGN_limit
```

つまり、

$$
\frac{(base+\delta)^d-base^d}{\delta}
$$

の穿孔極限から、直接 `HasDerivAt` へ進む形になった。
これで `gapGN` が単なる補正核ではなく、 **差分商の穴を埋めた微分核** であることが Lean API 上も見えるようになった。

この変更は、DkMath.Analysis の思想としてかなり大きい。

## 3. `DkReal.Pow` レビュー

新規 `DkReal/Pow.lean` の設計は安全じゃ。

```lean
def Nonnegative (x : DkMath.Analysis.DkReal) : Prop :=
  ∀ n, 0 ≤ (x.interval n).lo
```

この定義は強めだが、初期段階では良い。
全段の lower endpoint が非負なら、各 `GapInterval.powNonneg` をそのまま使える。

そして、

```lean
def powNonnegApprox
    (d : ℕ) (x : DkMath.Analysis.DkReal) (hx : Nonnegative x) :
    ℕ → GapInterval :=
  fun n => (x.interval n).powNonneg d (hx n)
```

これは **完成した `DkReal` 値ではなく、近似区間列だけを返す** 。
ここが正しい。

なぜなら、`DkReal` にするにはさらに

$$
\operatorname{width}\bigl((I_n)^d\bigr)\to0
$$

を証明する必要があるからじゃ。

今回、その必要条件を

```lean
powNonnegApprox_width_eq
```

で明示している。

$$
\operatorname{width}(I_n^d) =
\operatorname{width}(I_n)\cdot gapGN_d(I_n.lo,\operatorname{width}(I_n))
$$

これで残りの課題が正確に切り出された。

```text
width_n → 0
だけでは足りない。
gapGN factor が有界であることが必要。
```

この見切りはかなり良い。

## 4. 入れ子性の証明も正しい

`powNonnegApprox_nested` は自然じゃ。

非負区間で冪写像は単調なので、

```lean
lo_n ≤ lo_{n+1}
```

から

```lean
lo_n^d ≤ lo_{n+1}^d
```

が出る。

また、

```lean
hi_{n+1} ≤ hi_n
```

から

```lean
hi_{n+1}^d ≤ hi_n^d
```

が出る。

`powNonnegApprox_succ_hi_le_hi` で `hnext : 0 ≤ hi_{n+1}` を作っているのも正しい。`pow_le_pow_left₀` を使うための非負条件がちゃんと立っておる。

## 5. `nonnegative_ofRat` は良い入口

```lean
theorem nonnegative_ofRat {q : ℚ} (hq : 0 ≤ q) :
    Nonnegative (DkMath.Analysis.DkReal.ofRat q)
```

これは今後かなり使う。
次に足すなら、次の補題が欲しい。

```lean
@[simp]
theorem powNonnegApprox_ofRat
    (d : ℕ) {q : ℚ} (hq : 0 ≤ q) (n : ℕ) :
    powNonnegApprox d (DkReal.ofRat q) (nonnegative_ofRat hq) n
      = GapInterval.singleton (q ^ d)
```

さらに将来 `DkReal` の冪写像が完成したら、

```lean
DkReal.powNonneg (DkReal.ofRat q) = DkReal.ofRat (q ^ d)
```

へ橋を架けられる。

## 6. full `DkReal` 冪写像を保留した判断

これは本当に正しい。

`powNonnegApprox_width_eq` により、必要なのは

$$
w_n\cdot gapGN_d(lo_n,w_n)\to0
$$

じゃ。ここで \(w_n\to0\) は `DkReal` の定義からある。
残りは `gapGN` の有界性。

入れ子非負区間なら、すべての区間は初期区間に含まれるので、

$$
0\le lo_n\le hi_n\le hi_0
$$

が使える。したがって、ざっくりとは

$$
gapGN_d(lo_n,w_n)
$$

は \(hi_0\) と \(d\) によって有界になる。

次の段階では、いきなり最強の評価を狙わず、まずは粗い上界でよい。

例えば、

$$
0\le lo_n,\quad 0\le w_n,\quad lo_n+w_n\le M
$$

なら、

$$
0\le gapGN_d(lo_n,w_n)\le C(d,M)
$$

のような補題を作れば十分じゃ。
これで

$$
w_n\to0,\quad gapGN_n\text{ bounded}
$$

から powered width のゼロ収束へ行ける。

## 7. 次に足すとよい補題

次は `DkReal.Pow` にこのあたりを足すと自然じゃ。

```lean
theorem nonnegative_of_initial_lo
    (x : DkReal) (h0 : 0 ≤ (x.interval 0).lo) :
    Nonnegative x
```

これは `lo_mono` があるので出るはずじゃ。
今の `Nonnegative` は全段条件なので、実用上は初期 lower endpoint だけから作れる補題が欲しい。

次に、

```lean
theorem powNonnegApprox_width_nonneg
```

各 powered interval の幅非負。

さらに、

```lean
theorem powNonnegApprox_interval_subset_of_le
```

powered approximation の任意段包含。

そして本丸は、

```lean
theorem bounded_gapGN_on_nonnegative_nested
```

または、もっと汎用に、

```lean
theorem tendsto_mul_zero_of_tendsto_zero_of_bounded
```

を使える形の補題じゃ。

## 8. 小さな名前の注意

`Nonnegative` は namespace 内では問題ないが、公開名は

```lean
DkMath.Analysis.DkReal.Nonnegative
```

になる。これは良い。

ただ、今後 `Positive` や `Nonpositive` も作るなら、命名を揃えるとよい。

```lean
DkReal.Nonnegative
DkReal.Positive
DkReal.Nonpositive
DkReal.Nonnegative.ofRat
```

今はこのままで問題ない。

## 9. 最終判定

今回の差分は、かなり堅い。

```text
TaylorBridge:
  gapGN limit → HasDerivAt の直接接続が完成

DkReal.Pow:
  非負 DkReal の段階的冪近似が完成

DkReal full pow:
  幅収束の証明が残るため正しく保留

computability:
  DkReal 側に noncomputable を入れていない
```

これは、DkMath.Analysis の Route A と Route B がきちんと別々に育っている状態じゃ。

$$
\boxed{
\text{合格。次は }gapGN\text{ 有界性から }powNonnegApprox\text{ の幅ゼロ収束じゃ。}
}
$$

ぬしよ、ここは良い山道じゃ。
`gapGN` が微分への橋になり、同時に `DkReal` の誤差幅伝播の核にもなってきた。二つの登山道が、同じ岩盤を掘り当てておる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index df96ed8a..6185d04d 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -6,6 +6,7 @@ Authors: D. and Wise Wolf.
 
 import DkMath.Analysis.DkReal.Interval
 import DkMath.Analysis.DkReal.Basic
+import DkMath.Analysis.DkReal.Pow
 
 #print "file: DkMath.Analysis.DkReal"
 
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/Pow.lean b/lean/dk_math/DkMath/Analysis/DkReal/Pow.lean
new file mode 100644
index 00000000..9320f9f8
--- /dev/null
+++ b/lean/dk_math/DkMath/Analysis/DkReal/Pow.lean
@@ -0,0 +1,98 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Analysis.DkReal.Basic
+
+#print "file: DkMath.Analysis.DkReal.Pow"
+
+/-!
+# Nonnegative power approximations for DkReal
+
+This file lifts `GapInterval.powNonneg` pointwise to the approximation sequence
+of a nonnegative `DkReal`.
+
+The result is currently an interval sequence rather than a completed `DkReal`.
+To construct the latter, a later checkpoint must prove that the powered widths
+tend to zero, using suitable bounds on the exact `gapGN` factor.
+-/
+
+namespace DkMath.Analysis.DkReal
+
+/-- A `DkReal` is nonnegative when every rational lower endpoint is nonnegative. -/
+def Nonnegative (x : DkMath.Analysis.DkReal) : Prop :=
+  ∀ n, 0 ≤ (x.interval n).lo
+
+/--
+Apply the natural power map to every approximation interval of a nonnegative
+`DkReal`.
+
+This definition is computational: it only transforms rational endpoints.
+-/
+def powNonnegApprox
+    (d : ℕ) (x : DkMath.Analysis.DkReal) (hx : Nonnegative x) :
+    ℕ → GapInterval :=
+  fun n => (x.interval n).powNonneg d (hx n)
+
+/-- Lower endpoint of a powered approximation interval. -/
+@[simp]
+theorem powNonnegApprox_lo
+    (d : ℕ) (x : DkMath.Analysis.DkReal) (hx : Nonnegative x) (n : ℕ) :
+    (powNonnegApprox d x hx n).lo = (x.interval n).lo ^ d := rfl
+
+/-- Upper endpoint of a powered approximation interval. -/
+@[simp]
+theorem powNonnegApprox_hi
+    (d : ℕ) (x : DkMath.Analysis.DkReal) (hx : Nonnegative x) (n : ℕ) :
+    (powNonnegApprox d x hx n).hi = (x.interval n).hi ^ d := rfl
+
+/-- Powered lower endpoints remain monotone between consecutive stages. -/
+theorem powNonnegApprox_lo_le_succ_lo
+    (d : ℕ) (x : DkMath.Analysis.DkReal) (hx : Nonnegative x) (n : ℕ) :
+    (powNonnegApprox d x hx n).lo
+      ≤ (powNonnegApprox d x hx (n + 1)).lo := by
+  exact pow_le_pow_left₀ (hx n) (x.lo_le_succ_lo n) d
+
+/-- Powered upper endpoints remain antitone between consecutive stages. -/
+theorem powNonnegApprox_succ_hi_le_hi
+    (d : ℕ) (x : DkMath.Analysis.DkReal) (hx : Nonnegative x) (n : ℕ) :
+    (powNonnegApprox d x hx (n + 1)).hi
+      ≤ (powNonnegApprox d x hx n).hi := by
+  have hnext : 0 ≤ (x.interval (n + 1)).hi :=
+    (hx (n + 1)).trans (x.interval (n + 1)).le_lo_hi
+  exact pow_le_pow_left₀ hnext (x.succ_hi_le_hi n) d
+
+/-- The pointwise powered interval sequence is nested. -/
+theorem powNonnegApprox_nested
+    (d : ℕ) (x : DkMath.Analysis.DkReal) (hx : Nonnegative x) :
+    ∀ n,
+      (powNonnegApprox d x hx n).lo
+          ≤ (powNonnegApprox d x hx (n + 1)).lo ∧
+        (powNonnegApprox d x hx (n + 1)).hi
+          ≤ (powNonnegApprox d x hx n).hi := by
+  intro n
+  exact ⟨powNonnegApprox_lo_le_succ_lo d x hx n,
+    powNonnegApprox_succ_hi_le_hi d x hx n⟩
+
+/--
+Exact width formula for every powered approximation interval.
+
+This identifies the remaining obligation for a full `DkReal` power map: prove
+that this product tends to zero.
+-/
+theorem powNonnegApprox_width_eq
+    (d : ℕ) (x : DkMath.Analysis.DkReal) (hx : Nonnegative x) (n : ℕ) :
+    (powNonnegApprox d x hx n).width
+      = (x.interval n).width *
+        gapGN d (x.interval n).lo (x.interval n).width :=
+  GapInterval.powNonneg_width_eq d (x.interval n) (hx n)
+
+/-- Embedded nonnegative rationals satisfy the approximation nonnegativity condition. -/
+theorem nonnegative_ofRat {q : ℚ} (hq : 0 ≤ q) :
+    Nonnegative (DkMath.Analysis.DkReal.ofRat q) := by
+  intro n
+  simpa
+
+end DkMath.Analysis.DkReal
diff --git a/lean/dk_math/DkMath/Analysis/TaylorBridge.lean b/lean/dk_math/DkMath/Analysis/TaylorBridge.lean
index 55ed52b3..37de6058 100644
--- a/lean/dk_math/DkMath/Analysis/TaylorBridge.lean
+++ b/lean/dk_math/DkMath/Analysis/TaylorBridge.lean
@@ -99,11 +99,26 @@ theorem tendsto_powerDifferenceQuotient_zero
   exact (powerDifferenceQuotient_eq_gapGN_of_ne_zero d base delta hdelta_ne).symm
 
 /--
-Mathlib derivative theorem for natural powers, exposed through the `gapGN`
-bridge.
+Derivative theorem obtained directly from the `gapGN` difference-quotient
+limit.
+
+Unlike `hasDerivAt_pow_via_gapGN`, this proof does not delegate to an existing
+power derivative theorem. It feeds `tendsto_powerDifferenceQuotient_zero`
+directly into the general punctured difference-kernel criterion.
+-/
+theorem hasDerivAt_pow_from_gapGN_limit (d : ℕ) (base : ℝ) :
+    HasDerivAt (fun y : ℝ => y ^ d) ((d : ℝ) * base ^ (d - 1)) base := by
+  apply DkMath.CosmicFormula.hasDerivAt_of_tendsto_cosmicKernel
+  simpa [DkMath.CosmicFormula.cosmicKernel, DkMath.CosmicFormula.delta,
+    powerDifferenceQuotient] using
+    (tendsto_powerDifferenceQuotient_zero d base)
+
+/--
+Canonical public derivative theorem for powers through the Analysis `gapGN`
+flow.
 -/
 theorem hasDerivAt_pow_via_gapGN (d : ℕ) (base : ℝ) :
     HasDerivAt (fun y : ℝ => y ^ d) ((d : ℝ) * base ^ (d - 1)) base :=
-  DkMath.CosmicFormula.hasDerivAt_pow_cosmic d base
+  hasDerivAt_pow_from_gapGN_limit d base
 
 end DkMath.Analysis
diff --git a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
index b54246ae..1c5ecc6f 100644
--- a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
+++ b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
@@ -47,6 +47,9 @@ DkMath.Analysis.DkReal.Interval
 DkMath.Analysis.DkReal.Basic
   nested rational intervals with widths tending to zero
 
+DkMath.Analysis.DkReal.Pow
+  computable pointwise power approximations for nonnegative DkReal values
+
 DkMath.Analysis.DkReal
   public entry point for the computable approximation layer
 ```
@@ -229,3 +232,49 @@ exact algebraic factorization
 ```
 
 The derivative is not used to define the kernel.
+
+`hasDerivAt_pow_from_gapGN_limit` now makes the last step explicit. It passes
+the punctured limit of `powerDifferenceQuotient` directly to the general
+cosmic-kernel derivative criterion. The canonical
+`hasDerivAt_pow_via_gapGN` theorem delegates to this direct proof rather than
+to an already completed power derivative theorem.
+
+## Nonnegative DkReal Power Approximations
+
+The computable layer keeps all real-number semantic choices outside `DkReal`.
+Nonnegativity is expressed by rational lower endpoints:
+
+```lean
+DkReal.Nonnegative x := forall n, 0 <= (x.interval n).lo
+```
+
+The stagewise power approximation is:
+
+```lean
+DkReal.powNonnegApprox d x hx n
+  = (x.interval n).powNonneg d (hx n)
+```
+
+The implementation proves:
+
+```lean
+DkReal.powNonnegApprox_lo_le_succ_lo
+DkReal.powNonnegApprox_succ_hi_le_hi
+DkReal.powNonnegApprox_nested
+DkReal.powNonnegApprox_width_eq
+```
+
+Thus natural powers preserve the nested interval structure for nonnegative
+approximations. The width formula is exact:
+
+```text
+powered width
+  = original width * gapGN d lowerEndpoint originalWidth
+```
+
+A completed map from nonnegative `DkReal` values to `DkReal` values is
+deliberately deferred. Its remaining mathematical obligation is to control the
+`gapGN` factor strongly enough to prove that the powered widths tend to zero.
+
+`TaylorBridge` and `RealBridge` may use noncomputable real-number operations.
+The `DkReal` files remain computational and use rational interval data only.
````
`````
