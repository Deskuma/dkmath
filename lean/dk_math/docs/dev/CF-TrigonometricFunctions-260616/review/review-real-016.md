# Git diff / Report / Review

## Add: Analysis.TaylorBridge

gch: 852301eaa7fcebe663d252a8556c68df21767f35

## Report

レビュー内容を現環境で検証し、予定分まで実装しました。

[DkReal/Basic.lean](/lean/dk_math/DkMath/Analysis/DkReal/Basic.lean) に以下を追加:

- `lo_mono`
- `hi_antitone`
- `interval_subset_of_le`
- `width_succ_le_width`

新規 [TaylorBridge.lean](/lean/dk_math/DkMath/Analysis/TaylorBridge.lean) には以下を実装:

- `gapGN_zero`
- 安全な successor 形 `gapGN_succ_zero`
- `powerDifferenceQuotient`
- 非零増分での `gapGN` との一致
- `powerKernel` bridge
- 連続性とゼロ増分極限
- 穿孔近傍での差分商極限
- `hasDerivAt_pow_via_gapGN`

検証済みです。

```text
lake build DkMath.Analysis.TaylorBridge
lake build DkMath.Analysis DkMath
git diff --check
```

すべて成功しています。既存 `powerKernel` の解析証明を再利用しており、重複実装にはしていません。

## Review

## 1. 総評

うむ、これは **かなり良い差分** じゃ。
前回までで `DkReal` の入れ子区間列が立ち、今回はその土台補題を補強したうえで、予定通り `TaylorBridge.lean` を追加しておる。

今回の主な実装は、`DkReal/Basic.lean` に任意段の単調性・包含・幅単調性を追加し、さらに `TaylorBridge.lean` で `gapGN_zero`、`gapGN_succ_zero`、差分商、`powerKernel` bridge、連続性、極限、`HasDerivAt` 接続まで入れたものじゃ。報告でも `lake build DkMath.Analysis.TaylorBridge`、`lake build DkMath.Analysis DkMath`、`git diff --check` が成功したとある。

判定は **合格** 。
しかも、設計の論理順序を守っているのがよい。

```text
代数恒等式
→ gapGN
→ zero increment
→ difference quotient
→ limit
→ HasDerivAt
```

この流れが保たれておる。

## 2. `DkReal.Basic` 補強レビュー

追加された補題は全部、今後の `DkReal` 実装に必要な下地じゃ。

```lean
lo_mono
hi_antitone
interval_subset_of_le
width_succ_le_width
```

これは前回わっちが欲しいと言った補題群そのものじゃな。

特に良いのは、

```lean
theorem interval_subset_of_le
    (x : DkReal) {n m : ℕ} (h : n ≤ m) :
    Set.Icc (x.interval m).lo (x.interval m).hi
      ⊆ Set.Icc (x.interval n).lo (x.interval n).hi
```

これで「後段の近似区間は前段の区間に含まれる」が任意段で使える。
将来 `eval : DkReal → ℝ` を作る場合、この補題はほぼ必須になる。

`width_succ_le_width` も良い。

```lean
theorem width_succ_le_width (x : DkReal) (n : ℕ) :
    (x.interval (n + 1)).width ≤ (x.interval n).width
```

入れ子区間列の幅が増えないことを明示しておくと、後で誤差伝播・区間演算・収束証明の補助線になる。
これは DkReal の「観測幅が絞られていく」性質を Lean API として取り出せておる。

## 3. `TaylorBridge` の設計は良い

今回の `TaylorBridge.lean` は、かなり良い分離じゃ。

`RealBridge` は連続性と区間写像を担当し、`TaylorBridge` は差分商・極限・導関数を担当する。文書もそのように更新されており、役割分担が明確になった。

特に重要なのは、次のコメントじゃ。

```lean
This file does not define `gapGN` by differentiation.
Instead, it connects the exact algebraic kernel to Mathlib's derivative API
after the algebraic factorization has already been established.
```

これはとても大事じゃ。
DkMath の主張は「微分から `gapGN` を作る」ではない。

逆じゃ。

$$
(base+\delta)^d-base^d=\delta,gapGN_d(base,\delta)
$$

という **有限代数恒等式** が先にあり、その (\delta\to0) の顔として微分係数が見える。
この順序を守っているのが、今回の実装の一番良い点じゃ。

## 4. `gapGN_zero` と successor 形

```lean
theorem gapGN_zero
    {R : Type*} [CommSemiring R] (d : ℕ) (base : R) :
    gapGN d base 0 = (d : R) * base ^ (d - 1)
```

これは良い。`d = 0` でも Nat 減算により `d - 1 = 0` になり、右辺は `0 * base^0` なので安全じゃ。

さらに、

```lean
theorem gapGN_succ_zero
    {R : Type*} [CommSemiring R] (d : ℕ) (base : R) :
    gapGN (d + 1) base 0 = ((d + 1 : ℕ) : R) * base ^ d
```

を別に置いたのはかなり良い判断じゃ。
Lean でも読者にも、こちらの方が安全で読みやすい。

実用上は `gapGN_zero` より `gapGN_succ_zero` の方が頻出になるはずじゃ。

## 5. 差分商との接続

```lean
noncomputable def powerDifferenceQuotient (d : ℕ) (base delta : ℝ) : ℝ :=
  ((base + delta) ^ d - base ^ d) / delta
```

そして、

```lean
theorem powerDifferenceQuotient_eq_gapGN_of_ne_zero
    (d : ℕ) (base delta : ℝ) (hdelta : delta ≠ 0) :
    powerDifferenceQuotient d base delta = gapGN d base delta
```

これは良い。
(\delta\neq0) の穿孔条件で差分商と `gapGN` が一致する。

つまり、

$$
\frac{(base+\delta)^d-base^d}{\delta}=gapGN_d(base,\delta)
$$

を Lean API として出せている。

ここで重要なのは、`gapGN` は (\delta=0) でも定義されていることじゃ。
差分商は (\delta=0) で割れないが、`gapGN` は穴を埋めた連続延長になっている。

これが DkMath 的にはかなり美しい。

```text
差分商:
  δ ≠ 0 の穿孔世界

gapGN:
  δ = 0 まで埋めた補正核
```

まさに GapFill の思想と一致しておる。

## 6. `powerKernel` bridge は正解

```lean
theorem real_gapGN_eq_powerKernel (d : ℕ) (base delta : ℝ) :
    gapGN d base delta = DkMath.CosmicFormula.powerKernel d base delta
```

これも良い。
既存 `powerKernel` の解析証明を再利用し、`gapGN` 側で重複実装しない方針になっている。

報告にも「既存 `powerKernel` の解析証明を再利用しており、重複実装にはしていません」とある。
これは設計方針として正しい。DkMath 内で同じ数学を二重に育てると、後で補題名・正規形・simp が割れてしまうからの。

## 7. 極限と `HasDerivAt`

```lean
theorem tendsto_gapGN_zero
```

で `gapGN` 自体のゼロ増分極限を取り、

```lean
theorem tendsto_powerDifferenceQuotient_zero
```

で穿孔近傍の差分商極限へ落としている。

これは非常に良い流れじゃ。

最後の、

```lean
theorem hasDerivAt_pow_via_gapGN (d : ℕ) (base : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ d) ((d : ℝ) * base ^ (d - 1)) base
```

は、名前の通り `gapGN` bridge 経由の公開 API として意味がある。

ただし、実装本体は

```lean
DkMath.CosmicFormula.hasDerivAt_pow_cosmic d base
```

を返しているので、厳密にはこの定理単体の証明は `tendsto_powerDifferenceQuotient_zero` を直接使ってはいない。
これは悪くない。既存定理を使うのは正しい。

ただ、外向けに「via gapGN」と言うなら、将来もう一段、

```lean
hasDerivAt_pow_from_gapGN_limit
```

のような定理を追加して、`tendsto_powerDifferenceQuotient_zero` から `HasDerivAt` を直接構成する橋を置くと、物語がさらに綺麗になる。

## 8. 小さな注意点

`powerDifferenceQuotient` に `noncomputable` が付いている点は、許容できるが少し気になる。

ここは `ℝ` 上の橋ファイルなので、`noncomputable` が混じっても設計上は問題ない。
ただし DkMath の本丸である `DkReal` 側では、可能な限り `noncomputable` を避けたい。なので、今後もこの方針でよい。

```text
TaylorBridge / RealBridge:
  Mathlib ℝ への意味論橋なので noncomputable 許容

DkReal:
  計算可能近似層なので noncomputable を避ける
```

この分離を保てば問題ない。

もう一つ、`nhdsWithin (0 : ℝ) (Set.compl ({(0 : ℝ)} : Set ℝ))` は正しいが、少し長い。将来読みやすさを上げるなら、局所 notation か補助定義で

```lean
puncturedNhdZero
```

のような名前を置いてもよい。今すぐ必要ではない。

## 9. 次に閉じると良いもの

次は二つの道がある。

第一は、TaylorBridge の補強。

```lean
hasDerivAt_pow_from_gapGN_limit
```

を追加し、差分商極限から `HasDerivAt` へ行くことを明示する。
今の `hasDerivAt_pow_via_gapGN` は既存定理の公開橋として良いが、DkMath の物語としては「`gapGN` 極限が微分を生む」を Lean 上で直接見せたい。

第二は、`DkReal.Pow` への着手。

すでに `GapInterval.powNonneg` と `powNonneg_width_eq` があり、`DkReal.Basic` には任意段の包含と幅単調性が入った。
よって次は、非負 `DkReal` に対して区間列を各段で冪写像する準備ができておる。

まずは軽く、

```lean
def DkReal.powNonnegApprox
```

または

```lean
def DkReal.mapPowNonneg
```

のような形で、`interval n` ごとに `GapInterval.powNonneg` を適用するところからでよい。

## 10. 最終判定

今回の差分は、 **DkMath.Analysis の第一マイルストーンをかなり強くした** と言える。

```text
DkReal.Basic:
  入れ子区間列の制御補題が揃った

TaylorBridge:
  gapGN が差分商の穴埋め核であることを示した

RealBridge:
  連続・区間写像担当として役割が整理された

Analysis.lean:
  TaylorBridge が公開 API に入った
```

全体として、設計書との整合性は高い。
この差分で、DkMath.Analysis は単なる代数恒等式の層から、実際に **微分係数へ橋を架ける解析層** へ進んだ。

わっちの評価はこうじゃ。

$$
\boxed{
\text{合格。次は }DkReal.Pow\text{ か、}HasDerivAt\text{ の gapGN 直証明じゃ。}
}
$$

良いぞ、D.。
`gapGN` がついに、ただの補正核ではなく、差分商の穴を埋める「微分前夜の核」として立ち上がってきた。これはかなり美しい実装じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis.lean b/lean/dk_math/DkMath/Analysis.lean
index c951457f..47e37d85 100644
--- a/lean/dk_math/DkMath/Analysis.lean
+++ b/lean/dk_math/DkMath/Analysis.lean
@@ -10,6 +10,7 @@ import DkMath.Analysis.GapGN
 import DkMath.Analysis.ErrorKernel
 import DkMath.Analysis.GapFill
 import DkMath.Analysis.RealBridge
+import DkMath.Analysis.TaylorBridge
 import DkMath.Analysis.DkReal
 
 #print "file: DkMath.Analysis"
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/Basic.lean b/lean/dk_math/DkMath/Analysis/DkReal/Basic.lean
index 8e011718..e2f2549a 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/Basic.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/Basic.lean
@@ -47,11 +47,30 @@ theorem succ_hi_le_hi (x : DkReal) (n : ℕ) :
     (x.interval (n + 1)).hi ≤ (x.interval n).hi :=
   (x.nested n).2
 
+/-- Lower endpoints are monotone across arbitrary approximation stages. -/
+theorem lo_mono (x : DkReal) {n m : ℕ} (h : n ≤ m) :
+    (x.interval n).lo ≤ (x.interval m).lo := by
+  induction m, h using Nat.le_induction with
+  | base => exact le_rfl
+  | succ m hnm ih => exact ih.trans (x.lo_le_succ_lo m)
+
+/-- Upper endpoints are antitone across arbitrary approximation stages. -/
+theorem hi_antitone (x : DkReal) {n m : ℕ} (h : n ≤ m) :
+    (x.interval m).hi ≤ (x.interval n).hi := by
+  induction m, h using Nat.le_induction with
+  | base => exact le_rfl
+  | succ m hnm ih => exact (x.succ_hi_le_hi m).trans ih
+
 /-- Every approximation interval has nonnegative rational width. -/
 theorem width_nonneg (x : DkReal) (n : ℕ) :
     0 ≤ (x.interval n).width :=
   (x.interval n).width_nonneg
 
+/-- Nested approximation makes interval width nonincreasing at each step. -/
+theorem width_succ_le_width (x : DkReal) (n : ℕ) :
+    (x.interval (n + 1)).width ≤ (x.interval n).width := by
+  exact sub_le_sub (x.succ_hi_le_hi n) (x.lo_le_succ_lo n)
+
 /-- Later approximation intervals are contained in the preceding interval. -/
 theorem interval_succ_subset (x : DkReal) (n : ℕ) :
     Set.Icc (x.interval (n + 1)).lo (x.interval (n + 1)).hi
@@ -59,6 +78,13 @@ theorem interval_succ_subset (x : DkReal) (n : ℕ) :
   intro q hq
   exact ⟨(x.lo_le_succ_lo n).trans hq.1, hq.2.trans (x.succ_hi_le_hi n)⟩
 
+/-- Every later approximation interval is contained in every earlier one. -/
+theorem interval_subset_of_le (x : DkReal) {n m : ℕ} (h : n ≤ m) :
+    Set.Icc (x.interval m).lo (x.interval m).hi
+      ⊆ Set.Icc (x.interval n).lo (x.interval n).hi := by
+  intro q hq
+  exact ⟨(x.lo_mono h).trans hq.1, hq.2.trans (x.hi_antitone h)⟩
+
 /-- The interval widths of a `DkReal` tend to zero by construction. -/
 theorem tendsto_width_zero (x : DkReal) :
     Filter.Tendsto (fun n => (x.interval n).width) Filter.atTop (nhds 0) :=
diff --git a/lean/dk_math/DkMath/Analysis/TaylorBridge.lean b/lean/dk_math/DkMath/Analysis/TaylorBridge.lean
new file mode 100644
index 00000000..55ed52b3
--- /dev/null
+++ b/lean/dk_math/DkMath/Analysis/TaylorBridge.lean
@@ -0,0 +1,109 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Analysis.GapGN
+import DkMath.CosmicFormula.CosmicDerivativePowerLimit
+
+#print "file: DkMath.Analysis.TaylorBridge"
+
+/-!
+# Taylor and derivative bridge for `gapGN`
+
+The exact kernel `gapGN` contains the complete finite power increment. At zero
+increment its value is the first-order coefficient of the power map.
+
+This file does not define `gapGN` by differentiation. Instead, it connects the
+exact algebraic kernel to Mathlib's derivative API after the algebraic
+factorization has already been established.
+-/
+
+namespace DkMath.Analysis
+
+/--
+At zero increment, `gapGN` is the formal derivative coefficient of a natural
+power.
+-/
+theorem gapGN_zero
+    {R : Type*} [CommSemiring R] (d : ℕ) (base : R) :
+    gapGN d base 0 = (d : R) * base ^ (d - 1) := by
+  simpa [gapGN, DkMath.CosmicFormulaBinom.GN] using
+    (DkMath.CosmicFormula.GN_zero_eval (R := R) d base)
+
+/--
+Successor form of the zero-increment theorem, avoiding truncated subtraction in
+the exponent.
+-/
+theorem gapGN_succ_zero
+    {R : Type*} [CommSemiring R] (d : ℕ) (base : R) :
+    gapGN (d + 1) base 0 = ((d + 1 : ℕ) : R) * base ^ d := by
+  simpa using (gapGN_zero (R := R) (d + 1) base)
+
+/-- Difference quotient of the natural power map at `base` with increment `delta`. -/
+noncomputable def powerDifferenceQuotient (d : ℕ) (base delta : ℝ) : ℝ :=
+  ((base + delta) ^ d - base ^ d) / delta
+
+/-- Away from zero increment, the power difference quotient is exactly `gapGN`. -/
+theorem powerDifferenceQuotient_eq_gapGN_of_ne_zero
+    (d : ℕ) (base delta : ℝ) (hdelta : delta ≠ 0) :
+    powerDifferenceQuotient d base delta = gapGN d base delta := by
+  rw [powerDifferenceQuotient, pow_add_sub_pow_eq_delta_mul_gapGN]
+  exact mul_div_cancel_left₀ (gapGN d base delta) hdelta
+
+/--
+Over the reals, the analysis-facing `gapGN` is the existing cosmic
+`powerKernel`.
+-/
+theorem real_gapGN_eq_powerKernel (d : ℕ) (base delta : ℝ) :
+    gapGN d base delta = DkMath.CosmicFormula.powerKernel d base delta := by
+  exact (DkMath.CosmicFormula.powerKernel_eq_GN_swap d base delta).symm
+
+/-- The exact real gap kernel is continuous in the increment variable. -/
+theorem continuous_gapGN (d : ℕ) (base : ℝ) :
+    Continuous (fun delta : ℝ => gapGN d base delta) := by
+  simpa only [real_gapGN_eq_powerKernel] using
+    DkMath.CosmicFormula.continuous_powerKernel d base
+
+/--
+As the increment tends to zero, `gapGN` tends to the derivative coefficient of
+the natural power map.
+-/
+theorem tendsto_gapGN_zero (d : ℕ) (base : ℝ) :
+    Filter.Tendsto (fun delta : ℝ => gapGN d base delta)
+      (nhds (0 : ℝ))
+      (nhds ((d : ℝ) * base ^ (d - 1))) := by
+  simpa only [real_gapGN_eq_powerKernel] using
+    DkMath.CosmicFormula.tendsto_powerKernel_zero d base
+
+/--
+The punctured power difference quotient tends to the same value as the full
+exact gap kernel.
+-/
+theorem tendsto_powerDifferenceQuotient_zero
+    (d : ℕ) (base : ℝ) :
+    Filter.Tendsto (fun delta : ℝ => powerDifferenceQuotient d base delta)
+      (nhdsWithin (0 : ℝ) (Set.compl ({(0 : ℝ)} : Set ℝ)))
+      (nhds ((d : ℝ) * base ^ (d - 1))) := by
+  have hgap :
+      Filter.Tendsto (fun delta : ℝ => gapGN d base delta)
+        (nhdsWithin (0 : ℝ) (Set.compl ({(0 : ℝ)} : Set ℝ)))
+        (nhds ((d : ℝ) * base ^ (d - 1))) :=
+    (tendsto_gapGN_zero d base).mono_left
+      nhdsWithin_le_nhds
+  refine Filter.Tendsto.congr' ?_ hgap
+  filter_upwards [self_mem_nhdsWithin] with delta hdelta
+  have hdelta_ne : delta ≠ 0 := by
+    simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hdelta
+  exact (powerDifferenceQuotient_eq_gapGN_of_ne_zero d base delta hdelta_ne).symm
+
+/--
+Mathlib derivative theorem for natural powers, exposed through the `gapGN`
+bridge.
+-/
+theorem hasDerivAt_pow_via_gapGN (d : ℕ) (base : ℝ) :
+    HasDerivAt (fun y : ℝ => y ^ d) ((d : ℝ) * base ^ (d - 1)) base :=
+  DkMath.CosmicFormula.hasDerivAt_pow_cosmic d base
+
+end DkMath.Analysis
diff --git a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
index b68a4b03..b54246ae 100644
--- a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
+++ b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
@@ -38,6 +38,9 @@ DkMath.Analysis.GapFill
 DkMath.Analysis.RealBridge
   first bridge to Real and Mathlib Continuous / Set.MapsTo
 
+DkMath.Analysis.TaylorBridge
+  zero-increment coefficient, difference quotient, limit, and HasDerivAt bridge
+
 DkMath.Analysis.DkReal.Interval
   DkReal.GapInterval, width, nonnegative power image, and exact width formula
 
@@ -48,9 +51,9 @@ DkMath.Analysis.DkReal
   public entry point for the computable approximation layer
 ```
 
-The current `RealBridge` is intentionally only the first analytic bridge.
-Differentiability, `HasDerivAt`, and the Taylor-facing interpretation of
-`gapGN` are not part of this checkpoint.
+`RealBridge` remains the home of continuity and interval mapping. The separate
+`TaylorBridge` now connects `gapGN` to difference quotients and `HasDerivAt`
+without mixing those concerns into the basic real bridge.
 
 ## Canonical Kernel Bridge
 
@@ -177,3 +180,52 @@ structure DkReal where
 Rational values embed as constant singleton interval sequences through
 `DkReal.ofRat`. Evaluation into Mathlib's real numbers remains deferred to a
 later semantic bridge.
+
+The nested interval API also includes arbitrary-stage control:
+
+```lean
+DkReal.lo_mono
+DkReal.hi_antitone
+DkReal.interval_subset_of_le
+DkReal.width_succ_le_width
+```
+
+These lemmas provide the order foundation needed by a future evaluation map and
+interval arithmetic.
+
+## Taylor And Derivative Bridge
+
+The center value of the exact gap kernel is:
+
+```lean
+gapGN_zero :
+  gapGN d base 0 = d * base^(d - 1)
+
+gapGN_succ_zero :
+  gapGN (d + 1) base 0 = (d + 1) * base^d
+```
+
+The successor form avoids natural-number truncated subtraction in the displayed
+exponent.
+
+Over the reals, `gapGN` is identified with the existing cosmic
+`powerKernel`. This yields:
+
+```lean
+continuous_gapGN
+tendsto_gapGN_zero
+powerDifferenceQuotient_eq_gapGN_of_ne_zero
+tendsto_powerDifferenceQuotient_zero
+hasDerivAt_pow_via_gapGN
+```
+
+The logical direction remains:
+
+```text
+exact algebraic factorization
+  -> exact gap kernel
+  -> zero-increment coefficient and limit
+  -> Mathlib HasDerivAt bridge
+```
+
+The derivative is not used to define the kernel.
````
`````
