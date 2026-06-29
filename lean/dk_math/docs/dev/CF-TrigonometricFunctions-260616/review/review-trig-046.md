# Git diff / Report / Review

## Add: Analysis.DkReal.Semantic

gch: 0d5cf697d8d2e4dff217a7303aace73d1e503fb4

## Report

三角関数の実数解析本線へ戻り、semantic bridge の実装を開始しました。

追加:

- `DkReal.Semantic`
  - lower/upper endpoint の実数化
  - lower endpoint の単調性・上方有界性
  - `semanticValue : DkReal → ℝ`
  - 全近似区間への所属
  - lower endpoint の単調収束
- `task-trig-real-analysis-046.md`
- `History.md` の現場記録
- 公開 import と管理文書の更新

LinearOrder と decidable comparison は明示的に後回しです。

```text
lake build DkMath.Analysis.DkReal DkMath.Analysis DkMath
Build completed successfully (8565 jobs).
```

次は semantic point の一意性と、`Equiv x y → semanticValue x = semanticValue y` です。

## Review

## 1. 総評

ぬしよ、これは **正しい続行方向** じゃ。  
今回の `DkMath.Analysis.DkReal.Semantic` は、三角関数 CF2D Phase 1 の代数核から、実数解析 Phase 2 へ移るための最初の橋としてかなり筋が良い。

過去ログ・設計書では、DkMath.Analysis は Mathlib 解析を置き換える層ではなく、Gap / Body / GN の語彙で解析対象を再解釈する層と定義されていた。さらに、Route B の `DkReal` は計算可能な区間近似核で、Mathlib `Real` への意味論写像は別層として扱う方針だった。今回の `semanticValue` は、まさにその「別層」の入口になっている。

添付 diff 上では、`semanticValue : DkReal → ℝ` を lower endpoint の上限として定義し、全近似区間への所属と lower endpoint の単調収束まで閉じている。さらに build 成功も報告されている。

結論として、今回の実装は **採用でよい** 。  
ただし、次に進む前に 2 点だけ修正・補強した方がよい。

## 2. 実装の数学的妥当性

今回の意味論値は、

\[
\operatorname{semanticValue}(x)=\sup_n \operatorname{lowerReal}(x,n)
\]

として定義されている。

これはよい。理由は明確じゃ。

`lowerReal_monotone` で lower endpoint が単調増加する。  
`lowerReal_le_upperReal` で任意の upper endpoint が lower endpoint 全体の上界になる。  
したがって lower endpoint の上限が存在し、その値は全区間に入る。

この流れは、入れ子有理区間から実数値を取り出す標準的で堅い方法じゃ。しかも「全区間に属する」まで証明しているので、意味論値の候補としては十分に強い。

特に良いのは、Mathlib `Real` の完備性が `semanticValue` の一点に隔離されていることじゃ。DkReal の演算層は、これまでのマイルストーン通り、 rational endpoints と有限代数で閉じており、`noncomputable` な意味論層とは分離されている。

## 3. 良い点

まず、`LinearOrder` と decidable comparison を後回しにした判断は正しい。今回必要なのは DkReal 自体の線形順序ではなく、Mathlib `Real` 側で上限を取ることじゃ。DkReal の比較問題を無理に解かず、semantic bridge にだけ古典的完備性を使うのは安全な設計じゃ。

次に、`lowerReal_le_upperReal` がよい。これは単に同じ stage の `lo ≤ hi` を示すだけでなく、任意の \(m,n\) について、

\[
\operatorname{lowerReal}(x,m)\le \operatorname{upperReal}(x,n)
\]

を示している。これにより、どの upper endpoint も lower sequence 全体の上界になる。ここが `semanticValue_le_upperReal` に効いておる。

また、`tendsto_lowerReal_semanticValue` をここで入れたのも良い。次の `Equiv` 不変性は、まさに「lower endpoint の差が 0 に収束する」ことと「lower endpoint が semanticValue に収束する」ことを突き合わせれば落とせる。

## 4. 注意点その一：一意性には width が必要

今回の `semanticValue_mem_interval` は、意味論点が全区間に入ることを示している。だが、これだけでは **一意性** は出ない。

たとえば区間列がずっと \([0,1]\) のままなら、lower supremum は \(0\) だが、全区間に入る点は無数にある。もちろん実際の `DkReal` には width が 0 に近づく条件があるはずなので、次はそれを使う必要がある。

次に欲しい補題はこれじゃ。

```lean
def widthReal (x : DkMath.Analysis.DkReal) (n : ℕ) : ℝ :=
  upperReal x n - lowerReal x n

theorem tendsto_widthReal_zero
    (x : DkMath.Analysis.DkReal) :
    Filter.Tendsto (widthReal x) Filter.atTop (nhds 0) := by
  ...
```

その上で、全区間に入る点の一意性をこう閉じる。

```lean
theorem eq_semanticValue_of_mem_all_intervals
    (x : DkMath.Analysis.DkReal) (r : ℝ)
    (hr : ∀ n, r ∈ Set.Icc (lowerReal x n) (upperReal x n)) :
    r = semanticValue x := by
  ...
```

証明方針は、`r` と `semanticValue x` がどちらも同じ区間に入るので、

\[
|r-\operatorname{semanticValue}(x)|\le \operatorname{upperReal}(x,n)-\operatorname{lowerReal}(x,n)
\]

を任意の \(n\) で示す。右辺が \(0\) に収束するので、左辺は \(0\)。よって等しい。

これはかなり再利用価値が高い補題になる。

## 5. 注意点その二：公開 import の説明が少し矛盾している

ここは小さいが、賢狼としては見逃さぬ。

`DkReal.lean` に `DkReal.Semantic` を public import したことで、`DkMath.Analysis.DkReal` を import すると `semanticValue` も見えるようになる。これは実装上は問題ない。

ただし、diff 内の説明にはまだ「この import tree では Mathlib `Real` の represented limit を選ばない」という趣旨の古い文が残っておる。一方で今回の `DkReal.Semantic` は lower endpoint supremum として `semanticValue` を選んでいる。

ここは文書をこう直すのがよい。

```text
All endpoint operations in the computable representation layer remain computable.
The optional Semantic module selects a Mathlib Real value noncomputably.
```

または、より厳密に分けるなら、`DkMath.Analysis.DkReal` は計算可能核だけに留め、`DkMath.Analysis.DkReal.Semantic` は明示 import にする手もある。

わっちの推奨は、今のまま public import するなら **文書側を修正** じゃ。実装の利便性を優先してよい。ただし「計算可能核」と「意味論橋」の境界説明は濁らせぬ方がよい。

## 6. 次の実装順序

次はこの順がよい。

```lean
theorem tendsto_widthReal_zero
    (x : DkMath.Analysis.DkReal) :
    Filter.Tendsto (widthReal x) Filter.atTop (nhds 0)
```

次に、

```lean
theorem eq_semanticValue_of_mem_all_intervals
    (x : DkMath.Analysis.DkReal) (r : ℝ)
    (hr : ∀ n, r ∈ Set.Icc (lowerReal x n) (upperReal x n)) :
    r = semanticValue x
```

その次に本命。

```lean
theorem semanticValue_eq_of_equiv
    {x y : DkMath.Analysis.DkReal}
    (hxy : DkMath.Analysis.DkReal.Equiv x y) :
    semanticValue x = semanticValue y
```

報告書にもある通り、ここは既存候補の `equiv_tendsto_lo_sub_zero`、今回追加の `tendsto_lowerReal_semanticValue`、そして `Real` での極限一意性を使うのが最短じゃ。

証明の骨格はこうなる。

```lean
have hx :
    Filter.Tendsto (lowerReal x) Filter.atTop (nhds (semanticValue x)) :=
  tendsto_lowerReal_semanticValue x

have hy :
    Filter.Tendsto (lowerReal y) Filter.atTop (nhds (semanticValue y)) :=
  tendsto_lowerReal_semanticValue y

have hxy0 :
    Filter.Tendsto
      (fun n => lowerReal x n - lowerReal y n)
      Filter.atTop
      (nhds 0) := by
  ...

have hlim :
    Filter.Tendsto
      (fun n => lowerReal x n - lowerReal y n)
      Filter.atTop
      (nhds (semanticValue x - semanticValue y)) := by
  exact hx.sub hy

have hzero : semanticValue x - semanticValue y = 0 := by
  exact tendsto_nhds_unique hlim hxy0

exact sub_eq_zero.mp hzero
```

実際には `equiv_tendsto_lo_sub_zero` が \(\mathbb{Q}\) 側の差分収束なら、`Rat.cast` して `Real` へ移す補助補題が一枚必要になるはずじゃ。

## 7. CF2D Phase 2 との接続先

代表元独立が閉じたら、すぐに `DkNNRealQ` へ降ろす。ここが終わるまでは、CF2D へ直接つなぐのはまだ早い。

流れはこれでよい。

```text
DkReal
  -> semanticValue
  -> Equiv 不変
  -> DkNNRealQ.semanticValue
  -> map_zero / map_one / map_add / map_mul_nonneg / map_pow
  -> q2 保存の意味論 bridge
  -> CF2D UnitKernel の Real 解釈
```

三角関数側で最初に消費すべき定理は、角度復元や周期性ではなく、まず保存量の意味論保存じゃ。

\[
Q(r\star z)=Q(r)Q(z)
\]

を DkReal / DkNNRealQ で持ち、semantic map 後にも同じ式が Mathlib `Real` 上で成立する、という橋を最初に作るのがよい。角度、連続パラメータ、周期性、微分はその後じゃ。

## 8. 判定

今回の差分は **Phase 2 の第一歩として合格** じゃ。

ただし、完了ではない。今の状態は、

```text
semantic point を選んだ
全 interval に入ることを証明した
lower endpoint がそこへ収束することを証明した
```

までじゃ。

次に、

```text
その point が一意である
Equiv で不変である
quotient に降ろせる
演算を保つ
```

まで行って、初めて CF2D 解析消費者へ渡せる。

わっちの総合評価はこうじゃ。

**実装方向は正しい。数学的にも Lean 設計としても筋がよい。次の勝負所は width zero を使った一意性と、`Equiv` 不変性。ここを閉じれば、DkReal は本当に Mathlib `Real` へ橋を架け始める。**

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index fe285dbc..16978094 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -14,6 +14,7 @@ import DkMath.Analysis.DkReal.DkNNReal
 import DkMath.Analysis.DkReal.DkNNRealQ
 import DkMath.Analysis.DkReal.Order
 import DkMath.Analysis.DkReal.CanonicalOrder
+import DkMath.Analysis.DkReal.Semantic
 
 #print "file: DkMath.Analysis.DkReal"
 
@@ -28,6 +29,7 @@ Public entry point for the complete Route B algebraic checkpoint:
 * `DkNNReal` packages nonnegativity;
 * `DkNNRealQ` is the quotient-backed nonnegative ordered `CommSemiring`;
 * `DkReal.CanonicalOrder` extracts nonnegative Gap universes.
+* `DkReal.Semantic` begins the noncomputable bridge to Mathlib's `Real`.
 
 All endpoint operations in this import tree remain computable. No represented
 limit in Mathlib's `Real` or `NNReal` is selected here.
@@ -66,9 +68,12 @@ a linear order.
 decision procedure for asymptotic interval order is currently available.
 Classical comparison should therefore remain an explicit local choice.
 
-[TODO: semantic-bridge] Add `BridgeNNReal.lean` / `BridgeReal.lean` only after proving that the
-chosen evaluation is independent of representatives. Such evaluation may
-legitimately be `noncomputable`.
+`DkReal.Semantic` now selects the lower-endpoint supremum and proves that it
+lies in every approximation interval.
+
+[TODO: semantic-bridge] Prove that semantic evaluation is independent of
+representatives, then lift it to `DkNNRealQ` and establish arithmetic and order
+bridge laws.
 
 [TODO: signed-arithmetic] General signed multiplication requires the minimum and maximum of four
 endpoint products and belongs outside the current nonnegative API.
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/Semantic.lean b/lean/dk_math/DkMath/Analysis/DkReal/Semantic.lean
new file mode 100644
index 00000000..bf310158
--- /dev/null
+++ b/lean/dk_math/DkMath/Analysis/DkReal/Semantic.lean
@@ -0,0 +1,107 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Analysis.DkReal.Equiv
+
+#print "file: DkMath.Analysis.DkReal.Semantic"
+
+/-!
+# Semantic real value of a DkReal representation
+
+This module begins the noncomputable bridge from nested rational intervals to
+Mathlib's `Real`.
+
+The represented value is the supremum of the lower endpoints after casting
+them to `Real`. Nestedness makes this sequence monotone, while every upper
+endpoint bounds it. Consequently the supremum lies in every approximation
+interval.
+
+This file deliberately stops before quotient descent and arithmetic
+preservation. Those require representative independence of `semanticValue`.
+
+[TODO: semantic/equiv] Prove
+`DkReal.Equiv x y -> semanticValue x = semanticValue y`.
+
+[TODO: semantic/quotient] Lift the value through `DkNNRealQ`, then prove
+preservation of zero, one, addition, nonnegative multiplication, powers, and
+order.
+-/
+
+namespace DkMath.Analysis.DkReal
+
+noncomputable section
+
+/-- Lower endpoint of a representation, interpreted in Mathlib's `Real`. -/
+def lowerReal (x : DkMath.Analysis.DkReal) (n : ℕ) : ℝ :=
+  (x.interval n).lo
+
+/-- Upper endpoint of a representation, interpreted in Mathlib's `Real`. -/
+def upperReal (x : DkMath.Analysis.DkReal) (n : ℕ) : ℝ :=
+  (x.interval n).hi
+
+/-- Cast lower endpoints form a monotone real sequence. -/
+theorem lowerReal_monotone (x : DkMath.Analysis.DkReal) :
+    Monotone (lowerReal x) := by
+  intro n m hnm
+  simp only [lowerReal]
+  exact_mod_cast x.lo_mono hnm
+
+/-- Every fixed upper endpoint bounds all cast lower endpoints. -/
+theorem lowerReal_le_upperReal
+    (x : DkMath.Analysis.DkReal) (n m : ℕ) :
+    lowerReal x m ≤ upperReal x n := by
+  simp only [lowerReal, upperReal]
+  by_cases hmn : m ≤ n
+  · exact_mod_cast
+      (x.lo_mono hmn).trans (x.interval n).le_lo_hi
+  · have hnm : n ≤ m := le_of_not_ge hmn
+    exact_mod_cast
+      (x.interval m).le_lo_hi.trans (x.hi_antitone hnm)
+
+/-- The range of cast lower endpoints is bounded above. -/
+theorem bddAbove_range_lowerReal (x : DkMath.Analysis.DkReal) :
+    BddAbove (Set.range (lowerReal x)) := by
+  refine ⟨upperReal x 0, ?_⟩
+  rintro _ ⟨n, rfl⟩
+  exact lowerReal_le_upperReal x 0 n
+
+/--
+The semantic real represented by a nested interval sequence.
+
+Completeness enters exactly here, through the conditionally complete order on
+Mathlib's real numbers.
+-/
+def semanticValue (x : DkMath.Analysis.DkReal) : ℝ :=
+  ⨆ n, lowerReal x n
+
+/-- Every lower endpoint is below the represented semantic value. -/
+theorem lowerReal_le_semanticValue
+    (x : DkMath.Analysis.DkReal) (n : ℕ) :
+    lowerReal x n ≤ semanticValue x := by
+  exact le_ciSup (bddAbove_range_lowerReal x) n
+
+/-- The represented semantic value is below every upper endpoint. -/
+theorem semanticValue_le_upperReal
+    (x : DkMath.Analysis.DkReal) (n : ℕ) :
+    semanticValue x ≤ upperReal x n := by
+  apply ciSup_le
+  intro m
+  exact lowerReal_le_upperReal x n m
+
+/-- The semantic value belongs to every cast approximation interval. -/
+theorem semanticValue_mem_interval
+    (x : DkMath.Analysis.DkReal) (n : ℕ) :
+    semanticValue x ∈ Set.Icc (lowerReal x n) (upperReal x n) :=
+  ⟨lowerReal_le_semanticValue x n, semanticValue_le_upperReal x n⟩
+
+/-- Cast lower endpoints converge monotonically to the semantic value. -/
+theorem tendsto_lowerReal_semanticValue (x : DkMath.Analysis.DkReal) :
+    Filter.Tendsto (lowerReal x) Filter.atTop (nhds (semanticValue x)) := by
+  exact tendsto_atTop_ciSup (lowerReal_monotone x) (bddAbove_range_lowerReal x)
+
+end
+
+end DkMath.Analysis.DkReal
diff --git a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
index 135f06f5..bacfe9ab 100644
--- a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
+++ b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
@@ -82,6 +82,10 @@ DkMath.Analysis.DkReal.CanonicalOrder
   subtraction-free extraction of a nonnegative Gap representation,
   ExistsAddOfLE, and CanonicallyOrderedAdd
 
+DkMath.Analysis.DkReal.Semantic
+  noncomputable lower-endpoint supremum in Mathlib Real, interval membership,
+  and monotone endpoint convergence
+
 DkMath.Analysis.DkReal
   public entry point for the computable approximation layer
 ```
@@ -118,8 +122,8 @@ Order:
   use a semantic bridge only as an independent cross-check
 
 BridgeNNReal / BridgeReal:
-  select the unique semantic limit
-  prove representative independence
+  semanticValue now selects the lower-endpoint supremum
+  next prove representative independence and uniqueness
   prove semiring-homomorphism laws
   compare semantic equality with DkReal.Equiv
 ```
diff --git a/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md b/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
new file mode 100644
index 00000000..55714625
--- /dev/null
+++ b/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
@@ -0,0 +1,49 @@
+# Task 046: Return to the Trigonometric Real-Analysis Route
+
+## Policy
+
+`LinearOrder` and decidable comparison are deferred. The current public order
+surface remains `PartialOrder + Std.Total + IsStrictOrderedRing`.
+
+PowerSwap comparison research is complete enough to resume later, but it is
+not on the critical path for the trigonometric real-analysis layer.
+
+## Current Main Line
+
+CF2D Phase 1 already supplies the algebraic source of the trigonometric
+coordinate identities. The next main-line requirement is a semantic bridge
+from the Route B interval representation to Mathlib real analysis:
+
+```text
+DkReal representation
+  -> unique Mathlib Real value
+  -> representative independence
+  -> DkNNRealQ semantic map
+  -> arithmetic and order preservation
+  -> analytic CF2D consumers
+```
+
+## Checkpoints
+
+1. Define the semantic value of a `DkReal` representation.
+2. Prove that it belongs to every approximation interval.
+3. Prove uniqueness of a real point belonging to every interval.
+4. Prove invariance under `DkReal.Equiv`.
+5. Lift the map to `DkNNRealQ`.
+6. Prove zero, one, addition, multiplication, power, and order bridge laws.
+7. Reassess which CF2D Phase 2 theorem should consume this bridge first.
+
+## Current Implementation Step
+
+`DkMath.Analysis.DkReal.Semantic` implements the lower-endpoint supremum,
+boundedness, interval membership, and monotone convergence.
+
+The next obligation is representative independence. It should use:
+
+```text
+equiv_tendsto_lo_sub_zero
+tendsto_lowerReal_semanticValue
+uniqueness of limits in Real
+```
+
+No global decidable comparison or `LinearOrder` instance is needed.
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
index 85e85f13..42589462 100644
--- a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
@@ -87,3 +87,30 @@ Archive
 - `git diff --check` 成功
 
 補足: 既に index に載っていた前回追加分があるため、`git status` では旧 staged との差分として `AM` と新 `CF2D` untracked が混ざって見えています。staging は触っていません。
+
+### 2026/06/21 19:54 JST (Return to the trigonometric real-analysis route)
+
+1. 目的:
+   - `LinearOrder` と decidable comparison を独立保留課題とし、CF2D
+     Phase 2 に必要な実数解析本線へ戻る。
+   - 現場管理文書と TODO を再確認し、次の実装可能な checkpoint を定める。
+2. 実施:
+   - `DkMath.Analysis.DkReal.Semantic` を追加した。
+   - lower endpoint の実数列を定義し、単調性と上方有界性を証明した。
+   - semantic value を lower endpoint の上限として noncomputable に定義した。
+   - semantic value が全 approximation interval に属することを証明した。
+   - lower endpoint が semantic value へ単調収束することを証明した。
+   - `task-trig-real-analysis-046.md` に semantic bridge の実装順を記録した。
+3. 結論:
+   - Route B の計算可能核を変更せず、Mathlib `Real` の completeness を
+     semantic bridge にだけ導入できた。
+   - 次の主課題は `DkReal.Equiv` による semantic value の不変性である。
+4. 検証:
+   - `lake build DkMath.Analysis.DkReal.Semantic` 成功。
+5. 失敗事例:
+   - 最初のビルドでは `lowerReal` / `upperReal` が未展開のため
+     `exact_mod_cast` が型一致しなかった。定義を明示展開して修正した。
+6. 次の課題:
+   - 全区間に属する実数点の一意性を証明する。
+   - `Equiv x y -> semanticValue x = semanticValue y` を証明する。
+   - その後 `DkNNRealQ` へ semantic map を降ろす。
````
`````
