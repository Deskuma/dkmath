# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2D

gch: 89c760e39a96c0d143d7ffae9cac74be3ae28f1a

## Report

次の段階まで完了しました。

- semantic unit kernel の座標非負性
- 実数恒等式 `C² + S² = 1`
- 実数側 `semanticAct`
- action の座標式
- `semanticAct_q2` と `semanticAct_preservesQ2`
- 古い semantic TODO の整理

重要な境界も明記しました。`DkNNRealQ` には減算を追加せず、減算は semantic transport 後の `ℝ` 側 action にだけ現れます。

全体ビルド成功、8566 jobs。`git diff --check` も成功しています。

## Review

うむ。これは採用でよい。
今回の進展は、 **非負 DkNNRealQ の単位核を、減算なしで Real 側の回転作用へ渡せた** という点が大きい。

報告では、semantic unit kernel の座標非負性、実数恒等式 `C² + S² = 1`、`semanticAct`、座標式、`semanticAct_q2`、`semanticAct_preservesQ2` まで追加され、全体 build と `git diff --check` が通っている。

## 総評

これは前回の `semanticUnitKernel` の自然な次段じゃ。

前回までは、

```text
DkNNRealQ UnitKernel
  -> Real UnitKernel
```

までだった。今回はそこから、

```text
Real UnitKernel
  -> Real Vec への action
  -> q2 保存
```

まで進んだ。

しかも重要なのは、DkNNRealQ 側へ減算を入れていないことじゃ。
CF2D の core 座標には減算が出るので、source 側で無理に `Vec.star` を持たせると、非負実数層の設計を壊す。今回の実装は、減算を Real へ transport した後だけに限定している。これは正しい境界設計じゃ。

## 実装の良い点

`semanticUnitKernel_core_nonneg` と `semanticUnitKernel_beam_nonneg` は、地味だが良い補題じゃ。
DkNNRealQ 由来の kernel が Real 側でも第一象限の単位核として読めることを示している。

`semanticUnitKernel_sq_add_sq` も良い。

$$
C^2+S^2=1
$$

が semantic 座標で出る。これは、DkNNRealQ の `q2 = 1` が Real 側のピタゴラス恒等式へ輸送された形じゃ。ここまで来ると、三角関数的な読み替えがかなり自然になる。

`semanticAct` は、設計上かなり良い。

```lean
def semanticAct (r : UnitKernel DkNNRealQ) (z : Vec ℝ) : Vec ℝ :=
  UnitKernel.act (semanticUnitKernel r) z
```

つまり source は非負 DkNNRealQ のまま。
作用先は signed な Real vector。
減算は Real 側の既存 `UnitKernel.act` に任せる。

これはきれいじゃ。

## いちばん重要な点

`semanticAct_q2` が既存の `UnitKernel.q2_act` でそのまま閉じている点が強い。

```lean
theorem semanticAct_q2 (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
    Vec.q2 (semanticAct r z) = Vec.q2 z :=
  UnitKernel.q2_act (semanticUnitKernel r) z
```

これは「新しく解析を証明した」のではなく、既存 CF2D の保存定理へ semantic kernel を正しく渡せた、ということじゃ。

つまり、DkReal 解析層はここで初めて CF2D の既存定理を消費した。
これは milestone としてはかなり大きい。

## 境界判断は正しい

今回の TODO 更新も良い。

source-level `Vec.star` と `KernelFamily` を signed DkReal まで保留する判断は正しい。
理由は単純で、`Vec.star` の core は

$$
a x - b y
$$

を含む。非負半環だけでは、この値が非負に残る保証がない。
ここで無理に subtraction を DkNNRealQ へ生やすと、非負近似層の意味が崩れる。

だから現段階では、

```text
DkNNRealQ 側:
  非負座標、q2、UnitKernel、semantic transport

Real 側:
  減算ありの action、q2 保存
```

という分離が正しい。

## 注意点

ただし、この段階で得ている Real kernel は、source が DkNNRealQ なので core と beam が非負の単位核じゃ。

つまり Real 側では、

$$
C\ge 0,\quad S\ge 0,\quad C^2+S^2=1
$$

の範囲になる。幾何的には第一象限側の unit kernel じゃな。
全円の kernel family を source から直接作るには、やはり signed DkReal が必要になる。

これは弱点ではなく、正しい制約じゃ。
今は「非負世界から Real action へ入る入口」を作った段階と見るのがよい。

## 次の一手

次は、`semanticAct` の合成性を Real 側で確認するとよい。

たとえば、既存 CF2D に定理があるなら、

```text
semanticAct r (semanticAct s z)
```

が、

```text
UnitKernel.act ((semanticUnitKernel r) ⋆ (semanticUnitKernel s)) z
```

に対応することを見る。

ただし source 側で `r ⋆ s` を作るのは、signed arithmetic 待ちでよい。
今は Real 側だけの合成観察に留めるのが安全じゃ。

もう一つは、`semanticAct_preservesQ2` を使う consumer を一つ作ることじゃ。

```text
任意の z : Vec ℝ について、semanticAct r は q2 を保存する
```

これを「DkNNRealQ 由来 kernel が Real 上の square-mass-preserving map を生成する」として文書化するとよい。

## 判定

採用。かなり良い。

今回の到達点はこうじゃ。

```text
DkNNRealQ の非負 unit kernel
  -> Real unit kernel
  -> Real action
  -> q2 保存
```

そして、DkNNRealQ には減算を入れていない。
ここが一番偉い。

わっちの結論はこうじゃ。
**非負区間世界から Real の回転作用まで、設計境界を壊さずに接続できた。次は signed DkReal を待つ部分と、Real 側で消費できる部分を分けて進めるのがよい。**

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index bc7eca3c..ea4a369d 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -78,9 +78,12 @@ constants, addition, multiplication, natural powers, and canonical order.
 values reconstructs the canonical quotient order, without adding decidable
 comparison.
 
-[TODO: semantic-cf2d-analysis] Use the transported real `UnitKernel` as the
-input to the first CF2D analytic theorem. The algebraic `q2` transport is
-implemented separately in `DkReal.SemanticCF2D`.
+[IMPLEMENTED: semantic-cf2d-action] `DkReal.SemanticCF2D` transports unit
+kernels to `Real`, derives the Pythagorean coordinate identity, and applies
+the resulting kernel as a real square-mass-preserving action.
+
+[TODO: semantic-cf2d-signed] Source-level `Vec.star` and `KernelFamily` require
+signed arithmetic. Defer them until a signed DkReal layer exists.
 
 [TODO: signed-arithmetic] General signed multiplication requires the minimum and maximum of four
 endpoint products and belongs outside the current nonnegative API.
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/Equiv.lean b/lean/dk_math/DkMath/Analysis/DkReal/Equiv.lean
index 1af266fd..8db7d9d4 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/Equiv.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/Equiv.lean
@@ -32,9 +32,12 @@ monotonicity of interval separation under refinement: once a positive
 separation appears, nestedness prevents it from returning to zero. The reverse
 direction is immediate because every stage separation is zero.
 
-[TODO: semantic-bridge] For a future semantic evaluation `eval`, prove
-`Equiv x y → eval x = eval y` and, when justified by the representation
-theorem, the converse.
+[IMPLEMENTED: semantic-forward] `DkReal.semanticValue_eq_of_equiv` proves
+`Equiv x y → semanticValue x = semanticValue y`.
+
+[TODO: semantic-reflection] Prove the converse when needed. This is the
+representation-level equality-reflection problem and should remain separate
+from the computable definition of `Equiv`.
 -/
 
 namespace DkMath.Analysis.DkReal
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
index 2f260472..eabf45e7 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
@@ -80,6 +80,72 @@ def semanticUnitKernel (r : UnitKernel DkNNRealQ) : UnitKernel ℝ :=
 theorem semanticUnitKernel_val (r : UnitKernel DkNNRealQ) :
     (semanticUnitKernel r : Vec ℝ) = semanticVec (r : Vec DkNNRealQ) := rfl
 
+/-- The interpreted core coordinate remains nonnegative. -/
+theorem semanticUnitKernel_core_nonneg (r : UnitKernel DkNNRealQ) :
+    0 ≤ (semanticUnitKernel r : Vec ℝ).core :=
+  semanticValue_nonneg (r : Vec DkNNRealQ).core
+
+/-- The interpreted beam coordinate remains nonnegative. -/
+theorem semanticUnitKernel_beam_nonneg (r : UnitKernel DkNNRealQ) :
+    0 ≤ (semanticUnitKernel r : Vec ℝ).beam :=
+  semanticValue_nonneg (r : Vec DkNNRealQ).beam
+
+/--
+The coordinates of an interpreted nonnegative unit kernel satisfy the real
+Pythagorean identity.
+-/
+theorem semanticUnitKernel_sq_add_sq (r : UnitKernel DkNNRealQ) :
+    semanticValue (r : Vec DkNNRealQ).core ^ 2
+      + semanticValue (r : Vec DkNNRealQ).beam ^ 2 = 1 := by
+  simpa [Vec.q2, semanticVec] using
+    (UnitKernel.coe_q2 (semanticUnitKernel r))
+
+/--
+Act on a real CF2D vector by first interpreting a nonnegative DkMath unit
+kernel as a real unit kernel.
+
+Subtraction enters only in this real-side action. It is not added to
+`DkNNRealQ`.
+-/
+def semanticAct (r : UnitKernel DkNNRealQ) (z : Vec ℝ) : Vec ℝ :=
+  UnitKernel.act (semanticUnitKernel r) z
+
+/-- Core-coordinate formula for the transported real action. -/
+@[simp]
+theorem semanticAct_core (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
+    (semanticAct r z).core =
+      semanticValue (r : Vec DkNNRealQ).core * z.core
+        - semanticValue (r : Vec DkNNRealQ).beam * z.beam := rfl
+
+/-- Beam-coordinate formula for the transported real action. -/
+@[simp]
+theorem semanticAct_beam (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
+    (semanticAct r z).beam =
+      semanticValue (r : Vec DkNNRealQ).core * z.beam
+        + semanticValue (r : Vec DkNNRealQ).beam * z.core := rfl
+
+/--
+The transported real action preserves the CF2D quadratic invariant.
+
+This is the first direct consumer of an existing real-side CF2D action
+theorem. No new analytic argument is needed after the unit-kernel transport.
+-/
+theorem semanticAct_q2 (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
+    Vec.q2 (semanticAct r z) = Vec.q2 z :=
+  UnitKernel.q2_act (semanticUnitKernel r) z
+
+/-- The transported action is a square-mass-preserving real map. -/
+theorem semanticAct_preservesQ2 (r : UnitKernel DkNNRealQ) :
+    PreservesQ2 (semanticAct r) :=
+  semanticAct_q2 r
+
+/-
+[TODO: semantic-cf2d/signed-kernel] Source-level `Vec.star` and
+`KernelFamily` require a ring because their core coordinate uses subtraction.
+Keep the source in the nonnegative semiring until a signed DkReal layer is
+introduced; do not manufacture subtraction merely to mirror the real target.
+-/
+
 end
 
 end DkMath.Analysis.DkNNRealQ
diff --git a/lean/dk_math/DkMath/Analysis/RealBridge.lean b/lean/dk_math/DkMath/Analysis/RealBridge.lean
index 59b47f16..2dd2af26 100644
--- a/lean/dk_math/DkMath/Analysis/RealBridge.lean
+++ b/lean/dk_math/DkMath/Analysis/RealBridge.lean
@@ -16,12 +16,10 @@ The definitions in `DkMath.Analysis` are algebraic and remain meaningful over
 general rings. This file records their standard real interpretation and begins
 the bridge to Mathlib's topological and analytic API.
 
-This module concerns algebraic expressions already valued in `Real`. It is not
-the semantic evaluation bridge from `DkReal` or `DkNNRealQ`.
-
-[TODO] Keep the future representation-evaluation bridge in a distinct module,
-for example `DkMath.Analysis.DkReal.BridgeNNReal`, so importing elementary real
-continuity does not introduce a noncomputable dependency into Route B.
+This module concerns algebraic expressions already valued in `Real`. The
+semantic evaluation bridge from `DkReal` and `DkNNRealQ` is implemented
+separately in `DkMath.Analysis.DkReal.Semantic`; its CF2D consumer is isolated
+in `DkMath.Analysis.DkReal.SemanticCF2D`.
 -/
 
 namespace DkMath.Analysis
diff --git a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
index e1f1c363..f9425a16 100644
--- a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
+++ b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
@@ -128,7 +128,9 @@ BridgeNNReal / BridgeReal:
   canonical order preservation is proved by additive Gap extraction
   the semantic map is bundled as a semiring homomorphism to Real
   CF2D q2 and unit kernels are transported coordinatewise to Real
-  next consume the transported unit kernel in the analytic CF2D layer
+  transported kernels act on real vectors and preserve q2
+  their coordinates satisfy the real Pythagorean identity
+  source-level star and KernelFamily wait for signed DkReal arithmetic
   treat order reflection as a separate heavier task
   compare semantic equality with DkReal.Equiv
 ```
diff --git a/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md b/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
index 75f8b6a4..2e1075c5 100644
--- a/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
+++ b/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
@@ -68,7 +68,16 @@ semanticVec
 semanticValue_q2
 semanticValue_q2_eq
 semanticUnitKernel
+semanticUnitKernel_sq_add_sq
+semanticAct
+semanticAct_q2
 ```
 
-The next consumer should use the transported real `UnitKernel` in an analytic
-CF2D theorem. Order reflection remains a separate, heavier task.
+The transported kernel now acts on real CF2D vectors and preserves `q2`.
+Subtraction appears only after transport to `Real`; it is not added to the
+nonnegative source semiring.
+
+The next structural boundary is source-level `Vec.star` and `KernelFamily`.
+Both require signed arithmetic. They should wait for a signed DkReal layer
+rather than forcing subtraction into `DkNNRealQ`. Order reflection remains a
+separate, heavier task.
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
index b808b0f3..b67650a0 100644
--- a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
@@ -189,3 +189,25 @@ Archive
    - transported real `UnitKernel` を最初の CF2D 解析定理へ接続する。
    - order reflection は subtraction や decidable comparison を導入せず、
      独立課題として検討する。
+
+### 2026/06/21 23:29 JST (Real-side CF2D action without source subtraction)
+
+1. 方針:
+   - DkNNRealQ へ subtraction を追加せず、transport 後の `Real` 側でのみ
+     CF2D action を使う。
+2. 実施:
+   - semantic unit kernel の core / beam 非負性を証明した。
+   - semantic 座標について `C^2 + S^2 = 1` を証明した。
+   - `semanticAct` とその core / beam 座標式を追加した。
+   - 既存 `UnitKernel.q2_act` を直接消費し、`semanticAct_q2` と
+     `semanticAct_preservesQ2` を証明した。
+   - `Equiv.lean` と `RealBridge.lean` の完了済み future TODO を更新した。
+3. 結論:
+   - 非負区間世界から実数回転作用まで、source subtraction なしで接続した。
+   - subtraction は意味論輸送後の既知の `Real` 構造にだけ現れる。
+4. 境界:
+   - source-level `Vec.star` と `KernelFamily` は ring を要求するため、
+     signed DkReal 層まで保留する。
+   - order reflection も独立した重い課題として維持する。
+5. 検証:
+   - `lake build DkMath.Analysis.DkReal.SemanticCF2D` 成功 (8273 jobs)。
````
`````
