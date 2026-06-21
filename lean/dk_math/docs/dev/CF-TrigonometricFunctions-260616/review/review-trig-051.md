# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2D

gch: 8e5b1e58790467553ec85b4002e9039da408ee1f

## Report

次の段階まで完了しました。

- `semanticKernelProduct`: 輸送後の実数核の積
- `semanticAct_comp`: action の合成則
- `semanticActLevel`: 任意の実数 `q2` level set 上の作用
- `semanticActLevel_comp`: level-set 上の合成則
- 古い semantic bridge TODO を更新

source 側には積・減算を要求せず、すべて `Real` 輸送後に構成しています。

全体ビルド成功、8566 jobs。`git diff --check` も成功です。

## Review

うむ。これは採用でよい。
今回の差分は、かなり大事な境界を正しく踏んでおる。

今回の要点は、DkNNRealQ 側では kernel 積を作らず、Real へ輸送した後でだけ kernel 積と action 合成を扱ったことじゃ。報告でも、`semanticKernelProduct`、`semanticAct_comp`、`semanticActLevel`、`semanticActLevel_comp` を追加し、source 側に積・減算を要求しない方針が明記されている。

## 総評

これは正しい。

前回までで、

```text
DkNNRealQ UnitKernel
  -> Real UnitKernel
  -> Real action
  -> q2 保存
```

まで来ていた。今回はそこに、

```text
Real 側 kernel product
  -> action composition
  -> level set action
  -> level set composition
```

が乗った。

つまり、DkNNRealQ 由来の kernel は、Real 上では合成可能な保存作用として振る舞うことが分かった。

## いちばん重要な点

`semanticKernelProduct` は Real 側だけに置いたのが正しい。

```lean
def semanticKernelProduct
    (r s : UnitKernel DkNNRealQ) : UnitKernel ℝ :=
  UnitKernel.star (semanticUnitKernel r) (semanticUnitKernel s)
```

これを source 側に戻そうとしない判断が肝じゃ。

理由は、Real 側の kernel 積では core が

$$
C_r C_s - S_r S_s
$$

になるからじゃ。

たとえ \(C_r,S_r,C_s,S_s\) が全部非負でも、この差は負になることがある。
つまり、第一象限 kernel 同士を合成すると、角度が進んで第二象限へ出る可能性がある。

だから一般には、

```text
semanticKernelProduct r s
```

が、ある DkNNRealQ の `UnitKernel` から来たものとは限らない。

ここを無理に source 側へ戻すと、非負半環の境界を破る。
今回それをしていない。これはとても良い。

## `semanticAct_comp` の評価

`semanticAct_comp` は既存の `UnitKernel.act_star` をそのまま消費している。

```lean
theorem semanticAct_comp
    (r s : UnitKernel DkNNRealQ) (z : Vec ℝ) :
    semanticAct r (semanticAct s z) =
      UnitKernel.act (semanticKernelProduct r s) z := by
  exact
    (UnitKernel.act_star
      (semanticUnitKernel r) (semanticUnitKernel s) z).symm
```

これは良い。
新しい代数を作らず、Real 側 CF2D の既存作用定理へ transport しているだけ。
つまり、semantic bridge の役割が明確じゃ。

この定理は、DkNNRealQ kernel が Real 側で「作用素」として合成可能であることを示しておる。

## `semanticActLevel` の評価

`semanticActLevel` も良い。

```lean
def semanticActLevel
    (r : UnitKernel DkNNRealQ) {rho2 : ℝ}
    (z : LevelSet ℝ rho2) : LevelSet ℝ rho2 :=
  LevelSet.act (semanticUnitKernel r) z
```

これは任意の (q2) level set を保つ作用じゃ。

つまり、単位円だけではなく、

$$
q2(z)=\rho2
$$

の任意 level に作用できる。

これは幾何的にかなり良い。
半径固定の円、あるいは square-mass 固定面上の自己写像として読める。

## `semanticActLevel_comp` の評価

Subtype ext で閉じているのも自然じゃ。

```lean
theorem semanticActLevel_comp
    (r s : UnitKernel DkNNRealQ) {rho2 : ℝ}
    (z : LevelSet ℝ rho2) :
    semanticActLevel r (semanticActLevel s z) =
      LevelSet.act (semanticKernelProduct r s) z := by
  apply Subtype.ext
  exact semanticAct_comp r s z.1
```

これは、level set 上でも Real 側 kernel 積による合成則が保たれることを示している。
`LevelSet` の proof 部分を直接触らず、値部分の等式で落としているので堅い。

## ここで得た意味

今回の到達点はこれじゃ。

```text
非負 DkMath kernel
  -> Real unit kernel
  -> Real q2-preserving action
  -> action composition
  -> arbitrary q2 level-set self-map
```

この時点で、DkNNRealQ は source として十分機能している。
signed DkReal がまだ無くても、Real 側の幾何作用はもう使える。

## 注意点

ただし、これはまだ「source 側の kernel family」ではない。

DkNNRealQ 上で、

```text
r ⋆ s
```

を作ったわけではない。
また、

```text
T -> UnitKernel DkNNRealQ
```

のような `KernelFamily` を source 側で作ったわけでもない。

今あるのは、

```text
r, s : UnitKernel DkNNRealQ
```

を個別に Real へ輸送し、Real 側で合成する構造じゃ。

この違いは重要。
文書で「No source-level kernel product is asserted」と書いているのは正しい。

## 次の一手

次は Real 側 consumer を増やすのがよい。

候補はこのあたりじゃ。

```text
semanticActLevel が level を保つことの利用例
第一象限 kernel による Real plane action の幾何解釈
semanticAct の反復
固定 level 上の orbit
```

一方で、source-level `Vec.star` と `KernelFamily` は signed DkReal 待ちでよい。
ここを急ぐと、非負層に減算を混ぜることになる。

## 判定

採用。かなり良い。

今回の実装は、あっさりしているが薄くない。
むしろ、境界が正しく切れているから薄く書けている。

わっちの結論はこうじゃ。

DkNNRealQ は非負 source として kernel を供給する。
Real 側では、その kernel が合成可能な \(q2\) 保存作用になる。
source 側へ無理に戻さない。
この分離ができたので、三角関数 Phase 2 の幾何 consumer へ進める。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index ea4a369d..493bc80f 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -80,7 +80,9 @@ comparison.
 
 [IMPLEMENTED: semantic-cf2d-action] `DkReal.SemanticCF2D` transports unit
 kernels to `Real`, derives the Pythagorean coordinate identity, and applies
-the resulting kernel as a real square-mass-preserving action.
+the resulting kernel as a real square-mass-preserving action. Transported
+actions compose through real-side kernel products and restrict to every real
+square-mass level set.
 
 [TODO: semantic-cf2d-signed] Source-level `Vec.star` and `KernelFamily` require
 signed arithmetic. Defer them until a signed DkReal layer exists.
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/DkNNRealQ.lean b/lean/dk_math/DkMath/Analysis/DkReal/DkNNRealQ.lean
index 0f4c900f..724028dd 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/DkNNRealQ.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/DkNNRealQ.lean
@@ -37,10 +37,14 @@ vanishing-width bound and exports `Std.Total (· ≤ ·)`.
 `DkReal.CanonicalOrder` subsequently proves
 `x ≤ y ↔ ∃ z, y = x + z` and installs `CanonicallyOrderedAdd`.
 
-[TODO: semantic-bridge] A semantic map to Mathlib's `NNReal` should be placed in a separate
-bridge module and proved to preserve zero, one, addition, multiplication,
-natural powers, and order. It should also provide an independent validation
-of any future internal totality theorem.
+[IMPLEMENTED: semantic-real-bridge] `DkMath.Analysis.DkReal.Semantic`
+constructs a representation-independent map to Mathlib `Real`, bundles it as
+a semiring homomorphism, and proves order preservation. The computable
+quotient core remains independent of that module.
+
+[TODO: semantic-nnreal-codomain] Add the optional codomain refinement to
+Mathlib `NNReal` only when a consumer benefits from carrying nonnegativity in
+the target type.
 -/
 
 namespace DkMath.Analysis
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
index eabf45e7..1254f04c 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
@@ -139,6 +139,53 @@ theorem semanticAct_preservesQ2 (r : UnitKernel DkNNRealQ) :
     PreservesQ2 (semanticAct r) :=
   semanticAct_q2 r
 
+/--
+Real-side product of two independently interpreted nonnegative DkMath
+kernels.
+
+The product is deliberately formed after semantic transport, where signed
+coordinates and subtraction are already available.
+-/
+def semanticKernelProduct
+    (r s : UnitKernel DkNNRealQ) : UnitKernel ℝ :=
+  UnitKernel.star (semanticUnitKernel r) (semanticUnitKernel s)
+
+/--
+Successive transported actions are action by the real-side product kernel.
+
+This records composition without asserting that a corresponding source-level
+product exists in the nonnegative semiring.
+-/
+theorem semanticAct_comp
+    (r s : UnitKernel DkNNRealQ) (z : Vec ℝ) :
+    semanticAct r (semanticAct s z) =
+      UnitKernel.act (semanticKernelProduct r s) z := by
+  exact
+    (UnitKernel.act_star
+      (semanticUnitKernel r) (semanticUnitKernel s) z).symm
+
+/-- Transported action restricted to a real square-mass level set. -/
+def semanticActLevel
+    (r : UnitKernel DkNNRealQ) {rho2 : ℝ}
+    (z : LevelSet ℝ rho2) : LevelSet ℝ rho2 :=
+  LevelSet.act (semanticUnitKernel r) z
+
+/-- The value of a transported level-set action is the ordinary semantic action. -/
+@[simp]
+theorem semanticActLevel_val
+    (r : UnitKernel DkNNRealQ) {rho2 : ℝ}
+    (z : LevelSet ℝ rho2) :
+    (semanticActLevel r z).1 = semanticAct r z.1 := rfl
+
+/-- Successive transported actions compose on every real level set. -/
+theorem semanticActLevel_comp
+    (r s : UnitKernel DkNNRealQ) {rho2 : ℝ}
+    (z : LevelSet ℝ rho2) :
+    semanticActLevel r (semanticActLevel s z) =
+      LevelSet.act (semanticKernelProduct r s) z := by
+  apply Subtype.ext
+  exact semanticAct_comp r s z.1
+
 /-
 [TODO: semantic-cf2d/signed-kernel] Source-level `Vec.star` and
 `KernelFamily` require a ring because their core coordinate uses subtraction.
diff --git a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
index f9425a16..d5cbfaaf 100644
--- a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
+++ b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
@@ -130,6 +130,8 @@ BridgeNNReal / BridgeReal:
   CF2D q2 and unit kernels are transported coordinatewise to Real
   transported kernels act on real vectors and preserve q2
   their coordinates satisfy the real Pythagorean identity
+  transported actions compose through real-side kernel products
+  every real q2 level set is stable under transported actions
   source-level star and KernelFamily wait for signed DkReal arithmetic
   treat order reflection as a separate heavier task
   compare semantic equality with DkReal.Equiv
diff --git a/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md b/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
index 2e1075c5..f35fccde 100644
--- a/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
+++ b/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
@@ -71,13 +71,22 @@ semanticUnitKernel
 semanticUnitKernel_sq_add_sq
 semanticAct
 semanticAct_q2
+semanticKernelProduct
+semanticAct_comp
+semanticActLevel
+semanticActLevel_comp
 ```
 
 The transported kernel now acts on real CF2D vectors and preserves `q2`.
 Subtraction appears only after transport to `Real`; it is not added to the
 nonnegative source semiring.
 
+Two transported actions compose through the product of their real unit
+kernels, and every real `q2` level set is stable under the transported action.
+No source-level kernel product is asserted.
+
 The next structural boundary is source-level `Vec.star` and `KernelFamily`.
 Both require signed arithmetic. They should wait for a signed DkReal layer
-rather than forcing subtraction into `DkNNRealQ`. Order reflection remains a
-separate, heavier task.
+rather than forcing subtraction into `DkNNRealQ`. Until then, further work can
+remain on the real side, for example first-quadrant geometric consumers.
+Order reflection remains a separate, heavier task.
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
index b67650a0..1e6c4ec8 100644
--- a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
@@ -211,3 +211,24 @@ Archive
    - order reflection も独立した重い課題として維持する。
 5. 検証:
    - `lake build DkMath.Analysis.DkReal.SemanticCF2D` 成功 (8273 jobs)。
+
+### 2026/06/22 00:49 JST (Real-side composition and level-set action)
+
+1. 方針:
+   - source-level kernel product は導入せず、二つの kernel を個別に Real へ
+     輸送した後でのみ積を取る。
+2. 実施:
+   - `semanticKernelProduct` を real unit-kernel product として定義した。
+   - `semanticAct_comp` で successive action と product action を接続した。
+   - `semanticActLevel` を追加し、任意の実数 `q2` level set 上の自己写像を
+     構成した。
+   - `semanticActLevel_comp` で level-set action の合成を証明した。
+   - `DkNNRealQ.lean` の semantic bridge TODO を実装済み状態へ更新した。
+3. 結論:
+   - DkNNRealQ 由来の kernel は、Real 上で合成可能な保存作用を生成する。
+   - source semiring に subtraction や kernel product を要求しない。
+4. 次の境界:
+   - source-level `Vec.star` / `KernelFamily` は signed DkReal 待ち。
+   - それまでは第一象限 kernel の Real 幾何 consumer を進められる。
+5. 検証:
+   - `lake build DkMath.Analysis.DkReal.SemanticCF2D` 成功 (8273 jobs)。
````
`````
