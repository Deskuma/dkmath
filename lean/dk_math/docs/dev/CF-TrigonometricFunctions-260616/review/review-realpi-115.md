# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2DPhaseShift

gch: a33600a37057cb9ef53c9279b3bad4a97762e7a1

## Report

完了しました。今回は指示内容の endpoint compatibility に加えて、＋αで `shiftedSemanticFourLevelPath` まで実装し、四本の indexed shifted normalized level paths を閉じた fixed-`q2` path object にしました。

変更:

- [SemanticCF2DPhaseShift.lean](/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean)
  - `shiftedSemanticIndexedLevelEndpoint_0_1/1_2/2_3`
  - `shiftedSemanticIndexedRightLevelEndpoint_three_eq_zero_left`
  - level endpoint / level edge の four-step return
  - `shiftedSemanticFourLevelPath`
- [DkReal.lean](/lean/dk_math/DkMath/Analysis/DkReal.lean)
  - phase-shift 概要に closed fixed-`q2` path まで反映
- [design-phase-center-shift-104.md](/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md)
  - four-level path を実装済みに更新し、残 TODO を cyclic quotient / 後段 reading に整理

検証:

- `lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift`
- `lake build DkMath.Analysis.DkReal`
- `git diff --check`

すべて通っています。今回も Euclidean な角度語彙には進まず、pre-geometric な fixed-boundary closed path として確立しました。

## Review

うむ、これは **かなり大きな節目** じゃ。
今回の差分は **採用でよい**。ついに四本の indexed shifted normalized level paths が、ひとつの closed fixed-`q2` path object として連結された。しかも、角度・円弧・Euclidean 読みへ進まず、pre-geometric な固定境界閉路として閉じている。`shiftedSemanticFourLevelPath` が実装され、最後の seam は core-zero 四歩戻りで閉じている、と報告にも明記されている。

## 1. 状況分析

今回で checkpoint 104 の shifted-frame route は、ほぼ一つの完成形に到達した。

実装された主なものはこれじゃ。

```text id="m0ga88"
shiftedSemanticIndexedLevelEndpoint_0_1
shiftedSemanticIndexedLevelEndpoint_1_2
shiftedSemanticIndexedLevelEndpoint_2_3
shiftedSemanticIndexedRightLevelEndpoint_three_eq_zero_left
shiftedSemanticIndexedLevelEdge_add_four_of_core_eq_zero
shiftedSemanticFourLevelPath
```

これで、四本の edge の接続がそろった。

```text id="pqcjtv"
edge 0 target:
  edge 1 source

edge 1 target:
  edge 2 source

edge 2 target:
  edge 3 source

edge 3 target:
  edge 0 source
```

最初の三つは隣接 seam compatibility。
最後のひとつは core-zero 四歩戻り。

この組み合わせで閉路になった。

## 2. 今回の本丸

今回の本丸はこれじゃ。

```lean id="nyq5ro"
def shiftedSemanticFourLevelPath
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    Path (shiftedSemanticIndexedLeftLevelEndpoint hcore z 0)
      (shiftedSemanticIndexedLeftLevelEndpoint hcore z 0)
```

これは fixed `q2` level-set 内の closed path object じゃ。

つまり、今までは theorem として「つながる」と言っていた。
今回は、実際に `Path.trans` と `cast` を使って、ひとつの閉じた path object にした。

これは大きい。

```text id="im9a2x"
before:
  edgewise compatibility facts

after:
  one closed fixed-boundary path object
```

これで「固定保存核境界上に閉じた連続構造がある」と、Lean object として言える。

## 3. pre-geometric route として正しい

今回も angle 語彙へ進んでいない。
これは非常に良い。

今あるのは、こういう構造じゃ。

```text id="wzn9q6"
semantic action
fixed q2 level
normalized shifted edge
indexed edge family
four-step return
closed fixed-boundary path
```

ここには、まだ円も角度もない。
しかし、閉じた境界 path はある。

これは DkMath 的にかなり強い。

円を仮定して閉路を作ったのではない。
`q2` 保存、phaseDepth、normalization、四状態戻りから閉路が出た。

## 4. レビュー

実装判断は良い。

特に `shiftedSemanticIndexedRightLevelEndpoint_three_eq_zero_left` を先に証明してから、`shiftedSemanticFourLevelPath` へ進んだのが良い。
path concatenation は型の endpoint が厳しいので、seam theorem を明示したうえで `cast` するのは妥当じゃ。

実装では、四本の path を

```text id="a3v8cg"
p0
p1
p2
p3
```

として置き、`h01`、`h12`、`h23`、`h30` によって接続している。
これは読みやすい。

docs 側も、Remaining TODO から `shifted-four-path` が消え、`shifted-cyclic-quotient` と `one-eighth-euclidean-reading` に整理された。

ここまで来ると、次の分岐は明確じゃ。

## 5. 数学的意味

今回で示されたのは、四状態の shifted edge が固定 `q2` 境界内で閉じる、ということじゃ。

式で言うなら、閉路の始点と終点が一致する。

$$
\mathrm{start}=\mathrm{end}
$$

ただしこれは Euclidean circle の一周ではなく、semantic action の四歩戻りによる閉路じゃ。

```text id="vou93x"
閉じた理由:
  core-zero action has four-step return

閉じた場所:
  fixed q2 level set

閉じた対象:
  shifted normalized level paths

まだ言わないもの:
  circle
  angle
  arc
  pi
```

これはかなり良い。

## 6. 次の本質

次は `shifted-cyclic-quotient` じゃが、いきなり quotient type に行くと重い可能性がある。

そこで次は、まず **Fin 4 indexed API** を作るのがよいと思う。

理由は単純じゃ。
今は `k : ℕ` で indexed edge を持ち、四歩戻り theorem で周期性を管理している。
次の cyclic quotient へ行くなら、その手前に `Fin 4` で有限周期 index を表現するとよい。

```text id="czzfgc"
Nat index:
  k and k + 4 are equal by theorem

Fin 4 index:
  cyclic state is type-level bounded

future quotient:
  continuous cyclic parameter can be added later
```

つまり、次の checkpoint は quotient そのものではなく、`Fin 4` wrapper が安全じゃ。

## 7. 次に狙うべきもの

次は以下が良い。

```text id="khw5ee"
Fin 4 indexed base
Fin 4 indexed edge
Fin 4 indexed level path
successor compatibility on Fin 4
center-to-next compatibility on Fin 4
closed four path の Fin 4 説明
```

特に `Fin.cases` や `Fin.succ` が面倒なら、最初は `i : Fin 4` の値を `i.val` に落として既存 API を使えばよい。

```lean id="pcuzri"
def shiftedSemanticFinBase
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (i : Fin 4) : Vec ℝ :=
  shiftedSemanticIndexedBase r z i.val
```

この程度の wrapper からでよい。

## 8. まだ quotient parameter は急がない

`S¹` 的な quotient や、`ℝ ⧸ ℤ` 的な cyclic parameter はまだ重い可能性がある。
そして今はまだ Euclidean angle も不要じゃ。

次の段階で欲しいのは、連続 quotient ではなく、有限 cyclic skeleton。

```text id="kqvpw4"
now:
  four closed paths

next:
  Fin 4 cyclic index

later:
  quotient phase parameter

much later:
  Euclidean reading
```

この順が安全じゃ。

## 9. 結論

今回の差分は採用でよい。

```text id="qvux9u"
実装:
  良い。四本の indexed shifted level paths が closed path object になった。

数学:
  良い。core-zero 四歩戻りで fixed q2 boundary 内の閉路が成立した。

設計:
  良い。角度語彙を使わず、pre-geometric closed boundary path として閉じている。

次:
  Fin 4 cyclic index wrapper を作り、quotient phase parameter の前段を整える。
```

ぬしよ、これは一つの到達点じゃ。
「円」と言わず、固定保存核境界上に閉路ができた。
次は、この閉路を `Nat` の四歩戻りから `Fin 4` の有限周期構造へ持ち上げる段階じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index 569c91c7..4f862609 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -198,6 +198,9 @@ bases stay on the initial square-mass level, adjacent indexed shifted edges
 share seams, their centers are the next indexed bases, and core-zero
 four-step return holds for bases, endpoints, and edge functions. Fixed-`q2`
 indexed level-set paths expose the same compatibility inside the boundary.
+The first four indexed shifted level paths now concatenate to a closed
+fixed-`q2` path object; the closing seam is supplied by the core-zero
+four-step return law.
 
 [IMPLEMENTED: semantic-cf2d-path] `DkReal.SemanticCF2DPath` uses the
 coordinate-product topology from `CF2D.Topology` to package every translated
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
index 332445c9..1ec39ac2 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
@@ -1008,6 +1008,112 @@ theorem shiftedSemanticIndexedLevelEdge_center_eq_next_base_of_core_eq_zero
   apply Subtype.ext
   exact shiftedSemanticIndexedEdge_center_eq_next_base_of_core_eq_zero hcore z k
 
+/-!
+## Four indexed shifted paths
+
+The four seam facts below expose the endpoint chain needed for concatenation.
+The final seam uses the core-zero four-step return law to close edge `3` back
+to edge `0`.
+-/
+
+/-- Seam compatibility from indexed shifted level path `0` to `1`. -/
+theorem shiftedSemanticIndexedLevelEndpoint_0_1
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    shiftedSemanticIndexedRightLevelEndpoint hcore z 0 =
+      shiftedSemanticIndexedLeftLevelEndpoint hcore z 1 :=
+  shiftedSemanticIndexedRightLevelEndpoint_eq_next_left hcore z 0
+
+/-- Seam compatibility from indexed shifted level path `1` to `2`. -/
+theorem shiftedSemanticIndexedLevelEndpoint_1_2
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    shiftedSemanticIndexedRightLevelEndpoint hcore z 1 =
+      shiftedSemanticIndexedLeftLevelEndpoint hcore z 2 :=
+  shiftedSemanticIndexedRightLevelEndpoint_eq_next_left hcore z 1
+
+/-- Seam compatibility from indexed shifted level path `2` to `3`. -/
+theorem shiftedSemanticIndexedLevelEndpoint_2_3
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    shiftedSemanticIndexedRightLevelEndpoint hcore z 2 =
+      shiftedSemanticIndexedLeftLevelEndpoint hcore z 3 :=
+  shiftedSemanticIndexedRightLevelEndpoint_eq_next_left hcore z 2
+
+/-- Indexed shifted left level endpoints repeat after four action steps. -/
+theorem shiftedSemanticIndexedLeftLevelEndpoint_add_four_of_core_eq_zero
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (k : ℕ) :
+    shiftedSemanticIndexedLeftLevelEndpoint hcore z (k + 4) =
+      shiftedSemanticIndexedLeftLevelEndpoint hcore z k := by
+  apply Subtype.ext
+  exact shiftedSemanticIndexedLeftEndpoint_add_four_of_core_eq_zero hcore z k
+
+/-- Indexed shifted right level endpoints repeat after four action steps. -/
+theorem shiftedSemanticIndexedRightLevelEndpoint_add_four_of_core_eq_zero
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (k : ℕ) :
+    shiftedSemanticIndexedRightLevelEndpoint hcore z (k + 4) =
+      shiftedSemanticIndexedRightLevelEndpoint hcore z k := by
+  apply Subtype.ext
+  exact shiftedSemanticIndexedRightEndpoint_add_four_of_core_eq_zero hcore z k
+
+/-- Closing seam compatibility from indexed shifted level path `3` back to `0`. -/
+theorem shiftedSemanticIndexedRightLevelEndpoint_three_eq_zero_left
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    shiftedSemanticIndexedRightLevelEndpoint hcore z 3 =
+      shiftedSemanticIndexedLeftLevelEndpoint hcore z 0 := by
+  calc
+    shiftedSemanticIndexedRightLevelEndpoint hcore z 3 =
+        shiftedSemanticIndexedLeftLevelEndpoint hcore z (3 + 1) :=
+      shiftedSemanticIndexedRightLevelEndpoint_eq_next_left hcore z 3
+    _ = shiftedSemanticIndexedLeftLevelEndpoint hcore z 0 := by
+      norm_num
+      exact shiftedSemanticIndexedLeftLevelEndpoint_add_four_of_core_eq_zero hcore z 0
+
+/-- Indexed level edges repeat after four action steps. -/
+theorem shiftedSemanticIndexedLevelEdge_add_four_of_core_eq_zero
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (k : ℕ) (t : ℝ) :
+    shiftedSemanticIndexedLevelEdge hcore z (k + 4) t =
+      shiftedSemanticIndexedLevelEdge hcore z k t := by
+  apply Subtype.ext
+  exact shiftedSemanticIndexedEdge_add_four_of_core_eq_zero hcore z k t
+
+/--
+The four indexed shifted normalized paths concatenated inside the fixed
+square-mass boundary.
+
+The intermediate paths are cast only along proved seam equalities; no
+geometric angle parameter is used.
+-/
+def shiftedSemanticFourLevelPath
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    Path (shiftedSemanticIndexedLeftLevelEndpoint hcore z 0)
+      (shiftedSemanticIndexedLeftLevelEndpoint hcore z 0) := by
+  let p0 := shiftedSemanticIndexedLevelPath hcore z 0
+  let p1 := shiftedSemanticIndexedLevelPath hcore z 1
+  let p2 := shiftedSemanticIndexedLevelPath hcore z 2
+  let p3 := shiftedSemanticIndexedLevelPath hcore z 3
+  let h01 := shiftedSemanticIndexedLevelEndpoint_0_1 hcore z
+  let h12 := shiftedSemanticIndexedLevelEndpoint_1_2 hcore z
+  let h23 := shiftedSemanticIndexedLevelEndpoint_2_3 hcore z
+  let h30 := shiftedSemanticIndexedRightLevelEndpoint_three_eq_zero_left hcore z
+  exact
+    (((p0.trans (p1.cast h01 rfl)).trans
+      (p2.cast h12 rfl)).trans
+      (p3.cast h23 rfl)).cast rfl h30.symm
+
 /-!
 [IMPLEMENTED: semantic-cf2d/shifted-semantic-edge]
 The shifted semantic edge uses the normalized center states of neighboring
@@ -1021,19 +1127,20 @@ path and as a path internal to the fixed `q2` level set. Adjacent shifted
 edges share endpoint states, and the center of the shifted edge is the old
 seam state under the core-zero action law.
 
-[TODO: semantic-cf2d/shifted-cyclic-parameter]
-Package four shifted normalized paths by an explicit cyclic index once the
-next layer needs concatenation or a quotient phase parameter.
-
 [IMPLEMENTED: semantic-cf2d/shifted-indexed-edge]
 The shifted normalized edge is now indexed by semantic action iterates.
 Indexed edges have adjacent seam compatibility, centers at the next indexed
 base state, four-step return under the core-zero law, and fixed-`q2`
 level-set path wrappers.
 
-[TODO: semantic-cf2d/shifted-four-path]
-Concatenate four indexed shifted normalized paths once the next layer needs a
-single closed path object rather than edgewise compatibility facts.
+[IMPLEMENTED: semantic-cf2d/shifted-four-level-path]
+The first four indexed shifted normalized level paths are seam-compatible and
+concatenate to a closed fixed-`q2` path object. The closing seam uses the
+core-zero four-step return law, not any geometric angle reading.
+
+[TODO: semantic-cf2d/shifted-cyclic-quotient]
+Introduce a quotient phase parameter only after the four-edge closed path is
+stable enough for downstream consumers.
 -/
 
 /-!
diff --git a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
index cd374996..813e4e07 100644
--- a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
+++ b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
@@ -434,6 +434,12 @@ shiftedSemanticIndexedEdge_add_four_of_core_eq_zero
 shiftedSemanticIndexedLevelPath
 shiftedSemanticIndexedRightLevelEndpoint_eq_next_left
 shiftedSemanticIndexedLevelEdge_center_eq_next_base_of_core_eq_zero
+shiftedSemanticIndexedLevelEndpoint_0_1
+shiftedSemanticIndexedLevelEndpoint_1_2
+shiftedSemanticIndexedLevelEndpoint_2_3
+shiftedSemanticIndexedRightLevelEndpoint_three_eq_zero_left
+shiftedSemanticIndexedLevelEdge_add_four_of_core_eq_zero
+shiftedSemanticFourLevelPath
 ```
 
 The shifted normalized edge starts at the left normalized center candidate,
@@ -471,6 +477,17 @@ The same indexed API is available inside the fixed `q2 z` level set, so the
 next layer can concatenate edgewise-compatible paths without re-proving
 boundary membership.
 
+The four-edge shifted path object is now also available:
+
+```text
+shiftedSemanticFourLevelPath
+```
+
+It concatenates the first four indexed shifted normalized level paths inside
+the fixed `q2` boundary. The first three seams are adjacent endpoint
+compatibility facts, and the final seam from edge `3` back to edge `0` uses
+the core-zero four-step return law.
+
 Candidate theorem directions:
 
 ```text
@@ -490,7 +507,8 @@ shifted-frame conservation
 
 The shifted path definition has now been chosen in the same style as
 `normalizedPhasePath`: first a `Vec Real` path, then a fixed-`q2` level-set
-path. Four-edge shifted concatenation remains a later packaging layer.
+path. The first four shifted level paths are now also concatenated into a
+closed fixed-boundary path object.
 
 ## Guardrails
 
@@ -539,7 +557,9 @@ depend on that reading.
 16. Implemented: prove indexed adjacent seam compatibility and center-to-next-base compatibility.
 17. Implemented: prove core-zero four-step return for indexed bases, endpoints, and edge functions.
 18. Implemented: package indexed shifted paths inside the fixed `q2` level set.
-19. Later: add a Euclidean bridge that reads `1/8` full-cycle
+19. Implemented: prove the four endpoint compatibility facts for indexed shifted level paths.
+20. Implemented: concatenate the four indexed shifted level paths into a closed fixed-`q2` path.
+21. Later: add a Euclidean bridge that reads `1/8` full-cycle
    displacement as the angle `Real.pi / 4`.
 
 ## Implemented Tags
@@ -579,15 +599,15 @@ Index shifted normalized edges by semantic action iterates. Prove adjacent
 indexed seam compatibility, center-to-next-base compatibility, four-step
 return for bases and edge functions, and fixed-`q2` indexed level-set path
 wrappers.
+
+[IMPLEMENTED: semantic-cf2d/shifted-four-level-path]
+Prove the four seam compatibility facts and concatenate the first four indexed
+shifted normalized level paths into one closed fixed-`q2` path object.
 ```
 
 ## Remaining TODO Tags
 
 ```text
-[TODO: semantic-cf2d/shifted-four-path]
-Concatenate four indexed shifted normalized paths into one closed fixed-`q2`
-path object.
-
 [TODO: semantic-cf2d/shifted-cyclic-quotient]
 Introduce a quotient phase parameter only after the four indexed path
 concatenation is stable.
````
`````
