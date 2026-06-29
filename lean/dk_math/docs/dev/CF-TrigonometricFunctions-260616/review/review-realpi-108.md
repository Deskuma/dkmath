# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2DPhaseShift

gch: 55c2ee6aa1adc75ebfe4d73153dbe063360475a7

## Report

Goal まで進めました。

[SemanticCF2DPhaseShift.lean](/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean) に shifted-frame scalar API を追加しています。

追加した主な定義・定理:

```lean
shiftedQuarterLeftEndpoint
shiftedQuarterRightEndpoint
shiftedQuarterCenter

shiftedQuarterLeftEndpoint_eq_center
shiftedQuarterRightEndpoint_eq_next_center
shiftedQuarterCenter_eq_next_endpoint
shiftedQuarterRightEndpoint_eq_leftEndpoint_add_quarter
shiftedQuarterCenter_eq_midpoint
shiftedQuarterAffine_center_eq_shiftedQuarterCenter
```

これで「隣接 center を shifted frame の endpoints と見たとき、旧 seam endpoint が shifted center になる」ことを、scalar coordinate と affine interpolation の両方で証明済みにしました。

semantic shifted path はまだ endpoint state の選択が必要なので、今回は導入せず TODO として残しています。これは作業指示書の「premature なら force しない」に合わせた判断です。

docs も同期しました。

- [DkReal.lean](/lean/dk_math/DkMath/Analysis/DkReal.lean)
- [design-phase-center-shift-104.md](/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md)

検証:

```text
lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift
lake build DkMath.Analysis.DkReal
git diff --check
```

すべて成功です。

## Review

## 1. 状況解説

今回追加された主な構造はこれじゃ。

```text id="r0fc83"
shiftedQuarterLeftEndpoint
shiftedQuarterRightEndpoint
shiftedQuarterCenter
```

意味としては、隣接する quarter center を、新しい shifted frame の左右 endpoint として読む。

```text id="e7cn6t"
left endpoint:
  old center of edge k

right endpoint:
  old center of edge k + 1

shifted center:
  old seam endpoint after edge k
```

この読みが scalar coordinate 上で名前になった。
これは良い。これで「旧端点が新しい中心になる」という言葉が、Lean API として扱える。

## 2. 今回の本丸

今回の中心 theorem はこれじゃ。

```lean id="twa3vl"
theorem shiftedQuarterCenter_eq_midpoint (k : ℕ) :
    shiftedQuarterCenter k =
      (shiftedQuarterLeftEndpoint k + shiftedQuarterRightEndpoint k) / 2
```

これは、前回までの theorem を shifted-frame の語彙で包んだもの。

数学的にはこう読める。

$$
\mathrm{shiftedCenter}_k=\frac{\mathrm{shiftedLeft}_k+\mathrm{shiftedRight}_k}{2}
$$

ここで、旧 frame では seam endpoint だったものが、shifted frame では center になる。

この theorem があることで、設計語彙がかなり安定した。

## 3. affine center theorem まで届いたのが良い

さらに重めの theorem まで通っている。

```lean id="ctmgzj"
theorem shiftedQuarterAffine_center_eq_shiftedQuarterCenter (k : ℕ) :
    (1 - phaseCenter) * shiftedQuarterLeftEndpoint k +
        phaseCenter * shiftedQuarterRightEndpoint k =
      shiftedQuarterCenter k
```

これは良い。
単なる midpoint theorem ではなく、affine interpolation の local center (phaseCenter) で shifted center に到達することを言えている。

表示すればこうじゃ。

$$
(1-\mathrm{phaseCenter})L+\mathrm{phaseCenter}R=C
$$

ここで \(L\) は shifted left endpoint、\(R\) は shifted right endpoint、\(C\) は shifted center。

これは次に shifted semantic edge を定義するとき、ほぼそのまま設計核になる。

## 4. semantic shifted path を急がなかった判断も良い

今回、semantic shifted path は導入せず TODO に残している。これは正しい。

理由は、shifted semantic edge の左右 endpoint state をどう選ぶかが、まだ scalar coordinate だけでは決まらないからじゃ。

```text id="ij8ihz"
scalar shifted frame:
  implemented

semantic shifted path:
  endpoint states must be chosen

normalized shifted path:
  later
```

この段階で無理に path を作ると、あとで定義を差し替えることになりやすい。
だから今回は scalar API と affine theorem で止めたのが良い。

## 5. DkReal.lean の説明更新も良い

`DkReal.lean` の public comment も更新され、shifted scalar frame が「隣接 centers を endpoints として命名し、その affine center が旧 seam endpoint である」と説明されている。さらに shifted semantic paths は後の定義として残されている。

これは重要じゃ。
全体を読む人が、「ここで path まで実装済み」と誤読しない。

## 6. docs 同期も良い

`design-phase-center-shift-104.md` では implemented checkpoint に今回の API が反映され、Remaining TODO として `shifted-semantic-edge` と `one-eighth-euclidean-reading` が残されている。

この整理はかなり良い。

```text id="qmj7rl"
implemented:
  scalar shifted frame

remaining:
  semantic shifted edge
  one-eighth Euclidean reading
```

ここで task が小さく見えるようになった。

## 7. 今回の「一投指示」の効果

かなり良い効果が出ている。

細かく分けていたら、おそらく次の三往復になっていた。

```text id="ymap4q"
first:
  shiftedQuarterLeftEndpoint などの alias

second:
  midpoint theorem

third:
  affine center theorem
```

今回は一投でここまで来た。
Lean が検査役として働くので、この粒度でよい。

つまり、今後は次の方針がよさそうじゃ。

```text id="zbvtzr"
薄い API:
  必ず入れる

中くらい theorem:
  同じ依頼内で狙う

重い theorem:
  可能なら狙い、無理なら TODO として設計に残す
```

これならトークンも往復も減る。エネルギー効率も良い。

## 8. 次の技術的分岐

次は二方向ある。

ひとつ目は、semantic shifted edge の endpoint state を選ぶ route。

候補は、既存の normalized midpoint states を使い、隣接 center を boundary に戻した点を左右 endpoint とする方向じゃ。
ただしここは慎重に選ぶ必要がある。

ふたつ目は、まだ scalar 側でさらに整える route。

例えば shifted frame の幅や one-eighth offset をもう少し明示する。

```lean id="zz6bt1"
theorem shiftedQuarterRightEndpoint_sub_leftEndpoint (k : ℕ) :
    shiftedQuarterRightEndpoint k - shiftedQuarterLeftEndpoint k = 1 / 4
```

```lean id="j8ubcm"
theorem shiftedQuarterCenter_eq_leftEndpoint_add_halfQuarter (k : ℕ) :
    shiftedQuarterCenter k =
      shiftedQuarterLeftEndpoint k + phaseHalfQuarterStep
```

この二つは、次の semantic path に入る前にかなり役立つ。

## 9. 次は「scalar 補強＋semantic edge 設計」まで一投でよい

次も細切れにせず、一投でよいと思う。

狙いはこうじゃ。

```text id="lqmpde"
scalar shifted frame:
  width theorem
  center offset theorem
  right endpoint offset theorem

semantic endpoint state:
  candidate definition or design TODO

normalized shifted edge:
  feasibleなら定義
  無理なら theorem shape を docs に残す
```

このセットなら、Codex が安全に進められる。

## 10. 結論

今回の差分は採用でよい。

```text id="th1qwc"
実装:
  良い。shifted-frame scalar API が閉じた。

数学:
  良い。旧 seam endpoint が shifted frame の affine center であることまで証明された。

設計:
  良い。semantic shifted path は endpoint state 選択が必要として保留できている。

進め方:
  良い。薄い theorem と重め theorem を同時に狙う方式が機能した。

次:
  shifted scalar theorem を少し補強しつつ、semantic shifted edge の endpoint state 選択へ進む。
```

ぬしよ、この粒度がよさそうじゃ。
小さすぎず、飛びすぎず、Lean が止めるところまで進める。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index 1b9052bd..528b0463 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -179,8 +179,11 @@ The local center `phaseCenter = 1 / 2` is recognized by the unique minimum of
 quarter-cycle coordinates prove that the seam endpoint between adjacent
 quarter edges is the midpoint between their centers, isolating the one-eighth
 phase displacement without using circle or arc language. Scalar return laws
-for dyadic and positive `k` cycle divisions are also recorded, and the affine
-and normalized semantic edges expose their midpoint `q2` facts.
+for dyadic and positive `k` cycle divisions are also recorded. The shifted
+scalar frame now names neighboring centers as endpoints and proves that its
+affine center is the old seam endpoint. The affine and normalized semantic
+edges expose their midpoint `q2` facts, while shifted semantic paths remain a
+later definition.
 
 [IMPLEMENTED: semantic-cf2d-path] `DkReal.SemanticCF2DPath` uses the
 coordinate-product topology from `CF2D.Topology` to package every translated
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
index b05e8e2a..4f6767a2 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
@@ -160,6 +160,85 @@ theorem globalQuarterEndpoint_succ_is_center_between_centers (k : ℕ) :
   simp [globalQuarterCenter, globalQuarterEndpoint]
   ring
 
+/-!
+## Scalar shifted quarter frame
+
+The shifted frame uses the neighboring quarter centers as its endpoints. In
+that frame, the old seam endpoint is now the center. This remains scalar
+coordinate bookkeeping; no shifted semantic path is introduced yet.
+-/
+
+/-- Left endpoint of the shifted quarter frame around the seam after edge `k`. -/
+def shiftedQuarterLeftEndpoint (k : ℕ) : ℝ :=
+  globalQuarterCenter k
+
+/-- Right endpoint of the shifted quarter frame around the seam after edge `k`. -/
+def shiftedQuarterRightEndpoint (k : ℕ) : ℝ :=
+  globalQuarterCenter (k + 1)
+
+/-- Center of the shifted quarter frame, namely the old seam endpoint. -/
+def shiftedQuarterCenter (k : ℕ) : ℝ :=
+  globalQuarterEndpoint (k + 1)
+
+/-- The shifted-frame left endpoint is the old center of quarter edge `k`. -/
+@[simp]
+theorem shiftedQuarterLeftEndpoint_eq_center (k : ℕ) :
+    shiftedQuarterLeftEndpoint k = globalQuarterCenter k := rfl
+
+/-- The shifted-frame right endpoint is the old center of quarter edge `k + 1`. -/
+@[simp]
+theorem shiftedQuarterRightEndpoint_eq_next_center (k : ℕ) :
+    shiftedQuarterRightEndpoint k = globalQuarterCenter (k + 1) := rfl
+
+/-- The shifted-frame center is the old seam endpoint after quarter edge `k`. -/
+@[simp]
+theorem shiftedQuarterCenter_eq_next_endpoint (k : ℕ) :
+    shiftedQuarterCenter k = globalQuarterEndpoint (k + 1) := rfl
+
+/-- The shifted-frame endpoints are separated by one quarter step. -/
+theorem shiftedQuarterRightEndpoint_eq_leftEndpoint_add_quarter (k : ℕ) :
+    shiftedQuarterRightEndpoint k =
+      shiftedQuarterLeftEndpoint k + 1 / 4 := by
+  simp [shiftedQuarterLeftEndpoint, shiftedQuarterRightEndpoint,
+    globalQuarterCenter_succ_eq_center_add_quarter]
+
+/--
+The shifted-frame center is the midpoint of its shifted endpoints.
+
+This is the named scalar reading of the endpoint-to-center shift: the seam
+that was an endpoint in the old quarter frame is the center in the shifted
+frame.
+-/
+theorem shiftedQuarterCenter_eq_midpoint (k : ℕ) :
+    shiftedQuarterCenter k =
+      (shiftedQuarterLeftEndpoint k + shiftedQuarterRightEndpoint k) / 2 := by
+  rw [shiftedQuarterCenter_eq_next_endpoint,
+    shiftedQuarterLeftEndpoint_eq_center,
+    shiftedQuarterRightEndpoint_eq_next_center]
+  exact (globalQuarterEndpoint_succ_is_center_between_centers k).symm
+
+/--
+Affine interpolation in the shifted scalar frame reaches the shifted center
+at the local phase center.
+
+This prepares a future shifted semantic edge without defining that path yet.
+-/
+theorem shiftedQuarterAffine_center_eq_shiftedQuarterCenter (k : ℕ) :
+    (1 - phaseCenter) * shiftedQuarterLeftEndpoint k +
+        phaseCenter * shiftedQuarterRightEndpoint k =
+      shiftedQuarterCenter k := by
+  rw [shiftedQuarterCenter_eq_midpoint]
+  simp [phaseCenter]
+  ring
+
+/-!
+[TODO: semantic-cf2d/shifted-semantic-edge]
+Define a shifted semantic edge only after choosing the endpoint states that
+correspond to `shiftedQuarterLeftEndpoint` and `shiftedQuarterRightEndpoint`.
+The expected scalar compatibility theorem is that its value at `phaseCenter`
+represents `shiftedQuarterCenter`.
+-/
+
 /-!
 ## Scalar return laws for normalized cycle divisions
 
diff --git a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
index c01b6be6..3b6237f8 100644
--- a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
+++ b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
@@ -314,6 +314,15 @@ SemanticCF2DPhaseShift.lean
   globalQuarterCenter_succ_sub_center
   globalQuarterCenter_succ_eq_center_add_quarter
   globalQuarterEndpoint_succ_is_center_between_centers
+  shiftedQuarterLeftEndpoint
+  shiftedQuarterRightEndpoint
+  shiftedQuarterCenter
+  shiftedQuarterLeftEndpoint_eq_center
+  shiftedQuarterRightEndpoint_eq_next_center
+  shiftedQuarterCenter_eq_next_endpoint
+  shiftedQuarterRightEndpoint_eq_leftEndpoint_add_quarter
+  shiftedQuarterCenter_eq_midpoint
+  shiftedQuarterAffine_center_eq_shiftedQuarterCenter
   normalizedCycleStep
   dyadicCycleStep
   normalizedCycleStep_mul_returnCount
@@ -325,8 +334,9 @@ SemanticCF2DPhaseShift.lean
 
 ## Boundary and Normalization Targets
 
-After the scalar shift theorem, the next target is to lift it back to the
-semantic edge and normalized edge APIs.
+The scalar shifted-frame API is now implemented. The next target is to choose
+the semantic endpoint states for a shifted semantic edge and then lift the
+shifted-frame scalar center theorem to that path.
 
 Candidate theorem directions:
 
@@ -377,38 +387,49 @@ depend on that reading.
 
 ## Implementation Plan
 
-1. Add scalar aliases for `phaseCenter` and `phaseHalfQuarterStep`.
-2. Prove `phaseDepth_center_eq` and `phaseDepth_center_unique` as API aliases.
-3. Prove `phaseDepth_centered_reflect`.
-4. Add a small phase-shift module for global quarter endpoints and centers.
-5. Prove the endpoint-between-centers identity.
-6. Add scalar cycle-step facts for dyadic and positive `k` divisions.
-7. Lift midpoint facts to `semanticPhaseEdge` and `normalizedPhaseEdge`.
-8. Only after that, add a Euclidean bridge that reads `1/8` full-cycle
+1. Implemented: add scalar aliases for `phaseCenter` and `phaseHalfQuarterStep`.
+2. Implemented: prove `phaseDepth_center_eq` and `phaseDepth_center_unique`.
+3. Implemented: prove `phaseDepth_centered_reflect`.
+4. Implemented: add a phase-shift module for global quarter endpoints and centers.
+5. Implemented: prove the endpoint-between-centers identity.
+6. Implemented: add scalar cycle-step facts for dyadic and positive `k` divisions.
+7. Implemented: add scalar shifted-frame endpoints, center, and affine midpoint theorem.
+8. Implemented: lift midpoint facts to `semanticPhaseEdge` and `normalizedPhaseEdge`.
+9. Next: choose a shifted semantic edge definition.
+10. Later: add a Euclidean bridge that reads `1/8` full-cycle
    displacement as the angle `Real.pi / 4`.
 
-## TODO Tags
+## Implemented Tags
 
 ```text
-[TODO: semantic-cf2d/phase-center-alias]
+[IMPLEMENTED: semantic-cf2d/phase-center-alias]
 Add `phaseCenter`, `phaseHalfQuarterStep`, and centered-coordinate wrappers.
 
-[TODO: semantic-cf2d/centered-reflection]
+[IMPLEMENTED: semantic-cf2d/centered-reflection]
 Expose reflection about `phaseCenter` directly, not only as `t -> 1 - t`.
 
-[TODO: semantic-cf2d/endpoint-as-shifted-center]
+[IMPLEMENTED: semantic-cf2d/endpoint-as-shifted-center]
 Prove that the seam endpoint between adjacent quarter edges is the midpoint
 between their centers.
 
-[TODO: semantic-cf2d/one-eighth-euclidean-reading]
-After the algebraic shift theorem is closed, bridge the one-eighth phase
-displacement to the Euclidean `pi / 4` reading.
-
-[TODO: semantic-cf2d/dyadic-cycle-step]
+[IMPLEMENTED: semantic-cf2d/dyadic-cycle-step]
 Expose the dyadic return law `2^n * (1 / 2^n) = 1` as a normalized cycle
 parameter fact, not as an angle subdivision.
 
-[TODO: semantic-cf2d/k-division-cycle-step]
+[IMPLEMENTED: semantic-cf2d/k-division-cycle-step]
 Expose the positive `k` return law `k * (1 / k) = 1` for the normalized cycle
 parameter before assigning any Euclidean shape.
 ```
+
+## Remaining TODO Tags
+
+```text
+[TODO: semantic-cf2d/shifted-semantic-edge]
+Choose the endpoint states for the shifted semantic edge and prove its scalar
+compatibility with `shiftedQuarterCenter`.
+
+[TODO: semantic-cf2d/one-eighth-euclidean-reading]
+After the algebraic shifted-frame theorem is closed at the semantic path
+level, bridge the one-eighth phase displacement to the Euclidean `pi / 4`
+reading.
+```
````
`````
