# Git diff / Report / Review

## Upd: Analysis.DkReal

gch: 8e3a5310fd57ad78a3d91e2539fbeb255f9c13fe

## Report

`LevelSet` 内部の closed path まで実装しました。

追加内容:

- `LevelSet R rho2` の subtype topology
- `semanticPhaseLevelPoint`
- `normalizedPhaseLevelEdge`
- level-set edge の連続性
- `normalizedPhaseLevelPath`
- `normalizedLevelFourPhasePath`
- `normalizedClosedLevelFourPhasePath`

これで境界所属は外部定理ではなく、

```lean
Path
  (semanticPhaseLevelPoint r z 0)
  (semanticPhaseLevelPoint r z 0)
```

の codomain `LevelSet ℝ (Vec.q2 z)` が直接保証します。

検証:

- `lake build DkMath.Analysis`: 成功、8288 jobs
- `git diff --check`: 成功

## Review

うむ。これはかなり決定的な進捗じゃ。
今回で **fixed-\(q2\) boundary path が型として完成** した。前回までは「`Vec ℝ` 上の path が境界上にあることを定理で保証する」段階だったが、今回は `LevelSet ℝ (Vec.q2 z)` を codomain にしたので、境界所属が外部定理ではなく型そのものに入った。

## 状況解説

今回の中心はこれじゃ。

```lean
normalizedClosedLevelFourPhasePath :
  Path
    (semanticPhaseLevelPoint r z 0)
    (semanticPhaseLevelPoint r z 0)
```

しかも、この `Path` の値域は

```lean
LevelSet ℝ (Vec.q2 z)
```

じゃ。

つまり、path の各点は最初から

$$
q2(w)=q2(z)
$$

を満たす点として型付けされている。

前回の状態は、

```text
Vec ℝ 上の closed path
+ 各点が q2 境界上にある theorem
```

今回の状態は、

```text
LevelSet ℝ (q2 z) 内部の closed path
```

になった。

これは大きい。
「境界から出ない」が、証明の付録ではなく、構成の型安全性になった。

## 何が達成されたか

流れはきれいに閉じた。

```text
q2 境界判定
-> 離散四相
-> affine edge
-> phaseDepth によるくぼみ観測
-> sqrt 補正
-> normalized edge
-> 四相 translate
-> fixed-q2 closed path
-> LevelSet 内部 closed path
```

ここまで来て、まだ円・角度・三角関数は導入していない。

これはかなり強い。
「円を仮定せずに、境界上の連続一周を作った」と言える段階じゃ。

## Topology 側の評価

`CF2D.Topology` に `LevelSet R rho2` の subtype topology を追加したのは正しい。

```lean
instance : TopologicalSpace (LevelSet R rho2)
```

とし、さらに

```lean
continuous_levelSet_val
```

で underlying `Vec` への射影が連続であることを出している。

これは今後かなり効く。
Euclidean bridge へ行くときも、まず `LevelSet` から `Vec ℝ`、さらに `ℝ × ℝ` へ降ろして比較できる。

この時点でもまだ metric、norm、orthogonality、circle は入っていない。
あくまで subtype topology。方針に合っている。

## Normalize 側の評価

`semanticPhaseLevelPoint` は、離散 action state を level set に包む役。
`normalizedPhaseLevelEdge` は、正規化された連続 edge を level set に包む役。

この二つにより、

```text
点も edge も同じ q2 境界の内部対象
```

になった。

さらに `normalizedPhaseLevelPath` で各 edge が level-set 内部 path になり、`normalizedLevelFourPhasePath` で四本が連結され、最後に exact order four で閉じる。

構成が非常に自然じゃ。

## 数学的な意味

今回の到達点は、こう表現できる。

```text
境界を外から観測する段階が終わり、
境界そのものを住む空間として扱える段階に入った。
```

これは物語的にも強い。

これまでは、目を閉じて境界を触っていた。
今回は、触っていた境界の上に実際に乗った。

ただし、まだ「それが円だ」とは言っていない。
今あるのは、

```text
fixed-q2 level set 上の closed path
```

であって、

```text
Euclidean circle 上の rotation path
```

ではない。

この慎重さは維持すべきじゃ。

## レビュー上の注意点

大きな問題は見えぬ。
次に Euclidean bridge へ進むなら、一つ重要な分岐がある。

$$
q2(z)=0
$$

の場合、level set は原点だけになる。
このとき path は定数的で、「円」ではなく退化境界じゃ。

一方、

$$
q2(z)>0
$$

なら、標準 Euclidean 解釈で半径

$$
\sqrt{q2(z)}
$$

の円として読める。

したがって次の bridge では、

```text
zero boundary:
  degenerate one-point level set

positive boundary:
  Euclidean circle model
```

を分けるのが安全じゃ。

特に `z ≠ 0` から `0 < Vec.q2 z` を出す補題が必要になるはず。

```lean
Vec.q2_pos_of_ne_zero
```

のような補題候補じゃな。

## 次の自然な作業

次は、報告通り `euclidean-levelset-bridge` でよい。

ただし、いきなり角度へ行かず、まずは level set と円モデルの対応だけを作るのが安全。

順序はこうじゃ。

```text
1. Vec ℝ の q2 非負性を整理する
2. z ≠ 0 なら 0 < q2 z を証明する
3. LevelSet ℝ rho2 を Euclidean norm sphere と対応させる
4. rho2 = 0 と rho2 > 0 を分ける
5. positive case で半径 sqrt rho2 の circle model と接続する
6. その後に角度・quarter-turn 解釈へ進む
```

この順番なら、pre-geometric 構成を壊さずに Euclidean 読みへ進める。

## \(\pi\) 計画との関係

今回で、\(\pi\) へ向かう前の boundary path はかなり固まった。

ただし、まだ \(\pi\) は出ていない。
今あるのは、

```text
fixed-q2 boundary internal closed path
```

まで。

ここから、

```text
Euclidean circle model
refinement law
Gaussian bridge
normalization constant
Real.pi identification
```

へ進む。

焦らぬのが正解じゃ。
今回の成果は、`Real.pi` へ行く前に必要な「円以前の境界上閉路」を型として完成させたこと。

## 総評

非常によい更新じゃ。

一言で言えば、

```text
円や角度を使わず、固定 q2 境界そのものを値域とする連続閉路を構成した。
```

これは節目じゃ。
ここまで来ると、次の Euclidean bridge は「新しく円を作る」のではなく、「すでにある境界 path を円モデルとして読む」だけになる。

その順序が守られている。かなり堅い。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index a44ddff8..11b66ce8 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -111,7 +111,8 @@ root of `phaseDepth`. The resulting edge is continuous, has the same
 endpoints, and remains on the initial `q2` boundary for every real parameter
 under the core-zero action. Its four action translates retain this boundary,
 join at exact seams, repeat with phase index four, and concatenate to a closed
-continuous path.
+continuous path. The final path is also packaged directly in
+`LevelSet Real (q2 z)`, so boundary membership is enforced by its codomain.
 
 [TODO: semantic-cf2d-signed] Source-level `Vec.star` and `KernelFamily` require
 signed arithmetic. Defer them until a signed DkReal layer exists.
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
index 869501d3..130a8451 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
@@ -1330,8 +1330,13 @@ original boundary.
 transported through all four action phases. The resulting fixed-`q2` paths
 have exact seams and concatenate to a closed path.
 
-[TODO: semantic-cf2d-phase/levelset-path] Package the normalized paths directly
-in `LevelSet Real (q2 z)`, making boundary membership part of the target type.
+[IMPLEMENTED: semantic-cf2d-phase/levelset-path] The normalized phases and
+their closed four-phase concatenation are packaged directly in
+`LevelSet Real (q2 z)`, making boundary membership part of the target type.
+
+[TODO: semantic-cf2d-phase/euclidean-levelset-bridge] Identify the positive
+real `q2` level sets with the corresponding Euclidean circle model without
+changing the pre-geometric construction.
 
 [TODO: semantic-cf2d-phase/euclidean-interpretation] Only after normalization,
 identify the fixed-`q2` path with the standard Euclidean circle model and
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DNormalize.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DNormalize.lean
index da9850b8..f8492893 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DNormalize.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DNormalize.lean
@@ -258,6 +258,108 @@ def normalizedClosedFourPhasePath
       source' := p.source
       target' := p.target.trans hclose }
 
+/-!
+## Paths internal to the square-mass boundary
+
+The preceding paths are valued in `Vec Real`, with boundary membership proved
+by a theorem. The following layer strengthens the codomain to
+`LevelSet Real (q2 z)`, so leaving the boundary is no longer type-correct.
+-/
+
+/-- The `k`th discrete action state, packaged in the initial `q2` level set. -/
+def semanticPhaseLevelPoint
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (k : ℕ) :
+    LevelSet ℝ (Vec.q2 z) :=
+  ⟨(semanticAct r)^[k] z, semanticAct_iterate_q2 r k z⟩
+
+@[simp]
+theorem semanticPhaseLevelPoint_val
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (k : ℕ) :
+    (semanticPhaseLevelPoint r z k).1 = (semanticAct r)^[k] z := rfl
+
+/--
+The `k`th normalized transition as a point of the fixed square-mass level set.
+-/
+def normalizedPhaseLevelEdge
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (k : ℕ) (t : ℝ) :
+    LevelSet ℝ (Vec.q2 z) :=
+  ⟨normalizedPhaseEdgeAt r z k t,
+    normalizedPhaseEdgeAt_q2_of_core_eq_zero hcore z k t⟩
+
+@[simp]
+theorem normalizedPhaseLevelEdge_val
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (k : ℕ) (t : ℝ) :
+    (normalizedPhaseLevelEdge hcore z k t).1 =
+      normalizedPhaseEdgeAt r z k t := rfl
+
+/-- The level-set-valued normalized edge is continuous. -/
+theorem continuous_normalizedPhaseLevelEdge
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (k : ℕ) :
+    Continuous (fun t : ℝ => normalizedPhaseLevelEdge hcore z k t) :=
+  Continuous.subtype_mk (continuous_normalizedPhaseEdgeAt r z k) _
+
+/--
+The `k`th normalized phase as a path whose target type is the fixed `q2`
+boundary itself.
+-/
+def normalizedPhaseLevelPath
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (k : ℕ) :
+    Path (semanticPhaseLevelPoint r z k)
+      (semanticPhaseLevelPoint r z (k + 1)) where
+  toFun t := normalizedPhaseLevelEdge hcore z k t
+  continuous_toFun :=
+    (continuous_normalizedPhaseLevelEdge hcore z k).comp
+      continuous_subtype_val
+  source' := by
+    apply Subtype.ext
+    simp [normalizedPhaseLevelEdge, semanticPhaseLevelPoint]
+  target' := by
+    apply Subtype.ext
+    simp [normalizedPhaseLevelEdge, semanticPhaseLevelPoint]
+
+/-- Four normalized phases concatenated inside the fixed `q2` level set. -/
+def normalizedLevelFourPhasePath
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    Path (semanticPhaseLevelPoint r z 0)
+      (semanticPhaseLevelPoint r z 4) :=
+  (((normalizedPhaseLevelPath hcore z 0).trans
+      (normalizedPhaseLevelPath hcore z 1)).trans
+    (normalizedPhaseLevelPath hcore z 2)).trans
+      (normalizedPhaseLevelPath hcore z 3)
+
+/--
+The normalized four-phase path is a closed path internal to the fixed
+square-mass level set.
+-/
+def normalizedClosedLevelFourPhasePath
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    Path (semanticPhaseLevelPoint r z 0)
+      (semanticPhaseLevelPoint r z 0) := by
+  have hclose :
+      semanticPhaseLevelPoint r z 4 = semanticPhaseLevelPoint r z 0 := by
+    apply Subtype.ext
+    change (semanticAct r)^[4] z = (semanticAct r)^[0] z
+    have hfour := (semanticExactActionOrderFour_of_core_eq_zero hcore).1
+    rw [hfour]
+    rfl
+  let p := normalizedLevelFourPhasePath hcore z
+  exact
+    { toContinuousMap := p.toContinuousMap
+      source' := p.source
+      target' := p.target.trans hclose }
+
 end
 
 end DkMath.Analysis.DkNNRealQ
diff --git a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
index ab6fc307..f424183e 100644
--- a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
+++ b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
@@ -112,6 +112,8 @@ theorem, not inserted as notation.
 3. The normalized master edge is continuous and has the original endpoints.
 4. All four action translates preserve the same boundary, meet at exact
    seams, and concatenate to a closed continuous path.
+5. The closed path is packaged in the fixed `q2` level-set subtype, so
+   boundary membership is enforced by the target type.
 
 ### Milestone C: refinement law
 
@@ -153,6 +155,7 @@ mechanism from which these theorem obligations can be investigated.
 
 ## Immediate Next Step
 
-The next implementation may package the path directly in the `q2` level-set
-subtype before introducing any Euclidean circle terminology. Refinement and
-limit arguments remain separate checkpoints.
+The next bridge may identify positive real `q2` level sets with a standard
+Euclidean circle model. That bridge must remain an interpretation of the
+existing boundary path, not a replacement construction. Refinement and limit
+arguments remain separate checkpoints.
diff --git a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
index 713a092e..c0938864 100644
--- a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
+++ b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
@@ -21,6 +21,10 @@ That module also implements all four normalized action translates, their
 seams, common fixed-`q2` law, phase-index periodicity, continuous paths, and
 the resulting closed four-phase path.
 
+The same construction is now packaged directly in
+`LevelSet Real (Vec.q2 z)`. The level-set subtype carries its inherited
+topology, and the final closed path cannot leave the boundary by construction.
+
 The current implementation proves a four-state return:
 
 ```text
@@ -339,7 +343,8 @@ explicit.
 [IMPLEMENTED: semantic-cf2d-phase/path-concatenation]
 [IMPLEMENTED: semantic-cf2d-phase/boundary-normalization]
 [IMPLEMENTED: semantic-cf2d-phase/normalized-four-path]
-[TODO: semantic-cf2d-phase/levelset-path]
+[IMPLEMENTED: semantic-cf2d-phase/levelset-path]
+[TODO: semantic-cf2d-phase/euclidean-levelset-bridge]
 [TODO: semantic-cf2d-phase/refinement-law]
 [TODO: semantic-cf2d-phase/gaussian-limit]
 [TODO: semantic-cf2d-phase/pi-identification]
diff --git a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Topology.lean b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Topology.lean
index 827b9153..5c855199 100644
--- a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Topology.lean
+++ b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Topology.lean
@@ -94,6 +94,24 @@ theorem Continuous.vec_mk
     Continuous (fun x => Vec.mk (f x) (g x)) :=
   continuous_vec_iff.mpr ⟨hf, hg⟩
 
+section LevelSet
+
+variable [Semiring R] (rho2 : R)
+
+/--
+The topology on a square-mass level set is the subtype topology inherited
+from the coordinate-product topology on `Vec R`.
+-/
+instance : TopologicalSpace (LevelSet R rho2) :=
+  inferInstanceAs (TopologicalSpace {z : Vec R // Vec.q2 z = rho2})
+
+/-- Forgetting level-set membership is continuous. -/
+theorem continuous_levelSet_val :
+    Continuous (fun z : LevelSet R rho2 => z.1) :=
+  continuous_subtype_val
+
+end LevelSet
+
 end Topology
 
 end DkMath.CosmicFormula.Rotation.CF2D
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
index 640987eb..751eae0f 100644
--- a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
@@ -651,3 +651,25 @@ Archive
 5. 検証:
    - `lake build DkMath.Analysis.DkReal.SemanticCF2DNormalize` 成功
      (8277 jobs)。
+
+### 2026/06/23 06:50 JST (Level-set internal closed path)
+
+1. topology:
+   - `CF2D.Topology` に `LevelSet R rho2` の subtype topology を追加した。
+   - level-set から underlying `Vec` への射影の連続性を追加した。
+2. boundary type:
+   - 離散 action state を `semanticPhaseLevelPoint` として
+     `LevelSet Real (q2 z)` に包装した。
+   - normalized edge を `normalizedPhaseLevelEdge` として同じ level set に
+     包装し、その連続性を証明した。
+3. path:
+   - 各 edge を `normalizedPhaseLevelPath` として level-set 内部の Path にした。
+   - 4本を連結し、exact order four により
+     `normalizedClosedLevelFourPhasePath` を構成した。
+4. 結論:
+   - fixed-`q2` boundary membership は外部定理だけでなく codomain の型に
+     組み込まれた。
+   - 次候補は既存 path を Euclidean circle model へ解釈する bridge。
+5. 検証:
+   - `lake build DkMath.Analysis.DkReal.SemanticCF2DNormalize` 成功
+     (8277 jobs)。
````
`````
