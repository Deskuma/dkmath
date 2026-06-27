# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2DNormalize

gch: 0be90e5b9f560ddab8b18f443c155d3fc279dfa5

## Report

補正と normalized four-phase path を実装しました。

主な追加:

- `Vec.q2_scale`
- `phaseNormalization_sq_mul_phaseDepth`
- `normalizedPhaseEdgeAt`
- endpoint / seam / 固定 `q2` / 4周期性
- 全 translated edge の連続性
- `normalizedPhasePath`
- `normalizedClosedFourPhasePath : Path z z`

これで円・角度を導入せず、固定 `q2` 境界上の連続閉路まで到達しました。

実装: [SemanticCF2DNormalize.lean](/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DNormalize.lean)

検証:

- `lake build DkMath.Analysis`: 成功、8288 jobs
- `git diff --check`: 成功

## Review

うむ。これは大きい。
今回で、ついに **円・角度なしの fixed-\(q2\) continuous closed path** まで到達した。一本の正規化 edge だけでなく、それを四相へ作用移送し、seam をつなぎ、閉じた `Path z z` まで構成できている。

## 状況解説

前回までは、一本の affine edge を

$$
E(z,t)=(1-t)z+tA(z)
$$

として作り、それを

$$
\frac{1}{\sqrt{\operatorname{phaseDepth}(t)}}
$$

で補正して、一本の edge が固定 \(q2\) 境界へ戻るところまでだった。

今回はそこから進んで、

```text id="wh4cqs"
normalizedPhaseEdgeAt
normalizedPhaseEdgeAt_zero
normalizedPhaseEdgeAt_one
normalizedPhaseEdgeAt_seam
normalizedPhaseEdgeAt_q2_of_core_eq_zero
normalizedPhaseEdgeAt_add_four_of_core_eq_zero
continuous_normalizedPhaseEdgeAt
normalizedPhasePath
normalizedFourPhasePath
normalizedClosedFourPhasePath
```

が追加されている。

つまり、一本の normalized edge を四相すべてへ作用移送し、それぞれが固定 \(q2\) 境界を保ち、端点がぴったり接続し、4本で閉じるところまで来た。

## 何が本当に達成されたか

これは単なる path 化ではない。
流れとしてはこうじゃ。

```text id="fvghzv"
境界判定機 q2
-> 離散四相
-> affine edge
-> q2 境界欠損
-> sqrt 補正
-> normalized edge
-> 四相 translate
-> fixed-q2 closed path
```

ここまで一切、円・角度・三角関数を仮定していない。

この順序が強い。

特に今回は、

$$
q2(N_k(z,t))=q2(z)
$$

が各 translated edge で成立している。
これは「境界上にいる」と後から言えるための核じゃ。

## `Vec.q2_scale` の追加が良い

今回のレビュー補正として `Vec.q2_scale` が追加されたのはかなり良い。

$$
q2(cz)=c^2q2(z)
$$

という構造補題を切り出したことで、normalized edge の \(q2\) 証明が「計算の塊」から「構造的な補正」に変わった。

また、

$$
\operatorname{phaseNormalization}(t)^2\operatorname{phaseDepth}(t)=1
$$

も `phaseNormalization_sq_mul_phaseDepth` として独立 API になった。
この二つは今後、refinement や Gaussian bridge 側でも再利用しやすい。

## 数学的な意味

今回の到達点を言葉にすると、

```text id="q2ui7q"
直線で探った境界のくぼみを測り、
平方根補正で境界へ戻し、
その補正済み遷移を四相でつなぐと、
固定 q2 境界上の連続閉路が得られる。
```

これはかなり美しい。

最初から円を描いたのではない。
手で境界を探り、くぼみを測り、整えた結果として、境界上の一回りが出てきた。

この物語はそのまま論文化の説明骨格に使える。

## 注意点

一点だけ、表現はまだ少し慎重にした方がよい。

`normalizedClosedFourPhasePath : Path z z` は、型としては `Vec ℝ` 上の path じゃ。
各 edge が固定 \(q2\) 境界上にある定理はあるが、path の target type 自体はまだ `LevelSet ℝ (Vec.q2 z)` ではない。

だから現段階の最も正確な言い方は、

```text id="6dg7cr"
固定 q2 境界上にあることが定理で証明された Vec ℝ 上の closed path
```

じゃな。

次の TODO にある `levelset-path` は、この境界所属を型に焼き込む段階。これはとても自然な次手。

## 次にやると良いこと

次は報告の通り、`LevelSet` 化がよい。

たとえば目標は、

```lean id="d3infp"
normalizedLevelPhasePath
normalizedClosedLevelFourPhasePath
```

のような形じゃな。

意味としては、

```text id="068bom"
Path in Vec ℝ
  から
Path in LevelSet ℝ (q2 z)
```

へ移す。

これができると、「境界上にいる」が外部 theorem ではなく、型そのものの性質になる。後続の Euclidean interpretation bridge でも扱いやすい。

## \(\pi\) 計画との関係

今回で Milestone B はほぼ完了じゃ。
ただし、\(\pi\) にはまだ行かない。

今得たのは、

```text id="irvvrr"
local correction
boundary-valued closed path
```

まで。

この先に、

```text id="agq8yw"
refinement law
correction product
limit
Gaussian bridge
Real.pi identification
```

が来る。

焦らずでよい。
今回の成果は、「\(\pi\) へ行く前に必要な境界上の連続一周」ができたことじゃ。

## 総評

非常に良い進捗じゃ。

到達点はこう言える。

```text id="cbi8e9"
円や角度を使わず、
境界判定 q2 と四相作用と平方根補正だけで、
固定 q2 境界上の連続閉路を構成した。
```

これはかなり強い。

次に `LevelSet` に包めば、「円以前の境界上閉路」が型として完成する。
その後に初めて、Euclidean circle として読む橋を架ける。順序は今のままで正しい。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index 8b0d72f6..a44ddff8 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -109,7 +109,9 @@ is not yet normalized to a fixed `q2` boundary.
 `DkReal.SemanticCF2DNormalize` divides one affine edge by the positive square
 root of `phaseDepth`. The resulting edge is continuous, has the same
 endpoints, and remains on the initial `q2` boundary for every real parameter
-under the core-zero action.
+under the core-zero action. Its four action translates retain this boundary,
+join at exact seams, repeat with phase index four, and concatenate to a closed
+continuous path.
 
 [TODO: semantic-cf2d-signed] Source-level `Vec.star` and `KernelFamily` require
 signed arithmetic. Defer them until a signed DkReal layer exists.
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
index faee5cde..869501d3 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
@@ -1326,9 +1326,12 @@ into a closed piecewise-affine loop. It is not yet a fixed-`q2` boundary path.
 of its `q2` profile and proves that the resulting continuous edge stays on the
 original boundary.
 
-[TODO: semantic-cf2d-phase/normalized-four-path] Transport the normalized edge
-through all four action phases and concatenate the resulting boundary-valued
-paths into a closed path.
+[IMPLEMENTED: semantic-cf2d-phase/normalized-four-path] The normalized edge is
+transported through all four action phases. The resulting fixed-`q2` paths
+have exact seams and concatenate to a closed path.
+
+[TODO: semantic-cf2d-phase/levelset-path] Package the normalized paths directly
+in `LevelSet Real (q2 z)`, making boundary membership part of the target type.
 
 [TODO: semantic-cf2d-phase/euclidean-interpretation] Only after normalization,
 identify the fixed-`q2` path with the standard Euclidean circle model and
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DNormalize.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DNormalize.lean
index c0c023e9..da9850b8 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DNormalize.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DNormalize.lean
@@ -80,6 +80,17 @@ theorem continuous_phaseNormalization :
     (Real.continuous_sqrt.comp continuous_phaseDepth)
     sqrt_phaseDepth_ne_zero
 
+/-- Squared normalization cancels the affine boundary-depth factor. -/
+theorem phaseNormalization_sq_mul_phaseDepth (t : ℝ) :
+    phaseNormalization t ^ 2 * phaseDepth t = 1 := by
+  have hsqrt_sq :
+      (Real.sqrt (phaseDepth t)) ^ 2 = phaseDepth t :=
+    Real.sq_sqrt (phaseDepth_nonneg t)
+  have hsqrt_ne := sqrt_phaseDepth_ne_zero t
+  unfold phaseNormalization
+  field_simp
+  rw [hsqrt_sq]
+
 /--
 Scale a CF2D state by the reciprocal square root of affine phase depth.
 -/
@@ -115,18 +126,16 @@ theorem normalizedPhaseEdge_q2_of_core_eq_zero
     (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
     (z : Vec ℝ) (t : ℝ) :
     Vec.q2 (normalizedPhaseEdge r z t) = Vec.q2 z := by
-  have hsqrt_sq :
-      (Real.sqrt (phaseDepth t)) ^ 2 = phaseDepth t :=
-    Real.sq_sqrt (phaseDepth_nonneg t)
-  have hsqrt_ne := sqrt_phaseDepth_ne_zero t
   rw [show Vec.q2 (normalizedPhaseEdge r z t) =
       phaseNormalization t ^ 2 * Vec.q2 (semanticPhaseEdge r z t) by
-    simp [normalizedPhaseEdge, Vec.q2]
-    ring]
+    exact Vec.q2_scale _ _]
   rw [semanticPhaseEdge_q2_of_core_eq_zero hcore]
-  unfold phaseNormalization
-  field_simp
-  rw [hsqrt_sq]
+  calc
+    phaseNormalization t ^ 2 * (phaseDepth t * Vec.q2 z) =
+        (phaseNormalization t ^ 2 * phaseDepth t) * Vec.q2 z := by ring
+    _ = Vec.q2 z := by
+      rw [phaseNormalization_sq_mul_phaseDepth]
+      ring
 
 /-- The normalized master edge is continuous. -/
 theorem continuous_normalizedPhaseEdge
@@ -138,6 +147,117 @@ theorem continuous_normalizedPhaseEdge
   · exact continuous_phaseNormalization.mul hcore
   · exact continuous_phaseNormalization.mul hbeam
 
+/-!
+## Four normalized phases
+
+As in the affine layer, all four boundary-valued transitions are generated
+from one master edge by action iteration.
+-/
+
+/-- The `k`th normalized phase is an action translate of the master edge. -/
+def normalizedPhaseEdgeAt
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (k : ℕ) (t : ℝ) : Vec ℝ :=
+  (semanticAct r)^[k] (normalizedPhaseEdge r z t)
+
+/-- The `k`th normalized phase starts at the `k`th action state. -/
+@[simp]
+theorem normalizedPhaseEdgeAt_zero
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (k : ℕ) :
+    normalizedPhaseEdgeAt r z k 0 = (semanticAct r)^[k] z := by
+  simp [normalizedPhaseEdgeAt]
+
+/-- The `k`th normalized phase ends at the next action state. -/
+@[simp]
+theorem normalizedPhaseEdgeAt_one
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (k : ℕ) :
+    normalizedPhaseEdgeAt r z k 1 = (semanticAct r)^[k + 1] z := by
+  rw [normalizedPhaseEdgeAt, normalizedPhaseEdge_one]
+  exact (Function.iterate_succ_apply (semanticAct r) k z).symm
+
+/-- Consecutive normalized phases have identical seam points. -/
+theorem normalizedPhaseEdgeAt_seam
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (k : ℕ) :
+    normalizedPhaseEdgeAt r z k 1 =
+      normalizedPhaseEdgeAt r z (k + 1) 0 := by
+  simp
+
+/-- Every normalized phase stays on the initial square-mass boundary. -/
+theorem normalizedPhaseEdgeAt_q2_of_core_eq_zero
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (k : ℕ) (t : ℝ) :
+    Vec.q2 (normalizedPhaseEdgeAt r z k t) = Vec.q2 z := by
+  rw [normalizedPhaseEdgeAt, semanticAct_iterate_q2,
+    normalizedPhaseEdge_q2_of_core_eq_zero hcore]
+
+/-- The normalized phase family is periodic with phase index four. -/
+theorem normalizedPhaseEdgeAt_add_four_of_core_eq_zero
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) (k : ℕ) (t : ℝ) :
+    normalizedPhaseEdgeAt r z (k + 4) t =
+      normalizedPhaseEdgeAt r z k t := by
+  have hfour :
+      (semanticAct r)^[4] = id :=
+    (semanticExactActionOrderFour_of_core_eq_zero hcore).1
+  rw [normalizedPhaseEdgeAt, normalizedPhaseEdgeAt,
+    Function.iterate_add_apply, hfour]
+  rfl
+
+/-- Every action-translated normalized edge is continuous. -/
+theorem continuous_normalizedPhaseEdgeAt
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (k : ℕ) :
+    Continuous (fun t : ℝ => normalizedPhaseEdgeAt r z k t) := by
+  induction k with
+  | zero =>
+      simpa [normalizedPhaseEdgeAt] using continuous_normalizedPhaseEdge r z
+  | succ k ih =>
+      rw [show (fun t : ℝ => normalizedPhaseEdgeAt r z (k + 1) t) =
+          fun t => semanticAct r (normalizedPhaseEdgeAt r z k t) by
+        funext t
+        simp [normalizedPhaseEdgeAt, Function.iterate_succ_apply']]
+      rcases continuous_vec_iff.mp ih with ⟨hcore, hbeam⟩
+      apply Continuous.vec_mk
+      · exact
+          (continuous_const.mul hcore).sub (continuous_const.mul hbeam)
+      · exact
+          (continuous_const.mul hbeam).add (continuous_const.mul hcore)
+
+/-- The `k`th normalized phase packaged as a Mathlib path. -/
+def normalizedPhasePath
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (k : ℕ) :
+    Path ((semanticAct r)^[k] z) ((semanticAct r)^[k + 1] z) where
+  toFun t := normalizedPhaseEdgeAt r z k t
+  continuous_toFun :=
+    (continuous_normalizedPhaseEdgeAt r z k).comp continuous_subtype_val
+  source' := by simp
+  target' := by simp
+
+/-- Four normalized phases concatenated before endpoint identification. -/
+def normalizedFourPhasePath
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
+    Path z ((semanticAct r)^[4] z) :=
+  (((normalizedPhasePath r z 0).trans (normalizedPhasePath r z 1)).trans
+    (normalizedPhasePath r z 2)).trans (normalizedPhasePath r z 3)
+
+/--
+Core-zero exact order four closes the normalized boundary-valued transition
+into a continuous path based at `z`.
+-/
+def normalizedClosedFourPhasePath
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) : Path z z := by
+  have hclose : (semanticAct r)^[4] z = z := by
+    have hfour := (semanticExactActionOrderFour_of_core_eq_zero hcore).1
+    rw [hfour]
+    rfl
+  let p := normalizedFourPhasePath r z
+  exact
+    { toContinuousMap := p.toContinuousMap
+      source' := p.source
+      target' := p.target.trans hclose }
+
 end
 
 end DkMath.Analysis.DkNNRealQ
diff --git a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
index 7b1e5936..ab6fc307 100644
--- a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
+++ b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
@@ -105,13 +105,13 @@ theorem, not inserted as notation.
 4. Core-zero exact order four closes the endpoint without Euclidean
    terminology.
 
-### Milestone B: boundary normalization - one edge implemented
+### Milestone B: boundary normalization - implemented
 
 1. The positive correction `1 / sqrt (phaseDepth t)` is defined and continuous.
 2. The normalized master edge preserves the original `q2` value.
 3. The normalized master edge is continuous and has the original endpoints.
-4. Compatibility with all four action translates and their closed-path
-   concatenation remains to be implemented.
+4. All four action translates preserve the same boundary, meet at exact
+   seams, and concatenate to a closed continuous path.
 
 ### Milestone C: refinement law
 
@@ -153,6 +153,6 @@ mechanism from which these theorem obligations can be investigated.
 
 ## Immediate Next Step
 
-The next implementation transports the normalized edge through all four
-action phases and concatenates those boundary-valued paths into a closed path.
-Refinement and limit arguments remain separate checkpoints.
+The next implementation may package the path directly in the `q2` level-set
+subtype before introducing any Euclidean circle terminology. Refinement and
+limit arguments remain separate checkpoints.
diff --git a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
index 242393c5..713a092e 100644
--- a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
+++ b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
@@ -17,6 +17,10 @@ The positive reciprocal-square-root correction, normalized master edge,
 endpoint laws, continuity, and fixed-`q2` theorem are implemented in
 `DkMath.Analysis.DkReal.SemanticCF2DNormalize`.
 
+That module also implements all four normalized action translates, their
+seams, common fixed-`q2` law, phase-index periodicity, continuous paths, and
+the resulting closed four-phase path.
+
 The current implementation proves a four-state return:
 
 ```text
@@ -334,7 +338,8 @@ explicit.
 [IMPLEMENTED: semantic-cf2d-phase/path-topology]
 [IMPLEMENTED: semantic-cf2d-phase/path-concatenation]
 [IMPLEMENTED: semantic-cf2d-phase/boundary-normalization]
-[TODO: semantic-cf2d-phase/normalized-four-path]
+[IMPLEMENTED: semantic-cf2d-phase/normalized-four-path]
+[TODO: semantic-cf2d-phase/levelset-path]
 [TODO: semantic-cf2d-phase/refinement-law]
 [TODO: semantic-cf2d-phase/gaussian-limit]
 [TODO: semantic-cf2d-phase/pi-identification]
diff --git a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Basic.lean b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Basic.lean
index 244786b8..003565fe 100644
--- a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Basic.lean
+++ b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Basic.lean
@@ -61,6 +61,12 @@ def star [Ring R] (r z : Vec R) : Vec R :=
 @[simp]
 theorem q2_mk [Semiring R] (x y : R) : q2 (Vec.mk x y) = x ^ 2 + y ^ 2 := rfl
 
+/-- Scaling both coordinates scales square mass by the square of the scalar. -/
+theorem q2_scale [CommSemiring R] (c : R) (z : Vec R) :
+    q2 (Vec.mk (c * z.core) (c * z.beam)) = c ^ 2 * q2 z := by
+  simp [q2]
+  ring
+
 /-- The core coordinate of the neutral kernel is `1`. -/
 @[simp]
 theorem one_core [Zero R] [One R] : (one R).core = 1 := rfl
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
index 767870d7..640987eb 100644
--- a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
@@ -629,3 +629,25 @@ Archive
 4. 検証:
    - `lake build DkMath.Analysis.DkReal.SemanticCF2DNormalize` 成功
      (8277 jobs)。
+
+### 2026/06/23 06:35 JST (Normalized closed four-phase path)
+
+1. レビュー補正:
+   - 一般補題 `Vec.q2_scale` を追加した。
+   - `phaseNormalization_sq_mul_phaseDepth` を追加し、平方根補正の消去則を
+     独立 API とした。
+   - normalized edge の `q2` 証明をこれらの構造的補題で整理した。
+2. 四相:
+   - `normalizedPhaseEdgeAt` を master edge の action translate として
+     定義した。
+   - endpoint、seam、固定 `q2`、phase index の4周期性を証明した。
+   - 全 translated edge の連続性を証明した。
+3. closed path:
+   - 各 normalized edge を Mathlib `Path` に包装した。
+   - 4本を連結し、core-zero exact order four により `Path z z` を構成した。
+   - 円・角度なしで fixed-`q2` continuous closed path に到達した。
+4. 次段階:
+   - path の target を `LevelSet Real (q2 z)` へ強化する候補を記録した。
+5. 検証:
+   - `lake build DkMath.Analysis.DkReal.SemanticCF2DNormalize` 成功
+     (8277 jobs)。
````
`````
