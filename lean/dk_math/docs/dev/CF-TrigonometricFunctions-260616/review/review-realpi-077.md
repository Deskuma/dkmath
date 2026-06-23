# Git diff / Report / Review

## Upd: CosmicFormula.Rotation.CF2D.EuclideanPhase

gch: 4eb1ff6673b1c4fa919dd367fd9a3703c2f3dfd6

## Report

次の checkpoint を完了しました。

- semantic core-zero action と `rotation (Real.pi / 2)` を直接結ぶ定理を追加
- refinement を dyadic nodes、反射則、親子 subdivision 則へ具体化
- Gaussian・無限積の先取りを避ける方針を文書化
- `lake build DkMath.Analysis` 成功（8289 jobs）
- `git diff --check` 成功

次は finite dyadic phase nodes の Lean 実装です。

## Review

うむ。今回の更新は、二つの意味でよい checkpoint じゃ。

一つは、前回までに得た

```text id="m6bnnh"
semantic core-zero action
  -> quarter-turn linear isometry
  -> rotation (Real.pi / 2)
```

を、読者が一発で使える **直接定理** として閉じたこと。

もう一つは、次の本線である refinement / Gaussian / 内在的 \(\pi\) 導出へ進む前に、有限段階の dyadic nodes から始める、と方針をはっきり切ったことじゃ。

## 今回の到達点

追加された主役はこれじゃな。

```lean id="k3u2o4"
pairToEuclideanPlane_semanticAct_eq_rotation_pi_div_two
```

意味はこう。

$$
\mathrm{pairToEuclideanPlane}(\mathrm{semanticAct}(r,z))
$$

は、core-zero 条件のもとで、

$$
\mathrm{rotation}\left(\frac{\pi}{2}\right)
$$

を `pairToEuclideanPlane (Vec.toProd z)` に作用させたものと一致する。

つまり、以前までの橋を合成して、

```text id="1s59lk"
DkMath の semantic action
  が
Mathlib の oriented rotation by pi/2
  として読める
```

を一つの theorem にした。

これは非常に良い。
レビュー・論文・外部説明では、この定理が一番引用しやすい。

## ここで閉じたもの

ここまでで Euclidean 解釈ルートは、ほぼ一本の完成した橋になった。

```text id="d6fyui"
q2 保存
  -> exact-order-four action
  -> LevelSet closed path
  -> coordinate circle
  -> Euclidean L2 sphere
  -> quarter-turn linear isometry
  -> oriented rotation by Real.pi / 2
  -> semantic action direct bridge
```

この流れはかなり美しい。

特に重要なのは、最後まで順序が崩れていないことじゃ。

```text id="hq3nqb"
先に π/2 回転を仮定した
```

のではなく、

```text id="jfmswl"
pre-geometric action を標準 Euclidean 幾何へ移したら、
Mathlib の rotation (Real.pi / 2) と一致した
```

という形になっている。

この違いは大きい。

## レビュー：直接定理の追加は正しい

今回の定理は、前回の賢狼レビューで「欲しくなる」と言った形そのものじゃ。

```lean id="9agkm0"
pairToEuclideanPlane_semanticAct_of_core_eq_zero
rotation_pi_div_two_eq_quarterTurn
```

この二つをつなぐだけで出る。
だから実装としても薄く、意味としては強い。

こういう theorem は bridge 層でとても大事じゃ。

個別の小定理は内部構成を示す。
合成定理は外部読者に「結局何が言えるのか」を示す。

今回、その外向けの結論が得られた。

## \(\pi\) についての線引きも良い

文書側で、

```text id="e554v3"
これは Euclidean interpretation theorem であり、
pre-geometric phase construction から pi を内在的に導出したものではない
```

と明記しているのは非常に良い。

ここを曖昧にすると、過大主張に見える。

今回得た \(\pi/2\) は、Mathlib の標準 Euclidean 幾何・標準 orientation・標準 complex orientation への橋を通じた外部解釈じゃ。

DkMath 内部から \(\pi\) が生まれた、という話はまだ別。

だから現在の整理はこう。

```text id="5v4dk6"
外部解釈:
  DkMath の四相作用は Mathlib の rotation (Real.pi / 2) と一致する

内在的導出:
  phaseDepth、refinement、Gaussian limit から π を得る道は未実装
```

この分離は本当に大事じゃ。

## refinement 設計の更新がかなり良い

今回、研究資料側で Milestone C がかなり具体化された。

特に良いのは、

```text id="3m7di2"
infinite product
logarithmic sum
Gaussian limit
```

を先取りしない、と明記した点じゃ。

これは賢い。

今あるのは、まだ有限段階の構造。

まずは dyadic nodes。

$$
t_{n,k}=\frac{k}{2^n}
$$

ここから始めるべきじゃ。

次に、端点。

$$
t_{n,0}=0
$$

$$
t_{n,2^n}=1
$$

そして反射。

$$
t_{n,2^n-k}=1-t_{n,k}
$$

さらに親子 subdivision。

$$
t_{n+1,2k}=t_{n,k}
$$

$$
t_{n+1,2k+1}
=\frac{t_{n,k}+t_{n,k+1}}{2}
$$

ここまでが有限 combinatorics。
Gaussian も \(\pi\) もまだ不要じゃ。

## 次の Lean 実装案

次は `EuclideanPhase.lean` に入れるより、別ファイルの方がよいかもしれぬ。

候補名は、

```text id="4qeqxo"
DkMath.Analysis.DkReal.SemanticCF2DRefinement
```

または軽く、

```text id="9223g2"
DkMath.Analysis.DkReal.SemanticCF2DDyadic
```

定義候補はこう。

```lean id="q9f6be"
def dyadicDenom (n : ℕ) : ℕ :=
  2 ^ n

def dyadicPhaseNode (n k : ℕ) : ℝ :=
  (k : ℝ) / (2 ^ n : ℝ)
```

そして最初に閉じる定理は、

```lean id="15zwsm"
dyadicPhaseNode_zero
dyadicPhaseNode_last
dyadicPhaseNode_reflect
dyadicPhaseNode_child_even
dyadicPhaseNode_child_odd_mid
```

あたり。

特に `child_even` と `child_odd_mid` が refinement の入口じゃ。

## phaseDepth との接続

次に、今回の資料にある通り、centered quadratic form を明示するとよい。

既に同等の補題があるなら再利用でよいが、形としては、

$$
\operatorname{phaseDepth}(t)
============================

\frac12+2\left(t-\frac12\right)^2
$$

これを dyadic nodes に代入する。

すると反射対称はかなり扱いやすい。

$$
\operatorname{phaseDepth}(t_{n,2^n-k})
======================================

\operatorname{phaseDepth}(t_{n,k})
$$

これはすぐ欲しくなる。

定理名候補は、

```lean id="ew4n9n"
phaseDepth_dyadic_reflect
```

じゃな。

## refinement law でまだ決めない方がよい点

資料にも書いてある通り、局所補正が

```text id="gbygr4"
乗法的に合成されるのか
log を取って加法的に見るべきか
```

は、まだ仮定しない方がよい。

ここは実際に有限合成則を証明してから決めるべきじゃ。

候補は二つある。

```text id="ob0gbn"
correction multiplier:
  phaseNormalization(t)

boundary-depth defect:
  phaseDepth(t)

log-depth:
  log phaseDepth(t)
```

どれを「refinement の主量」にするかで、後の極限が変わる。

だから、まずは有限列として全部持つ。

```lean id="75z61d"
dyadicPhaseDepthSeq n
dyadicPhaseNormalizationSeq n
```

のようにし、総積や総和は後で定義するのが安全じゃ。

## 今回の総評

今回の成果は、外部解釈ルートを閉じ、内在ルートへ戻る準備をしたことじゃ。

一言で言えば、

```text id="ymz7qg"
core-zero semantic action は、標準 Euclidean 幾何では rotation (Real.pi / 2) と直接一致する。
しかし π の内在的導出は、finite dyadic refinement から改めて始める。
```

この整理が非常に良い。

ここで焦って Gaussian や無限積へ飛ぶと危ない。
まず有限 dyadic nodes。
反射則。
親子分割則。
phaseDepth の有限 refinement。

その後に初めて、

```text id="sxbku4"
この有限構造を極限へ送ると何が残るのか
```

を問える。

## 次の checkpoint

次の checkpoint はこれでよい。

```text id="chqg6e"
finite dyadic phase nodes の Lean 実装
```

具体的な成功条件は、

```text id="lpk9g3"
dyadic node の端点定理
反射定理
親子 subdivision 定理
phaseDepth の反射定理
```

まで。

ここまで閉じれば、refinement law の地面ができる。

## 最終評価

これはかなり堅い更新じゃ。

Euclidean interpretation は、

```text id="jj4m04"
DkMath 四相作用
  -> Mathlib rotation (Real.pi / 2)
```

まで到達した。

そして、そこから先の内在的 \(\pi\) への道は、

```text id="q3cgxh"
dyadic refinement
  -> finite correction law
  -> asymptotic profile
  -> Gaussian limit
  -> pi identification
```

として、あらためて正しい順序に戻された。

これでよい。
いまは「外部の \(\pi/2\) と握手した」段階。
次は「内部から \(\pi\) がどう現れるか」を有限 refinement から掘る段階じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
index 96076fc9..705cc278 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
@@ -1354,8 +1354,10 @@ under the coordinate bridge.
 [IMPLEMENTED: semantic-cf2d-phase/oriented-pi-over-two] The standard
 orientation is pulled back from Mathlib's complex plane, and the quarter-turn
 isometry is proved equal to the resulting oriented rotation by
-`Real.pi / 2`. This is a Euclidean interpretation theorem; it does not yet
-derive `pi` intrinsically from the pre-geometric phase construction.
+`Real.pi / 2`. A direct composite theorem identifies the transported
+core-zero semantic action with that rotation. This is a Euclidean
+interpretation theorem; it does not yet derive `pi` intrinsically from the
+pre-geometric phase construction.
 -/
 
 end
diff --git a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
index 26692593..204a8b0c 100644
--- a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
+++ b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
@@ -117,10 +117,23 @@ theorem, not inserted as notation.
 
 ### Milestone C: refinement law
 
-1. Define dyadic or rational subdivision of an affine phase.
-2. Express the total correction as a finite product or sum of logarithms.
-3. Prove compatibility under refinement.
-4. Identify the exact local quadratic term controlling the limit.
+1. Define a finite partition of one affine phase, initially by the dyadic
+   nodes `k / 2^n`.
+2. Define the local boundary correction from the exact identity
+   `q2 (semanticPhaseEdge r z t) = phaseDepth t * q2 z`.
+3. Specify whether refinement composes corrections multiplicatively or,
+   after taking logarithms, additively. This choice must be made by a proved
+   composition law rather than by analogy with Gaussian normalization.
+4. Prove the one-step refinement equation comparing level `n` with
+   level `n + 1`.
+5. Identify the centered quadratic term
+   `2 * (t - 1/2)^2 + 1/2` as the exact local datum controlling any later
+   asymptotic statement.
+
+The first implementation checkpoint is deliberately finite: dyadic nodes,
+their reflection symmetry, and a theorem stating how one subdivision level
+refines the preceding level. No infinite product or Gaussian claim belongs
+in that checkpoint.
 
 ### Milestone D: limit and Gaussian bridge
 
diff --git a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
index 3361293f..6f8e4895 100644
--- a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
+++ b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
@@ -361,7 +361,12 @@ explicit.
 [IMPLEMENTED: semantic-cf2d-phase/standard-euclidean-space]
 [IMPLEMENTED: semantic-cf2d-phase/quarter-turn-isometry]
 [IMPLEMENTED: semantic-cf2d-phase/oriented-pi-over-two]
-[TODO: semantic-cf2d-phase/refinement-law]
+[TODO: semantic-cf2d-phase/dyadic-refinement] Define finite dyadic phase
+nodes, prove their endpoint and reflection laws, and state the finite
+one-step subdivision relation before introducing any limit.
+[TODO: semantic-cf2d-phase/refinement-law] Select and prove the composition
+law for local boundary corrections. Do not assume that it is an infinite
+product or a logarithmic sum before this finite law is established.
 [TODO: semantic-cf2d-phase/gaussian-limit]
 [TODO: semantic-cf2d-phase/pi-identification]
 ```
diff --git a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/EuclideanPhase.lean b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/EuclideanPhase.lean
index 7e18dcca..2a628787 100644
--- a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/EuclideanPhase.lean
+++ b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/EuclideanPhase.lean
@@ -352,6 +352,10 @@ open DkMath.CosmicFormula.Rotation.CF2D
 
 noncomputable section
 
+local instance euclideanPlaneFinrankTwo :
+    Fact (Module.finrank ℝ EuclideanPlane = 2) :=
+  ⟨finrank_euclideanSpace_fin⟩
+
 /--
 The normalized closed level-set path interpreted in the explicit Euclidean
 circle equation with squared radius `q2 z`.
@@ -405,6 +409,24 @@ theorem pairToEuclideanPlane_semanticAct_of_core_eq_zero
     simp [pairToEuclideanPlane, quarterTurnLinearIsometry,
       quarterTurnLinearEquiv, euclideanPlaneToPair, Vec.toProd]
 
+/--
+Under the Euclidean coordinate bridge, the semantic core-zero action is
+Mathlib's oriented rotation by `pi / 2`.
+
+This theorem composes the pre-geometric semantic-action bridge with the
+chosen Euclidean orientation. It is an external interpretation of the action,
+not an intrinsic construction of `pi`.
+-/
+theorem pairToEuclideanPlane_semanticAct_eq_rotation_pi_div_two
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    pairToEuclideanPlane (Vec.toProd (semanticAct r z)) =
+      euclideanPlaneOrientation.rotation (Real.pi / 2 : ℝ)
+        (pairToEuclideanPlane (Vec.toProd z)) := by
+  rw [pairToEuclideanPlane_semanticAct_of_core_eq_zero hcore,
+    rotation_pi_div_two_eq_quarterTurn]
+
 end
 
 end DkMath.Analysis.DkNNRealQ
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
index c539e641..5f2f41c0 100644
--- a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
@@ -759,3 +759,14 @@ Archive
 4. 検証:
    - `lake build DkMath.CosmicFormula.Rotation.CF2D.EuclideanPhase` 成功
      (8278 jobs)。
+
+### 2026/06/23 (Direct semantic rotation bridge and refinement preparation)
+
+1. bridge:
+   - core-zero semantic action を Euclidean plane へ移した結果が、chosen
+     orientation の `rotation (Real.pi / 2)` に直接等しい合成定理を追加した。
+2. refinement design:
+   - 次段階を finite dyadic nodes、reflection、one-step subdivision relation
+     に分解した。
+   - infinite product、logarithmic sum、Gaussian limit は、有限合成則が
+     証明されるまで仮定しない方針を明記した。
````
`````
