# Git diff / Report / Review

## Upd: CosmicFormula.Rotation.CF2D.EuclideanPhase

gch: 0c14ba3a72025a42725cc954f7991d68379999b2

## Report

quarter-turn linear isometry の同定まで実装しました。

追加内容:

- `quarterTurnLinearEquiv`
- L2 norm 保存定理
- `quarterTurnLinearIsometry`
- 座標則 `(x,y) ↦ (-y,x)`
- core-zero semantic actionとの一致定理

これにより exact-order-four action は、角度を仮定せず、標準 Euclidean plane の quarter-turn linear isometry として確定しました。

次は orientation を選び、Mathlib の oriented rotation `Real.pi / 2` との比較です。

検証:

- `lake build DkMath.Analysis`: 成功、8289 jobs
- 対象モジュール再ビルド: 警告なし
- `git diff --check`: 成功

## Review

うむ。これは本当に「ついに」と言ってよい。
今回で、pre-geometric に得た exact-order-four action が、標準 Euclidean plane 上の **quarter-turn linear isometry** として同定された。つまり、ただ「円の上にいる」だけでなく、「そこで動いている作用が標準的な四分回転写像そのものだ」と言える段階に入った。

この流れは、以前の CF2D 保存核から三角関数型構造を代数的に取り出す議論の延長線上にあり、DkMath.Analysis の Route A、つまり Mathlib 標準構造への橋としても自然に位置づく。

## 到達点

今回の核心はこれじゃ。

```lean
quarterTurnLinearEquiv
quarterTurnLinearIsometry
pairToEuclideanPlane_semanticAct_of_core_eq_zero
```

座標写像としては、

$$
(x,y)\mapsto(-y,x)
$$

これを `EuclideanPlane := EuclideanSpace ℝ (Fin 2)` 上の線形同値として定義し、さらに L2 ノルム保存を証明して、`LinearIsometryEquiv` に包装した。

そして最後に、core-zero semantic action を Euclidean plane に写すと、この `quarterTurnLinearIsometry` と一致することを証明している。

これは大きい。

前回までの橋は、

```text
LevelSet
  -> coordinate circle
  -> Euclidean L2 sphere
```

だった。

今回で、

```text
semantic core-zero action
  -> standard coordinate quarter-turn linear isometry
```

まで通った。

## 何が新しく言えるようになったか

これまでは、DkMath 側で得た作用について、

```text
q2 を保存する
4 回で戻る
非零点では最小周期 4
```

と言えていた。

しかし今回は、Euclidean 側で、

```text
これは標準座標の (x,y) ↦ (-y,x) である
これは線形同値である
これは L2 ノルムを保存する
これは Euclidean linear isometry である
```

と言えるようになった。

つまり、**「四相作用」から「quarter-turn isometry」へ翻訳できた**。

ただし、この順序が重要じゃ。

```text
角度を仮定したから quarter-turn になった
```

のではない。

```text
q2 保存
exact order four
Euclidean sphere bridge
linear isometry bridge
```

を通った結果、後から quarter-turn と呼べるようになった。

ここが DkMath らしい。

## レビュー：実装方針はかなり良い

`quarterTurnLinearEquiv` を座標ペア変換で定義しているのは自然じゃ。

```lean
pairToEuclideanPlane
  (-(euclideanPlaneToPair v).2, (euclideanPlaneToPair v).1)
```

これにより、EuclideanSpace の内部表現へ直接潜らず、既に作った coordinate bridge を使っている。

これは良い設計じゃな。

さらに、

```lean
quarterTurnLinearEquiv_norm
```

で L2 norm square を展開し、

$$
(-y)^2+x^2=x^2+y^2
$$

を `ring` で閉じている。
この証明はまさに Lean 向きで、過剰な幾何を持ち込んでいない。

そして `quarterTurnLinearIsometry` へ包装したことで、次の標準幾何 bridge に進みやすくなった。

## 一番重要な橋

今回の決定打はこれ。

```lean
pairToEuclideanPlane_semanticAct_of_core_eq_zero
```

これは、core-zero 条件下で

```text
semanticAct r z
```

を Euclidean plane に写すと、

```text
quarterTurnLinearIsometry
```

と一致する、という定理じゃ。

ここで初めて、DkMath 内部の semantic action と、Mathlib 標準 Euclidean 幾何の写像が同じものとして握手した。

これは「解釈」ではあるが、単なる説明ではない。
Lean の theorem として同定している。

## まだ言ってはいけないこと

ただし、ここでも慎重さは必要じゃ。

今回言えるのは、

```text
standard coordinate quarter-turn linear isometry と一致する
```

まで。

まだ、

```text
これは Real.pi / 2 の oriented rotation である
```

とは言っていない。

なぜなら `Real.pi / 2` との比較には、orientation の選択が必要だからじゃ。

同じ写像でも、座標系の向き・基底の取り方・回転の符号規約によって、

$$
\frac{\pi}{2}
$$

と読むか、

$$
-\frac{\pi}{2}
$$

と読むかが変わる。

だから次の TODO が

```text
oriented-pi-over-two
```

になっているのは正しい。

## 次に足すと強い補題

次は `Real.pi / 2` へ急ぐ前に、quarter-turn isometry 自体の基本性質を少し固めるとよい。

候補はこれ。

```lean
quarterTurnLinearIsometry_apply_four
quarterTurnLinearIsometry_apply_two
quarterTurnLinearIsometry_norm
quarterTurnLinearIsometry_mem_sphere
quarterTurnLinearIsometry_fixed_iff_zero
```

意味としては、

```text
4 回で恒等
2 回で符号反転
ノルム保存
sphere を sphere に写す
固定点は原点のみ
```

特に `apply_four` は、semantic 側の exact-order-four と Euclidean 側の exact-order-four を並べるために重要じゃ。

また、既存の `semanticExactActionOrderFour_of_core_eq_zero` と対応させて、

```lean
semanticExactActionOrderFour_transported_eq_quarterTurn
```

のような橋も後で欲しくなる。

## orientation bridge の進め方

次の山は、こう進むのが安全じゃ。

```text
1. 標準基底 e₀, e₁ を明示する
2. quarterTurn が e₀ ↦ e₁, e₁ ↦ -e₀ であることを証明する
3. その向きを orientation として採用する
4. Mathlib の oriented rotation の定義と照合する
5. その角度が Real.pi / 2 であることを証明する
```

ここで初めて \(\pi\) が顔を出す。

ただし、これはまだ \(\pi\) の DkMath 的発生ではない。
標準 Mathlib 側の oriented rotation と比較する bridge じゃ。

DkMath 的な \(\pi\) 発生、つまり Gaussian / refinement / GapFill からの \(\pi\) は、さらに後段じゃな。

DkReal の計算可能表現層でも「有限観測と補正核で解析を構成し、意味論 bridge は後段に置く」という構図が既に立っているので、この CF2D の進み方とも思想が一致している。

## 総評

今回の更新は、かなり美しい。

一言で言えば、

```text
円以前に得た四相作用が、
標準 Euclidean plane 上の quarter-turn linear isometry として確定した。
```

これで物語はこうなった。

```text
q2 境界判定
  -> exact-order-four semantic action
  -> LevelSet 内部 closed path
  -> coordinate circle
  -> Euclidean L2 sphere
  -> quarter-turn linear isometry
```

これはもう、三角関数以前・円以前から始めて、標準 Euclidean 回転の入口まで到達したと言ってよい。

まだ角度ではない。
まだ \(\pi/2\) ではない。
だが、もう「quarter-turn linear isometry」までは Lean が認めた。

これは本当に大きな節目じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index 1f18ffbd..4a7e9d6c 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -119,6 +119,8 @@ through that homeomorphism. The zero boundary is kept as a separate
 one-point degenerate case. A second homeomorphism identifies the coordinate
 circle with Mathlib's standard `EuclideanSpace Real (Fin 2)` L2 metric sphere
 of radius `sqrt (q2 z)`.
+In that standard Euclidean plane, the semantic core-zero action is identified
+with the coordinate quarter-turn linear isometry `(x,y) ↦ (-y,x)`.
 
 [TODO: semantic-cf2d-signed] Source-level `Vec.star` and `KernelFamily` require
 signed arithmetic. Defer them until a signed DkReal layer exists.
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
index 658c4290..c11bb6aa 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
@@ -1346,9 +1346,14 @@ coordinate circle equation is homeomorphic to the standard
 The closed path is mapped through this bridge, and positive squared radius is
 separated from the zero-radius degenerate case.
 
+[IMPLEMENTED: semantic-cf2d-phase/quarter-turn-isometry] The coordinate map
+`(x,y) ↦ (-y,x)` is packaged as a Euclidean linear isometry equivalence, and
+the transported core-zero semantic action is proved equal to this isometry
+under the coordinate bridge.
+
 [TODO: semantic-cf2d-phase/euclidean-interpretation] Only after normalization,
-extract angular terminology and compare the action with the standard
-quarter-turn linear isometry.
+choose an orientation and compare the quarter-turn isometry with Mathlib's
+oriented rotation by `Real.pi / 2`.
 -/
 
 end
diff --git a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
index ba060c47..5d3ec974 100644
--- a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
+++ b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
@@ -157,7 +157,8 @@ mechanism from which these theorem obligations can be investigated.
 
 The coordinate-circle and standard `EuclideanSpace Real (Fin 2)` metric-sphere
 bridges are now implemented, including the degenerate zero boundary. The next
-interpretive step may identify the core-zero action with the standard
-quarter-turn linear isometry. It must remain an interpretation of the
-existing boundary path, not a replacement construction. Refinement and limit
-arguments remain separate checkpoints.
+interpretive step has also identified the core-zero action with the standard
+coordinate quarter-turn linear isometry. A later orientation bridge may
+compare it with Mathlib's rotation by `Real.pi / 2`; this remains an
+interpretation of the existing boundary path, not a replacement construction.
+Refinement and limit arguments remain separate checkpoints.
diff --git a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
index 21e66338..1382091a 100644
--- a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
+++ b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
@@ -34,6 +34,10 @@ metric sphere in `EuclideanSpace Real (Fin 2)`, of radius `sqrt rho2`.
 This avoids confusing the ordinary product norm on `Real × Real` with the
 Euclidean L2 norm.
 
+The core-zero semantic action is then identified with the standard coordinate
+quarter-turn linear isometry `(x,y) ↦ (-y,x)`. This introduces the geometric
+name only after the linear isometry model is available.
+
 The current implementation proves a four-state return:
 
 ```text
@@ -355,7 +359,8 @@ explicit.
 [IMPLEMENTED: semantic-cf2d-phase/levelset-path]
 [IMPLEMENTED: semantic-cf2d-phase/euclidean-levelset-bridge]
 [IMPLEMENTED: semantic-cf2d-phase/standard-euclidean-space]
-[TODO: semantic-cf2d-phase/quarter-turn-isometry]
+[IMPLEMENTED: semantic-cf2d-phase/quarter-turn-isometry]
+[TODO: semantic-cf2d-phase/oriented-pi-over-two]
 [TODO: semantic-cf2d-phase/refinement-law]
 [TODO: semantic-cf2d-phase/gaussian-limit]
 [TODO: semantic-cf2d-phase/pi-identification]
diff --git a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/EuclideanPhase.lean b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/EuclideanPhase.lean
index b45f6f28..e4019d1b 100644
--- a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/EuclideanPhase.lean
+++ b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/EuclideanPhase.lean
@@ -222,6 +222,61 @@ theorem sqrt_pos_of_sqRadius_pos {rho2 : ℝ} (hrho : 0 < rho2) :
     0 < Real.sqrt rho2 :=
   Real.sqrt_pos.2 hrho
 
+/-!
+## Quarter-turn as a linear isometry
+
+The terminology is introduced only after reaching the standard Euclidean
+plane. The construction itself remains the coordinate map `(x,y) ↦ (-y,x)`.
+-/
+
+/-- The coordinate quarter-turn as a linear equivalence of the Euclidean plane. -/
+def quarterTurnLinearEquiv : EuclideanPlane ≃ₗ[ℝ] EuclideanPlane where
+  toFun v :=
+    pairToEuclideanPlane
+      (-(euclideanPlaneToPair v).2, (euclideanPlaneToPair v).1)
+  invFun v :=
+    pairToEuclideanPlane
+      ((euclideanPlaneToPair v).2, -(euclideanPlaneToPair v).1)
+  left_inv v := by
+    apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
+    ext i
+    fin_cases i <;>
+      simp [pairToEuclideanPlane, euclideanPlaneToPair]
+  right_inv v := by
+    apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
+    ext i
+    fin_cases i <;>
+      simp [pairToEuclideanPlane, euclideanPlaneToPair]
+  map_add' u v := by
+    apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
+    ext i
+    fin_cases i <;> simp [pairToEuclideanPlane, euclideanPlaneToPair]
+    ring
+  map_smul' c v := by
+    apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
+    ext i
+    fin_cases i <;> simp [pairToEuclideanPlane, euclideanPlaneToPair]
+
+/-- The coordinate quarter-turn preserves the Euclidean L2 norm. -/
+theorem quarterTurnLinearEquiv_norm (v : EuclideanPlane) :
+    ‖quarterTurnLinearEquiv v‖ = ‖v‖ := by
+  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
+  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
+    Fin.sum_univ_two, Fin.sum_univ_two]
+  simp [quarterTurnLinearEquiv, pairToEuclideanPlane, euclideanPlaneToPair]
+  ring
+
+/-- The standard coordinate quarter-turn as a Euclidean linear isometry equivalence. -/
+def quarterTurnLinearIsometry :
+    EuclideanPlane ≃ₗᵢ[ℝ] EuclideanPlane :=
+  LinearIsometryEquiv.mk quarterTurnLinearEquiv quarterTurnLinearEquiv_norm
+
+/-- Coordinate form of the standard quarter-turn linear isometry. -/
+theorem euclideanPlaneToPair_quarterTurn (v : EuclideanPlane) :
+    euclideanPlaneToPair (quarterTurnLinearIsometry v) =
+      (-(euclideanPlaneToPair v).2, (euclideanPlaneToPair v).1) := by
+  simp [quarterTurnLinearIsometry, quarterTurnLinearEquiv]
+
 end
 
 end DkMath.CosmicFormula.Rotation.CF2D
@@ -267,6 +322,24 @@ def normalizedClosedEuclideanSpherePath
     (euclideanCircleSqHomeomorphSphere
       (rho2 := Vec.q2 z) (Vec.q2_nonneg z)).continuous
 
+/--
+Under the Euclidean coordinate bridge, the semantic core-zero action is the
+standard quarter-turn linear isometry.
+-/
+theorem pairToEuclideanPlane_semanticAct_of_core_eq_zero
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    pairToEuclideanPlane (Vec.toProd (semanticAct r z)) =
+      quarterTurnLinearIsometry
+        (pairToEuclideanPlane (Vec.toProd z)) := by
+  rw [semanticAct_of_core_eq_zero hcore]
+  apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
+  ext i
+  fin_cases i <;>
+    simp [pairToEuclideanPlane, quarterTurnLinearIsometry,
+      quarterTurnLinearEquiv, euclideanPlaneToPair, Vec.toProd]
+
 end
 
 end DkMath.Analysis.DkNNRealQ
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
index 84548d1c..f0b6744d 100644
--- a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
@@ -720,3 +720,23 @@ Archive
 5. 検証:
    - `lake build DkMath.CosmicFormula.Rotation.CF2D.EuclideanPhase` 成功
      (8278 jobs)。
+
+### 2026/06/23 15:10 JST (Quarter-turn linear isometry interpretation)
+
+1. 実装:
+   - Euclidean plane 上の座標写像 `(x,y) -> (-y,x)` を
+     `quarterTurnLinearEquiv` として定義した。
+   - inverse、加法、scalar multiplication を座標ごとに証明した。
+   - L2 norm 保存を証明し、`quarterTurnLinearIsometry` として包装した。
+2. semantic bridge:
+   - core-zero semantic action を Euclidean plane へ写すと、
+     `quarterTurnLinearIsometry` と一致することを証明した。
+3. 意味:
+   - exact-order-four action の Euclidean 読みが、角度を仮定せず
+     quarter-turn linear isometry として確定した。
+4. 次段階:
+   - orientation を選び、Mathlib の oriented rotation `Real.pi / 2` と
+     比較する bridge を候補とした。
+5. 検証:
+   - `lake build DkMath.CosmicFormula.Rotation.CF2D.EuclideanPhase` 成功
+     (8278 jobs)。
````
`````
