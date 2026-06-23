# Git diff / Report / Review

## Upd: CosmicFormula.Rotation.CF2D.EuclideanPhase

gch: 5f09f9e98279b7027ac8ebbc91e4f3e3f37a0625

## Report

次の checkpoint を完了しました。

- Euclidean plane の標準 orientation を complex plane から移送
- quarter-turn と複素数の `I` 倍を同定
- `quarterTurnLinearIsometry = rotation (Real.pi / 2)` を証明
- TODO、研究資料、タスク資料、履歴を同期
- `lake build DkMath.Analysis` 成功（8289 jobs）
- `git diff --check` 成功

次の本線は refinement law と Gaussian limit です。πとの同定は、現時点では標準 Euclidean 幾何への解釈であり、内在的導出とは明確に分離しています。

## Review

ついに来たな。
これは、CF2D の Euclidean 解釈フェーズとしては **大きな閉じ** じゃ。

今回で、

```text id="9fc5ab"
core-zero semantic action
  -> coordinate quarter-turn linear isometry
  -> oriented rotation by Real.pi / 2
```

まで通った。

つまり、円以前・角度以前に得ていた四相作用が、標準 Euclidean 幾何へ移したあと、Mathlib の向き付き回転として

$$
\operatorname{rotation}\left(\frac{\pi}{2}\right)
$$

と一致するところまで Lean が認めた、ということじゃ。

## 状況解説

前回までの流れはこうだった。

```text id="6wd9gp"
q2 保存作用
  -> exact order four
  -> LevelSet 上の closed path
  -> coordinate circle
  -> Euclidean L2 sphere
  -> quarter-turn linear isometry
```

今回さらに、

```text id="0xb81f"
Euclidean plane の orientation を選ぶ
quarter-turn を complex multiplication by I と同定する
right-angle rotation と同定する
rotation (Real.pi / 2) と同定する
```

まで進んだ。

ここで重要なのは、「向き」を先に固定してから \(\pi/2\) と言っていることじゃ。

向きを選ばないままでは、

$$
\frac{\pi}{2}
$$

なのか、

$$
-\frac{\pi}{2}
$$

なのかが決まらない。
今回の実装では、complex plane の標準 orientation を Euclidean plane へ引き戻して、その向きで正の quarter-turn を決めている。

これはかなり堅い。

## 実装の核

中心はこのあたりじゃな。

```lean id="e57cde"
euclideanPlaneComplexIsometry
euclideanPlaneOrientation
euclideanPlaneComplexIsometry_quarterTurn
rightAngleRotation_eq_quarterTurn
rotation_pi_div_two_eq_quarterTurn
```

`euclideanPlaneComplexIsometry` で、標準二次元 Euclidean plane を complex plane と線形等長同型で結ぶ。

次に、

```lean id="6m6lsw"
euclideanPlaneOrientation
```

で、complex plane の標準 orientation を Euclidean plane 側へ pullback する。

そのうえで、

```lean id="1ma5d0"
euclideanPlaneComplexIsometry_quarterTurn
```

により、明示的な quarter-turn が複素数側では

$$
z\mapsto i z
$$

に対応することを示す。

ここが決定打じゃ。

そして Mathlib 側の

```lean id="l8mibo"
rotation_pi_div_two
```

へ接続し、

```lean id="olz22j"
rotation_pi_div_two_eq_quarterTurn
```

が出る。

## 数学的な意味

今回、初めて \(\pi/2\) が登場した。
しかし、これは **内在的に \(\pi\) を導出した** という意味ではない。

正確には、

```text id="qcoxhi"
pre-geometric に構成した作用を、
標準 Euclidean 幾何へ解釈したとき、
Mathlib の oriented rotation by Real.pi / 2 と一致した
```

という意味じゃ。

これは非常に重要な区別。

DkMath 内部で \(\pi\) が発生したわけではまだない。
今回は Mathlib 標準 Euclidean 幾何の中にすでにある \(\pi\) と、DkMath 側の四相作用が一致した。

つまり、

```text id="q03cqx"
π の内在的導出ではなく、
π/2 回転との外部解釈 bridge
```

じゃな。

この区別を資料に明記しているのは非常に良い。

## ここまでの物語としての到達点

いま、DkMath の円以前の物語はこう閉じた。

```text id="ywl6x4"
q2 を境界判定機として置く
四相作用が現れる
直線でつなぐ
くぼみが出る
phaseDepth を得る
sqrt 補正で境界へ戻る
LevelSet 上の closed path になる
coordinate circle と同一視する
Euclidean L2 sphere と同一視する
quarter-turn linear isometry と同一視する
orientation を選ぶ
rotation (Real.pi / 2) と同一視する
```

これは本当に見事じゃ。

最初に円を仮定していない。
最初に角度を仮定していない。
最初に \(\pi\) を仮定していない。

最後に標準幾何へ移したとき、

$$
\frac{\pi}{2}
$$

という名前が付いた。

この順序が DkMath の価値じゃ。

## レビュー：実装方針は正しい

特に良い点は三つある。

第一に、orientation を complex plane から移送していること。
これは sign convention を曖昧にしない。`Complex.I` 倍と quarter-turn を同定することで、「正の向き」が明確になっている。

第二に、`rightAngleRotation` を経由していること。
いきなり `rotation (Real.pi / 2)` に飛ぶのではなく、Mathlib の幾何 API に沿っている。これにより theorem の意味が自然になる。

第三に、資料側で「これは内在的 \(\pi\) 導出ではない」と明記していること。
ここは本当に重要。過大主張を避けているので、外向けにも堅い。

## 追加するとさらに強い bridge theorem

今の theorem は EuclideanPhase 内では閉じている。
次に欲しくなるのは、semantic action から直接 `rotation (Real.pi / 2)` へつなぐ合成定理じゃ。

たとえば名前候補は、

```lean id="1jd4ip"
pairToEuclideanPlane_semanticAct_eq_rotation_pi_div_two
```

内容は概念的にはこう。

```lean id="5okxmb"
pairToEuclideanPlane (Vec.toProd (semanticAct r z))
  =
euclideanPlaneOrientation.rotation (Real.pi / 2)
  (pairToEuclideanPlane (Vec.toProd z))
```

仮定はもちろん、

```lean id="39s0eg"
hcore : semanticValue (r : Vec DkNNRealQ).core = 0
```

じゃ。

これは既存の

```lean id="1rpdc0"
pairToEuclideanPlane_semanticAct_of_core_eq_zero
rotation_pi_div_two_eq_quarterTurn
```

をつなげば出るはず。

この定理があると、読者向けにはかなり分かりやすい。

```text id="q451qd"
core-zero semantic action is the oriented pi-over-two rotation
```

を一行で言える。

## 次の本線：refinement law

報告通り、次の本線は `refinement law` と `Gaussian limit` でよい。

なぜなら、Euclidean 解釈フェーズはかなり閉じたからじゃ。

ここから先に進むなら、二つの道を分ける必要がある。

```text id="2tlfms"
外部解釈ルート:
  Mathlib の Euclidean geometry / Real.pi と接続する

内在導出ルート:
  phaseDepth, refinement, Gaussian limit から π を導く
```

今回完了したのは外部解釈ルート。

次に進むべきは内在導出ルートじゃ。

つまり、

```text id="byemjf"
直線補間のくぼみ
phaseDepth
sqrt normalization
refinement
limit profile
Gaussian
π identification
```

へ戻る。

この切り替えは大事じゃな。

## 注意点

一点だけ構造上の注意を挙げるなら、`EuclideanPhase.lean` がかなり大きくなってきている。

今このファイルには、

```text id="m5lcmu"
coordinate circle bridge
Euclidean sphere bridge
quarter-turn isometry
oriented rotation pi/2 bridge
semantic action bridge
```

が全部入っている。

しばらくはこのままでよいが、将来的には分割候補がある。

```text id="jjvt17"
CF2D.EuclideanPhase.Basic
CF2D.EuclideanPhase.Sphere
CF2D.EuclideanPhase.QuarterTurn
CF2D.EuclideanPhase.OrientedRotation
```

ただ、現時点ではまだ定理群を育てている段階なので、無理に分ける必要はない。
安定してからでよい。

## 総評

これは大成果じゃ。

一言でまとめるなら、

```text id="j5erq2"
円以前・角度以前に得た core-zero 四相作用が、
標準 Euclidean plane の oriented rotation by Real.pi / 2 として解釈された。
```

しかも、\(\pi\) を内在的に導出したとは言っていない。
これはあくまで標準 Euclidean 幾何への解釈 bridge。

だから、現在の到達点はこう。

```text id="rqwdri"
外部標準幾何との同定:
  完了に近い

内在的 π 導出:
  refinement law / Gaussian limit として次段階
```

ここまでで、CF2D Phase の Euclidean interpretation はかなり美しく閉じた。
次はいよいよ、DkMath 独自の \(\pi\) へ向かう本線じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
index c11bb6aa..96076fc9 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
@@ -1351,9 +1351,11 @@ separated from the zero-radius degenerate case.
 the transported core-zero semantic action is proved equal to this isometry
 under the coordinate bridge.
 
-[TODO: semantic-cf2d-phase/euclidean-interpretation] Only after normalization,
-choose an orientation and compare the quarter-turn isometry with Mathlib's
-oriented rotation by `Real.pi / 2`.
+[IMPLEMENTED: semantic-cf2d-phase/oriented-pi-over-two] The standard
+orientation is pulled back from Mathlib's complex plane, and the quarter-turn
+isometry is proved equal to the resulting oriented rotation by
+`Real.pi / 2`. This is a Euclidean interpretation theorem; it does not yet
+derive `pi` intrinsically from the pre-geometric phase construction.
 -/
 
 end
diff --git a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
index 5d3ec974..26692593 100644
--- a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
+++ b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
@@ -158,7 +158,9 @@ mechanism from which these theorem obligations can be investigated.
 The coordinate-circle and standard `EuclideanSpace Real (Fin 2)` metric-sphere
 bridges are now implemented, including the degenerate zero boundary. The next
 interpretive step has also identified the core-zero action with the standard
-coordinate quarter-turn linear isometry. A later orientation bridge may
-compare it with Mathlib's rotation by `Real.pi / 2`; this remains an
-interpretation of the existing boundary path, not a replacement construction.
+coordinate quarter-turn linear isometry. After pulling back Mathlib's standard
+complex orientation, that isometry is now proved equal to the oriented
+rotation by `Real.pi / 2`. This remains an interpretation of the existing
+boundary action, not an intrinsic derivation of `pi` and not a replacement
+construction.
 Refinement and limit arguments remain separate checkpoints.
diff --git a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
index 1382091a..3361293f 100644
--- a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
+++ b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
@@ -360,11 +360,10 @@ explicit.
 [IMPLEMENTED: semantic-cf2d-phase/euclidean-levelset-bridge]
 [IMPLEMENTED: semantic-cf2d-phase/standard-euclidean-space]
 [IMPLEMENTED: semantic-cf2d-phase/quarter-turn-isometry]
-[TODO: semantic-cf2d-phase/oriented-pi-over-two]
+[IMPLEMENTED: semantic-cf2d-phase/oriented-pi-over-two]
 [TODO: semantic-cf2d-phase/refinement-law]
 [TODO: semantic-cf2d-phase/gaussian-limit]
 [TODO: semantic-cf2d-phase/pi-identification]
-[TODO: semantic-cf2d-phase/euclidean-interpretation]
 ```
 
 The longer route from this local quadratic profile to a possible
diff --git a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/EuclideanPhase.lean b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/EuclideanPhase.lean
index e4019d1b..7e18dcca 100644
--- a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/EuclideanPhase.lean
+++ b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/EuclideanPhase.lean
@@ -6,6 +6,7 @@ Authors: D. and Wise Wolf.
 
 import DkMath.Analysis.DkReal.SemanticCF2DNormalize
 import Mathlib.Analysis.InnerProductSpace.PiL2
+import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
 import Mathlib.Topology.Homeomorph.Defs
 
 #print "file: DkMath.CosmicFormula.Rotation.CF2D.EuclideanPhase"
@@ -277,6 +278,70 @@ theorem euclideanPlaneToPair_quarterTurn (v : EuclideanPlane) :
       (-(euclideanPlaneToPair v).2, (euclideanPlaneToPair v).1) := by
   simp [quarterTurnLinearIsometry, quarterTurnLinearEquiv]
 
+/-!
+## Oriented angle interpretation
+
+The standard orientation is pulled back from Mathlib's complex-plane
+orientation through the orthonormal basis equivalence. This fixes the sign
+convention before mentioning `pi / 2`.
+-/
+
+/-- Standard Euclidean-plane coordinates interpreted as a complex number. -/
+def euclideanPlaneComplexIsometry : EuclideanPlane ≃ₗᵢ[ℝ] ℂ :=
+  (EuclideanSpace.basisFun (Fin 2) ℝ).equiv
+    Complex.orthonormalBasisOneI (Equiv.refl (Fin 2))
+
+local instance euclideanPlaneFinrankTwo :
+    Fact (Module.finrank ℝ EuclideanPlane = 2) :=
+  ⟨finrank_euclideanSpace_fin⟩
+
+/-- The orientation whose positive quarter-turn agrees with multiplication by `I`. -/
+def euclideanPlaneOrientation : Orientation ℝ EuclideanPlane (Fin 2) :=
+  (Orientation.map (Fin 2) euclideanPlaneComplexIsometry.toLinearEquiv).symm
+    Complex.orientation
+
+/-- The chosen orientation transports to Mathlib's standard complex orientation. -/
+theorem euclideanPlaneOrientation_map_complex :
+    Orientation.map (Fin 2) euclideanPlaneComplexIsometry.toLinearEquiv
+      euclideanPlaneOrientation = Complex.orientation := by
+  exact Equiv.apply_symm_apply _ _
+
+/-- Complex coordinates of the explicit quarter-turn are multiplication by `I`. -/
+theorem euclideanPlaneComplexIsometry_quarterTurn (v : EuclideanPlane) :
+    euclideanPlaneComplexIsometry (quarterTurnLinearIsometry v) =
+      Complex.I * euclideanPlaneComplexIsometry v := by
+  simp [euclideanPlaneComplexIsometry, quarterTurnLinearIsometry,
+    quarterTurnLinearEquiv, pairToEuclideanPlane, euclideanPlaneToPair,
+    OrthonormalBasis.equiv]
+  change
+    (-(v 1 : ℂ) + (v 0 : ℂ) * Complex.I) =
+      Complex.I * ((v 0 : ℂ) + (v 1 : ℂ) * Complex.I)
+  rw [mul_add, ← mul_assoc,
+    show Complex.I * (v 1 : ℂ) = (v 1 : ℂ) * Complex.I by ring,
+    mul_assoc, Complex.I_mul_I]
+  ring
+
+/-- The chosen orientation's right-angle rotation is the explicit quarter-turn. -/
+theorem rightAngleRotation_eq_quarterTurn :
+    euclideanPlaneOrientation.rightAngleRotation =
+      quarterTurnLinearIsometry := by
+  apply LinearIsometryEquiv.ext
+  intro v
+  apply euclideanPlaneComplexIsometry.injective
+  rw [euclideanPlaneOrientation.rightAngleRotation_map_complex
+    euclideanPlaneComplexIsometry euclideanPlaneOrientation_map_complex]
+  exact (euclideanPlaneComplexIsometry_quarterTurn v).symm
+
+/--
+The explicit quarter-turn is Mathlib's oriented rotation by `pi / 2` for the
+chosen standard orientation.
+-/
+theorem rotation_pi_div_two_eq_quarterTurn :
+    euclideanPlaneOrientation.rotation (Real.pi / 2 : ℝ) =
+      quarterTurnLinearIsometry := by
+  rw [euclideanPlaneOrientation.rotation_pi_div_two,
+    rightAngleRotation_eq_quarterTurn]
+
 end
 
 end DkMath.CosmicFormula.Rotation.CF2D
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
index f0b6744d..c539e641 100644
--- a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
@@ -740,3 +740,22 @@ Archive
 5. 検証:
    - `lake build DkMath.CosmicFormula.Rotation.CF2D.EuclideanPhase` 成功
      (8278 jobs)。
+
+### 2026/06/23 15:26 JST (Oriented rotation by pi/2 bridge)
+
+1. orientation:
+   - Euclidean plane と complex plane の orthonormal-basis isometry を定義した。
+   - complex plane の標準 orientation を Euclidean plane へ引き戻した。
+2. rotation bridge:
+   - 座標 quarter-turn が complex multiplication by `I` に写ることを証明した。
+   - chosen orientation の right-angle rotation と
+     `quarterTurnLinearIsometry` を同定した。
+   - Mathlib の `rotation_pi_div_two` により、quarter-turn が oriented
+     rotation by `Real.pi / 2` に等しいことを証明した。
+3. 境界:
+   - これは既存の pre-geometric action の Euclidean 解釈であり、
+     `pi` の内在的導出ではない。refinement、Gaussian limit、
+     pi identification は独立した未実装課題として維持する。
+4. 検証:
+   - `lake build DkMath.CosmicFormula.Rotation.CF2D.EuclideanPhase` 成功
+     (8278 jobs)。
````
`````
