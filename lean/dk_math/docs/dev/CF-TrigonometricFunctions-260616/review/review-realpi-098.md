# Git diff / Report / Review

## Upd: CosmicFormula.Rotation.CF2D.EuclideanPhase

gch: b92e126b47c243c1a4557139a832ef022fdcf13b

## Report

進めました。今回は極限側には寄せすぎず、三角関数・π・角度 θ の本線入口として、Euclidean 解釈層に DkMath 名の角度橋を追加しました。

変更点:

- [EuclideanPhase.lean](/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/EuclideanPhase.lean)
  - `semanticQuarterTurnAngle : ℝ := Real.pi / 2`
  - `rotation_semanticQuarterTurnAngle_eq_quarterTurn`
  - `pairToEuclideanPlane_semanticAct_eq_rotation_semanticQuarterTurnAngle`
- [research-pregeometric-pi-program-067.md](/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md)
  - “first angle reading” milestone を追加
  - これは π の内在的構成ではなく、既存の四状態作用を Euclidean モデルで `theta = pi / 2` と読む bridge だと明記
- [History.md](/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md)
  - 今回の checkpoint を追記

検証:

- `lake build DkMath.CosmicFormula.Rotation.CF2D.EuclideanPhase` 成功
- `lake build DkMath.Analysis` 成功
- `git diff --check` 成功

`CF2D.lean` の集約 import には今回は触れていません。`EuclideanPhase` は Analysis 側にも依存する重い bridge なので、core algebra の入口を重くしない判断です。次はこの `semanticQuarterTurnAngle` を基準に、半回転・四回転・角度加法の語彙を育てるのが自然です。

## Review

うむ、賢狼レビューじゃ。
今回の差分は **採用でよい** 。これは「極限から \(\pi\) へ行く道」とは別に、**対称性・四状態作用・Euclidean rotation から角度 \(\theta\) を読む入口** を作った checkpoint じゃ。

今回の report では、`EuclideanPhase.lean` に `semanticQuarterTurnAngle : ℝ := Real.pi / 2`、`rotation_semanticQuarterTurnAngle_eq_quarterTurn`、`pairToEuclideanPlane_semanticAct_eq_rotation_semanticQuarterTurnAngle` が追加され、研究メモには “first angle reading” milestone が追加された。これは \(\pi\) の内在的構成ではなく、既存の四状態作用を Euclidean モデル上で \(\theta=\pi/2\) と読む bridge だ、と明記されている。ここが非常に大事じゃ。

## 1. 状況解説

これまでの本線は、CF2D の保存核から始まっていた。

```text id="h4hrux"
代数層:
  q2 保存
  semantic action
  exact order four

解析層:
  affine filling
  phaseDepth
  normalization
  log / moment / limit

Euclidean 解釈層:
  standard plane
  coordinate quarter-turn
  Real.pi / 2 rotation
```

今回の差分は、この三段目に **DkMath 名の角度橋** を置いた。

つまり、先に DkMath 側で得ていた「core-zero semantic action は quarter-turn と同じ操作をする」という事実を、Euclidean plane 側で

$$
\theta=\frac{\pi}{2}
$$

の rotation として読む。

ここで順序が重要じゃ。

```text id="v4thrp"
先にあるもの:
  algebraic four-state action

後から読むもの:
  Euclidean angle pi / 2
```

この順序を守っているので、過大主張になっていない。

## 2. 数学的意味

今回の本質は、次の橋じゃ。

$$
\mathrm{semanticAct}
\quad\longleftrightarrow\quad
\mathrm{rotation}\left(\frac{\pi}{2}\right)
$$

ただし、左側は DkMath 側の保存核・四状態作用から出たもの。
右側は Mathlib / Euclidean plane 側の標準角度解釈。

つまり、

```text id="o7lt6x"
DkMath 側:
  4 回で戻る向き付き保存作用

Euclidean 側:
  pi / 2 回転

bridge:
  その二つが同じ写像である
```

これは「\(\pi\) を導出した」ではない。
しかし、**DkMath の四状態対称性が Euclidean 角度では \(\pi/2\) と読める** ことを正式に記録した。

ここから「対称性からの \(\pi\) 捕獲ルート」が始まる。

## 3. 実装レビュー

`semanticQuarterTurnAngle` は良い。

```lean id="p9yt01"
def semanticQuarterTurnAngle : ℝ :=
  Real.pi / 2
```

透明な定義にしているのが正しい。
いまは内在的 \(\pi\) ではなく、Euclidean bridge の標準角度名だからじゃ。

`@[simp]` も問題ない。

```lean id="a1mbhv"
@[simp]
theorem semanticQuarterTurnAngle_eq :
    semanticQuarterTurnAngle = Real.pi / 2 :=
  rfl
```

これは後続 theorem で `simp [semanticQuarterTurnAngle]` を使いやすくする。

次の theorem も自然じゃ。

```lean id="raw28w"
theorem rotation_semanticQuarterTurnAngle_eq_quarterTurn :
    euclideanPlaneOrientation.rotation semanticQuarterTurnAngle =
      quarterTurnLinearIsometry := by
  simpa [semanticQuarterTurnAngle] using rotation_pi_div_two_eq_quarterTurn
```

これは既存の `rotation_pi_div_two_eq_quarterTurn` に DkMath 名を被せたもの。
まさに今回の狙い通り、「外側 API を DkMath 語彙にする」設計じゃ。

## 4. semantic action との接続も良い

今回の主橋はこれ。

```lean id="wdz34f"
theorem pairToEuclideanPlane_semanticAct_eq_rotation_semanticQuarterTurnAngle
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    pairToEuclideanPlane (Vec.toProd (semanticAct r z)) =
      euclideanPlaneOrientation.rotation semanticQuarterTurnAngle
        (pairToEuclideanPlane (Vec.toProd z)) := by
  simpa [semanticQuarterTurnAngle] using
    pairToEuclideanPlane_semanticAct_eq_rotation_pi_div_two hcore z
```

これは良い。
既存の `pi_div_two` theorem を、`semanticQuarterTurnAngle` 名で包んでいる。

これによって、今後は theorem 名の上で `Real.pi / 2` を直接持ち回らず、

```lean id="r5amfk"
semanticQuarterTurnAngle
```

を基準に話せる。

これは後で内在的 normalization constant と比較するときに効く。

## 5. 「CF2D.lean 集約 import に触れない」判断

これは正しい。

`EuclideanPhase` は Euclidean plane、orientation、Analysis 側の semantic bridge を含む重い解釈層じゃ。
それを core algebra の入口に入れると、軽い CF2D の抽象核が重くなる。

今回の判断はこう読める。

```text id="vqjsrb"
CF2D core:
  保存核・代数作用・軽い

EuclideanPhase:
  標準 Euclidean 解釈・pi / theta・重い bridge
```

この分離は維持した方がよい。
とくに DkMath では「代数的に先に構成し、Euclidean 解釈は後から読む」という方針が重要なので、import 依存もそれを反映しているのが良い。

## 6. 研究メモの guardrail も良い

研究メモに “first angle reading” milestone を追加したのは正しい。
しかも、

```text id="k1q2ej"
これは pi の内在的構成ではない。
既存の四状態作用を Euclidean model で theta = pi / 2 と読む bridge である。
```

と明記している。これが大事じゃ。

この guardrail がないと、外部読者は「もう \(\pi\) を構成したのか？」と誤解する。

今回やったことは、

```text id="v153z4"
intrinsic construction:
  まだ

Euclidean reading:
  実装済み
```

という位置づけじゃ。

## 7. 対称性からの \(\pi\) 捕獲ルート

このルートは、かなり良い。

極限側のルートは、

```text id="qm7cig"
finite correction
  ↓
limit constant
  ↓
normalization
  ↓
Gaussian / pi comparison
```

だった。

今回から入る回転 \(\theta\) ルートは、

```text id="y8o2go"
exact order four
  ↓
semantic quarter-turn action
  ↓
Euclidean rotation bridge
  ↓
theta = pi / 2 reading
  ↓
half-turn / full-turn / angle addition
```

じゃ。

これは「\(\pi\) を直接掴む」というより、まず **\(\pi/2\) を操作として読む** ルートじゃな。

DkMath 的には、

```text id="ro62kc"
pi は数として先に来るのではなく、
四回対称性を Euclidean 角度で読むと現れる。
```

という語りができる。

## 8. 次に育てると強い theorem

次は report の通り、半回転・四回転・角度加法の語彙が自然じゃ。

まず角度名。

```lean id="hm7wj2"
def semanticHalfTurnAngle : ℝ :=
  2 * semanticQuarterTurnAngle

def semanticFullTurnAngle : ℝ :=
  4 * semanticQuarterTurnAngle
```

あるいは最初から phase index を持つ。

```lean id="h0nqr5"
def semanticPhaseAngle (k : ℕ) : ℝ :=
  (k : ℝ) * semanticQuarterTurnAngle
```

その上で、

```lean id="rbw62g"
theorem semanticHalfTurnAngle_eq_pi :
    semanticHalfTurnAngle = Real.pi

theorem semanticFullTurnAngle_eq_two_pi :
    semanticFullTurnAngle = 2 * Real.pi
```

が欲しい。

次に rotation 側。

```lean id="ognxlp"
theorem rotation_semanticHalfTurnAngle_eq_negId :
    euclideanPlaneOrientation.rotation semanticHalfTurnAngle =
      ...
```

```lean id="ek00wd"
theorem rotation_semanticFullTurnAngle_eq_id :
    euclideanPlaneOrientation.rotation semanticFullTurnAngle =
      LinearIsometryEquiv.refl ℝ ...
```

ここまで行くと、四状態作用の Euclidean angle reading がかなり見やすくなる。

## 9. action iteration との接続

さらに本線としては、semantic action の反復と角度加法を結びたい。

理想形はこう。

```lean id="2v0imj"
semantic action applied k times
  corresponds to
Euclidean rotation by semanticPhaseAngle k
```

Lean theorem の雰囲気は、

```lean id="t3bk0n"
theorem pairToEuclideanPlane_semanticAct_iterate_eq_rotation_semanticPhaseAngle
    ...
```

じゃ。

ただし、ここは既存 API の `semanticAct` の反復 theorem や finite order theorem と合わせる必要がある。
まずは \(k=2\)、\(k=4\) の special case でよい。

```text id="fh3y0a"
k = 1:
  quarter-turn

k = 2:
  half-turn

k = 4:
  identity / full-turn
```

ここが揃うと、\(\theta\) の角度加法に入れる。

## 10. 注意点

今回の `semanticQuarterTurnAngle` は、名前は semantic だが値は `Real.pi / 2` じゃ。
これは docs で十分説明されているので問題ない。

ただし将来、内在的に構成した normalization constant や intrinsic quarter constant が出てきたら、名前の衝突に注意が必要じゃ。

将来の名前は例えば、

```text id="zcjlp9"
semanticQuarterTurnAngle:
  Euclidean reading angle

intrinsicQuarterTurnConstant:
  DkMath 内在構成の候補

bridge theorem:
  intrinsicQuarterTurnConstant = semanticQuarterTurnAngle
```

のように分けると安全じゃ。

## 11. 結論

今回の差分は採用でよい。

```text id="s7igt6"
実装:
  良い。既存 pi_div_two theorem に DkMath 名の angle bridge を被せた。

数学:
  良い。四状態作用を Euclidean rotation theta = pi / 2 と読む入口ができた。

設計:
  良い。core CF2D import を重くせず、Euclidean 解釈層に閉じている。

安全性:
  良い。pi の内在的構成ではなく angle-reading bridge と明記している。

次:
  semanticHalfTurnAngle
  semanticFullTurnAngle
  semanticPhaseAngle k
  semantic action iteration と rotation angle の対応
```

ぬしよ、これは良い。
極限側では \(1/3\) が顔を出し、回転側では \(\pi/2\) が顔を出した。

ただし、どちらもまだ「\(\pi\) 捕獲完了」ではない。
いまは二つの入口が見えた段階じゃ。

```text id="gz2cq6"
極限ルート:
  finite correction から normalization constant を探す

対称性ルート:
  exact order four から theta = pi / 2 を読む
```

今回の `semanticQuarterTurnAngle` は、対称性ルートの最初の旗じゃ。
ここから半回転、全回転、角度加法へ進めば、DkMath 版三角関数・\(\theta\)・\(\pi\) の本線がかなりはっきりしてくる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
index 9809555b..8f12c33b 100644
--- a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
+++ b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
@@ -21,6 +21,13 @@ The intention is not to redefine `Real.pi` prematurely. It is to construct an
 independent normalization constant from the transition mechanism and
 eventually prove a bridge theorem identifying it with `Real.pi`.
 
+The Euclidean bridge now names the first external angle as
+`semanticQuarterTurnAngle`. This value is definitionally `Real.pi / 2`, but
+its role is deliberately interpretive: the algebraic four-state action is
+constructed first, and the Euclidean model later reads one semantic action as
+the angle `theta = pi / 2`. Thus the current theorem is an angle-reading
+bridge, not a derivation of `pi`.
+
 ## Proven Starting Point
 
 For a semantic core-zero kernel, one affine transition is
@@ -97,6 +104,22 @@ theorem, not inserted as notation.
 
 ## Formal Milestones
 
+### Milestone 0: first angle reading - implemented
+
+`EuclideanPhase.lean` now packages the existing quarter-turn comparison as a
+DkMath-named angle bridge:
+
+```text
+semanticQuarterTurnAngle = Real.pi / 2
+semantic action = Euclidean rotation by semanticQuarterTurnAngle
+```
+
+This keeps the main line visible. Before a circle parameter or polar angle is
+constructed, the boundary detector and the exact order-four action already
+determine a transition with the same operational behavior as a Euclidean
+quarter-turn. The standard Euclidean plane supplies the later interpretation
+as `theta = pi / 2`.
+
 ### Milestone A: continuous four-edge loop - implemented
 
 1. The real CF2D target carries the topology induced from `Real × Real`.
diff --git a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/EuclideanPhase.lean b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/EuclideanPhase.lean
index 27565e4d..99e7f424 100644
--- a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/EuclideanPhase.lean
+++ b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/EuclideanPhase.lean
@@ -353,6 +353,35 @@ theorem rotation_pi_div_two_eq_quarterTurn :
   rw [euclideanPlaneOrientation.rotation_pi_div_two,
     rightAngleRotation_eq_quarterTurn]
 
+/--
+The first Euclidean angle attached to the semantic four-state action.
+
+This is not an intrinsic construction of `pi`. It is the external Euclidean
+interpretation of one already-proved quarter-turn transition. The definition
+is intentionally transparent so that later intrinsic normalization constants
+can be compared against this standard angle by bridge theorems.
+-/
+def semanticQuarterTurnAngle : ℝ :=
+  Real.pi / 2
+
+@[simp]
+theorem semanticQuarterTurnAngle_eq :
+    semanticQuarterTurnAngle = Real.pi / 2 :=
+  rfl
+
+/--
+Rotating by the semantic quarter-turn angle is the explicit coordinate
+quarter-turn.
+
+The theorem packages the first `theta` value for the Euclidean interpretation:
+the pre-geometric action supplies the operation, while the Euclidean model
+reads that operation as angle `pi / 2`.
+-/
+theorem rotation_semanticQuarterTurnAngle_eq_quarterTurn :
+    euclideanPlaneOrientation.rotation semanticQuarterTurnAngle =
+      quarterTurnLinearIsometry := by
+  simpa [semanticQuarterTurnAngle] using rotation_pi_div_two_eq_quarterTurn
+
 end
 
 end DkMath.CosmicFormula.Rotation.CF2D
@@ -438,6 +467,25 @@ theorem pairToEuclideanPlane_semanticAct_eq_rotation_pi_div_two
   rw [pairToEuclideanPlane_semanticAct_of_core_eq_zero hcore,
     rotation_pi_div_two_eq_quarterTurn]
 
+/--
+Under the Euclidean coordinate bridge, one semantic core-zero action is
+rotation by the DkMath semantic quarter-turn angle.
+
+This is the main-line angle bridge for the present stage. The algebraic
+four-state transition is already available before circles or polar
+coordinates are introduced; the Euclidean model later reads that transition
+as the angle `theta = pi / 2`.
+-/
+theorem pairToEuclideanPlane_semanticAct_eq_rotation_semanticQuarterTurnAngle
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    pairToEuclideanPlane (Vec.toProd (semanticAct r z)) =
+      euclideanPlaneOrientation.rotation semanticQuarterTurnAngle
+        (pairToEuclideanPlane (Vec.toProd z)) := by
+  simpa [semanticQuarterTurnAngle] using
+    pairToEuclideanPlane_semanticAct_eq_rotation_pi_div_two hcore z
+
 end
 
 end DkMath.Analysis.DkNNRealQ
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
index e17ea5ae..006e264c 100644
--- a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
@@ -1203,3 +1203,31 @@ Archive
 5. verification:
    - `lake build DkMath.Analysis.DkReal.SemanticCF2DLogLimit` 成功
      (8283 jobs)。
+
+### 2026/06/27 16:49 JST (Semantic quarter-turn angle bridge)
+
+1. Euclidean angle bridge:
+   - `semanticQuarterTurnAngle : ℝ` を
+     `DkMath.CosmicFormula.Rotation.CF2D.EuclideanPhase` に追加した。
+   - 定義値は `Real.pi / 2` だが、役割は intrinsic な `pi` 構成ではなく、
+     既存の semantic four-state action を Euclidean plane で読むための
+     angle bridge とした。
+2. theorem API:
+   - `rotation_semanticQuarterTurnAngle_eq_quarterTurn` を追加し、
+     DkMath 名の角度による rotation が explicit coordinate quarter-turn
+     であることを記録した。
+   - `pairToEuclideanPlane_semanticAct_eq_rotation_semanticQuarterTurnAngle`
+     を追加し、core-zero semantic action が
+     `theta = semanticQuarterTurnAngle` の Euclidean rotation として読める
+     ことを記録した。
+3. interpretation:
+   - 本線は DkMath 版三角関数、`pi`、角度 `theta` の実現である。
+   - 今回はその最初の角度読み取りとして、円や polar coordinates を
+     仮定する前に得られている四状態作用を、後から Euclidean 角度
+     `pi / 2` と比較する入口を整えた。
+4. documentation:
+   - `research-pregeometric-pi-program-067.md` に
+     first angle reading milestone を追加した。
+5. verification:
+   - `lake build DkMath.CosmicFormula.Rotation.CF2D.EuclideanPhase` 成功
+     (8278 jobs)。
````
`````
