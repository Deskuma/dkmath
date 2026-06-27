# Git diff / Report / Review

## Upd: EuclideanPhase

gch: 3e45cedb71ddf25b20c882594de2db642573da47

## Report

進めました。今回はレビュー提案どおり、対称性ルートの角度語彙を `π/2` から半回転・全回転まで拡張しました。

主な追加:

- [EuclideanPhase.lean](/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/EuclideanPhase.lean)
  - `semanticPhaseAngle k := k * semanticQuarterTurnAngle`
  - `semanticHalfTurnAngle`
  - `semanticFullTurnAngle`
  - `semanticHalfTurnAngle_eq_pi`
  - `semanticFullTurnAngle_eq_two_pi`
  - `rotation_semanticHalfTurnAngle_eq_neg`
  - `rotation_semanticFullTurnAngle_eq_refl`

文書側も更新済み:

- [research-pregeometric-pi-program-067.md](/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md)
- [History.md](/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md)

検証:

- `lake build DkMath.CosmicFormula.Rotation.CF2D.EuclideanPhase` 成功
- `lake build DkMath.Analysis` 成功
- `git diff --check` 成功

次の自然な一手は、既存の semantic action の反復定理を拾って、`k = 2` と `k = 4` の作用側をこの `semanticPhaseAngle` と接続することです。

## Review

うむ、賢狼レビューじゃ。
今回の差分は **採用でよい** 。前回の `semanticQuarterTurnAngle` から、半回転・全回転まで角度語彙を伸ばしたことで、対称性ルートの \(\theta\) 側 API がかなり見通しよくなった。

今回できたことは、こうじゃ。

```text id="wur4sd"
semanticQuarterTurnAngle:
  π / 2

semanticHalfTurnAngle:
  π

semanticFullTurnAngle:
  2π

semanticPhaseAngle k:
  k 個の semantic quarter-turn を Euclidean 角度として読む語彙
```

## 1. 状況解説

前回は、四状態作用の一歩を Euclidean model で読むために、

```lean id="kvc1yi"
semanticQuarterTurnAngle : ℝ := Real.pi / 2
```

を置いた。

今回はそれを、

```lean id="dkdpbn"
def semanticPhaseAngle (k : ℕ) : ℝ :=
  (k : ℝ) * semanticQuarterTurnAngle
```

として一般化し、さらに special name として、

```lean id="zdoina"
semanticHalfTurnAngle
semanticFullTurnAngle
```

を置いた。

これは良い。
今後の本線である、

```text id="fff2mi"
k semantic actions
  corresponds to
Euclidean rotation by semanticPhaseAngle k
```

へ進むための角度側の足場ができた。

## 2. 数学的意味

今回の意味は、\(\pi\) を内在的に作ったことではない。
しかし、四状態対称性を Euclidean 角度で読むと、自然に次の列が見えるようになった。

$$
\theta_0=0
$$

$$
\theta_1=\frac{\pi}{2}
$$

$$
\theta_2=\pi
$$

$$
\theta_4=2\pi
$$

ここで \(\theta_k\) が `semanticPhaseAngle k` じゃ。

つまり、DkMath 側の「四回で戻る作用」は、Euclidean 側では \(2\pi\) 周期の回転として読める。

```text id="v23qpq"
DkMath 側:
  exact order four

Euclidean 側:
  full turn angle 2π

bridge:
  four semantic quarter-turns = identity rotation
```

この橋は、対称性から \(\pi\) を捕まえるルートの入口としてかなり良い。

## 3. 実装レビュー

`semanticPhaseAngle` の定義は素直で良い。

```lean id="l0i7l3"
def semanticPhaseAngle (k : ℕ) : ℝ :=
  (k : ℝ) * semanticQuarterTurnAngle
```

最初は \(k : \mathbb{N}\) で十分じゃ。
semantic action の反復は自然数回なので、まず Nat で攻めるのが Lean 的にも安全。

ただし将来、逆回転や負方向 phase を扱うなら、後で

```lean id="wx27sk"
semanticIntPhaseAngle (k : ℤ)
```

のような整数版が欲しくなるかもしれぬ。
今は不要じゃ。

## 4. half / full の定理も良い

これはよい。

```lean id="qp8l14"
@[simp]
theorem semanticHalfTurnAngle_eq_pi :
    semanticHalfTurnAngle = Real.pi
```

```lean id="fr3nzw"
@[simp]
theorem semanticFullTurnAngle_eq_two_pi :
    semanticFullTurnAngle = 2 * Real.pi
```

DkMath 名の角度が、Euclidean 標準角度として何に読まれるかを明示している。

ここは今後の文書でも効く。

```text id="pib9cw"
one semantic phase:
  pi / 2

two semantic phases:
  pi

four semantic phases:
  2pi
```

## 5. rotation bridge も良い

半回転が negation になる theorem は自然じゃ。

```lean id="ot579o"
theorem rotation_semanticHalfTurnAngle_eq_neg :
    euclideanPlaneOrientation.rotation semanticHalfTurnAngle =
      LinearIsometryEquiv.neg ℝ
```

全回転が identity になる theorem も良い。

```lean id="y3x4ms"
theorem rotation_semanticFullTurnAngle_eq_refl :
    euclideanPlaneOrientation.rotation semanticFullTurnAngle =
      LinearIsometryEquiv.refl ℝ EuclideanPlane
```

これにより、角度語彙側で、

```text id="a1xiyi"
quarter-turn:
  coordinate quarter-turn

half-turn:
  negation

full-turn:
  identity
```

が揃った。

これは次の semantic action iteration bridge に直接つながる。

## 6. `@[simp]` について

`semanticHalfTurnAngle_eq_pi` と `semanticFullTurnAngle_eq_two_pi` を `@[simp]` にしたのは、今の段階では問題ない。
証明では標準角度に戻したい場面が多いはずだからじゃ。

ただし、将来「semantic 名を式中に残して読みたい」場面が増えたら、`simp` が展開しすぎる可能性はある。
今は小さな bridge file なので、このままでよい。

## 7. 文書更新も良い

研究メモで、

```text id="ua32qk"
semanticQuarterTurnAngle = Real.pi / 2
semanticHalfTurnAngle    = Real.pi
semanticFullTurnAngle    = 2 * Real.pi
```

を明記したのは良い。

また、

```text id="r7td39"
k semantic actions <-> Euclidean rotation by semanticPhaseAngle k
```

を次の bridge として掲げているのも良い。
これで読者に「角度名だけ増やした」のではなく、「作用反復との接続へ向かうための準備」だと伝わる。

## 8. 研究上の位置づけ

これで対称性ルートは、かなり本線に入った。

```text id="kzqtb1"
exact order four
  ↓
quarter-turn action
  ↓
semanticQuarterTurnAngle = π / 2
  ↓
semanticPhaseAngle k
  ↓
half-turn = π
  ↓
full-turn = 2π
```

これは、\(\pi\) を数式の外から押し込んでいる段階ではある。
しかし重要なのは、DkMath 側にすでに存在していた四状態作用が、Euclidean model ではこれらの角度として読めることを API 化している点じゃ。

つまり、今はまだ、

```text id="rvwxqu"
intrinsic pi construction:
  未達

Euclidean angle reading:
  成功
```

の段階。

この guardrail は守れている。

## 9. 次の一手

次は report の通り、semantic action の反復側と接続するのが自然じゃ。

まずは \(k=2\) と \(k=4\) の special case が良い。

```lean id="djg5s7"
theorem pairToEuclideanPlane_semanticAct_twice_eq_rotation_semanticHalfTurnAngle
    ...
```

```lean id="vvl5di"
theorem pairToEuclideanPlane_semanticAct_four_eq_rotation_semanticFullTurnAngle
    ...
```

ただし、`semanticAct` の反復 theorem が既にあるなら、それを拾って薄く bridge するのが良い。
直接計算で殴るより、既存の finite-order API を使う方が設計として綺麗じゃ。

その後に一般形。

```lean id="gxz0hg"
theorem pairToEuclideanPlane_semanticAct_iterate_eq_rotation_semanticPhaseAngle
    (k : ℕ) :
    ...
```

ただし一般形は、rotation 側の角度加法 theorem と、semantic action 側の反復合成 theorem の両方が必要になるので、まず \(2\) と \(4\) がよい。

## 10. さらに欲しい補題

角度語彙側では、次の simp theorem があると便利そうじゃ。

```lean id="ovh3zs"
theorem semanticPhaseAngle_two :
    semanticPhaseAngle 2 = semanticHalfTurnAngle := rfl
```

```lean id="i95lpl"
theorem semanticPhaseAngle_four :
    semanticPhaseAngle 4 = semanticFullTurnAngle := rfl
```

また、加法語彙として、

```lean id="qq4r69"
theorem semanticPhaseAngle_add (m n : ℕ) :
    semanticPhaseAngle (m + n) =
      semanticPhaseAngle m + semanticPhaseAngle n
```

これは角度加法ルートに効く。
証明は `semanticPhaseAngle` を展開して `ring` で閉じるはずじゃ。

その次に、

```lean id="zbda2e"
theorem rotation_semanticPhaseAngle_add ...
```

へ進める。

## 11. 気になる点

大きな問題はない。

一点だけ、`semanticFullTurnAngle_eq_two_pi` の右辺を `2 * Real.pi` にしているのは良いが、Mathlib の rotation theorem 側が `Real.two_pi` のような形を好む場合がある。
今の build は通っているので問題ない。将来 theorem 探索で詰まるなら、`2 * Real.pi` と既存 `Real.two_pi` 系の補助 simp を用意すればよい。

## 12. 結論

今回の差分は採用でよい。

```text id="f06put"
実装:
  良い。quarter-turn から half/full turn へ角度語彙が拡張された。

数学:
  良い。四状態対称性を Euclidean 角度列として読めるようになった。

設計:
  良い。semanticPhaseAngle k が次の反復作用 bridge の基準になる。

安全性:
  良い。pi の内在的構成ではなく Euclidean reading として扱っている。

次:
  semantic action の 2 回反復と 4 回反復を、
  semanticHalfTurnAngle / semanticFullTurnAngle の rotation と接続する。
```

ぬしよ、これは良い進みじゃ。
いま対称性ルートでは、\(\pi/2\)、\(\pi\)、\(2\pi\) の語彙が揃った。

次に semantic action の反復とつなげれば、

```text id="eegmwj"
作用の回数
  ↔
角度の加法
```

が Lean 上で見え始める。
そこからが、DkMath 版 \(\theta\) の本線じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
index 8f12c33b..2b7492fe 100644
--- a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
+++ b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
@@ -111,6 +111,8 @@ DkMath-named angle bridge:
 
 ```text
 semanticQuarterTurnAngle = Real.pi / 2
+semanticHalfTurnAngle    = Real.pi
+semanticFullTurnAngle    = 2 * Real.pi
 semantic action = Euclidean rotation by semanticQuarterTurnAngle
 ```
 
@@ -120,6 +122,17 @@ determine a transition with the same operational behavior as a Euclidean
 quarter-turn. The standard Euclidean plane supplies the later interpretation
 as `theta = pi / 2`.
 
+The same module also introduces `semanticPhaseAngle k = k * theta`. At the
+current stage this is only Euclidean angle vocabulary, but it is deliberately
+shaped for the next bridge:
+
+```text
+k semantic actions  <->  Euclidean rotation by semanticPhaseAngle k
+```
+
+The implemented special cases already read two quarter-turns as negation and
+four quarter-turns as the identity rotation.
+
 ### Milestone A: continuous four-edge loop - implemented
 
 1. The real CF2D target carries the topology induced from `Real × Real`.
diff --git a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/EuclideanPhase.lean b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/EuclideanPhase.lean
index 99e7f424..715a0971 100644
--- a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/EuclideanPhase.lean
+++ b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/EuclideanPhase.lean
@@ -369,6 +369,47 @@ theorem semanticQuarterTurnAngle_eq :
     semanticQuarterTurnAngle = Real.pi / 2 :=
   rfl
 
+/--
+The Euclidean angle read from `k` semantic quarter-turn phases.
+
+This is the additive angle vocabulary for the symmetry route. It does not
+assert that the intrinsic DkMath normalization constant has already been
+constructed; it only records how the standard Euclidean model reads repeated
+quarter-turn actions.
+-/
+def semanticPhaseAngle (k : ℕ) : ℝ :=
+  (k : ℝ) * semanticQuarterTurnAngle
+
+/-- The angle read from two semantic quarter-turns. -/
+def semanticHalfTurnAngle : ℝ :=
+  semanticPhaseAngle 2
+
+/-- The angle read from four semantic quarter-turns. -/
+def semanticFullTurnAngle : ℝ :=
+  semanticPhaseAngle 4
+
+@[simp]
+theorem semanticPhaseAngle_zero :
+    semanticPhaseAngle 0 = 0 := by
+  simp [semanticPhaseAngle]
+
+@[simp]
+theorem semanticPhaseAngle_one :
+    semanticPhaseAngle 1 = semanticQuarterTurnAngle := by
+  simp [semanticPhaseAngle]
+
+@[simp]
+theorem semanticHalfTurnAngle_eq_pi :
+    semanticHalfTurnAngle = Real.pi := by
+  simp [semanticHalfTurnAngle, semanticPhaseAngle, semanticQuarterTurnAngle]
+  ring_nf
+
+@[simp]
+theorem semanticFullTurnAngle_eq_two_pi :
+    semanticFullTurnAngle = 2 * Real.pi := by
+  simp [semanticFullTurnAngle, semanticPhaseAngle, semanticQuarterTurnAngle]
+  ring
+
 /--
 Rotating by the semantic quarter-turn angle is the explicit coordinate
 quarter-turn.
@@ -380,7 +421,30 @@ reads that operation as angle `pi / 2`.
 theorem rotation_semanticQuarterTurnAngle_eq_quarterTurn :
     euclideanPlaneOrientation.rotation semanticQuarterTurnAngle =
       quarterTurnLinearIsometry := by
-  simpa [semanticQuarterTurnAngle] using rotation_pi_div_two_eq_quarterTurn
+  simp [semanticQuarterTurnAngle, rotation_pi_div_two_eq_quarterTurn]
+
+/--
+Rotating by the semantic half-turn angle is negation on the Euclidean plane.
+
+This is the `theta = pi` reading of two semantic quarter-turns.
+-/
+theorem rotation_semanticHalfTurnAngle_eq_neg :
+    euclideanPlaneOrientation.rotation semanticHalfTurnAngle =
+      LinearIsometryEquiv.neg ℝ := by
+  simp [semanticHalfTurnAngle_eq_pi]
+
+/--
+Rotating by the semantic full-turn angle is the identity on the Euclidean
+plane.
+
+This is the `theta = 2 * pi` reading of four semantic quarter-turns. It is the
+Euclidean angle counterpart of exact order four.
+-/
+theorem rotation_semanticFullTurnAngle_eq_refl :
+    euclideanPlaneOrientation.rotation semanticFullTurnAngle =
+      LinearIsometryEquiv.refl ℝ EuclideanPlane := by
+  ext v
+  simp [semanticFullTurnAngle_eq_two_pi]
 
 end
 
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
index 006e264c..9bef77f2 100644
--- a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
@@ -1231,3 +1231,28 @@ Archive
 5. verification:
    - `lake build DkMath.CosmicFormula.Rotation.CF2D.EuclideanPhase` 成功
      (8278 jobs)。
+
+### 2026/06/27 17:06 JST (Half-turn and full-turn angle readings)
+
+1. angle vocabulary:
+   - `semanticPhaseAngle (k : ℕ) : ℝ` を追加し、
+     `k * semanticQuarterTurnAngle` を DkMath 名で表した。
+   - `semanticHalfTurnAngle` と `semanticFullTurnAngle` を追加した。
+2. exact angle values:
+   - `semanticHalfTurnAngle_eq_pi` により二つの semantic quarter-turn が
+     `Real.pi` として読まれることを記録した。
+   - `semanticFullTurnAngle_eq_two_pi` により四つの semantic quarter-turn が
+     `2 * Real.pi` として読まれることを記録した。
+3. rotation bridge:
+   - `rotation_semanticHalfTurnAngle_eq_neg` を追加し、半回転が Euclidean
+     plane の negation であることを記録した。
+   - `rotation_semanticFullTurnAngle_eq_refl` を追加し、全回転が identity
+     rotation であることを記録した。
+4. interpretation:
+   - 対称性ルートの本線として、
+     `k semantic actions <-> rotation by semanticPhaseAngle k`
+     へ進むための角度側 API を先に整えた。
+   - まだ反復 semantic action との一般 theorem は未実装。
+5. documentation:
+   - `research-pregeometric-pi-program-067.md` の first angle reading
+     milestone を half/full turn まで拡張した。
````
`````
