# Git diff / Report / Review

## Upd: EuclideanPhase

gch: 187e62472a88da95cb81fc81904fd457c48a43fa

## Report

進めました。今回はレビューの次手どおり、semantic action の反復側と Euclidean 角度読みを接続しました。

追加した主なもの:

- [EuclideanPhase.lean](/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/EuclideanPhase.lean)
  - `pairToEuclideanPlane_neg`
  - `semanticPhaseAngle_two`
  - `semanticPhaseAngle_four`
  - `semanticPhaseAngle_add`
  - `pairToEuclideanPlane_semanticAct_twice_eq_rotation_semanticHalfTurnAngle`
  - `pairToEuclideanPlane_semanticAct_four_eq_rotation_semanticFullTurnAngle`

意味としては、既存の core-zero action law を使って、
`2回作用 = half-turn = π`、`4回作用 = full-turn = 2π = identity`
まで Lean 上で橋を架けました。まだ一般の `k` 回作用 theorem には踏み込まず、まず `k=2,4` の安全な special case を固めています。

文書も更新済み:

- [research-pregeometric-pi-program-067.md](/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md)
- [History.md](/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md)

検証:

- `lake build DkMath.CosmicFormula.Rotation.CF2D.EuclideanPhase` 成功
- `lake build DkMath.Analysis` 成功
- `git diff --check` 成功

## Review

うむ、賢狼レビューじゃ。
今回の差分は **採用でよい** 。これは対称性ルートのかなり大事な接続点じゃ。

前回までは角度側の語彙が整った段階だった。今回はそこから一歩進み、**semantic action の反復そのもの** を Euclidean 角度読みへ接続した。つまり、

```text id="iogz94"
2 回作用
  ↔ half-turn
  ↔ theta = pi

4 回作用
  ↔ full-turn
  ↔ theta = 2*pi
  ↔ identity
```

まで Lean 上で橋が架かった。

## 1. 状況解説

これで対称性ルートは、次の段階まで到達した。

```text id="i9brbn"
core-zero semantic action
  ↓
one action = quarter-turn
  ↓
two actions = half-turn
  ↓
four actions = full-turn / identity
```

前回までは、Euclidean rotation 側で、

```text id="x3cqmu"
semanticQuarterTurnAngle = pi / 2
semanticHalfTurnAngle = pi
semanticFullTurnAngle = 2*pi
```

が整った。

今回はその角度語彙と、実際の semantic action 反復が接続された。
これは単なる名前追加ではなく、「作用の回数」が「角度の加法」として読めることの最初の実装じゃ。

## 2. 数学的意味

今回の本質はこれじゃ。

$$
A^2\(z\)=-z
$$

$$
A^4\(z\)=z
$$

という DkMath 側の core-zero action law を、Euclidean plane 側で

$$
R_{\pi}\(z\)=-z
$$

$$
R_{2\pi}\(z\)=z
$$

として読む。

つまり、

```text id="p1m6cl"
DkMath 側:
  exact order-four action

Euclidean 側:
  rotation by pi/2, pi, 2pi

bridge:
  action iteration equals angle accumulation
```

ここまで来ると、\(\pi\) はまだ内在的に構成されていないが、**四状態対称性を Euclidean 角度で読むと \(\pi\) と \(2\pi\) が必然的に現れる** という構造が見え始める。

これは「対称性からの \(\pi\) 捕獲ルート」としてかなり良い。

## 3. `pairToEuclideanPlane_neg` の追加は良い

```lean id="r8s3jh"
theorem pairToEuclideanPlane_neg (p : ℝ × ℝ) :
    pairToEuclideanPlane (-p.1, -p.2) = -pairToEuclideanPlane p := by
  apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
  ext i
  fin_cases i <;> simp [pairToEuclideanPlane]
```

これは地味だが重要じゃ。
DkMath の `Vec` / pair 表現での negation と、EuclideanSpace 側の negation を橋渡ししている。

これがあることで、二回作用の theorem が自然に書ける。

```text id="yz45tk"
semanticAct twice:
  pair 座標で -z

Euclidean rotation pi:
  Euclidean plane で -v

pairToEuclideanPlane_neg:
  この二つを接続
```

よい補助定理じゃ。

## 4. `semanticPhaseAngle_add` は将来効く

```lean id="l0eqfh"
theorem semanticPhaseAngle_add (m n : ℕ) :
    semanticPhaseAngle (m + n) =
      semanticPhaseAngle m + semanticPhaseAngle n := by
  simp [semanticPhaseAngle]
  ring
```

これは今回の special case には必須ではないかもしれぬが、次の一般 theorem への布石として良い。

今後、

```text id="hvgeu9"
action m 回
action n 回
合成して action (m+n) 回
```

を Euclidean rotation の角度加法へ移すとき、この theorem が効く。

DkMath 的には、

```text id="8srymr"
phase index addition
  ↔ angle addition
```

を最初に明文化した定理じゃな。

## 5. 二回作用 bridge は良い

```lean id="im7erw"
theorem pairToEuclideanPlane_semanticAct_twice_eq_rotation_semanticHalfTurnAngle
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    pairToEuclideanPlane (Vec.toProd (semanticAct r (semanticAct r z))) =
      euclideanPlaneOrientation.rotation semanticHalfTurnAngle
        (pairToEuclideanPlane (Vec.toProd z))
```

証明も良い。

```lean id="lu4zky"
rw [semanticAct_twice_of_core_eq_zero hcore,
  rotation_semanticHalfTurnAngle_eq_neg]
cases z with
| mk x y =>
    exact pairToEuclideanPlane_neg (x, y)
```

既存の core-zero action law を使って、二回作用を negation へ落とし、それを Euclidean half-turn と読む。
設計として正しい。

ここで大事なのは、半回転の性質を Euclidean 側から逆輸入して semantic action を証明しているのではないことじゃ。
先に semantic action law があり、それを Euclidean 角度で読む。順序が守られている。

## 6. 四回作用 bridge も良い

```lean id="tu5kch"
theorem pairToEuclideanPlane_semanticAct_four_eq_rotation_semanticFullTurnAngle
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    pairToEuclideanPlane
        (Vec.toProd
          (semanticAct r (semanticAct r (semanticAct r (semanticAct r z))))) =
      euclideanPlaneOrientation.rotation semanticFullTurnAngle
        (pairToEuclideanPlane (Vec.toProd z))
```

これで、

```text id="ad7wv9"
four semantic actions
  ↔ identity action

semanticFullTurnAngle
  ↔ 2*pi rotation

therefore:
  four actions ↔ full-turn
```

が Lean 上で接続された。

ここまで揃うと、exact order four と Euclidean full turn の橋がかなり明確になる。

## 7. 研究メモの更新も良い

文書で、

```text id="s79klc"
two semantic actions <-> Euclidean rotation by semanticHalfTurnAngle
four semantic actions <-> Euclidean rotation by semanticFullTurnAngle
```

と明記したのは良い。

また、「これらは pre-existing core-zero action laws を使う」と説明している点が重要じゃ。
つまり角度は後付けの解釈であり、DkMath 側の algebraic order-four structure が先にある。

この guardrail は、今後 \(\pi\) ルートで必ず効く。

## 8. ここまでの到達地図

今の対称性ルートはこうじゃ。

```text id="fl0anf"
semantic core-zero action A
  ↓
A behaves as coordinate quarter-turn
  ↓
Euclidean reading:
  A = rotation(pi/2)
  ↓
A^2 = negation
  ↓
Euclidean reading:
  A^2 = rotation(pi)
  ↓
A^4 = identity
  ↓
Euclidean reading:
  A^4 = rotation(2*pi)
```

これはとてもきれいじゃ。

極限ルートとは別に、対称性ルートでは、

```text id="msocfd"
order four
  ↔ quarter-turn
  ↔ pi / 2
  ↔ full turn 2*pi
```

という捕獲線が育っている。

## 9. 次の一手

次は、一般 \(k\) 回作用へ行きたいところじゃが、いきなり完全一般 theorem に行く前に、少し整理すると安全じゃ。

まず欲しいのは、反復記法の API じゃ。

```lean id="fl0oip"
def semanticActIter
    (r : UnitKernel DkNNRealQ) (k : ℕ) (z : Vec ℝ) : Vec ℝ :=
  (semanticAct r)^[k] z
```

あるいは既存に `semanticActLevel` / orbit 系があるなら、それを使う方が良い。

その上で special theorem を置ける。

```lean id="gjv7u5"
theorem pairToEuclideanPlane_semanticActIter_two_eq_rotation_semanticPhaseAngle
```

```lean id="np7psg"
theorem pairToEuclideanPlane_semanticActIter_four_eq_rotation_semanticPhaseAngle
```

今の theorem はネストした `semanticAct r (semanticAct r ...)` で書かれている。
これは special case では十分だが、次の一般化には iterate 形式が欲しい。

## 10. 一般 theorem の候補

最終的にはこういう形が欲しい。

```lean id="qzeul1"
theorem pairToEuclideanPlane_semanticAct_iterate_eq_rotation_semanticPhaseAngle
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (k : ℕ) (z : Vec ℝ) :
    pairToEuclideanPlane
      (Vec.toProd ((semanticAct r)^[k] z)) =
    euclideanPlaneOrientation.rotation (semanticPhaseAngle k)
      (pairToEuclideanPlane (Vec.toProd z))
```

ただし注意点がある。
これは本当に \(k\) すべてで証明するには、rotation 側の angle addition theorem と、semantic action 側の composition theorem が必要じゃ。

さらに、semantic action が本当に毎回同じ `r` での作用であり、その action が quarter-turn と一致していることが必要になる。

今すでに \(k=1,2,4\) はある。
一般化は次でよい。

## 11. modulo 4 版も候補

exact order four を強調するなら、一般 \(k\) では modulo 4 版も自然じゃ。

```text id="tir1wn"
k mod 4 = 0:
  identity / full-turn

k mod 4 = 1:
  quarter-turn

k mod 4 = 2:
  negation / half-turn

k mod 4 = 3:
  inverse quarter-turn
```

このルートでは、次に \(k=3\) が欲しくなる。

```text id="g0j48e"
three semantic actions
  ↔ rotation by 3*pi/2
  ↔ inverse quarter-turn
```

これが揃うと、四状態表が完成する。

なので次は一般 \(k\) へ飛ぶより、

```text id="s5ryor"
k = 3
```

を埋めるのもかなり良い。

## 12. 気になる点

大きな問題はない。

一点だけ、`semanticAct_four` の証明で `semanticAct_twice_of_core_eq_zero` を二回 `rw` しているが、build が通っているなら問題ない。
ただ、将来読みやすさを上げるなら、既存に `semanticAct_four_of_core_eq_zero` のような theorem を置いても良い。

例えば、

```lean id="nujwc7"
theorem semanticAct_four_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    semanticAct r (semanticAct r (semanticAct r (semanticAct r z))) = z
```

を semantic 層側に置いて、Euclidean bridge ではそれを使う。
そうすると今回の theorem がさらに読みやすくなる。

## 13. 結論

今回の差分は採用でよい。

```text id="x3pzir"
実装:
  良い。二回作用・四回作用と Euclidean angle reading が接続された。

数学:
  良い。exact order-four structure が pi / pi*2 の Euclidean rotation として読める。

設計:
  良い。一般 k theorem に行く前に k=2,4 の special case を固めている。

安全性:
  良い。pi の内在的構成ではなく、Euclidean interpretation として整理されている。

次:
  semanticAct の iterate API を整える。
  あるいは k=3 を埋めて四状態表を完成させる。
```

ぬしよ、これはかなり良い一歩じゃ。
これで対称性ルートは、単に「一回作用が \(\pi/2\)」ではなく、

```text id="j5x2kp"
二回で pi
四回で 2pi
四回で戻る
```

まで Lean で読めるようになった。

次に \(k=3\) を埋めれば、四状態の角度読みが完全に閉じる。
そのあと一般 \(k\) の反復 theorem に行けばよい。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
index 2b7492fe..cd5e407d 100644
--- a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
+++ b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
@@ -133,6 +133,17 @@ k semantic actions  <->  Euclidean rotation by semanticPhaseAngle k
 The implemented special cases already read two quarter-turns as negation and
 four quarter-turns as the identity rotation.
 
+The action side is now connected for the first two special cases:
+
+```text
+two semantic actions   <->  Euclidean rotation by semanticHalfTurnAngle
+four semantic actions  <->  Euclidean rotation by semanticFullTurnAngle
+```
+
+These theorems use the pre-existing core-zero action laws: two actions
+negate both coordinates, while four actions return to the identity. Thus the
+angle reading remains downstream of the algebraic order-four structure.
+
 ### Milestone A: continuous four-edge loop - implemented
 
 1. The real CF2D target carries the topology induced from `Real × Real`.
diff --git a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/EuclideanPhase.lean b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/EuclideanPhase.lean
index 715a0971..ead8b5e7 100644
--- a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/EuclideanPhase.lean
+++ b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/EuclideanPhase.lean
@@ -160,6 +160,13 @@ theorem pairToEuclideanPlane_euclideanPlaneToPair (v : EuclideanPlane) :
   ext i
   fin_cases i <;> rfl
 
+/-- Coordinate insertion commutes with negation. -/
+theorem pairToEuclideanPlane_neg (p : ℝ × ℝ) :
+    pairToEuclideanPlane (-p.1, -p.2) = -pairToEuclideanPlane p := by
+  apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
+  ext i
+  fin_cases i <;> simp [pairToEuclideanPlane]
+
 /-- The coordinate insertion into the Euclidean plane is continuous. -/
 theorem continuous_pairToEuclideanPlane :
     Continuous pairToEuclideanPlane := by
@@ -398,6 +405,28 @@ theorem semanticPhaseAngle_one :
     semanticPhaseAngle 1 = semanticQuarterTurnAngle := by
   simp [semanticPhaseAngle]
 
+@[simp]
+theorem semanticPhaseAngle_two :
+    semanticPhaseAngle 2 = semanticHalfTurnAngle :=
+  rfl
+
+@[simp]
+theorem semanticPhaseAngle_four :
+    semanticPhaseAngle 4 = semanticFullTurnAngle :=
+  rfl
+
+/--
+Semantic phase angles add by adding their phase indices.
+
+This is the Euclidean angle-side vocabulary for the later theorem that
+successive semantic actions correspond to angle addition.
+-/
+theorem semanticPhaseAngle_add (m n : ℕ) :
+    semanticPhaseAngle (m + n) =
+      semanticPhaseAngle m + semanticPhaseAngle n := by
+  simp [semanticPhaseAngle]
+  ring
+
 @[simp]
 theorem semanticHalfTurnAngle_eq_pi :
     semanticHalfTurnAngle = Real.pi := by
@@ -550,6 +579,53 @@ theorem pairToEuclideanPlane_semanticAct_eq_rotation_semanticQuarterTurnAngle
   simpa [semanticQuarterTurnAngle] using
     pairToEuclideanPlane_semanticAct_eq_rotation_pi_div_two hcore z
 
+/--
+Under the Euclidean coordinate bridge, two semantic core-zero actions are
+rotation by the semantic half-turn angle.
+
+This is the first action-iteration bridge: the algebraic two-step action is
+negation of both coordinates, and the Euclidean angle reading is
+`theta = pi`.
+-/
+theorem pairToEuclideanPlane_semanticAct_twice_eq_rotation_semanticHalfTurnAngle
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    pairToEuclideanPlane (Vec.toProd (semanticAct r (semanticAct r z))) =
+      euclideanPlaneOrientation.rotation semanticHalfTurnAngle
+        (pairToEuclideanPlane (Vec.toProd z)) := by
+  rw [semanticAct_twice_of_core_eq_zero hcore,
+    rotation_semanticHalfTurnAngle_eq_neg]
+  cases z with
+  | mk x y =>
+      exact pairToEuclideanPlane_neg (x, y)
+
+/--
+Under the Euclidean coordinate bridge, four semantic core-zero actions are
+rotation by the semantic full-turn angle.
+
+This is the finite-order bridge for the present stage: exact order four on
+the semantic side is read as the Euclidean identity rotation by `2 * pi`.
+-/
+theorem pairToEuclideanPlane_semanticAct_four_eq_rotation_semanticFullTurnAngle
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (z : Vec ℝ) :
+    pairToEuclideanPlane
+        (Vec.toProd
+          (semanticAct r (semanticAct r (semanticAct r (semanticAct r z))))) =
+      euclideanPlaneOrientation.rotation semanticFullTurnAngle
+        (pairToEuclideanPlane (Vec.toProd z)) := by
+  have htwo :
+      semanticAct r (semanticAct r (semanticAct r (semanticAct r z))) = z := by
+    rw [semanticAct_twice_of_core_eq_zero hcore,
+      semanticAct_twice_of_core_eq_zero hcore]
+    cases z with
+    | mk x y =>
+        simp
+  rw [htwo, rotation_semanticFullTurnAngle_eq_refl]
+  rfl
+
 end
 
 end DkMath.Analysis.DkNNRealQ
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
index 9bef77f2..d8b7f2bb 100644
--- a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
@@ -1256,3 +1256,30 @@ Archive
 5. documentation:
    - `research-pregeometric-pi-program-067.md` の first angle reading
      milestone を half/full turn まで拡張した。
+
+### 2026/06/27 18:39 JST (Semantic action iteration angle bridge)
+
+1. angle API:
+   - `semanticPhaseAngle_two` と `semanticPhaseAngle_four` を追加し、
+     phase index `2` と `4` が half/full turn 名に一致することを
+     simp theorem として記録した。
+   - `semanticPhaseAngle_add` を追加し、phase index の加法が angle の
+     加法として読めることを記録した。
+2. coordinate bridge:
+   - `pairToEuclideanPlane_neg` を追加し、coordinate insertion が
+     negation と可換であることを記録した。
+3. action iteration bridge:
+   - `pairToEuclideanPlane_semanticAct_twice_eq_rotation_semanticHalfTurnAngle`
+     を追加した。
+   - `pairToEuclideanPlane_semanticAct_four_eq_rotation_semanticFullTurnAngle`
+     を追加した。
+4. interpretation:
+   - 既存の core-zero action law
+     `semanticAct_twice_of_core_eq_zero` を使い、二回作用は Euclidean
+     half-turn として読まれる。
+   - 四回作用は Euclidean full-turn、すなわち identity rotation として
+     読まれる。
+   - まだ一般 `k` 回作用の theorem は未実装。
+5. verification:
+   - `lake build DkMath.CosmicFormula.Rotation.CF2D.EuclideanPhase` 成功
+     (8278 jobs)。
````
`````
