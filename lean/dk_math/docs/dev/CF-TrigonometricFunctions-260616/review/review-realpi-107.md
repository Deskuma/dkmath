# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2DPhaseShift

gch: 320487674f823b6aaee457fbbd90c7364fc4f181

## Report

補正しつつ次へ進めました。

[SemanticCF2DPhaseShift.lean](/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean) に、レビューで挙がっていた加法形 API を追加しました。

```lean
globalQuarterEndpoint_succ_eq_endpoint_add_quarter
globalQuarterCenter_succ_eq_center_add_quarter
```

既存の差分形 `globalQuarterCenter_succ_sub_center` に加えて、後続の shifted-frame path 定義でそのまま使いやすい形です。

[design-phase-center-shift-104.md](/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md) の implemented checkpoint にも反映済みです。

検証:

```text
lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift
lake build DkMath.Analysis.DkReal
git diff --check
```

すべて成功です。

## Review

うむ、賢狼レビューじゃ。
今回の差分は **採用でよい**。これは小さいが、後続の shifted-frame path 定義へ向けてかなり実用的な補強じゃ。

## 1. 状況解説

前回までで `SemanticCF2DPhaseShift.lean` には、主に次が入っていた。

```text
globalQuarterEndpoint k
globalQuarterCenter k
globalQuarterCenter_eq_endpoint_add_halfQuarter
globalQuarterCenter_succ_sub_center
globalQuarterEndpoint_succ_is_center_between_centers
```

今回追加されたのは、差分形ではなく **加法形** の API じゃ。

```lean
globalQuarterEndpoint_succ_eq_endpoint_add_quarter
globalQuarterCenter_succ_eq_center_add_quarter
```

これは、数学的にはほぼ当然の等式だが、Lean 実装ではかなり効く。

## 2. endpoint 側の加法形

追加 theorem はこれ。

```lean
theorem globalQuarterEndpoint_succ_eq_endpoint_add_quarter (k : ℕ) :
    globalQuarterEndpoint (k + 1) =
      globalQuarterEndpoint k + 1 / 4 := by
  simp [globalQuarterEndpoint]
  ring
```

意味は、

$$
\mathrm{endpoint}_{k+1} = \mathrm{endpoint}_k+\frac{1}{4}
$$

じゃな。

これは unwrapped full-cycle coordinate 上で、隣の quarter endpoint へ進む操作を明示している。

ここでもまだ角度ではない。
ただの正規化周期パラメータ上の \(1/4\) step。

## 3. center 側の加法形

もうひとつはこれ。

```lean
theorem globalQuarterCenter_succ_eq_center_add_quarter (k : ℕ) :
    globalQuarterCenter (k + 1) =
      globalQuarterCenter k + 1 / 4 := by
  simp [globalQuarterCenter]
  ring
```

意味は、

$$
\mathrm{center}_{k+1} = \mathrm{center}_k+\frac{1}{4}
$$

じゃ。

既存の

```lean
globalQuarterCenter_succ_sub_center
```

は差分形だった。

$$
\mathrm{center}_{k+1}-\mathrm{center}_k=\frac{1}{4}
$$

今回の theorem は加法形なので、後続で path endpoint を作るときにそのまま `rw` しやすい。

## 4. なぜこの小補題が効くか

shifted-frame path を定義するとき、おそらく次のような点を扱うことになる。

```text
left shifted endpoint:
  globalQuarterCenter k

right shifted endpoint:
  globalQuarterCenter (k + 1)

shifted center:
  globalQuarterEndpoint (k + 1)
```

このとき、右 endpoint を左 endpoint からの \(1/4\) step として見たい。

$$
\mathrm{right} = \mathrm{left}+\frac{1}{4}
$$

この形で theorem があると、affine parameterization を書くときに便利じゃ。

例えば、中心間 edge を

$$
(1-t),\mathrm{center}*k+t,\mathrm{center}*{k+1}
$$

のように扱う場合、`center_{k+1}` を `center_k + 1/4` と読める。
これにより、shifted frame が「同じ幅 \(1/4\) の edge」として扱いやすくなる。

## 5. 差分形と加法形は両方あるのが良い

今回の判断は正しい。

差分形は距離・幅を読むときに良い。

```lean
globalQuarterCenter_succ_sub_center
```

加法形は遷移・次点・path definition に良い。

```lean
globalQuarterCenter_succ_eq_center_add_quarter
```

両方あることで、証明の向きに応じて theorem を選べる。

```text
差分形:
  width / separation を読む

加法形:
  next endpoint / shifted path を構成する
```

この使い分けは Lean ではかなり大事じゃ。

## 6. docs 反映も良い

`design-phase-center-shift-104.md` の implemented checkpoint に、今回の二つを追加したのも良い。

これで設計資料を見たとき、単に endpoint-center theorem があるだけでなく、後続の shifted-frame path 用に必要な scalar step API も揃っていることが分かる。

## 7. 次の実装候補

次は、本当に shifted-frame の名前を置ける段階じゃ。

最小なら、まだ path には行かず scalar alias だけでよい。

```lean
def shiftedQuarterLeftEndpoint (k : ℕ) : ℝ :=
  globalQuarterCenter k

def shiftedQuarterRightEndpoint (k : ℕ) : ℝ :=
  globalQuarterCenter (k + 1)

def shiftedQuarterCenter (k : ℕ) : ℝ :=
  globalQuarterEndpoint (k + 1)
```

そして、

```lean
theorem shiftedQuarterCenter_eq_midpoint (k : ℕ) :
    shiftedQuarterCenter k =
      (shiftedQuarterLeftEndpoint k + shiftedQuarterRightEndpoint k) / 2
```

これは既存の `globalQuarterEndpoint_succ_is_center_between_centers` の wrapper で閉じるはずじゃ。

この theorem が入ると、文脈上の意味がさらに明確になる。

```text
old frame:
  endpoint between two quarter edges

shifted frame:
  center between neighboring centers
```

## 8. まだ path へ急がなくてよい

shifted-frame path definition は次の大きめの段階じゃ。

現状は scalar coordinate layer がとてもきれいに育っている。
ここで無理に `semanticPhaseEdge` や `normalizedPhaseEdge` の shifted path へ飛ばず、まず scalar shifted frame の API を薄く作るのは良い進め方じゃ。

つまり次は、

```text
scalar shifted frame
```

その後に、

```text
semantic shifted edge
```

最後に、

```text
normalized shifted boundary preservation
```

が自然じゃな。

## 9. 結論

今回の差分は採用でよい。

```text
実装:
  良い。endpoint と center の succ 加法形 API が揃った。

数学:
  良い。unwrapped quarter coordinate 上で、隣接点が 1/4 step で進むことを明示した。

設計:
  良い。shifted-frame path 定義に向けて、rw しやすい形が追加された。

安全性:
  良い。角度・円弧・pi/4 にはまだ触れていない。

次:
  shiftedQuarterLeftEndpoint / shiftedQuarterRightEndpoint / shiftedQuarterCenter の scalar alias、
  あるいは shifted center midpoint theorem の wrapper。
```

ぬしよ、これは地味だが良い補強じゃ。
この加法形があると、次に「隣接 center を新しい端点にする」構造がかなり書きやすくなる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
index fcc9359b..b05e8e2a 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
@@ -116,6 +116,16 @@ theorem globalQuarterCenter_eq_endpoint_add_halfQuarter (k : ℕ) :
   simp [globalQuarterCenter, globalQuarterEndpoint, phaseHalfQuarterStep]
   ring
 
+/--
+Successive quarter endpoints differ by one quarter of the unwrapped full
+cycle.
+-/
+theorem globalQuarterEndpoint_succ_eq_endpoint_add_quarter (k : ℕ) :
+    globalQuarterEndpoint (k + 1) =
+      globalQuarterEndpoint k + 1 / 4 := by
+  simp [globalQuarterEndpoint]
+  ring
+
 /--
 Neighboring quarter-edge centers are separated by one full quarter step.
 
@@ -127,6 +137,16 @@ theorem globalQuarterCenter_succ_sub_center (k : ℕ) :
   simp [globalQuarterCenter]
   ring
 
+/--
+Additive form of the center-step law, convenient for later shifted-frame
+definitions.
+-/
+theorem globalQuarterCenter_succ_eq_center_add_quarter (k : ℕ) :
+    globalQuarterCenter (k + 1) =
+      globalQuarterCenter k + 1 / 4 := by
+  simp [globalQuarterCenter]
+  ring
+
 /--
 If adjacent quarter-edge centers are used as the endpoints of a shifted
 observation frame, the old seam endpoint becomes the new center.
diff --git a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
index 414b8347..c01b6be6 100644
--- a/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
+++ b/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md
@@ -310,7 +310,9 @@ SemanticCF2DPhaseShift.lean
   globalQuarterEndpoint_zero
   globalQuarterEndpoint_four
   globalQuarterCenter_eq_endpoint_add_halfQuarter
+  globalQuarterEndpoint_succ_eq_endpoint_add_quarter
   globalQuarterCenter_succ_sub_center
+  globalQuarterCenter_succ_eq_center_add_quarter
   globalQuarterEndpoint_succ_is_center_between_centers
   normalizedCycleStep
   dyadicCycleStep
````
`````
