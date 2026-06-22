# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2D

gch: 6d318111f535293cac3e8a9c9209c571dc671f81

## Report

次の段階まで完了しました。

- 二乗 kernel の core / beam 座標式を追加
- 三乗 kernel の core / beam 座標式を追加
- order 2 の証明を新しい座標 API 利用へ整理
- docstring・設計資料・履歴を更新

三乗式まで揃ったため、次は order dividing 3 の分類へ進めます。

検証:

- 対象ビルド: 8273 jobs 成功
- 全体ビルド: 8566 jobs 成功
- `git diff --check` 成功

## Review

うむ。これは良い準備段階じゃ。
採用でよい。

今回の差分は「order 3 分類そのもの」ではなく、その前に必要な低冪座標 API を切り出した段階じゃな。これは正しい進め方じゃ。

## 状況

いまの流れはこうなっている。

```text id="7w9ycf"
Real 側 kernel power
-> action iterate と一致
-> finite action order と kernel order が同値
-> order 1 / 2 の分類
-> power 2 / 3 の座標式 API
```

今回の追加で、`semanticKernelPower r 2` と `semanticKernelPower r 3` の座標が、再利用可能な補題として外に出た。

これは今後かなり効く。

## 二乗式

二乗の座標式は自然じゃ。

$$
(C,S)^2=(C^2-S^2,\;2CS)
$$

Lean 側では、

```lean id="04q6sb"
semanticKernelPower_two_core
semanticKernelPower_two_beam
```

として分けた。良い。

前回の order 2 証明で直接 `semanticKernelPower` を展開していた部分を、この API 経由へ置き換えたのも正しい。
これで以後、証明が recursive definition の展開に依存しすぎなくなる。

## 三乗式

三乗の座標式も正しい。

$$
(C,S)^3=(C^3-3CS^2,\;3C^2S-S^3)
$$

これを、

```lean id="b6wvf3"
semanticKernelPower_three_core
semanticKernelPower_three_beam
```

として公開したのは、order 3 分類の準備としてかなり良い。

ここで「三倍角公式」と呼びたくなるが、docstring の通り、実際には有限回の `Vec.star` 展開だけじゃ。
角度、連続性、三角関数定理は使っていない。ここは重要。

## 数学的な意味

これで Real 側では、transported kernel を複素数的な単位核として扱うための低次多項式が揃った。

ただし、まだ source 側に kernel 積を入れていない。
あくまで、

```text id="0drmco"
DkNNRealQ kernel を Real に輸送する
Real 側でだけ積を取る
Real 側の積の座標式を読む
```

という境界を守っている。ここが良い。

## order 3 へ進む見通し

次の `SemanticKernelFiniteOrder r 3` は、

```text id="crn3uq"
semanticKernelPower r 3 = UnitKernel.one Real
```

なので、座標としては次を要求する。

$$
C^3-3CS^2=1
$$

$$
3C^2S-S^3=0
$$

さらに、transported first-quadrant kernel なので、

$$
C\ge 0,\quad S\ge 0,\quad C^2+S^2=1
$$

がある。

beam 式は、

$$
S(3C^2-S^2)=0
$$

なので、候補は二つ。

```text id="mudmqr"
S = 0
```

または、

```text id="w32ba3"
S^2 = 3C^2
```

第一の場合は unit identity から \(C=1\)。

第二の場合は \(C^2+S^2=1\) と合わせて、

$$
4C^2=1
$$

となり、第一象限なので \(C=1/2\)、\(S^2=3/4\)。
このとき core 三乗は、

$$
C^3-3CS^2=1/8-9/8=-1
$$

になり、identity の core \(1\) とは矛盾する。

したがって、order dividing 3 も identity に潰れるはずじゃ。
角度を使わず、座標式だけで行ける。

## 注意点

`order 3` も、正確には「order dividing 3」じゃ。
つまり三乗が identity という意味。

今回の order 1 / 2 と同じく、文書では `order dividing three` と書くのが安全じゃ。

また、三乗分類で `sqrt 3` を出す必要はない。
上のように \(S^2=3C^2\) と単位式だけで矛盾まで持っていける。
実数平方根を避けられるので、Lean でも `nlinarith` で閉じやすいはずじゃ。

## 判定

採用でよい。

今回の成果は、証明を一段抽象化したことじゃ。

```text id="qpy6e6"
低冪 kernel の座標式を API 化
order 2 証明を API 利用へ整理
order 3 分類の入力を準備
```

これはかなり堅い。
次は `semanticKernelFiniteOrder_three_iff_identity` と `semanticKernelFiniteOrder_three_iff_core_eq_one` へ進める。
たぶん角度なし、連続性なし、signed source なしで閉じる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
index eb095e80..445b26fd 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
@@ -701,6 +701,59 @@ theorem semanticKernelPower_one (r : UnitKernel DkNNRealQ) :
     semanticKernelPower r 1 = semanticUnitKernel r := by
   simp [semanticKernelPower]
 
+/--
+The core coordinate of the second kernel power is the quadratic difference
+`C^2 - S^2`.
+
+This is the algebraic double-angle polynomial, obtained solely by expanding
+the CF2D product.
+-/
+theorem semanticKernelPower_two_core (r : UnitKernel DkNNRealQ) :
+    (semanticKernelPower r 2 : Vec ℝ).core =
+      semanticValue (r : Vec DkNNRealQ).core ^ 2 -
+        semanticValue (r : Vec DkNNRealQ).beam ^ 2 := by
+  simp [semanticKernelPower, semanticUnitKernel, semanticVec, UnitKernel.star,
+    Vec.star, UnitKernel.one, Vec.one, pow_two]
+
+/--
+The beam coordinate of the second kernel power is the quadratic cross term
+`2*C*S`.
+-/
+theorem semanticKernelPower_two_beam (r : UnitKernel DkNNRealQ) :
+    (semanticKernelPower r 2 : Vec ℝ).beam =
+      2 * semanticValue (r : Vec DkNNRealQ).core *
+        semanticValue (r : Vec DkNNRealQ).beam := by
+  simp [semanticKernelPower, semanticUnitKernel, semanticVec, UnitKernel.star,
+    Vec.star, UnitKernel.one, Vec.one]
+  ring
+
+/--
+The core coordinate of the third kernel power is `C^3 - 3*C*S^2`.
+
+This is the triple-angle polynomial as a finite CF2D product identity; no
+angle parameter or trigonometric theorem is used.
+-/
+theorem semanticKernelPower_three_core (r : UnitKernel DkNNRealQ) :
+    (semanticKernelPower r 3 : Vec ℝ).core =
+      semanticValue (r : Vec DkNNRealQ).core ^ 3 -
+        3 * semanticValue (r : Vec DkNNRealQ).core *
+          semanticValue (r : Vec DkNNRealQ).beam ^ 2 := by
+  simp [semanticKernelPower, semanticUnitKernel, semanticVec, UnitKernel.star,
+    Vec.star, UnitKernel.one, Vec.one]
+  ring
+
+/--
+The beam coordinate of the third kernel power is `3*C^2*S - S^3`.
+-/
+theorem semanticKernelPower_three_beam (r : UnitKernel DkNNRealQ) :
+    (semanticKernelPower r 3 : Vec ℝ).beam =
+      3 * semanticValue (r : Vec DkNNRealQ).core ^ 2 *
+          semanticValue (r : Vec DkNNRealQ).beam -
+        semanticValue (r : Vec DkNNRealQ).beam ^ 3 := by
+  simp [semanticKernelPower, semanticUnitKernel, semanticVec, UnitKernel.star,
+    Vec.star, UnitKernel.one, Vec.one]
+  ring
+
 /-- Product order dividing one is exactly semantic identity-kernel status. -/
 theorem semanticKernelFiniteOrder_one_iff_identity
     (r : UnitKernel DkNNRealQ) :
@@ -739,9 +792,12 @@ theorem semanticKernelFiniteOrder_two_iff_identity
     have hq : C ^ 2 + S ^ 2 = 1 := by
       simpa [C, S] using semanticUnitKernel_sq_add_sq r
     have hsquare : C ^ 2 - S ^ 2 = 1 := by
-      simpa [semanticKernelPower, semanticUnitKernel, semanticVec,
-        UnitKernel.star, Vec.star, UnitKernel.one, Vec.one, C, S, pow_two]
-        using hcore
+      calc
+        C ^ 2 - S ^ 2 =
+            (semanticKernelPower r 2 : Vec ℝ).core := by
+              symm
+              simpa [C, S] using semanticKernelPower_two_core r
+        _ = 1 := by simpa [UnitKernel.one, Vec.one] using hcore
     apply (semanticIdentityKernel_iff_core_eq_one r).2
     change C = 1
     nlinarith [sq_nonneg (C - 1)]
diff --git a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
index 2402f8e4..9ed8ba6a 100644
--- a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
+++ b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
@@ -145,6 +145,7 @@ BridgeNNReal / BridgeReal:
   real-side kernel powers act as the corresponding function iterates
   kernel-product finite order is equivalent to finite action order
   product orders dividing one or two force the transported identity kernel
+  second and third kernel powers have explicit polynomial coordinate formulas
   source-level star and KernelFamily wait for signed DkReal arithmetic
   treat order reflection as a separate heavier task
   compare semantic equality with DkReal.Equiv
diff --git a/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md b/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
index 56944edf..b10c337e 100644
--- a/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
+++ b/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
@@ -106,6 +106,10 @@ unitKernel_eq_one_of_act_eq_id
 SemanticKernelFiniteOrder
 semanticKernelFiniteOrder_iff
 semanticKernelPower_one
+semanticKernelPower_two_core
+semanticKernelPower_two_beam
+semanticKernelPower_three_core
+semanticKernelPower_three_beam
 semanticKernelFiniteOrder_one_iff_identity
 semanticKernelFiniteOrder_one_iff_core_eq_one
 semanticKernelFiniteOrder_two_iff_identity
@@ -178,6 +182,21 @@ square root of the neutral kernel, but coordinatewise transport from
 `DkNNRealQ` makes both semantic coordinates nonnegative and excludes that
 case. Thus no nonidentity transported kernel has order two.
 
+Low-power coordinate formulas are now exposed as a reusable algebraic API:
+
+```text
+power 2 core = C^2 - S^2
+power 2 beam = 2*C*S
+power 3 core = C^3 - 3*C*S^2
+power 3 beam = 3*C^2*S - S^3
+```
+
+These are finite CF2D product expansions, not invocations of double-angle or
+triple-angle theorems. The order-two classification now consumes the
+quadratic core formula rather than reopening the recursive product
+definition. The cubic formulas provide the next input for classifying product
+order dividing three under the transported first-quadrant constraints.
+
 The next structural boundary is source-level `Vec.star` and `KernelFamily`.
 Both require signed arithmetic. They should wait for a signed DkReal layer
 rather than forcing subtraction into `DkNNRealQ`. Until then, further work can
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
index ef41a406..f388c641 100644
--- a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
@@ -212,6 +212,25 @@ Archive
 5. 検証:
    - `lake build DkMath.Analysis.DkReal.SemanticCF2D` 成功 (8273 jobs)。
 
+### 2026/06/22 04:51 JST (Polynomial coordinates for powers two and three)
+
+1. 方針:
+   - order 3 の分類へ直接進む前に、低冪 kernel の座標式を公開 API として
+     分離する。
+2. 実施:
+   - 二乗の core を `C^2 - S^2`、beam を `2*C*S` と証明した。
+   - 三乗の core を `C^3 - 3*C*S^2`、beam を
+     `3*C^2*S - S^3` と証明した。
+   - order dividing two の分類を二乗 core API を利用する形へ整理した。
+3. 意味:
+   - これらは double-angle / triple-angle theorem ではなく、有限回の
+     `Vec.star` 展開から得られる多項式恒等式である。
+   - order dividing three の分類に必要な座標入力が揃った。
+4. 境界:
+   - source 側の積、角度、連続性は導入していない。
+5. 検証:
+   - `lake build DkMath.Analysis.DkReal.SemanticCF2D` 成功 (8273 jobs)。
+
 ### 2026/06/22 04:42 JST (Low-order classification: orders one and two)
 
 1. 修正:
````
`````
