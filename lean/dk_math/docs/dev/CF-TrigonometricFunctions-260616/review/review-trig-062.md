# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2D

gch: 1ae599e809b233a08184a597b727026a9f5c628b

## Report

order dividing 4 の分類を完了しました。

- 四乗 kernel の core / beam 座標式を追加
- 四乗が identity となる条件を `core = 1 ∨ core = 0` と分類
- `core = 0` では beam が `1` に確定
- 初の非 identity 有限位数 kernel `(0,1)` を検出
- 文書と履歴を更新

検証:

- 対象ビルド: 8273 jobs 成功
- 全体ビルド: 8566 jobs 成功
- `git diff --check` 成功

## Review

うむ。これはかなり面白い段階じゃ。
採用でよい。

今回で、低位数分類の様子がはっきり見えた。

```text id="4d83ll"
order dividing 1 -> identity
order dividing 2 -> identity
order dividing 3 -> identity
order dividing 4 -> identity または (0,1)
```

ここで初めて、非 identity branch が残った。

## 状況の意味

DkNNRealQ 由来の transported kernel は第一象限にいる。

$$
C\ge 0,\quad S\ge 0,\quad C^2+S^2=1
$$

この制約のもとで、Real 側の kernel power を分類している。

order 1, 2, 3 では、第一象限内の非自明候補が消えて identity だけになった。
しかし order 4 では、

$$
(C,S)=(0,1)
$$

が残る。

これは幾何的には quarter-turn だが、今回の証明では角度を使っていない。
有限積の座標多項式だけで検出している。ここが良い。

## 四乗式の評価

追加された座標式は正しい。

$$
\operatorname{core}(k^4)=C^4-6C^2S^2+S^4
$$

$$
\operatorname{beam}(k^4)=4CS(C^2-S^2)
$$

これを API として外に出したのは良い。
order 4 分類だけでなく、今後の低位数分類にも使える。

## order dividing 4 の証明

証明の核はかなり綺麗じゃ。

四乗が identity なら core 方程式から、

$$
C^4-6C^2S^2+S^4=1
$$

一方、unit-square を二乗すると、

$$
(C^2+S^2)^2=1
$$

つまり、

$$
C^4+2C^2S^2+S^4=1
$$

両者を比べると、

$$
C^2S^2=0
$$

が出る。

したがって、

```text id="m8nkk3"
C = 0
```

または、

```text id="y6dk2z"
S = 0
```

となる。

`S = 0` 側では unit-square と \(C\ge 0\) により \(C=1\)。
`C = 0` 側では unit-square と \(S\ge 0\) により \(S=1\)。
つまり分類は、

$$
C=1\quad\text{or}\quad C=0
$$

になる。

Lean の流れもこの数学と一致していてよい。

## 重要な発見

ここで初めて、非 identity の有限位数 kernel が見えた。

$$
(C,S)=(0,1)
$$

これは第一象限内にいる。
だから DkNNRealQ からの coordinatewise transport と矛盾しない。

ただし、ここが重要なのだが、この kernel の二乗は Real 側では

$$
(-1,0)
$$

になる。
これは第一象限を出る。

つまり、

```text id="4xs6wu"
元の kernel は DkNNRealQ 由来でよい
しかしその二乗 kernel は source 側へ戻らない
```

ということじゃ。

これは、今の設計方針を強く支持している。
source 側に積を入れず、Real 側でだけ kernel power を扱う判断が正しかった。

## 注意点

今回の theorem は、

```lean id="h1gayo"
SemanticKernelFiniteOrder r 4 ↔ core = 1 ∨ core = 0
```

なので、「四乗が identity」という分類じゃ。

`core = 0` の枝は exact order 4 の候補だが、exact order 4 そのものを theorem として出したわけではない。

ただし、既に order 1, 2, 3 の分類があるので、次に簡単に exact order 4 を示せるはずじゃ。

例えば core \(=0\) なら、

```text id="y4912x"
order dividing 4
not order dividing 1
not order dividing 2
not order dividing 3
```

が言える。
特に order 2 と order 3 は、既存の iff により core \(=1\) が必要なので、core \(=0\) から排除できる。

## 次の自然な補題

次はこのあたりじゃ。

```text id="53zaee"
core = 0 -> beam = 1
core = 0 -> SemanticKernelFiniteOrder r 4
core = 0 -> ¬ SemanticKernelFiniteOrder r 1
core = 0 -> ¬ SemanticKernelFiniteOrder r 2
core = 0 -> ¬ SemanticKernelFiniteOrder r 3
```

そして、名前を付けるなら、

```lean id="ru4ilm"
SemanticExactKernelOrderFour
```

のような定義も考えられる。

ただし、exact order を一般化すると少し重くなるので、まずは `core = 0` branch 用の補題を作るのがよい。

## 判定

採用でよい。かなり良い。

今回の到達点はこうじゃ。

```text id="ynyejc"
第一象限 transported kernel では、
1, 2, 3 回で identity になるなら identity そのもの。
しかし 4 回では、初めて非 identity branch (0,1) が現れる。
```

これは非常に綺麗な構造じゃ。
角度を使わずに、低位数の回転構造が座標多項式から生まれている。
まさに CF2D らしい進展じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
index 5e62e524..5a311213 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
@@ -754,6 +754,34 @@ theorem semanticKernelPower_three_beam (r : UnitKernel DkNNRealQ) :
     Vec.star, UnitKernel.one, Vec.one]
   ring
 
+/--
+The core coordinate of the fourth kernel power is
+`C^4 - 6*C^2*S^2 + S^4`.
+-/
+theorem semanticKernelPower_four_core (r : UnitKernel DkNNRealQ) :
+    (semanticKernelPower r 4 : Vec ℝ).core =
+      semanticValue (r : Vec DkNNRealQ).core ^ 4 -
+        6 * semanticValue (r : Vec DkNNRealQ).core ^ 2 *
+          semanticValue (r : Vec DkNNRealQ).beam ^ 2 +
+        semanticValue (r : Vec DkNNRealQ).beam ^ 4 := by
+  simp [semanticKernelPower, semanticUnitKernel, semanticVec, UnitKernel.star,
+    Vec.star, UnitKernel.one, Vec.one]
+  ring
+
+/--
+The beam coordinate of the fourth kernel power is
+`4*C*S*(C^2 - S^2)`.
+-/
+theorem semanticKernelPower_four_beam (r : UnitKernel DkNNRealQ) :
+    (semanticKernelPower r 4 : Vec ℝ).beam =
+      4 * semanticValue (r : Vec DkNNRealQ).core *
+        semanticValue (r : Vec DkNNRealQ).beam *
+        (semanticValue (r : Vec DkNNRealQ).core ^ 2 -
+          semanticValue (r : Vec DkNNRealQ).beam ^ 2) := by
+  simp [semanticKernelPower, semanticUnitKernel, semanticVec, UnitKernel.star,
+    Vec.star, UnitKernel.one, Vec.one]
+  ring
+
 /-- Product order dividing one is exactly semantic identity-kernel status. -/
 theorem semanticKernelFiniteOrder_one_iff_identity
     (r : UnitKernel DkNNRealQ) :
@@ -880,6 +908,69 @@ theorem semanticKernelFiniteOrder_three_iff_core_eq_one
   rw [semanticKernelFiniteOrder_three_iff_identity,
     semanticIdentityKernel_iff_core_eq_one]
 
+/--
+Product order dividing four is characterized by a boundary core coordinate:
+the transported kernel has semantic core `1` or semantic core `0`.
+
+The `core = 1` branch is the neutral kernel. The `core = 0` branch has beam
+`1` by the unit-square equation and coordinate nonnegativity; it is the first
+nonidentity finite-order kernel admitted by the transported first quadrant.
+-/
+theorem semanticKernelFiniteOrder_four_iff_core_eq_one_or_zero
+    (r : UnitKernel DkNNRealQ) :
+    SemanticKernelFiniteOrder r 4 ↔
+      semanticValue (r : Vec DkNNRealQ).core = 1 ∨
+        semanticValue (r : Vec DkNNRealQ).core = 0 := by
+  let C := semanticValue (r : Vec DkNNRealQ).core
+  let S := semanticValue (r : Vec DkNNRealQ).beam
+  have hC : 0 ≤ C := by
+    simpa [C] using semanticUnitKernel_core_nonneg r
+  have hS : 0 ≤ S := by
+    simpa [S] using semanticUnitKernel_beam_nonneg r
+  have hq : C ^ 2 + S ^ 2 = 1 := by
+    simpa [C, S] using semanticUnitKernel_sq_add_sq r
+  constructor
+  · intro h
+    change semanticKernelPower r 4 = UnitKernel.one ℝ at h
+    have hcore := congrArg (fun k : UnitKernel ℝ => (k : Vec ℝ).core) h
+    have hfour :
+        C ^ 4 - 6 * C ^ 2 * S ^ 2 + S ^ 4 = 1 := by
+      calc
+        C ^ 4 - 6 * C ^ 2 * S ^ 2 + S ^ 4 =
+            (semanticKernelPower r 4 : Vec ℝ).core := by
+              symm
+              simpa [C, S] using semanticKernelPower_four_core r
+        _ = 1 := by simpa [UnitKernel.one, Vec.one] using hcore
+    have hqSquare : (C ^ 2 + S ^ 2) ^ 2 = 1 := by rw [hq]; norm_num
+    have hprod : C ^ 2 * S ^ 2 = 0 := by
+      nlinarith
+    rcases mul_eq_zero.mp hprod with hCsq | hSsq
+    · right
+      change C = 0
+      nlinarith [sq_nonneg C]
+    · left
+      change C = 1
+      nlinarith [sq_nonneg (C - 1), sq_nonneg S]
+  · rintro (hCeq | hCeq)
+    · have hid : semanticUnitKernel r = UnitKernel.one ℝ :=
+        (semanticIdentityKernel_iff_core_eq_one r).2 hCeq
+      change semanticKernelPower r 4 = UnitKernel.one ℝ
+      simp [semanticKernelPower, hid]
+    · have hSeq : S = 1 := by
+        change C = 0 at hCeq
+        nlinarith [sq_nonneg (S - 1)]
+      change semanticKernelPower r 4 = UnitKernel.one ℝ
+      apply UnitKernel.ext
+      have hcore :
+          (semanticKernelPower r 4 : Vec ℝ).core = 1 := by
+        simpa [C, S, hCeq, hSeq] using semanticKernelPower_four_core r
+      have hbeam :
+          (semanticKernelPower r 4 : Vec ℝ).beam = 0 := by
+        simpa [C, S, hCeq, hSeq] using semanticKernelPower_four_beam r
+      cases hp : (semanticKernelPower r 4 : Vec ℝ) with
+      | mk core beam =>
+          simp_all [UnitKernel.one, Vec.one]
+
 /-
 [TODO: semantic-cf2d/signed-kernel] Source-level `Vec.star` and
 `KernelFamily` require a ring because their core coordinate uses subtraction.
diff --git a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
index 7a9bd55f..9335aec9 100644
--- a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
+++ b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
@@ -146,6 +146,7 @@ BridgeNNReal / BridgeReal:
   kernel-product finite order is equivalent to finite action order
   product orders dividing one, two, or three force the identity kernel
   second and third kernel powers have explicit polynomial coordinate formulas
+  order dividing four is equivalent to semantic core zero or one
   source-level star and KernelFamily wait for signed DkReal arithmetic
   treat order reflection as a separate heavier task
   compare semantic equality with DkReal.Equiv
diff --git a/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md b/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
index 45eb2662..a5b20a82 100644
--- a/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
+++ b/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
@@ -110,12 +110,15 @@ semanticKernelPower_two_core
 semanticKernelPower_two_beam
 semanticKernelPower_three_core
 semanticKernelPower_three_beam
+semanticKernelPower_four_core
+semanticKernelPower_four_beam
 semanticKernelFiniteOrder_one_iff_identity
 semanticKernelFiniteOrder_one_iff_core_eq_one
 semanticKernelFiniteOrder_two_iff_identity
 semanticKernelFiniteOrder_two_iff_core_eq_one
 semanticKernelFiniteOrder_three_iff_identity
 semanticKernelFiniteOrder_three_iff_core_eq_one
+semanticKernelFiniteOrder_four_iff_core_eq_one_or_zero
 ```
 
 The transported kernel now acts on real CF2D vectors and preserves `q2`.
@@ -214,6 +217,22 @@ unit-square equation gives `C^2 = 1/4` and `S^2 = 3/4`; nonnegativity gives
 orders dividing one, two, or three all force semantic identity. This concerns
 order dividing the displayed integer, not an assertion of exact order.
 
+Order dividing four is the first classification with a nonidentity branch.
+The fourth-power core polynomial, together with the square of the unit
+equation, forces `C^2*S^2 = 0`. Coordinate nonnegativity then gives:
+
+```text
+semanticKernelPower r 4 = one
+  iff
+C = 1 or C = 0
+```
+
+The `C = 1` branch is identity. In the `C = 0` branch, the unit equation and
+`S >= 0` force `S = 1`, so the transported kernel is `(0,1)`. Thus the
+first-quadrant restriction excludes nontrivial orders two and three but admits
+the quarter-turn kernel as an exact order-four candidate, still without
+introducing an angle parameter.
+
 The next structural boundary is source-level `Vec.star` and `KernelFamily`.
 Both require signed arithmetic. They should wait for a signed DkReal layer
 rather than forcing subtraction into `DkNNRealQ`. Until then, further work can
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
index 008ebf49..c450a40c 100644
--- a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
@@ -212,6 +212,23 @@ Archive
 5. 検証:
    - `lake build DkMath.Analysis.DkReal.SemanticCF2D` 成功 (8273 jobs)。
 
+### 2026/06/22 05:15 JST (Order dividing four classification)
+
+1. 実施:
+   - 四乗 kernel の core / beam 座標多項式を API 化した。
+   - order dividing four と `semantic core = 1 or 0` の同値を証明した。
+2. 証明:
+   - 四乗 core 方程式と unit-square の二乗から `C^2*S^2 = 0` を得た。
+   - `S = 0` 側は `C = 1`、`C = 0` 側は非負性から `S = 1` となる。
+3. 結論:
+   - order dividing one, two, three は identity のみだった。
+   - order dividing four では初めて非 identity の `(0,1)` 分岐が残る。
+   - これは transported first quadrant 内の exact order-four 候補である。
+4. 境界:
+   - 90 度という角度解釈は使用せず、有限積の座標多項式だけで分類した。
+5. 検証:
+   - `lake build DkMath.Analysis.DkReal.SemanticCF2D` 成功 (8273 jobs)。
+
 ### 2026/06/22 05:02 JST (Order dividing three classification)
 
 1. 実施:
````
`````
