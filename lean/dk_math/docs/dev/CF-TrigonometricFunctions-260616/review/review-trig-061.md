# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2D

gch: fe1a5e6bb756ff84ae5b7f160fb7dba0442cfda6

## Report

order dividing 3 の分類を完了しました。

- 三乗が identity なら transported kernel 自身も identity
- semantic core coordinate が `1` であることとも同値
- 平方根・角度・連続性・signed source は不使用
- docstring、設計資料、履歴を更新

検証:

- 対象ビルド: 8273 jobs 成功
- 全体ビルド: 8566 jobs 成功
- `git diff --check` 成功

## Review

うむ。これは採用でよい。
order dividing 3 まで、かなり綺麗に閉じておる。

状況としては、Real 側 transported kernel の低位数分類がこうなった。

```text id="aorh9p"
order dividing 1 -> identity
order dividing 2 -> identity
order dividing 3 -> identity
```

ここで言う order は、正確には「その数で割る位数」または「その回数の kernel power が identity」という意味じゃ。
exact order ではない。この注意も文書に入っていて良い。

## 数学的な意味

Real unit kernel 全体で見ると、三乗して identity になる非自明な kernel は存在する。
複素数的に言えば、三乗根のうち非自明なものじゃ。

しかし、それらは第一象限にはいない。
DkNNRealQ から semantic transport された kernel は、

$$
C\ge 0,\quad S\ge 0
$$

を満たす。
この第一象限制約によって、非自明な三乗根が排除される。

だから、

```text id="f4puki"
transported first-quadrant kernel では order dividing 3 も identity に潰れる
```

という結論は正しい。

## 証明の流れ

三乗が identity なら、三乗座標式から次が出る。

$$
C^3-3CS^2=1
$$

$$
3C^2S-S^3=0
$$

さらに unit kernel なので、

$$
C^2+S^2=1
$$

beam 式は、

$$
S(3C^2-S^2)=0
$$

と因数分解される。

分岐は二つ。

```text id="5tfa7a"
S = 0
```

または、

```text id="m3jlpv"
S^2 = 3C^2
```

前者なら、unit-square から \(C^2=1\)。
さらに \(C\ge 0\) なので \(C=1\)。よって identity。

後者なら、unit-square と合わせて、

$$
C^2=\frac14,\quad S^2=\frac34
$$

さらに \(C\ge 0\) なので、

$$
C=\frac12
$$

これを core 三乗式へ入れると、

$$
C^3-3CS^2=-1
$$

となり、identity の core \(1\) と矛盾する。

平方根を出さず、角度も使わず、全部二乗量と多項式だけで閉じている。
これはかなり良い。

## Lean 実装の評価

`semanticKernelFiniteOrder_three_iff_identity` の証明は、前回用意した API をちゃんと使っている。

```lean id="8qzbyq"
semanticKernelPower_three_core
semanticKernelPower_three_beam
```

から core / beam 方程式を取り出し、それを `nlinarith` で処理している。
低冪座標式を先に API 化した判断がここで効いている。

`hfactor` で beam 式を

```lean id="7ijr0h"
S * (3 * C ^ 2 - S ^ 2) = 0
```

に落とし、`mul_eq_zero` で分岐しているのも自然じゃ。

## 良い点

特に良いのは、非自明な cube root を「角度」で排除していないこと。

普通なら「角度 \(120^\circ\), \(240^\circ\) だから第一象限ではない」と言いたくなる。
だが今回は、

```text id="0h745b"
unit-square
cubic core
cubic beam
coordinate nonnegativity
```

だけで排除している。

これは DkMath の方針に合っている。
三角関数の公式を使わず、CF2D product の有限展開から低位数分類が出ている。

## 注意点

`hS : 0 ≤ S` は今回の証明では本質的にはあまり使っていないように見える。
ただし、first-quadrant kernel の文脈を明示する意味では保持してよい。将来の補題分離で使う可能性もある。

一方、`hC : 0 ≤ C` は重要じゃ。
\(C^2=1/4\) から \(C=1/2\) を出すために必要になる。

## 次の見通し

order dividing 4 は、ここから少し様子が変わる。

第一象限には、

$$
(C,S)=(0,1)
$$

があり、これは四乗で identity になる。
つまり order dividing 4 では、非 identity が出るはずじゃ。

なので次の分類は、おそらくこうなる。

```text id="gjk54i"
SemanticKernelFiniteOrder r 4
iff
semanticUnitKernel r = one または semantic coordinates が (0, 1)
```

より DkMath 的に書くなら、

```text id="nesyrd"
core = 1
または
core = 0
```

あたりに落ちる可能性がある。
beam は unit-square と非負性から決まる。

ここで初めて、第一象限内の非自明な有限位数 kernel が現れる。
幾何的には 90 度回転だが、証明は角度なしで行ける。

## 判定

採用でよい。

今回の到達点はこうじゃ。

```text id="0m8y3a"
order dividing 1, 2, 3 は transported first-quadrant kernel では identity のみ
```

そしてこれは、角度・平方根・連続性・signed source を使わず、多項式座標式と非負性だけで示されている。
かなり良い進展じゃ。

次は order dividing 4 が面白い。
そこでは、おそらく初めて非自明な第一象限 kernel が現れる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
index 445b26fd..5e62e524 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
@@ -814,6 +814,72 @@ theorem semanticKernelFiniteOrder_two_iff_core_eq_one
   rw [semanticKernelFiniteOrder_two_iff_identity,
     semanticIdentityKernel_iff_core_eq_one]
 
+/--
+For a transported first-quadrant kernel, product order dividing three also
+forces the neutral kernel.
+
+The cubic beam equation factors as `S * (3*C^2 - S^2) = 0`. The branch
+`S = 0` gives `C = 1`. In the other branch the unit-square equation forces
+`C^2 = 1/4` and `S^2 = 3/4`, which contradicts the cubic core equation.
+No square root or angle parameter is introduced.
+-/
+theorem semanticKernelFiniteOrder_three_iff_identity
+    (r : UnitKernel DkNNRealQ) :
+    SemanticKernelFiniteOrder r 3 ↔ SemanticIdentityKernel r := by
+  let C := semanticValue (r : Vec DkNNRealQ).core
+  let S := semanticValue (r : Vec DkNNRealQ).beam
+  constructor
+  · intro h
+    change semanticKernelPower r 3 = UnitKernel.one ℝ at h
+    have hcore := congrArg (fun k : UnitKernel ℝ => (k : Vec ℝ).core) h
+    have hbeam := congrArg (fun k : UnitKernel ℝ => (k : Vec ℝ).beam) h
+    have hC : 0 ≤ C := by
+      simpa [C] using semanticUnitKernel_core_nonneg r
+    have hS : 0 ≤ S := by
+      simpa [S] using semanticUnitKernel_beam_nonneg r
+    have hq : C ^ 2 + S ^ 2 = 1 := by
+      simpa [C, S] using semanticUnitKernel_sq_add_sq r
+    have hcubic : C ^ 3 - 3 * C * S ^ 2 = 1 := by
+      calc
+        C ^ 3 - 3 * C * S ^ 2 =
+            (semanticKernelPower r 3 : Vec ℝ).core := by
+              symm
+              simpa [C, S] using semanticKernelPower_three_core r
+        _ = 1 := by simpa [UnitKernel.one, Vec.one] using hcore
+    have hbeamCubic : 3 * C ^ 2 * S - S ^ 3 = 0 := by
+      calc
+        3 * C ^ 2 * S - S ^ 3 =
+            (semanticKernelPower r 3 : Vec ℝ).beam := by
+              symm
+              simpa [C, S] using semanticKernelPower_three_beam r
+        _ = 0 := by simpa [UnitKernel.one, Vec.one] using hbeam
+    have hfactor : S * (3 * C ^ 2 - S ^ 2) = 0 := by
+      nlinarith
+    rcases mul_eq_zero.mp hfactor with hSzero | hrelation
+    · apply (semanticIdentityKernel_iff_core_eq_one r).2
+      change C = 1
+      nlinarith [sq_nonneg (C - 1)]
+    · have hCsq : C ^ 2 = 1 / 4 := by
+        nlinarith
+      have hCeq : C = 1 / 2 := by
+        nlinarith [sq_nonneg (C - 1 / 2)]
+      have hSsq : S ^ 2 = 3 / 4 := by
+        nlinarith
+      exfalso
+      nlinarith
+  · intro h
+    change semanticKernelPower r 3 = UnitKernel.one ℝ
+    rw [SemanticIdentityKernel] at h
+    simp [semanticKernelPower, h]
+
+/-- Product order dividing three is characterized by semantic core one. -/
+theorem semanticKernelFiniteOrder_three_iff_core_eq_one
+    (r : UnitKernel DkNNRealQ) :
+    SemanticKernelFiniteOrder r 3 ↔
+      semanticValue (r : Vec DkNNRealQ).core = 1 := by
+  rw [semanticKernelFiniteOrder_three_iff_identity,
+    semanticIdentityKernel_iff_core_eq_one]
+
 /-
 [TODO: semantic-cf2d/signed-kernel] Source-level `Vec.star` and
 `KernelFamily` require a ring because their core coordinate uses subtraction.
diff --git a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
index 9ed8ba6a..7a9bd55f 100644
--- a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
+++ b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
@@ -144,7 +144,7 @@ BridgeNNReal / BridgeReal:
   nonidentity transported kernels fix exactly the origin
   real-side kernel powers act as the corresponding function iterates
   kernel-product finite order is equivalent to finite action order
-  product orders dividing one or two force the transported identity kernel
+  product orders dividing one, two, or three force the identity kernel
   second and third kernel powers have explicit polynomial coordinate formulas
   source-level star and KernelFamily wait for signed DkReal arithmetic
   treat order reflection as a separate heavier task
diff --git a/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md b/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
index b10c337e..45eb2662 100644
--- a/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
+++ b/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
@@ -114,6 +114,8 @@ semanticKernelFiniteOrder_one_iff_identity
 semanticKernelFiniteOrder_one_iff_core_eq_one
 semanticKernelFiniteOrder_two_iff_identity
 semanticKernelFiniteOrder_two_iff_core_eq_one
+semanticKernelFiniteOrder_three_iff_identity
+semanticKernelFiniteOrder_three_iff_core_eq_one
 ```
 
 The transported kernel now acts on real CF2D vectors and preserves `q2`.
@@ -197,6 +199,21 @@ quadratic core formula rather than reopening the recursive product
 definition. The cubic formulas provide the next input for classifying product
 order dividing three under the transported first-quadrant constraints.
 
+Product order dividing three is now classified as well. The cubic beam
+equation factors into:
+
+```text
+S = 0
+or
+S^2 = 3*C^2
+```
+
+The first branch gives the neutral kernel. In the second branch the
+unit-square equation gives `C^2 = 1/4` and `S^2 = 3/4`; nonnegativity gives
+`C = 1/2`, and the cubic core equation then contradicts identity. Therefore
+orders dividing one, two, or three all force semantic identity. This concerns
+order dividing the displayed integer, not an assertion of exact order.
+
 The next structural boundary is source-level `Vec.star` and `KernelFamily`.
 Both require signed arithmetic. They should wait for a signed DkReal layer
 rather than forcing subtraction into `DkNNRealQ`. Until then, further work can
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
index f388c641..008ebf49 100644
--- a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
@@ -212,6 +212,25 @@ Archive
 5. 検証:
    - `lake build DkMath.Analysis.DkReal.SemanticCF2D` 成功 (8273 jobs)。
 
+### 2026/06/22 05:02 JST (Order dividing three classification)
+
+1. 実施:
+   - `semanticKernelFiniteOrder_three_iff_identity` を追加した。
+   - order dividing three を semantic core coordinate one とも同値にした。
+2. 証明:
+   - 三乗 beam 方程式を `S * (3*C^2 - S^2) = 0` と因数分解した。
+   - `S = 0` 分岐は unit-square と core 非負性から `C = 1`。
+   - 他方は `C^2 = 1/4`, `S^2 = 3/4`, `C = 1/2` となり、三乗 core
+     方程式と矛盾する。
+3. 結論:
+   - transported first-quadrant kernel では、order dividing one, two,
+     three のいずれも identity に潰れる。
+   - exact order three の非自明 kernel は存在しない。
+4. 境界:
+   - 平方根、角度、連続性、signed source は使用していない。
+5. 検証:
+   - `lake build DkMath.Analysis.DkReal.SemanticCF2D` 成功 (8273 jobs)。
+
 ### 2026/06/22 04:51 JST (Polynomial coordinates for powers two and three)
 
 1. 方針:
````
`````
