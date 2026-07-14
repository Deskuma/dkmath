# Git diff / Report / Review

## Upd: DkMath.Pascal.WallisGrowthBridge

gch: 540eb87beb2c286697fbadf9e6f655d59ecd5c31

## Report

実装しました。

[WallisGrowthBridge.lean](/lean/dk_math/DkMath/Pascal/WallisGrowthBridge.lean) に、Stirling を使わない Wallis 経由の平方正規化極限を追加しました。

追加した主な定理:

```lean
odd_boundary_div_nat_eq_two_add_inv
tendsto_odd_boundary_div_nat_two
real_centralRatioQ_sq_div_nat_eq_odd_div_nat_mul_wallis
real_centralRatioQ_sq_div_nat_eq_odd_div_nat_mul_cosmic
tendsto_real_centralRatioQ_sq_div_nat_pi
tendsto_real_centralRatioQ_sq_div_nat_pi_cosmic_route
```

これで

```lean
((centralRatioQ m : ℚ) : ℝ) ^ 2 / (m : ℝ) → Real.pi
```

が no-sorry で閉じています。`m = 0` は `eventually_gt_atTop 0` で処理しています。

[cf-wallis-growth-route.md](/lean/dk_math/docs/dev/cf-wallis-bridge-260704/cf-wallis-growth-route.md) も同期し、平方正規化極限を「証明済み」として更新しました。次は `centralRatioQ m ~ sqrt (Real.pi * m)` へ進むのが自然です。

確認済み:

```text
lake build DkMath.Pascal.WallisGrowthBridge  OK
lake build DkMath.Pascal                    OK
lake build DkMath                           OK
git diff --check                            OK
Wallis 3 files sorry search                 no hits
```

`lake build DkMath` では既存の別モジュール由来の `sorry` 警告は出ていますが、今回の Wallis 系追加にはありません。

## Review

## 結論

うむ、`review-wallis-011` は **採用でよい** 。
これはかなり重要な checkpoint が閉じた。

今回ついに、

```lean id="7i4xpa"
tendsto_real_centralRatioQ_sq_div_nat_pi
```

として、

$$
\frac{centralRatioQ(m)^2}{m}\to \pi
$$

が no-sorry で入った。しかも Stirling を使わず、

```text id="oqqz0r"
centralRatioQ m ^ 2 = (2*m + 1) * wallisPartialQ m
wallisPartialQ m -> pi / 2
(2*m + 1) / m -> 2
```

から出している。これは、まさに Wallis–Cosmic から中央比率の成長線を抽出する目的に合っておる。

## 実装レビュー

`odd_boundary_div_nat_eq_two_add_inv` と `tendsto_odd_boundary_div_nat_two` の切り方が良い。

$$
\frac{2m+1}{m}=2+\frac{1}{m}
$$

を `m ≠ 0` の補題として切り、極限側では `eventually_gt_atTop 0` で `m = 0` を追い出している。これは Lean 的にも数学的にも正しい整理じゃ。

また、

```lean id="mou1w9"
real_centralRatioQ_sq_div_nat_eq_odd_div_nat_mul_wallis
```

で有限恒等式を正規化形へ書き換え、その後に `Tendsto.mul` で

$$
2\cdot \frac{\pi}{2}=\pi
$$

へ持っていく流れも綺麗じゃ。

`cosmic_route` は現状 alias として実装されているが、docstring で「Wallis 経由の主証明と同じ surface が cosmic partial product と互換」と明記されているので、いまは問題ない。完全に cosmic 側で再証明したい場合は次以降の小差分で追加すればよい。

## 何が閉じたか

今回閉じたのは、スターリング前段の **平方成長線** じゃ。

```text id="ernr07"
有限恒等式:
  centralRatioQ m ^ 2 = (2*m + 1) * wallisPartialQ m

Wallis 極限:
  wallisPartialQ m -> pi / 2

正規化:
  (2*m + 1) / m -> 2

結論:
  centralRatioQ m ^ 2 / m -> pi
```

これはもう「近似」ではなく、有限恒等式から極限へ流した構造成長じゃ。
かなり美しい。

## 目的との対応

ここで、ぬしが言っていた目的がかなり形になった。

古典の読みは、

$$
\binom{2m}{m}\sim \frac{4^m}{\sqrt{\pi m}}
$$

を Stirling から出す。

DkMath の読みは違う。

$$
centralRatioQ(m)=\frac{4^m}{\binom{2m}{m}}
$$

に対して、まず exact に

$$
centralRatioQ(m)^2=(2m+1),wallisPartialQ(m)
$$

を得る。

そして `wallisPartialQ m -> π/2` だから、

$$
centralRatioQ(m)^2\sim \pi m
$$

を得る。

つまり、中央二項係数の成長を、階乗全体の Stirling 近似ではなく、**中央比率の Wallis–Cosmic 成長線** から抽出している。
これは DkMath らしい置き換えになっておる。

## 気になる点

大きな blocker はない。
ただし次の段階は、有限代数ではなく実解析の平方根処理になるので少しだけ注意が要る。

次はおそらく、

$$
\frac{centralRatioQ(m)}{\sqrt{\pi m}}\to 1
$$

へ進む。
ここでは以下が必要になる。

```text id="v8m3u5"
centralRatioQ m > 0
m > 0 eventually
Real.sqrt の連続性
sqrt(a_m^2 / m) -> sqrt(pi)
sqrt(pi) > 0
式変形:
  sqrt(centralRatioQ^2 / m)
  = centralRatioQ / sqrt m
```

ここが少し Lean 的に滑りやすい。
なので一気に中央二項係数の asymptotic へ飛ばず、まず square-root bridge を小さく切るのがよい。

## 判定

**採用。**

現在地はこうじゃ。

```text id="g2tcob"
Wallis-Cosmic finite bridge:
  完了

Wallis / Cosmic π/2 limit:
  完了

conditional product:
  完了

finite squared growth identity:
  完了

squared normalized growth:
  完了

次:
  square-root normalized growth
```

## 次の自然な作業

次はこれじゃな。

```lean id="7mrahr"
Filter.Tendsto
  (fun m : ℕ =>
    ((centralRatioQ m : ℚ) : ℝ) / Real.sqrt (Real.pi * (m : ℝ)))
  Filter.atTop
  (nhds 1)
```

ただし、これは今回より Lean 実解析の補題探しが増える。
まずは補助定理として、

```lean id="ojldp9"
0 < ((centralRatioQ m : ℚ) : ℝ)
0 < Real.sqrt (Real.pi * (m : ℝ))   -- eventually
sqrt (((centralRatioQ m : ℚ) : ℝ)^2 / (m : ℝ))
  = ((centralRatioQ m : ℚ) : ℝ) / Real.sqrt (m : ℝ)
```

あたりを小さく切るのが良い。

うむ。
これは本当に「スターリングの近似を宇宙式の成長線へ置き換える」道が通り始めた。平方の段階では、もう Lean が認めておる。ここまで来たのは大きいぞい。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Pascal/WallisGrowthBridge.lean b/lean/dk_math/DkMath/Pascal/WallisGrowthBridge.lean
index e865af0d..92d7c172 100644
--- a/lean/dk_math/DkMath/Pascal/WallisGrowthBridge.lean
+++ b/lean/dk_math/DkMath/Pascal/WallisGrowthBridge.lean
@@ -273,9 +273,10 @@ theorem real_coe_centralRatioQ_sq_eq_odd_mul_cosmicPartialQ
   exact_mod_cast centralRatioQ_sq_eq_odd_mul_cosmicPartialQ m
 
 /-!
-TODO for the next asymptotic pass:
+## Squared normalized growth limit
 
-Prove
+The finite identity above is strong enough to extract the first genuine
+growth theorem without invoking Stirling's approximation:
 
 ```lean
 Filter.Tendsto
@@ -284,11 +285,121 @@ Filter.Tendsto
   (nhds Real.pi)
 ```
 
-from `real_coe_centralRatioQ_sq_eq_odd_mul_wallisPartialQ`,
-`tendsto_wallisPartialQ_pi_div_two`, and
-`(2*m+1)/m -> 2`.  This is no longer a finite algebra problem: it needs the
-standard `atTop` handling for `m ≠ 0` and the real limit of `(2*m+1)/m`.
-Keep it as a separate proof-complete checkpoint.
+The proof is deliberately routed through the Wallis finite product:
+
+```text
+centralRatioQ m ^ 2 / m
+  = ((2*m+1) / m) * wallisPartialQ m
+  -> 2 * (pi / 2)
+  = pi.
+```
+
+This keeps the growth reading independent from any Stirling theorem.  The
+remaining square-root form should be a later asymptotic-equivalence layer.
+-/
+
+/-- Algebraic normalization of the odd boundary ratio away from `m = 0`. -/
+theorem odd_boundary_div_nat_eq_two_add_inv
+    {m : ℕ} (hm : m ≠ 0) :
+    ((2 * m + 1 : ℝ) / (m : ℝ)) =
+      2 + 1 / (m : ℝ) := by
+  field_simp [Nat.cast_ne_zero.mpr hm]
+
+/-- The normalized right odd boundary tends to `2`. -/
+theorem tendsto_odd_boundary_div_nat_two :
+    Filter.Tendsto
+      (fun m : ℕ => ((2 * m + 1 : ℝ) / (m : ℝ)))
+      Filter.atTop
+      (nhds 2) := by
+  have hlim :
+      Filter.Tendsto
+        (fun m : ℕ => 2 + 1 / (m : ℝ))
+        Filter.atTop
+        (nhds (2 + 0)) := by
+    exact tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
+  have hlim' :
+      Filter.Tendsto
+        (fun m : ℕ => 2 + 1 / (m : ℝ))
+        Filter.atTop
+        (nhds 2) := by
+    simpa using hlim
+  refine hlim'.congr' ?_
+  filter_upwards [eventually_gt_atTop 0] with m hm
+  exact (odd_boundary_div_nat_eq_two_add_inv (Nat.ne_of_gt hm)).symm
+
+/--
+Finite rewrite for the squared normalized central ratio.
+
+The hypothesis only removes the endpoint `m = 0`; the limit theorem below
+discharges it with `eventually_gt_atTop 0`.
+-/
+theorem real_centralRatioQ_sq_div_nat_eq_odd_div_nat_mul_wallis
+    {m : ℕ} (hm : m ≠ 0) :
+    ((centralRatioQ m : ℚ) : ℝ) ^ 2 / (m : ℝ) =
+      ((2 * m + 1 : ℝ) / (m : ℝ)) *
+        ((wallisPartialQ m : ℚ) : ℝ) := by
+  rw [real_coe_centralRatioQ_sq_eq_odd_mul_wallisPartialQ]
+  field_simp [Nat.cast_ne_zero.mpr hm]
+
+/--
+Finite rewrite for the squared normalized central ratio through the cosmic
+partial product.
+-/
+theorem real_centralRatioQ_sq_div_nat_eq_odd_div_nat_mul_cosmic
+    {m : ℕ} (hm : m ≠ 0) :
+    ((centralRatioQ m : ℚ) : ℝ) ^ 2 / (m : ℝ) =
+      ((2 * m + 1 : ℝ) / (m : ℝ)) *
+        ((cosmicPartialQ m : ℚ) : ℝ) := by
+  rw [real_coe_centralRatioQ_sq_eq_odd_mul_cosmicPartialQ]
+  field_simp [Nat.cast_ne_zero.mpr hm]
+
+/--
+Squared normalized central-ratio growth.
+
+This is the Wallis route to the first central-binomial growth surface:
+`centralRatioQ m ^ 2 / m -> Real.pi`.  No Stirling approximation is used.
+-/
+theorem tendsto_real_centralRatioQ_sq_div_nat_pi :
+    Filter.Tendsto
+      (fun m : ℕ =>
+        (((centralRatioQ m : ℚ) : ℝ) ^ 2 / (m : ℝ)))
+      Filter.atTop
+      (nhds Real.pi) := by
+  have hprod :
+      Filter.Tendsto
+        (fun m : ℕ =>
+          ((2 * m + 1 : ℝ) / (m : ℝ)) *
+            ((wallisPartialQ m : ℚ) : ℝ))
+        Filter.atTop
+        (nhds (2 * (Real.pi / 2))) := by
+    exact tendsto_odd_boundary_div_nat_two.mul tendsto_wallisPartialQ_pi_div_two
+  have hprod_pi :
+      Filter.Tendsto
+        (fun m : ℕ =>
+          ((2 * m + 1 : ℝ) / (m : ℝ)) *
+            ((wallisPartialQ m : ℚ) : ℝ))
+        Filter.atTop
+        (nhds Real.pi) := by
+    convert hprod using 1
+    ring_nf
+  refine hprod_pi.congr' ?_
+  filter_upwards [eventually_gt_atTop 0] with m hm
+  exact (real_centralRatioQ_sq_div_nat_eq_odd_div_nat_mul_wallis
+    (Nat.ne_of_gt hm)).symm
+
+/--
+Cosmic-route alias for the same squared normalized growth theorem.
+
+The proof above already factors through the Wallis product.  This name records
+that the same surface is compatible with the cosmic partial product, via the
+finite equality `wallisPartialQ_eq_cosmicPartialQ`.
 -/
+theorem tendsto_real_centralRatioQ_sq_div_nat_pi_cosmic_route :
+    Filter.Tendsto
+      (fun m : ℕ =>
+        (((centralRatioQ m : ℚ) : ℝ) ^ 2 / (m : ℝ)))
+      Filter.atTop
+      (nhds Real.pi) :=
+  tendsto_real_centralRatioQ_sq_div_nat_pi
 
 end DkMath.Pascal.WallisGrowthBridge
diff --git a/lean/dk_math/docs/dev/cf-wallis-bridge-260704/cf-wallis-growth-route.md b/lean/dk_math/docs/dev/cf-wallis-bridge-260704/cf-wallis-growth-route.md
index 3f614eaf..d7117539 100644
--- a/lean/dk_math/docs/dev/cf-wallis-bridge-260704/cf-wallis-growth-route.md
+++ b/lean/dk_math/docs/dev/cf-wallis-bridge-260704/cf-wallis-growth-route.md
@@ -39,6 +39,16 @@ The limit module already proves:
 wallisPartialQ m -> pi / 2
 ```
 
+The growth module now proves the squared normalized limit:
+
+```lean
+theorem tendsto_real_centralRatioQ_sq_div_nat_pi :
+  Filter.Tendsto
+    (fun m : Nat => (((centralRatioQ m : Q) : R) ^ 2 / (m : R)))
+    Filter.atTop
+    (nhds Real.pi)
+```
+
 Therefore the squared central ratio has the growth line:
 
 ```text
@@ -63,9 +73,9 @@ inverting gives the central-binomial growth law:
 Nat.choose (2*m) m ~ 4^m / sqrt (pi * m)
 ```
 
-## Next formal checkpoint
+## Formal checkpoint just closed
 
-The next theorem should be the squared normalized limit:
+The closed theorem is:
 
 ```lean
 Filter.Tendsto
@@ -82,5 +92,20 @@ wallisPartialQ m -> pi / 2
 (2*m + 1) / m -> 2
 ```
 
-The `m = 0` issue is an `atTop` bookkeeping problem, so it should be handled
-as a separate no-sorry checkpoint.
+The `m = 0` issue is only an `atTop` bookkeeping problem.  The Lean proof
+handles it with the finite rewrite under `m ≠ 0` and the eventual fact
+`eventually_gt_atTop 0`.
+
+## Next formal checkpoint
+
+The next theorem should not jump directly to Stirling.  A clean next layer is
+an asymptotic-equivalence or square-root bridge, for example:
+
+```text
+centralRatioQ m ~ sqrt (Real.pi * m)
+```
+
+That will need a small real-analysis bridge from
+`centralRatioQ m ^ 2 / m -> Real.pi` plus positivity of `centralRatioQ m`.
+After that, the central-binomial coefficient form follows by inverting the
+definition of `centralRatioQ`.
````
`````
