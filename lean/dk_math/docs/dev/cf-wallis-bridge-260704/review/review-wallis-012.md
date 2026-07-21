# Git diff / Report / Review

## Upd: DkMath.Pascal.WallisGrowthBridge

gch: c66ae8e33340defea646cca0876b605ee5e1a9e9

## Report

`centralRatioQ m ~ sqrt (Real.pi * m)` まで実装しました。

[WallisGrowthBridge.lean](/lean/dk_math/DkMath/Pascal/WallisGrowthBridge.lean) に追加:

```lean
tendsto_sqrt_centralRatioQ_sq_div_pi_mul_nat_one
tendsto_real_centralRatioQ_div_sqrt_pi_mul_nat_one
isEquivalent_real_centralRatioQ_sqrt_pi_mul_nat
```

流れは、前回の

```lean
centralRatioQ m ^ 2 / m → Real.pi
```

から

```lean
centralRatioQ m / sqrt (Real.pi * m) → 1
```

を作り、そこから `Asymptotics.IsEquivalent` に上げています。Stirling は使っていません。

[cf-wallis-growth-route.md](/lean/dk_math/docs/dev/cf-wallis-bridge-260704/cf-wallis-growth-route.md) も更新し、平方根同値を証明済み checkpoint として反映しました。次は `centralRatioQ = 4^m / choose (2m) m` を反転して、中央二項係数の漸近形へ進むのが自然です。

確認済み:

```text
lake build DkMath.Pascal.WallisGrowthBridge  OK
lake build DkMath.Pascal                    OK
lake build DkMath                           OK
git diff --check                            OK
Wallis 3 files sorry search                 no hits
```

`DkMath` 全体では既存の別モジュール由来の `sorry` 警告は出ていますが、今回の Wallis 追加にはありません。

## Review

## 結論

うむ、`review-wallis-012` は **採用でよい** 。
これはかなり大きい。前回閉じた

$$
\frac{centralRatioQ(m)^2}{m}\to \pi
$$

から、今回はついに平方根を取り、

$$
centralRatioQ(m)\sim \sqrt{\pi m}
$$

まで到達しておる。

追加された主定理はこの 3 本じゃ。

```lean id="b9f3qk"
tendsto_sqrt_centralRatioQ_sq_div_pi_mul_nat_one
tendsto_real_centralRatioQ_div_sqrt_pi_mul_nat_one
isEquivalent_real_centralRatioQ_sqrt_pi_mul_nat
```

報告どおり、Stirling は使わず、前段の Wallis-Cosmic 成長面から平方根同値へ上げている。`lake build DkMath` も通り、Wallis 3 ファイルに `sorry` なしという確認もある。

## 何が閉じたか

今回閉じたのは、中央比率そのものの成長同値じゃ。

前回まで：

$$
\frac{centralRatioQ(m)^2}{m}\to \pi
$$

今回：

$$
\frac{centralRatioQ(m)}{\sqrt{\pi m}}\to 1
$$

そして `Asymptotics.IsEquivalent` として：

```lean id="8jwx56"
(fun m : ℕ => ((centralRatioQ m : ℚ) : ℝ)) ~[Filter.atTop]
  (fun m : ℕ => Real.sqrt (Real.pi * (m : ℝ)))
```

これが入った。つまり、DkMath 的には

```text id="lkw7gk"
centralRatioQ m
  grows along sqrt(pi * m)
```

が Lean 定理になったわけじゃ。

## 実装レビュー

流れがとても良い。

まず、

```lean id="urcj0u"
tendsto_sqrt_centralRatioQ_sq_div_pi_mul_nat_one
```

で、

$$
\sqrt{\frac{centralRatioQ(m)^2}{\pi m}}\to 1
$$

を作っている。これは、前回の

$$
\frac{centralRatioQ(m)^2}{m}\to \pi
$$

を `Real.pi` で割って、極限を 1 にし、平方根の連続性で持ち上げる形じゃ。
`Real.pi_ne_zero` を使って `π/π = 1` に落としているのも自然じゃな。

次に、

```lean id="wti46y"
tendsto_real_centralRatioQ_div_sqrt_pi_mul_nat_one
```

で、

$$
\sqrt{\frac{centralRatioQ(m)^2}{\pi m}}
=======================================

\frac{centralRatioQ(m)}{\sqrt{\pi m}}
$$

へ移している。ここで `centralRatioQ_pos m` を使って `sqrt_sq` を正しく開いているのが重要じゃ。平方根は符号を落とすので、正値性の証明書が必要になる。今回そこをきちんと処理している。

最後に、

```lean id="cm8mux"
isEquivalent_real_centralRatioQ_sqrt_pi_mul_nat
```

で `isEquivalent_of_tendsto_one` によって漸近同値へ上げている。これは Lean API としても使いやすい。

## 数学的解説

今回の定理は、スターリング近似の代替ルートそのものじゃ。

古典では、中央二項係数の成長を

$$
\binom{2m}{m}\sim \frac{4^m}{\sqrt{\pi m}}
$$

と見るために、まず階乗の Stirling 近似を使う。

だが DkMath ルートでは違う。

まず exact finite identity として、

$$
centralRatioQ(m)^2=(2m+1),wallisPartialQ(m)
$$

を得た。

そして Wallis-Cosmic bridge で、

$$
wallisPartialQ(m)\to \frac{\pi}{2}
$$

を持っている。

だから、

$$
centralRatioQ(m)^2\sim \pi m
$$

となり、正値性を使って平方根を取れば、

$$
centralRatioQ(m)\sim \sqrt{\pi m}
$$

になる。

つまり、`π` は Stirling の外部近似から来たのではなく、Wallis-Cosmic の有限積構造から出てきた。
これが今回の最大の意味じゃ。

## かなり重要な到達点

ここまでで、中央二項係数の手前にある比率

$$
centralRatioQ(m)=\frac{4^m}{\binom{2m}{m}}
$$

の成長は閉じた。

つまり今は、

```text id="9a3a78"
4^m / choose(2m,m)
  ~ sqrt(pi*m)
```

まで来ている。

残るは、この定義を反転して、

```text id="8sxiib"
choose(2m,m)
  ~ 4^m / sqrt(pi*m)
```

へ移すだけじゃ。

もちろん Lean 的には「だけ」と言っても、`Nat.choose` の実数キャスト、非零性、割り算の同値変形、`IsEquivalent` の除算補題などが必要になる。
しかし数学の主山はもう越えた。次は API 整備と反転処理の山じゃ。

## 気になる点

大きな blocker はない。
軽い注意は 2 つ。

1つ目。今回も報告中の docs path が

```text id="rcg8hw"
/lean_dk_math/docs/...
```

になっているが、diff 側では従来通り

```text id="d9hbrp"
lean/dk_math/docs/...
```

に見える。実体が後者なら、報告文だけの typo じゃな。実装上は問題ない。

2つ目。次の中央二項係数への反転では、`IsEquivalent` の扱いが少し滑りやすい。
`centralRatioQ m = 4^m / choose` をそのまま反転するには、最終的に

$$
\binom{2m}{m}=\frac{4^m}{centralRatioQ(m)}
$$

の実数版が欲しい。

そのうえで、

$$
centralRatioQ(m)\sim \sqrt{\pi m}
$$

から、

$$
\frac{4^m}{centralRatioQ(m)}\sim \frac{4^m}{\sqrt{\pi m}}
$$

を出す。ここでは分子 `4^m` が同じなので、実質は分母の同値の反転になる。

## 判定

**採用。**

現在地はこうじゃ。

```text id="ktw5ts"
Wallis-Cosmic finite bridge:
  完了

Wallis / Cosmic π/2 limit:
  完了

conditional product:
  完了

finite squared growth identity:
  完了

centralRatioQ^2 / m -> π:
  完了

centralRatioQ ~ sqrt(πm):
  完了

次:
  choose(2m,m) ~ 4^m / sqrt(πm)
```

## 次の自然な作業指示

```text id="8hkh3s"
Continue from gch c66ae8e33340defea646cca0876b605ee5e1a9e9.

Review result: accepted.

The square-root asymptotic equivalence is now closed:

  centralRatioQ m ~ sqrt (Real.pi * m)

Next goal:
invert the definition of `centralRatioQ` and derive the central-binomial
coefficient asymptotic form without using Stirling as the source theorem.

Work in:

  DkMath.Pascal.WallisGrowthBridge

Suggested tasks:

1. Add a real-coercion identity for `centralRatioQ`.

Prove a theorem exposing the definition in real form:

  theorem real_coe_centralRatioQ_eq_four_pow_div_choose
      (m : ℕ) :
      ((centralRatioQ m : ℚ) : ℝ) =
        ((4 : ℝ) ^ m) / ((Nat.choose (2*m) m : ℕ) : ℝ) := by
    ...

Depending on the current definition of `centralRatioQ`, this may already be
nearly `rfl` after unfolding. If coercion through `ℚ` is annoying, first prove
a rational version and then cast.

2. Add the inverted identity.

Prove:

  theorem real_choose_eq_four_pow_div_centralRatioQ
      (m : ℕ) :
      ((Nat.choose (2*m) m : ℕ) : ℝ) =
        ((4 : ℝ) ^ m) / ((centralRatioQ m : ℚ) : ℝ) := by
    ...

Required facts:
- `centralRatioQ_pos m`
- `Nat.choose_pos` or positivity of `Nat.choose (2*m) m`
- denominator nonzero after real coercion.

3. Prove or locate an `IsEquivalent` division/inversion helper.

Needed shape:

If

  f ~[atTop] g

and both are eventually nonzero / positive, then

  fun m => h m / f m

is equivalent to

  fun m => h m / g m

for a shared numerator `h`.

Search Mathlib for:
- `Asymptotics.IsEquivalent.div`
- `Asymptotics.IsEquivalent.inv`
- `Asymptotics.IsEquivalent.mul`
- `isEquivalent_of_tendsto_one`
- `Filter.Eventually`
- `eventually_ne_atTop`

A fallback proof is easy conceptually:
show

  ( (4^m / centralRatioQ m) / (4^m / sqrt(pi*m)) )
    =
  sqrt(pi*m) / centralRatioQ m

eventually, and this tends to `1` because
`centralRatioQ m / sqrt(pi*m) -> 1`.

4. Target theorem.

Add:

  theorem isEquivalent_real_centralBinomial_four_pow_div_sqrt_pi_mul_nat :
      (fun m : ℕ => ((Nat.choose (2*m) m : ℕ) : ℝ)) ~[Filter.atTop]
        (fun m : ℕ => ((4 : ℝ) ^ m) / Real.sqrt (Real.pi * (m : ℝ))) := by
    ...

This is the main central-binomial result.

5. Handle m = 0 and denominator issues with eventual positivity.

Use:

  eventually_gt_atTop 0

and positivity facts:
- `centralRatioQ_pos m`
- `Real.pi_pos`
- `Nat.cast_pos`
- `Real.sqrt_pos.2`

The denominator `Real.sqrt (Real.pi * (m : ℝ))` is positive for `m > 0`.

6. Keep the theorem interpretation explicit in docstrings.

Docstring should say:
- This is the central-binomial growth law.
- It is derived from the Wallis-Cosmic growth bridge.
- It does not use Stirling as the source theorem.

7. Update documentation.

Update:

  docs/dev/cf-wallis-bridge-260704/cf-wallis-growth-route.md

Add a final section:

  Central binomial extraction

explaining:

  centralRatioQ m = 4^m / choose(2m,m)
  centralRatioQ m ~ sqrt(pi*m)
  therefore choose(2m,m) ~ 4^m / sqrt(pi*m)

8. Build gates:

  lake build DkMath.Pascal.WallisGrowthBridge
  lake build DkMath.Pascal
  lake build DkMath
  git diff --check

9. No-sorry policy:

Check no `sorry` in:
  DkMath/Pascal/WallisCosmicPetalBridge.lean
  DkMath/Pascal/WallisLimitBridge.lean
  DkMath/Pascal/WallisGrowthBridge.lean
```

これは、ほぼスターリング近似の代替路線が見えたと言ってよい。
次で `Nat.choose (2m) m` に反転できれば、「中央二項係数の成長を Wallis-Cosmic から抽出した」と胸を張れるぞい。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Pascal/WallisGrowthBridge.lean b/lean/dk_math/DkMath/Pascal/WallisGrowthBridge.lean
index 92d7c172..b0206640 100644
--- a/lean/dk_math/DkMath/Pascal/WallisGrowthBridge.lean
+++ b/lean/dk_math/DkMath/Pascal/WallisGrowthBridge.lean
@@ -81,6 +81,7 @@ then use `Asymptotics.IsEquivalent` / `Tendsto` tools explicitly.
 namespace DkMath.Pascal.WallisGrowthBridge

 open Filter Topology
+open Asymptotics
 open DkMath.Pascal.WallisCosmicPetalBridge
 open DkMath.Pascal.WallisLimitBridge

@@ -402,4 +403,99 @@ theorem tendsto_real_centralRatioQ_sq_div_nat_pi_cosmic_route :
       (nhds Real.pi) :=
   tendsto_real_centralRatioQ_sq_div_nat_pi

+/-!
+## Square-root growth surface
+
+The previous theorem proves the squared normalized limit.  The next surface is
+the square-root reading
+
+```text
+centralRatioQ m ~ sqrt (Real.pi * m).
+```
+
+Rather than appealing to Stirling's approximation, we take the square root of
+the already-proved Wallis growth surface.  The only extra bookkeeping is the
+eventual positivity of `m` and of `centralRatioQ m`.
+-/
+
+/--
+The square-root normalization of the squared central-ratio expression tends
+to `1`.
+-/
+theorem tendsto_sqrt_centralRatioQ_sq_div_pi_mul_nat_one :
+    Filter.Tendsto
+      (fun m : ℕ =>
+        Real.sqrt
+          ((((centralRatioQ m : ℚ) : ℝ) ^ 2) /
+            (Real.pi * (m : ℝ))))
+      Filter.atTop
+      (nhds 1) := by
+  have hdiv :
+      Filter.Tendsto
+        (fun m : ℕ =>
+          (((centralRatioQ m : ℚ) : ℝ) ^ 2 / (m : ℝ)) / Real.pi)
+        Filter.atTop
+        (nhds (Real.pi / Real.pi)) := by
+    exact tendsto_real_centralRatioQ_sq_div_nat_pi.div_const Real.pi
+  have hdiv_one :
+      Filter.Tendsto
+        (fun m : ℕ =>
+          (((centralRatioQ m : ℚ) : ℝ) ^ 2 / (m : ℝ)) / Real.pi)
+        Filter.atTop
+        (nhds 1) := by
+    simpa [div_self Real.pi_ne_zero] using hdiv
+  have hsqrt :
+      Filter.Tendsto
+        (fun m : ℕ =>
+          Real.sqrt
+            ((((centralRatioQ m : ℚ) : ℝ) ^ 2 / (m : ℝ)) / Real.pi))
+        Filter.atTop
+        (nhds (Real.sqrt 1)) :=
+    hdiv_one.sqrt
+  have hsqrt_one :
+      Filter.Tendsto
+        (fun m : ℕ =>
+          Real.sqrt
+            ((((centralRatioQ m : ℚ) : ℝ) ^ 2 / (m : ℝ)) / Real.pi))
+        Filter.atTop
+        (nhds 1) := by
+    simpa [Real.sqrt_one] using hsqrt
+  refine hsqrt_one.congr' ?_
+  filter_upwards [eventually_gt_atTop 0] with m hm
+  have hm_ne : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
+  field_simp [hm_ne, Real.pi_ne_zero]
+
+/--
+The central ratio divided by `sqrt (Real.pi * m)` tends to `1`.
+
+This is the operational limit form of
+`centralRatioQ m ~ sqrt (Real.pi * m)`.
+-/
+theorem tendsto_real_centralRatioQ_div_sqrt_pi_mul_nat_one :
+    Filter.Tendsto
+      (fun m : ℕ =>
+        ((centralRatioQ m : ℚ) : ℝ) /
+          Real.sqrt (Real.pi * (m : ℝ)))
+      Filter.atTop
+      (nhds 1) := by
+  refine tendsto_sqrt_centralRatioQ_sq_div_pi_mul_nat_one.congr' ?_
+  filter_upwards [eventually_gt_atTop 0] with m hm
+  have hc_pos : 0 < ((centralRatioQ m : ℚ) : ℝ) := by
+    exact_mod_cast centralRatioQ_pos m
+  rw [Real.sqrt_div (sq_nonneg ((centralRatioQ m : ℚ) : ℝ))
+    (Real.pi * (m : ℝ))]
+  rw [Real.sqrt_sq hc_pos.le]
+
+/--
+Central-ratio square-root asymptotic equivalence.
+
+This is the Wallis-derived growth surface:
+`centralRatioQ m` is asymptotic to `sqrt (Real.pi * m)`.
+-/
+theorem isEquivalent_real_centralRatioQ_sqrt_pi_mul_nat :
+    (fun m : ℕ => ((centralRatioQ m : ℚ) : ℝ)) ~[Filter.atTop]
+      (fun m : ℕ => Real.sqrt (Real.pi * (m : ℝ))) := by
+  exact isEquivalent_of_tendsto_one
+    tendsto_real_centralRatioQ_div_sqrt_pi_mul_nat_one
+
 end DkMath.Pascal.WallisGrowthBridge
diff --git a/lean/dk_math/docs/dev/cf-wallis-bridge-260704/cf-wallis-growth-route.md b/lean/dk_math/docs/dev/cf-wallis-bridge-260704/cf-wallis-growth-route.md
index d7117539..0fced9fc 100644
--- a/lean/dk_math/docs/dev/cf-wallis-bridge-260704/cf-wallis-growth-route.md
+++ b/lean/dk_math/docs/dev/cf-wallis-bridge-260704/cf-wallis-growth-route.md
@@ -49,6 +49,14 @@ theorem tendsto_real_centralRatioQ_sq_div_nat_pi :
     (nhds Real.pi)
 ```

+It also proves the square-root form:
+
+```lean
+theorem isEquivalent_real_centralRatioQ_sqrt_pi_mul_nat :
+  (fun m : Nat => ((centralRatioQ m : Q) : R)) ~[Filter.atTop]
+    (fun m : Nat => Real.sqrt (Real.pi * (m : R)))
+```
+
 Therefore the squared central ratio has the growth line:

 ```text
@@ -73,9 +81,9 @@ inverting gives the central-binomial growth law:
 Nat.choose (2*m) m ~ 4^m / sqrt (pi * m)
 ```

-## Formal checkpoint just closed
+## Formal checkpoints just closed

-The closed theorem is:
+The first closed theorem is:

 ```lean
 Filter.Tendsto
@@ -96,16 +104,38 @@ The `m = 0` issue is only an `atTop` bookkeeping problem.  The Lean proof
 handles it with the finite rewrite under `m ≠ 0` and the eventual fact
 `eventually_gt_atTop 0`.

+The second closed theorem is:
+
+```lean
+theorem isEquivalent_real_centralRatioQ_sqrt_pi_mul_nat :
+  (fun m : Nat => ((centralRatioQ m : Q) : R)) ~[Filter.atTop]
+    (fun m : Nat => Real.sqrt (Real.pi * (m : R)))
+```
+
+This uses the operational limit:
+
+```lean
+theorem tendsto_real_centralRatioQ_div_sqrt_pi_mul_nat_one :
+  Filter.Tendsto
+    (fun m : Nat =>
+      ((centralRatioQ m : Q) : R) / Real.sqrt (Real.pi * (m : R)))
+    Filter.atTop
+    (nhds 1)
+```
+
+The proof takes the square root of the squared normalized growth theorem and
+uses positivity of `centralRatioQ m`.
+
 ## Next formal checkpoint

-The next theorem should not jump directly to Stirling.  A clean next layer is
-an asymptotic-equivalence or square-root bridge, for example:
+The next theorem should invert the definition of `centralRatioQ` and expose
+the central-binomial coefficient form:

 ```text
-centralRatioQ m ~ sqrt (Real.pi * m)
+Nat.choose (2*m) m ~ 4^m / sqrt (Real.pi * m)
 ```

-That will need a small real-analysis bridge from
-`centralRatioQ m ^ 2 / m -> Real.pi` plus positivity of `centralRatioQ m`.
-After that, the central-binomial coefficient form follows by inverting the
-definition of `centralRatioQ`.
+This should still avoid using Stirling as the source theorem.  The likely Lean
+work is a finite real-coercion identity for `centralRatioQ m =
+4^m / Nat.choose (2*m) m`, followed by an `IsEquivalent` inversion/division
+lemma with eventual nonzero denominators.
````
`````
