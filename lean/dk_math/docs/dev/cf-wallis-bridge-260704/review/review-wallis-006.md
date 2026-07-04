# Git diff / Report / Review

## Upd: DkMath.Pascal.WallisLimitBridge

gch: 5f5f4a67c1a927dd70ce89ec2c92d602e1f0f851

## Report

実装しました。

[WallisLimitBridge.lean](/lean/dk_math/DkMath/Pascal/WallisLimitBridge.lean:20) に、3つの有限実数列が pointwise に等しいことを明記し、実数キャスト helper を追加しました。

追加 theorem:

- `real_coe_wallisPartialQ_eq_cosmicPartialQ`
- `real_coe_centralRatioQ_mul_mirror_eq_wallisPartialQ`
- `real_coe_centralRatioQ_mul_mirror_eq_cosmicPartialQ`
- `tendsto_centralRatioQ_mul_mirror_pi_div_two`
- `tendsto_centralRatioQ_mul_mirror_via_wallis_pi_div_two`
- `dkTendsto_centralRatioQ_mul_mirror_pi_div_two`

主 route は cosmic 側:

```lean
centralRatioQ * mirror = cosmicPartialQ
cosmicPartialQ -> Real.pi / 2
```

補助 route として Wallis 側:

```lean
centralRatioQ * mirror = wallisPartialQ
wallisPartialQ -> Real.pi / 2
```

も閉じています。

Optional stretch として、短い note [cf-wallis-final-chain.md](/lean/dk_math/docs/dev/cf-wallis-bridge-260704/cf-wallis-final-chain.md:1) も追加しました。

確認済み:

```sh
lake build DkMath.Pascal.WallisCosmicPetalBridge
lake build DkMath.Pascal.WallisLimitBridge
lake build DkMath.Pascal
lake build DkMath
git diff --check
```

すべて成功です。

## Review

## 結論

うむ、 **閉じた** と言ってよいぞい。
少なくとも今回狙っていた **Wallis–Cosmic Petal Bridge の有限等式列から \(\pi/2\) 極限まで** は、Lean 上で一本通った。

今回の差分で、3 つの有限実数列が pointwise に等しいことが明記され、

```lean
((wallisPartialQ m : ℚ) : ℝ)
((cosmicPartialQ m : ℚ) : ℝ)
(((centralRatioQ m * mirrorOddRatioPartialQ m : ℚ) : ℝ))
```

さらに、それらが Mathlib の Wallis 定理を通じて `Real.pi / 2` に収束するところまで実装されておる。報告でも `tendsto_centralRatioQ_mul_mirror_pi_div_two`、`tendsto_centralRatioQ_mul_mirror_via_wallis_pi_div_two`、`dkTendsto_centralRatioQ_mul_mirror_pi_div_two` が追加され、build も `DkMath` まで通っている。

## 何が閉じたか

閉じた主鎖はこれじゃ。

$$
\left(\frac{2^{2m}}{\binom{2m}{m}}\right)M_m = W_m = C_m
\to
\frac{\pi}{2}
$$

DkMath の名前で言えば、

```text
centralRatioQ m * mirrorOddRatioPartialQ m
  = wallisPartialQ m
  = cosmicPartialQ m
  -> Real.pi / 2
```

じゃな。

今回の `cf-wallis-final-chain.md` でも、この最終鎖が短く整理されておる。有限モジュールで `ℚ` 上の等式を証明し、極限モジュールで `ℝ` にキャストして Mathlib の Wallis theorem を再利用する、という構成になっている。

## 実装レビュー

今回の追加 helper はよい。

```lean
real_coe_wallisPartialQ_eq_cosmicPartialQ
real_coe_centralRatioQ_mul_mirror_eq_wallisPartialQ
real_coe_centralRatioQ_mul_mirror_eq_cosmicPartialQ
```

この 3 本が入ったことで、以後の極限証明が `exact_mod_cast` の細工に埋もれず、構造そのものを読めるようになった。これは良い API 化じゃ。

また、主 route を cosmic 側にしたのも正しい。

```lean
centralRatioQ * mirror = cosmicPartialQ
cosmicPartialQ -> Real.pi / 2
```

一方で、補助 route として Wallis 側も残した。

```lean
centralRatioQ * mirror = wallisPartialQ
wallisPartialQ -> Real.pi / 2
```

これは重複ではあるが、数学的な説明経路として価値がある。証明ノート・古典 Wallis・宇宙式 Petal の三方向から読めるからじゃ。

## 判定

**採用。閉鎖判定。**

ただし、閉じた範囲を正確に言うならこうじゃ。

```text
閉じた:
  finite Wallis product
  finite cosmic gap product
  central binomial ratio × mirror product
  pointwise equality over ℝ
  convergence to Real.pi / 2
  DkMath limit alias

まだ別山:
  infinite product API としての HasProd / tsum / Multipliable 表現
  Wallis 積を宇宙式 Gap の無限積そのものとして扱う専用 theorem
```

つまり、 **部分積列の極限としては完全に閉じた** 。
もし「無限積オブジェクト」として

$$
\prod_{k=0}^{\infty}\left(1+\frac{1}{N_k}\right)=\frac{\pi}{2}
$$

を Lean の `HasProd` 系で表したいなら、それは次の別登山じゃ。だが今回の目標、すなわち partial product の `Tendsto` は閉じておる。

## 小さな気づき

`WallisLimitBridge.lean` のモジュールドキュメントで、3 つの列が pointwise equal だと明記したのはとても良い。これは未来の自分への道標になる。
あとで誰かが見ても、

```text
finite algebraic equality
real coercion
Wallis theorem
π/2 limit
```

の流れを見失わぬ。

ひとつだけ軽い注意を置くなら、`DkMath.Pascal.lean` が `WallisLimitBridge` まで import しているので、`DkMath.Pascal` は今後 `Real.pi` / topology / filter 系まで含む入口になる。これは公開入口としては問題ないが、もし将来「軽量 Pascal finite only」が欲しくなったら、別入口を切る余地はある。今は blocker ではない。

## まとめ

うむ、これは一山登頂じゃ。

Wallis 積は、DkMath では

$$
\prod_{k=0}^{m-1}\left(1+\frac{1}{(2k+1)(2k+3)}\right)
$$

という宇宙式 Gap 比率の有限蓄積として読める。
そしてその蓄積が

$$
\frac{\pi}{2}
$$

へ向かうところまで Lean が認めた。

これは美しい。
有限の Petal が積み重なり、極限で円の気配、つまり \(\pi\) が顔を出したのじゃ。賢狼としても、これは素直に「閉じた」と頷ける出来じゃよ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Pascal/WallisLimitBridge.lean b/lean/dk_math/DkMath/Pascal/WallisLimitBridge.lean
index 232b04d8..f77d5e9c 100644
--- a/lean/dk_math/DkMath/Pascal/WallisLimitBridge.lean
+++ b/lean/dk_math/DkMath/Pascal/WallisLimitBridge.lean
@@ -16,6 +16,14 @@ import DkMath.Pascal.WallisCosmicPetalBridge
 This module is the limit-facing layer for the finite Wallis-Cosmic Petal
 bridge.  The finite algebraic API remains in
 `DkMath.Pascal.WallisCosmicPetalBridge`.
+
+The following three real sequences are pointwise equal:
+
+* `fun m => ((wallisPartialQ m : ℚ) : ℝ)`;
+* `fun m => ((cosmicPartialQ m : ℚ) : ℝ)`;
+* `fun m => (((centralRatioQ m * mirrorOddRatioPartialQ m : ℚ) : ℝ))`.
+
+Mathlib's Wallis theorem then sends each of them to `Real.pi / 2`.
 -/
 
 namespace DkMath.Pascal.WallisLimitBridge
@@ -36,6 +44,30 @@ theorem real_coe_wallisPartialQ_eq_Wallis_W (m : ℕ) :
     norm_num
     field_simp
 
+/-- The finite Wallis and cosmic partial products are pointwise equal over `ℝ`. -/
+theorem real_coe_wallisPartialQ_eq_cosmicPartialQ (m : ℕ) :
+    ((wallisPartialQ m : ℚ) : ℝ) =
+      ((cosmicPartialQ m : ℚ) : ℝ) := by
+  exact_mod_cast wallisPartialQ_eq_cosmicPartialQ m
+
+/--
+The proof-note central-ratio expression is pointwise equal to the finite
+Wallis product over `ℝ`.
+-/
+theorem real_coe_centralRatioQ_mul_mirror_eq_wallisPartialQ (m : ℕ) :
+    (((centralRatioQ m * mirrorOddRatioPartialQ m : ℚ) : ℝ)) =
+      ((wallisPartialQ m : ℚ) : ℝ) := by
+  exact_mod_cast centralRatioQ_mul_mirror_eq_wallisPartialQ m
+
+/--
+The proof-note central-ratio expression is pointwise equal to the finite
+cosmic gap product over `ℝ`.
+-/
+theorem real_coe_centralRatioQ_mul_mirror_eq_cosmicPartialQ (m : ℕ) :
+    (((centralRatioQ m * mirrorOddRatioPartialQ m : ℚ) : ℝ)) =
+      ((cosmicPartialQ m : ℚ) : ℝ) := by
+  exact_mod_cast centralRatioQ_mul_mirror_eq_cosmicPartialQ m
+
 /--
 The real coercion of the finite rational Wallis partial products tends to
 `Real.pi / 2`, by Mathlib's Wallis product theorem.
@@ -64,9 +96,36 @@ theorem tendsto_cosmicPartialQ_pi_div_two :
       Filter.atTop
       (nhds (Real.pi / 2)) := by
   exact tendsto_wallisPartialQ_pi_div_two.congr' <|
-    Eventually.of_forall fun m => by
-      change ((wallisPartialQ m : ℚ) : ℝ) = ((cosmicPartialQ m : ℚ) : ℝ)
-      exact_mod_cast wallisPartialQ_eq_cosmicPartialQ m
+    Eventually.of_forall real_coe_wallisPartialQ_eq_cosmicPartialQ
+
+/--
+The proof-note expression
+`centralRatioQ m * mirrorOddRatioPartialQ m` tends to `Real.pi / 2`.
+
+This is the main public central-ratio route: pointwise, it is the finite
+cosmic gap product, and the cosmic partial products share the Wallis limit.
+-/
+theorem tendsto_centralRatioQ_mul_mirror_pi_div_two :
+    Filter.Tendsto
+      (fun m : ℕ => (((centralRatioQ m * mirrorOddRatioPartialQ m : ℚ) : ℝ)))
+      Filter.atTop
+      (nhds (Real.pi / 2)) := by
+  exact tendsto_cosmicPartialQ_pi_div_two.congr' <|
+    Eventually.of_forall fun m =>
+      (real_coe_centralRatioQ_mul_mirror_eq_cosmicPartialQ m).symm
+
+/--
+The same proof-note expression tends to `Real.pi / 2`, routed through the
+finite Wallis product stage instead of the cosmic gap product.
+-/
+theorem tendsto_centralRatioQ_mul_mirror_via_wallis_pi_div_two :
+    Filter.Tendsto
+      (fun m : ℕ => (((centralRatioQ m * mirrorOddRatioPartialQ m : ℚ) : ℝ)))
+      Filter.atTop
+      (nhds (Real.pi / 2)) := by
+  exact tendsto_wallisPartialQ_pi_div_two.congr' <|
+    Eventually.of_forall fun m =>
+      (real_coe_centralRatioQ_mul_mirror_eq_wallisPartialQ m).symm
 
 /--
 DkMath-named alias for the Wallis partial product convergence.
@@ -86,4 +145,13 @@ theorem dkTendsto_cosmicPartialQ_pi_div_two :
       (Real.pi / 2) :=
   tendsto_cosmicPartialQ_pi_div_two
 
+/--
+DkMath-named alias for convergence of the proof-note central-ratio expression.
+-/
+theorem dkTendsto_centralRatioQ_mul_mirror_pi_div_two :
+    DkMath.Analysis.DkTendstoAtTop
+      (fun m : ℕ => (((centralRatioQ m * mirrorOddRatioPartialQ m : ℚ) : ℝ)))
+      (Real.pi / 2) :=
+  tendsto_centralRatioQ_mul_mirror_pi_div_two
+
 end DkMath.Pascal.WallisLimitBridge
diff --git a/lean/dk_math/docs/dev/cf-wallis-bridge-260704/cf-wallis-final-chain.md b/lean/dk_math/docs/dev/cf-wallis-bridge-260704/cf-wallis-final-chain.md
new file mode 100644
index 00000000..e0a875d5
--- /dev/null
+++ b/lean/dk_math/docs/dev/cf-wallis-bridge-260704/cf-wallis-final-chain.md
@@ -0,0 +1,25 @@
+# Wallis-Cosmic Final Chain
+
+The formal bridge now has three pointwise-equal finite real sequences:
+
+```text
+((centralRatioQ m * mirrorOddRatioPartialQ m : Q) : R)
+  = ((wallisPartialQ m : Q) : R)
+  = ((cosmicPartialQ m : Q) : R)
+```
+
+The finite module proves the algebraic equalities over `Q`.
+The limit module coerces them to `R` and reuses Mathlib's Wallis theorem:
+
+```text
+((wallisPartialQ m : Q) : R) -> Real.pi / 2
+```
+
+Therefore the proof-note expression also converges:
+
+```text
+central binomial ratio * mirror product
+  = finite Wallis product
+  = finite cosmic gap product
+  -> Real.pi / 2
+```
````
`````
