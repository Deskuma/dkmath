# Git diff / Report / Review

## Upd: DkMath.Pascal.WallisGrowthBridge

gch: 5b0d3e1507bce238e04d154142ae5fb26e671052

## Report

中央二項係数の漸近形まで進めました。

[WallisGrowthBridge.lean](/lean/dk_math/DkMath/Pascal/WallisGrowthBridge.lean) に追加:

```lean
nat_choose_two_mul_self_cast_eq_pow_four_div_centralRatioQ
real_nat_choose_two_mul_self_eq_pow_four_div_centralRatioQ
isEquivalent_real_centralBinomial_sqrt_pi_mul_nat
```

最終形はこれです。

```lean
(fun m : ℕ => ((Nat.choose (2 * m) m : ℕ) : ℝ)) ~[Filter.atTop]
  (fun m : ℕ => (4 : ℝ) ^ m / Real.sqrt (Real.pi * (m : ℝ)))
```

つまり、Wallis 経由で

```text
choose (2m) m ~ 4^m / sqrt(pi*m)
```

を no-sorry で固定しました。Stirling は使っていません。

[cf-wallis-growth-route.md](/lean/dk_math/docs/dev/cf-wallis-bridge-260704/cf-wallis-growth-route.md) も更新し、中央二項係数 checkpoint を証明済みとして反映しました。

確認済み:

```text
lake build DkMath.Pascal.WallisGrowthBridge  OK
lake build DkMath.Pascal                    OK
lake build DkMath                           OK
git diff --check                            OK
Wallis 3 files sorry search                 no hits
```

`DkMath` 全体では既存の別モジュール由来の `sorry` 警告は出ていますが、今回の Wallis/Pascal 追加にはありません。

## Review

## 結論

うむ、`review-wallis-013` は **採用でよい** 。
これは、かなり大きな節目じゃ。

今回ついに、中央二項係数そのものの漸近形

$$
\binom{2m}{m}\sim \frac{4^m}{\sqrt{\pi m}}
$$

まで、Wallis–Cosmic 経由で no-sorry 実装された。報告でも、`isEquivalent_real_centralBinomial_sqrt_pi_mul_nat` が追加され、`lake build DkMath` まで通り、Wallis 3 ファイルに `sorry` なしと確認されている。

## 何が閉じたか

今回閉じた流れはこうじゃ。

まず前回までに、

$$
centralRatioQ(m)\sim \sqrt{\pi m}
$$

を得ていた。

今回、定義の反転として、

$$
centralRatioQ(m)=\frac{4^m}{\binom{2m}{m}}
$$

を使い、

$$
\binom{2m}{m}=\frac{4^m}{centralRatioQ(m)}
$$

を Lean 側に固定した。

追加された有限反転定理は、

```lean id="hha3cy"
nat_choose_two_mul_self_cast_eq_pow_four_div_centralRatioQ
real_nat_choose_two_mul_self_eq_pow_four_div_centralRatioQ
```

そして最終的に、

```lean id="jrtggx"
isEquivalent_real_centralBinomial_sqrt_pi_mul_nat
```

として、

```lean id="vxzgzc"
(fun m : ℕ => ((Nat.choose (2 * m) m : ℕ) : ℝ)) ~[Filter.atTop]
  (fun m : ℕ => (4 : ℝ) ^ m / Real.sqrt (Real.pi * (m : ℝ)))
```

まで来た。

## 解説：これは何を置き換えたのか

古典的には、この定理は Stirling 近似から出すことが多い。

$$
n!\sim \sqrt{2\pi n}\left(\frac{n}{e}\right)^n
$$

これを \((2m)!/(m!)^2\) に代入して整理すると、

$$
\binom{2m}{m}\sim \frac{4^m}{\sqrt{\pi m}}
$$

が出る。

しかし今回の DkMath ルートは違う。
階乗全体の近似へ飛ばず、中央二項係数に固有の比率

$$
centralRatioQ(m)=\frac{4^m}{\binom{2m}{m}}
$$

を主語にした。

そして Wallis–Cosmic bridge から、

$$
centralRatioQ(m)^2=(2m+1)\,wallisPartialQ(m)
$$

を exact に得て、

$$
wallisPartialQ(m)\to \frac{\pi}{2}
$$

を使うことで、

$$
centralRatioQ(m)\sim \sqrt{\pi m}
$$

を得た。

最後にこれを反転して、

$$
\binom{2m}{m}\sim \frac{4^m}{\sqrt{\pi m}}
$$

へ戻したわけじゃ。

つまり、**スターリング近似で外側から押し込んだのではなく、Wallis–Cosmic の有限積構造から中央二項係数の成長線を抽出した**。
ここが最大の意味じゃな。

## 実装レビュー

実装はかなり綺麗じゃ。

有限反転定理で `Nat.choose_pos` を使い、`m ≤ 2*m` を `omega` で処理して、choose の非零性を確保している。そこから `field_simp` で `centralRatioQ` の定義を反転している流れは自然じゃ。

また、最終定理の証明も筋がよい。

```lean id="2c1v27"
hfinite :
  choose =ᶠ[atTop] 4^m / centralRatioQ m
```

を作り、

```lean id="wvvdmy"
hratio :
  4^m / centralRatioQ m ~ 4^m / sqrt(pi*m)
```

を `IsEquivalent.div IsEquivalent.refl isEquivalent_real_centralRatioQ_sqrt_pi_mul_nat` で出している。

つまり、分子 \(4^m\) は同じ、分母だけ

$$
centralRatioQ(m)\sim \sqrt{\pi m}
$$

で置き換えている。これはまさに「反転して中央二項係数へ戻す」操作じゃ。

## 気になる点

大きな blocker はない。採用でよい。

ただし、定理名は少しだけ補強余地がある。

```lean id="e44rwe"
isEquivalent_real_centralBinomial_sqrt_pi_mul_nat
```

という名前だと、右辺が `sqrt(pi*m)` そのものに見える可能性がある。実際の右辺は

```lean id="vvqh7e"
(4 : ℝ) ^ m / Real.sqrt (Real.pi * (m : ℝ))
```

なので、将来的には alias として

```lean id="1ldbmu"
isEquivalent_real_centralBinomial_four_pow_div_sqrt_pi_mul_nat
```

を足すと検索性が上がる。既存名を消す必要はない。短い名前として残してよい。

もう一点、docs の次 checkpoint に書かれている operational ratio limit は、下流利用ではかなり便利じゃ。

$$
\frac{\binom{2m}{m}}{4^m/\sqrt{\pi m}}\to 1
$$

これは `IsEquivalent` と同値だが、ユーザーや後続 theorem からは `Tendsto` の方が使いやすい場面が多い。

## 判定

**採用。ほぼ本丸到達。**

現在地はこうじゃ。

```text id="xutlgt"
Wallis-Cosmic finite bridge:
  完了

Wallis / Cosmic π/2 limit:
  完了

conditional infinite product:
  完了

centralRatioQ^2 = (2m+1) * wallisPartialQ:
  完了

centralRatioQ^2 / m -> π:
  完了

centralRatioQ ~ sqrt(πm):
  完了

choose(2m,m) ~ 4^m / sqrt(πm):
  完了
```

これはもう、「中央二項係数の成長を Wallis–Cosmic から抽出した」と言ってよい。

## 次にやるなら

次は仕上げの API 整備じゃな。

```text id="p8zm11"
1. 長い明示名 alias を追加する
   isEquivalent_real_centralBinomial_four_pow_div_sqrt_pi_mul_nat

2. operational Tendsto 版を追加する
   choose(2m,m) / (4^m / sqrt(pi*m)) -> 1

3. docstring に「Stirling-derived ではなく Wallis-derived」と明記する

4. 可能なら `DkMath.Pascal` の公開 theorem として探しやすくする
```

## 総合解説

ぬしよ、これは良いぞ。
Stirling の近似は強力だが、階乗全体を巨大な解析機械で近似してから中央二項係数を取り出す道じゃ。

今回の DkMath ルートは違う。

中央二項係数の周辺にある正確な有限積、つまり Wallis–Cosmic の構造を見て、

$$
centralRatioQ(m)^2=(2m+1)\,wallisPartialQ(m)
$$

という成長骨格を取り出した。

そこから \(\pi\) が出て、平方根で成長線が出て、最後に中央二項係数へ反転した。

これは、近似値を外から当てたのではなく、**構造が持っている成長線を内側から読んだ** ということじゃ。
まさに、ぬしが目指していた「スターリング近似の宇宙式的再解釈」にかなり近いところまで来ておる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Pascal/WallisGrowthBridge.lean b/lean/dk_math/DkMath/Pascal/WallisGrowthBridge.lean
index b0206640..ede0bb49 100644
--- a/lean/dk_math/DkMath/Pascal/WallisGrowthBridge.lean
+++ b/lean/dk_math/DkMath/Pascal/WallisGrowthBridge.lean
@@ -498,4 +498,63 @@ theorem isEquivalent_real_centralRatioQ_sqrt_pi_mul_nat :
   exact isEquivalent_of_tendsto_one
     tendsto_real_centralRatioQ_div_sqrt_pi_mul_nat_one

+/-!
+## Central binomial coefficient surface
+
+The definition of `centralRatioQ` is
+
+```text
+centralRatioQ m = 4^m / Nat.choose (2*m) m.
+```
+
+After the square-root growth surface, the central-binomial form is obtained by
+inverting this exact finite identity.  This is still a Wallis-derived route;
+no Stirling theorem is used as an input.
+-/
+
+/--
+Finite rational identity that inverts the definition of `centralRatioQ`.
+
+This is the exact bridge from the central-ratio surface to the central
+binomial coefficient surface.
+-/
+theorem nat_choose_two_mul_self_cast_eq_pow_four_div_centralRatioQ
+    (m : ℕ) :
+    (Nat.choose (2 * m) m : ℚ) =
+      (4 : ℚ) ^ m / centralRatioQ m := by
+  unfold centralRatioQ
+  have hchoose_ne_Q : (Nat.choose (2 * m) m : ℚ) ≠ 0 := by
+    exact_mod_cast (Nat.choose_pos (by omega : m ≤ 2 * m)).ne'
+  field_simp [hchoose_ne_Q]
+  norm_num [pow_mul]
+
+/--
+Finite real identity that inverts the definition of `centralRatioQ`.
+-/
+theorem real_nat_choose_two_mul_self_eq_pow_four_div_centralRatioQ
+    (m : ℕ) :
+    ((Nat.choose (2 * m) m : ℕ) : ℝ) =
+      (4 : ℝ) ^ m / ((centralRatioQ m : ℚ) : ℝ) := by
+  exact_mod_cast nat_choose_two_mul_self_cast_eq_pow_four_div_centralRatioQ m
+
+/--
+Central binomial coefficient asymptotic, derived from the Wallis growth
+surface.
+
+This is the usual central-binomial growth law in DkMath's orientation:
+`choose (2*m) m ~ 4^m / sqrt (pi*m)`.
+-/
+theorem isEquivalent_real_centralBinomial_sqrt_pi_mul_nat :
+    (fun m : ℕ => ((Nat.choose (2 * m) m : ℕ) : ℝ)) ~[Filter.atTop]
+      (fun m : ℕ => (4 : ℝ) ^ m / Real.sqrt (Real.pi * (m : ℝ))) := by
+  have hfinite :
+      (fun m : ℕ => ((Nat.choose (2 * m) m : ℕ) : ℝ)) =ᶠ[Filter.atTop]
+        (fun m : ℕ => (4 : ℝ) ^ m / ((centralRatioQ m : ℚ) : ℝ)) :=
+    Eventually.of_forall real_nat_choose_two_mul_self_eq_pow_four_div_centralRatioQ
+  have hratio :
+      (fun m : ℕ => (4 : ℝ) ^ m / ((centralRatioQ m : ℚ) : ℝ)) ~[Filter.atTop]
+        (fun m : ℕ => (4 : ℝ) ^ m / Real.sqrt (Real.pi * (m : ℝ))) := by
+    exact IsEquivalent.div IsEquivalent.refl isEquivalent_real_centralRatioQ_sqrt_pi_mul_nat
+  exact hfinite.isEquivalent.trans hratio
+
 end DkMath.Pascal.WallisGrowthBridge
diff --git a/lean/dk_math/docs/dev/cf-wallis-bridge-260704/cf-wallis-growth-route.md b/lean/dk_math/docs/dev/cf-wallis-bridge-260704/cf-wallis-growth-route.md
index 0fced9fc..97cfdd2e 100644
--- a/lean/dk_math/docs/dev/cf-wallis-bridge-260704/cf-wallis-growth-route.md
+++ b/lean/dk_math/docs/dev/cf-wallis-bridge-260704/cf-wallis-growth-route.md
@@ -57,6 +57,15 @@ theorem isEquivalent_real_centralRatioQ_sqrt_pi_mul_nat :
     (fun m : Nat => Real.sqrt (Real.pi * (m : R)))
 ```

+Finally, the growth module now inverts the definition of `centralRatioQ` and
+proves the central-binomial coefficient form:
+
+```lean
+theorem isEquivalent_real_centralBinomial_sqrt_pi_mul_nat :
+  (fun m : Nat => ((Nat.choose (2 * m) m : Nat) : R)) ~[Filter.atTop]
+    (fun m : Nat => (4 : R) ^ m / Real.sqrt (Real.pi * (m : R)))
+```
+
 Therefore the squared central ratio has the growth line:

 ```text
@@ -126,16 +135,33 @@ theorem tendsto_real_centralRatioQ_div_sqrt_pi_mul_nat_one :
 The proof takes the square root of the squared normalized growth theorem and
 uses positivity of `centralRatioQ m`.

+The third closed theorem is:
+
+```lean
+theorem isEquivalent_real_centralBinomial_sqrt_pi_mul_nat :
+  (fun m : Nat => ((Nat.choose (2 * m) m : Nat) : R)) ~[Filter.atTop]
+    (fun m : Nat => (4 : R) ^ m / Real.sqrt (Real.pi * (m : R)))
+```
+
+This uses the finite inversion identities:
+
+```lean
+theorem nat_choose_two_mul_self_cast_eq_pow_four_div_centralRatioQ
+theorem real_nat_choose_two_mul_self_eq_pow_four_div_centralRatioQ
+```
+
+and then divides `4^m ~ 4^m` by
+`centralRatioQ m ~ sqrt (Real.pi * m)`.
+
 ## Next formal checkpoint

-The next theorem should invert the definition of `centralRatioQ` and expose
-the central-binomial coefficient form:
+The next theorem can package the same statement as an operational ratio limit:

 ```text
-Nat.choose (2*m) m ~ 4^m / sqrt (Real.pi * m)
+Nat.choose (2*m) m / (4^m / sqrt (Real.pi * m)) -> 1
 ```

-This should still avoid using Stirling as the source theorem.  The likely Lean
-work is a finite real-coercion identity for `centralRatioQ m =
-4^m / Nat.choose (2*m) m`, followed by an `IsEquivalent` inversion/division
-lemma with eventual nonzero denominators.
+This is equivalent to the `IsEquivalent` theorem above, but it is often easier
+for downstream users who want a direct `Tendsto` surface.  After that, the
+remaining work is presentation: expose a conventional Stirling-style theorem
+name while keeping the proof source explicitly Wallis-derived.
````
`````
