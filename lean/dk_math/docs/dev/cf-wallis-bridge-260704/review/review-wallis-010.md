# Git diff / Report / Review

## Upd: DkMath.Pascal.WallisGrowthBridge

gch: e47a3c0be8e47a7c9c282206f9784b5ce978b6b5

## Report

cp009 完了です。

[WallisGrowthBridge.lean](/lean/dk_math/DkMath/Pascal/WallisGrowthBridge.lean) に、中央比率の有限平方恒等式までを no-sorry で追加しました。

追加した主な定理:

- `centralRatioQ_succ_eq`
- `mirrorOddRatioPartialQ_succ_eq`
- `centralRatioQ_div_mirrorOddRatioPartialQ_eq_two_mul_add_one`
- `centralRatioQ_div_mirrorOddRatioPartialQ_eq_oddRightQ_pred`
- `centralRatioQ_sq_eq_odd_mul_wallisPartialQ`
- `centralRatioQ_sq_eq_odd_mul_cosmicPartialQ`
- real coercion 版 2 本

これで有限レベルでは

```text
centralRatioQ m ^ 2 = (2*m + 1) * wallisPartialQ m
centralRatioQ m ^ 2 = (2*m + 1) * cosmicPartialQ m
```

が固定されました。

あわせて [cf-wallis-growth-route.md](/lean/dk_math/docs/dev/cf-wallis-bridge-260704/cf-wallis-growth-route.md) を新規作成し、Stirling を主説明にせず、Wallis-Cosmic の exact identity から `centralRatioQ^2 ~ pi*m` へ進むルートを短く整理しました。

確認済み:

- `lake build DkMath.Pascal.WallisGrowthBridge` pass
- `lake build DkMath.Pascal` pass
- `lake build DkMath` pass
- Wallis 系 3 ファイルの `sorry` 検索: なし
- `git diff --check` pass

`lake build DkMath` の既存別件 `sorry` warning は継続していますが、今回の Wallis 変更範囲にはありません。

## Review

## 結論

うむ、`review-wallis-010` は **採用でよい** 。
これはかなり大きい。有限段階で、中央比率の成長線そのものが閉じた。

今回追加された主定理は、まさに次の有限恒等式じゃ。

$$
centralRatioQ(m)^2=(2m+1),wallisPartialQ(m)
$$

そして cosmic 側も、

$$
centralRatioQ(m)^2=(2m+1),cosmicPartialQ(m)
$$

として閉じておる。報告でも、`centralRatioQ_sq_eq_odd_mul_wallisPartialQ` と `centralRatioQ_sq_eq_odd_mul_cosmicPartialQ`、さらに real coercion 版まで no-sorry で追加され、`lake build DkMath` まで通っていると確認されている。

## 何が重要か

今回の核は、漸近ではない。
**有限恒等式として成長線を掴んだ** ことじゃ。

前回の `WallisGrowthBridge` では、スターリング近似を主説明にせず、`centralRatioQ` の成長を exact product から読む方針が module doc に明記されていた。特に、次の有限平方恒等式を先に証明してから漸近へ進む、という roadmap が置かれていた。

今回、それが実際に閉じた。

つまり、古典的に

$$
\binom{2m}{m}\sim \frac{4^m}{\sqrt{\pi m}}
$$

へ行く前に、DkMath 側では

$$
centralRatioQ(m)^2=(2m+1),wallisPartialQ(m)
$$

という **完全な有限骨格** を持てた。

これは「スターリング近似で外から眺める」のではなく、「Wallis–Cosmic の有限積から成長を取り出す」道が本当に開いたということじゃ。

## 実装レビュー

`centralRatioQ_succ_eq` と `mirrorOddRatioPartialQ_succ_eq` を先に置き、直積の割り算を一気に潰さず recurrence で telescoping した判断が良い。`Finset.prod_div_distrib` 周りで無理をしない設計になっておる。

特に、

```lean
centralRatioQ_div_mirrorOddRatioPartialQ_eq_two_mul_add_one
```

が良い。これは

$$
\frac{centralRatioQ(m)}{mirrorOddRatioPartialQ(m)}=2m+1
$$

を有限 exact に固定している。そこから

```lean
centralRatioQ_sq_eq_odd_mul_wallisPartialQ
```

へ進む流れは自然じゃ。実装でも、`centralRatioQ / mirror` と `centralRatioQ * mirror` を掛け合わせて平方恒等式へ落としておる。

`centralRatioQ_div_mirrorOddRatioPartialQ_eq_oddRightQ_pred` は検索用 alias として悪くない。ただし名前だけ見ると少しだけ注意が要る。値は `2*m+1` なので、実質的には `m = n+1` と見たときの `oddRightQ n` に対応する。docstring に “predecessor-indexed” とあるので、意図は伝わる。

## 数学的意味

この恒等式は、次の読みを許す。

$$
centralRatioQ(m)^2=(2m+1),wallisPartialQ(m)
$$

すでに Wallis 側では、

$$
wallisPartialQ(m)\to \frac{\pi}{2}
$$

が閉じている。

だから直感的には、

$$
centralRatioQ(m)^2\sim (2m)\frac{\pi}{2}=\pi m
$$

となる。

つまり、

$$
centralRatioQ(m)\sim \sqrt{\pi m}
$$

が出る。

そして

$$
centralRatioQ(m)=\frac{4^m}{\binom{2m}{m}}
$$

だから、反転すれば中央二項係数の成長

$$
\binom{2m}{m}\sim \frac{4^m}{\sqrt{\pi m}}
$$

に至る。

ここで大事なのは、`π` が Stirling から来たのではなく、**宇宙式 Gap 比率の Wallis 積から来ている** ことじゃ。
これはぬしの目的そのものに合っている。

## 気になる点

大きな blocker はない。
軽い注意は 2 つ。

1つ目。新規 docs のパス表記が報告文では

```text
/lean_dk_math/docs/dev/...
```

になっているが、diff では

```text
lean/dk_math/docs/dev/...
```

になっておる。実体が後者なら、報告文側の typo じゃな。機能上の問題ではないが、次回レポートでは揃えるとよい。

2つ目。次の `Tendsto` は finite algebra ではなく、`atTop` の実解析 bookkeeping になる。コメントでも、`m = 0` 問題と `(2*m+1)/m -> 2` の処理が別 checkpoint だと明記されている。
これは正しい。ここからは焦って一発で全部閉じようとせず、補助極限を小さく切るのがよい。

## 判定

**採用。**

現在地はこうじゃ。

```text
Wallis-Cosmic finite bridge:
  完了

π/2 limit bridge:
  完了

conditional infinite product:
  完了

growth decomposition:
  完了

finite squared growth identity:
  完了

次:
  centralRatioQ^2 / m -> π
```

## 次の作業指示

```text
Continue from gch e47a3c0be8e47a7c9c282206f9784b5ce978b6b5.

Review result: accepted.

The finite squared growth identity is now closed:

  centralRatioQ m ^ 2 = (2*m + 1) * wallisPartialQ m
  centralRatioQ m ^ 2 = (2*m + 1) * cosmicPartialQ m

Next goal:
prove the squared normalized central-ratio limit

  (((centralRatioQ m : ℚ) : ℝ) ^ 2 / (m : ℝ)) -> Real.pi

without using Stirling as the conceptual source.

Work in:

  DkMath.Pascal.WallisGrowthBridge

Do not move this into the finite bridge or limit bridge.

Suggested plan:

1. Add elementary real helper for the odd boundary ratio.

First prove a clean real limit:

  theorem tendsto_odd_boundary_div_nat_two :
      Filter.Tendsto
        (fun m : ℕ => ((2 * m + 1 : ℝ) / (m : ℝ)))
        Filter.atTop
        (nhds 2) := by
    ...

This has an `m = 0` division issue only at one point, so handle it with
eventual equality on `m ≥ 1`.

Possible route:

  (2*m + 1)/m = 2 + 1/m

eventually, then use:

  tendsto_const_nhds
  tendsto_one_div_atTop_nhds_zero_nat

or whatever Mathlib provides.

Search useful names:
- `tendsto_one_div_atTop_nhds_zero_nat`
- `tendsto_natCast_atTop_atTop`
- `Tendsto.div`
- `tendsto_const_nhds`
- `eventually_atTop`
- `Filter.Eventually`

2. Add a theorem rewriting the normalized square.

Use the finite real identity:

  real_coe_centralRatioQ_sq_eq_odd_mul_wallisPartialQ

to show eventually:

  ((centralRatioQ m : ℚ) : ℝ)^2 / (m : ℝ)
    =
  ((2*m + 1 : ℝ) / (m : ℝ)) *
    ((wallisPartialQ m : ℚ) : ℝ)

Suggested theorem:

  theorem real_centralRatioQ_sq_div_nat_eq_odd_div_nat_mul_wallis
      {m : ℕ} (hm : m ≠ 0) :
      ((centralRatioQ m : ℚ) : ℝ) ^ 2 / (m : ℝ)
        =
      ((2 * m + 1 : ℝ) / (m : ℝ)) *
        ((wallisPartialQ m : ℚ) : ℝ) := by
    rw [real_coe_centralRatioQ_sq_eq_odd_mul_wallisPartialQ]
    field_simp [Nat.cast_ne_zero.mpr hm]
    ring

If coercion of `2*m+1` causes trouble, add smaller cast lemmas first.

3. Prove the main squared normalized limit.

Target:

  theorem tendsto_real_centralRatioQ_sq_div_nat_pi :
      Filter.Tendsto
        (fun m : ℕ =>
          (((centralRatioQ m : ℚ) : ℝ) ^ 2 / (m : ℝ)))
        Filter.atTop
        (nhds Real.pi) := by
    ...

Proof idea:

- eventually rewrite using step 2;
- `((2*m+1)/m) -> 2`;
- `((wallisPartialQ m : ℚ) : ℝ) -> Real.pi / 2`;
- multiply limits:
  `2 * (Real.pi / 2) = Real.pi`.

4. Also add cosmic version if easy.

Because

  centralRatioQ m ^ 2 = (2*m + 1) * cosmicPartialQ m

also holds, a second theorem can be:

  theorem tendsto_real_centralRatioQ_sq_div_nat_pi_cosmic_route :
      Filter.Tendsto
        (fun m : ℕ =>
          (((centralRatioQ m : ℚ) : ℝ) ^ 2 / (m : ℝ)))
        Filter.atTop
        (nhds Real.pi) := by
    ...

This can either reuse the Wallis route theorem, or repeat the proof with:

  tendsto_cosmicPartialQ_pi_div_two

The Wallis route theorem can be the main public theorem.
The cosmic route can be a docstring alias if it is redundant.

5. Do not attempt the square-root asymptotic in the same pass unless the squared limit is already clean.

The next theorem after the squared limit would be:

  centralRatioQ m / Real.sqrt (Real.pi * m) -> 1

but this requires:
- positivity;
- sqrt continuity;
- `sqrt (x*y)` or equivalent normalization;
- nonzero eventual handling.

Keep that as the next checkpoint.

6. Update documentation.

Extend:

  docs/dev/cf-wallis-bridge-260704/cf-wallis-growth-route.md

Add:

  - finite squared identity is now proved;
  - next formal theorem is `centralRatioQ^2 / m -> π`;
  - this is the first formal extraction of central-binomial growth from Wallis-Cosmic structure.

7. Build gates:

  lake build DkMath.Pascal.WallisGrowthBridge
  lake build DkMath.Pascal
  lake build DkMath
  git diff --check

8. No-sorry policy:

Check no `sorry` in:
  DkMath/Pascal/WallisCosmicPetalBridge.lean
  DkMath/Pascal/WallisLimitBridge.lean
  DkMath/Pascal/WallisGrowthBridge.lean
```

ここは実に良い。
スターリング近似へ逃げず、有限恒等式から中央二項係数の成長線が見え始めた。わっちはこの流れ、かなり好きじゃ。次はとうとう

$$
\frac{centralRatioQ(m)^2}{m}\to \pi
$$

を Lean に認めさせる番じゃな。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Pascal/WallisGrowthBridge.lean b/lean/dk_math/DkMath/Pascal/WallisGrowthBridge.lean
index 3b7c900d..e865af0d 100644
--- a/lean/dk_math/DkMath/Pascal/WallisGrowthBridge.lean
+++ b/lean/dk_math/DkMath/Pascal/WallisGrowthBridge.lean
@@ -156,4 +156,139 @@ theorem real_coe_centralRatioQ_eq_wallisPartialQ_div_mirrorOddRatioPartialQ
   exact_mod_cast
     centralRatioQ_eq_wallisPartialQ_div_mirrorOddRatioPartialQ m

+/-!
+## Telescoping mirror ratio
+
+The next finite target is the exact squared growth identity
+
+```text
+centralRatioQ m ^ 2 = (2*m + 1) * wallisPartialQ m.
+```
+
+The key is not an asymptotic theorem; it is the telescoping ratio between the
+central half-product and the mirror half-product.  We prove it by recurrence,
+which keeps the product cancellation explicit and avoids a brittle direct
+`Finset.prod_div_distrib` proof.
+-/
+
+/-- One-step recurrence for the central ratio. -/
+theorem centralRatioQ_succ_eq
+    (m : ℕ) :
+    centralRatioQ (m + 1) =
+      centralRatioQ m * ((2 * m + 2 : ℚ) / (2 * m + 1 : ℚ)) := by
+  rw [centralRatioQ_eq_centralOddRatioPartialQ (m + 1),
+    centralRatioQ_eq_centralOddRatioPartialQ m]
+  unfold centralOddRatioPartialQ evenCenterQ oddLeftQ
+  rw [Finset.prod_range_succ]
+
+/-- One-step recurrence for the mirror half-product. -/
+theorem mirrorOddRatioPartialQ_succ_eq
+    (m : ℕ) :
+    mirrorOddRatioPartialQ (m + 1) =
+      mirrorOddRatioPartialQ m * ((2 * m + 2 : ℚ) / (2 * m + 3 : ℚ)) := by
+  unfold mirrorOddRatioPartialQ evenCenterQ oddRightQ
+  rw [Finset.prod_range_succ]
+
+/--
+The quotient of the central ratio by the mirror factor telescopes to the
+right odd boundary `2*m + 1`.
+-/
+theorem centralRatioQ_div_mirrorOddRatioPartialQ_eq_two_mul_add_one
+    (m : ℕ) :
+    centralRatioQ m / mirrorOddRatioPartialQ m = (2 * m + 1 : ℚ) := by
+  induction m with
+  | zero =>
+      simp [centralRatioQ, mirrorOddRatioPartialQ]
+  | succ m ih =>
+      have hcentral :
+          centralRatioQ m =
+            (2 * m + 1 : ℚ) * mirrorOddRatioPartialQ m := by
+        calc
+          centralRatioQ m =
+              (centralRatioQ m / mirrorOddRatioPartialQ m) *
+                mirrorOddRatioPartialQ m := by
+            field_simp [mirrorOddRatioPartialQ_ne_zero m]
+          _ = (2 * m + 1 : ℚ) * mirrorOddRatioPartialQ m := by
+            rw [ih]
+      rw [centralRatioQ_succ_eq, mirrorOddRatioPartialQ_succ_eq, hcentral]
+      field_simp [mirrorOddRatioPartialQ_ne_zero m]
+      norm_num
+      ring
+
+/--
+Searchable alias: the telescoping quotient reaches the predecessor-indexed
+right odd boundary.
+-/
+theorem centralRatioQ_div_mirrorOddRatioPartialQ_eq_oddRightQ_pred
+    (m : ℕ) :
+    centralRatioQ m / mirrorOddRatioPartialQ m = (2 * m + 1 : ℚ) :=
+  centralRatioQ_div_mirrorOddRatioPartialQ_eq_two_mul_add_one m
+
+/--
+Finite squared central-ratio identity through the Wallis product.
+
+This is the exact finite growth line behind the later asymptotic reading:
+the square of the central ratio is a linear odd boundary times the Wallis
+partial product.
+-/
+theorem centralRatioQ_sq_eq_odd_mul_wallisPartialQ
+    (m : ℕ) :
+    centralRatioQ m ^ 2 =
+      (2 * m + 1 : ℚ) * wallisPartialQ m := by
+  calc
+    centralRatioQ m ^ 2 =
+        (centralRatioQ m / mirrorOddRatioPartialQ m) *
+          (centralRatioQ m * mirrorOddRatioPartialQ m) := by
+      field_simp [mirrorOddRatioPartialQ_ne_zero m]
+    _ = (2 * m + 1 : ℚ) * wallisPartialQ m := by
+      rw [centralRatioQ_div_mirrorOddRatioPartialQ_eq_two_mul_add_one,
+        centralRatioQ_mul_mirror_eq_wallisPartialQ]
+
+/--
+Finite squared central-ratio identity through the cosmic gap product.
+-/
+theorem centralRatioQ_sq_eq_odd_mul_cosmicPartialQ
+    (m : ℕ) :
+    centralRatioQ m ^ 2 =
+      (2 * m + 1 : ℚ) * cosmicPartialQ m := by
+  rw [← wallisPartialQ_eq_cosmicPartialQ]
+  exact centralRatioQ_sq_eq_odd_mul_wallisPartialQ m
+
+/--
+Real-coercion form of the squared Wallis growth identity.
+-/
+theorem real_coe_centralRatioQ_sq_eq_odd_mul_wallisPartialQ
+    (m : ℕ) :
+    ((centralRatioQ m : ℚ) : ℝ) ^ 2 =
+      (2 * m + 1 : ℝ) * ((wallisPartialQ m : ℚ) : ℝ) := by
+  exact_mod_cast centralRatioQ_sq_eq_odd_mul_wallisPartialQ m
+
+/--
+Real-coercion form of the squared cosmic growth identity.
+-/
+theorem real_coe_centralRatioQ_sq_eq_odd_mul_cosmicPartialQ
+    (m : ℕ) :
+    ((centralRatioQ m : ℚ) : ℝ) ^ 2 =
+      (2 * m + 1 : ℝ) * ((cosmicPartialQ m : ℚ) : ℝ) := by
+  exact_mod_cast centralRatioQ_sq_eq_odd_mul_cosmicPartialQ m
+
+/-!
+TODO for the next asymptotic pass:
+
+Prove
+
+```lean
+Filter.Tendsto
+  (fun m : ℕ => (((centralRatioQ m : ℚ) : ℝ) ^ 2 / (m : ℝ)))
+  Filter.atTop
+  (nhds Real.pi)
+```
+
+from `real_coe_centralRatioQ_sq_eq_odd_mul_wallisPartialQ`,
+`tendsto_wallisPartialQ_pi_div_two`, and
+`(2*m+1)/m -> 2`.  This is no longer a finite algebra problem: it needs the
+standard `atTop` handling for `m ≠ 0` and the real limit of `(2*m+1)/m`.
+Keep it as a separate proof-complete checkpoint.
+-/
+
 end DkMath.Pascal.WallisGrowthBridge
diff --git a/lean/dk_math/docs/dev/cf-wallis-bridge-260704/cf-wallis-growth-route.md b/lean/dk_math/docs/dev/cf-wallis-bridge-260704/cf-wallis-growth-route.md
new file mode 100644
index 00000000..3f614eaf
--- /dev/null
+++ b/lean/dk_math/docs/dev/cf-wallis-bridge-260704/cf-wallis-growth-route.md
@@ -0,0 +1,86 @@
+# Wallis-Cosmic Growth Route
+
+This note records the growth route after the Wallis-Cosmic finite and limit
+bridges.
+
+The goal is not to use Stirling's approximation as the conceptual source.
+Instead, DkMath reads the central binomial growth from exact finite products.
+
+## Exact identity
+
+The Lean module `DkMath.Pascal.WallisGrowthBridge` now proves:
+
+```text
+centralRatioQ m ^ 2
+  = (2*m + 1) * wallisPartialQ m
+```
+
+and the cosmic version:
+
+```text
+centralRatioQ m ^ 2
+  = (2*m + 1) * cosmicPartialQ m
+```
+
+This comes from two exact finite facts:
+
+```text
+centralRatioQ m * mirrorOddRatioPartialQ m = wallisPartialQ m
+centralRatioQ m / mirrorOddRatioPartialQ m = 2*m + 1
+```
+
+The second identity is the telescoping mirror ratio.
+
+## Growth reading
+
+The limit module already proves:
+
+```text
+wallisPartialQ m -> pi / 2
+```
+
+Therefore the squared central ratio has the growth line:
+
+```text
+centralRatioQ m ^ 2 ~ pi * m
+```
+
+and hence:
+
+```text
+centralRatioQ m ~ sqrt (pi * m)
+```
+
+Since:
+
+```text
+centralRatioQ m = 4^m / Nat.choose (2*m) m
+```
+
+inverting gives the central-binomial growth law:
+
+```text
+Nat.choose (2*m) m ~ 4^m / sqrt (pi * m)
+```
+
+## Next formal checkpoint
+
+The next theorem should be the squared normalized limit:
+
+```lean
+Filter.Tendsto
+  (fun m : Nat => (((centralRatioQ m : Q) : R) ^ 2 / (m : R)))
+  Filter.atTop
+  (nhds Real.pi)
+```
+
+This should use:
+
+```text
+centralRatioQ m ^ 2 = (2*m + 1) * wallisPartialQ m
+wallisPartialQ m -> pi / 2
+(2*m + 1) / m -> 2
+```
+
+The `m = 0` issue is an `atTop` bookkeeping problem, so it should be handled
+as a separate no-sorry checkpoint.
````
`````
