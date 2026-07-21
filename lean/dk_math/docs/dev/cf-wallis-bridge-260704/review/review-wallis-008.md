# Git diff / Report / Review

## Upd: DkMath.Pascal.*

gch: 0105ce251c7fc87813b538f5e7d4ece5acd05d53

## Report

実装と gate 確認まで完了しました。

追加内容:

- [WallisCosmicPetalBridge.lean](/lean/dk_math/DkMath/Pascal/WallisCosmicPetalBridge.lean)
  - `centralRatioQ_mul_mirror_eq_prod_wallisFactorQ`
  - `centralRatioQ_mul_mirror_eq_prod_cosmicFactorQ`
  - 中央比率式は per-factor sequence ではなく partial-product expression だと docstring に明記。

- [WallisLimitBridge.lean](/lean/dk_math/DkMath/Pascal/WallisLimitBridge.lean)
  - `real_coe_prod_wallisFactorQ_eq_Wallis_W`
  - `real_coe_prod_cosmicFactorQ_eq_Wallis_W`

- [cf-wallis-final-chain.md](/lean/dk_math/docs/dev/cf-wallis-bridge-260704/cf-wallis-final-chain.md)
  - ordered / conditional product と default unordered / unconditional `HasProd` の違いを短く追記。
  - 無条件版には別途 absolute/log-product summability が必要、と明記。

確認済み:

- `lake build DkMath.Pascal.WallisCosmicPetalBridge` pass
- `lake build DkMath.Pascal.WallisLimitBridge` pass
- `lake build DkMath.Pascal` pass
- `lake build DkMath` pass
- `git diff --check` pass
- Wallis 2ファイルの `sorry` 検索: なし

`lake build DkMath` では既存の別件 `sorry` warning が複数出ていますが、今回の Wallis 変更範囲では増えていません。

## Review

## 結論

うむ、`review-wallis-008` は **採用でよい** 。
今回の差分は、Wallis–Cosmic bridge を「極限定理として閉じた」だけでなく、次の再利用段階へ向けて **有限積の明示 API** を整えたものじゃ。

追加された

```lean
centralRatioQ_mul_mirror_eq_prod_wallisFactorQ
centralRatioQ_mul_mirror_eq_prod_cosmicFactorQ
```

は、中央比率式が per-factor sequence ではなく **partial-product expression** であることを docstring で明記している。これはかなり大事じゃ。中央比率そのものを無理に因子列扱いせず、有限積列の結果として扱う、という型の筋が通っておる。

`WallisLimitBridge.lean` 側の

```lean
real_coe_prod_wallisFactorQ_eq_Wallis_W
real_coe_prod_cosmicFactorQ_eq_Wallis_W
```

も良い。明示的な `Finset.range m` 積が Mathlib の `Real.Wallis.W` と一致することを実数キャストで固定した。これにより「定義展開すれば同じ」の状態から、呼び出しやすい定理名を持つ API へ昇格しておる。

さらに `cf-wallis-final-chain.md` に ordered / conditional product と default unordered / unconditional `HasProd` の違いを追記し、無条件版には absolute / log-product summability が必要だと明記したのも正しい。

## 判定

**採用。閉じた橋の整備として良い差分。**

今回の到達点はこうじゃ。

```text
centralRatioQ * mirror
  = explicit finite Wallis product
  = explicit finite cosmic product
  -> Real.Wallis.W
  -> Real.pi / 2
```

加えて、

```text
ordered / conditional product:
  整理済み

default unconditional product:
  意図的に未主張
```

という境界線も明確になった。

## 目的を覚えているか

覚えておる。
これは単に「Wallis 積で \(\pi/2\) が出た、よかったね」という話ではない。

本当の目的は、 **スターリング近似に頼って中央二項係数の成長を外から近似するのではなく、宇宙式の有限積構造から成長線そのものを読む** ことじゃ。

つまり、古典的には

$$
\binom{2m}{m}\sim \frac{4^m}{\sqrt{\pi m}}
$$

を Stirling で得る。
しかし DkMath 的には、まず exact に

$$
\frac{4^m}{\binom{2m}{m}}\cdot M_m=C_m
$$

を作る。

ここで

$$
C_m=\prod_{k=0}^{m-1}\left(1+\frac{1}{N_k}\right)
$$

は宇宙式 Gap 比率の有限積で、今回すでに

$$
C_m\to \frac{\pi}{2}
$$

まで閉じた。

だから次の狙いは、

$$
\frac{4^m}{\binom{2m}{m}}
$$

つまり `centralRatioQ m` の成長を、Stirling の外部近似ではなく、

$$
centralRatioQ(m)=\frac{cosmicPartialQ(m)}{mirrorOddRatioPartialQ(m)}
$$

として分解し、`cosmicPartialQ` と `mirrorOddRatioPartialQ` の成長から読むことじゃ。

これが、ぬしの言う **近似でなく成長線を語れる構造視点** じゃな。

## 何が見えてきたか

いま Wallis bridge で得たのは、

$$
centralRatioQ(m)\cdot mirror(m)\to \frac{\pi}{2}
$$

じゃ。

しかし `centralRatioQ m` 自体は発散する。実際、古典的には

$$
centralRatioQ(m)=\frac{4^m}{\binom{2m}{m}}\sim \sqrt{\pi m}
$$

じゃ。

つまり、次の山はこれじゃ。

```text
centralRatioQ:
  √m スケールで成長する主成分

mirrorOddRatioPartialQ:
  1/√m スケールで減衰する補正成分

cosmicPartialQ:
  両者の積として π/2 に収束する保存積
```

ここが美しい。
`centralRatioQ` の成長と `mirror` の減衰が釣り合い、積として `cosmicPartialQ` が \(\pi/2\) に閉じる。

これはまさに、

```text
Big:
  π/2 へ閉じる cosmicPartialQ

Body:
  centralRatioQ と mirror の相互補正過程

Gap:
  有限段階での未到達分
```

として読める。

## 今回のレビュー上の注意点

差分そのものには大きな問題はない。
ただし、次の段階では `centralRatioQ` を「因子列」へ無理に分解しすぎない方がよい。

今回 docstring で明記された通り、`centralRatioQ m * mirrorOddRatioPartialQ m` は partial-product expression であり、per-factor sequence ではない。
したがって、次にやるなら主語は

```text
centralRatioQ m / sqrt m
mirrorOddRatioPartialQ m * sqrt m
```

のような **スケール正規化された列** がよい。

## 次の作業指示

```text
Continue from gch 0105ce251c7fc87813b538f5e7d4ece5acd05d53.

Review result: accepted.

The Wallis-Cosmic bridge is now structurally closed as:
- central ratio expression
- finite Wallis product
- finite cosmic gap product
- ordered / conditional infinite product
- convergence to Real.pi / 2

Now move toward the original purpose:
replace the Stirling-approximation viewpoint with a CosmicFormula growth-line viewpoint for the central binomial coefficient.

Main objective:
Do not use Stirling as the primary explanation.
Use the exact Wallis-Cosmic bridge to expose the growth structure of

  centralRatioQ m = 4^m / Nat.choose (2*m) m

and eventually recover the central-binomial growth law structurally.

Suggested new module:

  DkMath/Pascal/WallisGrowthBridge.lean

Imports:

  import Mathlib
  import DkMath.Pascal.WallisCosmicPetalBridge
  import DkMath.Pascal.WallisLimitBridge

Tasks:

1. Add a new growth-facing module, not inside `WallisCosmicPetalBridge.lean`.

   Keep responsibilities separated:

   - `WallisCosmicPetalBridge.lean`
     finite algebraic identities

   - `WallisLimitBridge.lean`
     Tendsto / HasProd / tprod / Real.pi

   - `WallisGrowthBridge.lean`
     centralRatioQ growth, mirror decay, central binomial asymptotic route

2. First add exact algebraic growth decompositions.

   Suggested theorem:

   theorem centralRatioQ_eq_cosmicPartialQ_div_mirrorOddRatioPartialQ
       (m : ℕ) :
       centralRatioQ m =
         cosmicPartialQ m / mirrorOddRatioPartialQ m := by
     -- from centralRatioQ_mul_mirror_eq_cosmicPartialQ
     -- use mirrorOddRatioPartialQ_pos m
     ...

   Also add the Wallis route variant:

   theorem centralRatioQ_eq_wallisPartialQ_div_mirrorOddRatioPartialQ
       (m : ℕ) :
       centralRatioQ m =
         wallisPartialQ m / mirrorOddRatioPartialQ m := by
     ...

   These are exact identities and should be the first bridge toward growth.

3. Add positivity / nonzero helpers needed for division.

   Use existing:

   - `mirrorOddRatioPartialQ_pos`
   - `cosmicPartialQ_pos`
   - `wallisPartialQ_pos`
   - `centralRatioQ_pos`

   If needed, expose:

   theorem mirrorOddRatioPartialQ_ne_zero (m : ℕ) :
       mirrorOddRatioPartialQ m ≠ 0 := ...

4. Investigate Mathlib for existing Wallis inequalities or central binomial bounds.

   Search for names involving:

   - `centralBinomial`
   - `choose`
   - `Nat.choose`
   - `wallis`
   - `Wallis`
   - `factorial`
   - `sqrt`
   - `asymptotic`
   - `IsEquivalent`
   - `Asymptotics`
   - `Stirling`

   Do not rely on Stirling as the final DkMath interpretation, but it is allowed to inspect existing theorems to know what Mathlib already has.

5. Target growth theorem candidates.

   Preferred structural target:

   theorem tendsto_centralRatioQ_div_sqrt_pi_mul_m :
       Filter.Tendsto
         (fun m : ℕ =>
           (((centralRatioQ m : ℚ) : ℝ) / Real.sqrt (Real.pi * m)))
         Filter.atTop
         (nhds 1)

   But this may require substantial asymptotic work.

   If this is too heavy, start with Wallis-style inequalities instead.

6. More realistic first growth target: finite Wallis inequalities.

   Try to prove or import bounds of the form:

     lower(m) ≤ centralRatioQ m / Real.sqrt m
     centralRatioQ m / Real.sqrt m ≤ upper(m)

   or directly:

     c1 * Real.sqrt m ≤ ((centralRatioQ m : ℚ) : ℝ)
     ((centralRatioQ m : ℚ) : ℝ) ≤ c2 * Real.sqrt m

   The exact constants can be adjusted based on what closes.

   The point is to show:
   centralRatioQ has √m growth without invoking Stirling as the conceptual source.

7. Mirror decay route.

   Since

     centralRatioQ m * mirrorOddRatioPartialQ m = cosmicPartialQ m

   and cosmicPartialQ tends to π/2, centralRatioQ grows if and only if mirror decays.

   Investigate proving:

     mirrorOddRatioPartialQ m ≈ const / sqrt m

   or at least:

     mirrorOddRatioPartialQ m * Real.sqrt m

   has a finite positive limit or bounded interval.

8. Do not force full asymptotics in one pass.

   Acceptable first pass:

   - add exact decomposition theorems;
   - add division identities;
   - add real coercion versions;
   - document the growth route;
   - search Mathlib and record available theorems;
   - prove easy inequalities if they close.

9. Suggested documentation note:

   Add a short note:

     docs/dev/cf-wallis-bridge-260704/cf-wallis-growth-route.md

   Explain:

   - Stirling gives central binomial growth externally.
   - The CosmicFormula route seeks the same growth from exact finite products.
   - `centralRatioQ * mirror = cosmicPartialQ`.
   - `cosmicPartialQ -> π/2`.
   - Therefore the growth of `centralRatioQ` is encoded in the decay of `mirror`.
   - This is the structural route toward extracting binomial coefficient growth.

10. Build gates:

   lake build DkMath.Pascal.WallisCosmicPetalBridge
   lake build DkMath.Pascal.WallisLimitBridge
   lake build DkMath.Pascal.WallisGrowthBridge
   lake build DkMath.Pascal
   lake build DkMath
   git diff --check

11. Keep no-sorry policy for Wallis files.

   If the full asymptotic theorem is too heavy, do not add it with `sorry`.
   Instead add exact identities and a documented TODO.
```

うむ、ここからが本当の目的じゃ。
Wallis–Cosmic bridge は、\(\pi/2\) を出すためだけの道ではない。中央二項係数の成長を、スターリングの近似という外部の霧ではなく、宇宙式の有限積の足跡から読むための道なのじゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Pascal/WallisCosmicPetalBridge.lean b/lean/dk_math/DkMath/Pascal/WallisCosmicPetalBridge.lean
index ed20e07d..b5714eab 100644
--- a/lean/dk_math/DkMath/Pascal/WallisCosmicPetalBridge.lean
+++ b/lean/dk_math/DkMath/Pascal/WallisCosmicPetalBridge.lean
@@ -308,6 +308,19 @@ theorem centralRatioQ_mul_mirror_eq_wallisPartialQ (m : ℕ) :
   rw [centralRatioQ_eq_centralOddRatioPartialQ,
     centralOdd_mul_mirror_eq_wallisPartialQ]

+/--
+The proof-note central-ratio expression is the ordered finite product of the
+Wallis factors.
+
+This is intentionally a finite theorem: `centralRatioQ m * mirrorOddRatioPartialQ m`
+is a partial-product expression, not a per-factor sequence.
+-/
+theorem centralRatioQ_mul_mirror_eq_prod_wallisFactorQ (m : ℕ) :
+    centralRatioQ m * mirrorOddRatioPartialQ m =
+      ∏ k ∈ Finset.range m, wallisFactorQ k := by
+  rw [centralRatioQ_mul_mirror_eq_wallisPartialQ]
+  rfl
+
 /--
 The finite Wallis-Cosmic Petal bridge:
 the central odd half-product times its mirror equals the cosmic gap product.
@@ -325,4 +338,17 @@ theorem centralRatioQ_mul_mirror_eq_cosmicPartialQ (m : ℕ) :
   rw [centralRatioQ_eq_centralOddRatioPartialQ,
     centralOdd_mul_mirror_eq_cosmicPartialQ]

+/--
+The proof-note central-ratio expression is the ordered finite product of the
+cosmic gap factors.
+
+As with `centralRatioQ_mul_mirror_eq_prod_wallisFactorQ`, this stays in the
+finite algebraic module because it does not assert an infinite product.
+-/
+theorem centralRatioQ_mul_mirror_eq_prod_cosmicFactorQ (m : ℕ) :
+    centralRatioQ m * mirrorOddRatioPartialQ m =
+      ∏ k ∈ Finset.range m, cosmicFactorQ k := by
+  rw [centralRatioQ_mul_mirror_eq_cosmicPartialQ]
+  rfl
+
 end DkMath.Pascal.WallisCosmicPetalBridge
diff --git a/lean/dk_math/DkMath/Pascal/WallisLimitBridge.lean b/lean/dk_math/DkMath/Pascal/WallisLimitBridge.lean
index 5036f96f..4b643b11 100644
--- a/lean/dk_math/DkMath/Pascal/WallisLimitBridge.lean
+++ b/lean/dk_math/DkMath/Pascal/WallisLimitBridge.lean
@@ -44,12 +44,32 @@ theorem real_coe_wallisPartialQ_eq_Wallis_W (m : ℕ) :
     norm_num
     field_simp

+/--
+The explicit ordered Wallis-factor product, after coercion to `ℝ`, is
+Mathlib's Wallis product `Real.Wallis.W`.
+-/
+theorem real_coe_prod_wallisFactorQ_eq_Wallis_W (m : ℕ) :
+    ((∏ k ∈ Finset.range m, wallisFactorQ k : ℚ) : ℝ) =
+      Real.Wallis.W m := by
+  rw [← real_coe_wallisPartialQ_eq_Wallis_W]
+  rfl
+
 /-- The finite Wallis and cosmic partial products are pointwise equal over `ℝ`. -/
 theorem real_coe_wallisPartialQ_eq_cosmicPartialQ (m : ℕ) :
     ((wallisPartialQ m : ℚ) : ℝ) =
       ((cosmicPartialQ m : ℚ) : ℝ) := by
   exact_mod_cast wallisPartialQ_eq_cosmicPartialQ m

+/--
+The explicit ordered cosmic-factor product, after coercion to `ℝ`, is also
+Mathlib's Wallis product `Real.Wallis.W`.
+-/
+theorem real_coe_prod_cosmicFactorQ_eq_Wallis_W (m : ℕ) :
+    ((∏ k ∈ Finset.range m, cosmicFactorQ k : ℚ) : ℝ) =
+      Real.Wallis.W m := by
+  rw [← real_coe_wallisPartialQ_eq_Wallis_W]
+  exact_mod_cast (wallisPartialQ_eq_cosmicPartialQ m).symm
+
 /--
 The proof-note central-ratio expression is pointwise equal to the finite
 Wallis product over `ℝ`.
diff --git a/lean/dk_math/docs/dev/cf-wallis-bridge-260704/cf-wallis-final-chain.md b/lean/dk_math/docs/dev/cf-wallis-bridge-260704/cf-wallis-final-chain.md
index e0a875d5..2dc7641f 100644
--- a/lean/dk_math/docs/dev/cf-wallis-bridge-260704/cf-wallis-final-chain.md
+++ b/lean/dk_math/docs/dev/cf-wallis-bridge-260704/cf-wallis-final-chain.md
@@ -23,3 +23,18 @@ central binomial ratio * mirror product
   = finite cosmic gap product
   -> Real.pi / 2
 ```
+
+## Conditional product caveat
+
+The infinite-product theorem in Lean is an ordered / conditional product:
+
+```text
+HasProd factor (Real.pi / 2) (SummationFilter.conditional Nat)
+```
+
+For `Nat`, this is exactly the classical exhaustion by `Finset.range m`.
+This matches the usual Wallis partial products.
+
+The default `HasProd` in Mathlib is unordered / unconditional.  We do not
+claim that stronger form here.  An unconditional Wallis-Cosmic product would
+require a separate absolute or log-product summability argument.
````
`````
