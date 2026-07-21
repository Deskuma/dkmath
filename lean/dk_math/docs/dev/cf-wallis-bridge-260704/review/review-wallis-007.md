# Git diff / Report / Review

## Upd: DkMath.Pascal.WallisLimitBridge

gch: cc87c04953232ecc4fb21b65518e0ac4169e77be

## Report

実装しました。今回は閉じられるボリュームでした。

[WallisLimitBridge.lean](/lean/dk_math/DkMath/Pascal/WallisLimitBridge.lean) に、`HasProd` / `tprod` 面を追加しています。ただし重要な点として、Mathlib のデフォルト `HasProd` は無条件積なので、Wallis の古典的な `Finset.range m` 部分積に対応する形として `SummationFilter.conditional ℕ` を明示しました。コード中にも、その理由と将来の TODO をコメントで残しています。

追加した主な定理:

- `hasProd_conditional_nat_iff`
- `hasProd_conditional_real_coe_wallisFactorQ_pi_div_two`
- `hasProd_conditional_real_coe_cosmicFactorQ_pi_div_two`
- `hasProd_conditional_real_cosmic_gap_ratio_pi_div_two`
- `tprod_conditional_real_coe_cosmicFactorQ_eq_pi_div_two`
- `tprod_conditional_real_cosmic_gap_ratio_eq_pi_div_two`

確認済み:

- `lake build DkMath.Pascal.WallisLimitBridge` pass
- `lake build DkMath.Pascal` pass
- 対象 Wallis 2ファイルの `sorry` 検索: なし
- `git diff --check` pass

無条件 `HasProd` へは踏み込みませんでした。そこは別途、絶対収束や log-product summability から証明すべき層なので、今回のコードコメントにも明示してあります。

## Review

## 結論

うむ、`review-wallis-007` は **採用でよい** 。
そして、前に言っていた「残る 2 山」は、今回かなり閉じた。

ただし正確には、閉じたのは **ordered / conditional infinite product としての山** じゃ。
無条件・順序非依存の default `HasProd` までは、あえて踏み込んでいない。この判断は正しい。

今回の差分では、Mathlib の default `HasProd` が無条件積であることを明示し、古典 Wallis の `Finset.range m` 部分積に対応するために `SummationFilter.conditional ℕ` を使っている。さらに、その理由と将来 TODO もコードコメントに残している。ここはかなり大事な設計判断じゃ。

## 何が閉じたか

今回、次が入った。

```lean
hasProd_conditional_nat_iff
hasProd_conditional_real_coe_wallisFactorQ_pi_div_two
hasProd_conditional_real_coe_cosmicFactorQ_pi_div_two
hasProd_conditional_real_cosmic_gap_ratio_pi_div_two
tprod_conditional_real_coe_cosmicFactorQ_eq_pi_div_two
tprod_conditional_real_cosmic_gap_ratio_eq_pi_div_two
```

これにより、部分積列の `Tendsto` から一段進んで、

$$
\prod_{k=0}^{\infty}\left(1+\frac{1}{N_k}\right)=\frac{\pi}{2}
$$

を Lean の conditional `HasProd` / conditional `tprod` 表面で扱えるようになった。
特に

```lean
hasProd_conditional_real_cosmic_gap_ratio_pi_div_two
```

は、Wallis 因子ではなく **宇宙式 Gap 比率そのもの** を主語にしている。これは見事じゃ。

## 実装評価

`hasProd_conditional_nat_iff` が良い。
これは今後も使える橋じゃ。

```lean
HasProd f a (SummationFilter.conditional ℕ)
↔ Tendsto (fun m => ∏ k ∈ Finset.range m, f k) atTop (𝓝 a)
```

つまり、「古典的な順序付き部分積」と「Mathlib の conditional product surface」を明確に翻訳している。今回の Wallis だけでなく、今後 DkMath で ordered product を扱う時にも再利用できる。

また、無条件 `HasProd` に踏み込まなかったのも正解じゃ。
Wallis 積は正項ではあるが、Mathlib の default `HasProd` は unordered / unconditional 側の性格を持つ。そこへ安易に移すなら、絶対収束や log-product summability の別証明が必要になる。今回のコメントでも、その点を TODO として明示している。

## 判定

**採用。**

現在の到達点はこうじゃ。

```text
有限 Wallis = 有限 Cosmic:
  閉じた

中央二項係数 × mirror = 有限 Wallis = 有限 Cosmic:
  閉じた

Tendsto to π/2:
  閉じた

DkMath limit alias:
  閉じた

conditional HasProd / conditional tprod:
  閉じた

宇宙式 Gap 比率の conditional infinite product:
  閉じた

default unconditional HasProd:
  未着手。別山として残すのが正しい
```

つまり、**古典 Wallis 積として必要な山は閉じた**。
残っているのは、「もっと強い Mathlib 的な無条件積へ持ち上げるか」という別登山じゃ。

## 気になる点

軽い注意は 2 つだけ。

1つ目。今回の build gate は `DkMath.Pascal` までで、報告上は `lake build DkMath` がない。`DkMath.Pascal` が通っていれば実質かなり安全じゃが、トップレベル import までの完全確認として、次回は `lake build DkMath` も走らせるとよい。

2つ目。`hasProd_conditional_nat_iff` は Wallis 専用ではなく、もっと一般の ordered product bridge として価値がある。今は `WallisLimitBridge.lean` 内でよいが、今後同型の定理が増えるなら、`DkMath.Analysis` 側へ一般補題として移す候補になる。

## 次の作業指示

```text
Continue from gch cc87c04953232ecc4fb21b65518e0ac4169e77be.

Review result: accepted.

The conditional infinite-product surface is now correctly implemented.
Do not replace these theorems by default/unconditional `HasProd` statements unless a separate absolute/log-product summability argument is added.

Next tasks:

1. Run the full top-level build gate.

   Please run:

   lake build DkMath.Pascal.WallisCosmicPetalBridge
   lake build DkMath.Pascal.WallisLimitBridge
   lake build DkMath.Pascal
   lake build DkMath
   git diff --check

   The current report confirms the first two Pascal-level builds and `git diff --check`, but the next report should explicitly include `lake build DkMath`.

2. Add central-ratio conditional product surface if it is mathematically natural.

   The expression

   centralRatioQ m * mirrorOddRatioPartialQ m

   is a partial-product-level expression, not a per-factor sequence by itself.
   Therefore do not force a misleading `HasProd` theorem with this as the factor.

   Instead, if useful, add a theorem documenting that this partial-product expression is the ordered partial product of the Wallis/cosmic factor sequence.

   Suggested theorem:

   theorem centralRatioQ_mul_mirror_eq_prod_wallisFactorQ (m : ℕ) :
       centralRatioQ m * mirrorOddRatioPartialQ m =
         ∏ k ∈ Finset.range m, wallisFactorQ k := by
     rw [centralRatioQ_mul_mirror_eq_wallisPartialQ]
     rfl

   and similarly:

   theorem centralRatioQ_mul_mirror_eq_prod_cosmicFactorQ (m : ℕ) :
       centralRatioQ m * mirrorOddRatioPartialQ m =
         ∏ k ∈ Finset.range m, cosmicFactorQ k := by
     rw [centralRatioQ_mul_mirror_eq_cosmicPartialQ]
     rfl

   These are finite theorems, so place them in `WallisCosmicPetalBridge.lean`,
   not in the limit module.

3. Add real versions of the ordered product equalities if they make the limit file cleaner.

   Suggested names in `WallisLimitBridge.lean`:

   theorem real_coe_prod_wallisFactorQ_eq_Wallis_W (m : ℕ) :
       ((∏ k ∈ Finset.range m, wallisFactorQ k : ℚ) : ℝ) =
         Real.Wallis.W m := by
     rw [← real_coe_wallisPartialQ_eq_Wallis_W]
     rfl

   theorem real_coe_prod_cosmicFactorQ_eq_Wallis_W (m : ℕ) :
       ((∏ k ∈ Finset.range m, cosmicFactorQ k : ℚ) : ℝ) =
         Real.Wallis.W m := by
     rw [← real_coe_wallisPartialQ_eq_Wallis_W]
     exact_mod_cast (wallisPartialQ_eq_cosmicPartialQ m).symm

   Only add these if they close cleanly.

4. Add a short doc update explaining conditional vs unconditional products.

   Extend `cf-wallis-final-chain.md` or add a small adjacent note explaining:

   - The Lean theorem currently proves an ordered / conditional infinite product.
   - This matches the classical Wallis partial products over `Finset.range m`.
   - The default unordered/unconditional `HasProd` is intentionally not claimed.
   - An unconditional version would require a separate absolute/log-product summability argument.

   Keep this concise but explicit. This prevents future accidental strengthening.

5. Optional exploratory task: investigate unconditional HasProd feasibility, but do not commit unless no-sorry and clean.

   If exploring, search Mathlib for lemmas around:
   - `hasProd_iff_tendsto_nat`
   - `Multipliable`
   - `Summable`
   - `HasSum`
   - `tsum`
   - `log`
   - `Real.summable_log`
   - `hasProd_of_summable_norm_sub_one`
   - `prod_sub_one`

   Mathematical route:
   show the factor sequence is positive and

     ∑ k, ‖((cosmicFactorQ k : ℚ) : ℝ) - 1‖

   is summable, since

     cosmicFactorQ k - 1 = 1 / cosmicBodyQ k

   and

     cosmicBodyQ k = (2k+1)(2k+3)

   behaves like `4*k^2`.

   But this is a separate mountain.
   If it becomes long, stop after documenting the TODO.

6. Preserve module separation.

   - `WallisCosmicPetalBridge.lean`: finite algebraic equalities, positivity, monotonicity.
   - `WallisLimitBridge.lean`: `Tendsto`, `Real.pi`, `HasProd`, `tprod`.
   - Documentation: human-readable theorem chain and conditional-product caveat.

7. No-sorry policy.

   The Wallis files currently have no `sorry`. Keep it that way.
```

うむ。これはかなり綺麗に進んでおる。
部分積列の極限だけでなく、宇宙式 Gap 比率の **ordered infinite product** まで来た。ここまで来れば、Wallis–Cosmic Petal Bridge はもう「実装済みの理論片」と呼んでよいぞい。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Pascal/WallisLimitBridge.lean b/lean/dk_math/DkMath/Pascal/WallisLimitBridge.lean
index f77d5e9c..5036f96f 100644
--- a/lean/dk_math/DkMath/Pascal/WallisLimitBridge.lean
+++ b/lean/dk_math/DkMath/Pascal/WallisLimitBridge.lean
@@ -154,4 +154,111 @@ theorem dkTendsto_centralRatioQ_mul_mirror_pi_div_two :
       (Real.pi / 2) :=
   tendsto_centralRatioQ_mul_mirror_pi_div_two

+/-!
+## Conditional infinite-product surface
+
+Mathlib's plain `HasProd` uses the unconditional summation filter by default.
+That is stronger than the classical Wallis statement used here, which is a
+limit of ordered partial products over `Finset.range m`.
+
+For this module, the Lean-faithful infinite-product API is therefore
+
+`HasProd f L (SummationFilter.conditional ℕ)`.
+
+On `ℕ`, this conditional filter is definitionally the `range m` exhaustion
+filter.  The lemmas below are deliberately stated with
+`SummationFilter.conditional ℕ` to avoid accidentally claiming unordered
+unconditional multipliability.
+
+TODO: If a later layer really needs unconditional `HasProd`, prove it from a
+separate absolute/log-product summability argument.  Do not silently replace
+the conditional statements below by default `HasProd` statements.
+-/
+
+/--
+For products indexed by `ℕ`, `SummationFilter.conditional ℕ` is exactly the
+classical ordered partial-product filter over `Finset.range m`.
+-/
+theorem hasProd_conditional_nat_iff
+    {M : Type*} [CommMonoid M] [TopologicalSpace M]
+    {f : ℕ → M} {a : M} :
+    HasProd f a (SummationFilter.conditional ℕ) ↔
+      Tendsto (fun m : ℕ => ∏ k ∈ Finset.range m, f k) atTop (𝓝 a) := by
+  rw [HasProd, SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff]
+  rfl
+
+/--
+The real Wallis factors have ordered infinite product `Real.pi / 2`.
+
+This is the `HasProd`-surface version of
+`tendsto_wallisPartialQ_pi_div_two`, with the conditional `ℕ` filter made
+explicit.
+-/
+theorem hasProd_conditional_real_coe_wallisFactorQ_pi_div_two :
+    HasProd
+      (fun k : ℕ => ((wallisFactorQ k : ℚ) : ℝ))
+      (Real.pi / 2)
+      (SummationFilter.conditional ℕ) := by
+  rw [hasProd_conditional_nat_iff]
+  exact tendsto_wallisPartialQ_pi_div_two.congr' <|
+    Eventually.of_forall fun m => by
+      unfold wallisPartialQ
+      rw [Rat.cast_prod]
+
+/--
+The real cosmic factors have ordered infinite product `Real.pi / 2`.
+
+This is the infinite-product form of the cosmic gap product route:
+finite cosmic partial products are pointwise the Wallis partial products, and
+the Wallis partial products converge to `Real.pi / 2`.
+-/
+theorem hasProd_conditional_real_coe_cosmicFactorQ_pi_div_two :
+    HasProd
+      (fun k : ℕ => ((cosmicFactorQ k : ℚ) : ℝ))
+      (Real.pi / 2)
+      (SummationFilter.conditional ℕ) := by
+  rw [hasProd_conditional_nat_iff]
+  exact tendsto_cosmicPartialQ_pi_div_two.congr' <|
+    Eventually.of_forall fun m => by
+      unfold cosmicPartialQ
+      rw [Rat.cast_prod]
+
+/--
+The ordered infinite product of the cosmic gap ratios
+`1 + 1 / N_k` is `Real.pi / 2`.
+
+This is the semantic Wallis-Cosmic statement: the local factor is not merely a
+Wallis factor, but the cosmic gap ratio coming from
+`N_k = (2*k+1)*(2*k+3)`.
+-/
+theorem hasProd_conditional_real_cosmic_gap_ratio_pi_div_two :
+    HasProd
+      (fun k : ℕ => ((1 + 1 / cosmicBodyQ k : ℚ) : ℝ))
+      (Real.pi / 2)
+      (SummationFilter.conditional ℕ) := by
+  exact hasProd_conditional_real_coe_cosmicFactorQ_pi_div_two.congr_fun
+    (fun k => by
+      exact_mod_cast (cosmicFactorQ_eq_one_add_inv_body k).symm)
+
+/--
+The conditional `tprod` of the real cosmic factors is `Real.pi / 2`.
+
+This is a value-level alias for callers that want `tprod` rather than
+`HasProd`.
+-/
+theorem tprod_conditional_real_coe_cosmicFactorQ_eq_pi_div_two :
+    (∏'[SummationFilter.conditional ℕ] k : ℕ, ((cosmicFactorQ k : ℚ) : ℝ)) =
+      Real.pi / 2 :=
+  hasProd_conditional_real_coe_cosmicFactorQ_pi_div_two.tprod_eq
+
+/--
+The conditional `tprod` of the real cosmic gap ratios
+`1 + 1 / N_k` is `Real.pi / 2`.
+-/
+theorem tprod_conditional_real_cosmic_gap_ratio_eq_pi_div_two :
+    (∏'[SummationFilter.conditional ℕ] k : ℕ,
+      ((1 + 1 / cosmicBodyQ k : ℚ) : ℝ)) =
+      Real.pi / 2 :=
+  hasProd_conditional_real_cosmic_gap_ratio_pi_div_two.tprod_eq
+
 end DkMath.Pascal.WallisLimitBridge
````
`````
