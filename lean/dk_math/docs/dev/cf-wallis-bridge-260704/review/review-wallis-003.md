# Git diff / Report / Review

## Upd: DkMath.Pascal.WallisCosmicPetalBridge

gch: 07b4c4042e99bd9c1471b1b0c4139b3953b1a7c7

## Report

追加しました。

[WallisCosmicPetalBridge.lean](/lean/dk_math/DkMath/Pascal/WallisCosmicPetalBridge.lean:152) に中間定理:

```lean
theorem centralRatioQ_mul_mirror_eq_wallisPartialQ (m : ℕ) :
    centralRatioQ m * mirrorOddRatioPartialQ m = wallisPartialQ m
```

を追加しました。既存の最終定理 `centralRatioQ_mul_mirror_eq_cosmicPartialQ` はそのまま残し、`π`・極限・漸近・Wallis 収束は入れていません。

確認済み:

```sh
lake build DkMath.Pascal.WallisCosmicPetalBridge
lake build DkMath.Pascal
git diff --check
```

## Review

## 結論

うむ、`review-wallis-003` は **採用でよい** 。
前回わっちが欲しがった中間定理

```lean
theorem centralRatioQ_mul_mirror_eq_wallisPartialQ (m : ℕ) :
    centralRatioQ m * mirrorOddRatioPartialQ m = wallisPartialQ m
```

がそのまま追加され、既存の最終定理 `centralRatioQ_mul_mirror_eq_cosmicPartialQ` も維持されておる。報告どおり、今回も `π`・極限・漸近・Wallis 収束は入れていないので、有限代数層としての純度も保たれている。

## 実装評価

これは小さい差分じゃが、意味は大きい。

いま橋の流れが完全に見えるようになった。

```text
centralRatioQ * mirrorOddRatioPartialQ
  -> wallisPartialQ
  -> cosmicPartialQ
```

つまり、

$$
\frac{2^{2m}}{\binom{2m}{m}}\prod_{j=1}^{m}\frac{2j}{2j+1}
$$

が、まず有限 Wallis 積へ行き、そこから宇宙式 Petal 積へ行く。この中間点を公開定理として置いたのは正解じゃ。

最新報告では `lake build DkMath.Pascal.WallisCosmicPetalBridge` と `lake build DkMath.Pascal` と `git diff --check` が成功している。トップレベル import まで前回通っているなら十分じゃが、次の大きめ差分では `lake build DkMath` も最後に走らせるのがよい。

## ここからは攻めてよい

ぬしよ、了解じゃ。
たしかに、ここはもう遠慮せず **もりもり実装指示** を出してよい段階じゃな。

今回の有限層は閉じておる。ならば次は、単に「壊さない」ではなく、 **後続が暴れられる足場** を増やすべきじゃ。

攻め筋は 4 本ある。

## 1. 有限積 API を厚くする

まず `wallisFactorQ`, `cosmicFactorQ`, `centralRatioQ`, `mirrorOddRatioPartialQ` の周辺に、使い回ししやすい補題を増やす。

欲しいのはこのあたりじゃ。

```lean
theorem wallisPartialQ_eq_prod_factor (m : ℕ) :
    wallisPartialQ m =
      ∏ k ∈ Finset.range m, wallisFactorQ k := rfl

theorem cosmicPartialQ_eq_prod_factor (m : ℕ) :
    cosmicPartialQ m =
      ∏ k ∈ Finset.range m, cosmicFactorQ k := rfl

theorem wallisFactorQ_eq_one_add_inv_body (k : ℕ) :
    wallisFactorQ k = 1 + 1 / cosmicBodyQ k := by
  ...

theorem cosmicFactorQ_eq_one_add_inv_body (k : ℕ) :
    cosmicFactorQ k = 1 + 1 / cosmicBodyQ k := by
  ...
```

ここで

$$
\frac{(P+1)^2}{P(P+2)}=1+\frac{1}{P(P+2)}
$$

を Lean に固定する。
これは宇宙式らしさが一気に増す。Wallis 因子がただの比ではなく、 **Gap 比率 $1+1/N$** として公開されるからじゃ。

## 2. 正値・非零・分母安全補題を入れる

次に、`field_simp` や将来の不等式・極限で必要になる安全補題を増やす。

```lean
theorem oddLeftQ_pos (k : ℕ) : 0 < oddLeftQ k := by
  ...

theorem evenCenterQ_pos (k : ℕ) : 0 < evenCenterQ k := by
  ...

theorem oddRightQ_pos (k : ℕ) : 0 < oddRightQ k := by
  ...

theorem cosmicBodyQ_pos (k : ℕ) : 0 < cosmicBodyQ k := by
  ...

theorem wallisFactorQ_pos (k : ℕ) : 0 < wallisFactorQ k := by
  ...

theorem cosmicFactorQ_pos (k : ℕ) : 0 < cosmicFactorQ k := by
  ...

theorem wallisPartialQ_pos (m : ℕ) : 0 < wallisPartialQ m := by
  ...

theorem cosmicPartialQ_pos (m : ℕ) : 0 < cosmicPartialQ m := by
  ...
```

これは地味じゃが強い。
あとで極限や単調性に入ると、分母非零で何度も足を取られる。ここで根こそぎ潰しておくのじゃ。

## 3. 単調性・上界下界へ攻める

Wallis 因子は各項が 1 より大きい。

$$
\frac{(2j)^2}{(2j-1)(2j+1)}>1
$$

なぜなら分母は

$$
(2j-1)(2j+1)=(2j)^2-1
$$

だからじゃ。

Lean 側ではこういう補題が欲しい。

```lean
theorem one_lt_wallisFactorQ (k : ℕ) :
    1 < wallisFactorQ k := by
  ...

theorem one_lt_cosmicFactorQ (k : ℕ) :
    1 < cosmicFactorQ k := by
  ...

theorem wallisPartialQ_mono :
    Monotone wallisPartialQ := by
  ...

theorem cosmicPartialQ_mono :
    Monotone cosmicPartialQ := by
  ...
```

ここまで入ると、有限積は単なる恒等式ではなく、 **成長する Gap 積** として動き始める。

## 4. 極限層へ入る準備ファイルを作る

そろそろ別ファイルを切ってよい。

```text
DkMath/Pascal/WallisLimitBridge.lean
```

ただし、いきなり完全証明を要求するより、Lean Sandbox で探索させる。Mathlib に Wallis 積の既存定理があるか、`Real.pi` 周辺に使えるものがあるか、まず探索じゃ。

最初の目標はこれでよい。

```lean
import Mathlib
import DkMath.Pascal.WallisCosmicPetalBridge

namespace DkMath.Pascal.WallisLimitBridge

open scoped BigOperators

-- TODO: locate Mathlib's Wallis product theorem if available.
-- Target shape:
-- Tendsto wallisPartialQ atTop (𝓝 (Real.pi / 2))

end DkMath.Pascal.WallisLimitBridge
```

もし既存定理が見つかれば接続。見つからなければ、有限層の準備だけして一旦止める。
でも探索はさせてよい。Codex には Sandbox がある。噛ませてよいのじゃ。

## Codex 向け指示

````text
Continue from gch 07b4c4042e99bd9c1471b1b0c4139b3953b1a7c7.

Review result: accepted. The intermediate theorem
`centralRatioQ_mul_mirror_eq_wallisPartialQ` is exactly the right bridge point.

Now proceed more aggressively. The finite algebraic layer is stable enough to expand.

Goals:

1. Keep `DkMath.Pascal.WallisCosmicPetalBridge` as the finite algebraic module.
   Do not add limits, `π`, asymptotics, or Wallis convergence here.

2. Add finite-factor API lemmas.

   Suggested lemmas:

   ```lean
   theorem wallisFactorQ_eq_one_add_inv_body (k : ℕ) :
       wallisFactorQ k = 1 + 1 / cosmicBodyQ k := by
     ...

   theorem cosmicFactorQ_eq_one_add_inv_body (k : ℕ) :
       cosmicFactorQ k = 1 + 1 / cosmicBodyQ k := by
     ...
````

These should expose the Cosmic Formula reading

```text
wallis factor = cosmic factor = (N + 1) / N = 1 + 1 / N
```

where `N = cosmicBodyQ k`.

1. Add positivity and nonzero safety lemmas for all basic factors.

   Suggested lemmas:

   ```lean
   theorem oddLeftQ_pos (k : ℕ) : 0 < oddLeftQ k := by ...
   theorem evenCenterQ_pos (k : ℕ) : 0 < evenCenterQ k := by ...
   theorem oddRightQ_pos (k : ℕ) : 0 < oddRightQ k := by ...
   theorem cosmicBodyQ_pos (k : ℕ) : 0 < cosmicBodyQ k := by ...

   theorem wallisFactorQ_pos (k : ℕ) : 0 < wallisFactorQ k := by ...
   theorem cosmicFactorQ_pos (k : ℕ) : 0 < cosmicFactorQ k := by ...

   theorem centralOddRatioPartialQ_pos (m : ℕ) :
       0 < centralOddRatioPartialQ m := by ...

   theorem mirrorOddRatioPartialQ_pos (m : ℕ) :
       0 < mirrorOddRatioPartialQ m := by ...

   theorem wallisPartialQ_pos (m : ℕ) :
       0 < wallisPartialQ m := by ...

   theorem cosmicPartialQ_pos (m : ℕ) :
       0 < cosmicPartialQ m := by ...

   theorem centralRatioQ_pos (m : ℕ) :
       0 < centralRatioQ m := by ...
   ```

   Use these to reduce future `field_simp` and inequality friction.

2. Add growth lemmas if they close cleanly.

   Suggested lemmas:

   ```lean
   theorem one_lt_wallisFactorQ (k : ℕ) :
       1 < wallisFactorQ k := by ...

   theorem one_lt_cosmicFactorQ (k : ℕ) :
       1 < cosmicFactorQ k := by ...

   theorem one_le_wallisPartialQ (m : ℕ) :
       1 ≤ wallisPartialQ m := by ...

   theorem one_le_cosmicPartialQ (m : ℕ) :
       1 ≤ cosmicPartialQ m := by ...
   ```

   If `Monotone` is easy, also try:

   ```lean
   theorem wallisPartialQ_mono : Monotone wallisPartialQ := by ...
   theorem cosmicPartialQ_mono : Monotone cosmicPartialQ := by ...
   ```

   Do not spend too long if `Monotone` becomes annoying; positivity and `1 < factor` are higher priority.

3. Create a separate exploratory module for the limit layer:

   ```text
   DkMath/Pascal/WallisLimitBridge.lean
   ```

   Initial content:

   ```lean
   import Mathlib
   import DkMath.Pascal.WallisCosmicPetalBridge

   namespace DkMath.Pascal.WallisLimitBridge

   open scoped BigOperators

   -- Explore Mathlib for an existing Wallis product theorem.
   -- Target shape, if available:
   -- Tendsto wallisPartialQ atTop (𝓝 (Real.pi / 2))

   end DkMath.Pascal.WallisLimitBridge
   ```

   Use Lean Sandbox / grep / search to find whether Mathlib already has a Wallis product theorem.
   Try names involving:

   * `Wallis`
   * `wallis`
   * `tendsto`
   * `Real.pi`
   * `centralBinomial`
   * `choose`
   * `factorial`

   If an existing theorem is found, add a thin bridge theorem.
   If no theorem is found quickly, leave the module with a documented TODO and keep all finite work no-sorry.

4. Build gates:

   Run:

   ```sh
   lake build DkMath.Pascal.WallisCosmicPetalBridge
   lake build DkMath.Pascal
   lake build DkMath
   git diff --check
   ```

5. Keep theorem names explicit and searchable.
   This Wallis bridge is becoming a reusable Pascal/CosmicFormula junction, so prefer descriptive names over short names.

```

これでよい。  
小さく守る段階は終わった。次は **有限因子を API として太らせる** 段じゃ。牙を出してよいぞい。
```

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Pascal/WallisCosmicPetalBridge.lean b/lean/dk_math/DkMath/Pascal/WallisCosmicPetalBridge.lean
index 965eb525..d0530451 100644
--- a/lean/dk_math/DkMath/Pascal/WallisCosmicPetalBridge.lean
+++ b/lean/dk_math/DkMath/Pascal/WallisCosmicPetalBridge.lean
@@ -149,6 +149,12 @@ theorem centralOdd_mul_mirror_eq_wallisPartialQ (m : ℕ) :
   rw [← Finset.prod_mul_distrib]
   exact Finset.prod_congr rfl fun k _ => halfFactor_mul_eq_wallisFactorQ k
 
+/-- The central binomial ratio times the mirror product equals the finite Wallis product. -/
+theorem centralRatioQ_mul_mirror_eq_wallisPartialQ (m : ℕ) :
+    centralRatioQ m * mirrorOddRatioPartialQ m = wallisPartialQ m := by
+  rw [centralRatioQ_eq_centralOddRatioPartialQ,
+    centralOdd_mul_mirror_eq_wallisPartialQ]
+
 /--
 The finite Wallis-Cosmic Petal bridge:
 the central odd half-product times its mirror equals the cosmic gap product.
````
`````
