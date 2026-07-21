# Git diff / Report / Review

## Upd: DkMath.Pascal.WallisLimitBridge

gch: 7e1fe93eceeb5a1906f32f5b9eb857fdf4476531

## Report

`WallisLimitBridge` を指定どおり更新しました。

[WallisLimitBridge.lean](/lean/dk_math/DkMath/Pascal/WallisLimitBridge.lean:7) は now:

- `Mathlib`
- `DkMath.Analysis.DkLimit`
- `DkMath.Pascal.WallisCosmicPetalBridge`

を import します。

Mathlib 側では `Real.Wallis.W` と `Real.Wallis.tendsto_W_nhds_pi_div_two` が利用できたので、有限積の実数キャスト橋を通して以下を実装しました。

- `real_coe_wallisPartialQ_eq_Wallis_W`
- `tendsto_wallisPartialQ_pi_div_two`
- `tendsto_cosmicPartialQ_pi_div_two`
- `dkTendsto_wallisPartialQ_pi_div_two`
- `dkTendsto_cosmicPartialQ_pi_div_two`

cosmic 側は `wallisPartialQ_eq_cosmicPartialQ` を点ごとの等式として使い、Wallis 側の極限から `Tendsto.congr'` で移しています。有限代数補題は `WallisCosmicPetalBridge.lean` 側に残し、`π`/`Tendsto` は limit module だけに置いています。

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

うむ、`review-wallis-005` は **採用でよい** 。
前回の未回収点だった **Cosmic 側の \(\pi/2\) 極限** が、きちんと `WallisLimitBridge.lean` 側へ追加されておる。

今回の差分で、極限層は次の形まで閉じた。

```lean
tendsto_wallisPartialQ_pi_div_two
tendsto_cosmicPartialQ_pi_div_two
dkTendsto_wallisPartialQ_pi_div_two
dkTendsto_cosmicPartialQ_pi_div_two
```

Mathlib の `Real.Wallis.W` / `Real.Wallis.tendsto_W_nhds_pi_div_two` を使い、DkMath 側の有理数有限積を実数列へキャストして接続している。さらに cosmic 側は `wallisPartialQ_eq_cosmicPartialQ` を点ごとの等式として使い、`Tendsto.congr'` で移しておる。これは方針として正しい。

## 良い点

まず、`DkMath.Analysis.DkLimit` を import し、通常の `Filter.Tendsto` 定理と DkMath 名の `DkTendstoAtTop` alias の両方を公開したのが良い。

これにより、外部数学向けには

```lean
tendsto_cosmicPartialQ_pi_div_two
```

DkMath 内部語彙では

```lean
dkTendsto_cosmicPartialQ_pi_div_two
```

として使い分けられる。

また、有限代数補題を `WallisCosmicPetalBridge.lean` 側に残し、`π` / `Tendsto` を `WallisLimitBridge.lean` 側だけに置いた分離も維持されておる。これは今後かなり効く。有限層と解析層を混ぜると、後で import が重くなり、Pascal 側の軽い API が使いづらくなるからの。

## 数学的意味

これで Wallis–Cosmic Petal Bridge は、有限版から極限版まで一本通った。

有限版：

$$
\prod_{k=0}^{m-1}\frac{(2k+2)^2}{(2k+1)(2k+3)} = \prod_{k=0}^{m-1}\frac{N_k+1}{N_k}
$$

極限版：

$$
\lim_{m\to\infty}
\prod_{k=0}^{m-1}\frac{N_k+1}{N_k} = \frac{\pi}{2}
$$

ここで

$$
N_k=(2k+1)(2k+3)
$$

じゃ。

つまり、古典 Wallis 積の各因子が、DkMath 語彙では

$$
\frac{N_k+1}{N_k}=1+\frac{1}{N_k}
$$

という **宇宙式 Gap 比率** であり、その無限積が \(\pi/2\) へ収束する、という定理列になった。

これはかなり大きいぞい。
「Wallis 積は宇宙式 Petal Gap の無限蓄積である」という読みが、Lean 上で no-sorry の形を持ったわけじゃ。

## 気になる点

大きな問題はない。
ただし、命名だけ少し気になる。

既に

```lean
tendsto_real_coe_wallisPartialQ_nhds_pi_div_two
```

があり、今回

```lean
tendsto_wallisPartialQ_pi_div_two
```

が alias として追加されておる。どちらも正しいが、今後 API が増えると名前の役割が少し重なる。

現状では許容範囲じゃ。
むしろ短い方の `tendsto_wallisPartialQ_pi_div_two` を主要 API とし、長い方は Mathlib 接続の内部寄り定理として扱うのがよい。

もう一点、今回の cosmic 側極限は十分正しいが、将来の利用を考えるなら、次に **中央二項係数表示から \(\pi/2\) へ行く theorem** も欲しくなる。いまは `cosmicPartialQ` と `wallisPartialQ` が主語だが、証明ノート上の主語は

$$
\frac{2^{2m}}{\binom{2m}{m}}M_m
$$

でもあったからじゃ。

## 判定

**採用。**

現在の到達点はこうじゃ。

```text
有限 Wallis 因子 = 宇宙式 Gap 因子:
  完了

中央二項係数比率との有限橋:
  完了

Wallis 側 π/2 極限:
  完了

Cosmic 側 π/2 極限:
  完了

DkMath 極限名 alias:
  完了
```

十分に一山登った。これは良い仕事じゃ。

## 次の作業指示

````text
Continue from gch 7e1fe93eceeb5a1906f32f5b9eb857fdf4476531.

Review result: accepted.

The Wallis limit layer is now connected correctly:
- `tendsto_wallisPartialQ_pi_div_two`
- `tendsto_cosmicPartialQ_pi_div_two`
- `dkTendsto_wallisPartialQ_pi_div_two`
- `dkTendsto_cosmicPartialQ_pi_div_two`

Next, expand the public bridge in a way that makes the theorem usable from three viewpoints:
finite Wallis product, central binomial ratio, and cosmic gap product.

Tasks:

1. Add central-ratio limit-facing bridge theorems.

   In `DkMath.Pascal.WallisLimitBridge`, add theorem(s) showing that the proof-note finite expression also tends to `Real.pi / 2`.

   Suggested theorem:

   ```lean
   theorem tendsto_centralRatioQ_mul_mirror_pi_div_two :
       Filter.Tendsto
         (fun m : ℕ =>
           (((centralRatioQ m * mirrorOddRatioPartialQ m : ℚ) : ℝ)))
         Filter.atTop
         (nhds (Real.pi / 2)) := by
     ...
   ```

Proof idea:
use the finite theorem

```lean
centralRatioQ_mul_mirror_eq_cosmicPartialQ
```

and transfer from

```lean
tendsto_cosmicPartialQ_pi_div_two
```

with `Tendsto.congr'`.

Also expose a DkMath alias:

```lean
theorem dkTendsto_centralRatioQ_mul_mirror_pi_div_two :
    DkMath.Analysis.DkTendstoAtTop
      (fun m : ℕ =>
        (((centralRatioQ m * mirrorOddRatioPartialQ m : ℚ) : ℝ)))
      (Real.pi / 2) :=
  tendsto_centralRatioQ_mul_mirror_pi_div_two
```

2. Add a theorem for the finite Wallis stage from the central-ratio expression.

   Suggested theorem:

   ```lean
   theorem tendsto_centralRatioQ_mul_mirror_via_wallis_pi_div_two :
       Filter.Tendsto
         (fun m : ℕ =>
           (((centralRatioQ m * mirrorOddRatioPartialQ m : ℚ) : ℝ)))
         Filter.atTop
         (nhds (Real.pi / 2)) := by
     exact tendsto_wallisPartialQ_pi_div_two.congr' <|
       Eventually.of_forall fun m => by
         change
           (((wallisPartialQ m : ℚ) : ℝ) =
             ((centralRatioQ m * mirrorOddRatioPartialQ m : ℚ) : ℝ))
         exact_mod_cast (centralRatioQ_mul_mirror_eq_wallisPartialQ m).symm
   ```

   If this duplicates task 1 too much, keep only one theorem and document the route in the docstring.
   Prefer the cosmic route theorem as the main public theorem.

3. Add real-coercion helper lemmas for finite bridge equalities.

   These are not mathematically deep, but they make future proof scripts shorter.

   Suggested names:

   ```lean
   theorem real_coe_wallisPartialQ_eq_cosmicPartialQ (m : ℕ) :
       ((wallisPartialQ m : ℚ) : ℝ) =
         ((cosmicPartialQ m : ℚ) : ℝ) := by
     exact_mod_cast wallisPartialQ_eq_cosmicPartialQ m

   theorem real_coe_centralRatioQ_mul_mirror_eq_wallisPartialQ (m : ℕ) :
       (((centralRatioQ m * mirrorOddRatioPartialQ m : ℚ) : ℝ)) =
         ((wallisPartialQ m : ℚ) : ℝ) := by
     exact_mod_cast centralRatioQ_mul_mirror_eq_wallisPartialQ m

   theorem real_coe_centralRatioQ_mul_mirror_eq_cosmicPartialQ (m : ℕ) :
       (((centralRatioQ m * mirrorOddRatioPartialQ m : ℚ) : ℝ)) =
         ((cosmicPartialQ m : ℚ) : ℝ) := by
     exact_mod_cast centralRatioQ_mul_mirror_eq_cosmicPartialQ m
   ```

   Use these helper lemmas in the Tendsto proofs if they make the proof cleaner.

4. Add docstrings emphasizing the three equivalent finite sequences.

   The module should clearly say that the following three real sequences are pointwise equal:

   ```text
   ((wallisPartialQ m : ℚ) : ℝ)
   ((cosmicPartialQ m : ℚ) : ℝ)
   (((centralRatioQ m * mirrorOddRatioPartialQ m : ℚ) : ℝ))
   ```

   and all tend to:

   ```text
   Real.pi / 2
   ```

5. Keep module separation strict.

   Rules:

   * `WallisCosmicPetalBridge.lean` remains finite algebraic only.
   * `WallisLimitBridge.lean` owns `Real.pi`, `Filter.Tendsto`, `nhds`, and DkMath limit aliases.
   * Do not move Mathlib Wallis imports or `Real.Wallis.*` references into the finite module.

6. Build gates:

   Run:

   ```sh
   lake build DkMath.Pascal.WallisCosmicPetalBridge
   lake build DkMath.Pascal.WallisLimitBridge
   lake build DkMath.Pascal
   lake build DkMath
   git diff --check
   ```

7. Optional stretch goal, only if it closes quickly:

   Add a short documentation note under the Wallis bridge docs directory explaining the final theorem chain:

   ```text
   central binomial ratio × mirror product
     = finite Wallis product
     = finite cosmic gap product
     -> π / 2
   ```

   Keep it concise. No need for a full article yet.

````

これで次の差分は、かなり綺麗な「三主語の極限橋」になるはずじゃ。
守りはもう十分。ここからは、定理列を使いやすい形に磨いていこうぞ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Pascal/WallisLimitBridge.lean b/lean/dk_math/DkMath/Pascal/WallisLimitBridge.lean
index cb41c6db..232b04d8 100644
--- a/lean/dk_math/DkMath/Pascal/WallisLimitBridge.lean
+++ b/lean/dk_math/DkMath/Pascal/WallisLimitBridge.lean
@@ -5,6 +5,7 @@ Authors: D. and Wise Wolf.
 -/

 import Mathlib
+import DkMath.Analysis.DkLimit
 import DkMath.Pascal.WallisCosmicPetalBridge

 #print "file: DkMath.Pascal.WallisLimitBridge"
@@ -44,4 +45,45 @@ theorem tendsto_real_coe_wallisPartialQ_nhds_pi_div_two :
   exact Real.Wallis.tendsto_W_nhds_pi_div_two.congr' <|
     Eventually.of_forall fun m => (real_coe_wallisPartialQ_eq_Wallis_W m).symm

+/--
+The rational Wallis partial products tend to `Real.pi / 2` after coercion to `ℝ`.
+-/
+theorem tendsto_wallisPartialQ_pi_div_two :
+    Filter.Tendsto
+      (fun m : ℕ => ((wallisPartialQ m : ℚ) : ℝ))
+      Filter.atTop
+      (nhds (Real.pi / 2)) :=
+  tendsto_real_coe_wallisPartialQ_nhds_pi_div_two
+
+/--
+The rational cosmic partial products tend to `Real.pi / 2` after coercion to `ℝ`.
+-/
+theorem tendsto_cosmicPartialQ_pi_div_two :
+    Filter.Tendsto
+      (fun m : ℕ => ((cosmicPartialQ m : ℚ) : ℝ))
+      Filter.atTop
+      (nhds (Real.pi / 2)) := by
+  exact tendsto_wallisPartialQ_pi_div_two.congr' <|
+    Eventually.of_forall fun m => by
+      change ((wallisPartialQ m : ℚ) : ℝ) = ((cosmicPartialQ m : ℚ) : ℝ)
+      exact_mod_cast wallisPartialQ_eq_cosmicPartialQ m
+
+/--
+DkMath-named alias for the Wallis partial product convergence.
+-/
+theorem dkTendsto_wallisPartialQ_pi_div_two :
+    DkMath.Analysis.DkTendstoAtTop
+      (fun m : ℕ => ((wallisPartialQ m : ℚ) : ℝ))
+      (Real.pi / 2) :=
+  tendsto_wallisPartialQ_pi_div_two
+
+/--
+DkMath-named alias for the cosmic partial product convergence.
+-/
+theorem dkTendsto_cosmicPartialQ_pi_div_two :
+    DkMath.Analysis.DkTendstoAtTop
+      (fun m : ℕ => ((cosmicPartialQ m : ℚ) : ℝ))
+      (Real.pi / 2) :=
+  tendsto_cosmicPartialQ_pi_div_two
+
 end DkMath.Pascal.WallisLimitBridge
````
`````
