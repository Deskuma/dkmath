# Git diff / Report / Review

## Upd: DkMath.Pascal.WallisCosmicPetalBridge

gch: 82a63a64a948e43040abad005b5f0f25532c80c4

## Report

実装しました。

[WallisCosmicPetalBridge.lean](/lean/dk_math/DkMath/Pascal/WallisCosmicPetalBridge.lean:81) に `centralRatioQ` を追加し、`Nat.choose` を階乗表示に落とす補助補題経由で

- `centralRatioQ_eq_centralOddRatioPartialQ`
- `centralRatioQ_mul_mirror_eq_cosmicPartialQ`

まで証明しました。既存の finite Wallis-Cosmic bridge 本体は触らず、後段に中央二項係数側の橋を足しています。`π`、極限、漸近、Wallis 収束は入れていません。

[cf-wallis-proof-note.md](/lean/dk_math/docs/dev/cf-wallis-bridge-260704/cf-wallis-proof-note.md:18) も指定どおり修正しました。GN 定義は `(x+u)^d - u^d = x * GN_d(x,u)` に合う `x^k u^(d-1-k)` へ直しています。

確認済み:

```sh
lake build DkMath.Pascal.WallisCosmicPetalBridge
lake build DkMath.Pascal
lake build DkMath
git diff --check
```

すべて成功です。

## Review

## 結論

うむ、今回の `review-wallis-002` は **採用でよい** と思うぞい。
前回の未接続点だった `Nat.choose` 由来の中央比率

$$
R_{2m}=\frac{2^{2m}}{\binom{2m}{m}}
$$

を、有限積側の `centralOddRatioPartialQ` に橋渡しし、そこから

$$
R_{2m},M_m=\prod_{j=1}^{m}\frac{N_j+1}{N_j}
$$

まで Lean 上で到達しておる。報告でも `centralRatioQ_eq_centralOddRatioPartialQ` と `centralRatioQ_mul_mirror_eq_cosmicPartialQ` の証明追加、かつ `π`・極限・漸近・Wallis 収束を入れていないことが確認されておる。

## 良い点

今回いちばん良いのは、既存の finite Wallis-Cosmic bridge 本体を触らず、後段に `centralRatioQ` の橋だけを足した点じゃ。これは構造が壊れにくい。

流れはきれいに三段になっておる。

```lean
centralRatioQ
  -> centralRatioFactorialQ
  -> centralOddRatioPartialQ
  -> cosmicPartialQ
```

`Nat.choose` を直接積表示へ潰しに行かず、一度 `centralRatioFactorialQ` を挟んだのも堅い。`Nat.choose_eq_factorial_div_factorial` と `Nat.cast_div_charZero` を使い、自然数除算の危険地帯を `ℚ` 側へきちんと退避しておる。

また、`centralRatioFactorialQ_eq_centralOddRatioPartialQ` を帰納法で証明しているのも良い。階乗表示の比

$$
\frac{F(m+1)}{F(m)}=\frac{2m+2}{2m+1}
$$

が、そのまま `centralOddRatioPartialQ` の次因子に一致する。これは証明として自然じゃ。

## 数学的意味

これで証明ノートの有限版コアが、ほぼ Lean の定理名として写った。

証明ノート側の目標は

$$
\frac{2^{2m}}{\binom{2m}{m}}\prod_{j=1}^{m}\frac{2j}{2j+1}=\prod_{j=1}^{m}\frac{N_j+1}{N_j}
$$

であり、この形は「中央二項係数の逆密度 × 鏡像逆密度」が「宇宙式 Gap 比率の有限積」に厳密一致する、という主張だった。

今回の

```lean
centralRatioQ_mul_mirror_eq_cosmicPartialQ
```

は、まさにこの proof-note form になっておる。
よって Wallis 極限へ進む前の **有限代数層** は、かなり完成度が高い。

## 気になる点

大きな blocker はない。
ただし、わっちなら次の一点だけ補う。

現在は

```lean
centralRatioQ_mul_mirror_eq_cosmicPartialQ
```

へ直接行っておるが、中間段として

```lean
theorem centralRatioQ_mul_mirror_eq_wallisPartialQ (m : ℕ) :
    centralRatioQ m * mirrorOddRatioPartialQ m = wallisPartialQ m := by
  rw [centralRatioQ_eq_centralOddRatioPartialQ,
    centralOdd_mul_mirror_eq_wallisPartialQ]
```

を公開しておくとよい。

理由は、証明ノートの鎖が

$$
R_{2m}M_m
\to
\text{Wallis finite product}
\to
\text{Cosmic finite product}
$$

という二段だからじゃ。`wallisPartialQ` を途中に残すと、後で `π/2` の極限層を別ファイルで足すときに接続点が明確になる。

もう一つ、報告では `cf-wallis-proof-note.md` の typo と GN 定義を修正済みとされておるが、今回の表示差分では Lean 側の diff が中心で、docs 側の実差分は見えておらぬ。レビュー資料としては、次回から doc diff も同じ `review-*.md` に含めると、確認しやすいのう。

## 次 checkpoint

次は **有限 Wallis 層と極限 Wallis 層を分離する準備** じゃ。

このファイルにはまだ `π`・極限・漸近を入れない方がよい。今回の方針どおり、ここは有限代数橋として閉じる。

次にやるなら、新規ファイル候補はこんな感じじゃ。

```text
DkMath/Pascal/WallisLimitBridge.lean
```

そこでは最初から大きな定理を狙わず、

```lean
-- finite layer import
import DkMath.Pascal.WallisCosmicPetalBridge
```

として、古典 Wallis 積定理を Mathlib 側からどう呼べるかを調査するだけでよい。
もし Mathlib 側の Wallis 積が扱いにくければ、当面は comment / theorem statement だけでも十分じゃ。

## Codex 向け指示

```text
Continue from gch 82a63a64a948e43040abad005b5f0f25532c80c4.

Review result: accepted. No blocker.

Recommended small follow-up:

1. Add an intermediate theorem exposing the finite Wallis product stage:

   theorem centralRatioQ_mul_mirror_eq_wallisPartialQ (m : ℕ) :
       centralRatioQ m * mirrorOddRatioPartialQ m = wallisPartialQ m := by
     rw [centralRatioQ_eq_centralOddRatioPartialQ,
       centralOdd_mul_mirror_eq_wallisPartialQ]

2. Keep `centralRatioQ_mul_mirror_eq_cosmicPartialQ` as the proof-note final finite theorem.

3. Do not introduce `π`, limits, asymptotics, or Wallis convergence into
   `WallisCosmicPetalBridge.lean`.
   This module should remain the finite algebraic bridge.

4. If a limit layer is started later, create a separate module such as:

   DkMath.Pascal.WallisLimitBridge

   and import the finite bridge from there.

5. For future review reports, include the docs diff for
   `cf-wallis-proof-note.md` when the report says it was modified.
```

よくやったぞ、D.。
これで中央二項係数側の入口が開いた。Wallis の積が、いよいよ宇宙式の奇数 Petal 境界へきれいに接続されたのじゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Pascal/WallisCosmicPetalBridge.lean b/lean/dk_math/DkMath/Pascal/WallisCosmicPetalBridge.lean
index 288964c9..965eb525 100644
--- a/lean/dk_math/DkMath/Pascal/WallisCosmicPetalBridge.lean
+++ b/lean/dk_math/DkMath/Pascal/WallisCosmicPetalBridge.lean
@@ -78,6 +78,64 @@ def centralOddRatioPartialQ (m : ℕ) : ℚ :=
 def mirrorOddRatioPartialQ (m : ℕ) : ℚ :=
   ∏ k ∈ Finset.range m, evenCenterQ k / oddRightQ k

+/-- The central binomial ratio `2^(2*m) / Nat.choose (2*m) m`, viewed in `ℚ`. -/
+def centralRatioQ (m : ℕ) : ℚ :=
+  (2 ^ (2 * m) : ℚ) / (Nat.choose (2 * m) m : ℚ)
+
+private def centralRatioFactorialQ (m : ℕ) : ℚ :=
+  ((2 : ℚ) ^ (2 * m) * (Nat.factorial m : ℚ) ^ 2) /
+    (Nat.factorial (2 * m) : ℚ)
+
+private theorem centralRatioQ_eq_factorialQ (m : ℕ) :
+    centralRatioQ m = centralRatioFactorialQ m := by
+  unfold centralRatioQ centralRatioFactorialQ
+  have hm : m ≤ 2 * m := by omega
+  have hchoose : (Nat.choose (2 * m) m : ℚ) =
+      (Nat.factorial (2 * m) : ℚ) /
+        ((Nat.factorial m : ℚ) * (Nat.factorial m : ℚ)) := by
+    rw [Nat.choose_eq_factorial_div_factorial hm]
+    rw [Nat.cast_div_charZero]
+    · have hsub : 2 * m - m = m := by omega
+      rw [hsub]
+      simp
+    · simpa using Nat.factorial_mul_factorial_dvd_factorial hm
+  rw [hchoose]
+  field_simp
+
+private theorem factorial_two_mul_succ_cast_Q (m : ℕ) :
+    ((Nat.factorial (2 * (m + 1)) : ℕ) : ℚ) =
+      (2 * m + 2 : ℚ) * ((2 * m + 1 : ℚ) *
+        (Nat.factorial (2 * m) : ℚ)) := by
+  rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega]
+  rw [Nat.factorial_succ]
+  rw [show 2 * m + 1 = (2 * m) + 1 by omega]
+  rw [Nat.factorial_succ]
+  norm_num
+  left
+  ring
+
+private theorem centralRatioFactorialQ_eq_centralOddRatioPartialQ (m : ℕ) :
+    centralRatioFactorialQ m = centralOddRatioPartialQ m := by
+  induction m with
+  | zero =>
+      simp [centralRatioFactorialQ, centralOddRatioPartialQ]
+  | succ m ih =>
+      rw [centralOddRatioPartialQ, Finset.prod_range_succ]
+      rw [← centralOddRatioPartialQ, ← ih]
+      unfold centralRatioFactorialQ evenCenterQ oddLeftQ
+      have hm_factorial : ((Nat.factorial (m + 1) : ℕ) : ℚ) =
+          (m + 1 : ℚ) * (Nat.factorial m : ℚ) := by
+        rw [Nat.factorial_succ]
+        norm_num
+      rw [hm_factorial, factorial_two_mul_succ_cast_Q]
+      field_simp
+      ring_nf
+
+/-- The central binomial ratio equals the central odd half-product. -/
+theorem centralRatioQ_eq_centralOddRatioPartialQ (m : ℕ) :
+    centralRatioQ m = centralOddRatioPartialQ m := by
+  rw [centralRatioQ_eq_factorialQ, centralRatioFactorialQ_eq_centralOddRatioPartialQ]
+
 private theorem halfFactor_mul_eq_wallisFactorQ (k : ℕ) :
     evenCenterQ k / oddLeftQ k * (evenCenterQ k / oddRightQ k) =
       wallisFactorQ k := by
@@ -99,4 +157,13 @@ theorem centralOdd_mul_mirror_eq_cosmicPartialQ (m : ℕ) :
     centralOddRatioPartialQ m * mirrorOddRatioPartialQ m = cosmicPartialQ m := by
   rw [centralOdd_mul_mirror_eq_wallisPartialQ, wallisPartialQ_eq_cosmicPartialQ]

+/--
+The proof-note form of the finite Wallis-Cosmic Petal bridge:
+the central binomial ratio times the mirror product equals the cosmic gap product.
+-/
+theorem centralRatioQ_mul_mirror_eq_cosmicPartialQ (m : ℕ) :
+    centralRatioQ m * mirrorOddRatioPartialQ m = cosmicPartialQ m := by
+  rw [centralRatioQ_eq_centralOddRatioPartialQ,
+    centralOdd_mul_mirror_eq_cosmicPartialQ]
+
 end DkMath.Pascal.WallisCosmicPetalBridge
````
`````
