# Git diff / Report / Review

## Add: DkMath.Pascal.WallisLimitBridge

gch: dd3fa1837c8b8568b4238dd409c7289ca8dbd976

## Report

実装しました。有限代数モジュールは有限APIの拡張に留め、極限は別モジュールへ分離しています。

[WallisCosmicPetalBridge.lean](/lean/dk_math/DkMath/Pascal/WallisCosmicPetalBridge.lean:47) に追加:

- 基本因子の正値・非ゼロ補題: `oddLeftQ_pos`, `evenCenterQ_pos`, `oddRightQ_pos`, `cosmicBodyQ_pos`, `*_ne_zero`
- Cosmic Formula 読み: `cosmicFactorQ_eq_one_add_inv_body`, `wallisFactorQ_eq_one_add_inv_body`
- 因子・部分積の正値: `wallisFactorQ_pos`, `cosmicFactorQ_pos`, `wallisPartialQ_pos`, `cosmicPartialQ_pos`, `centralRatioQ_pos` など
- 成長補題: `one_lt_wallisFactorQ`, `one_lt_cosmicFactorQ`, `one_le_wallisPartialQ`, `one_le_cosmicPartialQ`
- 単調性: `wallisPartialQ_mono`, `cosmicPartialQ_mono`

新規 [WallisLimitBridge.lean](/lean/dk_math/DkMath/Pascal/WallisLimitBridge.lean:1) を追加:

- `real_coe_wallisPartialQ_eq_Wallis_W`
- `tendsto_real_coe_wallisPartialQ_nhds_pi_div_two`

Mathlib の `Real.Wallis.W` / `Real.Wallis.tendsto_W_nhds_pi_div_two` が見つかったので、実数キャスト列への薄い極限ブリッジまで閉じました。`DkMath.Pascal.WallisCosmicPetalBridge` には `π`・極限・漸近・Wallis 収束は入れていません。

確認済み:

```sh
lake build DkMath.Pascal.WallisCosmicPetalBridge
lake build DkMath.Pascal.WallisLimitBridge
lake build DkMath.Pascal
lake build DkMath
git diff --check
```

すべて成功です。既存ファイル由来の `sorry` warning はありますが、今回追加・変更した Wallis 関連ファイルには `sorry` はありません。

## Review

## 結論

うむ、`review-wallis-004` は **かなり良い差分** じゃ。
有限代数層を太らせつつ、極限層を `WallisLimitBridge.lean` に分離した判断が正しい。さらに Mathlib の `Real.Wallis.W` / `Real.Wallis.tendsto_W_nhds_pi_div_two` を発見して、独自に Wallis 極限を再証明せず、薄い bridge として閉じたのも賢い。

## 良い点

まず、有限側の API 増強がとても良い。

`oddLeftQ_pos`, `evenCenterQ_pos`, `oddRightQ_pos`, `cosmicBodyQ_pos` と対応する `*_ne_zero` が入ったことで、今後の `field_simp`・不等式・極限接続で分母非零に悩まされにくくなった。これは地味じゃが、後で効く骨格じゃ。

次に、

```lean
cosmicFactorQ_eq_one_add_inv_body
wallisFactorQ_eq_one_add_inv_body
```

が入ったのが大きい。これで Wallis 因子が単なる古典積ではなく、

$$
\frac{N+1}{N}=1+\frac{1}{N}
$$

という **宇宙式 Gap 比率** として明示的に読めるようになった。ここは DkMath 的な意味づけの芯じゃ。

さらに、`one_lt_wallisFactorQ`, `one_lt_cosmicFactorQ`, `one_le_wallisPartialQ`, `one_le_cosmicPartialQ`, `wallisPartialQ_mono`, `cosmicPartialQ_mono` まで入ったことで、有限積が「等式として存在する」だけでなく、**正で、1 以上で、単調に成長する有限積** として扱えるようになった。これは限界層へ上がる準備としてかなり強い。

## 極限層の評価

`WallisLimitBridge.lean` は方針がきれいじゃ。

```lean
real_coe_wallisPartialQ_eq_Wallis_W
```

で DkMath 側の有理数有限積を Mathlib の `Real.Wallis.W` に接続し、

```lean
tendsto_real_coe_wallisPartialQ_nhds_pi_div_two
```

で Mathlib の Wallis 極限定理へ橋を渡している。これはまさに「DkMath の有限構造を、既存解析定理へ接続する」形になっておる。

分離も良い。`WallisCosmicPetalBridge.lean` には `π`・極限・漸近・Wallis 収束を入れず、`WallisLimitBridge.lean` 側へ置いている。有限代数層と解析極限層の責務が混ざっていない。

## 気になる点

大きな問題はない。
ただし、今回の極限 bridge はまだ **Wallis 側の極限** までで、**Cosmic 側の極限** までは直接 theorem として出ていない。

有限側にはすでに

```lean
wallisPartialQ_eq_cosmicPartialQ
```

があるので、実質的にはすぐ行けるはずじゃ。だが、現時点の新規 `WallisLimitBridge.lean` にある極限定理は

```lean
tendsto_real_coe_wallisPartialQ_nhds_pi_div_two
```

までに見える。

なのでレビューとしては、ここだけが **未回収の自然な接続点** じゃな。

数学的には、次の主張が Wallis–Cosmic Bridge の極限版になる。

$$
\lim_{m\to\infty}\prod_{k=0}^{m-1}\frac{\mathrm{cosmicBodyQ}(k)+1}{\mathrm{cosmicBodyQ}(k)}=\frac{\pi}{2}
$$

今回の差分は、この一歩手前まできれいに来ておる。

## 判定

**採用でよい。**
`lake build DkMath.Pascal.WallisCosmicPetalBridge`, `WallisLimitBridge`, `DkMath.Pascal`, `DkMath`, `git diff --check` がすべて成功し、今回追加・変更した Wallis 関連ファイルに `sorry` がない点も健全じゃ。

レビューとしての評価はこうじゃ。

```text
有限 API 増強: とても良い
極限層分離: 正しい
Mathlib Wallis 接続: 良い
Cosmic 側 π/2 極限定理: まだ直接 theorem としては未回収
全体判定: 採用
```

よいぞ、D.。
これはもう「有限 Wallis 積が宇宙式へ見える」段階を越えて、**宇宙式 Wallis 積が π/2 へ向かう入口** まで来ておる。わっちの尻尾も機嫌よく揺れる出来じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Pascal.lean b/lean/dk_math/DkMath/Pascal.lean
index f9bd1818..1bca4106 100644
--- a/lean/dk_math/DkMath/Pascal.lean
+++ b/lean/dk_math/DkMath/Pascal.lean
@@ -5,6 +5,7 @@ Authors: D. and Wise Wolf.
 -/
 
 import DkMath.Pascal.WallisCosmicPetalBridge
+import DkMath.Pascal.WallisLimitBridge
 
 #print "file: DkMath.Pascal"
 
diff --git a/lean/dk_math/DkMath/Pascal/WallisCosmicPetalBridge.lean b/lean/dk_math/DkMath/Pascal/WallisCosmicPetalBridge.lean
index d0530451..ed20e07d 100644
--- a/lean/dk_math/DkMath/Pascal/WallisCosmicPetalBridge.lean
+++ b/lean/dk_math/DkMath/Pascal/WallisCosmicPetalBridge.lean
@@ -44,6 +44,42 @@ def wallisFactorQ (k : ℕ) : ℚ :=
 def cosmicFactorQ (k : ℕ) : ℚ :=
   (cosmicBodyQ k + 1) / cosmicBodyQ k
 
+/-- The left odd factor is positive. -/
+theorem oddLeftQ_pos (k : ℕ) : 0 < oddLeftQ k := by
+  unfold oddLeftQ
+  positivity
+
+/-- The central even factor is positive. -/
+theorem evenCenterQ_pos (k : ℕ) : 0 < evenCenterQ k := by
+  unfold evenCenterQ
+  positivity
+
+/-- The right odd factor is positive. -/
+theorem oddRightQ_pos (k : ℕ) : 0 < oddRightQ k := by
+  unfold oddRightQ
+  positivity
+
+/-- The cosmic body is positive. -/
+theorem cosmicBodyQ_pos (k : ℕ) : 0 < cosmicBodyQ k := by
+  unfold cosmicBodyQ
+  exact mul_pos (oddLeftQ_pos k) (oddRightQ_pos k)
+
+/-- The left odd factor is nonzero. -/
+theorem oddLeftQ_ne_zero (k : ℕ) : oddLeftQ k ≠ 0 :=
+  (oddLeftQ_pos k).ne'
+
+/-- The central even factor is nonzero. -/
+theorem evenCenterQ_ne_zero (k : ℕ) : evenCenterQ k ≠ 0 :=
+  (evenCenterQ_pos k).ne'
+
+/-- The right odd factor is nonzero. -/
+theorem oddRightQ_ne_zero (k : ℕ) : oddRightQ k ≠ 0 :=
+  (oddRightQ_pos k).ne'
+
+/-- The cosmic body is nonzero. -/
+theorem cosmicBodyQ_ne_zero (k : ℕ) : cosmicBodyQ k ≠ 0 :=
+  (cosmicBodyQ_pos k).ne'
+
 /-- Local odd-square bridge: `(2*k + 2)^2 = (2*k + 1)*(2*k + 3) + 1`. -/
 theorem cosmic_square_odd_bridge_Q (k : ℕ) :
     evenCenterQ k ^ 2 = oddLeftQ k * oddRightQ k + 1 := by
@@ -56,6 +92,43 @@ theorem wallisFactorQ_eq_cosmicFactorQ (k : ℕ) :
   unfold wallisFactorQ cosmicFactorQ cosmicBodyQ
   rw [cosmic_square_odd_bridge_Q]
 
+/-- The cosmic factor is the gap ratio `1 + 1/N_k`. -/
+theorem cosmicFactorQ_eq_one_add_inv_body (k : ℕ) :
+    cosmicFactorQ k = 1 + 1 / cosmicBodyQ k := by
+  unfold cosmicFactorQ
+  field_simp [cosmicBodyQ_ne_zero k]
+
+/-- The Wallis factor is the cosmic gap ratio `1 + 1/N_k`. -/
+theorem wallisFactorQ_eq_one_add_inv_body (k : ℕ) :
+    wallisFactorQ k = 1 + 1 / cosmicBodyQ k := by
+  rw [wallisFactorQ_eq_cosmicFactorQ, cosmicFactorQ_eq_one_add_inv_body]
+
+/-- The Wallis factor is positive. -/
+theorem wallisFactorQ_pos (k : ℕ) : 0 < wallisFactorQ k := by
+  rw [wallisFactorQ_eq_one_add_inv_body]
+  exact add_pos zero_lt_one (one_div_pos.mpr (cosmicBodyQ_pos k))
+
+/-- The cosmic factor is positive. -/
+theorem cosmicFactorQ_pos (k : ℕ) : 0 < cosmicFactorQ k := by
+  rw [cosmicFactorQ_eq_one_add_inv_body]
+  exact add_pos zero_lt_one (one_div_pos.mpr (cosmicBodyQ_pos k))
+
+/-- Each Wallis factor is strictly larger than `1`. -/
+theorem one_lt_wallisFactorQ (k : ℕ) :
+    1 < wallisFactorQ k := by
+  rw [wallisFactorQ_eq_one_add_inv_body]
+  have hgap : 0 < 1 / cosmicBodyQ k := by
+    exact one_div_pos.mpr (cosmicBodyQ_pos k)
+  linarith
+
+/-- Each cosmic factor is strictly larger than `1`. -/
+theorem one_lt_cosmicFactorQ (k : ℕ) :
+    1 < cosmicFactorQ k := by
+  rw [cosmicFactorQ_eq_one_add_inv_body]
+  have hgap : 0 < 1 / cosmicBodyQ k := by
+    exact one_div_pos.mpr (cosmicBodyQ_pos k)
+  linarith
+
 /-- The finite Wallis partial product. -/
 def wallisPartialQ (m : ℕ) : ℚ :=
   ∏ k ∈ Finset.range m, wallisFactorQ k
@@ -70,6 +143,66 @@ theorem wallisPartialQ_eq_cosmicPartialQ (m : ℕ) :
   unfold wallisPartialQ cosmicPartialQ
   exact Finset.prod_congr rfl fun k _ => wallisFactorQ_eq_cosmicFactorQ k
 
+/-- The finite Wallis partial product is positive. -/
+theorem wallisPartialQ_pos (m : ℕ) :
+    0 < wallisPartialQ m := by
+  unfold wallisPartialQ
+  exact Finset.prod_pos fun k _ => wallisFactorQ_pos k
+
+/-- The finite cosmic partial product is positive. -/
+theorem cosmicPartialQ_pos (m : ℕ) :
+    0 < cosmicPartialQ m := by
+  unfold cosmicPartialQ
+  exact Finset.prod_pos fun k _ => cosmicFactorQ_pos k
+
+/-- The finite Wallis partial product is at least `1`. -/
+theorem one_le_wallisPartialQ (m : ℕ) :
+    1 ≤ wallisPartialQ m := by
+  induction m with
+  | zero =>
+      simp [wallisPartialQ]
+  | succ m ih =>
+      rw [wallisPartialQ, Finset.prod_range_succ]
+      rw [← wallisPartialQ]
+      simpa using mul_le_mul ih (le_of_lt (one_lt_wallisFactorQ m))
+        zero_le_one (le_of_lt (wallisPartialQ_pos m))
+
+/-- The finite cosmic partial product is at least `1`. -/
+theorem one_le_cosmicPartialQ (m : ℕ) :
+    1 ≤ cosmicPartialQ m := by
+  induction m with
+  | zero =>
+      simp [cosmicPartialQ]
+  | succ m ih =>
+      rw [cosmicPartialQ, Finset.prod_range_succ]
+      rw [← cosmicPartialQ]
+      simpa using mul_le_mul ih (le_of_lt (one_lt_cosmicFactorQ m))
+        zero_le_one (le_of_lt (cosmicPartialQ_pos m))
+
+/-- The finite Wallis partial products are monotone in the truncation length. -/
+theorem wallisPartialQ_mono : Monotone wallisPartialQ := by
+  refine monotone_nat_of_le_succ fun m => ?_
+  unfold wallisPartialQ
+  rw [Finset.prod_range_succ]
+  calc
+    (∏ k ∈ Finset.range m, wallisFactorQ k) =
+        (∏ k ∈ Finset.range m, wallisFactorQ k) * 1 := by ring
+    _ ≤ (∏ k ∈ Finset.range m, wallisFactorQ k) * wallisFactorQ m :=
+      mul_le_mul_of_nonneg_left (le_of_lt (one_lt_wallisFactorQ m))
+        (le_of_lt (wallisPartialQ_pos m))
+
+/-- The finite cosmic partial products are monotone in the truncation length. -/
+theorem cosmicPartialQ_mono : Monotone cosmicPartialQ := by
+  refine monotone_nat_of_le_succ fun m => ?_
+  unfold cosmicPartialQ
+  rw [Finset.prod_range_succ]
+  calc
+    (∏ k ∈ Finset.range m, cosmicFactorQ k) =
+        (∏ k ∈ Finset.range m, cosmicFactorQ k) * 1 := by ring
+    _ ≤ (∏ k ∈ Finset.range m, cosmicFactorQ k) * cosmicFactorQ m :=
+      mul_le_mul_of_nonneg_left (le_of_lt (one_lt_cosmicFactorQ m))
+        (le_of_lt (cosmicPartialQ_pos m))
+
 /-- The central odd half-product. -/
 def centralOddRatioPartialQ (m : ℕ) : ℚ :=
   ∏ k ∈ Finset.range m, evenCenterQ k / oddLeftQ k
@@ -82,6 +215,26 @@ def mirrorOddRatioPartialQ (m : ℕ) : ℚ :=
 def centralRatioQ (m : ℕ) : ℚ :=
   (2 ^ (2 * m) : ℚ) / (Nat.choose (2 * m) m : ℚ)
 
+/-- The central odd half-product is positive. -/
+theorem centralOddRatioPartialQ_pos (m : ℕ) :
+    0 < centralOddRatioPartialQ m := by
+  unfold centralOddRatioPartialQ
+  exact Finset.prod_pos fun k _ => div_pos (evenCenterQ_pos k) (oddLeftQ_pos k)
+
+/-- The mirror odd half-product is positive. -/
+theorem mirrorOddRatioPartialQ_pos (m : ℕ) :
+    0 < mirrorOddRatioPartialQ m := by
+  unfold mirrorOddRatioPartialQ
+  exact Finset.prod_pos fun k _ => div_pos (evenCenterQ_pos k) (oddRightQ_pos k)
+
+/-- The central binomial ratio is positive. -/
+theorem centralRatioQ_pos (m : ℕ) :
+    0 < centralRatioQ m := by
+  unfold centralRatioQ
+  have hchoose : 0 < (Nat.choose (2 * m) m : ℚ) := by
+    exact_mod_cast Nat.choose_pos (by omega : m ≤ 2 * m)
+  exact div_pos (pow_pos (by norm_num : (0 : ℚ) < 2) _) hchoose
+
 private def centralRatioFactorialQ (m : ℕ) : ℚ :=
   ((2 : ℚ) ^ (2 * m) * (Nat.factorial m : ℚ) ^ 2) /
     (Nat.factorial (2 * m) : ℚ)
diff --git a/lean/dk_math/DkMath/Pascal/WallisLimitBridge.lean b/lean/dk_math/DkMath/Pascal/WallisLimitBridge.lean
new file mode 100644
index 00000000..cb41c6db
--- /dev/null
+++ b/lean/dk_math/DkMath/Pascal/WallisLimitBridge.lean
@@ -0,0 +1,47 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import Mathlib
+import DkMath.Pascal.WallisCosmicPetalBridge
+
+#print "file: DkMath.Pascal.WallisLimitBridge"
+
+/-!
+# Wallis limit bridge
+
+This module is the limit-facing layer for the finite Wallis-Cosmic Petal
+bridge.  The finite algebraic API remains in
+`DkMath.Pascal.WallisCosmicPetalBridge`.
+-/
+
+namespace DkMath.Pascal.WallisLimitBridge
+
+open scoped BigOperators
+open Filter Topology
+open DkMath.Pascal.WallisCosmicPetalBridge
+
+/--
+The finite rational Wallis partial product, after coercion to `ℝ`, is
+Mathlib's Wallis product `Real.Wallis.W`.
+-/
+theorem real_coe_wallisPartialQ_eq_Wallis_W (m : ℕ) :
+    ((wallisPartialQ m : ℚ) : ℝ) = Real.Wallis.W m := by
+  unfold wallisPartialQ Real.Wallis.W wallisFactorQ evenCenterQ oddLeftQ oddRightQ
+  rw [Rat.cast_prod]
+  exact Finset.prod_congr rfl fun k _ => by
+    norm_num
+    field_simp
+
+/--
+The real coercion of the finite rational Wallis partial products tends to
+`Real.pi / 2`, by Mathlib's Wallis product theorem.
+-/
+theorem tendsto_real_coe_wallisPartialQ_nhds_pi_div_two :
+    Tendsto (fun m : ℕ => ((wallisPartialQ m : ℚ) : ℝ)) atTop (𝓝 (Real.pi / 2)) := by
+  exact Real.Wallis.tendsto_W_nhds_pi_div_two.congr' <|
+    Eventually.of_forall fun m => (real_coe_wallisPartialQ_eq_Wallis_W m).symm
+
+end DkMath.Pascal.WallisLimitBridge
````
`````
