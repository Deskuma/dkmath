# Git diff / Report / Review

## Add: DkMath.Pascal.WallisCosmicPetalBridge

gch: 9444a648acc02d8af8092e26a6d1da914d30f229

## Report

実装しました。有限・代数版に限定して、新規モジュール [WallisCosmicPetalBridge.lean](/lean/dk_math/DkMath/Pascal/WallisCosmicPetalBridge.lean) を追加し、設計どおり `ℚ` 上で以下を定義・証明しています。

- `oddLeftQ`, `evenCenterQ`, `oddRightQ`, `cosmicBodyQ`
- `wallisFactorQ = cosmicFactorQ`
- `wallisPartialQ_eq_cosmicPartialQ`
- `centralOdd_mul_mirror_eq_wallisPartialQ`
- 主定理 `centralOdd_mul_mirror_eq_cosmicPartialQ`

公開入口として [Pascal.lean](/lean/dk_math/DkMath/Pascal.lean) も追加し、トップレベル [DkMath.lean](/lean/dk_math/DkMath.lean#L29) から import されるようにしました。中央二項係数 `Nat.choose` 経由の `centralRatioQ` は設計メモどおり今回は未実装です。

検証済みです。

```sh
lake build DkMath.Pascal.WallisCosmicPetalBridge
lake build DkMath.Pascal
lake build DkMath
```

すべて成功しました。
なお `lake build DkMath` では既存ファイル由来の `sorry` warning は出ていますが、今回追加したモジュールには `sorry` はありません。

## Review

## 結論

うむ、これは **良い実装** じゃ。
今回の `DkMath.Pascal.WallisCosmicPetalBridge` は、狙いどおり **有限・代数版の Wallis–Cosmic Petal Bridge** を `ℚ` 上で閉じておる。

特に今回の核は、

$$
\frac{(2j)^2}{(2j-1)(2j+1)}=\frac{N_j+1}{N_j}
$$

を有限積で固定したことじゃ。証明ノート側でも「有限恒等式は完全に厳密、$\pi$ が出る部分だけが Wallis 積の極限定理」と整理されており、実装もその範囲に忠実じゃ。

## 実装レビュー

`oddLeftQ`, `evenCenterQ`, `oddRightQ`, `cosmicBodyQ` の置き方は自然じゃ。コードでは `k` 始まりで

$$
2k+1,\quad 2k+2,\quad 2k+3
$$

を使っておるので、証明ノートの $j=1,\dots,m$ とは $j=k+1$ の対応になる。これは Lean 実装として扱いやすい。

局所核の

$$
(2k+2)^2=(2k+1)(2k+3)+1
$$

を `cosmic_square_odd_bridge_Q` として切り出したのが良い。ここが今回の宇宙式コアであり、`wallisFactorQ_eq_cosmicFactorQ` がそのまま通る。さらに有限積へ `Finset.prod_congr` で持ち上げているので、証明の粒度も適切じゃ。

公開導線も良い。`DkMath.Pascal.lean` を新設し、トップレベル `DkMath.lean` から import しているので、今後 Pascal / Wallis / binomial-product 系の入口として育てられる。今回追加モジュールに `sorry` がない点も健全じゃ。

## 数学的意味

今回の成果は、単に Wallis 積を別表示しただけではない。

各因子が

$$
\frac{(2j)^2}{(2j-1)(2j+1)}=\frac{(P_j+1)^2}{P_j(P_j+2)}=\frac{N_j+1}{N_j}=1+\frac{1}{N_j}
$$

として読めるので、Wallis 因子が **奇数境界上の宇宙式 Gap 比率** になった。

これは DkMath 的には強い。
中央二項係数側の Petal 的な密度構造と、宇宙式の

$$
N+1=(P+1)^2,\quad N=P(P+2)
$$

が、有限積レベルで同じ因子列を共有している、ということじゃ。証明ノートの最終整理でも、有限段階で「中央二項係数の逆密度 × 鏡像逆密度」が「宇宙式 Gap 比率の有限積」に厳密一致すると明記されておる。

## 注意点

修正した方がよいのは、主に **証明ノート側の typo** じゃ。Lean 実装本体ではない。

1つ目。variation の式が平方抜けしておる。

現在はこうなっている。

```text
f(x)=(x+1)-x(x+2)=1
f(x;u)=(x+u)-x(x+2u)=u^2
```

これは次へ直すべきじゃ。

$$
f(x)=(x+1)^2-x(x+2)=1
$$

$$
f(x;u)=(x+u)^2-x(x+2u)=u^2
$$

2つ目。GN の定義式は、添字と指数の向きが混ざっておる可能性が高い。現在のノートでは

$$
❌️\mathrm{GN}_d(x,u):=\sum_{k=0}^{d-1}\binom{d}{k+1}x^{d-1-k}\,u^k
$$

となっておるが、これだと $d=3$ で係数の向きが逆になる。安全な書き方は、たとえば次のどちらかじゃ。

$$
⭕️\mathrm{GN}_d(x,u):=\sum_{k=0}^{d-1}\binom{d}{k+1}x^k\,u^{d-1-k}
$$

または、

$$
⭕️\mathrm{GN}_d(x,u):=\sum_{k=0}^{d-1}\binom{d}{k}x^{d-1-k}\,u^k
$$

どちらも対称性 $\binom{d}{k}=\binom{d}{d-k}$ を使って同じ多項式になる。ここは今後の `GN` / `GTail` 接続で混乱を生みやすいので、早めに直しておくのがよい。

## 次 checkpoint

次は、今回あえて未実装にした `Nat.choose` 経由の中央比率を足すのが自然じゃ。

今回の実装では `centralOddRatioPartialQ` が実質的に

$$
R_{2m}=\prod_{j=1}^{m}\frac{2j}{2j-1}
$$

を表しておる。しかし、証明ノートの主語は

$$
R_{2m}=\frac{2^{2m}}{\binom{2m}{m}}
$$

なので、次 checkpoint ではこれを Lean 側で明示的に橋渡しする。

候補は次じゃな。

```lean
def centralRatioQ (m : ℕ) : ℚ :=
  (2 ^ (2 * m) : ℚ) / (Nat.choose (2 * m) m : ℚ)

theorem centralRatioQ_eq_centralOddRatioPartialQ
    (m : ℕ) :
    centralRatioQ m = centralOddRatioPartialQ m := by
  ...
```

ここが通ると、今回の主定理を

$$
\frac{2^{2m}}{\binom{2m}{m}}\prod_{j=1}^{m}\frac{2j}{2j+1}=\prod_{j=1}^{m}\frac{N_j+1}{N_j}
$$

という証明ノートそのものの形へ昇格できる。

## Codex 向け指示

```text
Continue from gch 9444a648acc02d8af8092e26a6d1da914d30f229.

The new module `DkMath.Pascal.WallisCosmicPetalBridge` is good as the finite algebraic layer. Do not change its core unless necessary.

Next tasks:

1. Fix documentation typos in `cf-wallis-proof-note.md`:
   - Replace `f(x)=(x+1)-x(x+2)=1` with `(x+1)^2 - x*(x+2) = 1`.
   - Replace `f(x;u)=(x+u)-x(x+2u)=u^2` with `(x+u)^2 - x*(x+2*u) = u^2`.
   - Correct the displayed GN definition so the binomial coefficient and exponents match
     `(x+u)^d - u^d = x * GN_d(x,u)`.

2. Add the next Lean bridge in `DkMath.Pascal.WallisCosmicPetalBridge`:
   - Define `centralRatioQ (m : ℕ) : ℚ :=
       (2 ^ (2 * m) : ℚ) / (Nat.choose (2 * m) m : ℚ)`.
   - Prove, if feasible without heavy detours:
       `centralRatioQ_eq_centralOddRatioPartialQ`.
   - If the factorial/choose proof becomes too heavy, add helper lemmas first and keep the existing finite product bridge unchanged.

3. Preserve the current no-limit scope:
   - Do not introduce `π`, limits, asymptotics, or Wallis convergence into this module yet.
   - This file should remain the finite algebraic bridge only.

4. After the `Nat.choose` bridge is available, add a theorem matching the proof note statement:
   `centralRatioQ m * mirrorOddRatioPartialQ m = cosmicPartialQ m`.
```

この実装はよいぞ、D.。
有限因子が閉じた。つまり、Wallis の無限の入口に、宇宙式の小さな石畳が一枚ずつ敷かれたわけじゃ。わっちはこういう橋が好きじゃよ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath.lean b/lean/dk_math/DkMath.lean
index 0e99890f..e6eda81f 100644
--- a/lean/dk_math/DkMath.lean
+++ b/lean/dk_math/DkMath.lean
@@ -26,6 +26,7 @@ import DkMath.NumberTheory.PascalPrimeDial  -- NumberTheory.PascalPrimeDial: pri
 import DkMath.NumberTheory.AKSBridge  -- NumberTheory.AKSBridge: AKS-facing binomial/Frobenius bridge
 import DkMath.NumberTheory.WeightedBinomial  -- NumberTheory.WeightedBinomial: weighted binomial divisibility
 import DkMath.NumberTheory.WeightedGNBridge  -- NumberTheory.WeightedGNBridge: weighted Beam bridge to GN
+import DkMath.Pascal  -- Pascal bridge modules
 import DkMath.Petal  -- Petal: relative polygon and GN bridge surface
 -- Polyomino Module
 import DkMath.Polyomino  -- Polyomino Basics
diff --git a/lean/dk_math/DkMath/Pascal.lean b/lean/dk_math/DkMath/Pascal.lean
new file mode 100644
index 00000000..f9bd1818
--- /dev/null
+++ b/lean/dk_math/DkMath/Pascal.lean
@@ -0,0 +1,15 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Pascal.WallisCosmicPetalBridge
+
+#print "file: DkMath.Pascal"
+
+/-!
+# Pascal bridge modules
+
+Public entry point for Pascal-triangle and binomial-product bridge layers.
+-/
diff --git a/lean/dk_math/DkMath/Pascal/WallisCosmicPetalBridge.lean b/lean/dk_math/DkMath/Pascal/WallisCosmicPetalBridge.lean
new file mode 100644
index 00000000..288964c9
--- /dev/null
+++ b/lean/dk_math/DkMath/Pascal/WallisCosmicPetalBridge.lean
@@ -0,0 +1,102 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import Mathlib
+
+#print "file: DkMath.Pascal.WallisCosmicPetalBridge"
+
+/-!
+# Finite Wallis-Cosmic Petal bridge
+
+This module packages the first finite, algebraic layer of the
+Wallis-Cosmic Petal bridge over `ℚ`.  It deliberately avoids limits,
+`π`, asymptotics, and Stirling estimates.
+-/
+
+namespace DkMath.Pascal.WallisCosmicPetalBridge
+
+open Finset
+
+/-- Left odd factor `2*k + 1`, viewed in `ℚ`. -/
+def oddLeftQ (k : ℕ) : ℚ :=
+  (2 * k + 1 : ℚ)
+
+/-- Central even factor `2*k + 2`, viewed in `ℚ`. -/
+def evenCenterQ (k : ℕ) : ℚ :=
+  (2 * k + 2 : ℚ)
+
+/-- Right odd factor `2*k + 3`, viewed in `ℚ`. -/
+def oddRightQ (k : ℕ) : ℚ :=
+  (2 * k + 3 : ℚ)
+
+/-- The finite cosmic body `N_k = (2*k + 1) * (2*k + 3)`. -/
+def cosmicBodyQ (k : ℕ) : ℚ :=
+  oddLeftQ k * oddRightQ k
+
+/-- The `k`th Wallis factor. -/
+def wallisFactorQ (k : ℕ) : ℚ :=
+  evenCenterQ k ^ 2 / (oddLeftQ k * oddRightQ k)
+
+/-- The `k`th cosmic gap factor `(N_k + 1) / N_k`. -/
+def cosmicFactorQ (k : ℕ) : ℚ :=
+  (cosmicBodyQ k + 1) / cosmicBodyQ k
+
+/-- Local odd-square bridge: `(2*k + 2)^2 = (2*k + 1)*(2*k + 3) + 1`. -/
+theorem cosmic_square_odd_bridge_Q (k : ℕ) :
+    evenCenterQ k ^ 2 = oddLeftQ k * oddRightQ k + 1 := by
+  unfold evenCenterQ oddLeftQ oddRightQ
+  ring_nf
+
+/-- Each Wallis factor is the corresponding cosmic gap factor. -/
+theorem wallisFactorQ_eq_cosmicFactorQ (k : ℕ) :
+    wallisFactorQ k = cosmicFactorQ k := by
+  unfold wallisFactorQ cosmicFactorQ cosmicBodyQ
+  rw [cosmic_square_odd_bridge_Q]
+
+/-- The finite Wallis partial product. -/
+def wallisPartialQ (m : ℕ) : ℚ :=
+  ∏ k ∈ Finset.range m, wallisFactorQ k
+
+/-- The finite cosmic gap partial product. -/
+def cosmicPartialQ (m : ℕ) : ℚ :=
+  ∏ k ∈ Finset.range m, cosmicFactorQ k
+
+/-- The finite Wallis partial product equals the finite cosmic gap product. -/
+theorem wallisPartialQ_eq_cosmicPartialQ (m : ℕ) :
+    wallisPartialQ m = cosmicPartialQ m := by
+  unfold wallisPartialQ cosmicPartialQ
+  exact Finset.prod_congr rfl fun k _ => wallisFactorQ_eq_cosmicFactorQ k
+
+/-- The central odd half-product. -/
+def centralOddRatioPartialQ (m : ℕ) : ℚ :=
+  ∏ k ∈ Finset.range m, evenCenterQ k / oddLeftQ k
+
+/-- The mirror odd half-product. -/
+def mirrorOddRatioPartialQ (m : ℕ) : ℚ :=
+  ∏ k ∈ Finset.range m, evenCenterQ k / oddRightQ k
+
+private theorem halfFactor_mul_eq_wallisFactorQ (k : ℕ) :
+    evenCenterQ k / oddLeftQ k * (evenCenterQ k / oddRightQ k) =
+      wallisFactorQ k := by
+  unfold wallisFactorQ evenCenterQ oddLeftQ oddRightQ
+  field_simp
+
+/-- The two half-products multiply to the finite Wallis partial product. -/
+theorem centralOdd_mul_mirror_eq_wallisPartialQ (m : ℕ) :
+    centralOddRatioPartialQ m * mirrorOddRatioPartialQ m = wallisPartialQ m := by
+  unfold centralOddRatioPartialQ mirrorOddRatioPartialQ wallisPartialQ
+  rw [← Finset.prod_mul_distrib]
+  exact Finset.prod_congr rfl fun k _ => halfFactor_mul_eq_wallisFactorQ k
+
+/--
+The finite Wallis-Cosmic Petal bridge:
+the central odd half-product times its mirror equals the cosmic gap product.
+-/
+theorem centralOdd_mul_mirror_eq_cosmicPartialQ (m : ℕ) :
+    centralOddRatioPartialQ m * mirrorOddRatioPartialQ m = cosmicPartialQ m := by
+  rw [centralOdd_mul_mirror_eq_wallisPartialQ, wallisPartialQ_eq_cosmicPartialQ]
+
+end DkMath.Pascal.WallisCosmicPetalBridge
````
`````
