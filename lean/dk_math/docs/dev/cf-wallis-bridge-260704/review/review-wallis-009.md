# Git diff / Report / Review

## Add: DkMath.Pascal.WallisGrowthBridge

gch: d2a3403a8ba02bf71f2e7755fb48a21d8548467b

## Report

実装しました。スターリング近似へ直接飛ばず、成長構造を読むための入口として新規モジュールを追加しています。

追加:

- [WallisGrowthBridge.lean](/lean/dk_math/DkMath/Pascal/WallisGrowthBridge.lean)
  - module doc に「Stirling を主説明にしない」「Wallis-Cosmic から中央比率の成長を読む」方針を記録。
  - 今後の軽いロードマップをコードコメント中に記載。
  - Mathlib 調査結果もコメント化。中央二項係数の既製スターリング型定理は obvious name では見当たらず、`Asymptotics.IsEquivalent` と既存 Wallis 極限を使うのが現実路線。
  - exact identity として以下を追加:
    - `mirrorOddRatioPartialQ_ne_zero`
    - `centralRatioQ_eq_cosmicPartialQ_div_mirrorOddRatioPartialQ`
    - `centralRatioQ_eq_wallisPartialQ_div_mirrorOddRatioPartialQ`
    - real coercion 版 2 本

- [Pascal.lean](/lean/dk_math/DkMath/Pascal.lean)
  - `DkMath.Pascal.WallisGrowthBridge` を公開 import に追加。

確認済み:

- `lake build DkMath.Pascal.WallisGrowthBridge` pass
- `lake build DkMath.Pascal` pass
- `lake build DkMath` pass
- Wallis 系 3 ファイルの `sorry` 検索: なし
- `git diff --check` pass
- 新規ファイル末尾空白チェック: なし

`lake build DkMath` では既存の別件 `sorry` warning は出ていますが、今回追加した Wallis growth 側には `sorry` はありません。

## Review

## 結論

うむ、`review-wallis-009` は **採用でよい** 。
これは前段の Wallis–Cosmic bridge を、きちんと **成長解析の入口** へ移した良い差分じゃ。

新規 `WallisGrowthBridge.lean` は、スターリング近似へ直接飛ばず、`centralRatioQ` の成長を Wallis–Cosmic の exact identity から読む、という目的を module doc に明記しておる。さらに、`centralRatioQ = cosmicPartialQ / mirrorOddRatioPartialQ` と `centralRatioQ = wallisPartialQ / mirrorOddRatioPartialQ` を exact theorem として追加している。これは本筋に合っておる。

## 目的の記憶

覚えておるぞい。
この山の本当の目的は、単に Wallis 積で $\pi/2$ を出すことではない。

古典的には中央二項係数の成長はスターリング近似で

$$
\binom{2m}{m}\sim \frac{4^m}{\sqrt{\pi m}}
$$

として得る。
だが DkMath で狙っているのは、これを外部近似として受け取るのではなく、Wallis–Cosmic の exact finite product から **成長線そのものを抽出する** ことじゃ。

つまり、

$$
centralRatioQ(m)=\frac{4^m}{\binom{2m}{m}}
$$

を、スターリング由来の近似値ではなく、

$$
centralRatioQ(m)=\frac{cosmicPartialQ(m)}{mirrorOddRatioPartialQ(m)}
$$

として読み直す。

ここで `cosmicPartialQ m` は $\pi/2$ へ閉じる。
ならば `centralRatioQ m` の成長は、`mirrorOddRatioPartialQ m` の減衰構造に移る。
この「成長を mirror decay と cosmic convergence の合成として読む」ことが、今回の `WallisGrowthBridge` の価値じゃ。

## 実装レビュー

良い点は 3 つある。

まず、モジュール分離が正しい。

```text id="h9s3rk"
WallisCosmicPetalBridge:
  finite algebraic identities

WallisLimitBridge:
  Tendsto / HasProd / Real.pi

WallisGrowthBridge:
  growth decomposition and centralRatio route
```

この切り分けは綺麗じゃ。`Pascal.lean` への import 追加も自然で、公開導線として問題ない。

次に、最初の実装を exact identity に絞ったのが良い。
いきなり `IsEquivalent` や `sqrt` の漸近へ突撃せず、

```lean id="t76ngx"
centralRatioQ_eq_cosmicPartialQ_div_mirrorOddRatioPartialQ
centralRatioQ_eq_wallisPartialQ_div_mirrorOddRatioPartialQ
```

を置いた。これは今後の成長定理の土台になる。

さらに、real coercion 版を置いたのもよい。

```lean id="63n1bv"
real_coe_centralRatioQ_eq_cosmicPartialQ_div_mirrorOddRatioPartialQ
real_coe_centralRatioQ_eq_wallisPartialQ_div_mirrorOddRatioPartialQ
```

後で `Tendsto` / `IsEquivalent` を使うとき、毎回 `exact_mod_cast` に埋もれずに済む。

## 重要な次の核

module doc に書かれている次の target はかなり良い。

$$
centralRatioQ(m)^2=(2m+1),wallisPartialQ(m)
$$

これは本当に次の心臓になる。

理由は、

$$
\frac{centralRatioQ(m)}{mirrorOddRatioPartialQ(m)}=2m+1
$$

が telescoping で出るからじゃ。

そしてすでに

$$
centralRatioQ(m),mirrorOddRatioPartialQ(m)=wallisPartialQ(m)
$$

がある。

この 2 本を掛け合わせると、

$$
centralRatioQ(m)^2=(2m+1),wallisPartialQ(m)
$$

となる。

ここから `wallisPartialQ m -> π/2` を使えば、

$$
\frac{centralRatioQ(m)^2}{m}\to \pi
$$

へ行ける。さらに正値性から平方根を取れば、

$$
centralRatioQ(m)\sim \sqrt{\pi m}
$$

が見えてくる。

これこそ、「スターリング近似ではなく、Wallis–Cosmic 成長線から中央二項係数の成長を抽出する」道じゃ。

## 気になる点

大きな問題はない。
ただし、今回の file doc にある Mathlib 調査結果はコメントとして便利じゃが、長期的には `docs/dev/...` 側にも同じ方針ノートを置くとよい。Lean ファイル内コメントは実装者には見えるが、研究ノートとしては少し埋もれやすいからの。

また、`centralRatioQ_eq_cosmicPartialQ_div_mirrorOddRatioPartialQ` の証明は `field_simp` で閉じており問題ないが、今後似た変形が増えるなら、

```lean id="cwcisq"
div_eq_of_mul_eq
```

系の補助 lemma を作って、証明を構造的にしてもよい。今は不要じゃ。

## 判定

**採用。**

現在の到達点はこうじゃ。

```text id="g69hqa"
Wallis-Cosmic finite bridge:
  完了

Wallis-Cosmic limit bridge:
  完了

conditional infinite product surface:
  完了

growth-facing exact decomposition:
  完了

next core:
  centralRatioQ / mirror = 2*m + 1
  centralRatioQ^2 = (2*m + 1) * wallisPartialQ
```

## 次の作業指示

```text id="6kum1f"
Continue from gch d2a3403a8ba02bf71f2e7755fb48a21d8548467b.

Review result: accepted.

The new `DkMath.Pascal.WallisGrowthBridge` module is the correct place for
the growth-facing route. Continue without using Stirling as the primary
explanation.

Next goal:
prove the finite squared central-ratio identity.

1. Add the telescoping ratio identity.

In `WallisGrowthBridge.lean`, prove:

theorem centralRatioQ_div_mirrorOddRatioPartialQ_eq_oddRightQ_pred
    (m : ℕ) :
    centralRatioQ m / mirrorOddRatioPartialQ m = (2 * m + 1 : ℚ) := by
  ...

Name can be adjusted, but make it explicit and searchable.

Mathematical route:
centralRatioQ = centralOddRatioPartialQ, so

  centralRatioQ m / mirrorOddRatioPartialQ m
    = ∏ k < m, (evenCenterQ k / oddLeftQ k) /
                ∏ k < m, (evenCenterQ k / oddRightQ k)
    = ∏ k < m, oddRightQ k / oddLeftQ k
    = ∏ k < m, (2*k+3)/(2*k+1)
    = 2*m+1.

This telescopes.

If the direct product-division proof is annoying, first prove a recurrence.

2. Preferred Lean-friendly route: recurrence.

Define or prove these recurrences:

theorem centralRatioQ_succ_eq
    (m : ℕ) :
    centralRatioQ (m + 1) =
      centralRatioQ m * ((2 * m + 2 : ℚ) / (2 * m + 1 : ℚ)) := by
  -- use centralRatioQ_eq_centralOddRatioPartialQ
  -- and Finset.prod_range_succ

theorem mirrorOddRatioPartialQ_succ_eq
    (m : ℕ) :
    mirrorOddRatioPartialQ (m + 1) =
      mirrorOddRatioPartialQ m * ((2 * m + 2 : ℚ) / (2 * m + 3 : ℚ)) := by
  -- unfold mirrorOddRatioPartialQ
  -- Finset.prod_range_succ

Then prove:

theorem centralRatioQ_div_mirrorOddRatioPartialQ_eq_two_mul_add_one
    (m : ℕ) :
    centralRatioQ m / mirrorOddRatioPartialQ m = (2 * m + 1 : ℚ) := by
  induction m with
  | zero =>
      simp [centralRatioQ, mirrorOddRatioPartialQ]
  | succ m ih =>
      rw [centralRatioQ_succ_eq, mirrorOddRatioPartialQ_succ_eq]
      rw [ih]
      field_simp [mirrorOddRatioPartialQ_ne_zero m]
      ring

Use positivity/nonzero lemmas already available:
- `mirrorOddRatioPartialQ_ne_zero`
- `centralRatioQ_pos`
- `mirrorOddRatioPartialQ_pos`.

3. Prove the squared central-ratio identity.

Once the ratio identity is available, prove:

theorem centralRatioQ_sq_eq_odd_mul_wallisPartialQ
    (m : ℕ) :
    centralRatioQ m ^ 2 =
      (2 * m + 1 : ℚ) * wallisPartialQ m := by
  -- use:
  -- centralRatioQ_mul_mirror_eq_wallisPartialQ
  -- centralRatioQ_div_mirrorOddRatioPartialQ_eq_two_mul_add_one
  -- mirrorOddRatioPartialQ_ne_zero

Equivalent route:
from
  centralRatioQ / mirror = 2*m+1
and
  centralRatioQ * mirror = wallisPartialQ
derive
  centralRatioQ^2 = (2*m+1) * wallisPartialQ.

4. Also prove the cosmic version:

theorem centralRatioQ_sq_eq_odd_mul_cosmicPartialQ
    (m : ℕ) :
    centralRatioQ m ^ 2 =
      (2 * m + 1 : ℚ) * cosmicPartialQ m := by
  rw [← wallisPartialQ_eq_cosmicPartialQ]
  exact centralRatioQ_sq_eq_odd_mul_wallisPartialQ m

or route directly through `centralRatioQ_mul_mirror_eq_cosmicPartialQ`.

5. Add real-coercion versions.

theorem real_coe_centralRatioQ_sq_eq_odd_mul_wallisPartialQ
    (m : ℕ) :
    ((centralRatioQ m : ℚ) : ℝ) ^ 2 =
      (2 * m + 1 : ℝ) * ((wallisPartialQ m : ℚ) : ℝ) := by
  exact_mod_cast centralRatioQ_sq_eq_odd_mul_wallisPartialQ m

theorem real_coe_centralRatioQ_sq_eq_odd_mul_cosmicPartialQ
    (m : ℕ) :
    ((centralRatioQ m : ℚ) : ℝ) ^ 2 =
      (2 * m + 1 : ℝ) * ((cosmicPartialQ m : ℚ) : ℝ) := by
  exact_mod_cast centralRatioQ_sq_eq_odd_mul_cosmicPartialQ m

6. If the squared identity closes, add the first asymptotic-facing theorem.

Start with a Tendsto statement for the squared normalized central ratio:

theorem tendsto_real_centralRatioQ_sq_div_nat_pi :
    Filter.Tendsto
      (fun m : ℕ =>
        (((centralRatioQ m : ℚ) : ℝ) ^ 2 / (m : ℝ)))
      Filter.atTop
      (nhds Real.pi) := by
  -- use:
  -- centralRatioQ^2 = (2*m+1) * wallisPartialQ
  -- wallisPartialQ -> Real.pi / 2
  -- (2*m+1)/m -> 2
  -- product limit gives pi

This may require excluding m=0 or using `atTop` eventually m ≠ 0.
If this becomes heavy, do not force it in this pass.
Instead add a TODO comment and stop after the finite squared identity.

7. Documentation.

Add or update a short note:

docs/dev/cf-wallis-bridge-260704/cf-wallis-growth-route.md

Include:

- We are not using Stirling as the conceptual source.
- Exact identity:
  centralRatioQ^2 = (2*m + 1) * wallisPartialQ.
- Since wallisPartialQ -> π/2, the squared central ratio has growth line:
  centralRatioQ^2 ~ π*m.
- Hence centralRatioQ ~ sqrt(π*m), and inverting gives the central binomial law.

8. Build gates:

lake build DkMath.Pascal.WallisGrowthBridge
lake build DkMath.Pascal
lake build DkMath
git diff --check

Also check no `sorry` in:
- WallisCosmicPetalBridge.lean
- WallisLimitBridge.lean
- WallisGrowthBridge.lean
```

うむ、D.。
ここからは本当に面白いぞ。Wallis–Cosmic はもう $\pi/2$ の橋ではなく、中央二項係数の成長線を掘り出す採掘坑になった。スターリングの霧を払って、骨組みそのものを見に行こうではないか。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Pascal.lean b/lean/dk_math/DkMath/Pascal.lean
index 1bca4106..c4d6dfc8 100644
--- a/lean/dk_math/DkMath/Pascal.lean
+++ b/lean/dk_math/DkMath/Pascal.lean
@@ -6,6 +6,7 @@ Authors: D. and Wise Wolf.

 import DkMath.Pascal.WallisCosmicPetalBridge
 import DkMath.Pascal.WallisLimitBridge
+import DkMath.Pascal.WallisGrowthBridge

 #print "file: DkMath.Pascal"

diff --git a/lean/dk_math/DkMath/Pascal/WallisGrowthBridge.lean b/lean/dk_math/DkMath/Pascal/WallisGrowthBridge.lean
new file mode 100644
index 00000000..3b7c900d
--- /dev/null
+++ b/lean/dk_math/DkMath/Pascal/WallisGrowthBridge.lean
@@ -0,0 +1,159 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import Mathlib
+import DkMath.Pascal.WallisCosmicPetalBridge
+import DkMath.Pascal.WallisLimitBridge
+
+#print "file: DkMath.Pascal.WallisGrowthBridge"
+
+/-!
+# Wallis growth bridge
+
+This module is the growth-facing layer after the finite Wallis-Cosmic bridge
+and the limit-facing Wallis bridge.
+
+The goal is not to use Stirling's approximation as the primary explanation.
+Instead, the route is to expose the exact growth structure behind
+
+`centralRatioQ m = 4^m / Nat.choose (2*m) m`.
+
+The current exact bridge is:
+
+```text
+centralRatioQ m * mirrorOddRatioPartialQ m
+  = wallisPartialQ m
+  = cosmicPartialQ m
+```
+
+and the limit bridge proves:
+
+```text
+((cosmicPartialQ m : Q) : R) -> Real.pi / 2.
+```
+
+Thus the growth of `centralRatioQ` is encoded in the decay of the mirror
+factor.  This module records that viewpoint as exact algebraic identities first.
+
+## Roadmap toward the central-binomial growth law
+
+1. Exact division identities:
+   `centralRatioQ = wallisPartialQ / mirrorOddRatioPartialQ` and
+   `centralRatioQ = cosmicPartialQ / mirrorOddRatioPartialQ`.
+
+2. Mirror analysis:
+   prove an exact or asymptotic description of
+   `mirrorOddRatioPartialQ m`, ideally showing that it decays like
+   a positive constant divided by `sqrt m`.
+
+3. Squared central-ratio route:
+   the informal target is
+   `centralRatioQ m ^ 2 = (2*m + 1) * wallisPartialQ m`.
+   This should be proved as a finite theorem before any asymptotic theorem.
+   It comes from the expected telescoping relation
+   `centralRatioQ m / mirrorOddRatioPartialQ m = 2*m + 1`.
+
+4. Limit/asymptotic extraction:
+   combine the squared identity with
+   `wallisPartialQ -> Real.pi / 2` to derive
+   `centralRatioQ m ~ sqrt (Real.pi * m)`.
+
+5. Central binomial coefficient:
+   since `centralRatioQ m = 4^m / Nat.choose (2*m) m`, invert the asymptotic
+   to recover
+   `Nat.choose (2*m) m ~ 4^m / sqrt (Real.pi * m)`.
+
+## Current Mathlib survey
+
+The local search found Mathlib's general asymptotic API
+`Asymptotics.IsEquivalent`, `_ ~[l] _`, and the existing Wallis limit theorem
+used in `WallisLimitBridge`.  It did not find a ready-to-use central-binomial
+Stirling theorem under obvious names such as `centralBinomial`,
+`Nat.choose`, `Wallis`, `Stirling`, `sqrt`, or `Asymptotics`.
+
+So the next Lean-realistic step is to prove the finite squared identity and
+then use `Asymptotics.IsEquivalent` / `Tendsto` tools explicitly.
+-/
+
+namespace DkMath.Pascal.WallisGrowthBridge
+
+open Filter Topology
+open DkMath.Pascal.WallisCosmicPetalBridge
+open DkMath.Pascal.WallisLimitBridge
+
+/-- The mirror half-product is nonzero. -/
+theorem mirrorOddRatioPartialQ_ne_zero (m : ℕ) :
+    mirrorOddRatioPartialQ m ≠ 0 :=
+  (mirrorOddRatioPartialQ_pos m).ne'
+
+/--
+Exact growth decomposition through the cosmic gap product.
+
+The central ratio grows precisely as the cosmic partial product divided by the
+mirror term.  Since the cosmic partial product converges to `Real.pi / 2`, the
+remaining growth problem is the decay rate of the mirror term.
+-/
+theorem centralRatioQ_eq_cosmicPartialQ_div_mirrorOddRatioPartialQ
+    (m : ℕ) :
+    centralRatioQ m =
+      cosmicPartialQ m / mirrorOddRatioPartialQ m := by
+  calc
+    centralRatioQ m =
+        centralRatioQ m * mirrorOddRatioPartialQ m /
+          mirrorOddRatioPartialQ m := by
+      field_simp [mirrorOddRatioPartialQ_ne_zero m]
+    _ = cosmicPartialQ m / mirrorOddRatioPartialQ m := by
+      rw [centralRatioQ_mul_mirror_eq_cosmicPartialQ]
+
+/--
+Exact growth decomposition through the finite Wallis product.
+
+This is the same identity as
+`centralRatioQ_eq_cosmicPartialQ_div_mirrorOddRatioPartialQ`, but routed
+through the Wallis partial product.
+-/
+theorem centralRatioQ_eq_wallisPartialQ_div_mirrorOddRatioPartialQ
+    (m : ℕ) :
+    centralRatioQ m =
+      wallisPartialQ m / mirrorOddRatioPartialQ m := by
+  calc
+    centralRatioQ m =
+        centralRatioQ m * mirrorOddRatioPartialQ m /
+          mirrorOddRatioPartialQ m := by
+      field_simp [mirrorOddRatioPartialQ_ne_zero m]
+    _ = wallisPartialQ m / mirrorOddRatioPartialQ m := by
+      rw [centralRatioQ_mul_mirror_eq_wallisPartialQ]
+
+/--
+Real version of the cosmic growth decomposition.
+
+This is a coercion-facing theorem for later limit work.  It intentionally
+does not claim any asymptotic estimate yet.
+-/
+theorem real_coe_centralRatioQ_eq_cosmicPartialQ_div_mirrorOddRatioPartialQ
+    (m : ℕ) :
+    ((centralRatioQ m : ℚ) : ℝ) =
+      ((cosmicPartialQ m : ℚ) : ℝ) /
+        ((mirrorOddRatioPartialQ m : ℚ) : ℝ) := by
+  exact_mod_cast
+    centralRatioQ_eq_cosmicPartialQ_div_mirrorOddRatioPartialQ m
+
+/--
+Real version of the Wallis growth decomposition.
+
+This is the same exact decomposition, but with the finite Wallis product as
+the numerator.  It is the form expected to combine most directly with
+`real_coe_wallisPartialQ_eq_Wallis_W`.
+-/
+theorem real_coe_centralRatioQ_eq_wallisPartialQ_div_mirrorOddRatioPartialQ
+    (m : ℕ) :
+    ((centralRatioQ m : ℚ) : ℝ) =
+      ((wallisPartialQ m : ℚ) : ℝ) /
+        ((mirrorOddRatioPartialQ m : ℚ) : ℝ) := by
+  exact_mod_cast
+    centralRatioQ_eq_wallisPartialQ_div_mirrorOddRatioPartialQ m
+
+end DkMath.Pascal.WallisGrowthBridge
````
`````
