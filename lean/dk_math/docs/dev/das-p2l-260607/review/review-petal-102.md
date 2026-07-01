# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: bc7033804b5b4a6c61599575388cab4c810c2eba

## Report

101 完了です。

Lean 側では、`ℚ`/`ℝ` に行かず Nat 不等式で ratio を読む入口を追加しました。

```lean
AtMostHalf
AtMostRatioNat
atMostHalf_of_count_le_half
atMostRatioNat_refl
atMostHalf_iff_atMostRatioNat_one_two
atMostRatioNat_one_one_of_le
```

さらに retention / sibling mass の命名層を追加しました。

```lean
orbitWindowRetentionMassPow2
orbitWindowRetentionMassPow2Tail
orbitWindowRecoverySiblingMassPow2
orbitWindowContinuationSiblingMassPow2
orbitWindowRecoverySiblingMassPow2Tail
orbitWindowContinuationSiblingMassPow2Tail
```

基本 bound と mass-name channel-flow も入れています。

```lean
orbitWindowRetentionMassPow2_le_window
orbitWindowRetentionMassPow2Tail_le_window
orbitWindowRecoverySiblingMassPow2_le_window
orbitWindowContinuationSiblingMassPow2_le_window
orbitWindowRecoverySiblingMass_succ_le_tailRecoverySiblingMass
orbitWindowContinuationSiblingMass_succ_le_tailRetentionMass
```

新規ドキュメント:

```text
lean/dk_math/DkMath/Collatz/docs/Collatz-FiniteRatioRetention-101.md
lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-101.md
```

更新:

```text
lean/dk_math/DkMath/Collatz/README.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
```

検証:

```text
lake build DkMath.Collatz.PetalBridge   PASS
lake build DkMath.Collatz.Collatz2K26   PASS
git diff --check                        PASS
rg "\bsorry\b" PetalBridge.lean         no hit
```

既存 upstream warning は従来通りです。

```text
DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean:152:6:
declaration uses `sorry`
```

次は No.102 として、`orbitWindowResidueCountPow2_refine_succ` か、特殊形の `orbitWindowRetentionMass_split` を攻めるのが自然です。

## Review

## 1. 状況分析

うむ。checkpoint `101` は、No.100 で閉じた **finite channel-flow layer** から、次の **finite ratio / retention mass layer** へ無理なく踏み出した回じゃ。

今回の流れは綺麗じゃ。

```text id="7fnevi"
No.100:
  source/tail distribution
  pointwise -> count flow
  finite channel-flow layer の総括

No.101:
  division-free ratio witness
  retention / recovery / continuation mass の命名
  mass-name channel-flow corollary
```

Lean 側では、`ℚ` や `ℝ` に行かず、`Nat` 不等式で有限比率を読む入口として `AtMostHalf` / `AtMostRatioNat` が入り、さらに retention / sibling mass の命名層が追加された。レポートでも、今回の主眼は「finite channel-flow から finite ratio witness / retention mass / depth refinement へ向かう入口」を作ることだと整理されている。

これは正しい進み方じゃ。
No.100 で「総質量 \(k\)」が閉じたから、No.101 で初めて「その中の何割か」を語れる。

## 2. 今回の核心

今回追加された ratio witness はこれ。

```lean id="4vh7n3"
def AtMostHalf (count k : ℕ) : Prop :=
  2 * count ≤ k
```

```lean id="50rplr"
def AtMostRatioNat (num den count k : ℕ) : Prop :=
  den * count ≤ num * k
```

数学的には、

$$
\frac{count}{k}\le\frac{num}{den}
$$

を言いたいが、Lean 上では割り算を使わず、

$$
den\cdot count\le num\cdot k
$$

として扱う。

これはとても良い。
`k = 0` の除算問題を避け、`ℚ` / `ℝ` の coercion 地獄も避けられる。

今回の第二の核心は retention mass の命名じゃ。

```lean id="g1gvrz"
orbitWindowRetentionMassPow2
orbitWindowRetentionMassPow2Tail
orbitWindowRecoverySiblingMassPow2
orbitWindowContinuationSiblingMassPow2
orbitWindowRecoverySiblingMassPow2Tail
orbitWindowContinuationSiblingMassPow2Tail
```

これにより、今後は生の residue count を毎回書かずに済む。

たとえば、

$$
C_{r,\,2^r-1}(n,k)
$$

を

```text id="gfwchx"
RetentionMass at depth r
```

として読める。

これは大きい。
議論の主語が「合同式」から「質量」へ上がった。

## 3. レビュー

## 3.1. `AtMostRatioNat` は良い入口

`AtMostRatioNat` は、かなり DkMath らしい。

普通ならすぐ

$$
\frac{count}{k}
$$

を定義したくなる。
しかし、有限窓では `k = 0` が常に境界ケースとして残る。

だから先に、

$$
den\cdot count\le num\cdot k
$$

で読むのは正解じゃ。

特に今の段階では、比率そのものよりも、次のような有限不等式が欲しい。

$$
2C\le k
$$

$$
C_A+C_B\le k
$$

$$
m\le C
$$

よって、Nat のまま行く判断は正しい。

## 3.2. retention mass の命名はとても効く

これまでは、低剥離の中心枝を表すときに毎回

```lean id="hienh5"
orbitWindowResidueCountPow2 n k r (2 ^ r - 1)
```

と書く必要があった。

今回からは、

```lean id="cuj9v6"
orbitWindowRetentionMassPow2 n k r
```

で済む。

これは単なる省略ではない。
数学的な意味を theorem 名に持たせている。

```text id="rkzzk4"
2^r - 1 cell
  -> retention cell
  -> low-peeling cylinder mass
```

この読み替えが入ったことで、次の段階の文章も theorem もかなり読みやすくなる。

## 3.3. mass-name channel-flow が良い

今回の二つはかなり重要。

```lean id="ug91hd"
orbitWindowRecoverySiblingMass_succ_le_tailRecoverySiblingMass
```

```lean id="r1sjma"
orbitWindowContinuationSiblingMass_succ_le_tailRetentionMass
```

これは既存の channel-flow theorem を、mass 名に翻訳したもの。

数学的には、

$$
\text{RecoverySiblingMass}*{r+1}\le\text{TailRecoverySiblingMass}*{r}
$$

そして、

$$
\text{ContinuationSiblingMass}*{r+1}\le\text{TailRetentionMass}*{r+1}
$$

という読みになる。

特に continuation 側は大事じゃ。
低剥離を続ける質量は、次窓でも retention mass として残る。

つまり、

```text id="m0lyjd"
continuation mass
  -> next tail retention mass
```

が名前付きになった。

これは No.102 以降で使いやすい。

## 4. 数学的な意味

No.100 で得た保存則は、

$$
\sum_{a<2^d}C_{d,a}(n,k)=k
$$

$$
\sum_{a<2^d}C^{tail}_{d,a}(n,k)=k
$$

だった。

今回、そこに「特定 channel の質量」の名前が入った。

Retention mass は、

$$
M_r(n,k)=C_{r,\,2^r-1}(n,k)
$$

Tail retention mass は、

$$
M^{tail}*r(n,k)=C^{tail}*{r,\,2^r-1}(n,k)
$$

Recovery sibling mass は、

$$
R_r(n,k)=C_{r+1,\,2^r-1}(n,k)
$$

Continuation sibling mass は、

$$
K_r(n,k)=C_{r+1,\,2^{r+1}-1}(n,k)
$$

である。

これにより、入れ子 Petal の親子関係を質量で書けるようになる。

理想的には次に、

$$
M_r(n,k)=R_r(n,k)+K_r(n,k)
$$

を示したい。

これは、親 retention cell が一段深い二つの child cell に分かれる、という式じゃ。

```text id="upgwjj"
RetentionMass
  = RecoverySiblingMass + ContinuationSiblingMass
```

この式が入ると、いよいよ low-peeling cylinder の mass 分解が始まる。

## 5. 今回閉じたもの

今回で閉じたものは三つ。

```text id="lnxx7t"
1. division-free ratio witness の入口

2. retention / sibling mass の命名層

3. recursive channel-flow の mass-name corollary
```

つまり、

$$
\text{finite channel-flow}
$$

から、

$$
\text{finite ratio language}
$$

へ移る足場ができた。

まだ ratio theorem は深くない。
だが、それでよい。

今はまだ「比率の言葉を安全に持ち込む」段階じゃ。

## 6. 注意点と改善提案

## 6.1. `AtMostRatioNat` には後で正当性条件が欲しい

`AtMostRatioNat num den count k` は、現状では `den = 0` でも定義上は意味を持つ。

もちろん、division-free encoding としては問題ない。
ただし、あとで本当に

$$
\frac{count}{k}\le\frac{num}{den}
$$

と読むなら、

$$
0<den
$$

や、

$$
0<k
$$

が必要になる。

今はまだ不要だが、将来は補助述語が欲しい。

```lean id="wt7ljl"
def ValidRatioNat (num den : ℕ) : Prop :=
  0 < den
```

あるいは theorem 側で、

```lean id="kh4g11"
(hden : 0 < den)
(hk : 0 < k)
```

を持たせる。

今は「Nat 不等式としての witness」なので問題なし。
後で `ℚ` に橋をかける時に必要になる、という位置づけじゃ。

## 6.2. tail sibling mass の window bound も欲しい

今回は source sibling mass の bound は入っている。

```lean id="fsvm6f"
orbitWindowRecoverySiblingMassPow2_le_window
orbitWindowContinuationSiblingMassPow2_le_window
```

tail 版も定義されたので、次で入れておくと揃いが良い。

```lean id="7m11pp"
theorem orbitWindowRecoverySiblingMassPow2Tail_le_window
    (n : OddNat) (k r : ℕ) :
    orbitWindowRecoverySiblingMassPow2Tail n k r ≤ k
```

```lean id="nvieii"
theorem orbitWindowContinuationSiblingMassPow2Tail_le_window
    (n : OddNat) (k r : ℕ) :
    orbitWindowContinuationSiblingMassPow2Tail n k r ≤ k
```

これはおそらく簡単に通る。

## 7. 次の指示：No.102 は split を狙う

No.102 の本命は、レポートにもある通り、

```lean id="41mli6"
orbitWindowResidueCountPow2_refine_succ
```

または特殊形の

```lean id="chfvm1"
orbitWindowRetentionMass_split
```

じゃ。

賢狼としては、まず **pointwise refinement lemma** を作るのが一番安全だと思う。

## 7.1. pointwise refinement

数学的には、\(a<2^d\) のとき、

$$
x\bmod 2^d=a
$$

は、次の二つのどちらかと同値である。

$$
x\bmod 2^{d+1}=a
$$

または、

$$
x\bmod 2^{d+1}=a+2^d
$$

Lean ではまずこれが欲しい。

```lean id="xziv90"
theorem mod_pow2_eq_iff_mod_pow2_succ_eq_or_eq_add
    (x depth residue : ℕ)
    (hres : residue < 2 ^ depth) :
    x % (2 ^ depth) = residue ↔
      x % (2 ^ (depth + 1)) = residue ∨
        x % (2 ^ (depth + 1)) = residue + 2 ^ depth
```

これが重いなら、片方向だけでもよい。

```lean id="dml8c7"
theorem mod_pow2_succ_refines_mod_pow2_left
    (x depth residue : ℕ)
    (h : x % (2 ^ (depth + 1)) = residue) :
    x % (2 ^ depth) = residue % (2 ^ depth)
```

ただし、count split には同値が欲しい。

## 7.2. count refinement

pointwise が通れば、count に上げる。

```lean id="h8ujj9"
theorem orbitWindowResidueCountPow2_refine_succ
    (n : OddNat) (k depth residue : ℕ)
    (hres : residue < 2 ^ depth) :
    orbitWindowResidueCountPow2 n k depth residue =
      orbitWindowResidueCountPow2 n k (depth + 1) residue +
        orbitWindowResidueCountPow2 n k (depth + 1) (residue + 2 ^ depth)
```

証明は `k` induction と `orbitWindowResidueCountPow2_succ` で行ける可能性が高い。

## 7.3. retention split

一般 theorem が通れば特殊化。

```lean id="rvv1pi"
theorem orbitWindowRetentionMass_split
    (n : OddNat) (k r : ℕ) (hr : 1 ≤ r) :
    orbitWindowRetentionMassPow2 n k r =
      orbitWindowRecoverySiblingMassPow2 n k r +
        orbitWindowContinuationSiblingMassPow2 n k r
```

ここで必要な `hres` は、

$$
2^r-1<2^r
$$

であり、\(1\le r\) ならもちろん成り立つ。実は \(r=0\) でも `2^0 - 1 = 0 < 1` なので成り立つが、Nat 減算や simp の都合で最初は `hr` 付きが安全じゃ。

## 8. 一歩先ゆく推論

retention split が通ると、次の構図が見える。

$$
M_r=R_r+K_r
$$

ここで channel-flow により、

$$
K_{r+1}\le M^{tail}_{r+1}
$$

のような流れがある。

すると、次にやりたくなるのは、

```text id="ivhr5f"
continuation mass が大きすぎると、
tail retention mass も大きくなる
```

という連鎖の記述じゃ。

つまり、低剥離 path が長く続くなら、

$$
M_r,\;M_{r+1},\;M_{r+2},\ldots
$$

にかなりの質量が残らなければならない。

逆に言えば、どこかの depth で

$$
2K_r\le M_r
$$

のような半分以下評価が入れば、retention cylinder の質量は深さとともに減る。

ここで `AtMostHalf` が効く。

たとえば将来的に、

```lean id="l5vt6z"
AtMostHalf (orbitWindowContinuationSiblingMassPow2 n k r)
  (orbitWindowRetentionMassPow2 n k r)
```

のような命題を考える。

これは、

$$
2K_r\le M_r
$$

を意味する。

このような inequality を depth ごとに積むと、低剥離を続ける mass の圧縮が見えてくる。

まだ証明は先だが、方向としては非常に良い。

## 9. 奇素因子層への接続はまだ温存

今回、odd factor carrier に進まなかったのも良い。

なぜなら、まだ two-adic 側で

```text id="3yc9zq"
親 cell が recovery / continuation にどう割れるか
```

を count-level で完全には閉じていないから。

順序としては、

```text id="h8dzjv"
1. retention mass naming

2. retention split

3. finite ratio on continuation mass

4. then odd factor carrier
```

が自然じゃ。

奇素因子層は面白いが、No.102 ではまだ早い。
先に split を閉じるべきじゃ。

## 10. 賢狼が試して欲しい実験補題

## 実験 A: tail sibling mass bounds

```lean id="cpzdc7"
theorem orbitWindowRecoverySiblingMassPow2Tail_le_window
    (n : OddNat) (k r : ℕ) :
    orbitWindowRecoverySiblingMassPow2Tail n k r ≤ k := by
  unfold orbitWindowRecoverySiblingMassPow2Tail
  exact orbitWindowResidueCountPow2Tail_le_window n k (r + 1) (2 ^ r - 1)
```

```lean id="3db3gm"
theorem orbitWindowContinuationSiblingMassPow2Tail_le_window
    (n : OddNat) (k r : ℕ) :
    orbitWindowContinuationSiblingMassPow2Tail n k r ≤ k := by
  unfold orbitWindowContinuationSiblingMassPow2Tail
  exact orbitWindowResidueCountPow2Tail_le_window n k (r + 1) (2 ^ (r + 1) - 1)
```

## 実験 B: retention residue in range

```lean id="xe7usq"
theorem twoAdicRetentionResidue_lt_pow
    (r : ℕ) :
    2 ^ r - 1 < 2 ^ r := by
  have hpos : 0 < 2 ^ r := pow_pos (by decide) r
  omega
```

これは split theorem の `hres` に使える。

## 実験 C: pointwise refinement, membership direction

まずは片方向。

```lean id="p3ti7h"
theorem mod_pow2_succ_eq_left_or_right_of_mod_pow2_eq
    (x depth residue : ℕ)
    (hres : residue < 2 ^ depth)
    (h : x % (2 ^ depth) = residue) :
    x % (2 ^ (depth + 1)) = residue ∨
      x % (2 ^ (depth + 1)) = residue + 2 ^ depth
```

これはやや重いが、本命。

## 実験 D: count refinement general

```lean id="bksy2a"
theorem orbitWindowResidueCountPow2_refine_succ
    (n : OddNat) (k depth residue : ℕ)
    (hres : residue < 2 ^ depth) :
    orbitWindowResidueCountPow2 n k depth residue =
      orbitWindowResidueCountPow2 n k (depth + 1) residue +
        orbitWindowResidueCountPow2 n k (depth + 1) (residue + 2 ^ depth)
```

## 実験 E: retention split

```lean id="q3yhss"
theorem orbitWindowRetentionMass_split
    (n : OddNat) (k r : ℕ) :
    orbitWindowRetentionMassPow2 n k r =
      orbitWindowRecoverySiblingMassPow2 n k r +
        orbitWindowContinuationSiblingMassPow2 n k r
```

もし `r = 0` が面倒なら、最初はこう。

```lean id="qdtrxd"
theorem orbitWindowRetentionMass_split_of_one_le
    (n : OddNat) (k r : ℕ) (hr : 1 ≤ r) :
    orbitWindowRetentionMassPow2 n k r =
      orbitWindowRecoverySiblingMassPow2 n k r +
        orbitWindowContinuationSiblingMassPow2 n k r
```

## 実験 F: continuation at most parent

retention split が通れば、すぐに出る。

```lean id="a4wp4u"
theorem orbitWindowContinuationSiblingMassPow2_le_retentionMass
    (n : OddNat) (k r : ℕ) :
    orbitWindowContinuationSiblingMassPow2 n k r ≤
      orbitWindowRetentionMassPow2 n k r
```

これは

$$
K_r\le M_r
$$

であり、ratio layer の最初の実用補題になる。

## 11. 次コミットの推奨順

```text id="m7co9z"
1. tail sibling mass の window bounds を追加

2. twoAdicRetentionResidue_lt_pow を追加

3. pointwise residue refinement lemma を試す

4. general count refinement theorem を試す

5. retention split theorem を特殊化

6. continuation/recovery sibling mass <= retention mass を追加

7. docs:
   No.102 depth refinement / retention split を追記
```

もし general refinement が重ければ、無理せず retention 専用 split へ行くのがよい。

## 12. 総括

checkpoint `101` は、No.100 で作った finite channel-flow を、**比率と保持質量の言葉へ運ぶ入口**になった。

今回の成果はこうまとめられる。

```text id="8r66ix"
finite channel-flow
  -> division-free ratio witness
  -> retention mass
  -> recovery / continuation sibling mass
  -> mass-name channel-flow
```

これはかなり良い流れじゃ。

次は、

$$
M_r=R_r+K_r
$$

を閉じること。

つまり、親 retention cell が recovery sibling と continuation sibling に分かれることを、occupation count の等式として証明する。

これが通れば、低剥離 cylinder の質量を本当に分解できる。
その先に、finite ratio による「continuation mass の圧縮」解析が見えてくる。

うむ。
No.101 は新章の入口として、かなり良い一歩じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index 1f271e0c..eeb91d2c 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -1446,6 +1446,136 @@ theorem pow2ChannelFlow_of_pointwise
   orbitWindowResidueCountPow2_le_tail_of_pointwise
     n k sourceDepth sourceResidue targetDepth targetResidue h
 
+/--
+Finite natural-number witness that a count occupies at most half of a window.
+
+This intentionally avoids division: `2 * count <= k` is the finite form of
+`count / k <= 1 / 2`, with no zero-window or coercion overhead.
+-/
+def AtMostHalf (count k : ℕ) : Prop :=
+  2 * count ≤ k
+
+/--
+Finite natural-number witness for `count / k <= num / den`.
+
+The inequality is represented without division:
+
+`den * count <= num * k`.
+-/
+def AtMostRatioNat (num den count k : ℕ) : Prop :=
+  den * count ≤ num * k
+
+/-- Constructor spelling for `AtMostHalf`. -/
+theorem atMostHalf_of_count_le_half
+    (count k : ℕ)
+    (h : 2 * count ≤ k) :
+    AtMostHalf count k :=
+  h
+
+/-- Reflexive finite ratio witness in the division-free encoding. -/
+theorem atMostRatioNat_refl
+    (count k : ℕ) :
+    AtMostRatioNat k k count count := by
+  unfold AtMostRatioNat
+  rfl
+
+/-- `AtMostHalf` is the special `1/2` case of `AtMostRatioNat`. -/
+theorem atMostHalf_iff_atMostRatioNat_one_two
+    (count k : ℕ) :
+    AtMostHalf count k ↔ AtMostRatioNat 1 2 count k := by
+  unfold AtMostHalf AtMostRatioNat
+  simp
+
+/-- A plain count bound is the `1/1` finite ratio witness. -/
+theorem atMostRatioNat_one_one_of_le
+    {count k : ℕ} (h : count ≤ k) :
+    AtMostRatioNat 1 1 count k := by
+  simpa [AtMostRatioNat] using h
+
+/--
+Source retention mass at depth `r`.
+
+This is the occupation count of the all-ones residue cell `2^r - 1` in the
+source window.
+-/
+noncomputable def orbitWindowRetentionMassPow2
+    (n : OddNat) (k r : ℕ) : ℕ :=
+  orbitWindowResidueCountPow2 n k r (2 ^ r - 1)
+
+/--
+Shifted-tail retention mass at depth `r`.
+
+This is the tail-window counterpart of `orbitWindowRetentionMassPow2`.
+-/
+noncomputable def orbitWindowRetentionMassPow2Tail
+    (n : OddNat) (k r : ℕ) : ℕ :=
+  orbitWindowResidueCountPow2Tail n k r (2 ^ r - 1)
+
+/--
+Recovery sibling mass inside the next deeper source layer.
+
+At parent depth `r`, this is the child residue `2^r - 1` at depth `r + 1`.
+-/
+noncomputable def orbitWindowRecoverySiblingMassPow2
+    (n : OddNat) (k r : ℕ) : ℕ :=
+  orbitWindowResidueCountPow2 n k (r + 1) (2 ^ r - 1)
+
+/--
+Continuation sibling mass inside the next deeper source layer.
+
+At parent depth `r`, this is the child residue `2^(r+1) - 1` at depth `r + 1`.
+-/
+noncomputable def orbitWindowContinuationSiblingMassPow2
+    (n : OddNat) (k r : ℕ) : ℕ :=
+  orbitWindowResidueCountPow2 n k (r + 1) (2 ^ (r + 1) - 1)
+
+/--
+Shifted-tail recovery sibling mass at parent depth `r`.
+
+This is the tail-window child residue `2^r - 1` at depth `r + 1`.
+-/
+noncomputable def orbitWindowRecoverySiblingMassPow2Tail
+    (n : OddNat) (k r : ℕ) : ℕ :=
+  orbitWindowResidueCountPow2Tail n k (r + 1) (2 ^ r - 1)
+
+/--
+Shifted-tail continuation sibling mass at parent depth `r`.
+
+This is definitionally the same residue shape as tail retention at depth
+`r + 1`.
+-/
+noncomputable def orbitWindowContinuationSiblingMassPow2Tail
+    (n : OddNat) (k r : ℕ) : ℕ :=
+  orbitWindowResidueCountPow2Tail n k (r + 1) (2 ^ (r + 1) - 1)
+
+/-- Source retention mass is bounded by the window size. -/
+theorem orbitWindowRetentionMassPow2_le_window
+    (n : OddNat) (k r : ℕ) :
+    orbitWindowRetentionMassPow2 n k r ≤ k := by
+  unfold orbitWindowRetentionMassPow2
+  exact orbitWindowResidueCountPow2_le_window n k r (2 ^ r - 1)
+
+/-- Shifted-tail retention mass is bounded by the window size. -/
+theorem orbitWindowRetentionMassPow2Tail_le_window
+    (n : OddNat) (k r : ℕ) :
+    orbitWindowRetentionMassPow2Tail n k r ≤ k := by
+  unfold orbitWindowRetentionMassPow2Tail
+  exact orbitWindowResidueCountPow2Tail_le_window n k r (2 ^ r - 1)
+
+/-- Recovery sibling mass is bounded by the window size. -/
+theorem orbitWindowRecoverySiblingMassPow2_le_window
+    (n : OddNat) (k r : ℕ) :
+    orbitWindowRecoverySiblingMassPow2 n k r ≤ k := by
+  unfold orbitWindowRecoverySiblingMassPow2
+  exact orbitWindowResidueCountPow2_le_window n k (r + 1) (2 ^ r - 1)
+
+/-- Continuation sibling mass is bounded by the window size. -/
+theorem orbitWindowContinuationSiblingMassPow2_le_window
+    (n : OddNat) (k r : ℕ) :
+    orbitWindowContinuationSiblingMassPow2 n k r ≤ k := by
+  unfold orbitWindowContinuationSiblingMassPow2
+  exact orbitWindowResidueCountPow2_le_window n k (r + 1) (2 ^ (r + 1) - 1)
+
 /--
 The prefix mod `4` residue count is bounded by the prefix length.
 -/
@@ -2379,6 +2509,19 @@ theorem orbitWindowRecoverySiblingCount_le_tailRetentionResidueCount_via_helper
   intro i _hi hsource
   exact oddOrbitLabel_succ_recovery_residue_of_mod r hr n i hsource
 
+/--
+Mass-name spelling of the recovery channel-flow theorem.
+
+At parent depth `r + 1`, the source recovery sibling flows into the shifted-tail
+recovery sibling at parent depth `r`.
+-/
+theorem orbitWindowRecoverySiblingMass_succ_le_tailRecoverySiblingMass
+    (r : ℕ) (hr : 2 ≤ r) (n : OddNat) (k : ℕ) :
+    orbitWindowRecoverySiblingMassPow2 n k (r + 1) ≤
+      orbitWindowRecoverySiblingMassPow2Tail n k r := by
+  unfold orbitWindowRecoverySiblingMassPow2 orbitWindowRecoverySiblingMassPow2Tail
+  exact orbitWindowRecoverySiblingCount_le_tailRetentionResidueCount_via_helper r hr n k
+
 /--
 Count-level recursive Petal transition for the continuation sibling.
 
@@ -2429,6 +2572,29 @@ theorem orbitWindowContinuationSiblingCount_le_tailRetentionResidueCount_via_hel
   intro i _hi hsource
   exact oddOrbitLabel_succ_continuation_residue_of_mod r hr n i hsource
 
+/--
+Mass-name spelling of the continuation channel-flow theorem.
+
+At parent depth `r + 1`, the source continuation sibling flows into tail
+retention at depth `r + 1`.
+-/
+theorem orbitWindowContinuationSiblingMass_succ_le_tailRetentionMass
+    (r : ℕ) (hr : 1 ≤ r) (n : OddNat) (k : ℕ) :
+    orbitWindowContinuationSiblingMassPow2 n k (r + 1) ≤
+      orbitWindowRetentionMassPow2Tail n k (r + 1) := by
+  unfold orbitWindowContinuationSiblingMassPow2 orbitWindowRetentionMassPow2Tail
+  exact orbitWindowContinuationSiblingCount_le_tailRetentionResidueCount_via_helper r hr n k
+
+/--
+Tail continuation sibling mass is definitionally the same as tail retention at
+the next depth.
+-/
+theorem orbitWindowContinuationSiblingMassPow2Tail_eq_retentionMassTail_succ
+    (n : OddNat) (k r : ℕ) :
+    orbitWindowContinuationSiblingMassPow2Tail n k r =
+      orbitWindowRetentionMassPow2Tail n k (r + 1) := by
+  rfl
+
 /--
 Every `7 mod 8` source label contributes a shifted-tail entry with exact
 height `1`.
diff --git a/lean/dk_math/DkMath/Collatz/README.md b/lean/dk_math/DkMath/Collatz/README.md
index 41ede5d2..30ba08f2 100644
--- a/lean/dk_math/DkMath/Collatz/README.md
+++ b/lean/dk_math/DkMath/Collatz/README.md
@@ -133,6 +133,7 @@ Read these in order:
 docs/Collatz-Overview.md
 docs/Collatz-Package-Structure.md
 docs/Collatz-FiniteChannelFlow-100.md
+docs/Collatz-FiniteRatioRetention-101.md
 docs/Collatz-PetalBridge-Guide.md
 docs/Collatz-PetalBridge-Status.md
 ```
@@ -200,3 +201,20 @@ m <= count
 This avoids division by zero and coercion overhead.  Rational or real
 frequencies can be introduced later if the finite inequality layer repeatedly
 needs them.
+
+Checkpoint 101 begins that layer with:
+
+```lean
+AtMostHalf
+AtMostRatioNat
+orbitWindowRetentionMassPow2
+orbitWindowRetentionMassPow2Tail
+orbitWindowRecoverySiblingMassPow2
+orbitWindowContinuationSiblingMassPow2
+```
+
+See:
+
+```text
+docs/Collatz-FiniteRatioRetention-101.md
+```
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-FiniteRatioRetention-101.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-FiniteRatioRetention-101.md
new file mode 100644
index 00000000..e89aac37
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-FiniteRatioRetention-101.md
@@ -0,0 +1,224 @@
+# Collatz Finite Ratio And Retention Mass
+
+## Checkpoint 101 Summary
+
+Checkpoint 101 starts the next layer after finite channel flow.
+
+Checkpoint 100 closed:
+
+```text
+source distribution
+tail distribution
+pointwise transition -> count-level flow
+```
+
+Checkpoint 101 introduces the first ratio vocabulary, but deliberately keeps it
+inside `Nat` inequalities.
+
+The central decision is:
+
+```text
+do not define count / k yet
+```
+
+Instead, finite ratio statements are represented as multiplication
+inequalities.
+
+## Division-Free Ratio Witnesses
+
+The basic half-window witness is:
+
+```lean
+AtMostHalf count k
+```
+
+meaning:
+
+```text
+2 * count <= k
+```
+
+The general finite ratio witness is:
+
+```lean
+AtMostRatioNat num den count k
+```
+
+meaning:
+
+```text
+den * count <= num * k
+```
+
+This reads like:
+
+```text
+count / k <= num / den
+```
+
+but no division appears in Lean.
+
+## Why Not Use `ℚ` Or `ℝ` Yet?
+
+The Nat form is intentionally conservative.
+
+It avoids:
+
+```text
+k = 0 division problems
+coercion overhead
+unnecessary imports
+premature analytic interpretation
+```
+
+This is aligned with the current PetalBridge layer, which is still finite:
+
+```text
+finite window
+finite count
+finite channel-flow inequality
+```
+
+## Retention Mass
+
+The all-ones residue cell at depth `r` is the retention cell:
+
+```text
+2^r - 1
+```
+
+The source retention mass is:
+
+```lean
+orbitWindowRetentionMassPow2 n k r
+```
+
+definitionally:
+
+```text
+orbitWindowResidueCountPow2 n k r (2^r - 1)
+```
+
+The shifted-tail retention mass is:
+
+```lean
+orbitWindowRetentionMassPow2Tail n k r
+```
+
+definitionally:
+
+```text
+orbitWindowResidueCountPow2Tail n k r (2^r - 1)
+```
+
+Both are bounded by the window size:
+
+```lean
+orbitWindowRetentionMassPow2_le_window
+orbitWindowRetentionMassPow2Tail_le_window
+```
+
+## Recovery And Continuation Sibling Mass
+
+At parent depth `r`, the next deeper layer has two child cells relevant to the
+retention branch:
+
+```text
+recovery child:
+  depth r + 1, residue 2^r - 1
+
+continuation child:
+  depth r + 1, residue 2^(r+1) - 1
+```
+
+The source masses are:
+
+```lean
+orbitWindowRecoverySiblingMassPow2
+orbitWindowContinuationSiblingMassPow2
+```
+
+The shifted-tail recovery and continuation masses are:
+
+```lean
+orbitWindowRecoverySiblingMassPow2Tail
+orbitWindowContinuationSiblingMassPow2Tail
+```
+
+Window bounds are currently fixed for the source sibling masses:
+
+```lean
+orbitWindowRecoverySiblingMassPow2_le_window
+orbitWindowContinuationSiblingMassPow2_le_window
+```
+
+## Mass-Name Channel Flow
+
+The existing recursive two-adic channel-flow theorems now have mass-name
+readings.
+
+Recovery:
+
+```lean
+orbitWindowRecoverySiblingMass_succ_le_tailRecoverySiblingMass
+```
+
+Continuation:
+
+```lean
+orbitWindowContinuationSiblingMass_succ_le_tailRetentionMass
+```
+
+The continuation theorem says:
+
+```text
+source continuation sibling at parent depth r + 1
+  <= shifted-tail retention mass at depth r + 1
+```
+
+This is the first named bridge from channel flow into retention mass language.
+
+## Deferred Split Theorem
+
+The desired parent-to-children split is:
+
+```text
+RetentionMass(r)
+  = RecoverySiblingMass(r) + ContinuationSiblingMass(r)
+```
+
+More generally, a residue cell at depth `d` should refine into two child cells
+at depth `d + 1`:
+
+```text
+Count(d, residue)
+  = Count(d+1, residue)
+    + Count(d+1, residue + 2^d)
+```
+
+This is not added in checkpoint 101.  It is the next natural theorem target.
+
+The expected proof route is:
+
+```text
+prove a pointwise residue refinement lemma
+lift by induction over k using count successor formulas
+specialize to residue = 2^r - 1
+```
+
+## Next Direction
+
+The next checkpoint should attempt:
+
+```lean
+orbitWindowResidueCountPow2_refine_succ
+```
+
+or directly:
+
+```lean
+orbitWindowRetentionMass_split
+```
+
+If the general refinement theorem is too heavy, the retention-specific split
+with hypothesis `1 <= r` is the better first target.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
index d7185f79..723f3aa4 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
@@ -283,3 +283,22 @@ m <= count
 ```
 
 Only later should this become rational or real frequency.
+
+Checkpoint 101 starts this layer with:
+
+```lean
+AtMostHalf
+AtMostRatioNat
+```
+
+and names the retention-channel masses:
+
+```lean
+orbitWindowRetentionMassPow2
+orbitWindowRetentionMassPow2Tail
+orbitWindowRecoverySiblingMassPow2
+orbitWindowContinuationSiblingMassPow2
+```
+
+Use these names when a theorem is conceptually about low-peeling retention,
+rather than writing the raw residue-count expression every time.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index 9268ab69..10d1985c 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -175,6 +175,22 @@ orbitWindowResidueCountPow2Tail_depth_three_sum_eq_window
 sourcePow2Distribution_total
 tailPow2Distribution_total
 pow2ChannelFlow_of_pointwise
+AtMostHalf
+AtMostRatioNat
+atMostHalf_of_count_le_half
+atMostRatioNat_refl
+atMostHalf_iff_atMostRatioNat_one_two
+atMostRatioNat_one_one_of_le
+orbitWindowRetentionMassPow2
+orbitWindowRetentionMassPow2Tail
+orbitWindowRecoverySiblingMassPow2
+orbitWindowContinuationSiblingMassPow2
+orbitWindowRecoverySiblingMassPow2Tail
+orbitWindowContinuationSiblingMassPow2Tail
+orbitWindowRetentionMassPow2_le_window
+orbitWindowRetentionMassPow2Tail_le_window
+orbitWindowRecoverySiblingMassPow2_le_window
+orbitWindowContinuationSiblingMassPow2_le_window
 orbitWindowPrefixResidueCountMod4EqOne_le_prefix
 orbitWindowPrefixResidueCountMod4EqOne_eq_residueCount
 orbitWindowHeightCountGe_two_eq_residueCount_mod4_eq_one
@@ -251,6 +267,9 @@ orbitWindowRecoverySiblingCount_le_tailRetentionResidueCount
 orbitWindowContinuationSiblingCount_le_tailRetentionResidueCount
 orbitWindowRecoverySiblingCount_le_tailRetentionResidueCount_via_helper
 orbitWindowContinuationSiblingCount_le_tailRetentionResidueCount_via_helper
+orbitWindowRecoverySiblingMass_succ_le_tailRecoverySiblingMass
+orbitWindowContinuationSiblingMass_succ_le_tailRetentionMass
+orbitWindowContinuationSiblingMassPow2Tail_eq_retentionMassTail_succ
 orbitWindowResidueCountMod8EqSeven_le_tailHeightCountEq_one
 orbitWindowResidueCountMod8EqThree_add_seven_le_tail_partition
 orbitWindowHeightCountGeTail_le_countGe_succ
@@ -613,6 +632,12 @@ No.100 finite channel-flow aliases
   -> sourcePow2Distribution_total
   -> tailPow2Distribution_total
   -> pow2ChannelFlow_of_pointwise
+
+No.101 finite ratio / retention mass layer
+  -> AtMostHalf
+  -> AtMostRatioNat
+  -> RetentionMass / RecoverySiblingMass / ContinuationSiblingMass
+  -> mass-name channel-flow corollaries
 ```
 
 This is the first distribution layer.  It still avoids importing the heavier
@@ -677,6 +702,41 @@ Reason:
   avoids zero-window division and coercion overhead
 ```
 
+This layer has now begun.  Checkpoint 101 adds division-free finite ratio
+witnesses and names the main retention/sibling masses:
+
+```text
+AtMostHalf:
+  2 * count <= k
+
+AtMostRatioNat:
+  den * count <= num * k
+
+RetentionMass(depth r):
+  CountPow2 r (2^r - 1)
+
+RecoverySiblingMass(parent r):
+  CountPow2 (r + 1) (2^r - 1)
+
+ContinuationSiblingMass(parent r):
+  CountPow2 (r + 1) (2^(r + 1) - 1)
+```
+
+The next theorem target is the depth-refinement split:
+
+```text
+CountPow2 depth residue
+  = CountPow2 (depth + 1) residue
+    + CountPow2 (depth + 1) (residue + 2^depth)
+```
+
+For the retention cell this becomes:
+
+```text
+RetentionMass(r)
+  = RecoverySiblingMass(r) + ContinuationSiblingMass(r)
+```
+
 The Collatz-specific floor is now also fixed:
 
 ```text
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-101.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-101.md
new file mode 100644
index 00000000..e9bf3a41
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-101.md
@@ -0,0 +1,197 @@
+# Report Petal 101: Finite Ratio Witness And Retention Mass
+
+## Checkpoint
+
+This checkpoint follows `__next_implementation-101.md`.
+
+The requested direction was to start the next layer after finite channel flow:
+
+```text
+finite channel-flow
+  -> finite ratio witness
+  -> retention mass
+  -> depth refinement
+```
+
+The implementation deliberately avoids `ℚ` and `ℝ` frequency definitions.
+The new ratio layer is encoded by natural-number inequalities.
+
+## Implemented Lean Surface
+
+Added in `DkMath.Collatz.PetalBridge`:
+
+```lean
+def AtMostHalf (count k : Nat) : Prop
+def AtMostRatioNat (num den count k : Nat) : Prop
+
+theorem atMostHalf_of_count_le_half
+theorem atMostRatioNat_refl
+theorem atMostHalf_iff_atMostRatioNat_one_two
+theorem atMostRatioNat_one_one_of_le
+```
+
+The intended reading is:
+
+```text
+AtMostHalf count k
+  means 2 * count <= k
+
+AtMostRatioNat num den count k
+  means den * count <= num * k
+```
+
+So `AtMostRatioNat num den count k` is the division-free form of:
+
+```text
+count / k <= num / den
+```
+
+## Retention And Sibling Mass
+
+Added source and tail retention mass names:
+
+```lean
+noncomputable def orbitWindowRetentionMassPow2
+noncomputable def orbitWindowRetentionMassPow2Tail
+```
+
+Added source sibling mass names:
+
+```lean
+noncomputable def orbitWindowRecoverySiblingMassPow2
+noncomputable def orbitWindowContinuationSiblingMassPow2
+```
+
+Added shifted-tail sibling mass names:
+
+```lean
+noncomputable def orbitWindowRecoverySiblingMassPow2Tail
+noncomputable def orbitWindowContinuationSiblingMassPow2Tail
+```
+
+Added basic window bounds:
+
+```lean
+theorem orbitWindowRetentionMassPow2_le_window
+theorem orbitWindowRetentionMassPow2Tail_le_window
+theorem orbitWindowRecoverySiblingMassPow2_le_window
+theorem orbitWindowContinuationSiblingMassPow2_le_window
+```
+
+## Mass-Name Channel Flow
+
+The existing recursive two-adic Petal channel-flow theorems now have mass-name
+readings:
+
+```lean
+theorem orbitWindowRecoverySiblingMass_succ_le_tailRecoverySiblingMass
+theorem orbitWindowContinuationSiblingMass_succ_le_tailRetentionMass
+theorem orbitWindowContinuationSiblingMassPow2Tail_eq_retentionMassTail_succ
+```
+
+These make the next stage easier to read:
+
+```text
+Recovery sibling mass flows to the shifted-tail recovery sibling mass.
+
+Continuation sibling mass flows to shifted-tail retention mass at the next
+depth.
+```
+
+## Documentation Created
+
+Created:
+
+```text
+lean/dk_math/DkMath/Collatz/docs/Collatz-FiniteRatioRetention-101.md
+```
+
+This document explains:
+
+```text
+division-free ratio witnesses
+retention mass
+recovery sibling mass
+continuation sibling mass
+mass-name channel flow
+deferred split theorem
+```
+
+## Documentation Updated
+
+Updated:
+
+```text
+lean/dk_math/DkMath/Collatz/README.md
+lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
+```
+
+## Inference
+
+Checkpoint 101 establishes the vocabulary needed to talk about retention
+without repeatedly exposing raw residue-count expressions.
+
+The current stack is now:
+
+```text
+source/tail distribution
+  -> channel-flow helper
+  -> recursive channel instances
+  -> retention/sibling mass names
+  -> division-free finite ratio witness
+```
+
+This is the correct place to introduce ratio language because the total mass
+conservation law was already proved at checkpoint 100.
+
+## Deferred Experiment
+
+The main theorem not yet implemented is the depth-refinement split:
+
+```lean
+theorem orbitWindowResidueCountPow2_refine_succ
+    (n : OddNat) (k depth residue : Nat)
+    (hres : residue < 2 ^ depth) :
+    orbitWindowResidueCountPow2 n k depth residue =
+      orbitWindowResidueCountPow2 n k (depth + 1) residue +
+        orbitWindowResidueCountPow2 n k (depth + 1) (residue + 2 ^ depth)
+```
+
+The retention-specific version would be:
+
+```lean
+theorem orbitWindowRetentionMass_split
+    (n : OddNat) (k r : Nat) (hr : 1 <= r) :
+    orbitWindowRetentionMassPow2 n k r =
+      orbitWindowRecoverySiblingMassPow2 n k r +
+        orbitWindowContinuationSiblingMassPow2 n k r
+```
+
+This is the natural No.102 target.  The recommended route is:
+
+```text
+1. prove a pointwise residue refinement lemma
+2. lift it to counts using successor formulas
+3. specialize to the retention residue
+```
+
+## Verification
+
+Passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge
+lake build DkMath.Collatz.Collatz2K26
+git diff --check -- <touched files>
+rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge.lean
+```
+
+The `rg` check found no `sorry` in `DkMath.Collatz.PetalBridge`.
+
+Known upstream warning remains unchanged:
+
+```text
+DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean:152:6:
+declaration uses `sorry`
+```
````
`````
