# Git diff / Report / Review

## Add: docs: Collatz.PetalBridge

gch: 66163684c2467d02ef0e293e1636bb0190a2eecd

## Report

No.100 完了です。今回は節目として、Lean 側は薄い概念 alias に留め、ドキュメントを厚めに整備しました。

Lean 追加:

```lean
sourcePow2Distribution_total
tailPow2Distribution_total
pow2ChannelFlow_of_pointwise
```

新規ドキュメント:

```text
lean/dk_math/DkMath/Collatz/README.md
lean/dk_math/DkMath/Collatz/docs/Collatz-Overview.md
lean/dk_math/DkMath/Collatz/docs/Collatz-Package-Structure.md
lean/dk_math/DkMath/Collatz/docs/Collatz-FiniteChannelFlow-100.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
lean/dk_math/DkMath/Petal/docs/Petal-CollatzBridge.md
lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-100.md
```

更新:

```text
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
```

内容としては、Collatz package の入口、古い shift/cartography approach、今回の finite channel-flow layer、Petal ↔ Collatz の橋、次の Nat inequality ratio layer までを整理しました。

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

次は No.101 として、`Nat` 不等式ベースの finite ratio witness、または `RetentionMass / RecoverySiblingMass / ContinuationSiblingMass` の軽い命名層へ進むのが自然です。

## Review

## 1. 状況分析

うむ。これは **No.100 checkpoint として非常に良い締め** じゃ。
長いが、内容は散らかっておらぬ。むしろ今回の主眼ははっきりしている。

今回の作業は、新しい重い数学 theorem を増やすのではなく、

```text
finite channel-flow layer を、後から読める形に固定する
```

という整理作業じゃった。

Lean 側の追加は薄い。

```lean
sourcePow2Distribution_total
tailPow2Distribution_total
pow2ChannelFlow_of_pointwise
```

一方で、ドキュメントは厚い。

```text
Collatz README
Collatz Overview
Package Structure
FiniteChannelFlow-100
PetalBridge Guide
Petal-CollatzBridge
report-petal-100
```

つまり、No.100 は「理論を広げた checkpoint」ではなく、**ここまでの finite channel-flow 章を閉じる checkpoint** じゃ。レポートにも、No.100 は documentation-heavy consolidation checkpoint として、Collatz package、finite channel-flow layer、Petal-Collatz bridge を文脈忘れ後にも読めるように整理した、と明記されている。

## 2. 今回の核心

今回の最重要ポイントは、概念 alias の導入じゃ。

```lean
theorem sourcePow2Distribution_total
    (n : OddNat) (k depth : ℕ) :
    (Finset.range (2 ^ depth)).sum
      (fun residue => orbitWindowResidueCountPow2 n k depth residue) = k :=
  orbitWindowResidueCountPow2_sum_eq_window n k depth
```

```lean
theorem tailPow2Distribution_total
    (n : OddNat) (k depth : ℕ) :
    (Finset.range (2 ^ depth)).sum
      (fun residue => orbitWindowResidueCountPow2Tail n k depth residue) = k :=
  orbitWindowResidueCountPow2Tail_sum_eq_window n k depth
```

```lean
theorem pow2ChannelFlow_of_pointwise
    (n : OddNat) (k sourceDepth sourceResidue targetDepth targetResidue : ℕ)
    (h :
      ∀ i, i < k →
        oddOrbitLabel n i % (2 ^ sourceDepth) = sourceResidue →
          oddOrbitLabel n (i + 1) % (2 ^ targetDepth) = targetResidue) :
    orbitWindowResidueCountPow2 n k sourceDepth sourceResidue ≤
      orbitWindowResidueCountPow2Tail n k targetDepth targetResidue :=
  orbitWindowResidueCountPow2_le_tail_of_pointwise
    n k sourceDepth sourceResidue targetDepth targetResidue h
```

これらは数学的には新しい強い定理ではない。
しかし、**読み方を変える theorem 名** になっている。

技術名で読むと、

```text
orbitWindowResidueCountPow2_sum_eq_window
```

だが、概念名で読むと、

```text
sourcePow2Distribution_total
```

になる。

これは大きい。
以後、議論の主語を「実装細部」から「有限分布の保存」へ移せる。

## 3. レビュー

## 3.1. No.100 としての判断が良い

今回、新しい ratio layer や odd factor carrier に突っ込まなかったのは正解じゃ。

理由は、finite channel-flow layer がちょうど閉じた瞬間だったから。

ここで新しい章へ踏み出すと、No.100 は「未整理の新規開始」になってしまう。
しかし今回は、

```text
source distribution
tail distribution
channel-flow helper
recursive Petal instances
```

を文書で束ねた。

これは「章の終わり」として美しい。

## 3.2. ドキュメント構成が良い

今回の追加ドキュメントは役割分担がはっきりしている。

```text
README.md
  -> Collatz package の玄関

Collatz-Overview.md
  -> 数学的な概観

Collatz-Package-Structure.md
  -> ファイルごとの役割

Collatz-FiniteChannelFlow-100.md
  -> No.100 の中心説明

Collatz-PetalBridge-Guide.md
  -> 実装者向けの使い方

Petal-CollatzBridge.md
  -> Petal 側から見た橋
```

特に `Collatz-FiniteChannelFlow-100.md` は重要じゃ。
これは後で新しい作業者、あるいは未来のぬし自身が読んだときに、

```text
No.100 で何が閉じたのか？
```

を復元できる。

## 3.3. `pow2ChannelFlow_of_pointwise` の名前が効いている

これまでは、

```lean
orbitWindowResidueCountPow2_le_tail_of_pointwise
```

という技術名だった。

今回、

```lean
pow2ChannelFlow_of_pointwise
```

という alias がついた。

これはかなり良い。
今後の theorem は、

```text
pointwise transition を証明する
pow2ChannelFlow_of_pointwise に渡す
count-level flow を得る
```

という道順で書ける。

これにより、count induction を毎回書く必要がなくなる。

## 4. 数学的解説

今回閉じた構図はこうじゃ。

まず、加速 Collatz 軌道の odd label を置く。

$$
q_i=\operatorname{oddOrbitLabel}(n,i)
$$

固定 depth \(d\) で、modulus は

$$
2^d
$$

である。

source 側の residue occupation count は、

$$
C_{d,a}(n,k)=\#{i<k\mid q_i\bmod 2^d=a}
$$

tail 側は、

$$
C^{tail}*{d,a}(n,k)=\#{i<k\mid q*{i+1}\bmod 2^d=a}
$$

今回の alias で、この二つの保存則が読みやすくなった。

$$
\sum_{a<2^d} C_{d,a}(n,k)=k
$$

$$
\sum_{a<2^d} C^{tail}_{d,a}(n,k)=k
$$

つまり、source window も tail window も、同じ総質量 \(k\) を持つ有限分布である。

そこに pointwise transition を入れる。

$$
q_i\bmod 2^{d_s}=a_s\quad\Longrightarrow\quad q_{i+1}\bmod 2^{d_t}=a_t
$$

すると、有限 channel-flow helper により、

$$
C_{d_s,a_s}(n,k)\le C^{tail}_{d_t,a_t}(n,k)
$$

が得られる。

この一行が、今回の章の本質じゃ。

```text
点の遷移
  -> 窓内の質量移動
```

Collatz 軌道が、値の列から、有限個の residue channel 間を流れる質量として読めるようになった。

## 5. Petal-Collatz Bridge としての意味

Petal 側では、もともと有限 range、address、occupation、collision/separation を扱ってきた。
今回、Collatz 側の odd orbit label が、その Petal 的観測に乗った。

対応はこうじゃ。

```text
Petal finite range
  -> OrbitWindow n k

Petal label
  -> oddOrbitLabel n i

Petal address
  -> q_i mod 2^depth

Petal occupation
  -> orbitWindowResidueCountPow2

Petal channel flow
  -> pow2ChannelFlow_of_pointwise
```

ここが美しい。

Collatz は特殊な数列ではあるが、観測形式としては Petal の一般語彙に乗る。

つまり、今回の成果は Collatz だけのものではない。
DkMath の Petal 観測方法が、Collatz という別領域に移植できることを示した実例にもなっている。

## 6. ここで閉じたもの

No.100 で閉じたものは、次の四点じゃ。

```text
1. source 側の residue distribution 保存

2. tail 側の residue distribution 保存

3. pointwise transition から count-flow への汎用 helper

4. recursive two-adic Petal channel の helper route 接続
```

式で並べれば、

$$
\sum_{a<2^d} C_{d,a}=k
$$

$$
\sum_{a<2^d} C^{tail}_{d,a}=k
$$

$$
q_i\in A\Rightarrow q_{i+1}\in B
$$

$$
C_A\le C^{tail}_B
$$

この四本が揃った。

よって、finite channel-flow layer は一章として成立している。

## 7. ここでまだ閉じていないもの

一方で、今回まだ踏み込んでいないものも明確じゃ。

```text
1. Collatz 収束そのもの

2. asymptotic frequency

3. real-valued probability

4. odd factor carrier

5. new odd prime factor event

6. retention mass の比率評価
```

これは不足ではなく、設計上の保留じゃ。
むしろ、finite Nat count の層を先に閉じたことに価値がある。

次の層に行く前に、土台がしっかりした。

## 8. 次の指示

No.101 では、いよいよ軽く新章へ入ってよい。

賢狼の推奨は、いきなり \(\mathbb{Q}\) frequency ではなく、**Nat inequality ratio layer** じゃ。

まずは定義を置く。

```lean
def AtMostHalf (count k : ℕ) : Prop :=
  2 * count ≤ k
```

より一般に、

```lean
def AtMostRatioNat (num den count k : ℕ) : Prop :=
  den * count ≤ num * k
```

読みは、

$$
\frac{count}{k}\le\frac{num}{den}
$$

だが、Lean 上では割り算を使わない。

これが良い理由は三つ。

```text
1. k = 0 の除算問題を避ける

2. ℚ / ℝ coercion を避ける

3. 既存の Nat count theorem と相性が良い
```

## 9. 一歩先ゆく推論

No.101 以降で本当に欲しいのは、ratio そのものというより、**retention mass の圧縮評価** じゃ。

Retention mass を定義する。

```lean
noncomputable def orbitWindowRetentionMassPow2
    (n : OddNat) (k r : ℕ) : ℕ :=
  orbitWindowResidueCountPow2 n k r (2 ^ r - 1)
```

tail 版も置く。

```lean
noncomputable def orbitWindowRetentionMassPow2Tail
    (n : OddNat) (k r : ℕ) : ℕ :=
  orbitWindowResidueCountPow2Tail n k r (2 ^ r - 1)
```

さらに、親 retention cell が一段深い recovery sibling と continuation sibling に分裂することを count-level で見たい。

理想形は、

$$
C_{r,\,2^r-1}=C_{r+1,\,2^r-1}+C_{r+1,\,2^{r+1}-1}
$$

である。

Lean 候補はこれ。

```lean
theorem orbitWindowRetentionCount_split_recovery_continuation
    (n : OddNat) (k r : ℕ) :
    orbitWindowResidueCountPow2 n k r (2 ^ r - 1) =
      orbitWindowResidueCountPow2 n k (r + 1) (2 ^ r - 1) +
        orbitWindowResidueCountPow2 n k (r + 1) (2 ^ (r + 1) - 1)
```

ただし \(r=0\) は少し危ないので、最初は

```lean
(hr : 1 ≤ r)
```

を入れて安全にするのがよい。

これが通ると、Petal の親 cell が二つの child cell に割れることが、occupation count で言える。

その上で、

```text
continuation sibling mass がどれくらい残るか
```

を見る。

ここが低剥離 path の濃度解析へつながる。

## 10. 賢狼が試して欲しい実験補題

## 実験 A: finite ratio witness

```lean
def AtMostHalf (count k : ℕ) : Prop :=
  2 * count ≤ k
```

```lean
def AtMostRatioNat (num den count k : ℕ) : Prop :=
  den * count ≤ num * k
```

## 実験 B: basic ratio facts

```lean
theorem atMostHalf_of_count_le_half
    (count k : ℕ)
    (h : 2 * count ≤ k) :
    AtMostHalf count k := h
```

```lean
theorem atMostRatioNat_refl
    (count k : ℕ) :
    AtMostRatioNat k k count count := by
  unfold AtMostRatioNat
  omega
```

後者は `k = 0` 周辺で変な形なら無理に入れず、もっと意味のある補題に変えてよい。

## 実験 C: retention mass source/tail

```lean
noncomputable def orbitWindowRetentionMassPow2
    (n : OddNat) (k r : ℕ) : ℕ :=
  orbitWindowResidueCountPow2 n k r (2 ^ r - 1)
```

```lean
noncomputable def orbitWindowRetentionMassPow2Tail
    (n : OddNat) (k r : ℕ) : ℕ :=
  orbitWindowResidueCountPow2Tail n k r (2 ^ r - 1)
```

## 実験 D: recovery / continuation sibling mass

```lean
noncomputable def orbitWindowRecoverySiblingMassPow2
    (n : OddNat) (k r : ℕ) : ℕ :=
  orbitWindowResidueCountPow2 n k (r + 1) (2 ^ r - 1)
```

```lean
noncomputable def orbitWindowContinuationSiblingMassPow2
    (n : OddNat) (k r : ℕ) : ℕ :=
  orbitWindowResidueCountPow2 n k (r + 1) (2 ^ (r + 1) - 1)
```

## 実験 E: retention split

```lean
theorem orbitWindowRetentionMass_split
    (n : OddNat) (k r : ℕ) (hr : 1 ≤ r) :
    orbitWindowRetentionMassPow2 n k r =
      orbitWindowRecoverySiblingMassPow2 n k r +
        orbitWindowContinuationSiblingMassPow2 n k r
```

これは少し重い可能性がある。
先に一般 refinement lemma を作る方が楽かもしれない。

## 実験 F: general refinement lemma

```lean
theorem orbitWindowResidueCountPow2_refine_succ
    (n : OddNat) (k depth residue : ℕ)
    (hres : residue < 2 ^ depth) :
    orbitWindowResidueCountPow2 n k depth residue =
      orbitWindowResidueCountPow2 n k (depth + 1) residue +
        orbitWindowResidueCountPow2 n k (depth + 1) (residue + 2 ^ depth)
```

これが通れば、retention split はその特殊化で出る。

## 11. 次コミットの推奨順

```text
1. AtMostHalf / AtMostRatioNat を docs または Lean に薄く追加

2. RetentionMass / RecoverySiblingMass / ContinuationSiblingMass を定義

3. general refinement lemma を検討

4. retention split theorem を特殊化として追加

5. continuation mass -> tail retention mass の named corollary

6. docs:
   No.101 Finite Ratio / Retention Mass の設計メモ
```

No.101 では、ratio layer と retention mass の入口だけで良い。
いきなり奇素因子層へ行くのは、まだ少し早い。

## 12. 総括

No.100 は本当に良い節目になった。

ここまでで、

```text
Collatz orbit
  -> two-adic residue coordinate
  -> source/tail distribution
  -> finite channel-flow
```

が閉じた。

今回の追加は薄い alias と厚い docs だが、これは単なる文書整理ではない。
理論の読み方を安定させた。

今後は、

```text
finite channel-flow
  -> finite ratio witness
  -> retention mass
  -> depth refinement
  -> odd factor carrier
```

へ進むのが自然じゃ。

うむ。
長いが、内容はかなり良い。
No.100 として、「ここまで何を作ったのか」が後から読める状態になった。これは研究開発ではとても大事な成果じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index 3422dabf..1f271e0c 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -1403,6 +1403,49 @@ theorem orbitWindowResidueCountPow2_le_tail_of_pointwise
             simpa [hsource, htail] using Nat.le_succ_of_le ih'
         · simpa [hsource, htail] using ih'
 
+/--
+Conceptual alias for source-side power-of-two residue distribution
+conservation.
+
+This is the No.100 finite channel-flow spelling of
+`orbitWindowResidueCountPow2_sum_eq_window`.
+-/
+theorem sourcePow2Distribution_total
+    (n : OddNat) (k depth : ℕ) :
+    (Finset.range (2 ^ depth)).sum
+      (fun residue => orbitWindowResidueCountPow2 n k depth residue) = k :=
+  orbitWindowResidueCountPow2_sum_eq_window n k depth
+
+/--
+Conceptual alias for shifted-tail power-of-two residue distribution
+conservation.
+
+This is the No.100 finite channel-flow spelling of
+`orbitWindowResidueCountPow2Tail_sum_eq_window`.
+-/
+theorem tailPow2Distribution_total
+    (n : OddNat) (k depth : ℕ) :
+    (Finset.range (2 ^ depth)).sum
+      (fun residue => orbitWindowResidueCountPow2Tail n k depth residue) = k :=
+  orbitWindowResidueCountPow2Tail_sum_eq_window n k depth
+
+/--
+Conceptual alias for finite power-of-two channel flow.
+
+A pointwise residue transition from source labels to shifted-tail labels gives
+a count-level occupation inequality between the two channel distributions.
+-/
+theorem pow2ChannelFlow_of_pointwise
+    (n : OddNat) (k sourceDepth sourceResidue targetDepth targetResidue : ℕ)
+    (h :
+      ∀ i, i < k →
+        oddOrbitLabel n i % (2 ^ sourceDepth) = sourceResidue →
+          oddOrbitLabel n (i + 1) % (2 ^ targetDepth) = targetResidue) :
+    orbitWindowResidueCountPow2 n k sourceDepth sourceResidue ≤
+      orbitWindowResidueCountPow2Tail n k targetDepth targetResidue :=
+  orbitWindowResidueCountPow2_le_tail_of_pointwise
+    n k sourceDepth sourceResidue targetDepth targetResidue h
+
 /--
 The prefix mod `4` residue count is bounded by the prefix length.
 -/
diff --git a/lean/dk_math/DkMath/Collatz/README.md b/lean/dk_math/DkMath/Collatz/README.md
new file mode 100644
index 00000000..41ede5d2
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/README.md
@@ -0,0 +1,202 @@
+# DkMath.Collatz
+
+`DkMath.Collatz` is the DkMath formalization workspace for the accelerated
+Collatz map on odd natural states.
+
+The current package is not only a direct attempt to prove the Collatz
+conjecture.  It is a structured observation program:
+
+```text
+odd state dynamics
+  -> 2-adic height
+  -> residue channels
+  -> finite observation windows
+  -> source/tail distributions
+  -> finite channel flow
+```
+
+The most recent milestone is the finite channel-flow layer in
+`DkMath.Collatz.PetalBridge`.  It turns pointwise residue transitions into
+count-level statements over finite windows, without using limits,
+probability, or real-valued frequencies.
+
+## Module Entry Points
+
+```text
+DkMath.Collatz.Basic
+DkMath.Collatz.V2
+DkMath.Collatz.Accelerated
+DkMath.Collatz.Shift
+DkMath.Collatz.PetalBridge
+DkMath.Collatz.Collatz2K26
+```
+
+### `DkMath.Collatz.Basic`
+
+Defines the basic Collatz surface:
+
+```lean
+C
+OddNat
+threeNPlusOne
+```
+
+This is the lowest-level arithmetic layer.
+
+### `DkMath.Collatz.V2`
+
+Provides the local 2-adic valuation vocabulary used by the accelerated map.
+
+Important names include:
+
+```lean
+v2
+v2_3n_plus_1_ge_1
+v2_shift_invariant
+```
+
+This file is the arithmetic source of the fact that every odd accelerated
+Collatz state peels at least one factor of `2`.
+
+### `DkMath.Collatz.Accelerated`
+
+Defines the accelerated odd-state Collatz map:
+
+```lean
+s n = v2 (3 * n + 1)
+T n = (3 * n + 1) / 2 ^ s n
+iterateT
+sumS
+driftReal
+```
+
+This is the dynamical core.
+
+### `DkMath.Collatz.Shift`
+
+Records the block-shift / petal-cartography approach.
+
+This older approach studies how the valuation signal behaves under shifts by
+powers of two:
+
+```text
+n -> n + 2^k * m
+```
+
+The guiding idea is that many differences do not appear everywhere; they
+concentrate around singular 2-adic ridges.
+
+### `DkMath.Collatz.PetalBridge`
+
+This is the current main bridge.
+
+It packages finite windows of the accelerated orbit and connects them to
+Petal-style counting:
+
+```lean
+OrbitWindow
+oddOrbitLabel
+orbitWindowHeight
+orbitWindowHeightSeq
+orbitWindowResidueCountPow2
+orbitWindowResidueCountPow2Tail
+sourcePow2Distribution_total
+tailPow2Distribution_total
+pow2ChannelFlow_of_pointwise
+```
+
+The central No.100 layer is:
+
+```text
+Source distribution:
+  sum of all source residue counts = window size
+
+Tail distribution:
+  sum of all shifted-tail residue counts = window size
+
+Channel flow:
+  pointwise source-to-tail residue transition
+    -> source count <= target tail count
+```
+
+### `DkMath.Collatz.Collatz2K26`
+
+Integration file for the 2026 Collatz cartography project.
+
+It imports the main Collatz files and marks the package-level surface.
+
+## Main Documentation
+
+Read these in order:
+
+```text
+docs/Collatz-Overview.md
+docs/Collatz-Package-Structure.md
+docs/Collatz-FiniteChannelFlow-100.md
+docs/Collatz-PetalBridge-Guide.md
+docs/Collatz-PetalBridge-Status.md
+```
+
+Older and experimental notes:
+
+```text
+docs/CollatzCartography.md
+docs/CollatzCartography-ja.md
+docs/IMPLEMENTATION_REPORT_20260130.md
+docs/AUXILIARY_LEMMA_COMPLETION_20260130.md
+docs/SORRY_CLEANUP_PROGRESS_20260130.md
+```
+
+Petal-side companion:
+
+```text
+../Petal/docs/Petal-CollatzBridge.md
+```
+
+## What Was Achieved At Checkpoint 100?
+
+Checkpoint 100 closes a finite, natural-valued observation layer.
+
+The important Lean aliases are:
+
+```lean
+sourcePow2Distribution_total
+tailPow2Distribution_total
+pow2ChannelFlow_of_pointwise
+```
+
+They summarize earlier technical theorems:
+
+```lean
+orbitWindowResidueCountPow2_sum_eq_window
+orbitWindowResidueCountPow2Tail_sum_eq_window
+orbitWindowResidueCountPow2_le_tail_of_pointwise
+```
+
+The mathematical point is simple:
+
+```text
+Every label in a finite window occupies exactly one residue channel.
+If a pointwise transition sends one channel into another channel,
+then the occupation count of the source channel is bounded by the
+occupation count of the target shifted-tail channel.
+```
+
+This is not yet a proof of Collatz termination.  It is a verified framework
+for talking about finite channel mass and its movement under the accelerated
+map.
+
+## Next Direction
+
+The next natural layer is a finite ratio layer, but still using natural-number
+inequalities:
+
+```text
+2 * count <= k
+countA + countB <= k
+m <= count
+```
+
+This avoids division by zero and coercion overhead.  Rational or real
+frequencies can be introduced later if the finite inequality layer repeatedly
+needs them.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-FiniteChannelFlow-100.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-FiniteChannelFlow-100.md
new file mode 100644
index 00000000..dbdf3aa8
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-FiniteChannelFlow-100.md
@@ -0,0 +1,237 @@
+# Collatz Finite Channel-Flow Layer
+
+## Checkpoint 100 Summary
+
+Checkpoint 100 closes the first finite channel-flow layer for the accelerated
+Collatz map.
+
+The theorem chain is:
+
+```text
+1. residue arithmetic
+2. orbit-label transition
+3. source distribution conservation
+4. shifted-tail distribution conservation
+5. pointwise-to-count channel-flow helper
+6. recursive two-adic Petal instances
+```
+
+The important point is that this layer is entirely finite and natural-valued.
+
+It does not use:
+
+```text
+limits
+probability
+real-valued density
+asymptotic frequency
+```
+
+This is intentional.  The project first fixes exact finite conservation laws
+before introducing any ratio or analytic language.
+
+## Source And Tail Windows
+
+For a starting odd state `n` and window size `k`, the source window is:
+
+```text
+i = 0, 1, ..., k - 1
+```
+
+with labels:
+
+```lean
+oddOrbitLabel n i
+```
+
+The shifted-tail window is:
+
+```text
+i + 1 = 1, 2, ..., k
+```
+
+It is counted by the same index range `i < k`, but each label is shifted one
+step forward.
+
+## Power-Of-Two Residue Cells
+
+At depth `depth`, the residue modulus is:
+
+```text
+2^depth
+```
+
+The source count is:
+
+```lean
+orbitWindowResidueCountPow2 n k depth residue
+```
+
+and the tail count is:
+
+```lean
+orbitWindowResidueCountPow2Tail n k depth residue
+```
+
+These count how many source or shifted-tail labels occupy the chosen residue
+cell.
+
+## Conservation
+
+At a fixed depth, every label belongs to exactly one residue cell.
+
+The source conservation theorem is exposed as:
+
+```lean
+sourcePow2Distribution_total
+```
+
+It states:
+
+```text
+sum_{residue < 2^depth}
+  sourceCount(depth, residue)
+    = k
+```
+
+The shifted-tail conservation theorem is:
+
+```lean
+tailPow2Distribution_total
+```
+
+It states:
+
+```text
+sum_{residue < 2^depth}
+  tailCount(depth, residue)
+    = k
+```
+
+Thus source and tail are both finite distributions of total mass `k`.
+
+## Channel Flow
+
+The central abstraction is:
+
+```lean
+pow2ChannelFlow_of_pointwise
+```
+
+Informally:
+
+```text
+If every source label in cell A lands in shifted-tail cell B,
+then occupation(A) <= occupation(B).
+```
+
+The exact shape is:
+
+```text
+pointwise theorem:
+  for every i < k,
+  source residue condition at i
+    -> tail residue condition at i + 1
+
+count theorem:
+  source count <= tail count
+```
+
+This is the finite channel-flow bridge.
+
+## Recursive Two-Adic Petal Instances
+
+The recursive Petal residue channels now use the helper route.
+
+Recovery channel:
+
+```lean
+orbitWindowRecoverySiblingCount_le_tailRetentionResidueCount_via_helper
+```
+
+Continuation channel:
+
+```lean
+orbitWindowContinuationSiblingCount_le_tailRetentionResidueCount_via_helper
+```
+
+These are thin wrappers around:
+
+```lean
+pow2ChannelFlow_of_pointwise
+```
+
+with pointwise inputs:
+
+```lean
+oddOrbitLabel_succ_recovery_residue_of_mod
+oddOrbitLabel_succ_continuation_residue_of_mod
+```
+
+The message is:
+
+```text
+recursive residue arithmetic
+  -> pointwise orbit transition
+  -> count-level channel-flow inequality
+```
+
+## Why This Matters
+
+Before this layer, the project could prove individual pointwise residue
+transitions and some hand-written count inequalities.
+
+After this layer, future channel statements should use the pattern:
+
+```text
+prove pointwise source-to-tail transition
+apply channel-flow helper
+obtain count inequality
+```
+
+This reduces duplication and makes the mathematical structure easier to read.
+
+## Ratio Layer Is Next, But Not Yet Analytic
+
+The natural next question is:
+
+```text
+what fraction of the window occupies a given channel?
+```
+
+However, the first ratio layer should stay in `Nat` inequalities:
+
+```text
+2 * count <= k
+countA + countB <= k
+m <= count
+```
+
+This gives a finite ratio witness without division.
+
+Reasons:
+
+```text
+no zero-window division problem
+no coercion overhead
+no unnecessary real-analysis import pressure
+```
+
+Only after repeated use should the project introduce `ℚ` or `ℝ` frequency
+definitions.
+
+## Later Odd Factor Carrier Layer
+
+The channel-flow layer is still purely 2-adic.
+
+The later odd factor carrier layer would ask:
+
+```text
+inside a fixed two-adic residue cell,
+which odd prime factors appear after the next transition?
+```
+
+That belongs to the next chapter.
+
+The current checkpoint deliberately stops before that layer, so that the
+finite 2-adic channel framework remains clean.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-Overview.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-Overview.md
new file mode 100644
index 00000000..5118810e
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-Overview.md
@@ -0,0 +1,215 @@
+# Collatz Overview
+
+## Purpose
+
+`DkMath.Collatz` formalizes a Collatz research route centered on the
+accelerated odd-state map:
+
+```text
+T(n) = (3n + 1) / 2 ^ v2(3n + 1)
+```
+
+for odd natural states.
+
+The package does not currently claim a proof of the Collatz conjecture.  Its
+role is to build a verified observation language around:
+
+```text
+2-adic height
+residue class
+finite orbit window
+occupation count
+source/tail distribution
+channel flow
+```
+
+This gives a controlled way to discuss where the Collatz map spends its finite
+observation mass and how that mass moves from one residue channel to the next.
+
+## The Accelerated Odd-State View
+
+The ordinary Collatz map alternates between odd and even states.  The
+accelerated map skips the even chain after `3n + 1`.
+
+For an odd state `n`, define:
+
+```text
+s(n) = v2(3n + 1)
+T(n) = (3n + 1) / 2 ^ s(n)
+```
+
+Then `T(n)` is odd again.
+
+In Lean this surface is implemented around:
+
+```lean
+s
+T
+iterateT
+sumS
+```
+
+The quantity `s(n)` is the number of powers of two peeled off at that step.
+The finite sum
+
+```text
+sumS n k = s(n) + s(T n) + ... + s(T^(k-1) n)
+```
+
+is the accumulated 2-adic peeling in the first `k` accelerated steps.
+
+## First Observation: Every Step Peels At Least One Factor
+
+For odd `n`, `3n + 1` is even.  Therefore:
+
+```text
+1 <= s(n)
+```
+
+This gives the first lower bound:
+
+```text
+k <= sumS n k
+```
+
+In the PetalBridge file this becomes the count statement:
+
+```lean
+orbitWindowHeightCountGe_one_eq_window
+```
+
+Every entry in the observation window has height at least `1`.
+
+## Residue Classes As Height Detectors
+
+The bridge uses residue classes to read 2-adic heights.
+
+For odd labels:
+
+```text
+height >= 2  <->  label % 4 = 1
+height = 1   <->  label % 4 = 3
+height >= 3  <->  label % 8 = 5
+```
+
+The exact mod `8` split refines the first layers:
+
+```text
+height = 2        <-> label % 8 = 1
+height = 1        <-> label % 8 = 3 or 7
+height >= 3       <-> label % 8 = 5
+```
+
+This is why residue channels are not just cosmetic.  They expose Collatz
+height information without immediately leaving finite arithmetic.
+
+## Observation Windows
+
+`DkMath.Collatz.PetalBridge` defines a finite observation window:
+
+```lean
+OrbitWindow n k = Finset.range k
+```
+
+and labels it by the odd accelerated orbit:
+
+```lean
+oddOrbitLabel n i = (iterateT i n).val
+orbitWindowHeight n i = v2 (3 * oddOrbitLabel n i + 1)
+```
+
+The window can be read as an ordered height profile:
+
+```lean
+orbitWindowHeightSeq n k
+```
+
+with:
+
+```lean
+(orbitWindowHeightSeq n k).sum = sumS n k
+```
+
+This connects the local finite profile to the existing accumulated-height API.
+
+## From Counts To Distributions
+
+The file then counts how often a finite window enters a chosen residue cell:
+
+```lean
+orbitWindowResidueCountPow2 n k depth residue
+```
+
+This counts labels `i < k` such that:
+
+```text
+oddOrbitLabel n i % 2^depth = residue
+```
+
+The shifted-tail analogue is:
+
+```lean
+orbitWindowResidueCountPow2Tail n k depth residue
+```
+
+which counts labels at times `i + 1` for `i < k`.
+
+The No.100 conservation aliases are:
+
+```lean
+sourcePow2Distribution_total
+tailPow2Distribution_total
+```
+
+They state:
+
+```text
+sum over all source residue cells = k
+sum over all shifted-tail residue cells = k
+```
+
+This is a finite distribution layer.  Every label belongs to exactly one
+residue cell at a fixed power-of-two depth.
+
+## Channel Flow
+
+The central bridge theorem is:
+
+```lean
+pow2ChannelFlow_of_pointwise
+```
+
+It says:
+
+```text
+If every source hit in one residue cell moves to a chosen shifted-tail
+residue cell, then the source occupation count is bounded by the target
+tail occupation count.
+```
+
+This turns pointwise residue arithmetic into count-level channel flow.
+
+## What This Does Not Yet Do
+
+This layer does not prove global convergence.
+
+It also does not yet introduce:
+
+```text
+limits
+probability
+real-valued density
+odd prime factor carriers
+primitive factor events
+```
+
+The point is to keep the current layer finite and exact.  The next ratio layer
+should first use natural-number inequalities such as:
+
+```text
+2 * count <= k
+countA + countB <= k
+m <= count
+```
+
+before introducing rational or real frequencies.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-Package-Structure.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-Package-Structure.md
new file mode 100644
index 00000000..f3832a35
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-Package-Structure.md
@@ -0,0 +1,226 @@
+# Collatz Package Structure
+
+## Current Files
+
+The package currently consists of:
+
+```text
+DkMath.Collatz.Basic
+DkMath.Collatz.V2
+DkMath.Collatz.Accelerated
+DkMath.Collatz.Shift
+DkMath.Collatz.PetalBridge
+DkMath.Collatz.Collatz2K26
+```
+
+There is also a `python/` directory for numerical experiments and historical
+exploration scripts.
+
+## `Basic.lean`
+
+This file provides the lowest-level Collatz vocabulary.
+
+Important names:
+
+```lean
+C
+OddNat
+threeNPlusOne
+```
+
+The later accelerated map is built over `OddNat`, so that the main dynamics
+stay on odd states.
+
+## `V2.lean`
+
+This file contains the 2-adic valuation layer used by Collatz.
+
+Important names:
+
+```lean
+v2
+v2_3n_plus_1_ge_1
+v2_shift_invariant
+```
+
+The main mathematical role is to describe the power of two peeled from
+`3n + 1`.
+
+The theorem `v2_3n_plus_1_ge_1` is the local reason why every accelerated odd
+Collatz step has height at least one.
+
+## `Accelerated.lean`
+
+This file defines the accelerated odd-state dynamics.
+
+Important names:
+
+```lean
+s
+T
+iterateT
+sumS
+driftReal
+```
+
+The theorem work in `PetalBridge` uses `iterateT` to form finite orbit windows
+and `sumS` to connect local height profiles to accumulated Collatz peeling.
+
+## `Shift.lean`
+
+This file belongs to an older but still relevant proof approach:
+
+```text
+block shift / petal cartography
+```
+
+The idea is to compare an odd state `n` with shifted states of the form:
+
+```text
+n + 2^k * m
+```
+
+and ask when the 2-adic valuation behavior stays invariant.
+
+This approach is still useful because it points toward the same structural
+theme that later appears in `PetalBridge`:
+
+```text
+differences concentrate around 2-adic boundaries and singular residue ridges
+```
+
+## `PetalBridge.lean`
+
+This is the current active bridge layer.
+
+It packages the accelerated orbit as a Petal-style finite observation window:
+
+```lean
+OrbitWindow
+oddOrbitLabel
+orbitWindowHeight
+orbitWindowHeightSeq
+```
+
+It then introduces count surfaces:
+
+```lean
+orbitWindowHeightCountEq
+orbitWindowHeightCountGe
+orbitWindowResidueCountPow2
+orbitWindowResidueCountPow2Tail
+```
+
+and the No.100 finite channel-flow aliases:
+
+```lean
+sourcePow2Distribution_total
+tailPow2Distribution_total
+pow2ChannelFlow_of_pointwise
+```
+
+This file is where Collatz dynamics are read as finite channel movement.
+
+## `Collatz2K26.lean`
+
+This is the integration file for the 2026 Collatz cartography route.
+
+It imports:
+
+```lean
+DkMath.Collatz.Basic
+DkMath.Collatz.V2
+DkMath.Collatz.Accelerated
+DkMath.Collatz.Shift
+DkMath.Collatz.PetalBridge
+```
+
+Use this file when checking that the package-level surface still compiles.
+
+## Historical Proof Approaches
+
+### Direct accelerated dynamics
+
+The direct route studies:
+
+```text
+s(n)
+T(n)
+sumS n k
+driftReal
+```
+
+This is the most classical Collatz-facing part of the package.
+
+### Shift invariance / block cartography
+
+The shift route studies how behavior changes under power-of-two block offsets.
+
+It is documented in:
+
+```text
+docs/CollatzCartography.md
+docs/CollatzCartography-ja.md
+```
+
+The guiding concepts are:
+
+```text
+block size 2^k
+petal self-similarity
+singular ridges
+first divergence under offsets
+```
+
+### PetalBridge finite windows
+
+The current route does not start from global convergence.
+
+It starts from finite verified observations:
+
+```text
+finite window
+height profile
+residue occupation
+source/tail distribution
+channel flow
+```
+
+This is deliberately local.  It avoids making probabilistic or asymptotic
+claims before the finite theorem surface is stable.
+
+## Python Experiments
+
+The `python/` directory contains numerical scripts for cartography-style
+experiments.
+
+These scripts are not formal proofs.  They help identify patterns such as:
+
+```text
+where residue differences arise
+how long shift invariance persists
+which finite windows show concentrated behavior
+```
+
+The Lean side then decides which observations are real theorem candidates.
+
+## Suggested Reading Order
+
+For current development:
+
+```text
+1. README.md
+2. docs/Collatz-Overview.md
+3. docs/Collatz-Package-Structure.md
+4. docs/Collatz-FiniteChannelFlow-100.md
+5. docs/Collatz-PetalBridge-Guide.md
+6. docs/Collatz-PetalBridge-Status.md
+```
+
+For historical context:
+
+```text
+docs/CollatzCartography.md
+docs/IMPLEMENTATION_REPORT_20260130.md
+docs/SORRY_CLEANUP_PROGRESS_20260130.md
+```
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
new file mode 100644
index 00000000..d7185f79
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
@@ -0,0 +1,285 @@
+# Collatz PetalBridge Guide
+
+## Why PetalBridge Exists
+
+`DkMath.Collatz.PetalBridge` connects accelerated Collatz dynamics to the
+Petal observation style used elsewhere in DkMath.
+
+The Petal side already has language for:
+
+```text
+finite ranges
+addresses
+occupation counts
+separation vs collision
+boundary and channel behavior
+```
+
+The Collatz side has:
+
+```text
+odd states
+2-adic height
+accelerated transition
+finite orbit segments
+```
+
+`PetalBridge` is the file where these languages meet.
+
+## Basic Objects
+
+### `OrbitWindow`
+
+```lean
+OrbitWindow n k
+```
+
+This is the finite observation window of length `k`.
+
+It is definitionally:
+
+```text
+Finset.range k
+```
+
+### `oddOrbitLabel`
+
+```lean
+oddOrbitLabel n i
+```
+
+This is the natural value of the `i`-th accelerated odd state:
+
+```text
+(iterateT i n).val
+```
+
+### `orbitWindowHeight`
+
+```lean
+orbitWindowHeight n i
+```
+
+This is:
+
+```text
+v2 (3 * oddOrbitLabel n i + 1)
+```
+
+It is the local 2-adic peeling height.
+
+### `orbitWindowHeightSeq`
+
+```lean
+orbitWindowHeightSeq n k
+```
+
+This is the ordered list of the first `k` height values.
+
+The bridge theorem:
+
+```lean
+orbitWindowHeightSeq_sum_eq_sumS
+```
+
+connects the ordered list back to the accumulated Collatz height:
+
+```text
+(orbitWindowHeightSeq n k).sum = sumS n k
+```
+
+## Separation And Collision
+
+The bridge includes a finite split:
+
+```lean
+OrbitWindowSeparated n k
+OrbitWindowCollision n k
+orbitWindowSeparated_or_collision
+```
+
+This reads:
+
+```text
+either the first k odd orbit labels are separated,
+or there is a collision inside the window
+```
+
+The Petal reading:
+
+```text
+separated labels support independent finite counting
+collision is an obstruction to that independent route
+```
+
+The Collatz reading:
+
+```text
+collision means the accelerated odd state has merged/folded
+```
+
+This split is finite.  It is not a global convergence theorem.
+
+## Height Counts
+
+The file defines exact and threshold height counts:
+
+```lean
+orbitWindowHeightCountEq
+orbitWindowHeightCountGe
+orbitWindowHeightCountEqTail
+orbitWindowHeightCountGeTail
+```
+
+These are finite `Nat` counts.
+
+They support layer-cake style bounds such as:
+
+```lean
+orbitWindowHeightSeq_sum_ge_sum_countGe_range
+orbitWindowHeightSeq_sum_ge_window_add_sum_countGe_tail
+```
+
+The important Collatz floor is:
+
+```lean
+orbitWindowHeightCountGe_one_eq_window
+```
+
+Every odd accelerated state has height at least `1`.
+
+## Residue Counts
+
+Named residue counts exist for low layers:
+
+```lean
+orbitWindowResidueCountMod4EqOne
+orbitWindowResidueCountMod4EqThree
+orbitWindowResidueCountMod8EqOne
+orbitWindowResidueCountMod8EqThree
+orbitWindowResidueCountMod8EqFive
+orbitWindowResidueCountMod8EqSeven
+```
+
+The generic power-of-two count is:
+
+```lean
+orbitWindowResidueCountPow2 n k depth residue
+```
+
+The shifted-tail version is:
+
+```lean
+orbitWindowResidueCountPow2Tail n k depth residue
+```
+
+This generic surface is the current preferred route for new residue-channel
+work.
+
+## Distribution Conservation
+
+Checkpoint 100 exposes the conservation laws as conceptual aliases:
+
+```lean
+sourcePow2Distribution_total
+tailPow2Distribution_total
+```
+
+These say that every finite source or shifted-tail window is fully partitioned
+by its `2^depth` residue cells.
+
+This gives the exact finite analogue of:
+
+```text
+total distribution mass = window size
+```
+
+but still in `Nat`.
+
+## Channel Flow
+
+The main helper is:
+
+```lean
+pow2ChannelFlow_of_pointwise
+```
+
+Use it when you have a pointwise theorem of the form:
+
+```text
+for all i < k,
+  source cell condition at i
+    -> target tail cell condition at i + 1
+```
+
+The helper returns:
+
+```text
+source cell count <= target tail cell count
+```
+
+This is the theorem to reach for before writing a custom induction over `k`.
+
+## Recursive Petal Residues
+
+The current recursive two-adic Petal channels are:
+
+```lean
+twoAdicRetentionResidue
+twoAdicRecoverySiblingResidue
+twoAdicContinuationSiblingResidue
+```
+
+The count-level recursive instances are now available through helper-routed
+theorems:
+
+```lean
+orbitWindowRecoverySiblingCount_le_tailRetentionResidueCount_via_helper
+orbitWindowContinuationSiblingCount_le_tailRetentionResidueCount_via_helper
+```
+
+This fixes the intended proof route:
+
+```text
+residue formula
+  -> pointwise orbit-label transition
+  -> finite channel-flow count inequality
+```
+
+## How To Add A New Channel Theorem
+
+For a new residue channel:
+
+1. Prove the pointwise transition:
+
+```text
+if oddOrbitLabel n i is in source cell A,
+then oddOrbitLabel n (i + 1) is in tail cell B.
+```
+
+2. Apply:
+
+```lean
+pow2ChannelFlow_of_pointwise
+```
+
+3. State a named theorem for the channel:
+
+```text
+sourceChannelCount <= tailChannelCount
+```
+
+Avoid writing a fresh count induction unless the helper does not fit.
+
+## Next Work
+
+The next layer should probably introduce finite ratio witnesses, but still as
+natural-number inequalities:
+
+```text
+2 * count <= k
+countA + countB <= k
+m <= count
+```
+
+Only later should this become rational or real frequency.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index 4ed08523..9268ab69 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -172,6 +172,9 @@ orbitWindowResidueCountPow2Tail_sum_eq_window
 orbitWindowResidueCountPow2_le_tail_of_pointwise
 orbitWindowResidueCountPow2_depth_three_sum_eq_window
 orbitWindowResidueCountPow2Tail_depth_three_sum_eq_window
+sourcePow2Distribution_total
+tailPow2Distribution_total
+pow2ChannelFlow_of_pointwise
 orbitWindowPrefixResidueCountMod4EqOne_le_prefix
 orbitWindowPrefixResidueCountMod4EqOne_eq_residueCount
 orbitWindowHeightCountGe_two_eq_residueCount_mod4_eq_one
@@ -605,6 +608,11 @@ depth `3` shifted-tail distribution sanity
 helper-routed recursive two-adic Petal channels
   -> recovery source <= outward-retention tail
   -> continuation source <= next-retention tail
+
+No.100 finite channel-flow aliases
+  -> sourcePow2Distribution_total
+  -> tailPow2Distribution_total
+  -> pow2ChannelFlow_of_pointwise
 ```
 
 This is the first distribution layer.  It still avoids importing the heavier
@@ -646,6 +654,17 @@ Recursive two-adic Petal instances:
   continuation source <= next-retention tail
 ```
 
+The No.100 entry documents for this layer are:
+
+```text
+README.md
+docs/Collatz-Overview.md
+docs/Collatz-Package-Structure.md
+docs/Collatz-FiniteChannelFlow-100.md
+docs/Collatz-PetalBridge-Guide.md
+../Petal/docs/Petal-CollatzBridge.md
+```
+
 The next ratio layer should initially stay in `Nat` inequalities rather than
 introducing `ℚ` or `ℝ` frequencies:
 
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-CollatzBridge.md b/lean/dk_math/DkMath/Petal/docs/Petal-CollatzBridge.md
new file mode 100644
index 00000000..dad8bcfd
--- /dev/null
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-CollatzBridge.md
@@ -0,0 +1,212 @@
+# Petal And Collatz Bridge
+
+## Purpose
+
+This document records how the Petal package connects to the Collatz package.
+
+The bridge is implemented on the Collatz side:
+
+```text
+DkMath.Collatz.PetalBridge
+```
+
+but the conceptual reason it works comes from Petal-style finite observation:
+
+```text
+finite range
+address / residue cell
+occupation count
+separation or collision
+channel movement
+```
+
+## Petal View
+
+The Petal package studies finite structured observation surfaces.
+
+In number-theory work this appears as:
+
+```text
+GN kernels
+boundary / beam / gap separation
+primitive factor support
+range-family labels
+obstruction when labels collide
+```
+
+The Collatz bridge uses the same kind of language, but the labels are not GN
+terms.  They are accelerated Collatz odd orbit labels:
+
+```text
+oddOrbitLabel n i = value of T^i(n)
+```
+
+## Collatz View
+
+The accelerated Collatz map has a natural Petal-like coordinate:
+
+```text
+2-adic residue class modulo 2^depth
+```
+
+At a fixed depth, all odd orbit labels fall into exactly one residue cell.
+
+This allows Collatz to be read as:
+
+```text
+finite source distribution
+finite shifted-tail distribution
+pointwise channel transition
+count-level channel flow
+```
+
+## The Bridge Object
+
+The finite window is:
+
+```lean
+OrbitWindow n k = Finset.range k
+```
+
+The label function is:
+
+```lean
+oddOrbitLabel n i
+```
+
+The height function is:
+
+```lean
+orbitWindowHeight n i
+```
+
+The generic source count is:
+
+```lean
+orbitWindowResidueCountPow2 n k depth residue
+```
+
+The generic shifted-tail count is:
+
+```lean
+orbitWindowResidueCountPow2Tail n k depth residue
+```
+
+## No.100 Finite Channel-Flow Layer
+
+The Collatz side exposes the theorem chain with conceptual names:
+
+```lean
+sourcePow2Distribution_total
+tailPow2Distribution_total
+pow2ChannelFlow_of_pointwise
+```
+
+Petal reading:
+
+```text
+source distribution total is conserved
+tail distribution total is conserved
+pointwise motion of labels induces count-level channel flow
+```
+
+Collatz reading:
+
+```text
+residue cells of odd orbit labels form a finite distribution
+one-step residue transitions push source mass into tail cells
+```
+
+## Why This Matters For Petal
+
+Petal theory often separates two cases:
+
+```text
+labels remain separated
+labels collide and the independent route closes as False
+```
+
+Collatz orbit windows have the same finite split:
+
+```lean
+OrbitWindowSeparated
+OrbitWindowCollision
+orbitWindowSeparated_or_collision
+```
+
+This makes Collatz a testbed for Petal observation logic:
+
+```text
+finite observation window
+label uniqueness or collision
+address cells
+occupation counts
+channel transitions
+obstruction when the independent counting picture breaks
+```
+
+## Relation To Existing Petal RangeFamily
+
+`DkMath.Petal.RangeFamily` provides a range-indexed observation layer:
+
+```text
+I = Finset.range k
+qOf i = selected label at index i
+```
+
+It can express:
+
+```text
+pairwise label separation
+same label at two distinct indices -> False
+```
+
+The Collatz bridge uses this spirit, but specializes the labels to the
+accelerated odd orbit.
+
+## What Is Not Yet Connected
+
+The Collatz bridge currently remains 2-adic.
+
+It does not yet connect Collatz channel occupation to:
+
+```text
+GN primitive factors
+odd prime carriers
+Zsigmondy witnesses
+ABC support/radical estimates
+```
+
+Those are later chapters.
+
+The immediate next layer should be finite ratio witnesses, still written as
+natural-number inequalities:
+
+```text
+2 * count <= k
+countA + countB <= k
+m <= count
+```
+
+This keeps the Petal-Collatz bridge elementary before it is attached to
+heavier factor-support machinery.
+
+## Reading Pointers
+
+Collatz side:
+
+```text
+DkMath/Collatz/README.md
+DkMath/Collatz/docs/Collatz-Overview.md
+DkMath/Collatz/docs/Collatz-FiniteChannelFlow-100.md
+DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
+DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+```
+
+Petal side:
+
+```text
+DkMath/Petal/docs/Petal-Overview.md
+DkMath/Petal/docs/Petal-Zsigmondy-Preflight.md
+DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md
+```
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
index 4932fae0..6055ec8b 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
@@ -46,6 +46,24 @@ Phase 5: Zsigmondy preparation
 It is not a replacement for the number-theory route.  It is a structured
 observation layer used before primitive prime divisors are studied directly.
 
+There is now also a Collatz-facing bridge note:
+
+```text
+DkMath/Petal/docs/Petal-CollatzBridge.md
+```
+
+That bridge uses Petal-style finite range, occupation, and channel-flow
+language to read accelerated Collatz orbit windows.  It is separate from the
+Zsigmondy route, but it tests the same observation discipline:
+
+```text
+finite labels
+residue/address cells
+occupation counts
+source/tail conservation
+pointwise transition -> count-level flow
+```
+
 ## Why Petal Counting Was Needed
 
 The long-term target includes continuous-dimensional or dimension-parametric
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-100.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-100.md
new file mode 100644
index 00000000..50e67f0f
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-100.md
@@ -0,0 +1,288 @@
+# Report Petal 100: Collatz Finite Channel-Flow Documentation Checkpoint
+
+## Checkpoint
+
+This checkpoint follows `__next_implementation-100.md` and the conductor's
+additional instruction:
+
+```text
+make No.100 a documentation-heavy consolidation checkpoint
+```
+
+The main work was to document the Collatz package, the recent finite
+channel-flow layer, and the Petal-Collatz bridge in a way that remains useful
+after the development context has been forgotten.
+
+## Lean Surface Added
+
+Added three thin conceptual aliases in `DkMath.Collatz.PetalBridge`:
+
+```lean
+theorem sourcePow2Distribution_total
+theorem tailPow2Distribution_total
+theorem pow2ChannelFlow_of_pointwise
+```
+
+These do not add new mathematical burden.  They expose the No.100 theorem
+chain with conceptual names:
+
+```text
+source distribution conservation
+tail distribution conservation
+pointwise transition -> finite channel flow
+```
+
+They wrap:
+
+```lean
+orbitWindowResidueCountPow2_sum_eq_window
+orbitWindowResidueCountPow2Tail_sum_eq_window
+orbitWindowResidueCountPow2_le_tail_of_pointwise
+```
+
+## Documentation Created
+
+### Collatz package entry
+
+Created:
+
+```text
+lean/dk_math/DkMath/Collatz/README.md
+```
+
+Purpose:
+
+```text
+module entry document
+package map
+current milestone summary
+reading order
+future direction
+```
+
+It introduces the package as:
+
+```text
+odd state dynamics
+  -> 2-adic height
+  -> residue channels
+  -> finite observation windows
+  -> source/tail distributions
+  -> finite channel flow
+```
+
+### Collatz overview
+
+Created:
+
+```text
+lean/dk_math/DkMath/Collatz/docs/Collatz-Overview.md
+```
+
+Purpose:
+
+```text
+mathematical overview of the accelerated odd-state map
+height and residue interpretation
+finite observation windows
+distribution conservation
+channel flow
+```
+
+### Package structure
+
+Created:
+
+```text
+lean/dk_math/DkMath/Collatz/docs/Collatz-Package-Structure.md
+```
+
+Purpose:
+
+```text
+file-by-file package explanation
+older proof approaches
+current PetalBridge route
+Python experiment role
+suggested reading order
+```
+
+It explicitly records older routes:
+
+```text
+direct accelerated dynamics
+shift invariance / block cartography
+finite PetalBridge windows
+```
+
+### Finite channel-flow checkpoint
+
+Created:
+
+```text
+lean/dk_math/DkMath/Collatz/docs/Collatz-FiniteChannelFlow-100.md
+```
+
+Purpose:
+
+```text
+No.100 theorem chain summary
+source/tail distribution conservation
+channel-flow helper
+recursive two-adic Petal instances
+next Nat-ratio layer
+later odd factor carrier layer
+```
+
+This is the central math explanation document for the checkpoint.
+
+### PetalBridge guide
+
+Created:
+
+```text
+lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
+```
+
+Purpose:
+
+```text
+how to use PetalBridge
+what each major definition means
+how to add new channel theorems
+why pow2ChannelFlow_of_pointwise should be preferred
+```
+
+### Petal-side bridge
+
+Created:
+
+```text
+lean/dk_math/DkMath/Petal/docs/Petal-CollatzBridge.md
+```
+
+Purpose:
+
+```text
+Petal-facing explanation of Collatz.PetalBridge
+finite range / occupation / channel-flow reading
+what is connected now
+what remains separate
+```
+
+## Documentation Updated
+
+Updated:
+
+```text
+lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
+```
+
+The status document now includes the No.100 conceptual aliases and points to
+the new entry documents.
+
+The Petal overview now points to the new Petal-Collatz bridge document.
+
+## Mathematical State After No.100
+
+The current theorem chain is:
+
+```text
+Residue arithmetic:
+  labels have computable 2-adic residue behavior
+
+Orbit-label transition:
+  source residue condition implies shifted-tail residue condition
+
+Source distribution:
+  sum source cells = k
+
+Tail distribution:
+  sum tail cells = k
+
+Channel-flow helper:
+  pointwise source-to-tail transition
+    -> source occupation <= tail occupation
+
+Recursive two-adic Petal instances:
+  recovery source <= outward-retention tail
+  continuation source <= next-retention tail
+```
+
+The conceptual aliases make this readable:
+
+```lean
+sourcePow2Distribution_total
+tailPow2Distribution_total
+pow2ChannelFlow_of_pointwise
+```
+
+## Inference
+
+No.100 should be treated as the closure of the first Collatz/Petal finite
+channel-flow chapter.
+
+The current layer is deliberately finite:
+
+```text
+no limits
+no probability
+no real-valued density
+no odd prime carrier yet
+```
+
+This is a strength, not a gap.  It means later ratio and factor layers can be
+attached to exact finite conservation laws rather than informal numerical
+distribution language.
+
+## Next Implementation Candidates
+
+The next layer should be a finite ratio witness layer, but still in `Nat`.
+
+Recommended first definitions or theorem style:
+
+```text
+2 * count <= k
+countA + countB <= k
+m <= count
+```
+
+Avoid introducing `ℚ` or `ℝ` until the Nat inequality API shows repeated need.
+
+Candidate next documents or definitions:
+
+```text
+FiniteRatioWitness
+RetentionMass(depth r)
+RecoverySiblingMass(depth r)
+ContinuationSiblingMass(depth r)
+```
+
+The odd factor carrier layer should remain a later chapter:
+
+```text
+same two-adic cell
+  -> next odd core
+  -> new odd prime factor event
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
