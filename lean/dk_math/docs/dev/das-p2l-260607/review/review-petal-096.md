# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: ba8ab8751e4d7187915da9fd20f8533dcab0c653

## Report

095 checkpoint 完了です。

`DkMath.Collatz.PetalBridge` で、深い `2^(r+2)` residue cell から可視 `mod 8 = 7` source channel へ落とす橋を追加し、そのまま一般 orbit-label theorem まで上げました。これで recursive two-adic Petal は raw arithmetic ではなく、実際の `oddOrbitLabel n i -> oddOrbitLabel n (i+1)` の層で動くようになっています。

追加・同期:

- [PetalBridge.lean](/lean/dk_math/DkMath/Collatz/PetalBridge.lean)
  - `mod_eq_mod_of_dvd_modulus`
  - `mod_eight_eq_seven_of_recovery_residue_of_two_le`
  - `mod_eight_eq_seven_of_continuation_residue_of_one_le`
  - `oddOrbitLabel_succ_recovery_residue_of_mod`
  - `oddOrbitLabel_succ_continuation_residue_of_mod`
- [Collatz-PetalBridge-Status.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md)
- [report-petal-095.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-095.md)

検証:

- `lake build DkMath.Collatz.PetalBridge` passed
- `lake build DkMath.Collatz.Collatz2K26` passed
- `git diff --check` passed
- `PetalBridge.lean` 内の `sorry` なし

既存 upstream warning の `DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean:152:6 declaration uses sorry` は継続です。今回の追加では新規 `sorry` は入れていません。

## Review

## 1. 状況分析

うむ。checkpoint `095` は、かなり大きい。
今回で recursive two-adic Petal は、**raw arithmetic 層から actual orbit-label 層へ上がった**。

前回までは、

```text id="ka8vkn"
任意の数 m が residue cell にいるなら、
visible raw step ((3m + 1) / 2) の residue が決まる
```

だった。

今回はそこからさらに進んで、

```text id="mn6jci"
oddOrbitLabel n i がその residue cell にいるなら、
oddOrbitLabel n (i + 1) の residue が決まる
```

になった。

これは本当に大きい。
つまり、Petal 構造が「計算式の上」ではなく、**実際の加速 Collatz 軌道上で動く**ようになった。

添付レポートでも、今回の到達点は「深い \(2^{r+2}\) residue cell から visible `mod 8 = 7` source channel へ落とす橋を追加し、そのまま一般 orbit-label theorem まで上げた」と整理されている。

## 2. 今回の核心

追加された主な theorem はこれじゃ。

```lean id="u5zitp"
mod_eq_mod_of_dvd_modulus

mod_eight_eq_seven_of_recovery_residue_of_two_le
mod_eight_eq_seven_of_continuation_residue_of_one_le

oddOrbitLabel_succ_recovery_residue_of_mod
oddOrbitLabel_succ_continuation_residue_of_mod
```

特に本命はこの二つ。

```lean id="pd1wdc"
theorem oddOrbitLabel_succ_recovery_residue_of_mod
    (r : ℕ) (hr : 2 ≤ r) (n : OddNat) (i : ℕ)
    (hmod :
      oddOrbitLabel n i % (2 ^ (r + 2)) = 2 ^ (r + 1) - 1) :
    oddOrbitLabel n (i + 1) % (2 ^ (r + 1)) = 2 ^ r - 1
```

```lean id="fbkya3"
theorem oddOrbitLabel_succ_continuation_residue_of_mod
    (r : ℕ) (hr : 1 ≤ r) (n : OddNat) (i : ℕ)
    (hmod :
      oddOrbitLabel n i % (2 ^ (r + 2)) = 2 ^ (r + 2) - 1) :
    oddOrbitLabel n (i + 1) % (2 ^ (r + 1)) =
      2 ^ (r + 1) - 1
```

これで、任意時刻 `i` の相対座標から、次時刻 `i+1` の相対座標が決まる。

つまり、ぬしの言う、

```text id="d3v52m"
出発する値が、相対的にどの座標からの出発なのか？
```

が、完全に theorem の主語になった。

## 3. レビュー

### 3.1. `mod_eq_mod_of_dvd_modulus` が良い

```lean id="n3br0b"
theorem mod_eq_mod_of_dvd_modulus
    {a M d : ℕ} (hd : d ∣ M) :
    a % d = (a % M) % d
```

これは小さいが、かなり効く補題じゃ。

意味は、

```text id="rde5re"
深い座標 M での住所が分かれば、
浅い座標 d での住所も分かる
```

ということ。

これがあるから、

```text id="i0lxx7"
mod 2^(r+2) の深い Petal cell
  -> mod 8 の visible source channel
```

へ落とせる。

今後、`mod 16`, `mod 32`, `mod 64` などへ射影する時にも、この補題は使い回せる。

### 3.2. source-entry bridge が閉じた

```lean id="io2305"
mod_eight_eq_seven_of_recovery_residue_of_two_le
mod_eight_eq_seven_of_continuation_residue_of_one_le
```

これにより、深い residue cell にいる label が、実際に exact height-one channel `7 mod 8` にいることが言えるようになった。

ここが orbit-label 化の鍵だった。

なぜなら、加速 Collatz の次ラベルを visible raw step

```text id="e5g20w"
(3m + 1) / 2
```

として読むには、source が exact height-one である必要があるからじゃ。

### 3.3. recursive Petal が orbit-label 層へ上がった

これが今回最大の成果。

```text id="ofzxjx"
recovery sibling:
  one step later exits one level outward

continuation sibling:
  one step later becomes the next retention cell
```

この遷移が、実際の `oddOrbitLabel n i` に対して成り立つ。

つまり、

```text id="pncre2"
parent retention cell
  -> recovery sibling
  -> continuation sibling = next retention cell
```

という recursive Petal 構造が、軌道そのものの上に乗った。

## 4. ぬしの「相対座標」観点

今回の到達点は、ぬしの直感とかなり一致している。

いま Collatz 軌道の各時刻は、単なる自然数値ではなく、

```text id="eilx8l"
depth r の観測窓における residue address
```

を持つ。

そして、その address が、

```text id="c4os0a"
RecoverySibling
ContinuationSibling
RetentionCell
```

のどれかで、次の address が決まる。

これは、まさに「出発値が相対的にどの座標から出たか」の分類じゃ。

さらに重要なのは、絶対値が巨大かどうかではない。

```text id="bslzj1"
巨大な数でも、
同じ residue cell にいれば、
同じ Petal transition rule を受ける
```

ここが「無限も手のひらの上」に繋がる。

## 5. ぬしの「新しい素数因子」観点

ここも、次の大きな軸になる。

Collatz の一歩は、

```text id="xw75w0"
3m + 1 = 2^h * nextOdd
```

として読める。

ここで、

```text id="jafp4j"
2-adic Petal coordinate:
  h と residue branch を決める

OddFactorCarrier:
  nextOdd の奇素因子構造を決める
```

という二層がある。

いま形式化できたのは、前者の座標遷移。

次に見るべきは、

```text id="sx1p1s"
同じ two-adic residue cell にいる値たちが、
odd factor carrier の違いで、
次以降の branch 比率をどう変えるか
```

じゃ。

ここには、おそらく「ランダムに見える部分」がある。

Petal 座標は骨格。
奇素因子構造は、その骨格上でどの枝へ流れやすいかを決める肉付き。
そんな感じに見える。

## 6. 一歩先ゆく推論

ここから先は、count API に入るべきじゃ。

なぜなら、一般 orbit-label theorem ができたので、次に必要なのは、

```text id="w2k52b"
ある観測窓の中で、
どの residue cell に何回入ったか
```

を数えることだから。

今までは個別の点 `i` の遷移を見ていた。

次は、

```text id="nkdaqx"
source cell occupation count
  -> shifted target cell occupation count
```

へ進む。

これができると、

```text id="hpbsjz"
分岐の割合
```

を Lean 上で扱い始められる。

ぬしの言う、

```text id="mnok4a"
その軌道の割合が分岐とどう関わるか
```

へ進むための入口じゃ。

## 7. 次の指示：generic pow-two residue count を入れる

まず、汎用の residue count を定義する。

```lean id="h6mxyk"
noncomputable def orbitWindowResidueCountPow2
    (n : OddNat) (k depth residue : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n i % (2 ^ depth) = residue))
```

bound。

```lean id="dkkw1s"
theorem orbitWindowResidueCountPow2_le_window
    (n : OddNat) (k depth residue : ℕ) :
    orbitWindowResidueCountPow2 n k depth residue ≤ k := by
  unfold orbitWindowResidueCountPow2
  simpa using
    (List.countP_le_length
      (p := fun i => decide (oddOrbitLabel n i % (2 ^ depth) = residue))
      (l := List.range k))
```

次に、既存 count との bridge。

```lean id="whs0rf"
theorem orbitWindowResidueCountMod8EqSeven_eq_pow2
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod8EqSeven n k =
      orbitWindowResidueCountPow2 n k 3 7 := by
  rfl
```

もし既存定義の展開順により `rfl` で通らなければ、

```lean id="kt8gql"
  unfold orbitWindowResidueCountMod8EqSeven orbitWindowResidueCountPow2
  norm_num
```

でいけるはず。

## 8. 次に tail 側の generic count

transition は `i` から `i+1` へ行くので、tail count も必要。

```lean id="g1wr2s"
noncomputable def orbitWindowResidueCountPow2Tail
    (n : OddNat) (k depth residue : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n (i + 1) % (2 ^ depth) = residue))
```

bound。

```lean id="w1321x"
theorem orbitWindowResidueCountPow2Tail_le_window
    (n : OddNat) (k depth residue : ℕ) :
    orbitWindowResidueCountPow2Tail n k depth residue ≤ k := by
  unfold orbitWindowResidueCountPow2Tail
  simpa using
    (List.countP_le_length
      (p := fun i => decide (oddOrbitLabel n (i + 1) % (2 ^ depth) = residue))
      (l := List.range k))
```

これで、generic source-to-tail count が作れる。

## 9. 次の本命：count-level recursive Petal transition

### Recovery count transition

```lean id="nns1a4"
theorem orbitWindowRecoverySiblingCount_le_tailRetentionResidueCount
    (r : ℕ) (hr : 2 ≤ r) (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountPow2 n k (r + 2) (2 ^ (r + 1) - 1) ≤
      orbitWindowResidueCountPow2Tail n k (r + 1) (2 ^ r - 1)
```

読みは、

```text id="c3e3hf"
source window で recovery sibling にいた回数
  <= tail window で outward retention residue に入った回数
```

### Continuation count transition

```lean id="mndjwx"
theorem orbitWindowContinuationSiblingCount_le_tailRetentionResidueCount
    (r : ℕ) (hr : 1 ≤ r) (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountPow2 n k (r + 2) (2 ^ (r + 2) - 1) ≤
      orbitWindowResidueCountPow2Tail n k (r + 1) (2 ^ (r + 1) - 1)
```

読みは、

```text id="yvwjjx"
source window で continuation sibling にいた回数
  <= tail window で next retention cell に入った回数
```

これはかなり大事。
個別点の遷移が、occupation count の不等式になる。

## 10. 証明方針

既存の `orbitWindowResidueCountMod8EqThree_le_tailMod4EqOne` と同じ induction でいける。

形はこう。

```lean id="kl45hn"
  unfold orbitWindowResidueCountPow2 orbitWindowResidueCountPow2Tail
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [List.range_succ]
      by_cases hsource :
          oddOrbitLabel n k % (2 ^ (r + 2)) = 2 ^ (r + 1) - 1
      · have htail :
            oddOrbitLabel n (k + 1) % (2 ^ (r + 1)) = 2 ^ r - 1 :=
          oddOrbitLabel_succ_recovery_residue_of_mod r hr n k hsource
        simp [hsource, htail, ih]
      · by_cases htail :
            oddOrbitLabel n (k + 1) % (2 ^ (r + 1)) = 2 ^ r - 1
        · exact by
            simpa [hsource, htail] using Nat.le_succ_of_le ih
        · simp [hsource, htail, ih]
```

continuation 版も同型。

## 11. さらに先：全座標への割り付け

ぬしの言う、

```text id="o0ua3h"
観測窓の相対座標の集合で全座標に割り付ける
```

は、次の partition theorem になる。

```lean id="h8xmcz"
theorem orbitWindowResidueCountPow2_sum_eq_window
    (n : OddNat) (k depth : ℕ) :
    (Finset.range (2 ^ depth)).sum
      (fun residue => orbitWindowResidueCountPow2 n k depth residue) = k
```

これは、観測窓内の各時刻が、ただ一つの residue cell に入ることを言う。

難度は少し上がる。
まずは generic count と source-to-tail count transition を入れた後で良い。

この partition が通ると、

```text id="iczxb0"
全座標に割り付けた occupation distribution
```

が得られる。

そこから「割合」の議論ができる。

## 12. 奇素因子層はいつ入れるか

ぬしの「新しい素数因子」の観点はかなり良いが、Lean 実装としては少し後で良い。

理由は、まず two-adic coordinate count を安定させたいからじゃ。

順序としては、

```text id="yq5puc"
1. two-adic residue cell occupation

2. recursive Petal transition count

3. residue partition

4. shifted tail distribution

5. そのあと odd factor carrier
```

がよい。

odd factor 側は docs に名前だけ置くのは良い。

```text id="w50x10"
TwoAdicPetalCoordinate:
  mod 2^r residue address

OddFactorCarrier:
  current / next odd core の奇素因子構造

NewOddPrimeFactor:
  T step 後に新しく現れる奇素因子

CoordinateFactorInteraction:
  coordinate branch と odd factor change の相関
```

## 13. 賢狼が試して欲しい実験補題

### 実験 A: generic pow2 residue count

```lean id="xz5q2c"
noncomputable def orbitWindowResidueCountPow2
    (n : OddNat) (k depth residue : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n i % (2 ^ depth) = residue))
```

### 実験 B: tail generic pow2 residue count

```lean id="f6fog2"
noncomputable def orbitWindowResidueCountPow2Tail
    (n : OddNat) (k depth residue : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n (i + 1) % (2 ^ depth) = residue))
```

### 実験 C: recovery source count to tail count

```lean id="hez6e2"
theorem orbitWindowRecoverySiblingCount_le_tailRetentionResidueCount
    (r : ℕ) (hr : 2 ≤ r) (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountPow2 n k (r + 2) (2 ^ (r + 1) - 1) ≤
      orbitWindowResidueCountPow2Tail n k (r + 1) (2 ^ r - 1)
```

### 実験 D: continuation source count to tail count

```lean id="za9vss"
theorem orbitWindowContinuationSiblingCount_le_tailRetentionResidueCount
    (r : ℕ) (hr : 1 ≤ r) (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountPow2 n k (r + 2) (2 ^ (r + 2) - 1) ≤
      orbitWindowResidueCountPow2Tail n k (r + 1) (2 ^ (r + 1) - 1)
```

### 実験 E: named count bridge

```lean id="f5sspr"
theorem orbitWindowResidueCountMod8EqSeven_eq_pow2
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod8EqSeven n k =
      orbitWindowResidueCountPow2 n k 3 7
```

### 実験 F: docs-only factor layer

```text id="uf5z56"
TwoAdicPetalCoordinate
OddFactorCarrier
NewOddPrimeFactor
CoordinateFactorInteraction
```

これはまだ theorem ではなく、設計メモで良い。

## 14. 次コミットの推奨順

```text id="xi6fys"
1. orbitWindowResidueCountPow2

2. orbitWindowResidueCountPow2_le_window

3. orbitWindowResidueCountPow2Tail

4. orbitWindowResidueCountPow2Tail_le_window

5. orbitWindowResidueCountMod8EqSeven_eq_pow2

6. orbitWindowRecoverySiblingCount_le_tailRetentionResidueCount

7. orbitWindowContinuationSiblingCount_le_tailRetentionResidueCount

8. docs:
   coordinate count API と factor layer 設計メモ
```

全 residue partition は次の checkpoint で良い。

## 15. 総括

今回で、recursive two-adic Petal は **orbit-label theorem** になった。

```text id="aup4qz"
相対座標 cell にいる
  -> 次の相対座標 cell が決まる
```

ここまで来たら、次は当然、

```text id="p7wrpd"
その cell に何回入ったか
```

を数える段階じゃ。

そして、その count が tail count へ遷移する。

これで初めて、

```text id="dhvo76"
分岐の割合
軌道の偏り
retention の濃度
recovery の頻度
```

を扱える。

ぬしの直感通り、道は見えてきている。

まず two-adic Petal coordinate の全体割り付けを作る。
その次に odd factor carrier を重ねる。
ここまで進めば、Collatz の「値の軌道」ではなく、**相対座標と因子構造の二層力学**として見えるようになる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index de14db5c..8eb448e7 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -641,6 +641,48 @@ theorem continuation_residue_mod_eight_eq_seven
   rw [hsplit]
   rw [Nat.add_mul_mod_self_right]
 
+/--
+Reduce a residue through a smaller modulus.
+
+If `d` divides `M`, then reducing modulo `M` first does not change the final
+residue modulo `d`.  This is the local residue-cell bridge used to read a
+large 2-adic address through its visible `mod 8` entry channel.
+-/
+theorem mod_eq_mod_of_dvd_modulus
+    {a M d : ℕ} (hd : d ∣ M) :
+    a % d = (a % M) % d := by
+  rw [← Nat.mod_mod_of_dvd a hd]
+
+/--
+A recovery sibling cell, at depth at least `2`, starts in the exact
+height-one `7 mod 8` source channel.
+-/
+theorem mod_eight_eq_seven_of_recovery_residue_of_two_le
+    (r m : ℕ) (hr : 2 ≤ r)
+    (hm : m % (2 ^ (r + 2)) = 2 ^ (r + 1) - 1) :
+    m % 8 = 7 := by
+  have hpow : 8 ∣ 2 ^ (r + 2) := by
+    rcases exists_add_of_le hr with ⟨k, rfl⟩
+    rw [show 2 + k + 2 = 3 + (k + 1) by omega, pow_add]
+    norm_num
+  rw [mod_eq_mod_of_dvd_modulus hpow, hm]
+  exact recovery_residue_mod_eight_eq_seven r hr
+
+/--
+A continuation sibling cell, at depth at least `1`, starts in the exact
+height-one `7 mod 8` source channel.
+-/
+theorem mod_eight_eq_seven_of_continuation_residue_of_one_le
+    (r m : ℕ) (hr : 1 ≤ r)
+    (hm : m % (2 ^ (r + 2)) = 2 ^ (r + 2) - 1) :
+    m % 8 = 7 := by
+  have hpow : 8 ∣ 2 ^ (r + 2) := by
+    rcases exists_add_of_le hr with ⟨k, rfl⟩
+    rw [show 1 + k + 2 = 3 + k by omega, pow_add]
+    norm_num
+  rw [mod_eq_mod_of_dvd_modulus hpow, hm]
+  exact continuation_residue_mod_eight_eq_seven r hr
+
 /--
 On the exact height-one channel, the accelerated Collatz map is the visible
 one-step expression `(3m + 1) / 2`.
@@ -1777,6 +1819,54 @@ theorem oddOrbitLabel_succ_mod_thirtytwo_eq_thirtyone_of_mod_sixtyfour_eq_sixtyt
   rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one (iterateT i n) hs]
   exact next_mod_thirtytwo_of_mod_sixtyfour_eq_sixtythree hmod
 
+/--
+General orbit-label transition for the recovery sibling.
+
+If the current label lies in the recovery sibling modulo `2^(r + 2)` and
+`2 <= r`, then the source is in the exact height-one `7 mod 8` channel and the
+next accelerated label lands in the outward retention residue.
+-/
+theorem oddOrbitLabel_succ_recovery_residue_of_mod
+    (r : ℕ) (hr : 2 ≤ r) (n : OddNat) (i : ℕ)
+    (hmod :
+      oddOrbitLabel n i % (2 ^ (r + 2)) = 2 ^ (r + 1) - 1) :
+    oddOrbitLabel n (i + 1) % (2 ^ (r + 1)) = 2 ^ r - 1 := by
+  have hmod8 : oddOrbitLabel n i % 8 = 7 :=
+    mod_eight_eq_seven_of_recovery_residue_of_two_le r (oddOrbitLabel n i) hr hmod
+  have hheight : orbitWindowHeight n i = 1 :=
+    (orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n i).mpr
+      (Or.inr hmod8)
+  have hs : s (iterateT i n) = 1 := by
+    simpa [orbitWindowHeight_eq_s_iterateT] using hheight
+  rw [oddOrbitLabel_succ_eq_T_iterateT]
+  rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one (iterateT i n) hs]
+  exact next_recovery_residue_of_mod r (oddOrbitLabel n i) hmod
+
+/--
+General orbit-label transition for the continuation sibling.
+
+If the current label lies in the continuation sibling modulo `2^(r + 2)` and
+`1 <= r`, then the source is in the exact height-one `7 mod 8` channel and the
+next accelerated label lands in the next retention cell.
+-/
+theorem oddOrbitLabel_succ_continuation_residue_of_mod
+    (r : ℕ) (hr : 1 ≤ r) (n : OddNat) (i : ℕ)
+    (hmod :
+      oddOrbitLabel n i % (2 ^ (r + 2)) = 2 ^ (r + 2) - 1) :
+    oddOrbitLabel n (i + 1) % (2 ^ (r + 1)) =
+      2 ^ (r + 1) - 1 := by
+  have hmod8 : oddOrbitLabel n i % 8 = 7 :=
+    mod_eight_eq_seven_of_continuation_residue_of_one_le
+      r (oddOrbitLabel n i) hr hmod
+  have hheight : orbitWindowHeight n i = 1 :=
+    (orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n i).mpr
+      (Or.inr hmod8)
+  have hs : s (iterateT i n) = 1 := by
+    simpa [orbitWindowHeight_eq_s_iterateT] using hheight
+  rw [oddOrbitLabel_succ_eq_T_iterateT]
+  rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one (iterateT i n) hs]
+  exact next_continuation_residue_of_mod r (oddOrbitLabel n i) hmod
+
 /--
 Delayed peeling from the `3 mod 8` height-one channel.
 
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index 6f62ca4c..bbbd2937 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -206,6 +206,9 @@ next_mod_twohundredfiftysix_of_mod_fivehundredtwelve_eq_twohundredfiftyfive_via_
 next_mod_twohundredfiftysix_of_mod_fivehundredtwelve_eq_fivehundredeleven_via_general
 recovery_residue_mod_eight_eq_seven
 continuation_residue_mod_eight_eq_seven
+mod_eq_mod_of_dvd_modulus
+mod_eight_eq_seven_of_recovery_residue_of_two_le
+mod_eight_eq_seven_of_continuation_residue_of_one_le
 iterateT_succ_eq_T_iterateT
 oddOrbitLabel_succ_eq_T_iterateT
 oddOrbitLabel_succ_mod_four_eq_one_of_mod_eight_eq_three
@@ -216,6 +219,8 @@ oddOrbitLabel_succ_mod_sixteen_eq_seven_of_mod_thirtytwo_eq_fifteen
 oddOrbitLabel_succ_mod_sixteen_eq_fifteen_of_mod_thirtytwo_eq_thirtyone
 oddOrbitLabel_succ_mod_thirtytwo_eq_fifteen_of_mod_sixtyfour_eq_thirtyone
 oddOrbitLabel_succ_mod_thirtytwo_eq_thirtyone_of_mod_sixtyfour_eq_sixtythree
+oddOrbitLabel_succ_recovery_residue_of_mod
+oddOrbitLabel_succ_continuation_residue_of_mod
 orbitWindowNextHeight_two_le_of_mod_eight_eq_three
 orbitWindowNextHeight_eq_one_of_mod_eight_eq_seven
 orbitWindowNextNextHeight_two_le_of_mod_sixteen_eq_seven
@@ -941,6 +946,39 @@ This is the lower-bound condition needed before promoting the practical raw
 theorem to an orbit-label theorem: the source label must be in the exact
 height-one `7 mod 8` channel so that `T` is the visible `(3m + 1) / 2` step.
 
+That promotion is now closed.  The residue-cell reduction bridge is:
+
+```text
+d | M
+  -> m % d = (m % M) % d
+```
+
+In particular, when `8 | 2^(r+2)`, the large 2-adic address determines the
+visible `mod 8` source channel:
+
+```text
+m % 2^(r+2) = 2^(r+1) - 1, 2 <= r
+  -> m % 8 = 7
+
+m % 2^(r+2) = 2^(r+2) - 1, 1 <= r
+  -> m % 8 = 7
+```
+
+Therefore the recursive two-adic Petal theorem has reached the orbit-label
+layer:
+
+```text
+oddOrbitLabel n i % 2^(r+2) = 2^(r+1) - 1, 2 <= r
+  -> oddOrbitLabel n (i+1) % 2^(r+1) = 2^r - 1
+
+oddOrbitLabel n i % 2^(r+2) = 2^(r+2) - 1, 1 <= r
+  -> oddOrbitLabel n (i+1) % 2^(r+1) = 2^(r+1) - 1
+```
+
+This is the first general orbit-level statement of the narrowing retention
+cylinder: recovery exits one level outward, while continuation becomes the next
+retention cell.
+
 At count level, the two exact-height-one source channels also have a source
 mass bound:
 
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-095.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-095.md
new file mode 100644
index 00000000..e64571e4
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-095.md
@@ -0,0 +1,282 @@
+# Report Petal 095: Orbit-Level Recursive Two-Adic Petal
+
+## Checkpoint
+
+This checkpoint follows `__next_implementation-095.md`.
+
+The target was to move from practical raw residue-cell theorems to orbit-label
+theorems.  The missing bridge was:
+
+```text
+large residue modulo 2^(r+2)
+  -> visible source residue modulo 8
+```
+
+The checkpoint closed with no new Lean `sorry`.
+
+## Implemented Lean Surface
+
+File:
+
+```text
+lean/dk_math/DkMath/Collatz/PetalBridge.lean
+```
+
+New residue reduction helper:
+
+```lean
+mod_eq_mod_of_dvd_modulus
+```
+
+New source-entry bridges:
+
+```lean
+mod_eight_eq_seven_of_recovery_residue_of_two_le
+mod_eight_eq_seven_of_continuation_residue_of_one_le
+```
+
+New orbit-label recursive transition theorems:
+
+```lean
+oddOrbitLabel_succ_recovery_residue_of_mod
+oddOrbitLabel_succ_continuation_residue_of_mod
+```
+
+## Residue Reduction Bridge
+
+The local helper is:
+
+```lean
+theorem mod_eq_mod_of_dvd_modulus
+    {a M d : ℕ} (hd : d ∣ M) :
+    a % d = (a % M) % d
+```
+
+It wraps `Nat.mod_mod_of_dvd` in the orientation used by the Collatz Petal
+bridge.
+
+Reading:
+
+```text
+if a smaller modulus d divides a larger modulus M,
+then the M-address determines the d-address
+```
+
+This is the general mechanism for projecting a deep two-adic Petal cell down
+to its visible `mod 8` entry channel.
+
+## Source Entry
+
+Recovery side:
+
+```lean
+theorem mod_eight_eq_seven_of_recovery_residue_of_two_le
+    (r m : ℕ) (hr : 2 ≤ r)
+    (hm : m % (2 ^ (r + 2)) = 2 ^ (r + 1) - 1) :
+    m % 8 = 7
+```
+
+Continuation side:
+
+```lean
+theorem mod_eight_eq_seven_of_continuation_residue_of_one_le
+    (r m : ℕ) (hr : 1 ≤ r)
+    (hm : m % (2 ^ (r + 2)) = 2 ^ (r + 2) - 1) :
+    m % 8 = 7
+```
+
+The lower bounds on `r` are not decoration.  They ensure that the source cell
+has enough two-adic depth to project to the exact height-one `7 mod 8` channel.
+
+## Orbit-Level Theorems
+
+Recovery sibling:
+
+```lean
+theorem oddOrbitLabel_succ_recovery_residue_of_mod
+    (r : ℕ) (hr : 2 ≤ r) (n : OddNat) (i : ℕ)
+    (hmod :
+      oddOrbitLabel n i % (2 ^ (r + 2)) = 2 ^ (r + 1) - 1) :
+    oddOrbitLabel n (i + 1) % (2 ^ (r + 1)) = 2 ^ r - 1
+```
+
+Continuation sibling:
+
+```lean
+theorem oddOrbitLabel_succ_continuation_residue_of_mod
+    (r : ℕ) (hr : 1 ≤ r) (n : OddNat) (i : ℕ)
+    (hmod :
+      oddOrbitLabel n i % (2 ^ (r + 2)) = 2 ^ (r + 2) - 1) :
+    oddOrbitLabel n (i + 1) % (2 ^ (r + 1)) =
+      2 ^ (r + 1) - 1
+```
+
+This is the orbit-label version of the recursive two-adic Petal:
+
+```text
+recovery sibling:
+  exits one level outward
+
+continuation sibling:
+  becomes the next retention cell
+```
+
+The previous fixed ladder up to `mod 512` is now explained by a general theorem
+at the actual accelerated orbit-label layer.
+
+## Proof Shape
+
+Each orbit theorem follows the same four-step pattern:
+
+```text
+1. use the large residue hypothesis to prove source mod 8 = 7
+2. use the exact height-one theorem for the 7 mod 8 channel
+3. rewrite oddOrbitLabel (i+1) as T (iterateT i n)
+4. rewrite T as (3m + 1) / 2 and apply the practical raw theorem
+```
+
+The important point is that the raw theorem is no longer isolated arithmetic.
+It now acts on the actual Collatz orbit label.
+
+## Documentation Sync
+
+Updated:
+
+```text
+lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+```
+
+The status note now records:
+
+```text
+residue reduction through a divisor modulus
+large residue -> mod 8 source-entry
+general orbit-label recovery transition
+general orbit-label continuation transition
+```
+
+## Factor-Layer Design Note
+
+This checkpoint also clarifies the next conceptual split.
+
+The Collatz state has at least two visible coordinate systems:
+
+```text
+TwoAdicPetalCoordinate:
+  the residue address modulo 2^r
+
+OddFactorCarrier:
+  the odd-prime factor structure of the current or next odd core
+```
+
+After one accelerated step:
+
+```text
+3m + 1 = 2^h * nextOdd
+```
+
+The two-adic coordinate controls the peeling branch:
+
+```text
+height h
+recovery sibling
+continuation sibling
+retention cell
+```
+
+The odd factor carrier controls the remaining odd core:
+
+```text
+which odd primes divide nextOdd
+which were already present in m
+which are newly introduced by the step
+```
+
+Useful future vocabulary:
+
+```text
+NewOddPrimeFactor:
+  a prime p such that p | (T n).val and not p | n.val
+
+CoordinateFactorInteraction:
+  how a two-adic Petal branch changes, or correlates with,
+  the odd-prime carrier of the next odd state
+```
+
+This should remain docs/design level for now.  The current Lean bridge has just
+stabilized the two-adic coordinate transition; the factor layer should be added
+only after the coordinate-count API is ready.
+
+## Verification
+
+Passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge
+```
+
+The build still reports the existing upstream warning:
+
+```text
+DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean: declaration uses `sorry`
+```
+
+No new `sorry` was introduced in `DkMath.Collatz.PetalBridge`.
+
+## What Was Not Done Yet
+
+The residue-cell occupation count API was not added.
+
+The natural next definition is still:
+
+```lean
+def orbitWindowResidueCountPow2
+    (n : OddNat) (k depth residue : ℕ) : ℕ :=
+  (List.range k).countP
+    (fun i => decide (oddOrbitLabel n i % (2 ^ depth) = residue))
+```
+
+This should come after the transition theorem because it can now count actual
+orbit-label addresses at arbitrary two-adic depth.
+
+## Next Implementation Candidates
+
+Candidate A: pow-two residue count.
+
+```lean
+def orbitWindowResidueCountPow2
+    (n : OddNat) (k depth residue : ℕ) : ℕ :=
+  (List.range k).countP
+    (fun i => decide (oddOrbitLabel n i % (2 ^ depth) = residue))
+```
+
+Candidate B: count bound.
+
+```lean
+theorem orbitWindowResidueCountPow2_le_window
+    (n : OddNat) (k depth residue : ℕ) :
+    orbitWindowResidueCountPow2 n k depth residue ≤ k
+```
+
+Candidate C: bridge existing named counts into the generic count.
+
+```lean
+theorem orbitWindowResidueCountMod8EqSeven_eq_pow2
+    (n : OddNat) (k : ℕ) :
+    orbitWindowResidueCountMod8EqSeven n k =
+      orbitWindowResidueCountPow2 n k 3 7
+```
+
+Candidate D: docs-only design for future factor layer.
+
+```text
+TwoAdicPetalCoordinate
+OddFactorCarrier
+NewOddPrimeFactor
+CoordinateFactorInteraction
+```
+
+The next strong technical direction is to count occupation of arbitrary
+two-adic cells, then use the new orbit-level recursive theorem to relate
+occupation at depth `r + 2` to occupation at depth `r + 1` in the next shifted
+window.
````
`````
