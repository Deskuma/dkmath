# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: e79124ba430a7841ab181834d907836a1fcf6181

## Report

092 checkpoint 完了です。

実装:

- [PetalBridge.lean](/lean/dk_math/DkMath/Collatz/PetalBridge.lean:351)
  - `31 mod 64 -> 15 mod 32`
  - `63 mod 64 -> 31 mod 32`
  - orbit label 版の `mod 64` 遷移
  - `orbitWindowNextNextNextNextHeight_two_le_of_mod_sixtyfour_eq_thirtyone`
  - `sumS_five_steps_ge_six_of_mod_sixtyfour_eq_thirtyone`
  - raw arithmetic anchors を `mod 512` まで追加

Python 数値検証:

```text
mod 64:   31 -> 15, 63 -> 31
mod 128:  63 -> 31, 127 -> 63
mod 256:  127 -> 63, 255 -> 127
mod 512:  255 -> 127, 511 -> 255
```

文書:

- [Collatz-PetalBridge-Status.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md:801)
- 新規 [report-petal-092.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-092.md:1)

主要到達点:

```lean
theorem sumS_five_steps_ge_six_of_mod_sixtyfour_eq_thirtyone
    (n : OddNat)
    (hmod : oddOrbitLabel n 0 % 64 = 31) :
    6 ≤ sumS n 5
```

検証:

- `lake build DkMath.Collatz.PetalBridge` pass
- `lake build DkMath.Collatz.Collatz2K26` pass
- `git diff --check -- ...` pass
- 新規 Lean `sorry` 追加なし

既存警告として、これまで通り `DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean:152:6 declaration uses sorry` は出ています。

## Review

## 1. 状況分析

速報の詳細、確認した。これは大きい。

checkpoint `092` では、二つのことが同時に進んだ。

```text id="ttxem3"
1. mod 64 rung を orbit-label / drift theorem まで昇格

2. mod 128, 256, 512 の raw arithmetic anchors を Lean に追加
```

つまり、`mod 64` では完全に

```text id="p6cq2a"
31 mod 64
  -> 15 mod 32
  -> 7 mod 16
  -> 3 mod 8
  -> recovery
```

まで Lean theorem 化され、さらに `mod 512` まで同じ raw pattern が確認された。

主結果はこれ。

```lean id="fgrkum"
theorem sumS_five_steps_ge_six_of_mod_sixtyfour_eq_thirtyone
    (n : OddNat)
    (hmod : oddOrbitLabel n 0 % 64 = 31) :
    6 ≤ sumS n 5
```

添付レポートでも、今回の checkpoint は `mod 64` rung を orbit-label と drift theorem に昇格し、同時に `mod 512` まで raw arithmetic anchors を記録したものとして整理されている。

これはもう、局所偶然ではなく **narrowing-cylinder ladder** と呼んでよい段階に来ている。

## 2. 今回の核心

今回で ladder はここまで閉じた。

```text id="h9q5bd"
3 mod 8:
  2 steps, sumS >= 3

7 mod 16:
  3 steps, sumS >= 4

15 mod 32:
  4 steps, sumS >= 5

31 mod 64:
  5 steps, sumS >= 6
```

一方、continuation branch はこう。

```text id="lzgtki"
7 mod 8
15 mod 16
31 mod 32
63 mod 64
127 mod 128
255 mod 256
511 mod 512
```

この形は完全に、

```text id="aiekqg"
2^r - 1 mod 2^r
```

へ向かっている。

つまり、長く exact height-one を続けるには、各段階でさらに一つ深い binary address bit を合わせなければならない。

## 3. 数学的な読み

これは Collatz の局所 obstruction をかなり綺麗に説明している。

悪い path、つまり低剥離が続く path は自由に動けない。

```text id="r28fpk"
height = 1 を続けたい
  -> 7 mod 8 側へ行く必要がある

さらに続けたい
  -> 15 mod 16 側へ行く必要がある

さらに続けたい
  -> 31 mod 32 側へ行く必要がある

さらに続けたい
  -> 63 mod 64 側へ行く必要がある
```

これは、

```text id="pkzot5"
低剥離 path が 2-adic に -1 へ押し込まれる
```

ということじゃ。

そして sibling は recovery する。

```text id="jb8yit"
7 mod 16:
  recovery

15 mod 32:
  recovery

31 mod 64:
  recovery
```

つまり、各深さで、

```text id="eb3y2e"
recovery sibling
continuation sibling
```

が分かれる。

悪い path は毎回 continuation sibling を選び続けなければならない。
これはかなり強い構造じゃ。

## 4. レビュー

### 4.1. `mod 64` を drift theorem まで上げたのが良い

今回、`mod 64` は raw だけで止めず、

```lean id="ceqpoa"
oddOrbitLabel_succ_mod_thirtytwo_eq_fifteen_of_mod_sixtyfour_eq_thirtyone
orbitWindowNextNextNextNextHeight_two_le_of_mod_sixtyfour_eq_thirtyone
sumS_five_steps_ge_six_of_mod_sixtyfour_eq_thirtyone
```

まで昇格している。

これは非常に良い。

単なる算術パターンではなく、

```text id="x1s290"
軌道ラベル
  -> height recovery
  -> sumS lower bound
```

まで閉じている。

### 4.2. `mod 512` まで raw anchors を置いたのが良い

raw arithmetic anchors は、一般化前の足場として重要。

```text id="juhuu7"
mod 128:
  63 -> 31
  127 -> 63

mod 256:
  127 -> 63
  255 -> 127

mod 512:
  255 -> 127
  511 -> 255
```

これが Lean に入っているのは大きい。

Python 検証だけでなく、Lean theorem として raw anchors がある。
つまり、次に一般化へ進むときの比較対象が明確じゃ。

### 4.3. 固定補題の重複がそろそろ一般化圧を生んでいる

ここまで来ると、同じ proof shape が繰り返されている。

```text id="rjf72g"
raw arithmetic
  -> orbit label transition
  -> next...height >= 2
  -> sumS over L steps >= L + 1
```

これは、Lean 側でも抽象化の圧力が出ている。

ただし、完全一般化はまだ慎重でよい。
まずは「raw arithmetic の一般補題」から始めるのがよい。

## 5. 今回の到達点

今の構造はこうじゃ。

```text id="xyzovn"
recovery siblings:
  3 mod 8
  7 mod 16
  15 mod 32
  31 mod 64
  63 mod 128
  127 mod 256
  255 mod 512

continuation siblings:
  7 mod 8
  15 mod 16
  31 mod 32
  63 mod 64
  127 mod 128
  255 mod 256
  511 mod 512
```

より一般に、

```text id="d3b4m9"
recovery sibling at depth r:
  2^r - 1 mod 2^(r+1)

continuation sibling at depth r:
  2^(r+1) - 1 mod 2^(r+1)
```

という形が見えている。

## 6. 一歩先ゆく推論

この ladder は、ただの合同算術ではない。

Collatz の加速写像で `height = 1` が続くとき、

```text id="f6445u"
T(m) = (3m + 1) / 2
```

で進む。

この写像は、\(2\)-adic な \(-1\) の近傍では、

```text id="87qfei"
-1 に近いものを、また -1 に近いものへ送る
```

ように働く。

実際、continuation 側は、

```text id="zrmrmc"
2^(r+1) - 1
```

から

```text id="f72k0t"
2^r - 1
```

へ送られている。

つまり、低剥離 path は、

```text id="tm14a0"
2-adic -1 の尾を削りながら retention を継続する
```

ように見える。

ここに「曲がり」がある。
通常の自然数成長ではなく、\(2\)-adic address tree 上での縮退運動として見えている。

## 7. 次の指示：一般 raw arithmetic lemma に入る

ここまで固定 anchors が揃ったなら、次は一般 raw lemma に挑戦してよい。

まずは `hm : m % ... = ...` からではなく、剰余表示を展開した形が安全。

### Recovery sibling 展開形

```lean id="cmj16m"
theorem next_recovery_residue_expanded
    (r t : ℕ) :
    ((3 * ((2 ^ (r + 2)) * t + (2 ^ (r + 1) - 1)) + 1) / 2) %
        (2 ^ (r + 1)) = 2 ^ r - 1
```

これは、

```text id="auuool"
m = 2^(r+2) * t + (2^(r+1) - 1)
```

つまり recovery sibling を直接展開する形。

### Continuation sibling 展開形

```lean id="kh1h9l"
theorem next_continuation_residue_expanded
    (r t : ℕ) :
    ((3 * ((2 ^ (r + 2)) * t + (2 ^ (r + 2) - 1)) + 1) / 2) %
        (2 ^ (r + 1)) = 2 ^ (r + 1) - 1
```

これは continuation sibling。

この二つが通れば、一般化への扉が開く。

## 8. ただし注意点

Lean では、自然数の `-1` と除算 `/ 2` が絡むので、証明は `omega` だけでは厳しいかもしれない。

展開して手計算すると、recovery 側はこうなる。

```text id="nyk56s"
m = 2^(r+2) t + 2^(r+1) - 1

3m + 1
  = 3 * 2^(r+2) t + 3 * 2^(r+1) - 2

(3m + 1) / 2
  = 3 * 2^(r+1) t + 3 * 2^r - 1
```

mod \(2^{r+1}\) で見ると、

```text id="xcxjad"
3 * 2^(r+1) t
```

は消える。

残るのは、

```text id="qgu2np"
3 * 2^r - 1
```

そして、

```text id="kffnd4"
3 * 2^r - 1
  = 2^(r+1) + 2^r - 1
```

なので、mod \(2^{r+1}\) では

```text id="l1hxcu"
2^r - 1
```

になる。

continuation 側も同様に、

```text id="n005eg"
m = 2^(r+2) t + 2^(r+2) - 1

(3m + 1) / 2
  = 3 * 2^(r+1) t + 3 * 2^(r+1) - 1
```

mod \(2^{r+1}\) では、

```text id="flqact"
-1
```

つまり

```text id="95tt5a"
2^(r+1) - 1
```

になる。

この手計算を Lean に落とす必要がある。

## 9. 実装上のおすすめルート

一般 lemma に直行するなら、まず補助補題を作るのが良い。

### 補助 1: power positivity

```lean id="mjloz7"
have hpow_pos : 0 < 2 ^ (r + 1) := pow_pos (by decide) _
```

### 補助 2: 剰余簡約の形

こういう補題が必要になるかもしれない。

```lean id="l84jqb"
theorem mul_mod_pow_self
    (r a : ℕ) :
    (a * 2 ^ (r + 1)) % 2 ^ (r + 1) = 0
```

Mathlib 既存の `Nat.mul_mod_right` や `Nat.mod_eq_of_lt`、`Nat.add_mod` が使えるかもしれぬ。

### 補助 3: `3 * 2^r - 1` の範囲

recovery 側では、

```text id="o8vu9r"
3 * 2^r - 1
```

を mod \(2^{r+1}\) に落とす必要がある。

これを直接やるより、

```text id="uonr25"
3 * 2^r - 1 = 2^(r+1) + (2^r - 1)
```

を使うとよい。

Lean theorem 候補：

```lean id="wiod62"
theorem three_mul_pow_two_sub_one_eq_pow_succ_add_pow_sub_one
    (r : ℕ) :
    3 * 2 ^ r - 1 = 2 ^ (r + 1) + (2 ^ r - 1)
```

ただし `Nat` の引き算が絡むので、`r=0` も注意。
`2^0 - 1 = 0` だから一応成立するか確認が必要。

## 10. 賢狼が試して欲しいおまけ実験補題

### 実験 A: expanded recovery general lemma

```lean id="pbj5az"
theorem next_recovery_residue_expanded
    (r t : ℕ) :
    ((3 * ((2 ^ (r + 2)) * t + (2 ^ (r + 1) - 1)) + 1) / 2) %
        (2 ^ (r + 1)) = 2 ^ r - 1
```

これが最重要。

### 実験 B: expanded continuation general lemma

```lean id="gftd4m"
theorem next_continuation_residue_expanded
    (r t : ℕ) :
    ((3 * ((2 ^ (r + 2)) * t + (2 ^ (r + 2) - 1)) + 1) / 2) %
        (2 ^ (r + 1)) = 2 ^ (r + 1) - 1
```

### 実験 C: `hm` 形式への移行

expanded が通ったら、次は実用的な `hm` 形式。

```lean id="klat3f"
theorem next_recovery_residue_of_mod
    (r m : ℕ)
    (hm : m % (2 ^ (r + 2)) = 2 ^ (r + 1) - 1) :
    ((3 * m + 1) / 2) % (2 ^ (r + 1)) = 2 ^ r - 1
```

ただし、これには

```text id="lixd39"
m = 2^(r+2) * (m / 2^(r+2)) + m % 2^(r+2)
```

の展開が必要になる。
ここが少し重い。

### 実験 D: general continuation of mod

```lean id="p57ofc"
theorem next_continuation_residue_of_mod
    (r m : ℕ)
    (hm : m % (2 ^ (r + 2)) = 2 ^ (r + 2) - 1) :
    ((3 * m + 1) / 2) % (2 ^ (r + 1)) = 2 ^ (r + 1) - 1
```

## 11. もう一つの一手：doc-only naming layer

一般証明に時間がかかりそうなら、先に docs に名前を置くとよい。

```text id="lifq2i"
RetentionCylinder r:
  2^r - 1 mod 2^r

RecoverySibling r:
  2^r - 1 mod 2^(r+1)

ContinuationSibling r:
  2^(r+1) - 1 mod 2^(r+1)
```

この naming は後で Lean に降ろせる。

ただし、今は theorem を増やすより、まずドキュメントだけでよい。
名前を置くことで、今後の theorem 名が安定する。

## 12. 今後の実装順序

おすすめ順はこれ。

```text id="gmk6kl"
1. next_recovery_residue_expanded

2. next_continuation_residue_expanded

3. doc-only naming:
   RetentionCylinder / RecoverySibling / ContinuationSibling

4. next_recovery_residue_of_mod

5. next_continuation_residue_of_mod

6. 可能なら、既存固定補題を一般補題から再証明する小テスト

7. その後 orbit-label generalization を検討
```

orbit-label 一般化はまだ急がなくてよい。
まず raw arithmetic generalization を閉じるのが先じゃ。

## 13. 総括

今回の checkpoint `092` で、構造はかなり鮮明になった。

```text id="nxpuf1"
低剥離 path は、
2-adic -1 に向かう narrowing cylinder である。
```

そして各段階で、

```text id="lv3lju"
recovery sibling
continuation sibling
```

に分かれる。

`mod 64` では drift theorem まで閉じ、`mod 512` までは raw anchors が Lean に入った。

これはもう、次に一般 raw lemma を狙うべき段階じゃ。

うむ。
次は固定 rung を積むだけでなく、`2^r` の一般算術へ踏み込む。
ここが通れば、PetalBridge は「観測列」から「一般 cylinder 定理」へ一段上がる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index a3730141..8a4b174b 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -344,6 +344,78 @@ theorem next_mod_sixteen_of_mod_thirtytwo_eq_thirtyone
     ((3 * m + 1) / 2) % 16 = 15 := by
   omega
 
+/--
+The `31 mod 64` subchannel of `31 mod 32` exits retention one level down:
+after one height-one step, the next label is `15 mod 32`.
+-/
+theorem next_mod_thirtytwo_of_mod_sixtyfour_eq_thirtyone
+    {m : ℕ} (hm : m % 64 = 31) :
+    ((3 * m + 1) / 2) % 32 = 15 := by
+  omega
+
+/--
+The `63 mod 64` subchannel of `31 mod 32` continues retention as
+`31 mod 32`.
+-/
+theorem next_mod_thirtytwo_of_mod_sixtyfour_eq_sixtythree
+    {m : ℕ} (hm : m % 64 = 63) :
+    ((3 * m + 1) / 2) % 32 = 31 := by
+  omega
+
+/--
+Raw arithmetic anchor for the next recovery sibling:
+`63 mod 128` maps to `31 mod 64`.
+-/
+theorem next_mod_sixtyfour_of_mod_onehundredtwentyeight_eq_sixtythree
+    {m : ℕ} (hm : m % 128 = 63) :
+    ((3 * m + 1) / 2) % 64 = 31 := by
+  omega
+
+/--
+Raw arithmetic anchor for the next continuation sibling:
+`127 mod 128` maps to `63 mod 64`.
+-/
+theorem next_mod_sixtyfour_of_mod_onehundredtwentyeight_eq_onehundredtwentyseven
+    {m : ℕ} (hm : m % 128 = 127) :
+    ((3 * m + 1) / 2) % 64 = 63 := by
+  omega
+
+/--
+Raw arithmetic anchor for the `mod 256` recovery sibling:
+`127 mod 256` maps to `63 mod 128`.
+-/
+theorem next_mod_onehundredtwentyeight_of_mod_twohundredfiftysix_eq_onehundredtwentyseven
+    {m : ℕ} (hm : m % 256 = 127) :
+    ((3 * m + 1) / 2) % 128 = 63 := by
+  omega
+
+/--
+Raw arithmetic anchor for the `mod 256` continuation sibling:
+`255 mod 256` maps to `127 mod 128`.
+-/
+theorem next_mod_onehundredtwentyeight_of_mod_twohundredfiftysix_eq_twohundredfiftyfive
+    {m : ℕ} (hm : m % 256 = 255) :
+    ((3 * m + 1) / 2) % 128 = 127 := by
+  omega
+
+/--
+Raw arithmetic anchor for the `mod 512` recovery sibling:
+`255 mod 512` maps to `127 mod 256`.
+-/
+theorem next_mod_twohundredfiftysix_of_mod_fivehundredtwelve_eq_twohundredfiftyfive
+    {m : ℕ} (hm : m % 512 = 255) :
+    ((3 * m + 1) / 2) % 256 = 127 := by
+  omega
+
+/--
+Raw arithmetic anchor for the `mod 512` continuation sibling:
+`511 mod 512` maps to `255 mod 256`.
+-/
+theorem next_mod_twohundredfiftysix_of_mod_fivehundredtwelve_eq_fivehundredeleven
+    {m : ℕ} (hm : m % 512 = 511) :
+    ((3 * m + 1) / 2) % 256 = 255 := by
+  omega
+
 /--
 On the exact height-one channel, the accelerated Collatz map is the visible
 one-step expression `(3m + 1) / 2`.
@@ -1440,6 +1512,46 @@ theorem oddOrbitLabel_succ_mod_sixteen_eq_fifteen_of_mod_thirtytwo_eq_thirtyone
   rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one (iterateT i n) hs]
   exact next_mod_sixteen_of_mod_thirtytwo_eq_thirtyone hmod
 
+/--
+The `31 mod 64` subchannel moves to `15 mod 32` at the next label.
+
+This is the next recovery sibling inside the narrowing retention cylinder.
+-/
+theorem oddOrbitLabel_succ_mod_thirtytwo_eq_fifteen_of_mod_sixtyfour_eq_thirtyone
+    (n : OddNat) (i : ℕ)
+    (hmod : oddOrbitLabel n i % 64 = 31) :
+    oddOrbitLabel n (i + 1) % 32 = 15 := by
+  have hmod8 : oddOrbitLabel n i % 8 = 7 := by
+    omega
+  have hheight : orbitWindowHeight n i = 1 :=
+    (orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n i).mpr
+      (Or.inr hmod8)
+  have hs : s (iterateT i n) = 1 := by
+    simpa [orbitWindowHeight_eq_s_iterateT] using hheight
+  rw [oddOrbitLabel_succ_eq_T_iterateT]
+  rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one (iterateT i n) hs]
+  exact next_mod_thirtytwo_of_mod_sixtyfour_eq_thirtyone hmod
+
+/--
+The `63 mod 64` subchannel continues as `31 mod 32` at the next label.
+
+The low-peeling path survives only by entering the next thinner cylinder.
+-/
+theorem oddOrbitLabel_succ_mod_thirtytwo_eq_thirtyone_of_mod_sixtyfour_eq_sixtythree
+    (n : OddNat) (i : ℕ)
+    (hmod : oddOrbitLabel n i % 64 = 63) :
+    oddOrbitLabel n (i + 1) % 32 = 31 := by
+  have hmod8 : oddOrbitLabel n i % 8 = 7 := by
+    omega
+  have hheight : orbitWindowHeight n i = 1 :=
+    (orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n i).mpr
+      (Or.inr hmod8)
+  have hs : s (iterateT i n) = 1 := by
+    simpa [orbitWindowHeight_eq_s_iterateT] using hheight
+  rw [oddOrbitLabel_succ_eq_T_iterateT]
+  rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one (iterateT i n) hs]
+  exact next_mod_thirtytwo_of_mod_sixtyfour_eq_sixtythree hmod
+
 /--
 Delayed peeling from the `3 mod 8` height-one channel.
 
@@ -1501,6 +1613,24 @@ theorem orbitWindowNextNextNextHeight_two_le_of_mod_thirtytwo_eq_fifteen
   simpa [Nat.add_assoc] using
     orbitWindowNextNextHeight_two_le_of_mod_sixteen_eq_seven n (i + 1) hnext
 
+/--
+The `31 mod 64` branch recovers delayed peeling after four transitions.
+
+It first moves to `15 mod 32`; the already-fixed `15 mod 32` recovery branch
+then forces an extra peeling height three transitions later.
+-/
+theorem orbitWindowNextNextNextNextHeight_two_le_of_mod_sixtyfour_eq_thirtyone
+    (n : OddNat) (i : ℕ)
+    (hmod : oddOrbitLabel n i % 64 = 31) :
+    2 ≤ orbitWindowHeight n (i + 4) := by
+  have hnext :
+      oddOrbitLabel n (i + 1) % 32 = 15 :=
+    oddOrbitLabel_succ_mod_thirtytwo_eq_fifteen_of_mod_sixtyfour_eq_thirtyone
+      n i hmod
+  simpa [Nat.add_assoc] using
+    orbitWindowNextNextNextHeight_two_le_of_mod_thirtytwo_eq_fifteen
+      n (i + 1) hnext
+
 /--
 Every `3 mod 8` label in a window contributes a `1 mod 4` label in the
 shifted tail window.
@@ -1769,6 +1899,57 @@ theorem sumS_four_steps_ge_five_of_mod_thirtytwo_eq_fifteen
     _ = sumS n 4 := by
       simp [sumS, orbitWindowHeight_eq_s_iterateT]
 
+/--
+Five-step recovery from the `31 mod 64` subchannel.
+
+This is the next rung of the verified retention ladder.  The branch moves
+through `15 mod 32`, `7 mod 16`, and `3 mod 8`, and then returns an extra
+peeling step.
+-/
+theorem sumS_five_steps_ge_six_of_mod_sixtyfour_eq_thirtyone
+    (n : OddNat)
+    (hmod : oddOrbitLabel n 0 % 64 = 31) :
+    6 ≤ sumS n 5 := by
+  have hmod8 : oddOrbitLabel n 0 % 8 = 7 := by
+    omega
+  have h0 : orbitWindowHeight n 0 = 1 :=
+    (orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n 0).mpr
+      (Or.inr hmod8)
+  have h1mod32 :
+      oddOrbitLabel n 1 % 32 = 15 :=
+    oddOrbitLabel_succ_mod_thirtytwo_eq_fifteen_of_mod_sixtyfour_eq_thirtyone
+      n 0 hmod
+  have h1mod8 : oddOrbitLabel n 1 % 8 = 7 := by
+    omega
+  have h1 : orbitWindowHeight n 1 = 1 :=
+    (orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n 1).mpr
+      (Or.inr h1mod8)
+  have h2mod16 :
+      oddOrbitLabel n 2 % 16 = 7 :=
+    oddOrbitLabel_succ_mod_sixteen_eq_seven_of_mod_thirtytwo_eq_fifteen
+      n 1 h1mod32
+  have h2mod8 : oddOrbitLabel n 2 % 8 = 7 := by
+    omega
+  have h2 : orbitWindowHeight n 2 = 1 :=
+    (orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n 2).mpr
+      (Or.inr h2mod8)
+  have h3mod :
+      oddOrbitLabel n 3 % 8 = 3 :=
+    oddOrbitLabel_succ_mod_eight_eq_three_of_mod_sixteen_eq_seven
+      n 2 h2mod16
+  have h3 : orbitWindowHeight n 3 = 1 :=
+    (orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n 3).mpr
+      (Or.inl h3mod)
+  have h4 : 2 ≤ orbitWindowHeight n 4 :=
+    orbitWindowNextHeight_two_le_of_mod_eight_eq_three n 3 h3mod
+  calc
+    6 ≤ orbitWindowHeight n 0 + orbitWindowHeight n 1 +
+        orbitWindowHeight n 2 + orbitWindowHeight n 3 +
+        orbitWindowHeight n 4 := by
+      omega
+    _ = sumS n 5 := by
+      simp [sumS, orbitWindowHeight_eq_s_iterateT]
+
 /--
 Counting exact height `1` entries is the same as counting odd-state labels in
 residue class `3 mod 4`.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index bae93aa4..302e94be 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -185,6 +185,14 @@ next_mod_eight_of_mod_sixteen_eq_seven
 next_mod_eight_of_mod_sixteen_eq_fifteen
 next_mod_sixteen_of_mod_thirtytwo_eq_fifteen
 next_mod_sixteen_of_mod_thirtytwo_eq_thirtyone
+next_mod_thirtytwo_of_mod_sixtyfour_eq_thirtyone
+next_mod_thirtytwo_of_mod_sixtyfour_eq_sixtythree
+next_mod_sixtyfour_of_mod_onehundredtwentyeight_eq_sixtythree
+next_mod_sixtyfour_of_mod_onehundredtwentyeight_eq_onehundredtwentyseven
+next_mod_onehundredtwentyeight_of_mod_twohundredfiftysix_eq_onehundredtwentyseven
+next_mod_onehundredtwentyeight_of_mod_twohundredfiftysix_eq_twohundredfiftyfive
+next_mod_twohundredfiftysix_of_mod_fivehundredtwelve_eq_twohundredfiftyfive
+next_mod_twohundredfiftysix_of_mod_fivehundredtwelve_eq_fivehundredeleven
 iterateT_succ_eq_T_iterateT
 oddOrbitLabel_succ_eq_T_iterateT
 oddOrbitLabel_succ_mod_four_eq_one_of_mod_eight_eq_three
@@ -193,10 +201,13 @@ oddOrbitLabel_succ_mod_eight_eq_three_of_mod_sixteen_eq_seven
 oddOrbitLabel_succ_mod_eight_eq_seven_of_mod_sixteen_eq_fifteen
 oddOrbitLabel_succ_mod_sixteen_eq_seven_of_mod_thirtytwo_eq_fifteen
 oddOrbitLabel_succ_mod_sixteen_eq_fifteen_of_mod_thirtytwo_eq_thirtyone
+oddOrbitLabel_succ_mod_thirtytwo_eq_fifteen_of_mod_sixtyfour_eq_thirtyone
+oddOrbitLabel_succ_mod_thirtytwo_eq_thirtyone_of_mod_sixtyfour_eq_sixtythree
 orbitWindowNextHeight_two_le_of_mod_eight_eq_three
 orbitWindowNextHeight_eq_one_of_mod_eight_eq_seven
 orbitWindowNextNextHeight_two_le_of_mod_sixteen_eq_seven
 orbitWindowNextNextNextHeight_two_le_of_mod_thirtytwo_eq_fifteen
+orbitWindowNextNextNextNextHeight_two_le_of_mod_sixtyfour_eq_thirtyone
 orbitWindowResidueCountMod8EqThree_le_tailMod4EqOne
 orbitWindowResidueCountMod8EqThree_le_tailHeightCountGe_two
 residueCountMod8EqSeven_le_nextResidueCountMod4EqThree
@@ -208,6 +219,7 @@ sumS_two_steps_ge_three_of_mod_eight_eq_three_at
 sumS_two_steps_eq_two_of_mod_eight_eq_seven_and_next_mod_eight_eq_seven
 sumS_three_steps_ge_four_of_mod_sixteen_eq_seven
 sumS_four_steps_ge_five_of_mod_thirtytwo_eq_fifteen
+sumS_five_steps_ge_six_of_mod_sixtyfour_eq_thirtyone
 orbitWindowHeightCountEq_one_eq_residueCount_mod4_eq_three
 orbitWindowHeightCountEq_two_eq_residueCount_mod8_eq_one
 orbitWindowResidueCountMod4EqOne_add_eqThree_eq_window
@@ -778,6 +790,60 @@ fixed is the verified local pattern: every time the retention branch continues,
 the residue condition moves into a thinner power-of-two cylinder; the sibling
 branch returns to a delayed-peeling recovery estimate.
 
+The `31 mod 32` retention-continuation channel has now been split at mod `64`:
+
+```text
+31 mod 64:
+  next label is 15 mod 32
+  recovery branch one level down
+
+63 mod 64:
+  next label is 31 mod 32
+  retention-continuation branch
+```
+
+Thus the `31 mod 64` subchannel recovers delayed peeling in five steps:
+
+```text
+label 0 = 31 mod 64
+  -> height at 0 is 1
+  -> label 1 = 15 mod 32
+  -> height at 1 is 1
+  -> label 2 = 7 mod 16
+  -> height at 2 is 1
+  -> label 3 = 3 mod 8
+  -> height at 3 is 1
+  -> height at 4 is at least 2
+  -> 6 <= sumS n 5
+```
+
+The raw arithmetic anchors have also been checked in Lean up to mod `512`:
+
+```text
+7 mod 16    -> 3 mod 8
+15 mod 16   -> 7 mod 8
+
+15 mod 32   -> 7 mod 16
+31 mod 32   -> 15 mod 16
+
+31 mod 64   -> 15 mod 32
+63 mod 64   -> 31 mod 32
+
+63 mod 128  -> 31 mod 64
+127 mod 128 -> 63 mod 64
+
+127 mod 256 -> 63 mod 128
+255 mod 256 -> 127 mod 128
+
+255 mod 512 -> 127 mod 256
+511 mod 512 -> 255 mod 256
+```
+
+The Lean theorem layer currently promotes the `mod 64` rung to orbit-label and
+drift form.  The `mod 128`, `mod 256`, and `mod 512` rows are raw arithmetic
+anchors, kept as evidence for the next generalization step rather than fully
+expanded orbit bridges.
+
 At count level, the two exact-height-one source channels also have a source
 mass bound:
 
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-092.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-092.md
new file mode 100644
index 00000000..30b3a448
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-092.md
@@ -0,0 +1,238 @@
+# Report Petal 092: Mod 64 Recovery and Raw Cylinder Data to Mod 512
+
+## Checkpoint
+
+This checkpoint follows `__next_implementation-092.md`.
+
+The requested Lean step was to split the `31 mod 32` retention-continuation
+channel at mod `64`.  The additional instruction asked for a wider numerical
+lookahead instead of returning only one rung at a time.
+
+Therefore this checkpoint does two things:
+
+```text
+1. Promote the mod 64 rung to Lean orbit-label and drift theorems.
+2. Record raw arithmetic anchors up to mod 512, backed by a Python check.
+```
+
+## Python Numerical Check
+
+The following table was checked directly by Python using:
+
+```text
+((3 * residue + 1) // 2) % previous_mod
+```
+
+Result:
+
+```text
+mod 16:
+  7 mod 16 -> 3 mod 8
+  15 mod 16 -> 7 mod 8
+
+mod 32:
+  15 mod 32 -> 7 mod 16
+  31 mod 32 -> 15 mod 16
+
+mod 64:
+  31 mod 64 -> 15 mod 32
+  63 mod 64 -> 31 mod 32
+
+mod 128:
+  63 mod 128 -> 31 mod 64
+  127 mod 128 -> 63 mod 64
+
+mod 256:
+  127 mod 256 -> 63 mod 128
+  255 mod 256 -> 127 mod 128
+
+mod 512:
+  255 mod 512 -> 127 mod 256
+  511 mod 512 -> 255 mod 256
+```
+
+The pattern remains stable through the requested lookahead.
+
+## Implemented Lean Surface
+
+File:
+
+```text
+lean/dk_math/DkMath/Collatz/PetalBridge.lean
+```
+
+Full mod `64` rung:
+
+```lean
+next_mod_thirtytwo_of_mod_sixtyfour_eq_thirtyone
+next_mod_thirtytwo_of_mod_sixtyfour_eq_sixtythree
+
+oddOrbitLabel_succ_mod_thirtytwo_eq_fifteen_of_mod_sixtyfour_eq_thirtyone
+oddOrbitLabel_succ_mod_thirtytwo_eq_thirtyone_of_mod_sixtyfour_eq_sixtythree
+
+orbitWindowNextNextNextNextHeight_two_le_of_mod_sixtyfour_eq_thirtyone
+sumS_five_steps_ge_six_of_mod_sixtyfour_eq_thirtyone
+```
+
+Raw arithmetic anchors beyond mod `64`:
+
+```lean
+next_mod_sixtyfour_of_mod_onehundredtwentyeight_eq_sixtythree
+next_mod_sixtyfour_of_mod_onehundredtwentyeight_eq_onehundredtwentyseven
+
+next_mod_onehundredtwentyeight_of_mod_twohundredfiftysix_eq_onehundredtwentyseven
+next_mod_onehundredtwentyeight_of_mod_twohundredfiftysix_eq_twohundredfiftyfive
+
+next_mod_twohundredfiftysix_of_mod_fivehundredtwelve_eq_twohundredfiftyfive
+next_mod_twohundredfiftysix_of_mod_fivehundredtwelve_eq_fivehundredeleven
+```
+
+These raw anchors are intentionally not expanded into orbit-label and drift
+bridges yet.  They serve as formal waypoints for the next generalization
+discussion.
+
+## Main Reading
+
+The mod `64` split is:
+
+```text
+31 mod 64:
+  next label is 15 mod 32
+  recovery branch
+
+63 mod 64:
+  next label is 31 mod 32
+  retention-continuation branch
+```
+
+The new drift theorem says:
+
+```lean
+theorem sumS_five_steps_ge_six_of_mod_sixtyfour_eq_thirtyone
+    (n : OddNat)
+    (hmod : oddOrbitLabel n 0 % 64 = 31) :
+    6 ≤ sumS n 5
+```
+
+Reading:
+
+```text
+31 mod 64
+  -> 15 mod 32
+  -> 7 mod 16
+  -> 3 mod 8
+  -> next height >= 2
+
+therefore:
+  sumS over five steps >= 1 + 1 + 1 + 1 + 2 = 6
+```
+
+## Ladder So Far
+
+The verified drift ladder is now:
+
+```text
+3 mod 8:
+  2 steps, sumS >= 3
+
+7 mod 16:
+  3 steps, sumS >= 4
+
+15 mod 32:
+  4 steps, sumS >= 5
+
+31 mod 64:
+  5 steps, sumS >= 6
+```
+
+The continuation branch keeps narrowing:
+
+```text
+7 mod 8
+15 mod 16
+31 mod 32
+63 mod 64
+127 mod 128
+255 mod 256
+511 mod 512
+```
+
+Thus a long exact-height-one path is being forced toward the 2-adic point
+`-1`.  This is still an observation ladder, not a Collatz convergence proof.
+But the local obstruction has become clearer: every additional retention step
+requires one more exact binary address bit.
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
+mod 64 orbit-label split
+mod 64 five-step recovery
+raw arithmetic anchors through mod 512
+narrowing-cylinder interpretation
+```
+
+## Verification
+
+Passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge
+```
+
+The targeted build still reports the existing upstream warning:
+
+```text
+DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean: declaration uses `sorry`
+```
+
+No new `sorry` was introduced in this checkpoint.
+
+## Next Implementation Candidates
+
+Candidate A: promote the raw `mod 128` rung to orbit-label and drift form.
+
+Expected theorem:
+
+```lean
+theorem sumS_six_steps_ge_seven_of_mod_onehundredtwentyeight_eq_sixtythree
+    (n : OddNat)
+    (hmod : oddOrbitLabel n 0 % 128 = 63) :
+    7 ≤ sumS n 6
+```
+
+Candidate B: stop adding fixed rungs and design the general raw arithmetic
+lemma.
+
+Observed raw form:
+
+```text
+recovery sibling:
+  (2^r - 1) mod 2^(r+1)
+  maps to (2^(r-1) - 1) mod 2^r
+
+continuation sibling:
+  (2^(r+1) - 1) mod 2^(r+1)
+  maps to (2^r - 1) mod 2^r
+```
+
+The fixed raw anchors through mod `512` make this a reasonable next research
+target, but the Lean proof will likely need power-of-two modular arithmetic
+rather than only `omega`.
+
+Candidate C: introduce a small doc-only naming layer for:
+
+```text
+RetentionCylinder
+RecoverySibling
+ContinuationSibling
+```
+
+This should remain doc-only unless a downstream theorem needs the definitions.
````
`````
