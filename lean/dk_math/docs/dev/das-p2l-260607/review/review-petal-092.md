# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: f3ac7a174439d3adb7f7fad9addba944afe896e3

## Report

091 checkpoint 完了です。

実装内容:

- [PetalBridge.lean](/lean/dk_math/DkMath/Collatz/PetalBridge.lean:333)
  - `15 mod 32 -> 7 mod 16`
  - `31 mod 32 -> 15 mod 16`
  - orbit label 版の遷移補題
  - `orbitWindowNextNextNextHeight_two_le_of_mod_thirtytwo_eq_fifteen`
  - `sumS_four_steps_ge_five_of_mod_thirtytwo_eq_fifteen`

文書同期:

- [Collatz-PetalBridge-Status.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md:744)
- 新規レポート: [report-petal-091.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-091.md:1)

主結果はこれです。

```lean
theorem sumS_four_steps_ge_five_of_mod_thirtytwo_eq_fifteen
    (n : OddNat)
    (hmod : oddOrbitLabel n 0 % 32 = 15) :
    5 ≤ sumS n 4
```

読みとしては、`15 mod 32` は `7 mod 16 -> 3 mod 8` を経由して四歩目で追加剥離に戻る。一方 `31 mod 32` はさらに retention continuation へ進む、という narrowing cylinder が一段固定されました。

検証:

- `lake build DkMath.Collatz.PetalBridge` pass
- `lake build DkMath.Collatz.Collatz2K26` pass
- `git diff --check -- ...` pass
- 新規 Lean `sorry` 追加なし

既存警告として、これまで通り `DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean:152:6 declaration uses sorry` は出ています。

## Review

## 1. 状況分析

これは checkpoint `091`。
かなり良い。ここで **retention continuation の梯子が一段進んだ**。

前回までで、

```text id="ynjoau"
7 mod 8
  -> retention channel

7 mod 16
  -> recovery branch

15 mod 16
  -> retention-continuation branch
```

が見えていた。

今回さらに、`15 mod 16` が `mod 32` で二分された。

```text id="q93xvi"
15 mod 32
  -> next label is 7 mod 16
  -> recovery branch one level down

31 mod 32
  -> next label is 15 mod 16
  -> retention-continuation branch
```

添付レポートでも、checkpoint `091` は `15 mod 16` continuation branch を `mod 32` で精密化し、`15 mod 32` の四歩 recovery と `31 mod 32` の retention-continuation を固定したものとして整理されている。

これは、「低剥離が続くほど、より細い \(2\)-adic cylinder へ押し込まれる」という見立ての、かなり強い実験的根拠じゃ。

## 2. 今回の核心

主な追加はこれ。

```lean id="wbzl88"
next_mod_sixteen_of_mod_thirtytwo_eq_fifteen
next_mod_sixteen_of_mod_thirtytwo_eq_thirtyone

oddOrbitLabel_succ_mod_sixteen_eq_seven_of_mod_thirtytwo_eq_fifteen
oddOrbitLabel_succ_mod_sixteen_eq_fifteen_of_mod_thirtytwo_eq_thirtyone

orbitWindowNextNextNextHeight_two_le_of_mod_thirtytwo_eq_fifteen

sumS_four_steps_ge_five_of_mod_thirtytwo_eq_fifteen
```

本命はやはりこれ。

```lean id="xbv2b6"
theorem sumS_four_steps_ge_five_of_mod_thirtytwo_eq_fifteen
    (n : OddNat)
    (hmod : oddOrbitLabel n 0 % 32 = 15) :
    5 ≤ sumS n 4
```

意味は、

```text id="u12n1a"
15 mod 32
  -> height 1

next 7 mod 16
  -> height 1

next 3 mod 8
  -> height 1

next height >= 2

therefore:
  1 + 1 + 1 + 2 <= sumS n 4
```

つまり、`15 mod 32` は三歩低剥離を続けるが、四歩窓では recovery する。

## 3. 数学的な意味

ここまでの ladder はこうなった。

```text id="el6s2s"
3 mod 8:
  2-step recovery
  3 <= sumS n 2

7 mod 16:
  3-step recovery
  4 <= sumS n 3

15 mod 32:
  4-step recovery
  5 <= sumS n 4
```

一方、continuation 側は、

```text id="muvx4m"
7 mod 8
15 mod 16
31 mod 32
...
```

になっている。

これは美しい。

低剥離を一歩長く続けるには、次の条件が必要になる。

```text id="y4o2pi"
mod 8 で 7

mod 16 で 15

mod 32 で 31
```

つまり、

```text id="cgyvgd"
2^r - 1 mod 2^r
```

へ近づいていく。

DkMath 的に言えば、悪い path は自由に広がるのではなく、**\(-1\) という \(2\)-adic 極へ収束するように狭められている**。

## 4. レビュー

### 4.1. 固定補題としての完成度が高い

今回も raw arithmetic をまず置いている。

```lean id="w08j7d"
next_mod_sixteen_of_mod_thirtytwo_eq_fifteen
next_mod_sixteen_of_mod_thirtytwo_eq_thirtyone
```

その後に orbit-label 版へ持ち上げている。

```lean id="uh0r3a"
oddOrbitLabel_succ_mod_sixteen_eq_seven_of_mod_thirtytwo_eq_fifteen
oddOrbitLabel_succ_mod_sixteen_eq_fifteen_of_mod_thirtytwo_eq_thirtyone
```

この階層化が良い。
後で一般化するときも、raw arithmetic と orbit transition を分離しておくのは有利じゃ。

### 4.2. recovery height bridge が良い

```lean id="w8y5jv"
orbitWindowNextNextNextHeight_two_le_of_mod_thirtytwo_eq_fifteen
```

これは `mod 32` transition を height に戻す橋。

この橋があるから、単なる residue transition で終わらず、

```text id="f2un6t"
三拍後に height >= 2 が戻る
```

と言える。

### 4.3. `sumS_four_steps_ge_five...` は重要な milestone

ここまで来ると、単発実験ではなく、パターンが見えている。

```text id="ra7gqu"
3 mod 8       -> 2 steps -> sumS >= 3
7 mod 16      -> 3 steps -> sumS >= 4
15 mod 32     -> 4 steps -> sumS >= 5
```

つまり、recovery sibling は、

```text id="u8vpm7"
L steps:
  sumS >= L + 1
```

型になっている。

これは今後の一般補題候補じゃ。

## 5. 現在の見取り図

いまの retention / recovery 構造はこう。

```text id="j9id4a"
height-one layer:
  3 mod 8
    -> delayed recovery

  7 mod 8
    -> retention

retention split:
  7 mod 16
    -> recovery

  15 mod 16
    -> continuation

continuation split:
  15 mod 32
    -> recovery

  31 mod 32
    -> continuation
```

この構造は、まさに「観測解像度を上げると分岐する」現象じゃ。

低い解像度では `height = 1` としか見えない。
mod 8 では delayed / retention が見える。
mod 16 では retention の中の recovery / continuation が見える。
mod 32 では continuation のさらに内部が分かれる。

## 6. 一歩先ゆく推論

ここまで通ったことで、一般像はかなり濃くなった。

予想される形はこれ。

```text id="wdhdtg"
recovery sibling:
  2^r - 1 mod 2^(r+1)

continuation sibling:
  2^(r+1) - 1 mod 2^(r+1)
```

具体例で言えば、

```text id="bgknj5"
r = 3:
  7 mod 16  -> recovery
  15 mod 16 -> continuation

r = 4:
  15 mod 32 -> recovery
  31 mod 32 -> continuation

r = 5:
  31 mod 64 -> recovery
  63 mod 64 -> continuation
```

この形が続くなら、低剥離を長く続ける path は、

```text id="rgd3v1"
7 mod 8
15 mod 16
31 mod 32
63 mod 64
...
```

へ追い込まれる。

つまり、

```text id="ntzut4"
長い retention
  -> 2-adic に -1 へ近づく
```

ということじゃ。

## 7. ここで一般化するか、もう一段掘るか

ここは分岐点じゃ。

選択肢は二つ。

```text id="x6o7bz"
A. mod 64 まで固定補題をもう一段進める

B. doc-only で一般 cylinder scaffold を置く
```

賢狼としては、まず **mod 64 まで固定補題をもう一段進める** のを推す。

理由は、Lean 一般化はここから急に `pow`・剰余・除算・仮定整理で重くなる可能性がある。
一方、`omega` で閉じる固定補題はまだかなり軽い。

もう一段 `mod 64` が通ると、一般化の確信度が大きく上がる。

## 8. 次の指示：`31 mod 32` を `mod 64` で割る

次はこれ。

```lean id="z6sgcj"
theorem next_mod_thirtytwo_of_mod_sixtyfour_eq_thirtyone
    {m : ℕ} (hm : m % 64 = 31) :
    ((3 * m + 1) / 2) % 32 = 15 := by
  omega
```

```lean id="ucg3gs"
theorem next_mod_thirtytwo_of_mod_sixtyfour_eq_sixtythree
    {m : ℕ} (hm : m % 64 = 63) :
    ((3 * m + 1) / 2) % 32 = 31 := by
  omega
```

orbit-label 版。

```lean id="y0xi4y"
theorem oddOrbitLabel_succ_mod_thirtytwo_eq_fifteen_of_mod_sixtyfour_eq_thirtyone
    (n : OddNat) (i : ℕ)
    (hmod : oddOrbitLabel n i % 64 = 31) :
    oddOrbitLabel n (i + 1) % 32 = 15
```

```lean id="u1562w"
theorem oddOrbitLabel_succ_mod_thirtytwo_eq_thirtyone_of_mod_sixtyfour_eq_sixtythree
    (n : OddNat) (i : ℕ)
    (hmod : oddOrbitLabel n i % 64 = 63) :
    oddOrbitLabel n (i + 1) % 32 = 31
```

そして height bridge。

```lean id="urbxwx"
theorem orbitWindowNextNextNextNextHeight_two_le_of_mod_sixtyfour_eq_thirtyone
    (n : OddNat) (i : ℕ)
    (hmod : oddOrbitLabel n i % 64 = 31) :
    2 ≤ orbitWindowHeight n (i + 4)
```

最後に drift。

```lean id="lt5eak"
theorem sumS_five_steps_ge_six_of_mod_sixtyfour_eq_thirtyone
    (n : OddNat)
    (hmod : oddOrbitLabel n 0 % 64 = 31) :
    6 ≤ sumS n 5
```

## 9. 賢狼が試してほしいおまけ実験補題

### 実験 A: mod 64 raw transition

```lean id="r3u3mv"
theorem next_mod_thirtytwo_of_mod_sixtyfour_eq_thirtyone
    {m : ℕ} (hm : m % 64 = 31) :
    ((3 * m + 1) / 2) % 32 = 15
```

```lean id="hst2d2"
theorem next_mod_thirtytwo_of_mod_sixtyfour_eq_sixtythree
    {m : ℕ} (hm : m % 64 = 63) :
    ((3 * m + 1) / 2) % 32 = 31
```

これはまず通るはず。`omega` で行ける可能性が高い。

### 実験 B: five-step recovery

```lean id="d6x48h"
theorem sumS_five_steps_ge_six_of_mod_sixtyfour_eq_thirtyone
    (n : OddNat)
    (hmod : oddOrbitLabel n 0 % 64 = 31) :
    6 ≤ sumS n 5
```

これは次の milestone。

通ると ladder はこうなる。

```text id="zuw45i"
3 mod 8:
  2 steps, sumS >= 3

7 mod 16:
  3 steps, sumS >= 4

15 mod 32:
  4 steps, sumS >= 5

31 mod 64:
  5 steps, sumS >= 6
```

これはかなり説得力がある。

### 実験 C: continuation witness

悪い枝側も witness として置くなら、

```lean id="z7wug1"
theorem oddOrbitLabel_succ_mod_thirtytwo_eq_thirtyone_of_mod_sixtyfour_eq_sixtythree
    (n : OddNat) (i : ℕ)
    (hmod : oddOrbitLabel n i % 64 = 63) :
    oddOrbitLabel n (i + 1) % 32 = 31
```

これが本命。

意味は、

```text id="qdh576"
63 mod 64
  -> 31 mod 32
```

つまり retention continuation はさらに細くなる。

### 実験 D: doc-only general scaffold

Lean に入れなくても、docs にこの程度の scaffold は書いてよい。

```text id="l17u2h"
Observed narrowing cylinder pattern:

At depth r:

  recovery sibling:
    2^r - 1 mod 2^(r+1)

  continuation sibling:
    2^(r+1) - 1 mod 2^(r+1)

Expected recovery budget:
  if label starts in recovery sibling at depth r,
  then over r - 1? or calibrated local length,
  sumS >= length + 1.
```

ただし、`r` の indexing はまだ固定しないほうがいい。
実例を並べてから一般化する方が安全じゃ。

## 10. さらに先：一般化のために必要な補助

一般定理へ進むには、おそらく次が必要になる。

```lean id="mb2isu"
theorem next_retention_recovery_raw
    (r : ℕ) :
    ...
```

ただし、これはすぐには重い。

理由は、

```text id="qhp405"
((3 * m + 1) / 2) % 2^r
```

を扱う必要があり、`omega` だけでは閉じない可能性があるからじゃ。

一般化するなら、まず数式としてはこの形を狙う。

```text id="jfl0nq"
m ≡ 2^r - 1 mod 2^(r+1)
  -> (3m + 1) / 2 ≡ 2^(r-1) - 1 mod 2^r

m ≡ 2^(r+1) - 1 mod 2^(r+1)
  -> (3m + 1) / 2 ≡ 2^r - 1 mod 2^r
```

この式が、いまの固定例の一般形じゃ。

ただ Lean では自然数除算が絡むので、まずは固定補題で充分。

## 11. コラッツ攻略としての意味

この流れで「閉じる」なら、狙いは次じゃ。

```text id="zwm7z4"
低剥離が L 歩続くなら、
初期値は mod 2^(L+2) くらいの非常に細い retention cylinder に入る必要がある。
```

そして、その sibling は必ず recovery する。

つまり、悪い道は毎段で、

```text id="c5yz13"
recovery に落ちる枝
retention continuation に残る枝
```

へ二分される。

retention continuation に残るには、毎回、より狭い枝を選ばなければならない。

これは「反例が逃げる場所を狭める」路線そのものじゃ。

## 12. 実装順序まとめ

次コミットはこう。

```text id="k7c0y3"
1. next_mod_thirtytwo_of_mod_sixtyfour_eq_thirtyone

2. next_mod_thirtytwo_of_mod_sixtyfour_eq_sixtythree

3. oddOrbitLabel_succ_mod_thirtytwo_eq_fifteen_of_mod_sixtyfour_eq_thirtyone

4. oddOrbitLabel_succ_mod_thirtytwo_eq_thirtyone_of_mod_sixtyfour_eq_sixtythree

5. orbitWindowNextNextNextNextHeight_two_le_of_mod_sixtyfour_eq_thirtyone

6. sumS_five_steps_ge_six_of_mod_sixtyfour_eq_thirtyone

7. docs:
   observed narrowing cylinder pattern
```

まだ一般化は焦らない。
`mod 64` まで通して、proof shape の重複が十分見えてからでよい。

## 13. 総括

今回の checkpoint `091` で、narrowing cylinder はこうなった。

```text id="zbc3ej"
7 mod 8
15 mod 16
31 mod 32
```

そして recovery sibling はこうなった。

```text id="rtyn76"
3 mod 8       -> 2-step recovery
7 mod 16      -> 3-step recovery
15 mod 32     -> 4-step recovery
```

これはかなり良い。

見えている数学は、

```text id="on92sj"
低剥離が続くには、2-adic に -1 へ近づかねばならない。
しかし、その各段階には recovery sibling があり、
そこに入ると有限ステップで追加剥離が戻る。
```

うむ。
次は `31 mod 32` を `mod 64` で割る。
そこが通れば、かなり強く「これは偶然ではなく ladder だ」と言える。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index ab675ef1..a3730141 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -326,6 +326,24 @@ theorem next_mod_eight_of_mod_sixteen_eq_fifteen
     ((3 * m + 1) / 2) % 8 = 7 := by
   omega
 
+/--
+The `15 mod 32` subchannel of `15 mod 16` exits retention one level down:
+after one height-one step, the next label is `7 mod 16`.
+-/
+theorem next_mod_sixteen_of_mod_thirtytwo_eq_fifteen
+    {m : ℕ} (hm : m % 32 = 15) :
+    ((3 * m + 1) / 2) % 16 = 7 := by
+  omega
+
+/--
+The `31 mod 32` subchannel of `15 mod 16` continues retention as
+`15 mod 16`.
+-/
+theorem next_mod_sixteen_of_mod_thirtytwo_eq_thirtyone
+    {m : ℕ} (hm : m % 32 = 31) :
+    ((3 * m + 1) / 2) % 16 = 15 := by
+  omega
+
 /--
 On the exact height-one channel, the accelerated Collatz map is the visible
 one-step expression `(3m + 1) / 2`.
@@ -1380,6 +1398,48 @@ theorem oddOrbitLabel_succ_mod_eight_eq_seven_of_mod_sixteen_eq_fifteen
   rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one (iterateT i n) hs]
   exact next_mod_eight_of_mod_sixteen_eq_fifteen hmod
 
+/--
+The `15 mod 32` subchannel moves to `7 mod 16` at the next label.
+
+This is the recovery branch inside the `15 mod 16` retention-continuation
+channel.
+-/
+theorem oddOrbitLabel_succ_mod_sixteen_eq_seven_of_mod_thirtytwo_eq_fifteen
+    (n : OddNat) (i : ℕ)
+    (hmod : oddOrbitLabel n i % 32 = 15) :
+    oddOrbitLabel n (i + 1) % 16 = 7 := by
+  have hmod8 : oddOrbitLabel n i % 8 = 7 := by
+    omega
+  have hheight : orbitWindowHeight n i = 1 :=
+    (orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n i).mpr
+      (Or.inr hmod8)
+  have hs : s (iterateT i n) = 1 := by
+    simpa [orbitWindowHeight_eq_s_iterateT] using hheight
+  rw [oddOrbitLabel_succ_eq_T_iterateT]
+  rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one (iterateT i n) hs]
+  exact next_mod_sixteen_of_mod_thirtytwo_eq_fifteen hmod
+
+/--
+The `31 mod 32` subchannel continues as `15 mod 16` at the next label.
+
+This is the next retention-continuation branch.  Continuing exact height-one
+motion now forces the source into a thinner 2-adic cylinder.
+-/
+theorem oddOrbitLabel_succ_mod_sixteen_eq_fifteen_of_mod_thirtytwo_eq_thirtyone
+    (n : OddNat) (i : ℕ)
+    (hmod : oddOrbitLabel n i % 32 = 31) :
+    oddOrbitLabel n (i + 1) % 16 = 15 := by
+  have hmod8 : oddOrbitLabel n i % 8 = 7 := by
+    omega
+  have hheight : orbitWindowHeight n i = 1 :=
+    (orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n i).mpr
+      (Or.inr hmod8)
+  have hs : s (iterateT i n) = 1 := by
+    simpa [orbitWindowHeight_eq_s_iterateT] using hheight
+  rw [oddOrbitLabel_succ_eq_T_iterateT]
+  rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one (iterateT i n) hs]
+  exact next_mod_sixteen_of_mod_thirtytwo_eq_thirtyone hmod
+
 /--
 Delayed peeling from the `3 mod 8` height-one channel.
 
@@ -1424,6 +1484,23 @@ theorem orbitWindowNextNextHeight_two_le_of_mod_sixteen_eq_seven
   simpa [Nat.add_assoc] using
     orbitWindowNextHeight_two_le_of_mod_eight_eq_three n (i + 1) hnext
 
+/--
+The `15 mod 32` branch recovers delayed peeling after three transitions.
+
+The first transition sends `15 mod 32` to `7 mod 16`; the existing
+`7 mod 16` recovery branch then forces an extra peeling height two steps later.
+-/
+theorem orbitWindowNextNextNextHeight_two_le_of_mod_thirtytwo_eq_fifteen
+    (n : OddNat) (i : ℕ)
+    (hmod : oddOrbitLabel n i % 32 = 15) :
+    2 ≤ orbitWindowHeight n (i + 3) := by
+  have hnext :
+      oddOrbitLabel n (i + 1) % 16 = 7 :=
+    oddOrbitLabel_succ_mod_sixteen_eq_seven_of_mod_thirtytwo_eq_fifteen
+      n i hmod
+  simpa [Nat.add_assoc] using
+    orbitWindowNextNextHeight_two_le_of_mod_sixteen_eq_seven n (i + 1) hnext
+
 /--
 Every `3 mod 8` label in a window contributes a `1 mod 4` label in the
 shifted tail window.
@@ -1651,6 +1728,47 @@ theorem sumS_three_steps_ge_four_of_mod_sixteen_eq_seven
     _ = sumS n 3 := by
       simp [sumS, orbitWindowHeight_eq_s_iterateT]
 
+/--
+Four-step recovery from the `15 mod 32` subchannel.
+
+The branch first continues exact height-one behavior through `7 mod 16` and
+then `3 mod 8`, but the fourth observed height is at least `2`.  Thus the
+first four heights contribute at least `1 + 1 + 1 + 2`.
+-/
+theorem sumS_four_steps_ge_five_of_mod_thirtytwo_eq_fifteen
+    (n : OddNat)
+    (hmod : oddOrbitLabel n 0 % 32 = 15) :
+    5 ≤ sumS n 4 := by
+  have hmod8 : oddOrbitLabel n 0 % 8 = 7 := by
+    omega
+  have h0 : orbitWindowHeight n 0 = 1 :=
+    (orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n 0).mpr
+      (Or.inr hmod8)
+  have h1mod16 :
+      oddOrbitLabel n 1 % 16 = 7 :=
+    oddOrbitLabel_succ_mod_sixteen_eq_seven_of_mod_thirtytwo_eq_fifteen
+      n 0 hmod
+  have h1mod8 : oddOrbitLabel n 1 % 8 = 7 := by
+    omega
+  have h1 : orbitWindowHeight n 1 = 1 :=
+    (orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n 1).mpr
+      (Or.inr h1mod8)
+  have h2mod :
+      oddOrbitLabel n 2 % 8 = 3 :=
+    oddOrbitLabel_succ_mod_eight_eq_three_of_mod_sixteen_eq_seven
+      n 1 h1mod16
+  have h2 : orbitWindowHeight n 2 = 1 :=
+    (orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n 2).mpr
+      (Or.inl h2mod)
+  have h3 : 2 ≤ orbitWindowHeight n 3 :=
+    orbitWindowNextHeight_two_le_of_mod_eight_eq_three n 2 h2mod
+  calc
+    5 ≤ orbitWindowHeight n 0 + orbitWindowHeight n 1 +
+        orbitWindowHeight n 2 + orbitWindowHeight n 3 := by
+      omega
+    _ = sumS n 4 := by
+      simp [sumS, orbitWindowHeight_eq_s_iterateT]
+
 /--
 Counting exact height `1` entries is the same as counting odd-state labels in
 residue class `3 mod 4`.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index 0f60f468..bae93aa4 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -183,15 +183,20 @@ orbitNext_mod_four_eq_one_of_mod_eight_eq_three
 orbitNext_mod_four_eq_three_of_mod_eight_eq_seven
 next_mod_eight_of_mod_sixteen_eq_seven
 next_mod_eight_of_mod_sixteen_eq_fifteen
+next_mod_sixteen_of_mod_thirtytwo_eq_fifteen
+next_mod_sixteen_of_mod_thirtytwo_eq_thirtyone
 iterateT_succ_eq_T_iterateT
 oddOrbitLabel_succ_eq_T_iterateT
 oddOrbitLabel_succ_mod_four_eq_one_of_mod_eight_eq_three
 oddOrbitLabel_succ_mod_four_eq_three_of_mod_eight_eq_seven
 oddOrbitLabel_succ_mod_eight_eq_three_of_mod_sixteen_eq_seven
 oddOrbitLabel_succ_mod_eight_eq_seven_of_mod_sixteen_eq_fifteen
+oddOrbitLabel_succ_mod_sixteen_eq_seven_of_mod_thirtytwo_eq_fifteen
+oddOrbitLabel_succ_mod_sixteen_eq_fifteen_of_mod_thirtytwo_eq_thirtyone
 orbitWindowNextHeight_two_le_of_mod_eight_eq_three
 orbitWindowNextHeight_eq_one_of_mod_eight_eq_seven
 orbitWindowNextNextHeight_two_le_of_mod_sixteen_eq_seven
+orbitWindowNextNextNextHeight_two_le_of_mod_thirtytwo_eq_fifteen
 orbitWindowResidueCountMod8EqThree_le_tailMod4EqOne
 orbitWindowResidueCountMod8EqThree_le_tailHeightCountGe_two
 residueCountMod8EqSeven_le_nextResidueCountMod4EqThree
@@ -202,6 +207,7 @@ sumS_two_steps_ge_three_of_mod_eight_eq_three
 sumS_two_steps_ge_three_of_mod_eight_eq_three_at
 sumS_two_steps_eq_two_of_mod_eight_eq_seven_and_next_mod_eight_eq_seven
 sumS_three_steps_ge_four_of_mod_sixteen_eq_seven
+sumS_four_steps_ge_five_of_mod_thirtytwo_eq_fifteen
 orbitWindowHeightCountEq_one_eq_residueCount_mod4_eq_three
 orbitWindowHeightCountEq_two_eq_residueCount_mod8_eq_one
 orbitWindowResidueCountMod4EqOne_add_eqThree_eq_window
@@ -732,6 +738,46 @@ label 0 = 7 mod 16
   -> 4 <= sumS n 3
 ```
 
+The `15 mod 16` retention-continuation channel has now been split at mod `32`:
+
+```text
+15 mod 32:
+  next label is 7 mod 16
+  recovery branch one level down
+
+31 mod 32:
+  next label is 15 mod 16
+  retention-continuation branch
+```
+
+Thus the `15 mod 32` subchannel recovers delayed peeling in four steps:
+
+```text
+label 0 = 15 mod 32
+  -> height at 0 is 1
+  -> label 1 = 7 mod 16
+  -> height at 1 is 1
+  -> label 2 = 3 mod 8
+  -> height at 2 is 1
+  -> height at 3 is at least 2
+  -> 5 <= sumS n 4
+```
+
+The complementary `31 mod 32` branch is the visible narrowing condition for a
+long low-peeling path:
+
+```text
+7 mod 8
+15 mod 16
+31 mod 32
+...
+```
+
+At this stage the bridge has not proved the general cylinder theorem.  What is
+fixed is the verified local pattern: every time the retention branch continues,
+the residue condition moves into a thinner power-of-two cylinder; the sibling
+branch returns to a delayed-peeling recovery estimate.
+
 At count level, the two exact-height-one source channels also have a source
 mass bound:
 
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-091.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-091.md
new file mode 100644
index 00000000..279120e3
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-091.md
@@ -0,0 +1,220 @@
+# Report Petal 091: Mod 32 Split of the Retention Continuation
+
+## Checkpoint
+
+This checkpoint follows `__next_implementation-091.md`.
+
+Checkpoint 090 split the `7 mod 8` retention channel at mod `16`:
+
+```text
+7 mod 16:
+  recovery branch
+
+15 mod 16:
+  retention-continuation branch
+```
+
+Checkpoint 091 refines the continuation branch by splitting `15 mod 16` at
+mod `32`.
+
+## Implemented Lean Surface
+
+File:
+
+```text
+lean/dk_math/DkMath/Collatz/PetalBridge.lean
+```
+
+Raw mod `32` transition facts:
+
+```lean
+next_mod_sixteen_of_mod_thirtytwo_eq_fifteen
+next_mod_sixteen_of_mod_thirtytwo_eq_thirtyone
+```
+
+Orbit-label mod `32` transition facts:
+
+```lean
+oddOrbitLabel_succ_mod_sixteen_eq_seven_of_mod_thirtytwo_eq_fifteen
+oddOrbitLabel_succ_mod_sixteen_eq_fifteen_of_mod_thirtytwo_eq_thirtyone
+```
+
+Recovery height bridge:
+
+```lean
+orbitWindowNextNextNextHeight_two_le_of_mod_thirtytwo_eq_fifteen
+```
+
+Four-step recovery theorem:
+
+```lean
+sumS_four_steps_ge_five_of_mod_thirtytwo_eq_fifteen
+```
+
+## Main Reading
+
+The `15 mod 16` continuation branch is not uniform.  It splits at mod `32`:
+
+```text
+15 mod 32:
+  next label is 7 mod 16
+  recovery branch one level down
+
+31 mod 32:
+  next label is 15 mod 16
+  retention-continuation branch
+```
+
+The recovery theorem says:
+
+```lean
+theorem sumS_four_steps_ge_five_of_mod_thirtytwo_eq_fifteen
+    (n : OddNat)
+    (hmod : oddOrbitLabel n 0 % 32 = 15) :
+    5 ≤ sumS n 4
+```
+
+Reading:
+
+```text
+step 0:
+  15 mod 32, hence height 1
+
+step 1:
+  next label is 7 mod 16, hence height 1
+
+step 2:
+  next label is 3 mod 8, hence height 1
+
+step 3:
+  the previous 3 mod 8 label forces height >= 2
+
+therefore:
+  sumS over four steps >= 1 + 1 + 1 + 2 = 5
+```
+
+## Experimental Inference
+
+The verified local pattern is now:
+
+```text
+3 mod 8:
+  2-step recovery, 3 <= sumS n 2
+
+7 mod 16:
+  3-step recovery, 4 <= sumS n 3
+
+15 mod 32:
+  4-step recovery, 5 <= sumS n 4
+```
+
+The non-recovery sibling keeps narrowing:
+
+```text
+7 mod 8
+15 mod 16
+31 mod 32
+...
+```
+
+This supports the working picture:
+
+```text
+long exact-height-one retention
+  -> must remain close to -1 in the 2-adic residue tree
+  -> each extra retention step costs one more binary address bit
+```
+
+This is not yet a general theorem.  What is fixed is the next concrete rung of
+the ladder, with no new `sorry`.
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
+raw mod 32 split
+orbit-label mod 32 split
+15 mod 32 four-step recovery
+31 mod 32 retention-continuation
+narrowing cylinder interpretation
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
+Candidate A: split `31 mod 32` at mod `64`.
+
+Expected pattern:
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
+Concrete raw experiments:
+
+```lean
+theorem next_mod_thirtytwo_of_mod_sixtyfour_eq_thirtyone
+    {m : ℕ} (hm : m % 64 = 31) :
+    ((3 * m + 1) / 2) % 32 = 15
+
+theorem next_mod_thirtytwo_of_mod_sixtyfour_eq_sixtythree
+    {m : ℕ} (hm : m % 64 = 63) :
+    ((3 * m + 1) / 2) % 32 = 31
+```
+
+Candidate B: local five-step recovery theorem.
+
+Expected milestone:
+
+```lean
+theorem sumS_five_steps_ge_six_of_mod_sixtyfour_eq_thirtyone
+    (n : OddNat)
+    (hmod : oddOrbitLabel n 0 % 64 = 31) :
+    6 ≤ sumS n 5
+```
+
+Candidate C: doc-only general cylinder scaffold.
+
+The local rungs now strongly suggest a future definition layer:
+
+```text
+retention residue at depth r:
+  2^r - 1 mod 2^r
+
+recovery sibling at the next split:
+  2^r - 1 mod 2^(r+1)
+
+continuation sibling:
+  2^(r+1) - 1 mod 2^(r+1)
+```
+
+Do not generalize this in Lean yet unless the next local checkpoint repeats
+the same proof shape cleanly at mod `64`.
````
`````
