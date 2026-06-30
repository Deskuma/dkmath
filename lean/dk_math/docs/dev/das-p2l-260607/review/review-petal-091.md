# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: 2522dbc94a528e86cfce672c00bc398636d76579

## Report

090 を実装しました。

[PetalBridge.lean](/lean/dk_math/DkMath/Collatz/PetalBridge.lean) で、`7 mod 8` retention channel を `mod 16` で二分しました。

主な追加は以下です。

```lean
orbitWindowResidueCountMod8EqThree_add_seven_le_window
orbitWindowResidueCountMod8EqThree_add_seven_le_tail_partition

next_mod_eight_of_mod_sixteen_eq_seven
next_mod_eight_of_mod_sixteen_eq_fifteen

oddOrbitLabel_succ_mod_eight_eq_three_of_mod_sixteen_eq_seven
oddOrbitLabel_succ_mod_eight_eq_seven_of_mod_sixteen_eq_fifteen

orbitWindowNextNextHeight_two_le_of_mod_sixteen_eq_seven
sumS_three_steps_ge_four_of_mod_sixteen_eq_seven
```

読みとしては、`7 mod 8` の retention はさらに分岐します。

```text
7 mod 16  -> next 3 mod 8  -> recovery
15 mod 16 -> next 7 mod 8  -> retention continuation
```

特に `7 mod 16` は三歩で recovery することを Lean に固定しました。

```lean
theorem sumS_three_steps_ge_four_of_mod_sixteen_eq_seven
    (n : OddNat)
    (hmod : oddOrbitLabel n 0 % 16 = 7) :
    4 ≤ sumS n 3
```

同期済み:

- [Collatz-PetalBridge-Status.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md)
- [report-petal-090.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-090.md)

検証:

- `lake build DkMath.Collatz.PetalBridge` pass
- `lake build DkMath.Collatz.Collatz2K26` pass
- `git diff --check` pass

既存の `DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean` の `sorry` warning は引き続き出ますが、今回の変更で新しい `sorry` は入れていません。

## Review

## 1. 状況分析

来たな、ぬしよ。
checkpoint `090` は、かなり重要な節目じゃ。

今回で、前回まで残っていた

```text id="nl2ei7"
7 mod 8 retention channel
```

が、さらに `mod 16` で二分された。

```text id="cc3fem"
7 mod 16:
  next label is 3 mod 8
  recovery branch

15 mod 16:
  next label is 7 mod 8
  retention-continuation branch
```

これは、我々が話していた

```text id="ogp1w2"
低剥離が続くなら、
どんどん細い 2-adic cylinder に押し込まれる
```

という見立てに、最初の明確な Lean 証拠が入ったことになる。

添付レポートでも、checkpoint `090` は `7 mod 8` retention source を `mod 16` で精密化し、`7 mod 16` を recovery branch、`15 mod 16` を retention-continuation branch として整理している。

これは良い。
「コラッツを閉じに行く」ための方向が、かなりはっきりした。

## 2. 今回の核心

今回の主な追加はこの群じゃ。

```lean id="db4p3p"
next_mod_eight_of_mod_sixteen_eq_seven
next_mod_eight_of_mod_sixteen_eq_fifteen

oddOrbitLabel_succ_mod_eight_eq_three_of_mod_sixteen_eq_seven
oddOrbitLabel_succ_mod_eight_eq_seven_of_mod_sixteen_eq_fifteen

orbitWindowNextNextHeight_two_le_of_mod_sixteen_eq_seven
sumS_three_steps_ge_four_of_mod_sixteen_eq_seven
```

本命はこれ。

```lean id="od7j49"
theorem sumS_three_steps_ge_four_of_mod_sixteen_eq_seven
    (n : OddNat)
    (hmod : oddOrbitLabel n 0 % 16 = 7) :
    4 ≤ sumS n 3
```

意味はこう。

```text id="v4yixy"
0 step:
  7 mod 16
  -> height = 1

1 step:
  next label = 3 mod 8
  -> height = 1

2 step:
  next-next height >= 2

therefore:
  1 + 1 + 2 <= sumS over 3 steps
```

つまり、`7 mod 16` は一度 retention に入るが、三歩窓では recovery する。

これは「retention は無条件に悪いわけではない」ことを Lean 上で固定している。

## 3. 数学的な意味

ここまでの流れを整理すると、低剥離 channel はこう細分化されている。

```text id="cr0dfl"
height = 1
  -> mod 8 で見る

3 mod 8:
  delayed-peeling
  次に height >= 2

7 mod 8:
  retention
  次も height = 1 側
```

しかし今回、`7 mod 8` の内部が割れた。

```text id="2fulfi"
7 mod 8
  -> mod 16 で見る

7 mod 16:
  recovery branch
  次に 3 mod 8 へ行き、その次に height >= 2

15 mod 16:
  retention-continuation branch
  次も 7 mod 8 へ残る
```

つまり、悪い道はさらに狭まった。

以前は、

```text id="xwan0g"
低剥離を続けるには 7 mod 8 にいる必要がある
```

だった。

今回からは、

```text id="mmg7sq"
低剥離をさらに続けるには 15 mod 16 にいる必要がある
```

になる。

これが重要じゃ。

## 4. レビュー

### 4.1. raw transition と orbit transition の両方があるのが良い

まず算術として、

```lean id="emy5a0"
next_mod_eight_of_mod_sixteen_eq_seven
next_mod_eight_of_mod_sixteen_eq_fifteen
```

を置き、その後で orbit label へ持ち上げている。

この順序は正しい。

```text id="z3jqc7"
raw arithmetic
  -> T value
  -> orbit label transition
```

という橋が明確になっている。

### 4.2. `orbitWindowNextNextHeight_two_le_of_mod_sixteen_eq_seven` が良い

これは、単なる residue transition ではなく、height 側へ戻している。

```lean id="ye6sx7"
theorem orbitWindowNextNextHeight_two_le_of_mod_sixteen_eq_seven
    (n : OddNat) (i : ℕ)
    (hmod : oddOrbitLabel n i % 16 = 7) :
    2 ≤ orbitWindowHeight n (i + 2)
```

読みは、

```text id="qi7kp8"
7 mod 16 は二拍後に追加剥離を返す
```

じゃ。

これは delayed-peeling の階層版。
`3 mod 8` は一拍後、`7 mod 16` は二拍後に縮小力を返す。

このパターンはかなり大事。

### 4.3. source-channel bound も入った

```lean id="hoc5ho"
orbitWindowResidueCountMod8EqThree_add_seven_le_window
orbitWindowResidueCountMod8EqThree_add_seven_le_tail_partition
```

これは、`3 mod 8` と `7 mod 8` の exact height-one source channel 総量が窓を超えないという補題。

特に tail partition 由来の証明は意味が良い。

```text id="3t4fv5"
3 source:
  tail CountGe 2 へ入る

7 source:
  tail CountEq 1 へ入る

tail CountGe 2 + tail CountEq 1 = k
```

これは、単なる不等式ではなく、transition graph の保存量として読める。

## 5. いま見えている階層パターン

かなり綺麗なパターンが出てきた。

```text id="9wlyj4"
3 mod 8:
  1拍後に recovery

7 mod 16:
  2拍後に recovery

15 mod 32:
  おそらく 3拍後に recovery

31 mod 64:
  おそらく 4拍後に recovery
```

一方で retention continuation は、

```text id="x2ewvg"
7 mod 8
15 mod 16
31 mod 32
63 mod 64
...
```

のように進むはずじゃ。

つまり、低剥離を続ける道は、

```text id="uuz3wc"
2^r - 1 mod 2^r
```

へ押し込まれていく。

ここに、コラッツ攻略のかなり良い構造がある。

## 6. 一歩先ゆく推論

ここから見える一般像はこうじゃ。

```text id="drwpnn"
長く height = 1 を続けるには、
初期ラベルが 2^r - 1 mod 2^r に近い residue cylinder に入る必要がある。
```

これは直感的には、

```text id="btdszp"
低剥離 path は 2-adic に -1 へ近づく
```

と言える。

ただし注意が必要じゃ。
これはまだ一般定理ではない。
いま Lean で固定できているのは、`mod 8`, `mod 16` までの局所事実。

しかし観測パターンとしては、かなりはっきりしている。

```text id="1qmf04"
retention continuation:
  2^(r+1) - 1

recovery branch:
  2^r - 1
```

という形が見える。

## 7. 次の指示：`15 mod 16` を mod 32 で割る

次は `15 mod 16` の内部を `mod 32` で割るのが自然じゃ。

期待パターンはこれ。

```text id="o7m50r"
15 mod 32:
  next label is 7 mod 16
  recovery branch one level down

31 mod 32:
  next label is 15 mod 16
  retention-continuation branch
```

raw arithmetic から行く。

```lean id="l0czrb"
theorem next_mod_sixteen_of_mod_thirtytwo_eq_fifteen
    {m : ℕ} (hm : m % 32 = 15) :
    ((3 * m + 1) / 2) % 16 = 7 := by
  omega
```

```lean id="c92gqf"
theorem next_mod_sixteen_of_mod_thirtytwo_eq_thirtyone
    {m : ℕ} (hm : m % 32 = 31) :
    ((3 * m + 1) / 2) % 16 = 15 := by
  omega
```

orbit label 版。

```lean id="tccul4"
theorem oddOrbitLabel_succ_mod_sixteen_eq_seven_of_mod_thirtytwo_eq_fifteen
    (n : OddNat) (i : ℕ)
    (hmod : oddOrbitLabel n i % 32 = 15) :
    oddOrbitLabel n (i + 1) % 16 = 7
```

```lean id="w2gmwr"
theorem oddOrbitLabel_succ_mod_sixteen_eq_fifteen_of_mod_thirtytwo_eq_thirtyone
    (n : OddNat) (i : ℕ)
    (hmod : oddOrbitLabel n i % 32 = 31) :
    oddOrbitLabel n (i + 1) % 16 = 15
```

ここまで通れば、

```text id="hzu9d1"
15 mod 32
  -> 7 mod 16
  -> recovery after 3 transitions
```

が見える。

## 8. 次の本命補題：四歩 recovery

`15 mod 32` は、三拍目あたりで recovery するはずじゃ。

期待する theorem はこれ。

```lean id="w5n0ti"
theorem sumS_four_steps_ge_five_of_mod_thirtytwo_eq_fifteen
    (n : OddNat)
    (hmod : oddOrbitLabel n 0 % 32 = 15) :
    5 ≤ sumS n 4
```

読みはこう。

```text id="jkg8wh"
0 step:
  15 mod 32
  -> height = 1

1 step:
  next label = 7 mod 16
  -> height = 1

2 step:
  next label = 3 mod 8
  -> height = 1

3 step:
  next height >= 2

therefore:
  1 + 1 + 1 + 2 = 5
```

これはかなり良い。

`3 mod 8` は二歩合計で `3`。
`7 mod 16` は三歩合計で `4`。
`15 mod 32` は四歩合計で `5`。

つまり、

```text id="svcbfq"
recovery branch at depth r:
  L steps have sumS >= L + 1
```

という型が見えてくる。

## 9. さらに先：general cylinder scaffold

まだ一般化は早いが、薄い定義だけなら準備してよい。

たとえば doc-only か theorem 名だけの設計として、

```text id="p2e3mp"
RetentionCylinder r:
  residue = 2^r - 1 mod 2^r

RecoverySubchannel r:
  residue = 2^r - 1 mod 2^(r+1)

RetentionContinuation r:
  residue = 2^(r+1) - 1 mod 2^(r+1)
```

のように置ける。

Lean の def にするなら、まずは軽く。

```lean id="yydud6"
def retentionResidue (r : ℕ) : ℕ :=
  2 ^ r - 1
```

ただし、`2^0 - 1` などの端点が面倒なので、`r >= 3` などを仮定するか、まだ doc-only でよい。

今は固定補題をもう一段、`mod 32` まで通す方がよい。

## 10. 賢狼が試して欲しいおまけ実験補題

### 実験 A: `15 mod 32` recovery branch

```lean id="oqh47y"
theorem next_mod_sixteen_of_mod_thirtytwo_eq_fifteen
    {m : ℕ} (hm : m % 32 = 15) :
    ((3 * m + 1) / 2) % 16 = 7
```

これは最重要おまけ。
`15 mod 16` retention-continuation の内部が割れる。

### 実験 B: `31 mod 32` retention-continuation

```lean id="lz3vgw"
theorem next_mod_sixteen_of_mod_thirtytwo_eq_thirtyone
    {m : ℕ} (hm : m % 32 = 31) :
    ((3 * m + 1) / 2) % 16 = 15
```

これは悪い道がさらに細くなることを示す。

### 実験 C: 三段 recovery height bridge

```lean id="k9dpvj"
theorem orbitWindowNextNextNextHeight_two_le_of_mod_thirtytwo_eq_fifteen
    (n : OddNat) (i : ℕ)
    (hmod : oddOrbitLabel n i % 32 = 15) :
    2 ≤ orbitWindowHeight n (i + 3)
```

これは、`15 mod 32` が三拍後に追加剥離を返すことを言う。

### 実験 D: 四歩 drift

```lean id="rxl3pj"
theorem sumS_four_steps_ge_five_of_mod_thirtytwo_eq_fifteen
    (n : OddNat)
    (hmod : oddOrbitLabel n 0 % 32 = 15) :
    5 ≤ sumS n 4
```

これはかなり良い milestone になる。

## 11. 実装順序まとめ

Codex 復帰後のおすすめ順はこれ。

```text id="ysw57s"
1. next_mod_sixteen_of_mod_thirtytwo_eq_fifteen

2. next_mod_sixteen_of_mod_thirtytwo_eq_thirtyone

3. oddOrbitLabel_succ_mod_sixteen_eq_seven_of_mod_thirtytwo_eq_fifteen

4. oddOrbitLabel_succ_mod_sixteen_eq_fifteen_of_mod_thirtytwo_eq_thirtyone

5. orbitWindowNextNextNextHeight_two_le_of_mod_thirtytwo_eq_fifteen

6. sumS_four_steps_ge_five_of_mod_thirtytwo_eq_fifteen

7. doc note:
   retention cylinder pattern
```

余裕があれば、

```text id="kmgq3c"
8. retentionResidue def の設計だけ追加
```

ただし一般化はまだ焦らない方がよい。

## 12. 総括

今回の checkpoint `090` で、かなり良い絵が見えた。

```text id="zz0x7s"
7 mod 8:
  retention channel

7 mod 16:
  recovery branch

15 mod 16:
  retention-continuation branch
```

つまり、悪い channel は一段深く見れば二分される。

```text id="o6efud"
一方は recovery へ戻る。
一方はさらに細い retention cylinder へ進む。
```

この構造が続くなら、コラッツの低剥離 path は、

```text id="u47t78"
7 mod 8
15 mod 16
31 mod 32
63 mod 64
...
```

という、どんどん細い 2-adic cylinder に追い込まれる。

うむ。
この道は良い。
次は `15 mod 16` を `mod 32` で割る。
そこが通れば、`7 mod 16` の三歩 recovery に続いて、`15 mod 32` の四歩 recovery が見える。
これは「retention は続くほど条件が細くなる」という構造を、Lean 上で一段ずつ噛み砕く道じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index 7d3a3ec0..ab675ef1 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -310,6 +310,22 @@ theorem next_mod_four_of_mod_eight_eq_seven
     ((3 * m + 1) / 2) % 4 = 3 := by
   omega
 
+/--
+The `7 mod 16` subchannel of `7 mod 8` exits retention toward `3 mod 8`.
+-/
+theorem next_mod_eight_of_mod_sixteen_eq_seven
+    {m : ℕ} (hm : m % 16 = 7) :
+    ((3 * m + 1) / 2) % 8 = 3 := by
+  omega
+
+/--
+The `15 mod 16` subchannel of `7 mod 8` continues retention as `7 mod 8`.
+-/
+theorem next_mod_eight_of_mod_sixteen_eq_fifteen
+    {m : ℕ} (hm : m % 16 = 15) :
+    ((3 * m + 1) / 2) % 8 = 7 := by
+  omega
+
 /--
 On the exact height-one channel, the accelerated Collatz map is the visible
 one-step expression `(3m + 1) / 2`.
@@ -1324,6 +1340,46 @@ theorem oddOrbitLabel_succ_mod_four_eq_three_of_mod_eight_eq_seven
   rw [oddOrbitLabel_succ_eq_T_iterateT]
   exact orbitNext_mod_four_eq_three_of_mod_eight_eq_seven n i hmod
 
+/--
+The `7 mod 16` subchannel moves to `3 mod 8` at the next label.
+
+This is the recovery branch inside the `7 mod 8` retention channel.
+-/
+theorem oddOrbitLabel_succ_mod_eight_eq_three_of_mod_sixteen_eq_seven
+    (n : OddNat) (i : ℕ)
+    (hmod : oddOrbitLabel n i % 16 = 7) :
+    oddOrbitLabel n (i + 1) % 8 = 3 := by
+  have hmod8 : oddOrbitLabel n i % 8 = 7 := by
+    omega
+  have hheight : orbitWindowHeight n i = 1 :=
+    (orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n i).mpr
+      (Or.inr hmod8)
+  have hs : s (iterateT i n) = 1 := by
+    simpa [orbitWindowHeight_eq_s_iterateT] using hheight
+  rw [oddOrbitLabel_succ_eq_T_iterateT]
+  rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one (iterateT i n) hs]
+  exact next_mod_eight_of_mod_sixteen_eq_seven hmod
+
+/--
+The `15 mod 16` subchannel continues as `7 mod 8` at the next label.
+
+This is the next retention-continuation branch.
+-/
+theorem oddOrbitLabel_succ_mod_eight_eq_seven_of_mod_sixteen_eq_fifteen
+    (n : OddNat) (i : ℕ)
+    (hmod : oddOrbitLabel n i % 16 = 15) :
+    oddOrbitLabel n (i + 1) % 8 = 7 := by
+  have hmod8 : oddOrbitLabel n i % 8 = 7 := by
+    omega
+  have hheight : orbitWindowHeight n i = 1 :=
+    (orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n i).mpr
+      (Or.inr hmod8)
+  have hs : s (iterateT i n) = 1 := by
+    simpa [orbitWindowHeight_eq_s_iterateT] using hheight
+  rw [oddOrbitLabel_succ_eq_T_iterateT]
+  rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one (iterateT i n) hs]
+  exact next_mod_eight_of_mod_sixteen_eq_fifteen hmod
+
 /--
 Delayed peeling from the `3 mod 8` height-one channel.
 
@@ -1351,6 +1407,23 @@ theorem orbitWindowNextHeight_eq_one_of_mod_eight_eq_seven
   apply (orbitWindowHeight_eq_one_iff_mod_four_eq_three n (i + 1)).mpr
   exact oddOrbitLabel_succ_mod_four_eq_three_of_mod_eight_eq_seven n i hmod
 
+/--
+The `7 mod 16` branch recovers delayed peeling after two transitions.
+
+At time `i`, the label is in the retaining `7 mod 8` channel.  The finer
+`7 mod 16` coordinate sends the next label to `3 mod 8`, so the following
+height is at least `2`.
+-/
+theorem orbitWindowNextNextHeight_two_le_of_mod_sixteen_eq_seven
+    (n : OddNat) (i : ℕ)
+    (hmod : oddOrbitLabel n i % 16 = 7) :
+    2 ≤ orbitWindowHeight n (i + 2) := by
+  have hnext :
+      oddOrbitLabel n (i + 1) % 8 = 3 :=
+    oddOrbitLabel_succ_mod_eight_eq_three_of_mod_sixteen_eq_seven n i hmod
+  simpa [Nat.add_assoc] using
+    orbitWindowNextHeight_two_le_of_mod_eight_eq_three n (i + 1) hnext
+
 /--
 Every `3 mod 8` label in a window contributes a `1 mod 4` label in the
 shifted tail window.
@@ -1431,6 +1504,28 @@ theorem orbitWindowResidueCountMod8EqSeven_le_tailHeightCountEq_one
   rw [orbitWindowHeightCountEqTail_one_eq_tailResidueCount_mod4_eq_three]
   exact residueCountMod8EqSeven_le_nextResidueCountMod4EqThree n k
 
+/--
+Source-channel sum bound through the tail partition.
+
+The `3 mod 8` source feeds the tail extra-peeling side, and the `7 mod 8`
+source feeds the tail exact-height-one side.  Since those two tail sides
+partition the tail window, the two source counts together cannot exceed `k`.
+-/
+theorem orbitWindowResidueCountMod8EqThree_add_seven_le_tail_partition
+    (n : OddNat) (k : ℕ) :
+    orbitWindowResidueCountMod8EqThree n k +
+      orbitWindowResidueCountMod8EqSeven n k ≤ k := by
+  have h3 :
+      orbitWindowResidueCountMod8EqThree n k ≤
+        orbitWindowHeightCountGeTail n k 2 :=
+    orbitWindowResidueCountMod8EqThree_le_tailHeightCountGe_two n k
+  have h7 :
+      orbitWindowResidueCountMod8EqSeven n k ≤
+        orbitWindowHeightCountEqTail n k 1 :=
+    orbitWindowResidueCountMod8EqSeven_le_tailHeightCountEq_one n k
+  have hsplit := orbitWindowHeightTail_countGe_two_add_countEq_one_eq_window n k
+  omega
+
 /--
 The shifted-tail threshold count is contained in the ordinary count over the
 one-step-longer window.
@@ -1525,6 +1620,37 @@ theorem sumS_two_steps_eq_two_of_mod_eight_eq_seven_and_next_mod_eight_eq_seven
     _ = 2 := by
       omega
 
+/--
+Three-step recovery from the `7 mod 16` subchannel.
+
+The first step is exact height `1`; the next label lands in `3 mod 8`, hence
+the second step is also exact height `1` but forces height at least `2` on the
+third step.  Thus the first three heights contribute at least `1 + 1 + 2`.
+-/
+theorem sumS_three_steps_ge_four_of_mod_sixteen_eq_seven
+    (n : OddNat)
+    (hmod : oddOrbitLabel n 0 % 16 = 7) :
+    4 ≤ sumS n 3 := by
+  have hmod8 : oddOrbitLabel n 0 % 8 = 7 := by
+    omega
+  have h0 : orbitWindowHeight n 0 = 1 :=
+    (orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n 0).mpr
+      (Or.inr hmod8)
+  have h1mod :
+      oddOrbitLabel n 1 % 8 = 3 :=
+    oddOrbitLabel_succ_mod_eight_eq_three_of_mod_sixteen_eq_seven n 0 hmod
+  have h1 : orbitWindowHeight n 1 = 1 :=
+    (orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n 1).mpr
+      (Or.inl h1mod)
+  have h2 : 2 ≤ orbitWindowHeight n 2 :=
+    orbitWindowNextHeight_two_le_of_mod_eight_eq_three n 1 h1mod
+  calc
+    4 ≤ orbitWindowHeight n 0 + orbitWindowHeight n 1 +
+        orbitWindowHeight n 2 := by
+      omega
+    _ = sumS n 3 := by
+      simp [sumS, orbitWindowHeight_eq_s_iterateT]
+
 /--
 Counting exact height `1` entries is the same as counting odd-state labels in
 residue class `3 mod 4`.
@@ -1632,6 +1758,18 @@ theorem orbitWindowResidueCountMod8_partition_eq_window
                   simp [hSeven]
                   omega
 
+/--
+The two exact-height-one source channels cannot exceed the window size.
+
+This proof reads directly from the mod `8` partition.
+-/
+theorem orbitWindowResidueCountMod8EqThree_add_seven_le_window
+    (n : OddNat) (k : ℕ) :
+    orbitWindowResidueCountMod8EqThree n k +
+      orbitWindowResidueCountMod8EqSeven n k ≤ k := by
+  have hpart := orbitWindowResidueCountMod8_partition_eq_window n k
+  omega
+
 /--
 The `height >= 1` occupation count fills the whole observation window.
 
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index 4fc4df3c..0f60f468 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -181,24 +181,32 @@ orbitWindowHeightTail_countGe_two_add_countEq_one_eq_window
 orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven
 orbitNext_mod_four_eq_one_of_mod_eight_eq_three
 orbitNext_mod_four_eq_three_of_mod_eight_eq_seven
+next_mod_eight_of_mod_sixteen_eq_seven
+next_mod_eight_of_mod_sixteen_eq_fifteen
 iterateT_succ_eq_T_iterateT
 oddOrbitLabel_succ_eq_T_iterateT
 oddOrbitLabel_succ_mod_four_eq_one_of_mod_eight_eq_three
 oddOrbitLabel_succ_mod_four_eq_three_of_mod_eight_eq_seven
+oddOrbitLabel_succ_mod_eight_eq_three_of_mod_sixteen_eq_seven
+oddOrbitLabel_succ_mod_eight_eq_seven_of_mod_sixteen_eq_fifteen
 orbitWindowNextHeight_two_le_of_mod_eight_eq_three
 orbitWindowNextHeight_eq_one_of_mod_eight_eq_seven
+orbitWindowNextNextHeight_two_le_of_mod_sixteen_eq_seven
 orbitWindowResidueCountMod8EqThree_le_tailMod4EqOne
 orbitWindowResidueCountMod8EqThree_le_tailHeightCountGe_two
 residueCountMod8EqSeven_le_nextResidueCountMod4EqThree
 orbitWindowResidueCountMod8EqSeven_le_tailHeightCountEq_one
+orbitWindowResidueCountMod8EqThree_add_seven_le_tail_partition
 orbitWindowHeightCountGeTail_le_countGe_succ
 sumS_two_steps_ge_three_of_mod_eight_eq_three
 sumS_two_steps_ge_three_of_mod_eight_eq_three_at
 sumS_two_steps_eq_two_of_mod_eight_eq_seven_and_next_mod_eight_eq_seven
+sumS_three_steps_ge_four_of_mod_sixteen_eq_seven
 orbitWindowHeightCountEq_one_eq_residueCount_mod4_eq_three
 orbitWindowHeightCountEq_two_eq_residueCount_mod8_eq_one
 orbitWindowResidueCountMod4EqOne_add_eqThree_eq_window
 orbitWindowResidueCountMod8_partition_eq_window
+orbitWindowResidueCountMod8EqThree_add_seven_le_window
 orbitWindowHeightPrefixCountGe_one_eq
 orbitWindowHeightPrefixCountGe_two_eq_prefixResidueCount_mod4_eq_one
 orbitWindowHeightPrefix_sum_ge_window_add_countGe_two
@@ -701,6 +709,48 @@ label 0 = 7 mod 8 and label 1 = 7 mod 8
   -> sumS n 2 = 2
 ```
 
+The `7 mod 8` retention channel has now been split at mod `16`:
+
+```text
+7 mod 16:
+  next label is 3 mod 8
+  recovery branch
+
+15 mod 16:
+  next label is 7 mod 8
+  retention-continuation branch
+```
+
+Thus the `7 mod 16` subchannel recovers delayed peeling in three steps:
+
+```text
+label 0 = 7 mod 16
+  -> height at 0 is 1
+  -> label 1 = 3 mod 8
+  -> height at 1 is 1
+  -> height at 2 is at least 2
+  -> 4 <= sumS n 3
+```
+
+At count level, the two exact-height-one source channels also have a source
+mass bound:
+
+```text
+residueCountMod8EqThree + residueCountMod8EqSeven <= k
+```
+
+There are two readings of this bound:
+
+```text
+mod 8 partition:
+  the two source channels are part of the four odd mod 8 classes
+
+tail partition:
+  3 source enters tail CountGe 2
+  7 source enters tail CountEq 1
+  tail CountGe 2 + tail CountEq 1 = k
+```
+
 The next higher-coordinate experiment also passed:
 
 ```text
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-090.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-090.md
new file mode 100644
index 00000000..a1b64f22
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-090.md
@@ -0,0 +1,223 @@
+# Report Petal 090: Mod 16 Split of the Retention Channel
+
+## Checkpoint
+
+This checkpoint follows `__next_implementation-090.md`.
+
+Checkpoint 089 split the exact height-one layer into:
+
+```text
+3 mod 8:
+  delayed-peeling source
+
+7 mod 8:
+  retention source
+```
+
+Checkpoint 090 refines the retention source by splitting `7 mod 8` at
+mod `16`.
+
+## Implemented Lean Surface
+
+File:
+
+```text
+lean/dk_math/DkMath/Collatz/PetalBridge.lean
+```
+
+Source-channel bounds:
+
+```lean
+orbitWindowResidueCountMod8EqThree_add_seven_le_tail_partition
+orbitWindowResidueCountMod8EqThree_add_seven_le_window
+```
+
+Raw mod `16` transition facts:
+
+```lean
+next_mod_eight_of_mod_sixteen_eq_seven
+next_mod_eight_of_mod_sixteen_eq_fifteen
+```
+
+Orbit-label mod `16` transition facts:
+
+```lean
+oddOrbitLabel_succ_mod_eight_eq_three_of_mod_sixteen_eq_seven
+oddOrbitLabel_succ_mod_eight_eq_seven_of_mod_sixteen_eq_fifteen
+```
+
+Recovery height bridge:
+
+```lean
+orbitWindowNextNextHeight_two_le_of_mod_sixteen_eq_seven
+```
+
+Three-step recovery theorem:
+
+```lean
+sumS_three_steps_ge_four_of_mod_sixteen_eq_seven
+```
+
+## Main Reading
+
+The `7 mod 8` retention channel is not uniform.  It splits at mod `16`:
+
+```text
+7 mod 16:
+  next label is 3 mod 8
+  recovery branch
+
+15 mod 16:
+  next label is 7 mod 8
+  retention-continuation branch
+```
+
+This is the first formal evidence for the narrowing-cylinder picture:
+
+```text
+long low-peeling retention
+  -> must pass through narrower 2-adic residue channels
+```
+
+The recovery theorem says:
+
+```lean
+theorem sumS_three_steps_ge_four_of_mod_sixteen_eq_seven
+    (n : OddNat)
+    (hmod : oddOrbitLabel n 0 % 16 = 7) :
+    4 ≤ sumS n 3
+```
+
+Reading:
+
+```text
+step 0:
+  7 mod 16, hence height 1
+
+step 1:
+  next label is 3 mod 8, hence height 1
+
+step 2:
+  3 mod 8 forces next height >= 2
+
+therefore:
+  sumS over three steps >= 1 + 1 + 2 = 4
+```
+
+## Source Mass Bound
+
+The two exact-height-one source channels satisfy:
+
+```lean
+theorem orbitWindowResidueCountMod8EqThree_add_seven_le_window
+    (n : OddNat) (k : ℕ) :
+    orbitWindowResidueCountMod8EqThree n k +
+      orbitWindowResidueCountMod8EqSeven n k ≤ k
+```
+
+The tail-split proof is also available:
+
+```lean
+theorem orbitWindowResidueCountMod8EqThree_add_seven_le_tail_partition
+    (n : OddNat) (k : ℕ) :
+    orbitWindowResidueCountMod8EqThree n k +
+      orbitWindowResidueCountMod8EqSeven n k ≤ k
+```
+
+The second proof is more meaningful for the transition graph:
+
+```text
+3 source -> tail CountGe 2
+7 source -> tail CountEq 1
+tail CountGe 2 + tail CountEq 1 = k
+```
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
+source-channel sum bound
+mod 16 split of the 7 mod 8 retention channel
+7 mod 16 recovery branch
+15 mod 16 retention-continuation branch
+three-step recovery theorem
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
+Candidate A: split `15 mod 16` at mod `32`.
+
+Expected pattern:
+
+```text
+15 mod 32:
+  exits toward 3 mod 8 or 3 mod 16-style recovery
+
+31 mod 32:
+  continues retention as 7 mod 8
+```
+
+Concrete raw experiments:
+
+```lean
+theorem next_mod_sixteen_of_mod_thirtytwo_eq_fifteen
+    {m : ℕ} (hm : m % 32 = 15) :
+    ((3 * m + 1) / 2) % 16 = 7
+
+theorem next_mod_sixteen_of_mod_thirtytwo_eq_thirtyone
+    {m : ℕ} (hm : m % 32 = 31) :
+    ((3 * m + 1) / 2) % 16 = 15
+```
+
+Candidate B: general cylinder conjecture scaffold.
+
+The observed pattern suggests:
+
+```text
+2^(r+1) - 1:
+  retention continuation
+
+2^r - 1:
+  recovery branch at the next residue depth
+```
+
+Do not generalize too early, but a doc-only conjecture note may help guide
+future local theorem names.
+
+Candidate C: local sum API.
+
+The recovery theorem is currently expressed through `sumS n 3`.  If local
+multi-step statements become common, define:
+
+```lean
+noncomputable def sumSFrom (n : OddNat) (start len : ℕ) : ℕ :=
+  (List.range len).map
+    (fun j => orbitWindowHeight n (start + j))
+  |>.sum
+```
+
+This should wait until there are at least two or three local-window theorems
+that would actually use it.
````
`````
