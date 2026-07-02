# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: 75236b956566b13edbdeefe5762331452acaae0c

## Report

094 checkpoint 完了です。

`DkMath.Collatz.PetalBridge` に practical `hm` form を追加しました。`next_recovery_residue_of_mod` / `next_continuation_residue_of_mod` が入り、expanded theorem が任意の residue cell 上のラベルへ使える形になりました。あわせて `mod 512` 固定 anchor を general theorem から再証明する補題と、orbit-label 化の入口になる `mod 8 = 7` source-entry 補題も追加しています。

同期済み:

- [PetalBridge.lean](/lean/dk_math/DkMath/Collatz/PetalBridge.lean)
- [Collatz-PetalBridge-Status.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md)
- [report-petal-094.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-094.md)

検証:

- `lake build DkMath.Collatz.PetalBridge` passed
- `lake build DkMath.Collatz.Collatz2K26` passed
- `git diff --check` passed
- `PetalBridge.lean` 内の `sorry` なし

既存の upstream warning として `DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean:152:6 declaration uses sorry` は引き続き出ています。今回の追加では新規 `sorry` は入れていません。

## Review

## 1. 状況分析

うむ、ぬしの直感はまた当たりに近い。
今回の checkpoint `094` は、まさに「出発値が相対的にどの座標 cell にいるか」を扱える段階へ進んだ。

前回までは、

```text id="dxnmrn"
m = 2^(r+2) * t + residue
```

という展開形だった。

今回からは、

```text id="etmz93"
m % 2^(r+2) = residue
```

という **任意の値 `m` がその residue cell にいる** という実用形になった。

主結果はこれ。

```lean id="mu994k"
theorem next_recovery_residue_of_mod
    (r m : ℕ)
    (hm : m % (2 ^ (r + 2)) = 2 ^ (r + 1) - 1) :
    ((3 * m + 1) / 2) % (2 ^ (r + 1)) = 2 ^ r - 1
```

```lean id="nwknp4"
theorem next_continuation_residue_of_mod
    (r m : ℕ)
    (hm : m % (2 ^ (r + 2)) = 2 ^ (r + 2) - 1) :
    ((3 * m + 1) / 2) % (2 ^ (r + 1)) = 2 ^ (r + 1) - 1
```

添付レポートでも、expanded theorem が arbitrary label `m` の residue class へ使える practical `hm` form になった、と整理されている。さらに `mod 512` 固定 anchor も general theorem から再証明され、source-entry の `mod 8 = 7` 補題も入っている。

これはかなり大きい。
固定観測列から、**相対座標 cell 上の任意点に作用する遷移定理**へ変わった。

## 2. ぬしの見立てとの対応

ぬしの言う、

```text id="b3kske"
出発する値が、相対的にどの座標からの出発なのか？
```

これは今回、まさに

```lean id="zutdwz"
m % (2 ^ (r + 2)) = residue
```

として形式化され始めた。

つまり、

```text id="a9az4r"
値そのものを見るのではなく、
観測窓 mod 2^(r+2) の中での相対座標を見る
```

ということ。

そして、その相対座標が、

```text id="wdhdz4"
recovery sibling なのか
continuation sibling なのか
```

で、次の合同類が決まる。

これはかなり Petal 的じゃ。
`m` は絶対値ではなく、Petal cell 内の住所を持つ。

## 3. 今回の数学的意味

今回の theorem は、こう読める。

```text id="v12bnb"
recovery cell にいる任意の m:
  一歩後に外側の retention residue へ戻る

continuation cell にいる任意の m:
  一歩後に次階層の retention residue へ入る
```

以前は `t` を使った展開形だったので、

```text id="llzulk"
この形に書ける数ならそうなる
```

だった。

今回は、

```text id="i0us04"
この residue class に属する任意の数ならそうなる
```

になった。

ここが重要じゃ。

これはもう「観測窓の全座標に割り付ける」方向の入口じゃ。

## 4. レビュー

### 4.1. `hm` form は大成功

`Nat.mod_add_div` で

```text id="s27f6x"
m = M * (m / M) + m % M
```

へ分解し、`hm` で余りを書き換えて expanded theorem に戻す。
これは非常に良い設計じゃ。

今回のレポートでも、証明は checkpoint `093` の expanded theorem を再利用して短く閉じた、と整理されている。

この形は今後あらゆる residue-cell theorem の標準パターンになる。

### 4.2. `mod 512` anchor の再証明が良い

```lean id="agepbf"
next_mod_twohundredfiftysix_of_mod_fivehundredtwelve_eq_twohundredfiftyfive_via_general
next_mod_twohundredfiftysix_of_mod_fivehundredtwelve_eq_fivehundredeleven_via_general
```

これは usability test として非常に良い。

固定観測が、一般 theorem の instance であることが確認された。

つまり、`mod 512` までの ladder は偶然列ではなく、

```text id="un3jiz"
general recursive two-adic Petal theorem の具体例
```

になった。

### 4.3. source-entry 補題が orbit 化の入口

```lean id="v2j7ev"
recovery_residue_mod_eight_eq_seven
continuation_residue_mod_eight_eq_seven
```

これも重要。

orbit-label theorem に進むには、

```text id="vygzhp"
source label が exact height-one channel にいる
```

ことが必要。

つまり、加速 Collatz の `T` を visible raw step

```text id="dphvvr"
(3m + 1) / 2
```

として読むには、`m % 8 = 7` から `height = 1` を得たい。

今回、その source residue 自体が `7 mod 8` になることが押さえられた。

残るのは、

```text id="ff4hpg"
m % 2^(r+2) = residue
  -> m % 8 = 7
```

を arbitrary `m` へ移す橋じゃ。

## 5. ぬしの「新しい素数因子」観点

ここも面白い。

Collatz の奇数 step では、

```text id="vxa3m5"
3m + 1 = 2^h * nextOdd
```

となる。

ここで `h` が剥離量。
そして `nextOdd` の側には、当然、新しい奇数因子が現れる可能性がある。

つまり、`mod 2^r` の座標は、

```text id="ao296m"
2-adic な剥離・分岐の座標
```

を見ている。

一方で、`nextOdd` の奇数因子は、

```text id="x28mwl"
odd-prime side の構造変化
```

を見ている。

これは二層構造じゃ。

```text id="88a62y"
2-adic coordinate:
  どの branch を通るか

odd-prime factor side:
  次の odd core がどう変質するか
```

ぬしの言う「奇数操作が新しく増える」はここに繋がる。
`3m+1` のあと、2 の剥離を済ませると、残った奇数 core が次の出発点になる。
その odd core の因子構造が変われば、次にどの residue cell へ入るかの分布にも影響する可能性がある。

## 6. 一歩先ゆく推論

ここから見えてくる大きな構造はこうじゃ。

```text id="t1szu3"
出発値 m は、
2-adic Petal coordinate と
odd-prime factor coordinate
を同時に持つ。
```

2-adic 側は、今回の theorem でかなり規則的になった。

```text id="bcy304"
recovery sibling
continuation sibling
next retention cell
```

しかし odd-prime factor 側は、まだ見ていない。

ここを観測すると、

```text id="mceugx"
同じ 2-adic residue cell にいる値たちでも、
odd factor 構造の違いによって、
次以降の分岐頻度が変わるか？
```

が見える可能性がある。

これはかなり面白い。
Collatz の「ランダムに見える部分」は、この odd factor side にあるかもしれぬ。

## 7. 次の指示：まず practical residue-to-mod8 bridge

次はレポート通り、`m` に対する `mod 8` bridge を入れるのがよい。

### Recovery side

```lean id="a4uvb4"
theorem mod_eight_eq_seven_of_recovery_residue_of_two_le
    (r m : ℕ) (hr : 2 ≤ r)
    (hm : m % (2 ^ (r + 2)) = 2 ^ (r + 1) - 1) :
    m % 8 = 7
```

### Continuation side

```lean id="lu6pdr"
theorem mod_eight_eq_seven_of_continuation_residue_of_one_le
    (r m : ℕ) (hr : 1 ≤ r)
    (hm : m % (2 ^ (r + 2)) = 2 ^ (r + 2) - 1) :
    m % 8 = 7
```

証明方針は、レポートにもある通り、

```text id="nayzo2"
8 | 2^(r+2)

m % 8 = (m % 2^(r+2)) % 8
```

を使う方向がよい。

ただ、Lean で扱いやすくするなら、まず補助補題を作るのがよい。

```lean id="x4rl8q"
theorem mod_eq_mod_of_dvd_modulus
    {a M d : ℕ} (hd : d ∣ M) :
    a % d = (a % M) % d
```

Mathlib に似た補題がある可能性もあるが、なければこの形を作る。

使い方は、

```lean id="z6h60t"
have hmodReduce :
    m % 8 = (m % (2 ^ (r + 2))) % 8 := by
  -- use divisibility 8 ∣ 2^(r+2)
```

その後、

```lean id="rzc5n9"
rw [hm]
exact recovery_residue_mod_eight_eq_seven r hr
```

で閉じる。

## 8. 次の本命：orbit-label general theorem

`mod 8` bridge が通れば、orbit-label theorem に行ける。

### Recovery orbit theorem

```lean id="wvn4im"
theorem oddOrbitLabel_succ_recovery_residue_of_mod
    (r : ℕ) (hr : 2 ≤ r) (n : OddNat) (i : ℕ)
    (hmod :
      oddOrbitLabel n i % (2 ^ (r + 2)) = 2 ^ (r + 1) - 1) :
    oddOrbitLabel n (i + 1) % (2 ^ (r + 1)) = 2 ^ r - 1
```

証明の形はこう。

```text id="d96zbn"
1. hmod から oddOrbitLabel n i % 8 = 7 を得る

2. height = 1 を得る

3. T_val_eq_three_mul_add_one_div_two_of_s_eq_one を使う

4. next_recovery_residue_of_mod を適用
```

### Continuation orbit theorem

```lean id="ui6dii"
theorem oddOrbitLabel_succ_continuation_residue_of_mod
    (r : ℕ) (hr : 1 ≤ r) (n : OddNat) (i : ℕ)
    (hmod :
      oddOrbitLabel n i % (2 ^ (r + 2)) = 2 ^ (r + 2) - 1) :
    oddOrbitLabel n (i + 1) % (2 ^ (r + 1)) =
      2 ^ (r + 1) - 1
```

これは、recursive two-adic Petal が orbit-label 層に上がる瞬間じゃ。

## 9. さらに先：相対座標の集合で全座標を割り付ける

ぬしの言う、

```text id="cg78s0"
観測窓の相対座標の集合で全座標に割り付けられたら、無限も手のひらの上
```

これは良い。

Lean 的には次の方向になる。

```lean id="m0ngzm"
def TwoAdicCell (r : ℕ) := Fin (2 ^ r)
```

あるいは、既存の `PetalAddress` に寄せて、

```lean id="fnfek4"
structure CollatzTwoAdicPetalCell where
  depth : ℕ
  residue : ℕ
  bound : residue < 2 ^ depth
```

ただし、すぐ構造体化するより、まずは count と partition で行くのが良い。

たとえば、

```lean id="vqfb8q"
def orbitWindowResidueCountPow2
    (n : OddNat) (k depth residue : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n i % (2 ^ depth) = residue))
```

これがあると、

```text id="of519s"
ある depth の全 residue cell への occupation count
```

を扱える。

次に partition。

```lean id="n9dvfn"
theorem orbitWindowResidueCountPow2_sum_eq_window
    (n : OddNat) (k depth : ℕ) :
    (Finset.range (2 ^ depth)).sum
      (fun a => orbitWindowResidueCountPow2 n k depth a) = k
```

これは少し重いが、本当に「全座標に割り付ける」ならここが本丸。

## 10. 新しい素数因子を見るための実験案

ここはまだ PetalBridge に入れるには早いが、実験補題としては面白い。

Collatz step の odd core を、

```text id="qgzzdw"
nextOdd = (3m + 1) / 2^height
```

として、`m` と `nextOdd` の gcd や新因子を見る。

候補：

```lean id="houmhf"
def collatzOddNextVal (n : OddNat) : ℕ :=
  (T n).1
```

既に `(T n).1` があるなら不要。

観測したい性質は、

```text id="jydn5f"
Prime p divides next label
but p does not divide current label
```

つまり新奇数因子の発生。

```lean id="rpku8z"
def HasNewOddPrimeFactorAfterT (n : OddNat) : Prop :=
  ∃ p, Nat.Prime p ∧ p ∣ (T n).1 ∧ ¬ p ∣ n.1
```

ただし、これは常にあるとは限らない。
むしろ観測対象にするのがよい。

residue cell ごとに、

```text id="lv9vd8"
new odd prime factor が出る頻度
```

を見ると、ぬしの言う「近い出発値の値の中の因子に新しい素数因子の有無で軌道はどう変わるか」に近づく。

Lean theorem としては最初から頻度ではなく、定義だけで良い。

```lean id="m08ps2"
def OrbitWindowNewOddPrimeFactorCount
    (n : OddNat) (k : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (HasNewOddPrimeFactorAfterT (iterateT i n)))
```

ただし `Prop` の decidability が必要になるので、実装は重い可能性がある。
最初は docs / experiment note で十分。

## 11. 賢狼が試して欲しいおまけ実験補題

### 実験 A: modulus reduction bridge

```lean id="zy90n3"
theorem mod_eq_mod_of_dvd_modulus
    {a M d : ℕ} (hd : d ∣ M) :
    a % d = (a % M) % d
```

これが通ると、今後すべての「大きい residue から小さい residue へ落とす」証明が楽になる。

### 実験 B: recovery residue から `mod 8 = 7`

```lean id="p6m7y1"
theorem mod_eight_eq_seven_of_recovery_residue_of_two_le
    (r m : ℕ) (hr : 2 ≤ r)
    (hm : m % (2 ^ (r + 2)) = 2 ^ (r + 1) - 1) :
    m % 8 = 7
```

### 実験 C: continuation residue から `mod 8 = 7`

```lean id="d8to09"
theorem mod_eight_eq_seven_of_continuation_residue_of_one_le
    (r m : ℕ) (hr : 1 ≤ r)
    (hm : m % (2 ^ (r + 2)) = 2 ^ (r + 2) - 1) :
    m % 8 = 7
```

### 実験 D: orbit-label recovery theorem

```lean id="w0k8iv"
theorem oddOrbitLabel_succ_recovery_residue_of_mod
    (r : ℕ) (hr : 2 ≤ r) (n : OddNat) (i : ℕ)
    (hmod :
      oddOrbitLabel n i % (2 ^ (r + 2)) = 2 ^ (r + 1) - 1) :
    oddOrbitLabel n (i + 1) % (2 ^ (r + 1)) = 2 ^ r - 1
```

### 実験 E: orbit-label continuation theorem

```lean id="esz6q9"
theorem oddOrbitLabel_succ_continuation_residue_of_mod
    (r : ℕ) (hr : 1 ≤ r) (n : OddNat) (i : ℕ)
    (hmod :
      oddOrbitLabel n i % (2 ^ (r + 2)) = 2 ^ (r + 2) - 1) :
    oddOrbitLabel n (i + 1) % (2 ^ (r + 1)) =
      2 ^ (r + 1) - 1
```

### 実験 F: docs-only factor layer

ドキュメントだけでよいので、次の概念名を置く。

```text id="h735qo"
TwoAdicPetalCoordinate:
  mod 2^r residue address

OddFactorCarrier:
  odd core の素因子構造

NewOddPrimeFactor:
  T step 後に新しく現れる奇素因子

CoordinateFactorInteraction:
  2-adic coordinate branch と odd factor 変化の相互作用
```

## 12. 次コミットの推奨順

```text id="qnxxpm"
1. mod_eq_mod_of_dvd_modulus
   または Mathlib 既存補題の探索

2. mod_eight_eq_seven_of_recovery_residue_of_two_le

3. mod_eight_eq_seven_of_continuation_residue_of_one_le

4. oddOrbitLabel_succ_recovery_residue_of_mod

5. oddOrbitLabel_succ_continuation_residue_of_mod

6. docs:
   relative coordinate / factor layer の構想追加

7. 余裕があれば:
   orbitWindowResidueCountPow2 の設計だけメモ
```

## 13. 総括

今回の checkpoint `094` で、recursive two-adic Petal は practical form になった。

```text id="rsfvr7"
値 m がどの相対座標 cell にいるか
  -> 次の相対座標が決まる
```

これで、ぬしの言う

```text id="o86inc"
出発する値が、相対的にどの座標からの出発なのか
```

が、Lean theorem の主語になった。

次は、その相対座標が exact height-one source であることを arbitrary label `m` に移して、orbit-label theorem へ上げる。

そして、その先にあるのが、

```text id="rka1iv"
2-adic Petal coordinate
  ×
odd-prime factor structure
```

の相互作用じゃ。

うむ、道が見えてきた。
まずは相対座標の遷移法則を orbit-label 層まで上げる。
その後で、同じ座標 cell にいる出発値たちの odd factor side が軌道分岐にどう影響するかを見る。
ここまで行けば、「無限も手のひらの上」という言葉が、かなり具体的な数学になる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index 0acbd5cc..de14db5c 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -551,6 +551,96 @@ theorem next_continuation_residue_expanded
   rw [Nat.add_mul_mod_self_left]
   exact Nat.mod_eq_of_lt hlt
 
+/--
+The recovery sibling in practical residue-class form.
+
+This is the usable version of `next_recovery_residue_expanded`: if an arbitrary
+label lies in the recovery sibling modulo `2^(r + 2)`, then one visible
+height-one raw step lands in the outward residue `2^r - 1` modulo `2^(r + 1)`.
+-/
+theorem next_recovery_residue_of_mod
+    (r m : ℕ)
+    (hm : m % (2 ^ (r + 2)) = 2 ^ (r + 1) - 1) :
+    ((3 * m + 1) / 2) % (2 ^ (r + 1)) = 2 ^ r - 1 := by
+  let M := 2 ^ (r + 2)
+  have hdecomp : m = M * (m / M) + m % M := by
+    have h := Nat.mod_add_div m M
+    omega
+  rw [hdecomp]
+  dsimp [M] at hm ⊢
+  rw [hm]
+  simpa using next_recovery_residue_expanded r (m / 2 ^ (r + 2))
+
+/--
+The continuation sibling in practical residue-class form.
+
+If a label lies in the continuation sibling modulo `2^(r + 2)`, then one
+visible height-one raw step lands in `2^(r + 1) - 1` modulo `2^(r + 1)`, the
+next retention cell.
+-/
+theorem next_continuation_residue_of_mod
+    (r m : ℕ)
+    (hm : m % (2 ^ (r + 2)) = 2 ^ (r + 2) - 1) :
+    ((3 * m + 1) / 2) % (2 ^ (r + 1)) = 2 ^ (r + 1) - 1 := by
+  let M := 2 ^ (r + 2)
+  have hdecomp : m = M * (m / M) + m % M := by
+    have h := Nat.mod_add_div m M
+    omega
+  rw [hdecomp]
+  dsimp [M] at hm ⊢
+  rw [hm]
+  simpa using next_continuation_residue_expanded r (m / 2 ^ (r + 2))
+
+/--
+Usability test: the `mod 512` recovery anchor follows from the general
+residue-class theorem.
+-/
+theorem next_mod_twohundredfiftysix_of_mod_fivehundredtwelve_eq_twohundredfiftyfive_via_general
+    {m : ℕ} (hm : m % 512 = 255) :
+    ((3 * m + 1) / 2) % 256 = 127 := by
+  simpa using next_recovery_residue_of_mod 7 m hm
+
+/--
+Usability test: the `mod 512` continuation anchor follows from the general
+residue-class theorem.
+-/
+theorem next_mod_twohundredfiftysix_of_mod_fivehundredtwelve_eq_fivehundredeleven_via_general
+    {m : ℕ} (hm : m % 512 = 511) :
+    ((3 * m + 1) / 2) % 256 = 255 := by
+  simpa using next_continuation_residue_of_mod 7 m hm
+
+/--
+For depth at least `2`, a recovery sibling residue is an exact height-one
+source residue modulo `8`.
+-/
+theorem recovery_residue_mod_eight_eq_seven
+    (r : ℕ) (hr : 2 ≤ r) :
+    (2 ^ (r + 1) - 1) % 8 = 7 := by
+  rcases exists_add_of_le hr with ⟨k, rfl⟩
+  rw [show 2 + k + 1 = 3 + k by omega, pow_add]
+  norm_num
+  have hsplit : 8 * 2 ^ k - 1 = 7 + (2 ^ k - 1) * 8 := by
+    have hpos : 0 < 2 ^ k := pow_pos (by decide) k
+    omega
+  rw [hsplit]
+  rw [Nat.add_mul_mod_self_right]
+
+/--
+For depth at least `1`, a continuation sibling residue is an exact height-one
+source residue modulo `8`.
+-/
+theorem continuation_residue_mod_eight_eq_seven
+    (r : ℕ) (hr : 1 ≤ r) :
+    (2 ^ (r + 2) - 1) % 8 = 7 := by
+  rcases exists_add_of_le hr with ⟨k, rfl⟩
+  rw [show 1 + k + 2 = 3 + k by omega, pow_add]
+  norm_num
+  have hsplit : 8 * 2 ^ k - 1 = 7 + (2 ^ k - 1) * 8 := by
+    have hpos : 0 < 2 ^ k := pow_pos (by decide) k
+    omega
+  rw [hsplit]
+  rw [Nat.add_mul_mod_self_right]
+
 /--
 On the exact height-one channel, the accelerated Collatz map is the visible
 one-step expression `(3m + 1) / 2`.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index 9bc5a332..6f62ca4c 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -200,6 +200,12 @@ twoAdicRecoverySiblingResidue_eq_retentionResidue
 twoAdicContinuationSiblingResidue_eq_retentionResidue_succ
 next_recovery_residue_expanded
 next_continuation_residue_expanded
+next_recovery_residue_of_mod
+next_continuation_residue_of_mod
+next_mod_twohundredfiftysix_of_mod_fivehundredtwelve_eq_twohundredfiftyfive_via_general
+next_mod_twohundredfiftysix_of_mod_fivehundredtwelve_eq_fivehundredeleven_via_general
+recovery_residue_mod_eight_eq_seven
+continuation_residue_mod_eight_eq_seven
 iterateT_succ_eq_T_iterateT
 oddOrbitLabel_succ_eq_T_iterateT
 oddOrbitLabel_succ_mod_four_eq_one_of_mod_eight_eq_three
@@ -900,6 +906,41 @@ parent retention cell
   -> continuation sibling = next retention cell
 ```
 
+The expanded raw theorems now also have practical residue-class forms:
+
+```text
+m % 2^(r+2) = 2^(r+1) - 1
+  -> ((3m + 1) / 2) % 2^(r+1) = 2^r - 1
+
+m % 2^(r+2) = 2^(r+2) - 1
+  -> ((3m + 1) / 2) % 2^(r+1) = 2^(r+1) - 1
+```
+
+The proof decomposes an arbitrary label by `Nat.mod_add_div`:
+
+```text
+m = 2^(r+2) * (m / 2^(r+2)) + m % 2^(r+2)
+```
+
+and then reuses the expanded theorem.  This turns the recursive Petal theorem
+from a parametric raw expression into a theorem about any label inside the
+given residue cell.  The fixed `mod 512` anchors have been rederived from this
+general theorem as usability tests.
+
+The source-entry side is also now recorded:
+
+```text
+2 <= r
+  -> (2^(r+1) - 1) % 8 = 7
+
+1 <= r
+  -> (2^(r+2) - 1) % 8 = 7
+```
+
+This is the lower-bound condition needed before promoting the practical raw
+theorem to an orbit-label theorem: the source label must be in the exact
+height-one `7 mod 8` channel so that `T` is the visible `(3m + 1) / 2` step.
+
 At count level, the two exact-height-one source channels also have a source
 mass bound:
 
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-094.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-094.md
new file mode 100644
index 00000000..9e798829
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-094.md
@@ -0,0 +1,233 @@
+# Report Petal 094: Practical Residue Form and Source Entry
+
+## Checkpoint
+
+This checkpoint follows `__next_implementation-094.md`.
+
+The goal was to move from the expanded raw theorem to a practical theorem about
+an arbitrary label `m` known only by its residue class.
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
+New practical residue-class theorems:
+
+```lean
+next_recovery_residue_of_mod
+next_continuation_residue_of_mod
+```
+
+Fixed anchors rederived from the general theorem:
+
+```lean
+next_mod_twohundredfiftysix_of_mod_fivehundredtwelve_eq_twohundredfiftyfive_via_general
+next_mod_twohundredfiftysix_of_mod_fivehundredtwelve_eq_fivehundredeleven_via_general
+```
+
+Source-entry residue checks:
+
+```lean
+recovery_residue_mod_eight_eq_seven
+continuation_residue_mod_eight_eq_seven
+```
+
+## Main Result
+
+Recovery sibling:
+
+```lean
+theorem next_recovery_residue_of_mod
+    (r m : ℕ)
+    (hm : m % (2 ^ (r + 2)) = 2 ^ (r + 1) - 1) :
+    ((3 * m + 1) / 2) % (2 ^ (r + 1)) = 2 ^ r - 1
+```
+
+Continuation sibling:
+
+```lean
+theorem next_continuation_residue_of_mod
+    (r m : ℕ)
+    (hm : m % (2 ^ (r + 2)) = 2 ^ (r + 2) - 1) :
+    ((3 * m + 1) / 2) % (2 ^ (r + 1)) = 2 ^ (r + 1) - 1
+```
+
+This is the practical form of the recursive two-adic Petal:
+
+```text
+parent retention cell
+  -> recovery sibling
+  -> continuation sibling = next retention cell
+```
+
+The theorem now applies directly to any label sitting in the relevant residue
+cell, not only to a syntactic expanded expression.
+
+## Proof Reading
+
+The proof is short because checkpoint 093 already did the hard arithmetic.
+
+For `M = 2^(r+2)`, decompose:
+
+```text
+m = M * (m / M) + m % M
+```
+
+This is obtained from `Nat.mod_add_div` and normalized by `omega`.
+
+After rewriting by the hypothesis on `m % M`, the goal is exactly the expanded
+theorem from checkpoint 093:
+
+```lean
+next_recovery_residue_expanded r (m / 2 ^ (r + 2))
+next_continuation_residue_expanded r (m / 2 ^ (r + 2))
+```
+
+## Usability Tests
+
+The old fixed `mod 512` anchors were rederived from the general theorem:
+
+```text
+255 mod 512 -> 127 mod 256
+511 mod 512 -> 255 mod 256
+```
+
+This confirms that the previous numeric ladder is now an instance of the
+general recursive theorem.
+
+## Source Entry Condition
+
+The next orbit-label theorem cannot use the raw step unless the source is in
+the exact height-one channel.  The needed residue fact is now explicit:
+
+```lean
+theorem recovery_residue_mod_eight_eq_seven
+    (r : ℕ) (hr : 2 ≤ r) :
+    (2 ^ (r + 1) - 1) % 8 = 7
+
+theorem continuation_residue_mod_eight_eq_seven
+    (r : ℕ) (hr : 1 ≤ r) :
+    (2 ^ (r + 2) - 1) % 8 = 7
+```
+
+Reading:
+
+```text
+recovery source needs 2 <= r
+continuation source needs 1 <= r
+both enter the exact height-one 7 mod 8 channel
+```
+
+This is why the future orbit-label theorem should carry a lower-bound
+hypothesis on `r`.
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
+practical hm form
+mod 512 anchors via the general theorem
+source-entry mod 8 checks
+next orbit-label condition
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
+The orbit-label generalization itself was not added in this checkpoint.
+
+Reason:
+
+```text
+we still need the bridge from a large residue hypothesis on oddOrbitLabel
+to oddOrbitLabel % 8 = 7
+```
+
+The new residue checks prove the source residue itself is `7 mod 8`, but the
+next theorem must transfer this through an arbitrary label hypothesis:
+
+```lean
+m % (2 ^ (r + 2)) = residue
+  -> m % 8 = 7
+```
+
+This is the next small missing bridge.
+
+## Next Implementation Candidates
+
+Candidate A: practical residue-to-`mod 8` bridge.
+
+```lean
+theorem mod_eight_eq_seven_of_recovery_residue_of_two_le
+    (r m : ℕ) (hr : 2 ≤ r)
+    (hm : m % (2 ^ (r + 2)) = 2 ^ (r + 1) - 1) :
+    m % 8 = 7
+```
+
+Candidate B: continuation counterpart.
+
+```lean
+theorem mod_eight_eq_seven_of_continuation_residue_of_one_le
+    (r m : ℕ) (hr : 1 ≤ r)
+    (hm : m % (2 ^ (r + 2)) = 2 ^ (r + 2) - 1) :
+    m % 8 = 7
+```
+
+Candidate C: orbit-label recovery theorem.
+
+```lean
+theorem oddOrbitLabel_succ_recovery_residue_of_mod
+    (r : ℕ) (hr : 2 ≤ r) (n : OddNat) (i : ℕ)
+    (hmod :
+      oddOrbitLabel n i % (2 ^ (r + 2)) = 2 ^ (r + 1) - 1) :
+    oddOrbitLabel n (i + 1) % (2 ^ (r + 1)) = 2 ^ r - 1
+```
+
+Candidate D: orbit-label continuation theorem.
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
+The likely proof route for A and B is to use divisibility of moduli:
+
+```text
+8 | 2^(r+2)
+m % 8 = (m % 2^(r+2)) % 8
+```
+
+After that, the source-entry lemmas from this checkpoint should close the
+exact-height-one condition needed for C and D.
````
`````
