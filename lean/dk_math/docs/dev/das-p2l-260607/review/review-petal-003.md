# Git diff / Report / Review

## Update: Petal Address

gch: df2a91fbd5171c33b69a29994c64ffd12ecba40c

## Report

[Address.lean](/lean/dk_math/DkMath/Petal/Address.lean) に `outerPetalRemainder` 層を追加しました。

追加した定義:

```lean
def outerPetalRemainder (n lap m : Nat) : Nat :=
  (outerPetalAddress n lap m).offset
```

追加した補題:

```lean
theorem outerPetalRemainder_eq_offset
theorem outerPetalRemainder_pos
theorem outerPetalRemainder_le_blockSize
theorem outerPetalRemainder_eq_self_of_le_blockSize
theorem outerPetalRemainder_eq_self_of_isInheritanceChannel
theorem outerPetalAddress_channel_zero_remainder_eq_self
```

これで review の推奨だった核心、

```text
channel = 0 -> offset = m
```

を固定できました。つまり Lean 上で、

```text
継承口に入った値は、そのまま inner lap へ降りる
```

と言える状態になっています。

検証:

```text
lake build DkMath.Petal.Address
lake build DkMath.Petal
lake build DkMath
git diff --check
```

すべて成功です。

## Review

うむ、これは綺麗に決まった。
今回の `df2a91...` は、Petal Address における **継承口の本質** を Lean theorem として固定した更新じゃ。

## 1. 今回の核心

前回までで、

```text
channel = 0 ↔ m ≤ blockSize
```

が入っていた。

今回さらに、

```text
channel = 0 → outerPetalRemainder = m
```

が入った。

つまり、Petal の言葉では、

```text
継承口に入った値は、値を変えずに次の inner lap へ降りる
```

が Lean で証明された。

これはかなり大きい。
`channel 0` が単なる番号ではなく、 **継承口 / core channel** であることの振る舞いが、算術的に固定されたわけじゃ。

## 2. `outerPetalRemainder` の追加

追加された定義はこれじゃな。

```lean
def outerPetalRemainder (n lap m : Nat) : Nat :=
  (outerPetalAddress n lap m).offset
```

これは薄い定義だが、役割は大きい。

前は `offset` は address の一部だった。
今回から `outerPetalRemainder` という名前で、

```text
次の内側 lap へ渡す値
```

として読めるようになった。

この名前付けにより、今後の nested address がかなり書きやすくなる。

```text
outerPetalAddress
  現 lap での外側住所

outerPetalRemainder
  次 lap へ降りる値
```

という分担ができた。

## 3. 基本境界も揃った

追加された基本補題はよい。

```lean
outerPetalRemainder_eq_offset
outerPetalRemainder_pos
outerPetalRemainder_le_blockSize
```

これで remainder は、

$$
1\le \operatorname{remainder}\le blockSize
$$

という one-based value として再利用できる。

つまり、次の inner lap に渡したときにも、同じ address 関数の入力として扱える。

これは nested recursion の前提条件になる。

## 4. 継承口の振る舞いが theorem 化された

主補題はこれじゃ。

```lean
theorem outerPetalRemainder_eq_self_of_le_blockSize
```

意味は、

$$
1\le m,\quad m\le blockSize
$$

なら、

$$
outerPetalRemainder(n,lap,m)=m
$$

ということ。

これは zero-based 内部では、

$$
(m-1)\bmod blockSize=m-1
$$

だから当然だが、Petal 的にはもっと大事じゃ。

```text
値が最初の外側 block に収まるなら、
外側展開では何も剥がれず、
そのまま内側へ降りる
```

という意味になる。

さらに、

```lean
theorem outerPetalRemainder_eq_self_of_isInheritanceChannel
```

により、

```text
IsInheritanceChannel → remainder = m
```

が得られた。

そして最後に、

```lean
theorem outerPetalAddress_channel_zero_remainder_eq_self
```

で、

```text
channel = 0 → remainder = m
```

という計算寄りの表現も用意された。

この三層はよい。

```text
m ≤ blockSize 版
IsInheritanceChannel 版
channel = 0 版
```

がそれぞれ使える。

## 5. Petal Address の意味論が一段閉じた

ここまでで、Petal Address の外側 one-step はこう読める。

```text
m を lap 空間の中で観測する
  ↓
blockSize = 前 lap の総数
  ↓
channel = どの外側 channel にいるか
offset/remainder = その channel 内での位置
```

そして、

```text
channel = 0 のとき
  remainder = m
```

つまり、

```text
継承口は値を変えずに内側へ通す
```

が成立した。

一方で `channel > 0` なら Petal channel なので、そこでは

```text
外側 channel を一枚剥がして、
offset を内側値として読む
```

という構造になる。

これで nested address の再帰はほぼ見えた。

## 6. (R_5(2,25)) の読みが完全に定まった

例で言えば、

$$
R_5(2)=180,\quad blockSize=R_5(1)=30
$$

で、

$$
25\le 30
$$

だから channel (0)。

今回の theorem により、

$$
outerPetalRemainder(5,2,25)=25
$$

が出る。

つまり、

```text
R_5(2) から見ると 25 は継承口
  ↓
値 25 のまま R_5(1) へ降りる
  ↓
R_5(1) で見ると channel 4, offset 5
```

という読みが、もう単なる解釈ではなく、Lean に支えられる構造になった。

## 7. 次に自然な theorem

ここまで来たなら、次は二つが自然じゃ。

### 7.1. Petal channel では remainder が blockSize 以下

これはもう `outerPetalRemainder_le_blockSize` である程度ある。
次は、valid value のとき remainder が次 lap total に収まる、という名前付き補題が欲しい。

```lean
theorem outerPetalRemainder_le_prevTotal_of_valid
    {n lap m : Nat}
    (hlap : 0 < lap)
    (hm : 1 ≤ m)
    (hbound : m ≤ relPetalTotal n lap) :
    outerPetalRemainder n lap m ≤ relPetalTotal n (lap - 1)
```

これは `relPetalBlockSize` を経由するだけじゃが、nested address では使いやすい。

### 7.2. 1-step decomposition

より重要なのは、値の分解式じゃ。

$$
m = channel\cdot blockSize + remainder
$$

ただし one-based なので正確には、

$$
m-1 = channel\cdot blockSize + (remainder-1)
$$

または、

$$
m = channel\cdot blockSize + remainder
$$

が成立するはずじゃ。
なぜなら、

$$
m-1 = \left\lfloor\frac{m-1}{B}\right\rfloor B + ((m-1)\bmod B)
$$

なので、両辺に (1) を足すと、

$$
m = channel\cdot B + remainder
$$

になる。

Lean theorem 候補は、

```lean
theorem outerPetalAddress_decompose
    {n lap m : Nat} (hb : 0 < relPetalBlockSize n lap) :
    m =
      (outerPetalAddress n lap m).channel * relPetalBlockSize n lap
        + outerPetalRemainder n lap m
```

これは強い。
この定理が入ると、Petal Address が単なる計算ではなく、 **一意的な商・余り分解** として固定される。

わっちなら次はこれを入れる。

## 8. nested address への準備が整った

nested address は、概念的にはこうじゃ。

```text
nested(n, lap, m):
  if lap = 0:
    stop
  else:
    A := outerPetalAddress n lap m
    m' := outerPetalRemainder n lap m
    A :: nested(n, lap - 1, m')
```

ただし Lean では `lap - 1` 再帰より、`lap` に structural recursion する方がよい。

```lean
def nestedPetalAddress (n : Nat) : Nat → Nat → List PetalAddress
  | 0, m => []
  | lap + 1, m =>
      let A := outerPetalAddress n (lap + 1) m
      A :: nestedPetalAddress n lap (outerPetalRemainder n (lap + 1) m)
```

このとき今回の補題が効く。

継承口なら、

```text
m' = m
```

なので、値がそのまま内側へ降りる。
Petal channel なら、値は offset に圧縮される。

この差が「log 的圧縮位置情報」と「アドレス座標情報」の分岐点になる。

## 9. 実装フェーズ判定

わっちの判定では、

```text
Petal Address Phase 3:
  outer remainder / inheritance descent 完了
```

じゃ。

現状の到達点はこう。

```text
Counting:
  R_n(k) = baseUnitCore n * lapBase n ^ k

Address:
  channel / offset の算出

Channel semantics:
  channel 0 = inheritance/core
  channel > 0 = Petal

Remainder:
  次の inner lap へ渡す値
  channel 0 なら値は不変
```

これはかなり良い。
最初に曖昧だった「相対多角数」の土台が、もう住所体系として動き始めておる。

## 10. 総括

今回の更新で、継承口は名前だけではなくなった。

```text
channel 0
```

は、

```text
最初の外側 block
値を変えずに inner lap へ渡す口
```

として theorem 化された。

これは、今後の階層 address、階乗 orbit、プリモリアル orbit に進むときの核心になる。

次の一手は、

```lean
outerPetalAddress_decompose
```

じゃな。

これが入れば、

$$
m=channel\cdot blockSize+remainder
$$

として、Petal Address が完全に商余り分解になる。
ふふん、よいぞ D.。この調子なら、花弁の住所録どころか、花畑全体の測量図が描けるようになるぞい。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Petal/Address.lean b/lean/dk_math/DkMath/Petal/Address.lean
index 57f70d79..6802c66a 100644
--- a/lean/dk_math/DkMath/Petal/Address.lean
+++ b/lean/dk_math/DkMath/Petal/Address.lean
@@ -60,6 +60,15 @@ def outerPetalAddress (n lap m : Nat) : PetalAddress :=
     channel := (m - 1) / b
     offset := (m - 1) % b + 1 }
 
+/--
+The one-step remainder passed to the next inner lap.
+
+This is the offset component of the outer address.  If the address lands in the
+inheritance/core channel, this remainder is the original value itself.
+-/
+def outerPetalRemainder (n lap m : Nat) : Nat :=
+  (outerPetalAddress n lap m).offset
+
 /-- The block size at lap zero is the base unit core. -/
 theorem relPetalBlockSize_zero (n : Nat) :
     relPetalBlockSize n 0 = n := by
@@ -89,6 +98,11 @@ theorem outerPetalAddress_lap (n lap m : Nat) :
     (outerPetalAddress n lap m).lap = lap := by
   rfl
 
+/-- The outer remainder is definitionally the address offset. -/
+theorem outerPetalRemainder_eq_offset (n lap m : Nat) :
+    outerPetalRemainder n lap m = (outerPetalAddress n lap m).offset := by
+  rfl
+
 /-- The address is in the inheritance/core channel exactly when its channel is zero. -/
 theorem isInheritanceChannel_iff_channel_eq_zero (A : PetalAddress) :
     IsInheritanceChannel A ↔ A.channel = 0 := by
@@ -121,6 +135,12 @@ theorem outerPetalAddress_offset_pos
     0 < (outerPetalAddress n lap m).offset := by
   simp [outerPetalAddress]
 
+/-- The outer remainder is always positive. -/
+theorem outerPetalRemainder_pos
+    {n lap m : Nat} :
+    0 < outerPetalRemainder n lap m := by
+  exact outerPetalAddress_offset_pos
+
 /-- The offset of a valid address is bounded by the outer block size. -/
 theorem outerPetalAddress_offset_le_blockSize
     {n lap m : Nat} (hb : 0 < relPetalBlockSize n lap) :
@@ -128,6 +148,12 @@ theorem outerPetalAddress_offset_le_blockSize
   rw [outerPetalAddress]
   exact Nat.succ_le_of_lt (Nat.mod_lt _ hb)
 
+/-- The outer remainder is bounded by the outer block size. -/
+theorem outerPetalRemainder_le_blockSize
+    {n lap m : Nat} (hb : 0 < relPetalBlockSize n lap) :
+    outerPetalRemainder n lap m ≤ relPetalBlockSize n lap := by
+  exact outerPetalAddress_offset_le_blockSize hb
+
 /--
 The channel is bounded by the lap base when the observed value stays inside the
 current lap total.
@@ -206,6 +232,46 @@ theorem outerPetalAddress_isPetalChannel_of_blockSize_lt
     (outerPetalAddress_channel_eq_zero_iff_le_blockSize hm hb).1 h0
   exact (not_lt_of_ge hle) hbm
 
+/--
+If a one-based value stays inside the first outer block, the outer remainder is
+the original value.
+-/
+theorem outerPetalRemainder_eq_self_of_le_blockSize
+    {n lap m : Nat}
+    (hm : 1 ≤ m)
+    (hmb : m ≤ relPetalBlockSize n lap) :
+    outerPetalRemainder n lap m = m := by
+  have hlt : m - 1 < relPetalBlockSize n lap :=
+    Nat.sub_one_lt_of_le hm hmb
+  rw [outerPetalRemainder, outerPetalAddress]
+  rw [Nat.mod_eq_of_lt hlt]
+  exact Nat.sub_add_cancel hm
+
+/--
+If the outer address lands in the inheritance/core channel, the outer remainder
+is the original value.
+-/
+theorem outerPetalRemainder_eq_self_of_isInheritanceChannel
+    {n lap m : Nat}
+    (hm : 1 ≤ m)
+    (hb : 0 < relPetalBlockSize n lap)
+    (hA : IsInheritanceChannel (outerPetalAddress n lap m)) :
+    outerPetalRemainder n lap m = m := by
+  have hle : m ≤ relPetalBlockSize n lap :=
+    (outerPetalAddress_isInheritanceChannel_iff_le_blockSize hm hb).1 hA
+  exact outerPetalRemainder_eq_self_of_le_blockSize hm hle
+
+/--
+Channel `0` means the value descends unchanged to the next inner lap.
+-/
+theorem outerPetalAddress_channel_zero_remainder_eq_self
+    {n lap m : Nat}
+    (hm : 1 ≤ m)
+    (hb : 0 < relPetalBlockSize n lap)
+    (hch : (outerPetalAddress n lap m).channel = 0) :
+    outerPetalRemainder n lap m = m := by
+  exact outerPetalRemainder_eq_self_of_isInheritanceChannel hm hb hch
+
 /-- A bounded channel is at most the base unit core. -/
 theorem outerPetalAddress_channel_le_baseUnitCore
     {n lap m : Nat}
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/History.md b/lean/dk_math/docs/dev/das-p2l-260607/History.md
index 3707e9c2..de095a5b 100644
--- a/lean/dk_math/docs/dev/das-p2l-260607/History.md
+++ b/lean/dk_math/docs/dev/das-p2l-260607/History.md
@@ -1337,3 +1337,50 @@ git diff --check
 ```
 
 すべて成功です。
+
+### 2026/06/10  7:23
+
+[Address.lean](/lean/dk_math/DkMath/Petal/Address.lean) に `outerPetalRemainder` 層を追加しました。
+
+追加した定義:
+
+```lean
+def outerPetalRemainder (n lap m : Nat) : Nat :=
+  (outerPetalAddress n lap m).offset
+```
+
+追加した補題:
+
+```lean
+theorem outerPetalRemainder_eq_offset
+theorem outerPetalRemainder_pos
+theorem outerPetalRemainder_le_blockSize
+theorem outerPetalRemainder_eq_self_of_le_blockSize
+theorem outerPetalRemainder_eq_self_of_isInheritanceChannel
+theorem outerPetalAddress_channel_zero_remainder_eq_self
+```
+
+これで review の推奨だった核心、
+
+```text
+channel = 0 -> offset = m
+```
+
+を固定できました。つまり Lean 上で、
+
+```text
+継承口に入った値は、そのまま inner lap へ降りる
+```
+
+と言える状態になっています。
+
+検証:
+
+```text
+lake build DkMath.Petal.Address
+lake build DkMath.Petal
+lake build DkMath
+git diff --check
+```
+
+すべて成功です。
````
`````
