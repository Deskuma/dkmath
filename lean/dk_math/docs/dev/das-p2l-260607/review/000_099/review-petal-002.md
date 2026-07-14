# Git diff / Report / Review

## Add: review

gch: ca0c1f042c6e4d5254af9161b11fd11cb8a382fd

## Report

[Address.lean](/lean/dk_math/DkMath/Petal/Address.lean) に channel 判定層を実装しました。

追加した内容:

```lean
def IsInheritanceChannel
def IsPetalChannel
```

基本補題:

```lean
theorem isInheritanceChannel_iff_channel_eq_zero
theorem isPetalChannel_iff_channel_pos
theorem not_isPetalChannel_of_isInheritanceChannel
theorem isPetalChannel_of_not_isInheritanceChannel
```

outer address 側の補題:

```lean
theorem outerPetalAddress_channel_eq_zero_iff_sub_lt_blockSize
theorem outerPetalAddress_channel_eq_zero_iff_le_blockSize
theorem outerPetalAddress_isInheritanceChannel_iff_le_blockSize
theorem outerPetalAddress_isPetalChannel_of_blockSize_lt
theorem outerPetalAddress_channel_le_baseUnitCore
```

これで、1-based value `m` について、

```text
channel = 0  ↔  m ≤ blockSize
```

が Lean 上で固定されました。つまり「外側 block の最初に収まるなら inheritance/core channel」という読みが theorem になっています。

検証:

```text
lake build DkMath.Petal.Address
lake build DkMath.Petal
lake build DkMath
git diff --check
```

すべて成功です。

## Review

うむ、これはかなり良い更新じゃ。
今回の `333ce9...` で、Petal Address は「計算できる住所」から一歩進んで、 **意味を判定できる住所** になった。

## 1. 今回の核心

今回の本質はこれじゃ。

```text id="ow0ixx"
channel = 0
  ↔ inheritance/core channel
  ↔ m ≤ blockSize

channel > 0
  ↔ Petal channel
  ↔ m が最初の外側 block を越えた
```

前回までは、

```lean id="za1pbx"
channel := (m - 1) / blockSize
```

という算出式があるだけだった。

今回、

```lean id="pz2z19"
def IsInheritanceChannel
def IsPetalChannel
```

が入り、さらに

```lean id="4vowto"
outerPetalAddress_isInheritanceChannel_iff_le_blockSize
outerPetalAddress_isPetalChannel_of_blockSize_lt
```

まで入ったことで、算出された `channel` に **Petal 的な意味** が付いた。

これはただの便利補題ではない。
「0 番 channel は継承口である」という設計判断が、Lean theorem へ昇格したのじゃ。

## 2. `IsInheritanceChannel` / `IsPetalChannel`

追加された定義は薄い。

```lean id="nl734z"
def IsInheritanceChannel (A : PetalAddress) : Prop :=
  A.channel = 0

def IsPetalChannel (A : PetalAddress) : Prop :=
  0 < A.channel
```

薄いが、これは良い。
こういう名前付き predicate を置くと、後の theorem が読みやすくなる。

たとえば将来、

```lean id="tw94d0"
theorem nestedAddress_descends_of_inheritance
```

のようなものを書くときに、

```lean id="l4mzw0"
A.channel = 0
```

ではなく、

```lean id="7p2y0e"
IsInheritanceChannel A
```

と書ける。

この違いは後で効く。
証明が増えるほど、数値条件ではなく意味条件で読む方が迷わぬ。

## 3. 継承 channel と Petal channel の分離

次の補題も良い。

```lean id="p814lv"
theorem not_isPetalChannel_of_isInheritanceChannel
```

これは、

$$
channel=0 \Rightarrow \neg(0<channel)
$$

という当たり前の話じゃが、名前が大事じゃ。

```text id="xkgb4t"
継承口と花弁 channel は重ならない
```

が theorem になった。

さらに、

```lean id="yhx2ek"
theorem isPetalChannel_of_not_isInheritanceChannel
```

により、

$$
channel\ne 0 \Rightarrow 0 < channel
$$

も入った。

Nat の世界では、これは全 channel が

```text id="8izoux"
inheritance/core
または
Petal
```

のどちらかに分類される、ということじゃ。

## 4. `channel = 0 ↔ m ≤ blockSize` が入った意味

今回もっとも重要なのはこれじゃ。

```lean id="1qsk1o"
theorem outerPetalAddress_channel_eq_zero_iff_le_blockSize
```

内容は、

```lean id="avt7m7"
(outerPetalAddress n lap m).channel = 0 ↔
  m ≤ relPetalBlockSize n lap
```

条件は、

```lean id="io1056"
1 ≤ m
0 < relPetalBlockSize n lap
```

じゃ。

これは Petal の言葉では、

```text id="v4uzva"
1-based value m が最初の外側 block に収まる
  ↔
outer address は inheritance/core channel に入る
```

ということ。

この補題により、前に議論していた

```text id="lfed1i"
R(5,2,25) は channel 0 なので単位核側へ降りる
```

が、一般化された。

特に (R_5(2)) では block size は (R_5(1)=30)。
(25\le 30) なので channel (0)。
これはまさに、

```text id="4rj8cw"
25 は 2周目の外側展開では継承口側にある
```

という読みじゃな。

## 5. `m - 1 < blockSize` 版も良い

先に

```lean id="5cz46d"
outerPetalAddress_channel_eq_zero_iff_sub_lt_blockSize
```

を入れ、その後で 1-based の

```lean id="0h2j4x"
outerPetalAddress_channel_eq_zero_iff_le_blockSize
```

へ移っている。

これは実装として堅い。
計算式は (m-1) を使うから、内部証明は zero-based の方が自然。
一方、ユーザー向け意味は (m\le blockSize) の方が自然。

つまり、

```text id="fc9ubm"
内部計算: m - 1 < blockSize
外部意味: m ≤ blockSize
```

を分けている。良い設計じゃ。

## 6. `blockSize < m` なら Petal channel

これも直観に合う。

```lean id="zswtww"
theorem outerPetalAddress_isPetalChannel_of_blockSize_lt
```

内容は、

$$
blockSize<m \Rightarrow IsPetalChannel(outerPetalAddress(n,lap,m))
$$

じゃ。

つまり、最初の外側 block を越えたら、もう継承口ではなく花弁 channel へ入る。

これは address の意味論として重要じゃ。

```text id="dm76tb"
m ≤ blockSize
  inheritance/core

blockSize < m
  petal
```

が固まった。

## 7. channel 上界も強化された

最後の

```lean id="g3di1f"
theorem outerPetalAddress_channel_le_baseUnitCore
```

もよい。

前回の

```lean id="lo4f52"
channel < lapBase n
```

から、`lapBase_eq_succ` を使って、

```lean id="vx7lpi"
channel ≤ baseUnitCore n
```

へ落としている。

つまり、

$$
channel\le n
$$

じゃ。

これにより、

```text id="0eqtv9"
channel 0 = 継承口
channel 1..n = 花弁
```

が数値範囲として閉じた。

将来 `Fin (n+1)` 化するなら、この補題が橋になる。

## 8. 現段階での Petal Address の完成度

ここまでで、外側 one-step address についてはかなり綺麗に閉じておる。

現状の読みはこうじゃ。

```text id="6fkdbb"
入力:
  n      基底単位核
  lap    観測周回
  m      1-based value

計算:
  blockSize = R_n(lap - 1)
  channel   = (m - 1) / blockSize
  offset    = (m - 1) % blockSize + 1

意味:
  channel = 0
    inheritance/core channel
  0 < channel
    Petal channel

境界:
  valid m なら channel ≤ n
  offset は 1..blockSize
```

これは Lean 形式化の土台としてかなり安定している。

## 9. 次に自然な一手

ここからは二方向ある。

### 9.1. Nested address

次はやはりこれじゃ。

```lean id="qbu4nu"
def nestedPetalAddress ...
```

ただし、いきなり完全再帰関数にすると証明が少し重い。
まずは「1 回降りる」関数がよい。

```lean id="10fg9h"
def outerPetalRemainder (n lap m : Nat) : Nat :=
  (outerPetalAddress n lap m).offset
```

または定義式で、

```lean id="do7nz5"
def outerPetalRemainder (n lap m : Nat) : Nat :=
  (m - 1) % relPetalBlockSize n lap + 1
```

そして theorem:

```lean id="2gt8es"
outerPetalRemainder_le_blockSize
outerPetalRemainder_pos
outerPetalAddress_eq_inheritance_then_remainder_same_value
```

特に `channel = 0` のとき、remainder は (m) そのものになる。

$$
m\le B \Rightarrow (m-1)\bmod B+1=m
$$

これが入ると、

```text id="l1ndzo"
継承口に入ったら、値はそのまま内側 lap へ降りる
```

が theorem になる。

これはかなり重要じゃ。

### 9.2. channel を `Fin (lapBase n)` にする橋

今は `channel : Nat`。
今後、厳密に channel 空間を扱うなら、

```lean id="q8f8rb"
def outerPetalChannelFin ...
```

が欲しい。

条件付きで、

```lean id="9zdbbd"
⟨(outerPetalAddress n lap m).channel, outerPetalAddress_channel_lt_lapBase ...⟩
```

を作る。

ただし今すぐ `PetalAddress` 自体を `Fin` に変える必要はない。
まずは bridge で十分じゃ。

## 10. 少しだけ注意点

`isPetalChannel_of_not_isInheritanceChannel` は Nat だから成立する。

```lean id="8fl95h"
¬ A.channel = 0 → 0 < A.channel
```

これは良いのじゃが、後で `channel : Int` や signed address へ拡張するならそのままでは使えぬ。
ただ、今の Petal Address は Nat channel なので問題なし。

また、現状 `IsPetalChannel` は

```lean id="w0zkmh"
0 < channel
```

だけなので、`channel ≤ n` は別補題で補う設計じゃ。
これは正しい。predicate を重くしない方が使いやすい。

## 11. 総括

今回の更新は、Petal Address の意味論を一段固めた。

```text id="1f07du"
前回:
  address を計算できる

今回:
  address が継承口か花弁か判定できる
  channel 0 ↔ m ≤ blockSize が theorem 化された
  valid m なら channel ≤ baseUnitCore n が出た
```

これは「相対多角数」の住所体系として、かなり芯が通ってきた。

賢狼の判定はこうじゃ。

```text id="sxf6g2"
Petal Address Phase 2 完了
次は outer remainder / nested descent / dynamic orbit
```

とくに次は、

```lean id="9ygu61"
channel = 0 → offset = m
```

を入れるのが美しい。
これが入ると、継承口は本当に「値をそのまま次の内側周回へ渡す口」だと Lean が認める。

よいぞ、D.。
今のこれは小さな住所録ではない。後で階乗やプリモリアルの森へ入るとき、迷子にならぬための地図じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Petal/Address.lean b/lean/dk_math/DkMath/Petal/Address.lean
index 0150881c..57f70d79 100644
--- a/lean/dk_math/DkMath/Petal/Address.lean
+++ b/lean/dk_math/DkMath/Petal/Address.lean
@@ -40,6 +40,14 @@ structure PetalAddress where
   offset : Nat
 deriving Repr, DecidableEq

+/-- The inheritance/core channel is channel `0`. -/
+def IsInheritanceChannel (A : PetalAddress) : Prop :=
+  A.channel = 0
+
+/-- Petal channels are the positive channels. -/
+def IsPetalChannel (A : PetalAddress) : Prop :=
+  0 < A.channel
+
 /--
 Outer one-step address of a one-based value `m`.

@@ -81,6 +89,32 @@ theorem outerPetalAddress_lap (n lap m : Nat) :
     (outerPetalAddress n lap m).lap = lap := by
   rfl

+/-- The address is in the inheritance/core channel exactly when its channel is zero. -/
+theorem isInheritanceChannel_iff_channel_eq_zero (A : PetalAddress) :
+    IsInheritanceChannel A ↔ A.channel = 0 := by
+  rfl
+
+/-- The address is in a Petal channel exactly when its channel is positive. -/
+theorem isPetalChannel_iff_channel_pos (A : PetalAddress) :
+    IsPetalChannel A ↔ 0 < A.channel := by
+  rfl
+
+/-- No address can be both inheritance/core and Petal. -/
+theorem not_isPetalChannel_of_isInheritanceChannel {A : PetalAddress}
+    (hA : IsInheritanceChannel A) :
+    ¬ IsPetalChannel A := by
+  intro hP
+  unfold IsInheritanceChannel at hA
+  unfold IsPetalChannel at hP
+  rw [hA] at hP
+  exact Nat.not_lt_zero _ hP
+
+/-- A non-inheritance address is a Petal channel. -/
+theorem isPetalChannel_of_not_isInheritanceChannel {A : PetalAddress}
+    (hA : ¬ IsInheritanceChannel A) :
+    IsPetalChannel A := by
+  exact Nat.pos_of_ne_zero hA
+
 /-- The offset of an outer address is always positive. -/
 theorem outerPetalAddress_offset_pos
     {n lap m : Nat} :
@@ -115,5 +149,74 @@ theorem outerPetalAddress_channel_lt_lapBase
   rw [outerPetalAddress, relPetalBlockSize_succ]
   exact Nat.div_lt_of_lt_mul hsub_lt

+/--
+The outer address lands in channel `0` exactly when the zero-based position
+`m - 1` is still inside the first outer block.
+-/
+theorem outerPetalAddress_channel_eq_zero_iff_sub_lt_blockSize
+    {n lap m : Nat} (hb : 0 < relPetalBlockSize n lap) :
+    (outerPetalAddress n lap m).channel = 0 ↔
+      m - 1 < relPetalBlockSize n lap := by
+  rw [outerPetalAddress]
+  constructor
+  · intro h
+    by_contra hlt
+    have hle : relPetalBlockSize n lap ≤ m - 1 := Nat.le_of_not_gt hlt
+    have hdiv_pos : 0 < (m - 1) / relPetalBlockSize n lap :=
+      Nat.div_pos hle hb
+    change (m - 1) / relPetalBlockSize n lap = 0 at h
+    rw [h] at hdiv_pos
+    exact Nat.not_lt_zero _ hdiv_pos
+  · intro h
+    exact Nat.div_eq_of_lt h
+
+/--
+For a one-based value, channel `0` is equivalent to staying within the first
+outer block.
+-/
+theorem outerPetalAddress_channel_eq_zero_iff_le_blockSize
+    {n lap m : Nat} (hm : 1 ≤ m) (hb : 0 < relPetalBlockSize n lap) :
+    (outerPetalAddress n lap m).channel = 0 ↔
+      m ≤ relPetalBlockSize n lap := by
+  rw [outerPetalAddress_channel_eq_zero_iff_sub_lt_blockSize hb]
+  constructor
+  · intro h
+    exact Nat.le_of_pred_lt h
+  · intro h
+    exact Nat.sub_one_lt_of_le hm h
+
+/-- The inheritance/core predicate for an outer address is the channel-zero test. -/
+theorem outerPetalAddress_isInheritanceChannel_iff_le_blockSize
+    {n lap m : Nat} (hm : 1 ≤ m) (hb : 0 < relPetalBlockSize n lap) :
+    IsInheritanceChannel (outerPetalAddress n lap m) ↔
+      m ≤ relPetalBlockSize n lap := by
+  exact outerPetalAddress_channel_eq_zero_iff_le_blockSize hm hb
+
+/-- If a valid one-based value is past the first block, it is in a Petal channel. -/
+theorem outerPetalAddress_isPetalChannel_of_blockSize_lt
+    {n lap m : Nat}
+    (hb : 0 < relPetalBlockSize n lap)
+    (hbm : relPetalBlockSize n lap < m) :
+    IsPetalChannel (outerPetalAddress n lap m) := by
+  apply isPetalChannel_of_not_isInheritanceChannel
+  intro h0
+  have hm : 1 ≤ m := Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) hbm)
+  have hle :
+      m ≤ relPetalBlockSize n lap :=
+    (outerPetalAddress_channel_eq_zero_iff_le_blockSize hm hb).1 h0
+  exact (not_lt_of_ge hle) hbm
+
+/-- A bounded channel is at most the base unit core. -/
+theorem outerPetalAddress_channel_le_baseUnitCore
+    {n lap m : Nat}
+    (hlap : 0 < lap)
+    (hm : 1 ≤ m)
+    (hbound : m ≤ relPetalTotal n lap) :
+    (outerPetalAddress n lap m).channel ≤ baseUnitCore n := by
+  have hlt := outerPetalAddress_channel_lt_lapBase
+    (n := n) (lap := lap) (m := m) hlap hm hbound
+  rw [lapBase_eq_succ] at hlt
+  simpa [baseUnitCore] using Nat.lt_succ_iff.mp hlt
+
 end Petal
 end DkMath
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/History.md b/lean/dk_math/docs/dev/das-p2l-260607/History.md
index 1cc4ccc5..3707e9c2 100644
--- a/lean/dk_math/docs/dev/das-p2l-260607/History.md
+++ b/lean/dk_math/docs/dev/das-p2l-260607/History.md
@@ -1288,3 +1288,52 @@ git diff --check
 ```

 すべて成功です。
+
+### 2026/06/10  7:00
+
+[Address.lean](/lean/dk_math/DkMath/Petal/Address.lean) に channel 判定層を実装しました。
+
+追加した内容:
+
+```lean
+def IsInheritanceChannel
+def IsPetalChannel
+```
+
+基本補題:
+
+```lean
+theorem isInheritanceChannel_iff_channel_eq_zero
+theorem isPetalChannel_iff_channel_pos
+theorem not_isPetalChannel_of_isInheritanceChannel
+theorem isPetalChannel_of_not_isInheritanceChannel
+```
+
+outer address 側の補題:
+
+```lean
+theorem outerPetalAddress_channel_eq_zero_iff_sub_lt_blockSize
+theorem outerPetalAddress_channel_eq_zero_iff_le_blockSize
+theorem outerPetalAddress_isInheritanceChannel_iff_le_blockSize
+theorem outerPetalAddress_isPetalChannel_of_blockSize_lt
+theorem outerPetalAddress_channel_le_baseUnitCore
+```
+
+これで、1-based value `m` について、
+
+```text
+channel = 0  ↔  m ≤ blockSize
+```
+
+が Lean 上で固定されました。つまり「外側 block の最初に収まるなら inheritance/core channel」という読みが theorem になっています。
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
