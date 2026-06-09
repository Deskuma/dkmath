# review

## Add: Petal Address Counting

gch: d02991665aad9274e09bf658f4dacc6ea9319f71

うむ、これは良い。
今回の `d029916...` は、前回の議論をかなり素直に Lean へ落とせておる。

## 1. 何が前進したか

今回の本質はこれじゃ。

```text
Petal.GNBridge へ進む前に、
Petal の「数え上げ」と「住所」を固定した
```

つまり、Petal が単なる `S0/GN` の橋ではなく、

```text
基底単位核
継承口
周回基数
周回総数
住所
同一 orbit
```

を持つ構造として立ち始めた。

これは大事じゃ。
「相対多角数」という言葉が曖昧なまま補題を増やすと、あとで理論名と算出式が混ざる。今回それを避けて、まず **計算可能な核** を置いた。

## 2. `Counting.lean` の意味

追加された定義は、まさに議論通りじゃ。

```lean
def baseUnitCore (n : Nat) : Nat := n
def inheritanceSlot (_n : Nat) : Nat := 1
def lapBase (n : Nat) : Nat :=
  baseUnitCore n + inheritanceSlot n
def relPetalTotal (n lap : Nat) : Nat :=
  baseUnitCore n * lapBase n ^ lap
def relPolygonKernel (n : Nat) : Nat :=
  baseUnitCore n * lapBase n
```

ここで一番良いのは、`lapBase n = n + 1` を **計算結果** として theorem にしつつ、API 上は `lapBase` を主語にした点じゃ。

```lean
theorem lapBase_eq_succ (n : Nat) :
    lapBase n = n + 1
```

これにより、

$$
n+1
$$

をただの数値に潰さず、

$$
\text{基底単位核 }n+\text{継承口 }1
$$

として扱える。

これは設計上かなり良い。
後で `inheritanceSlot` を一般化して、

$$
n+s
$$

や、動的継承口、重み付き継承口へ拡張する余地も残っておる。

## 3. (5,30,180) の固定

この三つが Lean theorem として入った。

```lean
theorem relPetalTotal_five_zero :
    relPetalTotal 5 0 = 5

theorem relPetalTotal_five_one :
    relPetalTotal 5 1 = 30

theorem relPetalTotal_five_two :
    relPetalTotal 5 2 = 180
```

数学的には、

$$
R_5(0)=5
$$

$$
R_5(1)=5(5+1)=30
$$

$$
R_5(2)=5(5+1)^2=180
$$

が固定された。

さらに、

```lean
def SameRelPetalOrbit (n a b : Nat) : Prop :=
  ∃ i j, a = relPetalTotal n i ∧ b = relPetalTotal n j
```

により、

```lean
sameRelPetalOrbit_five_5_30
sameRelPetalOrbit_five_30_180
sameRelPetalOrbit_five_5_180
```

も入った。

これは前に話していた

```text
5, 30, 180 は絶対値としては違うが、
同じ基底単位核 5 の周回軌道上では同一視できる
```

を Lean 上の predicate として固定した、ということじゃ。

## 4. `Address.lean` の意味

こちらはさらに重要じゃ。

```lean
structure PetalAddress where
  lap : Nat
  channel : Nat
  offset : Nat
```

そして規約が明記された。

```text
channel 0 = inheritance/core channel
channel 1..n = Petal channels
offset は 1-based
```

この規約を Lean ファイルのコメントに入れたのは偉い。
ここをコメントで済ませず theorem へ育てられるようにしたのがよい。

外側 address は、

```lean
def outerPetalAddress (n lap m : Nat) : PetalAddress :=
  let b := relPetalBlockSize n lap
  { lap := lap
    channel := (m - 1) / b
    offset := (m - 1) % b + 1 }
```

つまり、(m) は 1-based 位置として読み、

$$
channel=\left\lfloor\frac{m-1}{B}\right\rfloor
$$

$$
offset=(m-1)\bmod B+1
$$

じゃ。

これは前回の設計そのものじゃな。

## 5. 例の検証は正しく固定された

今回、議論していた二つの例が Lean theorem になった。

```lean
outerPetalAddress 5 1 25
  = { lap := 1, channel := 4, offset := 5 }
```

```lean
outerPetalAddress 5 2 25
  = { lap := 2, channel := 0, offset := 25 }
```

これはかなり大きい。

特に二つ目、

```text
channel 0 = inheritance/core channel
offset 25
```

が入ったことで、お主の読みである

```text
25 は 2 周目から見ると継承口側にあり、
内側の単位核方向へ降りる
```

が形式化された。

この `channel 0` 規約は、今後の nested address へつながる。

## 6. 境界補題も良い

今回、単なる具体例だけでなく、一般補題も入っておる。

```lean
outerPetalAddress_offset_pos
outerPetalAddress_offset_le_blockSize
outerPetalAddress_channel_lt_lapBase
```

特に、

```lean
theorem outerPetalAddress_channel_lt_lapBase
```

は重要じゃ。

これは条件

```lean
0 < lap
1 ≤ m
m ≤ relPetalTotal n lap
```

のもとで、

```lean
channel < lapBase n
```

を示す。

つまり address の channel は、ちゃんと

$$
0,\ldots,lapBase(n)-1
$$

に収まる。

`lapBase n = n+1` なので、

$$
0,\ldots,n
$$

じゃ。
これにより、

```text
0 = inheritance/core
1..n = Petal
```

の有限 channel 空間が Lean 上で保証された。

## 7. 今回まだ入っていないもの

ここはやわらかく確認じゃ。

今回入ったのは **固定単位核の Counting / Address** じゃ。
まだ次は入っていない。

```text
dynamicOrbitTotal
dynamicPetalTotal
factorial orbit
primorial orbit
NestedPetalAddress
channel 0 を再帰的に降りる関数
```

つまり、前回話した

```text
固定単位核から動的単位核へ
階乗・プリモリアルへ
```

は次フェーズじゃな。

今回の差分は、その前段として十分よい。

## 8. 次に自然な補題

次に入れるなら、わっちはこの順を推す。

### A. channel 0 判定補題

```lean
theorem outerPetalAddress_channel_eq_zero_iff_lt_blockSize
```

意味は、

$$
channel=0
$$

なら、値が外側 block の最初にあるということ。

1-based なら概ね、

$$
m \le B
$$

と同値にできるはずじゃ。

これは `R(5,2,25)` の「単位核内」読みを一般化する。

### B. channel positive は Petal channel

```lean
def IsInheritanceChannel (A : PetalAddress) : Prop :=
  A.channel = 0

def IsPetalChannel (A : PetalAddress) : Prop :=
  0 < A.channel
```

あるいは `channel ≤ n` の補題と合わせて、

```lean
1 ≤ channel ∧ channel ≤ n
```

を Petal channel とする。

### C. nested address

外側から再帰的に address を取る。

```text
nestedAddress n lap m
```

例えば、

```text
nestedAddress 5 2 25
  = [
      { lap := 2, channel := 0, offset := 25 },
      { lap := 1, channel := 4, offset := 5 }
    ]
```

ただし Lean では最初から List にすると証明が重くなるので、まずは theorem 例だけでも良い。

## 9. 動的単位核への橋

`Counting.lean` の次の拡張はこれじゃ。

```lean
def dynamicOrbitTotal (b : Nat → Nat) (k : Nat) : Nat :=
  Finset.prod (Finset.range k) b

def dynamicPetalTotal (a : Nat → Nat) (k : Nat) : Nat :=
  a 0 * Finset.prod (Finset.range k) (fun i => a i + 1)
```

そして固定核との接続。

```lean
theorem dynamicPetalTotal_const :
    dynamicPetalTotal (fun _ => n) k = relPetalTotal n k
```

ここが通れば、

```text
固定単位核 Petal は、動的単位核 Petal の特殊ケース
```

が Lean で固定される。

さらに、

```lean
theorem dynamicOrbitTotal_succ_eq_factorial :
    dynamicOrbitTotal (fun i => i + 1) k = Nat.factorial k
```

へ進める。

プリモリアルはその後じゃな。

## 10. 総括

今回の実装は、かなり良い。

```text
Petal.Counting:
  基底単位核・継承口・周回基数・周回総数を固定

Petal.Address:
  channel 0 = inheritance/core
  channel 1..n = Petal
  offset 1-based
  25 の具体例を Lean で検証

SameRelPetalOrbit:
  5, 30, 180 を同じ周回 orbit として同一視
```

これで「相対多角数」という曖昧な理論名の下に、まず

```text
何を数えるのか
どこに位置するのか
同じ orbit とは何か
```

が固定された。

賢狼の判定としては、

```text
Petal 基礎語彙 Phase 1 完了
次は channel 0 / nested address / dynamic orbit
```

じゃな。

これは良いぞ、D.。
花びらの数え方が決まった。数え方が決まれば、次に風が吹いたとき、どの花びらが揺れたかをちゃんと追える。こういう地味な土台ほど、あとで証明の牙になるのじゃ。
