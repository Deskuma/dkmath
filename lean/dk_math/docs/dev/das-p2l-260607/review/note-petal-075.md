# Note: No.075

## Collatz 観測窓

コラッツ側で実装していた Collatz Petal 補題より、新しい Petal が見せるものねぇ。
単位核の内外の切り分け、それによって相対伸縮方向が明確になる。
肥大化と縮小化の様子を、アドレスで観測できる。

つまり観測しやすい「窓」を手に入れた。どれだけ巨大になろうが、相対的には窓の枠内。
どこに住まう数か、アドレスで解る。窓の中の１点！その点を追って観測するだけ。

窓枠内で全てが起こるなら、もう統計確率論に話をもっていきやすい。
もしその点の動きが幾何的原理として見えたら、代数幾何解釈も可能！うん。これは行ける！

---

うむ。見えてきた。
これは **Collatz.PetalBridge が「証明の橋」ではなく「観測窓」として機能し始めた** ということじゃ。

前回の実装では、加速 Collatz 軌道 `iterateT i n` の自然数値を `oddOrbitLabel n i` として読み、Petal `RangeFamily` の label separation / collision へ接続した。つまり、Collatz 軌道片を **Petal の range-indexed label 列として見る窓** ができた。

## 1. 新しい Petal が見せるもの

従来の Collatz 補題は、おおむね

```text
n -> T n
s n = v2(3n+1)
iterateT i n
```

のように、軌道を直接追っていた。

しかし新しい Petal 読みでは、軌道をそのまま巨大数として見るのではなく、

```text
どの単位核の内側か
どの単位核の外側か
どの address にいるか
次にどの address へ移るか
```

として見る。

これは大きい。
Collatz の値そのものは巨大化することがある。
だが Petal address に落とすと、

```text
巨大な数そのもの
  -> 窓の中の相対位置
```

として観測できる。

つまり、絶対値ではなく **住所** を追う。

## 2. 単位核の内外という切り分け

Collatz の加速写像は、

```text
3n + 1 で伸びる
2^s で剥がす
odd core に戻る
```

という流れじゃ。

Petal 的には、

```text
3n + 1:
  外側への肥大化

2^s:
  単位核による剥離・縮小化

odd core:
  次の address に再配置された点
```

と読める。

ここで `s = v2(3n+1)` は、単なる割れる 2 の個数ではなく、

```text
どれだけ外側へ伸びたものを
どれだけ単位核側へ吸収したか
```

を示す量になる。

だから相対伸縮方向が見える。

```text
肥大化:
  3n + 1

縮小化:
  / 2^s

観測点:
  oddOrbitLabel n i
```

## 3. アドレスで見る意味

これはまさに「窓」じゃ。

普通に Collatz を見ると、

```text
値が大きくなる
値が小さくなる
また大きくなる
```

と見える。

しかし Petal address で見ると、

```text
同じ窓枠の中で
点がどこへ移動したか
```

として見える。

値がどれだけ巨大でも、address 化すれば、

```text
どの lap
どの channel
どの offset
どの residue
```

のような有限的・相対的な情報に落とせる。

これは統計化しやすい。
なぜなら、観測対象が「巨大整数」ではなく「窓内の点列」になるからじゃ。

## 4. collision の意味が変わる

今回の `Collatz.PetalBridge` で重要なのは、同じ label が出たときの読みじゃ。

Petal/ABC では、

```text
同じ label が出る
  -> 独立 carrier family としては False
```

だった。

Collatz では、

```text
同じ label が出る
  -> 同じ accelerated odd state
  -> merge / fold / cycle candidate
```

になる。

つまり Collatz では、collision は失敗ではない。
むしろ観測対象そのものじゃ。

```text
分離している軌道片:
  まだ窓の中で別々の点として動いている

衝突した軌道片:
  fold, merge, cycle の構造が見えた
```

この二択が Petal の窓で見える。

## 5. 統計確率論へ行きやすくなる理由

「窓枠内で全てが起こる」という見方は強い。

Collatz の実数値や自然数値をそのまま確率論に乗せると、スケールが暴れる。
しかし address に落とすと、

```text
窓の中の点
窓の中の遷移
窓の中の滞在頻度
窓の中の collision 頻度
```

として扱える。

すると、次のような量が定義しやすくなる。

```text
address transition frequency
collision rate
height distribution
v2-height drift
window occupation measure
return probability
fold probability
```

これは DkMath Kernel 的にも自然じゃ。

```text
Collatz transition
  -> address transition
  -> finite/statistical kernel
  -> normalized observation
```

つまり、巨大整数軌道を直接追うのではなく、**窓内遷移の確率過程** として観測できる。

## 6. 代数幾何解釈への道

幾何的原理が見えれば、代数幾何的にも読める可能性が出る。

たとえば、Petal address を

```text
residue class
fiber
orbit point
local chart
```

として扱うなら、Collatz 軌道は

```text
整数直線上の軌道
```

ではなく、

```text
Petal chart 上の写像反復
```

になる。

つまり、

```text
T : address chart -> address chart
```

を見る。

その上で、

```text
固定点
周期点
合流点
特異点
例外 fiber
```

を調べる。

これはかなり代数幾何っぽい読みになる。
特に Collatz の周期候補は、

```text
T^k(P) = P
```

という固定点方程式として見られる。
Petal address 上でこれを見れば、巨大数の周期方程式ではなく、**局所 chart 上の閉路条件** として扱える。

## 7. 次に固定すべき初手定義

次に Lean でやるなら、いきなり確率へ行くより、まずこれを固定するのがよい。

```lean
def collatzPetalAddress (n : OddNat) (i : ℕ) : PetalAddress := ...
```

あるいは、まだ `PetalAddress` へ直接落とせないなら、

```lean
def collatzOrbitWindowLabel (n : OddNat) (i : ℕ) : ℕ :=
  oddOrbitLabel n i
```

を土台にして、

```text
Separated:
  最初の k 点が全部異なる

Collision:
  i != j で同じ点に戻る

Fold:
  collision を持つ orbit segment

Window:
  range k 上の観測枠
```

を定義する。

候補名はこうじゃ。

```lean
def CollatzOrbitWindow (n : OddNat) (k : ℕ) : Finset ℕ :=
  Finset.range k

def CollatzOrbitSeparated (n : OddNat) (k : ℕ) : Prop :=
  OddOrbitLabelsPairwiseSeparated n k

def CollatzOrbitCollision (n : OddNat) (k : ℕ) : Prop :=
  ∃ i j, i < k ∧ j < k ∧ i ≠ j ∧ oddOrbitLabel n i = oddOrbitLabel n j
```

まずはこの二分岐を作るのが良い。

```text
Separated or Collision
```

この case split ができると、トロミノ論法になる。

## 8. 現在の見立て

今見えている構造はこう。

```text
Collatz:
  値の軌道

Petal:
  住所の軌道

RangeFamily:
  有限窓

Obstruction:
  衝突診断

Future probability:
  窓内遷移の統計

Future geometry:
  address chart 上の写像
```

つまり、今回得たのは証明そのものではなく、

```text
巨大軌道を、相対的な窓内点列として見る観測装置
```

じゃ。

これはかなり重要。
観測装置がないと、Collatz はただの暴れる数列に見える。
観測装置があると、そこに **流れ・合流・折り返し・滞在分布** が見える。

## 9. 総括

お主の言葉をそのまま整理すると、こうじゃ。

```text
新しい Petal は、
Collatz 軌道を巨大な自然数列としてではなく、
単位核の内外をまたぐ相対伸縮運動として観測する窓である。

どれだけ値が肥大化しても、
Petal address に落とせば窓枠内の一点として追跡できる。

分離すれば独立軌道片。
衝突すれば fold / merge / cycle の信号。

この窓があることで、
統計確率論にも、
代数幾何的な写像解釈にも進みやすくなる。
```

うむ。
これは行ける。Collatz に対して Petal は、**証明をいきなり与える道具ではなく、軌道を見える形に正規化する観測窓** になる。
