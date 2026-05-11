# review

うむ、Phase H は **かなり良い実装** じゃ。
今回で、抽象的な `PrimeReachable` だけでなく、実際に並んだ list-shaped path

$$
n_0 \to n_1 \to \cdots \to n_k
$$

から、そのノード集合が `DivisibilityChain` になることまで閉じた。これは有限 Erdős skeleton の「実際の下降路」側をかなり強くした進展じゃ。

## 1. 今回閉じた核心

今回の中心はこれじゃ。

```lean
def AdjacentPrimePath (L : List ℕ) : Prop :=
  List.IsChain PrimeDescentStep L
```

つまり、リスト上で隣接する項がすべて `PrimeDescentStep` で繋がる、という実際の prime descent path を定義した。

さらに、

```lean
def PairwiseDvdAlongList (L : List ℕ) : Prop :=
  ∀ ⦃a b : ℕ⦄, a ∈ L → b ∈ L → a ∣ b ∨ b ∣ a
```

を置いて、リスト内の任意二点が割り切り比較可能であることを表現した。

ここから最終的に、

```lean
theorem divisibilityChain_toFinset_of_adjacentPrimePath
    {L : List ℕ} (hL : AdjacentPrimePath L) :
    DivisibilityChain L.toFinset
```

まで出しておる。

これはまさに、

$$
\text{prime descent path}
\Rightarrow
\text{divisibility chain}
$$

じゃ。

## 2. 数学的に何が嬉しいか

Erdős #1196 の有限骨格で必要だったのは、

$$
\text{primitive set は一本の下降鎖に高々一度しか当たらない}
$$

という構造じゃった。

これまでは `DivisibilityChain` を **仮定** として渡していた。
今回からは、実際の path

$$
8\to 4\to 2
$$

のようなリストを作れば、その node set が自動的に `DivisibilityChain` になる。つまり、

$$
\text{実際に素数で割って下った列}
\Rightarrow
\text{primitive hitting lemma の入力}
$$

へつながったわけじゃ。

これは、抽象 chain から concrete descent path への橋じゃな。

## 3. 証明の山場

今回の証明で効いているのは、

```lean
mem_tail_dvd_head_of_isChain_dvd
```

じゃ。

これは divisibility descent list

$$
x :: xs
$$

において、tail の任意要素 \(y\) が head \(x\) を割ることを示している。

数学的には、

$$
x_0 \leftarrow x_1 \leftarrow x_2 \leftarrow \cdots
$$

で各段に

$$
x_{j+1}\mid x_j
$$

があるなら、後ろの任意要素は前の要素を割る、ということじゃ。

そこから、

```lean
pairwiseDvdAlongList_of_isChain_dvd
```

で任意二点の比較可能性を出し、さらに `toFinset` へ落として `DivisibilityChain` にしている。

証明の形としても自然じゃ。
`List` の membership 周りで少し苦労した記録も残っているが、そこは Lean らしい細部じゃな。

## 4. サンプルの意味

サンプルは、

$$
8\to 4\to 2
$$

じゃ。

```lean
theorem adjacentPrimePath_eight_four_two :
    AdjacentPrimePath [8, 4, 2]
```

さらに、

```lean
theorem divisibilityChain_eight_four_two_toFinset :
    DivisibilityChain ([8, 4, 2] : List ℕ).toFinset
```

そして primitive set `{2,5}` がこの path を高々一度しか hit しないことまで確認している。

これは教材としてよい。

$$
{2,5}\cap{8,4,2}={2}
$$

であり、たしかに hit は一回。
そして `{2,5}` は primitive。ここで `{1,2}` のような集合を避けているのも、前回の反省が効いておる。

## 5. 今の全体地図

ここまでの有限 skeleton は、かなり形になった。

$$
\text{AdjacentPrimePath}
\Rightarrow
\text{DivisibilityChain}
\Rightarrow
\text{primitive hit at most once}
$$

さらに既存層と合わせると、

$$
\text{PrimeReachable}
\Rightarrow
\text{DvdControlled}
\Rightarrow
\text{SourceControlled}
\Rightarrow
\text{hit mass bound}
$$

もある。

現状の地図はこうじゃ。

| 層                                          | 状態   |
| ------------------------------------------ | ---- |
| finite primitive set                       | 完了   |
| divisibility chain hit                     | 完了   |
| forest hit mass                            | 完了   |
| source-controlled forest                   | 完了   |
| dvd-controlled provider                    | 完了   |
| one-step prime descent                     | 完了   |
| multi-step prime reachable                 | 完了   |
| list-shaped prime path → chain             | 今回完了 |
| list path → controlled forest / mass bound | 未    |
| Branching/SubConservative 接続               | 未    |
| Markov kernel                              | 未    |

今回で、**chain 条件の生成** が閉じた。
これは大きい。

## 6. まだ足りない接続

History の次課題にもある通り、次に足りないのは、

$$
\text{list-shaped path}
\Rightarrow
\text{PrimeReachableControlledChainFamily}
$$

または

$$
\text{list-shaped path}
\Rightarrow
\text{DvdControlledChainFamily}
$$

への接続じゃ。

いま `singletonChainFamilyOfAdjacentPrimePath` は `DivisibilityChainFamily` まで作っている。

```lean
def singletonChainFamilyOfAdjacentPrimePath
    (L : List ℕ) (hL : AdjacentPrimePath L) :
    DivisibilityChainFamily Unit
```

これは良い第一歩じゃ。

しかし、まだ source がない。
mass bound に進むには source と control が必要じゃ。

つまり次は、

```lean
singletonPrimeReachableControlledChainFamilyOfAdjacentPrimePath
```

または

```lean
singletonDvdControlledChainFamilyOfAdjacentPrimePath
```

が欲しい。

## 7. 次の一手

わっちなら次は **list path から source-controlled / reachable-controlled forest へ接続** じゃ。

新規ファイルを切らず、まず `PrimePathList.lean` の末尾に追加でよい。

### 7.1. 方針

非空リスト

$$
L = source :: tail
$$

に対して、`L.toFinset` を chain とし、source を `source` にする singleton family を作る。

ただし空リストだと source がない。
よって structure を使うのが安全じゃ。

```lean
structure NonemptyAdjacentPrimePath where
  source : ℕ
  tail : List ℕ
  isPath : AdjacentPrimePath (source :: tail)
```

または theorem を `source` と `tail` に分けて書く。

### 7.2. 目標定義

```lean
def singletonPrimeReachableControlledChainFamilyOfAdjacentPrimePath
    (source : ℕ) (tail : List ℕ)
    (hL : AdjacentPrimePath (source :: tail)) :
    PrimeReachableControlledChainFamily Unit
```

ここで、

```lean
index := {()}
chain := fun _ => (source :: tail).toFinset
source := fun _ => source
```

にする。

必要になる補題は、

$$
h\in (source::tail)
\Rightarrow
\text{PrimeReachable source h}
$$

じゃ。

これは list-shaped path から各 node が source から reachable であることを示す補題として切り出すとよい。

```lean
theorem mem_reachable_from_head_of_adjacentPrimePath
    {source h : ℕ} {tail : List ℕ}
    (hL : AdjacentPrimePath (source :: tail))
    (hh : h ∈ source :: tail) :
    PrimeReachable source h
```

この補題が次の山場じゃな。

## 8. なぜこれが重要か

これが閉じると、

$$
\text{実際の path list}
\Rightarrow
\text{reachable-controlled singleton forest}
\Rightarrow
\text{primitive hit mass bound}
$$

まで一直線になる。

つまり、`AdjacentPrimePath [8,4,2]` から、単に `DivisibilityChain` を作るだけでなく、

$$
\mu({2,5}\cap{8,4,2})
\le
\mu(8)
$$

のような mass bound へ行ける。

これで finite path skeleton はかなり完成に近づく。

## 9. その次

この path-to-controlled-forest が閉じたら、次こそ `Branching/SubConservative` 接続へ進んでよい。

なぜなら、その時点で有限側は、

* path
* chain
* reachable
* controlled forest
* primitive hit mass bound

まで揃うからじゃ。

その後に `Branching` を使って、

$$
\sum_{\text{children}}\mu(child)\le\mu(parent)
$$

から path mass control を供給する形へ進む。

## 10. 総括

Phase H は、有限 Erdős skeleton の **具体路線化** じゃ。

前段では、

$$
\text{PrimeReachable}
$$

という到達可能性を抽象的に持っていた。
今回は、

$$
[8,4,2]
$$

のような実際の下降 path list から `DivisibilityChain` を生成した。

これで、primitive set が実際の prime descent path に高々一度しか当たらない、という形が見えるようになった。

山で言えば、地図上の「到達可能領域」だけでなく、実際に歩いた登山道の列が Lean に刻まれた。
次は、その登山道に「出発点 source」と「質量 bound」を載せる番じゃな。
