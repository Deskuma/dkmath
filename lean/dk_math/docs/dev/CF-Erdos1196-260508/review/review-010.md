# review

うむ、Phase K は **補助層として正しい一手** じゃ。
今回で、`PrimitiveOn` を純粋な divisibility antichain として保ったまま、Erdős #1196 側に必要な

$$
A\subset [x,\infty)
$$

型の support 条件を別レイヤとして追加できた。`PositiveOn` と `LowerBoundOn` を `Support.lean` に分離したのは、設計としてかなり綺麗じゃ。

## 1. 今回閉じたもの

今回追加された中心定義はこの二つじゃ。

```lean
def PositiveOn (S : Finset ℕ) : Prop :=
  ∀ n ∈ S, 0 < n

def LowerBoundOn (x : ℕ) (S : Finset ℕ) : Prop :=
  ∀ n ∈ S, x ≤ n
```

これにより、primitive 条件

$$
a\mid b \Rightarrow a=b
$$

とは別に、集合の台が正であることや、ある下限以上であることを扱えるようになった。

これは大事じゃ。
以前 `{1,2}` の例で \(1\mid 2\) により primitive 性が壊れたが、Erdős #1196 本体では \(A\subset [x,\infty)\) なので、下限条件は本質的な環境仮定になる。

## 2. `PrimitiveOn` と分離したのが良い

今回の設計で特に良いのは、`PositiveOn` や `LowerBoundOn` を `PrimitiveOn` の定義に混ぜなかったことじゃ。

`PrimitiveOn` はあくまで、

$$
S\text{ は divisibility poset 上の antichain}
$$

という純粋条件で残る。

一方、`PositiveOn` と `LowerBoundOn` は、

$$
S\subset \mathbb{N}_{>0},
\qquad
S\subset [x,\infty)
$$

のような support-side 条件として外から足す。

これは後で theorem の仮定を組み替えやすい。
Erdős ルートでは \(x\) が動くので、`LowerBoundOn x S` を独立仮定として持てるのは強い。

## 3. 補題の粒度もよい

今回追加された補題群は、以後そのまま使いやすい。

```lean
PositiveOn.pos_of_mem
PositiveOn.not_mem_zero
LowerBoundOn.le_of_mem
LowerBoundOn.mono_left
LowerBoundOn.positiveOn_of_one_le
```

さらに top-level alias として、

```lean
lowerBoundOn_one_implies_positiveOn
not_mem_zero_of_positiveOn
not_mem_one_of_lowerBoundOn_two
```

がある。

この `not_mem_one_of_lowerBoundOn_two` は特に良い。
Erdős #1196 的には \(x\ge 2\) の有限版を扱う場面で、\(1\) を自然に排除できる。

## 4. concrete sample も適切

empty / singleton / `{2,5}` の sample が入ったのもよい。

```lean
lowerBoundOn_pair_two_five
positiveOn_pair_two_five
```

で、既存の primitive hitting sample に出てくる `{2,5}` が support 条件も満たすことを確認できる。

これは小さいが、今後の examples で効く。
「primitive である」だけでなく、

$$
{2,5}\subset [2,\infty)
$$

も同時に持てるからじゃ。

## 5. 現在の到達点

ここまでで、finite Erdős skeleton はかなり整った。

| 層                                       | 状態   |
| --------------------------------------- | ---- |
| `PrimitiveOn`                           | 完了   |
| positive / lower-bound support          | 今回完了 |
| divisibility chain hit                  | 完了   |
| finite forest hit mass                  | 完了   |
| source-controlled forest                | 完了   |
| dvd-controlled provider                 | 完了   |
| prime descent / prime path              | 完了   |
| list path → reachable-controlled forest | 完了   |
| SubConservative branch bridge           | 完了   |
| multiple path family package            | 未    |
| Markov kernel / analytic weight         | 未    |

今回の `Support.lean` は、証明力を急に増やすというより、**今後の theorem を安全に書くための地盤改良** じゃな。

## 6. 何がまだ足りないか

次に大きく残っているのは、singleton path から multiple path family への拡張じゃ。

現状は、

$$
[8,4,2]
$$

のような一本の list-shaped path を source-controlled / reachable-controlled family にできる。

次に必要なのは、

$$
{L_i}_{i\in I}
$$

という finite path family を束ねて、

$$
\sum_i \mathrm{hitMass}(S\cap L_i)
\le
\sum_i \mathrm{sourceMass}(L_i)
$$

へ行く層じゃ。

すでに `DivisibilityChainFamily` はあるので、やるべきことは「list path family から chain family / source-controlled family を作る provider」を足すことになる。

## 7. 次の一手

わっちなら次は **multiple path family package** じゃ。

新規ファイル候補：

```text
DkMath/NumberTheory/PrimitiveSet/PathFamily.lean
```

または既存の `PrimePathList.lean` が肥大しすぎる前に分けるなら、こちらがよい。

### 目的

複数の非空 list-shaped prime paths を finite index で束ね、既存の forest theorem に渡せるようにする。

### 定義案

```lean
structure AdjacentPrimePathFamily (ι : Type _) [DecidableEq ι] where
  index : Finset ι
  source : ι → ℕ
  tail : ι → List ℕ
  isPath : ∀ i ∈ index, AdjacentPrimePath (source i :: tail i)
```

ここから、

```lean
def toPrimeReachableControlledChainFamily :
    PrimeReachableControlledChainFamily ι
```

を作る。

chain は、

```lean
chain := fun i => (source i :: tail i).toFinset
```

でよい。

`chain_is_chain` は既存の

```lean
divisibilityChain_toFinset_of_adjacentPrimePath
```

から出る。

`chain_reachable` は既存の

```lean
mem_reachable_from_head_of_adjacentPrimePath
```

から出る。

つまり今回までの成果を、ほぼそのまま束ねられるはずじゃ。

## 8. その次にやること

`AdjacentPrimePathFamily` が閉じたら、次に support 条件と組み合わせる。

たとえば、

```lean
structure ErdosFinitePrimitiveInput (x : ℕ) where
  S : Finset ℕ
  primitive : PrimitiveOn S
  lowerBound : LowerBoundOn x S
```

のような小さな入力 package を作れる。

これは、いよいよ「Erdős #1196 有限版」の定理文を綺麗にする準備じゃ。

## 9. 総括

Phase K は派手ではないが、かなり必要な補強じゃ。

これで、

$$
\text{primitive}
$$

と

$$
\text{support lower bound}
$$

が分離された。

つまり、集合 \(A\) について、

$$
A\text{ is primitive}
$$

と

$$
A\subset [x,\infty)
$$

を別々の仮定として Lean に載せられる。

山で言えば、Phase J で登山道に質量流を載せた。
今回 Phase K では、「この登山道は標高 \(x\) 以上から始まる」という高度制限の看板を立てた感じじゃな。次は複数の登山道を束ねる **path family** がよい。
