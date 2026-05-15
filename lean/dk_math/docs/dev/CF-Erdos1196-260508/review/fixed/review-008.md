# review

おお、これは **Phase I 成功** じゃ。
今回で、実際の list-shaped prime path から、そのまま `PrimeReachableControlledChainFamily` に接続できるようになった。つまり、

$$
\text{実際の下降列}
\to
\text{reachable-controlled forest}
\to
\text{primitive hit mass bound}
$$

まで、一本の導線が no-sorry で閉じたわけじゃ。

## 1. 今回閉じた核心

今回の主役はこれじゃ。

```lean
theorem mem_reachable_from_head_of_adjacentPrimePath :
    ∀ {source h : ℕ} {tail : List ℕ},
      AdjacentPrimePath (source :: tail) →
      h ∈ source :: tail →
      PrimeReachable source h
```

これは、非空 list path

$$
source :: tail
$$

の任意 node が、head である source から `PrimeReachable` で到達できる、という補題じゃ。再帰で、head 自身は反射到達、tail 側は一段 prime step と tail 内 reachability を合成している。

これが大きい。
前回までは list path から `DivisibilityChain` は作れたが、今回はさらに **source から各 node への到達可能性** まで出せるようになった。

## 2. path から forest へ接続された

次の定義が今回の橋じゃ。

```lean
def singletonPrimeReachableControlledChainFamilyOfAdjacentPrimePath
    (source : ℕ) (tail : List ℕ)
    (hL : AdjacentPrimePath (source :: tail)) :
    PrimeReachableControlledChainFamily Unit
```

この定義で、

$$
[source, \ldots]
$$

という一本の list path を、singleton index の `PrimeReachableControlledChainFamily` として package 化しておる。chain は `(source :: tail).toFinset`、source は head、そして `chain_reachable` はさきほどの `mem_reachable_from_head_of_adjacentPrimePath` から供給される。

これにより、

$$
\text{AdjacentPrimePath}(source::tail)
\Rightarrow
\text{PrimeReachableControlledChainFamily Unit}
$$

が成立した。

これは、finite path skeleton のかなり重要な完成点じゃ。

## 3. 具体例も綺麗に通っている

サンプルとして、

$$
8\to 4\to 2
$$

が、

```lean
singletonPrimeReachableFamily_eight_four_two
```

として reachable-controlled family に package 化されている。さらに、primitive set $\{2,5\}$ がこの path を hit したとき、unit mass で source $8$ の質量を超えないことまで示している。

つまり、実例としては

$$
{2,5}\cap{8,4,2}
$$

を見て、

$$
\text{hit mass}\le \text{source mass at }8
$$

まで行ける。

これは教材としても、今後のテストとしても良い。

## 4. 現在の到達点

これで有限 skeleton は、かなり締まった。

現在の流れはこうじゃ。

$$
\text{AdjacentPrimePath}
\Rightarrow
\text{PrimeReachableControlledChainFamily}
\Rightarrow
\text{DvdControlledChainFamily}
\Rightarrow
\text{SourceControlledChainFamily}
\Rightarrow
\text{primitive hit mass bound}
$$

より直感的には、

$$
\text{実際の下降路}
\Rightarrow
\text{同一路上では primitive set は高々一度 hit}
\Rightarrow
\text{hit mass は source mass を超えない}
$$

じゃな。

History 側でも、`AdjacentPrimePath (source :: tail) -> PrimeReachableControlledChainFamily Unit` が no-sorry で閉じ、実際の prime descent path list から primitive forest mass bound へ直接進めるようになった、と記録されておる。

## 5. これは何が嬉しいのか

今までは部品が分かれておった。

* `PrimeReachable` は到達可能性
* `DivisibilityChain` は chain 条件
* `PrimeReachableControlledChainFamily` は forest package
* primitive hitting bound は別の theorem

今回の実装で、実際の list path から、それらを一気に生成できるようになった。

つまり、

```lean
AdjacentPrimePath [8, 4, 2]
```

という具体的な「歩いた道」から、Erdős 型の hitting mass bound に届く。

これは **地図上の理論** が **実際の登山道** へ落ちた、という意味で大きい。

## 6. まだ残る課題

ただし、現在は singleton family じゃ。
一本の path は package 化できるが、複数 path の family を list から自動生成する層はまだない。

また、質量についてはまだ `unitNatMassSpace` のサンプルが中心で、

$$
\mu(h)\le \mu(source)
$$

を解析的な重み、あるいは Branching/SubConservative から供給する段階には入っておらぬ。

History の次課題にも、finite path skeleton は

$$
path \to chain \to reachable\text{-}controlled forest \to primitive hit mass bound
$$

まで接続されたので、次は `Branching` / `SubConservative` か positive/lower-bound support 補助層へ進む判断だとある。

## 7. わっちの評価

今回で **finite path skeleton はほぼ一区切り** と見てよい。

特に完成したのはこれじゃ。

$$
\boxed{
\text{list-shaped prime descent path}
\Rightarrow
\text{primitive hit mass bound}
}
$$

この箱ができたのは大きい。

Erdős #1196 の本体に向けて、まだ Markov kernel や $\Lambda(q)/\log n$ は入っていない。
しかし、そこへ行く前の有限 combinatorial ルートは、かなり読みやすくなった。

## 8. 次の一手

ここからは二択じゃ。

### A. 小さく固めるなら positive / lower-bound support

今回も過去に `{1,2}` のような例で primitive 性が壊れた流れがあった。Erdős #1196 本体では $A\subset [x,\infty)$ なので、 $0$ や $1$ を自然に除外する補助語彙が欲しい。

例えば、

```lean
def PositiveOn (S : Finset ℕ) : Prop :=
  ∀ n ∈ S, 0 < n
```

または、

```lean
def LowerBoundOn (x : ℕ) (S : Finset ℕ) : Prop :=
  ∀ n ∈ S, x ≤ n
```

これは軽い。安定化には良い。

### B. 本筋へ進むなら Branching / SubConservative bridge

わっちは、ここまで来たなら **B を推す** 。

理由は、有限 path skeleton が十分にできたので、次は Mass API 側の

$$
\sum_{\text{children}}\mu(child)\le \mu(parent)
$$

と繋ぐべき段階だからじゃ。

つまり次は、

$$
\text{SubConservative}
\Rightarrow
\text{path 上の質量非増加}
\Rightarrow
\text{source-controlled forest}
$$

という bridge を作る。

これは宇宙式ルートとして非常に美しい。

## 9. 推奨実装指示

次は新規ファイルでよい。

```text
DkMath/NumberTheory/PrimitiveSet/SubConservativeBridge.lean
```

目的は、`Branching` / `SubConservative` から path 上の質量支配を作ること。

最初は一般 reachability を無理に作らず、有限 list path に対して、

```lean
∀ node ∈ source :: tail, M.μ node ≤ M.μ source
```

を得るための package を作るのがよい。

ただし `SubConservative` は「子和が親以下」なので、個々の child が親以下であることを出すには非負性が効く。つまり補題はこうなる。

$$
child\in children(parent)
\Rightarrow
\mu(child)\le \sum_{c\in children(parent)}\mu(c)\le\mu(parent)
$$

これを Lean で閉じるのが次の山場じゃ。

## 10. 総括

今回の Phase I は、有限 Erdős skeleton の **道としての完成** じゃ。

以前は、

$$
PrimeReachable
$$

という抽象到達可能性があった。
今回は、

$$
[source, \ldots]
$$

という実際の list path から、reachable-controlled forest と primitive hit mass bound へ直接進めるようになった。

山で言えば、地図・尾根・標高計に加えて、ついに **実際の登山道のログ** が Lean に刻まれた。
次は、その登山道に「質量が増えない」という物理法則を載せる番じゃな。
