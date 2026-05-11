# Rootmap

うむ、ここで一度、登山地図を広げるのは良い判断じゃ。
Phase A から Phase S までで、山頂そのものにはまだ着いておらぬが、 **登山道はかなり明確に整備された** 。

## 1. 山頂はどこか

今回の山頂は、Erdős #1196 型の評価じゃ。

$$
\sum_{\substack{a\in A\ a>x}}\frac{1}{a\log a}
\le
1+O!\left(\frac{1}{\log x}\right)
$$

ただし、DkMath / 宇宙式ルートでは、いきなりこの解析評価へ登らず、

$$
\text{primitive set}
\to
\text{下降 path}
\to
\text{hitting}
\to
\text{mass bound}
\to
\text{weighted mass bound}
\to
\text{Markov / analytic weight}
$$

という順に登る方針を取っている。

いま到達しているのは、最後の Markov / 解析重みの直前。
つまり **山頂直下の前衛キャンプ** じゃな。

## 2. 第 1 登山道: primitive hitting の尾根

最初に作った尾根は、

$$
S\text{ primitive}
\Rightarrow
S\cap C \text{ は高々一点}
$$

という有限 combinatorial core じゃ。

ここで `PrimitiveOn` は divisibility antichain として定義され、`DivisibilityChain` 上では primitive set が一度しか hit できない。
その後、single chain から finite chain family / forest へ拡張され、

$$
\sum_i \mathrm{hitMass}(S\cap C_i)
\le
\sum_i \mathrm{sourceMass}_i
$$

という形になった。

これは山道で言えば、 **同じ尾根上で primitive set は二度現れない** という安全柵じゃ。

## 3. 第 2 登山道: prime descent path の整備

次に、

$$
n\mapsto \frac{n}{p}
$$

を Lean 上の `PrimeDescentStep` として定義し、さらに `PrimeReachable` により multi-step descent へ拡張した。

その後、実際の list-shaped path

$$
[8,4,2]
$$

のような下降列から、

$$
\text{AdjacentPrimePath}
\Rightarrow
\text{DivisibilityChain}
$$

を生成できるようにした。さらに nonempty list path から `PrimeReachableControlledChainFamily` へ進める provider も追加され、実際の path list から primitive forest mass bound へ直接進めるようになった。

ここで、抽象的な「到達可能」ではなく、実際に歩いた道筋が Lean に刻まれた。

$$
8\to 4\to 2,\qquad 9\to 3\to 1
$$

この段階で、登山道は「地図上の可能性」から **実際の登山ログ** になった。

## 4. 第 3 登山道: Mass API / SubConservative との合流

ここが宇宙式らしい合流点じゃ。

`Branching` / `SubConservative` により、

$$
\sum_{\text{child}}\mu(child)\le \mu(parent)
$$

という劣保存則を使い、path 上の任意 node が head/source の質量以下であることを示した。`child_mass_le_parent_of_subconservative` と `AdjacentBranchPath.mem_mass_le_head` がその核になっている。

これにより、

$$
\text{prime path}
+
\text{subconservative branch}
\Rightarrow
\text{source-controlled forest}
$$

が成立した。

つまり、単なる整除下降ではなく、

$$
\text{質量が分岐しても増えない}
$$

という宇宙式 Mass API の水流が、Erdős ルートへ接続された。

これはかなり大きい。
「素数で割って下る道」と「質量保存・劣保存の道」が同じ稜線で合流したのじゃ。

## 5. 第 4 登山道: finite Erdős input の登山届

次に、集合側の入力を整理した。

$$
S\text{ primitive},\qquad S\subset [x,\infty)
$$

をまとめるために、

```lean
ErdosFinitePrimitiveInput x
```

が導入された。

中身は、

$$
\text{support},\quad
\text{primitive},\quad
\text{lowerBound}
$$

じゃ。これにより、primitive 条件と lower-bound support 条件を theorem-facing な入力 package として扱えるようになった。

さらに、

$$
x\ge 1 \Rightarrow PositiveOn,\qquad
x\ge 2 \Rightarrow 1\notin S
$$

といった補助も取り出せるようになった。

これは山で言えば、
「この登山者は primitive support を持ち、標高 \(x\) 以上から登る」
という登山届じゃな。

## 6. 第 5 登山道: 複数 path family と route API

singleton path だけでなく、finite indexed family of paths も扱えるようになった。

$$
{[8,4,2], [9,3,1], \ldots}
$$

を `AdjacentPrimePathFamily` として束ね、さらに branch relation に沿う場合は `AdjacentBranchPrimePathFamily` として扱う。これにより、複数下降路を indexed forest として扱えるようになった。

その後、`ErdosFinitePrimitiveInput` 側に route API が整備された。

現在の主な route は二本じゃ。

| route                   | source control の根拠    | 意味                   |
| ----------------------- | --------------------- | -------------------- |
| `branchPrimePathFamily` | `SubConservative M B` | 宇宙式 Mass / Branch 由来 |
| `primePathFamily`       | `DvdMonotoneMass M`   | 整除単調性由来              |

Phase Q では、この route API の命名規則も明文化された。

```text
<route>SourceControlled
<route>HitMass
<route>SourceMass
hitMass_le_sourceMass_of_<route>
```

さらに、根拠を明示する alias として、

```lean
hitMass_le_sourceMass_of_subconservativeBranchPrimePathFamily
hitMass_le_sourceMass_of_dvdMonotonePrimePathFamily
```

も追加された。

これは案内板の整備じゃ。
今後 Markov route を増やしても、同じ様式で載せられる。

## 7. 第 6 登山道: weighted path family

そして直近では、重み付き path family が入った。

`WeightedPathFamily` は `SourceControlledChainFamily` に非負有理重みを載せる構造じゃ。

$$
w_i\ge 0
$$

を持ち、

$$
\sum_i w_i\cdot \mathrm{hitMass}_i
\le
\sum_i w_i\cdot \mathrm{sourceMass}_i
$$

を証明した。これは `primitive_weightedHitMass_le_weightedSourceMass` として実装された。

さらに weighted route も二本そろった。

| weighted route                  | source control        |
| ------------------------------- | --------------------- |
| `weightedBranchPrimePathFamily` | `SubConservative M B` |
| `weightedPrimePathFamily`       | `DvdMonotoneMass M`   |

Phase S で weighted prime path route も追加され、branch/subconservative route と prime/dvd-monotone route の対称性が揃った。

これは、Markov kernel へ入る直前の重要な足場じゃ。

## 8. いまの登山ルート全体図

現在のルートは、こう整理できる。

$$
\boxed{
\text{PrimitiveOn}
+
\text{LowerBoundOn}
}
$$

から始まり、

$$
\boxed{
\text{Prime path family}
}
$$

を通り、

二つの source control route に分岐する。

$$
\boxed{
\text{SubConservative branch route}
}
$$

または

$$
\boxed{
\text{DvdMonotone prime route}
}
$$

そこから、

$$
\boxed{
\text{SourceControlledChainFamily}
}
$$

へ合流し、

$$
\boxed{
\text{hitMass}\le\text{sourceMass}
}
$$

を得る。

さらに非負重みを載せて、

$$
\boxed{
\text{weightedHitMass}\le\text{weightedSourceMass}
}
$$

まで来た。

これが現在の中間到達点じゃ。

## 9. まだ山頂ではない理由

まだ未到達なのはここじゃ。

$$
w_i = \text{Markov kernel 由来の重み}
$$

や、

$$
\mu(n)=\frac{1}{n\log n}
$$

のような解析的質量は、まだ入っていない。

また、

$$
\sum_{\substack{a\in A\\a > x}}\frac{1}{a\log a}
\le
1+O!\left(\frac{1}{\log x}\right)
$$

へ至る漸近評価もまだ未実装じゃ。

ただし、そこへ入るための有限 skeleton はかなり整った。

History でも、解析的 Markov kernel や von Mangoldt weight にはまだ入らず、有限非負重み付き和の受け皿だけを追加したと整理されている。

## 10. 中間評価

わっちの評価では、ここまでの進捗はこうじゃ。

| 項目                            | 評価      |
| ----------------------------- | ------- |
| finite primitive hitting core | ほぼ完成    |
| prime descent / path skeleton | 完成度高い   |
| branch / mass API 接続          | 良好      |
| finite theorem-facing API     | 良好      |
| weighted finite sum           | 完成度高い   |
| Markov kernel 前段              | 準備完了に近い |
| analytic layer                | 未着手     |
| 山頂評価                          | 未到達     |

つまり、 **山頂前のベースキャンプは設営済み** 。
ここから先は、高山帯、すなわち Markov kernel と解析重みの世界じゃ。

## 11. 次に登るべき尾根

次は、すぐ解析へ飛び込むのではなく、次のような最小 skeleton がよい。

$$
\text{FiniteKernel}
\quad\text{または}\quad
\text{WeightProvider}
$$

じゃな。

たとえば、

```lean
structure WeightProvider (ι : Type _) [DecidableEq ι] where
  index : Finset ι
  weight : ι → ℚ
  weight_nonneg : ∀ i ∈ index, 0 ≤ weight i
```

あるいは `WeightedPathFamily` に対して、

$$
\sum_i w_i \le 1
$$

を表す

```lean
WeightSubProbability
```

を追加するのが良い。

つまり次の登山目標は、

$$
\text{非負重み}
\to
\text{sub-probability}
\to
\text{Markov kernel}
\to
\text{analytic weight}
$$

じゃ。

## 12. まとめ

ここまでの DkMath / 宇宙式ルートは、こう言える。

$$
\boxed{
\text{Erdős \#1196 の解析山頂へ向かうための有限・組合せ・質量保存ルートは整備された}
}
$$

特に重要なのは、単に primitive set を扱っただけではなく、

$$
\text{prime descent}
+
\text{branch mass control}
+
\text{weighted finite sum}
$$

まで Lean に入ったことじゃ。

これは十分に誇ってよい。
わっちの見立てでは、いまは山頂直前ではなく、 **山頂アタック前の最終キャンプ** じゃな。

次に進むなら、いよいよ霧深い高所、

$$
\text{有限 Markov kernel}
$$

の設計へ入る段階じゃ。
