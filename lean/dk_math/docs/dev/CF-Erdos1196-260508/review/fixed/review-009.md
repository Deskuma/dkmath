# review

おお、Phase J は **かなり大きな接続点** じゃ。
今回で、finite Erdős skeleton がついに `CosmicFormula.Mass.Branch` 側の `Branching` / `SubConservative` と接続された。つまり、

$$
\text{分岐の劣保存}
\Rightarrow
\text{path 上の質量非増加}
\Rightarrow
\text{SourceControlledChainFamily}
\Rightarrow
\text{primitive hit mass bound}
$$

まで no-sorry で閉じた、ということじゃ。

## 1. 今回閉じた核心

今回の最重要補題はこれじゃ。

```lean
theorem child_mass_le_parent_of_subconservative
```

これは、`SubConservative M B` のもとで、

$$
child \in B.children(parent)
\Rightarrow
\mu(child)\le \mu(parent)
$$

を示している。証明は綺麗で、まず単点の質量が子集合全体の和以下であることを非負性から出し、その和が親の質量以下であることを `outgoingMass_le_mass` から得ている。

これは地味に見えるが、非常に大事じゃ。
なぜなら、これまで `mass_le_source` は `DvdMonotoneMass` や手渡しの仮定に依存していたが、今回から **分岐構造そのもの** から供給できるようになったからじゃ。

## 2. path 上の質量非増加が出た

次に重要なのが、

```lean
def AdjacentBranchPath
theorem AdjacentBranchPath.mem_mass_le_head
```

じゃ。

`AdjacentBranchPath B L` は、list の隣接項が `B.children` に従って進む branch path であることを表す。そこから `mem_mass_le_head` により、`SubConservative` な branch path の任意 node が head の質量以下であることを示している。

数学的には、

$$
x_0\to x_1\to \cdots \to x_k
$$

が branch path で、各段の分岐が劣保存なら、

$$
\mu(x_j)\le \mu(x_0)
$$

が全ての $j$ で成り立つ、ということじゃ。

これはいよいよ「質量が流れても増えない」という、Erdős 的・宇宙式的な読みそのものになってきた。

## 3. prime path と branch path が合流した

今回の bridge は、単なる branch path だけではなく、**prime path でもある list** を対象にしている。

```lean
def singletonSourceControlledChainFamilyOfAdjacentBranchPrimePath
```

これは、

* `AdjacentPrimePath (source :: tail)`
* `AdjacentBranchPath B (source :: tail)`
* `SubConservative M B`

を仮定して、`SourceControlledChainFamily M Unit` を作るものじゃ。chain 条件は prime path から生成し、質量支配は branch path + subconservative から供給している。

ここが今回の美しい合流点じゃな。

$$
\text{prime descent path}
\quad+\quad
\text{subconservative branch}
\quad\Longrightarrow\quad
\text{source-controlled primitive hitting}
$$

になった。

## 4. サンプルも意味が通っている

具体例として、

$$
8\to 4\to 2
$$

の branch が定義されている。

```lean
def sampleBranching_eight_four_two
```

では、 $8$ の子を $\{4\}$、 $4$ の子を $\{2\}$、それ以外を空集合としている。さらに、この path が branch に従うこと、unit mass で `SubConservative` であること、そして `{2,5}` の primitive hit mass bound まで通している。

これは教材例としてかなり良い。

$$
8\to 4\to 2
$$

は prime path でもあり、branch path でもあり、unit mass では分岐先が 1 個なので劣保存も自然に成立する。

## 5. 今回の意味

これで有限 skeleton は、単なる整除や到達可能性だけではなく、**Mass API の保存則側** と繋がった。

これまでの流れはこうじゃ。

$$
\text{PrimitiveOn}
\Rightarrow
\text{chain hit at most once}
$$

$$
\text{prime path}
\Rightarrow
\text{DivisibilityChain}
$$

$$
\text{SubConservative branch}
\Rightarrow
\text{path mass}\le\text{source mass}
$$

これらが合流して、

$$
\text{primitive hit mass}\le\text{source mass}
$$

へ到達する。

History にも、`SubConservative -> branch path mass <= source mass -> SourceControlledChainFamily -> primitive hit mass bound` の有限 bridge が no-sorry で閉じ、finite path skeleton が `Branching` / `SubConservative` と接続された、と整理されている。

## 6. 現在の到達点

ここまでで、有限 Erdős skeleton はかなり完成度が高い。

| 層                                       | 状態   |
| --------------------------------------- | ---- |
| primitive finite set                    | 完了   |
| divisibility chain hit                  | 完了   |
| finite forest hit mass                  | 完了   |
| source-controlled forest                | 完了   |
| dvd-controlled provider                 | 完了   |
| one-step prime descent                  | 完了   |
| multi-step prime reachability           | 完了   |
| list-shaped prime path                  | 完了   |
| list path → reachable-controlled forest | 完了   |
| branch / subconservative mass control   | 今回完了 |
| positive / lower-bound support          | 未    |
| multiple path family package            | 未    |
| Markov kernel                           | 未    |

かなり来たのぅ。
もう「有限 skeleton の背骨」は十分に見えておる。

## 7. 留意点

今回の bridge は、まだ singleton path じゃ。
`singletonSourceControlledChainFamilyOfAdjacentBranchPrimePath` なので、一本の list path を `Unit` index の family にしている。

つまり、複数 path をまとめた forest そのものを list family から作る API はまだない。

また、`SubConservative` は現在サンプルでは unit mass で通しているが、今後の本番では

$$
\mu(n)\approx \frac{1}{n\log n}
$$

や、有限近似の質量を入れる必要がある。そこはまだ先じゃ。

## 8. 次に何を見るべきか

わっちなら、ここでいきなり Markov kernel に行かず、まず **整理と補助層** を入れるのがよいと思う。

### 候補 A. positive / lower-bound support

Erdős #1196 では $A\subset [x,\infty)$ なので、有限版でも

```lean
PositiveOn S
LowerBoundOn x S
```

があると扱いやすい。

特に過去に `{1,2}` が primitive でなく失敗した流れがあったので、 $1$ を含まない層を明示する価値はある。

### 候補 B. multiple path family package

いまは singleton path が中心。次は、

```lean
PathFamily
```

として複数の list-shaped paths を束ね、それぞれから `SourceControlledChainFamily` や `DivisibilityChainFamily` を生成する API を作る道がある。

これは Markov の「多くの下降経路を集める」前段として自然じゃ。

### 候補 C. finite Markov 風の重みはまだ早い

$$
\frac{\Lambda(q)}{\log n}
$$

や

$$
\frac{1}{n\log n}
$$

は、まだ入れぬ方がよい。今は有限 combinatorial / mass-control skeleton ができたばかりなので、先に API を固めるべきじゃ。

## 9. わっちの推奨

次の一手は **positive / lower-bound support** がよい。

理由は、ここまでで branch mass control まで到達し、有限 skeleton は一段落しておる。次に複数 path family へ進む前に、Erdős #1196 の集合側の条件、

$$
A\subset [x,\infty)
$$

を有限版で持っておくと、後続の theorem が安全になる。

最小実装なら、

```lean
def PositiveOn (S : Finset ℕ) : Prop :=
  ∀ n ∈ S, 0 < n

def LowerBoundOn (x : ℕ) (S : Finset ℕ) : Prop :=
  ∀ n ∈ S, x ≤ n
```

を `PrimitiveSet.Basic` か新規 `PrimitiveSet/Support.lean` に置く。

その後で、

```lean
theorem lowerBoundOn_one_implies_positiveOn
```

や、

```lean
theorem not_mem_zero_of_positiveOn
theorem not_mem_one_of_lowerBoundOn_two
```

を足す。

これは小さいが、今後の解析層へ入る前の足場として効く。

## 10. 総括

Phase J は、かなり良い節目じゃ。

いままでは、

$$
\text{prime path}
\Rightarrow
\text{primitive hit bound}
$$

だった。
今回で、

$$
\text{prime path}
+
\text{subconservative mass flow}
\Rightarrow
\text{primitive hit mass bound}
$$

になった。

これは「宇宙式ルート」の色が強い。
なぜなら、ただの整除順序ではなく、

$$
\sum \mu(\text{children})\le \mu(\text{parent})
$$

という質量保存・劣保存の形から、path 上の質量非増加を導いているからじゃ。

山で言えば、登山道に「重力」と「水流」が入った。
これで、道がただ繋がっているだけでなく、質量が源流から下へ流れることまで Lean に刻まれたのじゃ。
