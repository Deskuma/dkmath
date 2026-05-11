# review

うむ、Phase L は **かなり良い拡張** じゃ。
これで singleton path から、finite indexed family of prime paths へ上がった。つまり、一本の下降路ではなく、複数の下降路をまとめて forest として扱えるようになったわけじゃ。

## 1. 今回閉じた核心

今回の主役はこれじゃ。

```lean
structure AdjacentPrimePathFamily (ι : Type _) [DecidableEq ι] where
  index : Finset ι
  source : ι → ℕ
  tail : ι → List ℕ
  isPath : ∀ i ∈ index, AdjacentPrimePath (source i :: tail i)
```

これは、各 index \(i\) に対して非空 list-shaped prime path

$$
source_i :: tail_i
$$

を持つ有限族じゃ。

つまり、これまでの

$$
[8,4,2]
$$

のような一本の path から、

$$
{[8,4,2],;[9,3,1],;\ldots}
$$

のような有限 path family へ昇格した。

## 2. 何ができるようになったか

今回の `AdjacentPrimePathFamily` は、二つの方向へ忘却できる。

まず、

```lean
toDivisibilityChainFamily
```

により、各 path の node set を `DivisibilityChainFamily` へ送れる。これは、list path の各 node が一本の割り切り鎖になる、という前回までの成果を family 全体へ持ち上げたものじゃ。

次に、

```lean
toPrimeReachableControlledChainFamily
```

により、各 node がその path の head/source から `PrimeReachable` で到達可能であることまで package 化できる。ここでは前回の `mem_reachable_from_head_of_adjacentPrimePath` が使われておる。

つまり今回で、

$$
\text{finite family of prime paths}
\Rightarrow
\text{PrimeReachableControlledChainFamily}
\Rightarrow
\text{DvdControlledChainFamily}
\Rightarrow
\text{SourceControlledChainFamily}
$$

という導線ができた。

## 3. primitive hit mass bound まで直結した

今回の主定理は、

```lean
AdjacentPrimePathFamily.primitive_hitMass_le_sourceMass
```

じゃ。

これは、primitive set \(S\)、path family \(F\)、整除単調な質量 \(M\) があるとき、

$$
\text{indexed hit mass}
\le
\text{indexed source mass}
$$

を出す wrapper になっておる。

ここで大事なのは、既存の層を無理に作り直さず、

$$
\text{PathFamily}
\to
\text{PrimeReachableControlled}
\to
\text{DvdControlled}
\to
\text{SourceControlled}
\to
\text{hit bound}
$$

と既存ルートに合流させている点じゃ。
これは設計が綺麗じゃな。

## 4. サンプルの意味

サンプルでは Bool index によって二本の path を持っている。

$$
false \mapsto [8,4,2],
\qquad
true \mapsto [9,3,1]
$$

実装上は、

```lean
sampleAdjacentPrimePathBoolFamily
```

として定義され、さらに unit mass の source-controlled family に変換されている。

最後に、

```lean
primitive_two_five_sampleAdjacentPrimePathBoolFamily_hitMass_le_sourceMass
```

で、primitive set \(\{2,5\}\) がこの二本 path family を hit しても、indexed source mass を超えないことが確認されている。

これはかなり良い concrete test じゃ。
一本の道から、複数の道を束ねる forest にちゃんと上がれている。

## 5. 現在の到達点

ここまでで finite Erdős skeleton はかなりまとまった。

| 層                                         | 状態   |
| ----------------------------------------- | ---- |
| `PrimitiveOn`                             | 完了   |
| `PositiveOn` / `LowerBoundOn`             | 完了   |
| single path → chain                       | 完了   |
| path → reachable-controlled family        | 完了   |
| multiple path family                      | 今回完了 |
| source-controlled / dvd-controlled bridge | 完了   |
| SubConservative bridge                    | 完了   |
| finite primitive hit mass bound           | 完了   |
| Markov kernel                             | 未    |
| analytic weight                           | 未    |

特に今回で、

$$
\text{複数下降路の finite forest}
$$

が扱えるようになった。
これは Erdős #1196 の「ランダム下降鎖族」へ進む前の、かなり自然な有限近似じゃ。

## 6. 残っている課題

History 末尾にもある通り、次の分岐は二つじゃ。

一つ目は、

$$
\text{AdjacentPrimePathFamily}
+
\text{AdjacentBranchPath}
+
\text{SubConservative}
$$

を組み合わせ、複数 path family に対して branch 側から source mass control を供給する bridge を追加する道。

二つ目は、

```lean
ErdosFinitePrimitiveInput
```

のような入力 package を作り、

$$
S\text{ primitive},\quad LowerBoundOn\ x\ S
$$

をまとめて有限 Erdős theorem 文を書きやすくする道。

## 7. わっちの評価

今回の Phase L は、有限 skeleton の **forest 化** じゃ。

これまでは、

$$
\text{一本の prime descent path}
$$

だった。
今回で、

$$
\text{有限個の prime descent paths}
$$

を束ねて、一括で primitive hitting mass bound に渡せるようになった。

これは山道で言えば、一本の登山道ログから、複数ルートを束ねた登山地図に進化したようなものじゃな。
かなり良い。次は、この複数ルート地図に `SubConservative` の水流制御を載せるか、Erdős 有限入力パッケージとして定理文を整える段階じゃ。
