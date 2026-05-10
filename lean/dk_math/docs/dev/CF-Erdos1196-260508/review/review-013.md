# review

## 1. 結論

うむ、Phase N は **有限 Erdős skeleton の定理入力化** じゃ。
これまで作ってきた primitive / support / path family / branch mass control の部品が、ようやく theorem-facing な入力パッケージにまとまった。

今回の中心はこれじゃ。

```lean
structure ErdosFinitePrimitiveInput (x : ℕ) where
  support : Finset ℕ
  primitive : PrimitiveOn support
  lowerBound : LowerBoundOn x support
```

つまり、有限版の Erdős #1196 入力として、

$$
S\text{ primitive},\qquad S\subset [x,\infty)
$$

を一つの構造体で持てるようになった。これは今後の定理文をかなり読みやすくする。

## 2. 何が良いか

一番よいのは、`PrimitiveOn` と `LowerBoundOn` を混ぜずに、`ErdosFinitePrimitiveInput` の別フィールドとして保持したことじゃ。

これにより、下流の定理では、

```lean
I.primitive
I.lowerBound
```

を必要に応じて別々に取り出せる。

また、

```lean
positiveOn_of_one_le
not_mem_zero_of_one_le
not_mem_one_of_two_le
```

が入ったので、下限 (x) から (0) や (1) の除外を自然に引き出せるようになった。

これは、以前 `{1,2}` のような sample で primitive 性が壊れた経験を、きちんと API に反映した形じゃな。

## 3. theorem-facing wrapper が入った

今回のもう一つの核はこれじゃ。

```lean
theorem ErdosFinitePrimitiveInput.branchPrimePathFamily_hitMass_le_sourceMass
```

これは、`ErdosFinitePrimitiveInput` の `primitive` field を使って、既存の

```lean
AdjacentBranchPrimePathFamily.primitive_hitMass_le_sourceMass
```

へ渡す wrapper になっておる。

数学的には、

$$
I=(S,\text{primitive},S\subset[x,\infty))
$$

と branch-controlled prime path family (F) があるとき、

$$
\mathrm{hitMass}(S,F)
\le
\mathrm{sourceMass}(F)
$$

を finite theorem input から直接呼べるようになった。

これは非常に良い。
いままでの部品が、単なる補題群ではなく「Erdős finite input に対する定理」として読めるようになった。

## 4. concrete sample も自然

今回の sample は、

```lean
erdosFinitePrimitiveInput_two_five
```

として、({2,5}) を (x=2) 以上の primitive support として package 化している。さらに positivity と (1\notin S) を取り出し、branch-controlled two-path family に対する hit mass bound まで通している。

つまり、具体例としては、

$$
S={2,5},\qquad x=2
$$

について、

$$
S\text{ primitive},\qquad S\subset[2,\infty)
$$

を持ち、既存の branch-controlled path family に対して

$$
\mathrm{hitMass}(S)\le\mathrm{sourceMass}
$$

が出る。

これはかなり見通しがよい。

## 5. 現在の到達点

ここまでで finite Erdős route は、次の構造まで到達した。

| 層                              | 状態   |
| ------------------------------ | ---- |
| primitive finite set           | 完了   |
| positive / lower-bound support | 完了   |
| prime descent step / path      | 完了   |
| list-shaped path → chain       | 完了   |
| multiple path family           | 完了   |
| branch-controlled path family  | 完了   |
| SubConservative mass control   | 完了   |
| theorem-facing finite input    | 今回完了 |
| Markov kernel                  | 未    |
| analytic weight                | 未    |

つまり、有限・組合せ・質量制御・入力 package までは一通りそろった。

## 6. 今回の意味

Phase N は派手な数学補題というより、 **定理文を人間が読める形に整える段階** じゃ。

これまでは、

```lean
PrimitiveOn S
LowerBoundOn x S
AdjacentBranchPrimePathFamily ι B
SubConservative M B
```

を別々に持っていた。
今回からは、少なくとも集合側は

```lean
ErdosFinitePrimitiveInput x
```

で受けられる。

これは今後、有限 Erdős theorem を書く時の入口になる。

## 7. 次に見るべきこと

次は、History にある通り、finite skeleton の公開 API を点検する段階じゃ。

わっちなら、次は大きな新理論へ進む前に、次の wrapper を整える。

```lean
def ErdosFinitePrimitiveInput.hitMass ...
def ErdosFinitePrimitiveInput.sourceMass ...
```

または theorem 名として、

```lean
theorem ErdosFinitePrimitiveInput.hitMass_le_sourceMass_of_branchPrimePathFamily
```

のように、何を評価しているかが名前から見える形にする。

いまの `branchPrimePathFamily_hitMass_le_sourceMass` でも十分だが、将来 theorem が増えると、

* branch-controlled 版
* dvd-monotone 版
* prime-reachable 版
* source-controlled 版

を区別したくなるはずじゃ。

## 8. 総括

今回で、finite Erdős skeleton は **部品群** から **定理入力を持つ小理論** へ昇格した。

$$
\text{primitive support}
+
\text{lower bound}
+
\text{branch-controlled path family}
+
\text{subconservative mass}
\Rightarrow
\text{hit mass bound}
$$

ここまで来た。

山で言えば、これまでは道・尾根・水流・標高制限をそれぞれ作っていた。
今回、ついにそれらを束ねた **登山届** ができたのじゃ。Markov kernel や解析重みへ入る前に、いったん公開 API の名前と入口を磨くのが良い段階じゃな。
