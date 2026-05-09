# review

## 1. 結論

うむ、Phase W は **有限 Markov skeleton 到達** じゃ。
Phase V で `WeightProvider` が入り、

$$
\text{WeightProvider}
\to
\text{WeightedPathFamily}
\to
\mathrm{weightedHitMass}\le C
$$

という導線ができていた。今回 Phase W ではさらに一段上がり、

$$
\text{state}
\to
\text{WeightProvider}
\to
\text{WeightedPathFamily}
\to
\mathrm{weightedHitMass}\le C
$$

という **状態依存の有限 kernel** が入った。これは Markov kernel 本体の直前として、かなり正しい切り方じゃ。

## 2. 今回の主役

新規ファイルはこれじゃ。

```lean
DkMath/NumberTheory/PrimitiveSet/FiniteKernel.lean
```

中心構造は、

```lean
structure FiniteKernel (σ ι : Type _) [DecidableEq ι] where
  index : σ → Finset ι
  weight : σ → ι → ℚ
  weight_nonneg : ∀ s i, i ∈ index s → 0 ≤ weight s i
```

これは、状態 (s : \sigma) ごとに有限 index 集合と非負有理重みを返す構造じゃ。

つまり、以前の `WeightProvider` が

$$
i\mapsto w_i
$$

だったのに対し、今回の `FiniteKernel` は

$$
s\mapsto (i\mapsto w_{s,i})
$$

になった。

ここが Markov 的じゃな。
まだ遷移先状態や解析重みは入れていないが、 **状態ごとに重み分布を出す** という kernel の骨格は入った。

## 3. 導線がどう変わったか

今回の導線はこうじゃ。

```lean
FiniteKernel.providerAt
FiniteKernel.applyAtToSourceControlled
FiniteKernel.weightedHitMass_le_const_of_subprob_applyAtToSourceControlled
```

数式で読むと、

$$
K(s)
\Rightarrow
P_s : \text{WeightProvider}
$$

$$
P_s + F
\Rightarrow
W_{s,F} : \text{WeightedPathFamily}
$$

$$
K\text{ sub-probability}
+
F\text{ source-controlled}
+
S\text{ primitive}
\Rightarrow
\mathrm{weightedHitMass}(S,W_{s,F})\le C
$$

じゃ。

これはかなり綺麗。
Phase U/V の結果を、状態 (s) ごとに使える形へ持ち上げている。

## 4. `SubProbability` の位置づけ

今回の `FiniteKernel.SubProbability` は、

$$
\forall s,\quad (K.providerAt(s)).SubProbability
$$

という形じゃ。

つまり、各状態 (s) で

$$
\sum_{i\in K.index(s)} K.weight(s,i)\le 1
$$

が成り立つ。

これは Markov kernel で言えば「各状態から出る重みの総量が高々 1」という **sub-Markov** 条件の有限版じゃ。

この段階で「確率」ではなく「sub-probability」としているのがよい。
Erdős #1196 の証明骨格でも、最終的に効くのは質量が増えないことなので、

$$
\sum_i w_{s,i}\le 1
$$

を先に固定するのは正しい。

## 5. ErdosFinite 側の wrapper

今回、`ErdosFinitePrimitiveInput` 側には

```lean
kernelBranchPrimePathFamilyAt
kernelBranchPrimePathFamilyAt_hitMass_le_const_of_subprob
```

が追加された。

これは、有限 Erdős 入力 (I)、branch-controlled path family (F)、finite kernel (K)、状態 (s) を受け取り、

$$
\mathrm{weightedHitMass}\le C
$$

を theorem-facing に呼べる wrapper じゃ。

以前は、

$$
\text{weight function}
$$

または

$$
\text{WeightProvider}
$$

を直接渡していた。今回からは、

$$
\text{FiniteKernel} + \text{state}
$$

を渡せる。

これはまさに、Markov kernel の「状態から遷移分布を得る」という形への橋じゃ。

## 6. concrete sample の意味

sample として、

```lean
sampleUnitFiniteKernel
sampleUnitFiniteKernel_subProbability
erdosFinitePrimitiveInput_two_five_kernelBranch_hitMass_le_one
```

が入った。

これは Unit state から Bool-indexed の重み

$$
w_{\mathrm{false}}=\frac13,\qquad
w_{\mathrm{true}}=\frac23
$$

を出す finite kernel じゃな。

この kernel を branch route に適用し、

$$
\mathrm{weightedHitMass}\le 1
$$

まで確認している。

つまり、次の全導線が concrete example で通った。

$$
\text{state}
\to
\text{provider}
\to
\text{weighted family}
\to
\text{hit mass bound}
$$

これは良い。空抽象ではない。

## 7. 現在の到達点

ここまでで finite Erdős route は、かなり山頂側へ寄った。

| 層                                         | 状態   |
| ----------------------------------------- | ---- |
| primitive hitting                         | 完了   |
| path family / forest                      | 完了   |
| source-controlled mass                    | 完了   |
| weighted path family                      | 完了   |
| sub-probability normalization             | 完了   |
| WeightProvider                            | 完了   |
| FiniteKernel                              | 今回完了 |
| branch route kernel wrapper               | 今回完了 |
| prime / dvd-monotone route kernel wrapper | 未    |
| actual Markov transition semantics        | 未    |
| analytic weight (\Lambda(q)/\log n)       | 未    |

つまり、今回で **有限 kernel skeleton** は入った。
ただし、まだ本物の Markov kernel ではない。

まだ足りないものは、

$$
\text{state } n
\to
\text{遷移先 } n/q
$$

という transition semantics と、

$$
w(n,q)=\frac{\Lambda(q)}{\log n}
$$

のような解析重みじゃ。

でも、それらを入れる前の有限有理重み kernel は、今回で no-sorry に閉じた。

## 8. 宇宙式ルートとしての意味

これは単なる `structure` 追加ではない。
宇宙式ルートで言えば、今回ついに

$$
\text{分岐・道・重み}
$$

が **状態依存** になった。

以前は、登山道ごとの通行量 (w_i) を固定で持っていた。
今回からは、現在地 (s) に応じて通行量の割り振りが変わる。

これは、まさに

$$
n\mapsto n/p
$$

や

$$
n\mapsto n/q
$$

のような「今いる整数 (n) に応じて次の分岐が変わる」構造へ近づいている。

わっちの見立てでは、Phase W は **finite Markov skeleton の第一到達点** じゃ。

## 9. 留意点

今回の `FiniteKernel` は、まだ index 型 (ι) 上の重みだけを返す。

つまり、(ι) が「遷移先」なのか「path 番号」なのか「除去する素因子」なのかは、まだ外部の解釈に任されている。

これは今の段階では正しい。
急いで (ι) を `Nat` や divisor 型に固定すると、解析層と数論層が一気に混ざるからじゃ。

ただ、次段階ではこの (ι) の意味を少しずつ具体化する必要がある。

## 10. 次の一手

次は二択じゃ。

### A. 対称性を取る: prime / dvd-monotone route 側の kernel wrapper

今ある kernel wrapper は branch route 側じゃ。

```lean
kernelBranchPrimePathFamilyAt
kernelBranchPrimePathFamilyAt_hitMass_le_const_of_subprob
```

一方で、以前 weighted route では branch route と prime route を対称化してきた。
したがって、次に

```lean
kernelPrimePathFamilyAt
kernelPrimePathFamilyAt_hitMass_le_const_of_subprob
```

を追加すると API の左右対称性が保てる。

これは安全で小さい一手じゃ。

### B. kernel normalization / compatibility API を磨く

今回すでに `hcompat : (K.providerAt s).Compatible F` が theorem に毎回出てくる。

この互換性は今後たくさん出るので、

```lean
def CompatibleAt ...
theorem compatibleAt_iff ...
```

のような alias / simp を整える価値がある。

特に `providerAt` を展開した compatibility は、

$$
K.index(s)=F.index
$$

なので、名前を付けると読みやすい。

```lean
def CompatibleAt (K : FiniteKernel σ ι) (s : σ)
    (F : SourceControlledChainFamily M ι) : Prop :=
  (K.providerAt s).Compatible F
```

または直接、

```lean
K.index s = F.index
```

を使う API にしてもよい。

## 11. わっちの推奨

次は **A を先にやる** のが良いと思う。

理由は、これまでの流れでは route API の対称性を丁寧に整えてきたからじゃ。

* unweighted branch route
* unweighted prime route
* weighted branch route
* weighted prime route
* provider branch route
* kernel branch route

と来た。

ここで、

* provider prime route
* kernel prime route

も整えるか、少なくとも kernel prime route を入れると、後で Markov 由来の prime process に自然接続しやすくなる。

特に Erdős #1196 の実際の流れは、prime / prime-power descent 側に寄る。
だから `kernelPrimePathFamilyAt` は早めに欲しい。

## 12. 総括

Phase W は、かなり大きな節目じゃ。

$$
\text{state}
\to
\text{WeightProvider}
\to
\text{WeightedPathFamily}
\to
\mathrm{weightedHitMass}\le C
$$

が no-sorry で閉じた。

山で言えば、これまでは「登山道に重みを載せる」段階だった。
今回からは「現在地によって、どの登山道へどれだけ流すか」を決める **分岐配給所** ができた。

次は、prime / dvd-monotone route へも同じ配給所をつなぐ。
その後で、いよいよ \(n\) を状態、\(q\) を除去因子、\(n/q\) を遷移先とする本格的な finite Markov model へ進むのが自然じゃ。
