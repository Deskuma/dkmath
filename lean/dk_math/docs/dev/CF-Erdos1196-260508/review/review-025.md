# review

## 1. 結論

うむ、Phase Z は **actual finite transition skeleton の初到達** じゃ。
これまでの `FiniteKernel` は、

$$
\text{state}
\to
\text{index}
\to
\text{weight}
$$

までだった。今回 `FiniteTransitionKernel` によって、

$$
\text{state}
\to
\text{index}
\to
\text{next state}
$$

が入った。つまり、有限 Markov skeleton が「重み配布装置」から、 **遷移先を持つ kernel** へ昇格したのじゃ。

## 2. 今回の主役

新規ファイルはこれじゃ。

```lean
DkMath/NumberTheory/PrimitiveSet/FiniteTransitionKernel.lean
```

中心構造は、

```lean
structure FiniteTransitionKernel (σ ι : Type _) [DecidableEq ι] where
  index : σ → Finset ι
  next : σ → ι → σ
  weight : σ → ι → ℚ
  weight_nonneg : ∀ s i, i ∈ index s → 0 ≤ weight s i
```

これで、状態 (s) から label (i) を選び、

$$
s \xrightarrow{i} next(s,i)
$$

へ進む有限遷移を表せるようになった。

重要なのは、まだ (next) に数論的意味を押し込んでいない点じゃ。
今は抽象的に、

$$
s,; i,; next(s,i),; weight(s,i)
$$

を持つだけ。これは正しい。解析重みや素因子条件をここで混ぜると一気に重くなるからの。

## 3. 既存 skeleton への接続が綺麗

今回の良いところは、`FiniteTransitionKernel` を新しく作りながら、証明力は既存の `FiniteKernel` / `WeightProvider` / `WeightedPathFamily` に流している点じゃ。

その橋がこれ。

```lean
def toFiniteKernel
```

つまり、

$$
\text{FiniteTransitionKernel}
\to
\text{FiniteKernel}
$$

で、遷移先 `next` を忘却して、重み評価だけを既存 theorem に渡す。

この設計は賢い。
`next` を持つ構造へ昇格しつつ、既存の weighted hit mass bound を作り直さずに済む。

導線はこうじゃ。

$$
\text{FiniteTransitionKernel}
\to
\text{FiniteKernel}
\to
\text{WeightProvider}
\to
\text{WeightedPathFamily}
\to
\mathrm{weightedHitMass}\le C
$$

## 4. 今回閉じた theorem

今回の中心 theorem は、

```lean
FiniteTransitionKernel.weightedHitMass_le_const_of_subprob_applyAtToSourceControlled
```

じゃ。

内容は、transition kernel が sub-probability で、source-controlled family と compatible で、source mass が一様に (C) 以下なら、

$$
\mathrm{weightedHitMass}\le C
$$

が出る、というもの。

つまり、Phase U/V/W/Y で作ってきた定理列が、transition kernel からも呼べるようになった。

これは大きい。
ただの構造追加ではなく、 **transition kernel 経由でも hit mass bound へ到達できる** ところまで閉じておる。

## 5. ErdosFinite 側の wrapper

`ErdosFinitePrimitiveInput` 側にも、

```lean
transitionBranchPrimePathFamilyAt
transitionBranchPrimePathFamilyAt_hitMass_le_const_of_subprob
```

が追加された。

つまり、finite Erdős input (I)、branch-controlled path family (F)、transition kernel (T)、状態 (s) から、

$$
\mathrm{weightedHitMass}(I,F,T,s)\le C
$$

を theorem-facing に呼べる。

ここまで来ると、かなり Markov らしい姿じゃ。
まだ確率論・解析ではないが、

$$
\text{状態から重み付き遷移を出し、それを path family の hitting bound に渡す}
$$

という構文はもう完成している。

## 6. concrete sample の意味

sample は、

```lean
sampleUnitTransitionKernel
sampleUnitTransitionKernel_subProbability
erdosFinitePrimitiveInput_two_five_transitionBranch_hitMass_le_one
```

じゃ。

これは Unit 状態から Bool label を出し、

$$
w_{\mathrm{false}}=\frac13,\qquad
w_{\mathrm{true}}=\frac23
$$

を割り当て、`next` は常に `()` に戻る簡単な transition kernel じゃ。

この kernel で branch route に載せて、

$$
\mathrm{weightedHitMass}\le 1
$$

が確認されておる。

つまり、

$$
\text{state}
\to
\text{index}
\to
\text{next state}
\to
\text{weight}
\to
\text{hit mass bound}
$$

の全線が concrete sample で通った。空抽象ではないのがよい。

## 7. 現在地

ここまでで、Erdős #1196 宇宙式ルートの有限 skeleton はこうなった。

| 層                                  | 状態   |
| ---------------------------------- | ---- |
| primitive hitting                  | 完了   |
| path family / forest               | 完了   |
| source-controlled mass             | 完了   |
| weighted path family               | 完了   |
| WeightProvider                     | 完了   |
| FiniteKernel                       | 完了   |
| FiniteTransitionKernel             | 今回完了 |
| transition branch route wrapper    | 今回完了 |
| transition prime route wrapper     | 未    |
| divisor / prime descent transition | 未    |
| analytic weight                    | 未    |

今回で、有限 Markov skeleton は **かなり明確に立った** と言える。

## 8. 残っている注意点

`FiniteTransitionKernel` は `next` を持つが、まだその `next` は hit mass bound の証明には使われていない。

これは欠陥ではなく、今の段階では設計上の分離じゃ。

現状では、

$$
next
$$

は「将来の遷移意味論」の席だけを確保している。
重み評価は `toFiniteKernel` で既存 route に流している。

次の段階で、

$$
next(n,q)=n/q
$$

のような意味を入れると、この `next` が本当に働き始める。

## 9. 次の一手

次は History にある通り、まず **transition prime route wrapper** を追加して対称化するのが安全じゃ。

今あるのは branch route 側。

```lean
transitionBranchPrimePathFamilyAt
transitionBranchPrimePathFamilyAt_hitMass_le_const_of_subprob
```

次に欲しいのは、

```lean
transitionPrimePathFamilyAt
transitionPrimePathFamilyAt_hitMass_le_const_of_subprob
```

じゃな。

これで、

| transition route | source control        |
| ---------------- | --------------------- |
| branch route     | `SubConservative M B` |
| prime route      | `DvdMonotoneMass M`   |

が揃う。

この対称化を済ませてから、

$$
\sigma := \mathbb{N},\qquad
\iota := \text{除去因子}
$$

へ進むのがよい。

## 10. その次の山道

対称化が済んだら、いよいよ数論的 transition skeleton じゃ。

候補は、

```lean
FiniteDivisorTransitionKernel
PrimeDescentTransitionKernel
PrimePowerTransitionKernel
```

のような層。

最小形は、

$$
q\in index(n)\Rightarrow q\mid n
$$

と、

$$
next(n,q)=n/q
$$

を持つ構造じゃな。

ただし、まだ

$$
w(n,q)=\frac{\Lambda(q)}{\log n}
$$

は入れない。
最初は有理重みのまま、

$$
q\mid n
$$

と

$$
next(n,q)=n/q
$$

だけを Lean に刻むのがよい。

## 11. 総括

Phase Z は、かなり大きな節目じゃ。

これまでの有限 kernel は「重みを配る」だけだった。
今回からは「次にどこへ行くか」も持った。

山で言えば、配給所がついに **道案内付きの分岐所** になった。
まだ道の名前は抽象的だが、次はその道標に

$$
n\to n/q
$$

と書き込む段階じゃな。
