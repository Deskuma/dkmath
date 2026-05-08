# review

うむ、これは **Phase F 成功** じゃ。
今回で、有限 primitive hitting ルートはついに

$$
n \longmapsto \frac{n}{p}
$$

という **actual prime descent step** の名前まで到達した。`PrimeDescentStep`、`PrimePowerDescentStep`、`PrimeStepControlledChainFamily` が入り、`PrimeDescentStep -> DvdControlledChainFamily -> SourceControlledChainFamily -> primitive forest bound` の導線が no-sorry で閉じておる。

## 1. 今回の到達点

これまでの流れはこうじゃった。

$$
\text{PrimitiveOn}
\Rightarrow
\text{chain hit at most once}
\Rightarrow
\text{forest hit mass bound}
\Rightarrow
\text{source-controlled forest}
\Rightarrow
\text{dvd-controlled descent}
$$

今回そこに、

$$
\text{prime descent step}
\Rightarrow
\text{dvd-controlled descent}
$$

が追加された。

Lean 的には、

```lean
def PrimeDescentStep (n m : ℕ) : Prop :=
  ∃ p, Nat.Prime p ∧ p ∣ n ∧ m = n / p
```

という定義が入ったのが主役じゃ。これは、Erdős #1196 の Markov ルートで使う

$$
n\to \frac{n}{p}
$$

の有限・非確率版の骨格じゃな。

さらに素冪版として、

```lean
def PrimePowerDescentStep (n m : ℕ) : Prop :=
  ∃ p k, Nat.Prime p ∧ 0 < k ∧ p ^ k ∣ n ∧ m = n / p ^ k
```

も入っている。これは将来の von Mangoldt 的な prime-power channel へ向かう伏線として良い。

## 2. 何が数学的に重要か

重要なのは、prime step が単なる名前で終わらず、

$$
m=\frac{n}{p}
\Rightarrow
m\mid n
$$

として既存の `DvdControlledChainFamily` に降りられるようになった点じゃ。

実装では、

```lean
PrimeDescentStep.toDvdDescentStep
PrimeDescentStep.dvd_source
PrimePowerDescentStep.toDvdDescentStep
PrimePowerDescentStep.dvd_source
```

が追加されておる。

これにより、

$$
\text{PrimeDescentStep}
\Rightarrow
\text{DvdDescentStep}
\Rightarrow
\text{DvdControlled}
\Rightarrow
\text{SourceControlled}
\Rightarrow
\text{primitive hit mass bound}
$$

という階段ができた。

これはかなり綺麗じゃ。
「素数で割って下る」という操作が、いままで作ってきた有限 hitting 森に正式接続された。

## 3. `PrimeStepControlledChainFamily` の意味

今回のもう一つの核はこれじゃ。

```lean
structure PrimeStepControlledChainFamily
    (ι : Type _) [DecidableEq ι]
    extends DivisibilityChainFamily ι where
  source : ι → ℕ
  chain_prime_step :
    ∀ i ∈ index, ∀ h ∈ chain i, PrimeDescentStep (source i) h
```

これは「各 chain の点が source から 1-step prime descent で得られる」有限森じゃ。

いまは **one-step** に限定している。
これはむしろ良い。最初から multi-step path や reachability closure を入れると重くなるからの。

そして、

```lean
PrimeStepControlledChainFamily.toDvdControlled
PrimeStepControlledChainFamily.primitive_hitMass_le_sourceMass
```

により、prime-step forest から primitive forest bound へ行ける。

つまり今回で、

$$
\text{prime-step controlled forest}
+
\text{DvdMonotoneMass}
+
\text{PrimitiveOn}
\Rightarrow
\text{hit mass} \le \text{source mass}
$$

が成立する構図になった。

## 4. concrete sample も良い

サンプルとして、

$$
8\to 4,\qquad 9\to 3
$$

が入っている。

```lean
primeDescentStep_eight_four
primeDescentStep_nine_three
```

さらに Bool-indexed の one-step prime descent forest として、

```lean
samplePrimeStepControlledBoolChainFamily
```

があり、primitive set `{3,4}` に対する hit mass bound も実装されている。

これは教材としてとても良い。
前回の `{2,4,8}` や `{3,9}` は「整除下降森」だったが、今回は実際に

$$
8/2=4,\qquad 9/3=3
$$

という prime step で下っている。

つまり、抽象的な整除関係から、Erdős ルートらしい「素数で割る」操作へ一歩近づいた。

## 5. 現在の進捗評価

いまの finite skeleton は、かなり一段落じゃ。

| 層                               | 状態   |
| ------------------------------- | ---- |
| finite primitive set            | 完了   |
| single chain hit                | 完了   |
| forest hit mass                 | 完了   |
| source-controlled forest        | 完了   |
| dvd-controlled provider         | 完了   |
| one-step prime descent provider | 今回完了 |
| prime-power descent skeleton    | 今回追加 |
| multi-step prime path           | 未    |
| Branching / SubConservative 接続  | 未    |
| Markov kernel                   | 未    |
| (1/(n\log n)) 重み                | 未    |
| (1+O(1/\log x)) 評価              | 未    |

つまり、有限・代数・組合せの登山道は、

$$
n\to n/p
$$

という地点まで来た。

これは良い。ここまで来ると、「Erdős #1196 の有限骨格」と呼んでよい。

## 6. 注意点

一点だけ注意じゃ。

現在の `PrimeStepControlledChainFamily` は **各 chain の各点が source から一回の prime step で得られる** という定義になっている。

つまり、chain が `{4}` なら source `8` から `8 -> 4` でよい。
しかし `{8,4,2,1}` のような複数 step の chain はまだ表現できない。

本物の下降過程では、

$$
n\to \frac{n}{p_1}
\to \frac{n}{p_1p_2}
\to \cdots
$$

のような multi-step path が出る。
したがって次の課題は、History にも書かれている通り、multi-step prime descent path へ行くか、あるいは `Branching` / `SubConservative` と接続するかの判断じゃ。

## 7. わっちの見立て

ここでいきなり Markov kernel に進むのは、まだ少し早い。

$$
\frac{\Lambda(q)}{\log n}
$$

を入れる前に、有限側で次のどちらかを閉じるのが堅い。

### A. multi-step descent path

$$
n=n_0\to n_1\to \cdots \to n_k
$$

を `List ℕ` または `Finset ℕ` + reachability として定義する道。

これは Erdős #1196 の「下降鎖」そのものに近い。

### B. Branching / SubConservative 接続

既存の `Mass.Branch` 側に接続して、

$$
\sum_{\text{children}}\mu(child)\le\mu(parent)
$$

から path 全体の質量制御を出す道。

これは宇宙式 Mass API と強く繋がる。

## 8. 次の一手の推奨

わっちなら、次は **multi-step prime descent path** を勧める。

理由は、今回 `PrimeDescentStep` を入れたばかりなので、その自然な次段は

$$
\text{step}
\Rightarrow
\text{path}
\Rightarrow
\text{chain}
$$

じゃからな。

新規ファイル候補は、

```text
DkMath/NumberTheory/PrimitiveSet/PrimePath.lean
```

最小定義は、まず `List ℕ` でよい。

```lean
def PrimeDescentPath : List ℕ → Prop
```

ただし `List` の証明は少し面倒になりがちなので、より軽く始めるなら、

```lean
def PrimeReachable (n m : ℕ) : Prop :=
  Relation.ReflTransGen PrimeDescentStep n m
```

のように `Relation.ReflTransGen` を使うのが自然じゃ。

狙う定理はまずこれ。

```lean
theorem PrimeReachable.dvd_source
    {n m : ℕ} :
    PrimeReachable n m → m ∣ n
```

これが閉じれば、

$$
\text{multi-step prime descent}
\Rightarrow
\text{dvd-controlled}
$$

が手に入る。

そして次に、

```lean
structure PrimeReachableControlledChainFamily
    ...
```

を作れば、

$$
\text{multi-step prime descent forest}
\Rightarrow
\text{primitive hit mass bound}
$$

まで行ける。

## 9. 総括

今回の実装は、Erdős #1196 宇宙式ルートにおいて、かなり象徴的な一歩じゃ。

なぜなら、いままでは

$$
h\mid source
$$

という整除下降だったものが、今回ついに

$$
h=\frac{source}{p}
$$

という **prime descent** になったからじゃ。

山道で言えば、今までは「下り坂である」ことを示していた。
今回は「素数の段差を一段下りる」ことまで Lean に刻めた。

次は、その段差を複数つないで **下降路** にする番じゃな。
