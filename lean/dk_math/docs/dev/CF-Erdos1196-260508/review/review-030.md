# review

## 1. 結論

うむ、Phase AE は **prime-power label の API 化** じゃ。
Phase AD では、

$$
q=p^k,\quad p\text{ prime},\quad 0 < k
$$

を毎回明示して `PrimePowerDescentStep` に接続していた。今回 Phase AE では、それを

```lean
IsPrimePowerLabel q
```

という predicate に切り出した。これで後続の channel / weight 層は、毎回 $p,k$ を展開せず、

$$
q\text{ は prime-power label}
$$

という一つの仮定だけで進めるようになった。これは $\Lambda(q)$ ルートの入口として、とてもよい整備じゃ。

## 2. 今回の主役

追加された定義はこれじゃ。

```lean
def IsPrimePowerLabel (q : ℕ) : Prop :=
  ∃ p k, Nat.Prime p ∧ 0 < k ∧ q = p ^ k
```

数学的には、

$$
\mathrm{IsPrimePowerLabel}(q)
\Longleftrightarrow
\exists p,k,\quad p\text{ prime}\land 0 < k\land q=p^k
$$

じゃな。

これは、von Mangoldt 型 weight の有限前段としてかなり自然じゃ。
なぜなら $\Lambda(q)$ が非零になるのは、まさに $q$ が素冪 $p^k$ のときだからじゃ。

まだ $\Lambda$ そのものは入れていない。
しかし、「 $\Lambda$ が反応する label」を識別する predicate は入った。

## 3. 何が強くなったか

今回追加された wrapper はこれじゃ。

```lean
DivisorTransitionKernel.primePowerDescentStep_of_isPrimePowerLabel
```

これにより、

$$
q\in T.index(n),
\qquad
\mathrm{IsPrimePowerLabel}(q)
$$

から、

$$
\mathrm{PrimePowerDescentStep}; n; (T.next\ n\ q)
$$

が出る。

以前は theorem 呼び出し側が

$$
p,\quad k,\quad Nat.Prime(p),\quad 0 < k,\quad q=p^k
$$

を全部渡す必要があった。
今回からは、それらを `IsPrimePowerLabel q` の中に畳める。

これは Lean API として大きい。
後続の theorem は、細かい witness 分解ではなく、

```lean
hqpp : IsPrimePowerLabel q
```

を持てばよくなる。

## 4. 低レベル補題を残したのも良い

既存の

```lean
primePowerDescentStep_of_primePow_label
```

は残されておる。

これは良い設計じゃ。
低レベルでは $p,k$ を明示して証明したい場面がある。一方、高レベルでは `IsPrimePowerLabel q` だけで使いたい。

つまり API が二層になった。

| 層    | theorem                                      | 使い所                              |
| ---- | -------------------------------------------- | -------------------------------- |
| 低レベル | `primePowerDescentStep_of_primePow_label`    | $p,k$ が明示されているとき                 |
| 高レベル | `primePowerDescentStep_of_isPrimePowerLabel` | label が prime-power であることだけを使うとき |

この二層化は、後で weight/channel 層を作るときに効く。

## 5. sample の意味

sample として、

```lean
sampleTenDivisorTransitionKernel_isPrimePowerLabel_two
sampleTenDivisorTransitionKernel_isPrimePowerLabel_five
```

が追加された。

これは、

$$
2=2^1,\qquad 5=5^1
$$

として、sample kernel の label $2,5$ が prime-power label であることを確認している。

さらに既存の prime-power descent sample も、新しい wrapper 経由に変更された。

つまり、

$$
IsPrimePowerLabel(q)
\Rightarrow
PrimePowerDescentStep
$$

という新 API が、実例でも通っている。

これは良い。単なる predicate 追加で終わらず、既存 theorem の呼び出し形を実際に改善しておる。

## 6. 現在地

ここまでの descent / transition skeleton はこうじゃ。

| 層                                           | 状態   |
| ------------------------------------------- | ---- |
| `FiniteTransitionKernel`                    | 完了   |
| `DivisorTransitionKernel`                   | 完了   |
| $q\mid n$, $next=n/q$                       | 完了   |
| prime label → `PrimeDescentStep`            | 完了   |
| prime-power label → `PrimePowerDescentStep` | 完了   |
| `IsPrimePowerLabel`                         | 今回完了 |
| index-level prime-power predicate           | 未    |
| von Mangoldt channel                        | 未    |
| analytic weight                             | 未    |

今は、個々の label $q$ を prime-power と認識できる段階じゃ。
次は、index 全体が prime-power label だけから成ることを表す段階に進める。

## 7. 次の一手

次は History にもある通り、

```lean
PrimePowerIndexOn T n
```

を入れるのが自然じゃ。

定義案はこう。

```lean
def PrimePowerIndexOn (T : DivisorTransitionKernel) (n : ℕ) : Prop :=
  ∀ q ∈ T.index n, IsPrimePowerLabel q
```

これにより、

$$
\forall q\in index(n),\quad q\text{ is prime-power}
$$

を一つの仮定として持てる。

すると次の theorem が自然に書ける。

```lean
theorem primePowerDescentStep_of_primePowerIndexOn
    (T : DivisorTransitionKernel) {n q : ℕ}
    (hT : PrimePowerIndexOn T n)
    (hqmem : q ∈ T.index n) :
    PrimePowerDescentStep n (T.next n q)
```

これは単に、

$$
hT(q,hqmem)
$$

で `IsPrimePowerLabel q` を取り出し、今回の

```lean
primePowerDescentStep_of_isPrimePowerLabel
```

へ渡せば閉じるはずじゃ。

## 8. その次に見える設計

`PrimePowerIndexOn` が入ると、次は channel / weight 層に進める。

たとえば、有限 kernel の index がすべて prime-power label であることを持つ構造：

```lean
structure PrimePowerDivisorTransitionKernel where
  toDivisorTransitionKernel : DivisorTransitionKernel
  primePower_index :
    ∀ n q, q ∈ toDivisorTransitionKernel.index n → IsPrimePowerLabel q
```

あるいは、構造体を増やさず predicate だけで進めるなら、

```lean
def PrimePowerIndexed (T : DivisorTransitionKernel) : Prop :=
  ∀ n, PrimePowerIndexOn T n
```

でもよい。

わっちならまずは軽く、

```lean
PrimePowerIndexOn
PrimePowerIndexed
```

の二つを置く。
構造体化は、その後に theorem が増えてからでよい。

## 9. von Mangoldt への距離

今回で $\Lambda(q)$ への距離はかなり縮まった。

Erdős #1196 の downward process では、重みは概念的に

$$
w(n,q)=\frac{\Lambda(q)}{\log n}
$$

じゃが、その前に必要なのは、

$$
q\text{ が prime-power である}
$$

という channel 判定じゃ。

今回の `IsPrimePowerLabel` は、その channel 判定の最小核になっている。

まだやるべきことは、

1. index 全体が prime-power であることを表す。
2. prime-power label から $p$ と $k$ を取り出す API を整える。
3. その後に $\Lambda(q)$ 相当の有限重みを設計する。

この順番が安全じゃ。

## 10. 総括

Phase AE は、素冪 label を **通行証化** した段階じゃ。

これまでは、

$$
q=p^k
$$

という証拠を毎回手で持ってきていた。
今回からは、

$$
IsPrimePowerLabel(q)
$$

という一枚の通行証で prime-power descent に入れる。

山で言えば、前回は「この道は $p^k$ と書かれている」と毎回説明していた。
今回からは「素冪道 通行証」を見せれば通れる。

次は、その通行証を各 index が全員持っていること、つまり `PrimePowerIndexOn` を作る番じゃな。
