# review

## 1. 結論

うむ、Phase AM は **toy weight が実際に weighted hit mass bound まで通った段階** じゃ。
Phase AL では、

$$
\text{withWeight}
\to
\text{ofKernel}
\to
\text{PrimePowerChannelProvider}
$$

まで接続できていた。今回 Phase AM ではさらに、

$$
\text{toy-weighted channel provider}
\to
\text{SourceControlledChainFamily}
\to
\mathrm{weightedHitMass}\le 1
$$

まで concrete theorem として閉じた。つまり、有限 toy weight が「登録できる」だけでなく、既存の hitting bound の本線を実際に走れることが確認されたのじゃ。

## 2. 今回の主役

今回追加された中心はこの二つじゃ。

```lean
sampleTenToyWeightSourceControlledFamily
sampleTenToyWeightChannelProvider_hitMass_le_one
```

`sampleTenToyWeightSourceControlledFamily` は、state $10$ の toy-weighted channel と同じ index

$$
{2,5}
$$

を持つ `SourceControlledChainFamily unitNatMassSpace ℕ` じゃ。各 label $q$ に singleton chain $\{q\}$ を割り当て、source は常に $10$ にしている。

つまり、

$$
q\in{2,5}
\quad\mapsto\quad
C_q={q},\qquad source(q)=10
$$

という、とても小さいが意味のはっきりした source-controlled forest になっておる。

## 3. 何が閉じたか

今回の theorem は、

```lean
sampleTenToyWeightChannelProvider_hitMass_le_one
```

じゃ。

内容は、toy weight を載せ替えた channel provider を `sampleTenToyWeightSourceControlledFamily` に適用し、primitive set $\{2,5\}$ に対する weighted hit mass が

$$
\le 1
$$

であることを示している。

導線はこうじゃ。

$$
\text{sampleTenToyWeight}
$$

$$
\to
\text{sampleTenToyWeightKernel}
$$

$$
\to
\text{sampleTenToyWeightChannelProvider}
$$

$$
\to
\text{applyAtToSourceControlled}
$$

$$
\to
\mathrm{weightedHitMass}\le 1
$$

これはまさに History にある通り、

```text
withWeight -> ofKernel -> applyAtToSourceControlled -> weightedHitMass <= 1
```

が no-sorry で通った、ということじゃ。

## 4. compatibility の山場

今回の小さな山場は compatibility 証明じゃな。

最初は `simp` だけでは閉じず、

```lean
change sampleTenToyWeightKernel.toDivisorTransitionKernel.index 10 =
  sampleTenToyWeightSourceControlledFamily.index
```

で index equality に落としてから `simp` で解いている。

これは良い修正じゃ。
今回の compatibility は本質的に、

$$
sampleTenToyWeightKernel.\text{index}(10) = \{2,5\} = sampleTenToyWeightSourceControlledFamily.\text{index}
$$

という index 一致条件じゃから、`change` で目標を正しい形に露出させるのは Lean 的にも読みやすい。

今後、この形が頻出するなら、`CompatibleAt` 系の補題や sample 専用 simp 補題を増やす価値があるかもしれぬ。

## 5. 今回の数学的意味

今回の結果は小さな sample に見えるが、構造的には大きい。

これまでの流れは、

$$
\text{prime-power channel}
+
\text{toy weight}
+
\text{sub-probability}
$$

までだった。

今回、それが

$$
\text{primitive hitting bound}
$$

に実際に接続された。

つまり、

$$
\text{有限 toy weight}
\Rightarrow
\text{weighted hit mass bound}
$$

という本来の目的地まで、一度 concrete に到達したことになる。

これは、von-Mangoldt-like weight へ進む前の実験路としてかなり重要じゃ。
なぜなら後で重みを

$$
w_{\mathrm{toy}}(n,q)
$$

から

$$
w_{\Lambda\text{-like}}(n,q)
$$

へ替えても、同じ `PrimePowerChannelProvider` / `applyAtToSourceControlled` / `weightedHitMass` route を使える見込みが立つからじゃ。

## 6. 現在地

いまの階層はこうじゃ。

| 層                                        | 状態   |
| ---------------------------------------- | ---- |
| `PrimePowerDivisorTransitionKernel`      | 完了   |
| `PrimePowerChannelProvider`              | 完了   |
| `withWeight`                             | 完了   |
| concrete finite toy weight               | 完了   |
| toy-weighted channel provider            | 完了   |
| toy weight → weighted hit mass bound     | 今回完了 |
| finite index 上の手定義 weight 一般 constructor | 未    |
| witness-dependent toy weight             | 未    |
| von-Mangoldt-like finite weight          | 未    |
| analytic $\Lambda(q)/\log n$             | 未    |

これで finite toy weight route は、かなり一段落じゃな。

## 7. 次の一手

次は History にある通り、witness-dependent toy weight へ行く前に、 **finite index 上の手定義 weight を一般化する constructor** を検討するのがよい。

今は sample 専用に、

$$
w(10,2)=1,\qquad w(10,5)=0
$$

を直接書いた。

次は、より一般に、

$$
w : \mathbb{N}\to\mathbb{N}\to\mathbb{Q}
$$

を与えて、

1. index 上で非負
2. 各 state で総和が $1$ 以下
3. `withWeight` で差し替え
4. `PrimePowerChannelProvider.ofKernel` で package 化

まで行う constructor があるとよい。

候補名は例えば、

```lean
PrimePowerChannelProvider.ofWeight
```

または、より正確に、

```lean
PrimePowerChannelProvider.ofKernelWithWeight
```

じゃな。

## 8. 次 Phase 案

わっちなら Phase AN はこう切る。

**Phase AN: general finite toy weight constructor**

目的：

`PrimePowerDivisorTransitionKernel` と任意の手定義 weight $w$ から、非負性と sub-probability を仮定して `PrimePowerChannelProvider` を作る。

候補 API はこうじゃ。

```lean
def PrimePowerChannelProvider.ofKernelWithWeight
    (T : PrimePowerDivisorTransitionKernel)
    (w : ℕ → ℕ → ℚ)
    (hw_nonneg :
      ∀ n q, q ∈ T.toDivisorTransitionKernel.index n → 0 ≤ w n q)
    (hw_subprob :
      (T.withWeight w hw_nonneg).SubProbability) :
    PrimePowerChannelProvider :=
  PrimePowerChannelProvider.ofKernel
    (T.withWeight w hw_nonneg)
    hw_subprob
```

これがあると、sample theorem はかなり短くなる。
そして後で von-Mangoldt-like weight を作る時も、

$$
w_{\Lambda\text{-like}}
$$

をこの constructor に渡すだけでよくなる。

## 9. その次に見える山

その後はいよいよ、

$$
q=p^k
\Rightarrow
w(n,q)\text{ depends on }p
$$

という witness-dependent toy weight じゃ。

ただし、ここは慎重に進むべきじゃ。
`IsPrimePowerLabel q` は存在命題なので、Lean 上で $p$ をどう選ぶか、あるいは $p,k$ を label 側に構造として持たせるかが問題になる。

安全な候補は二つある。

一つ目は、label を単なる $q$ ではなく、

```lean
structure PrimePowerLabel where
  q : ℕ
  p : ℕ
  k : ℕ
  prime : Nat.Prime p
  k_pos : 0 < k
  eq_pow : q = p ^ k
```

のように構造化する道。

二つ目は、今の $\mathbb{N}$ label のまま、weight を外から手定義し、 $\Lambda$-like 性質だけを predicate として持つ道。

今の流れなら、まず後者の方が軽いじゃろう。

## 10. 総括

Phase AM は、素冪 channel の toy weight が **実際の mass bound まで走った** 段階じゃ。

山で言えば、前回までは料金表を受付に登録できた。
今回、その料金表を使って、実際に登山道の通行量制限

$$
\mathrm{weightedHitMass}\le 1
$$

を通過できた。

これは小さな sample だが、登山ルートとしては大きい。
次は、手書き料金表を一般化する `ofKernelWithWeight` のような constructor を作るのが賢い一手じゃな。
