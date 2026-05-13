# review

## 1. 結論

うむ、Phase AL は **finite toy weight の実地試験成功** じゃ。
前回 Phase AK で `withWeight` による重み差し替え口を作った。今回、その差し替え口を実際に使い、

$$
w(10,2)=1,\qquad w(10,5)=0
$$

という concrete toy weight を `sampleTenPrimePowerDivisorTransitionKernel` に載せ替え、さらに `PrimePowerChannelProvider.ofKernel` まで接続した。これで「素冪 channel を保ったまま、別の有限 toy weight を載せて sub-probability provider として扱う」流れが no-sorry で通ったわけじゃ。

## 2. 今回の主役

追加された中心はこの一連の流れじゃ。

```lean
sampleTenToyWeight
sampleTenToyWeight_nonneg
sampleTenToyWeightKernel
sampleTenToyWeightKernel_subProbability
sampleTenToyWeightChannelProvider
```

数学的には、

$$
sampleTenToyWeight(n,q)=
\begin{cases}
1 & n=10,\ q=2,\\
0 & \text{otherwise}
\end{cases}
$$

という重みを定義し、それが sample channel index 上で非負であることを示した。

そのうえで、

$$
sampleTenPrimePowerDivisorTransitionKernel.withWeight(sampleTenToyWeight)
$$

により、index / next / divisor semantics / prime-power channel 条件を保ったまま、weight だけを差し替えた。

これは Phase AK の `withWeight` が実際に機能することを示す、良い concrete test じゃ。

## 3. 何が保たれたか

今回の toy-weighted kernel では、重みだけが変わり、遷移構造は保たれている。

確認用 theorem として、

```lean
sampleTenToyWeightKernel_index_ten
sampleTenToyWeightKernel_next_two
sampleTenToyWeightKernel_next_five
```

が追加されている。

つまり、

$$
index(10)={2,5}
$$

は保たれ、

$$
10\xrightarrow{2}5,\qquad 10\xrightarrow{5}2
$$

も保たれている。

差し替わったのは、

$$
w(10,2)=1,\qquad w(10,5)=0
$$

という weight だけじゃ。

これは非常に重要。
今後 von-Mangoldt-like weight に差し替えるときも、下降路や素冪 channel の構造はそのままに、重みだけを変えられることになる。

## 4. sub-probability も閉じた

今回の核心の一つは、

```lean
sampleTenToyWeightKernel_subProbability
```

じゃ。

状態 $10$ では、

$$
w(10,2)+w(10,5)=1+0=1
$$

それ以外の状態では index が空なので、総重みは $0$。
したがって全状態で

$$
\sum_{q\in index(n)}w(n,q)\le 1
$$

が成立する。

つまり、この toy weight はちゃんと finite sub-probability channel になっている。

これで、

$$
\text{prime-power channel}
+
\text{toy weight}
+
\text{sub-probability}
$$

が `PrimePowerChannelProvider` に乗るところまで到達した。

## 5. `PrimePowerChannelProvider` への接続

最後に、

```lean
sampleTenToyWeightChannelProvider
```

が追加されている。

これは、

$$
sampleTenToyWeightKernel
$$

と

$$
sampleTenToyWeightKernel.SubProbability
$$

を使って、

```lean
PrimePowerChannelProvider.ofKernel
```

へ接続したものじゃ。

つまり Phase AJ / AK で作った受付カウンターに、今回の toy weight を正式登録できた。

ここまで通ったことで、今後の流れはかなり明確になった。

$$
\text{PrimePowerDivisorTransitionKernel}
$$

$$
\xrightarrow{\text{withWeight}}
\text{toy-weighted kernel}
$$

$$
\xrightarrow{\text{subProbability}}
\text{PrimePowerChannelProvider}
$$

$$
\to
\text{weighted hit mass bound}
$$

この道が具体例で開通した。

## 6. 現在地

いまの進捗はこうじゃ。

| 層                                           | 状態   |
| ------------------------------------------- | ---- |
| `DivisorTransitionKernel`                   | 完了   |
| `PrimePowerDivisorTransitionKernel`         | 完了   |
| `PrimePowerChannelProvider`                 | 完了   |
| `withWeight`                                | 完了   |
| concrete finite toy weight                  | 今回完了 |
| toy-weighted channel provider               | 今回完了 |
| weighted hit mass bound への concrete theorem | 未    |
| witness-dependent toy weight                | 未    |
| von-Mangoldt-like weight                    | 未    |
| analytic $\Lambda(q)/\log n$                | 未    |

Phase AL により、toy weight は「設計上できるはず」から「実際に Lean で通る」へ進んだ。

## 7. 次の一手

次は History にある通り、toy weight provider が既存 weighted hit mass bound に入る concrete theorem を追加するのが自然じゃ。

つまり、今回作った

```lean
sampleTenToyWeightChannelProvider
```

を使って、

$$
\mathrm{weightedHitMass}\le 1
$$

のような theorem を実際に呼ぶ。

候補はこうじゃ。

```lean
theorem sampleTenToyWeightChannelProvider_hitMass_le_one :
    ...
```

あるいは `ErdosFinitePrimitiveInput` 側の sample と接続するなら、

```lean
theorem erdosFinitePrimitiveInput_two_five_sampleTenToyWeight_hitMass_le_one :
    ...
```

のような形じゃな。

これが閉じると、

$$
\text{toy weight}
\Rightarrow
\text{channel provider}
\Rightarrow
\text{weighted hit mass bound}
$$

まで concrete に完成する。

## 8. その次に見える課題

その次は、いよいよ **prime-power witness に依存する weight** じゃ。

今の toy weight は手定義で、

$$
(n,q)=(10,2)
$$

だけに重み $1$ を置いた。

次は、

$$
q=p^k
\Rightarrow
w(n,q)=c(p,n)
$$

のような形式へ進む。

ただし注意点として、`IsPrimePowerLabel q` は存在命題なので、Lean 上で $p$ をどう選ぶかが問題になる。
本物の von Mangoldt weight へ進むには、prime-power 表現の一意性や代表選択をどう扱うかが山場になるじゃろう。

だから次の一歩は、まだ本物の $\Lambda$ ではなく、

$$
\text{witness を明示的に渡す toy weight}
$$

または

$$
\text{finite index 上に手で weight を与える generalized constructor}
$$

が安全じゃ。

## 9. 総括

Phase AL は、素冪 channel に **実際の toy 通行料** を載せた段階じゃ。

前回までは、料金表を差し替えられる掲示板ができた。
今回、その掲示板に実際の料金表

$$
2\mapsto 1,\qquad 5\mapsto 0
$$

を貼り、sub-probability provider として登録できた。

山で言えば、素冪専用ルートの受付で、初めて具体的な通行料プランが運用開始された。
次は、その通行料プランを使って、既存の weighted hit mass bound まで実際に通す番じゃな。
