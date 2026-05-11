# review

## 1. 結論

うむ、Phase AX は **witness-provider-driven weight の標準 constructor 完成** じゃ。
ここでかなり大きな橋が架かった。

これまでの流れは、

$$
\text{PrimePowerWitnessProvider}
\to
w(n,q)=c(n,p)
\to
\text{PrimeWitnessDependentWeight}
\to
\text{PrimePowerChannelProvider}
$$

という理論的導線だった。今回、

```lean
PrimePowerChannelProvider.ofWitnessProviderWeight
```

が入ったことで、この導線が一つの constructor として固定された。

つまり、今後は

$$
W:\text{PrimePowerWitnessProvider}(T)
$$

と base-prime weight

$$
c(n,p)
$$

を与えれば、label weight

$$
w(n,q)=c(n,p(q))
$$

を内部で作り、`PrimeWitnessDependentWeight` を経由して `PrimePowerChannelProvider` まで持っていける。

これは、(\Lambda(q)=\log p) の「(p) に依存する」構造へ向かうためのかなり重要な足場じゃ。

## 2. 今回の主役

追加された中心 API はこれじゃ。

```lean
def PrimePowerChannelProvider.ofWitnessProviderWeight
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (c : ℕ → ℕ → ℚ)
    (hc_nonneg :
      ∀ n q (hq : q ∈ T.toDivisorTransitionKernel.index n),
        0 ≤ c n ((W.label n q hq).p))
    (hw_subprob :
      (T.withWeight (W.weightOfBase c)
        (T.vonMangoldtLikeWeight_nonneg
          (T.vonMangoldtLikeWeight_of_primeWitnessDependent
            (W.weightOfBase_primeWitnessDependent c hc_nonneg)))).SubProbability) :
    PrimePowerChannelProvider
```

少し長いが、意味は美しい。

$$
c(n,p)\ge 0
$$

を index 上で示し、さらに `W.weightOfBase c` で作った weight が sub-probability なら、provider が得られる。

つまり、

$$
c(n,p)
$$

を入力して、

$$
w(n,q)=c(n,(W.label(n,q,hq)).p)
$$

を作り、それを channel provider にする標準入口じゃ。

## 3. 何が強くなったか

Phase AW では、

```lean
W.weightOfBase c
```

が `PrimeWitnessDependentWeight` に乗るところまで閉じていた。

今回 Phase AX では、それをさらに

```lean
PrimePowerChannelProvider
```

まで直接つないだ。

導線はこうじゃ。

$$
c(n,p)
$$

$$
\longmapsto
W.weightOfBase(c)(n,q)
$$

$$
\longmapsto
T.PrimeWitnessDependentWeight(W.weightOfBase(c),c)
$$

$$
\longmapsto
PrimePowerChannelProvider
$$

これで「base prime (p) 依存 weight を provider として使う」道が一般 API になった。

## 4. simp API も良い

今回追加された simp 補題も重要じゃ。

```lean
ofWitnessProviderWeight_kernel
ofWitnessProviderWeight_channelProviderAt_index
ofWitnessProviderWeight_channelProviderAt_weight
```

特に、

$$
\bigl(\mathrm{ofWitnessProviderWeight}(W,c,\ldots).\mathrm{channelProviderAt}(n)\bigr).\mathrm{weight} = W.weightOfBase(c)(n)
$$

が `[simp]` で取れるのは大きい。

今後 sample や一般定理で、

$$
\text{この provider の weight は本当に }W.weightOfBase(c)\text{ か？}
$$

を確認したい場面が出る。そこを `simp` で処理できる。

これは後続の証明摩擦をかなり減らすじゃろう。

## 5. 現在地

いまの階層はこうじゃ。

| 層                                         | 状態   |
| ----------------------------------------- | ---- |
| `PrimePowerLabel` sidecar                 | 完了   |
| `PrimePowerWitnessProvider`               | 完了   |
| `weightOfBase`                            | 完了   |
| `weightOfBase_primeWitnessDependent`      | 完了   |
| `ofPrimeWitnessDependentWeight`           | 完了   |
| `ofWitnessProviderWeight`                 | 今回完了 |
| witness-provider weight の sample provider | 未    |
| witness-provider weight の hit mass bound  | 未    |
| (\Lambda(q)=\log p) 型の解析 weight           | 未    |

ここまでで、DkMath の Erdős #1196 ルートは、

$$
q=p^k
$$

の witness から base prime (p) を取り出し、

$$
c(n,p)
$$

に基づいて weight を構成し、それを channel provider に流すところまで一般化された。

これはかなりよい登りじゃ。

## 6. 次の一手: Phase AY

次は History にある通り、sample を通す段階じゃ。

目的は、

$$
sampleTenPrimePowerWitnessProvider
$$

と

$$
sampleTenToyPrimeBaseWeight
$$

から、`ofWitnessProviderWeight` 経由で `PrimePowerChannelProvider` を作り、hit mass bound まで接続することじゃ。

候補名はこう。

```lean
def sampleTenWitnessProviderWeightChannelProvider :
    PrimePowerChannelProvider :=
  PrimePowerChannelProvider.ofWitnessProviderWeight
    sampleTenPrimePowerWitnessProvider
    sampleTenToyPrimeBaseWeight
    ...
    ...
```

ここで必要になるのは二つ。

第一に、base weight の非負性。

```lean
theorem sampleTenToyPrimeBaseWeight_nonneg_on_index :
    ∀ n q
      (hq :
        q ∈ sampleTenPrimePowerDivisorTransitionKernel
          .toDivisorTransitionKernel.index n),
      0 ≤ sampleTenToyPrimeBaseWeight n
        ((sampleTenPrimePowerWitnessProvider.label n q hq).p)
```

第二に、`W.weightOfBase c` で作った weight の sub-probability。

既に似たものとして `sampleTenToyWeightKernel_subProbability` があるが、今回は weight が

```lean
sampleTenPrimePowerWitnessProvider.weightOfBase sampleTenToyPrimeBaseWeight
```

なので、必要ならこれを別名 theorem として置くのがよい。

```lean
theorem sampleTenWitnessProviderWeightKernel_subProbability :
    ...
```

## 7. Phase AY の hit mass bound

その次に欲しい theorem はこれじゃ。

```lean
theorem sampleTenWitnessProviderWeight_hitMass_le_one :
    ...
```

意味は、

$$
\text{witness provider}
+
\text{base-prime toy weight}
\Rightarrow
\mathrm{weightedHitMass}\le 1
$$

じゃ。

これは Phase AM / AT で通した bound と同型だが、今回は route がより意味論的になる。

以前は「手定義 toy weight」だった。
今回は、

$$
q=p^k
\quad\text{の witness から }p\text{ を読み}
\quad
c(n,p)\text{ で weight を作る}
$$

という route で通る。

ここまで閉じると、witness-provider-driven weight の実例が完成する。

## 8. 二手先: Phase AZ

Phase AY の次は、わっちなら **一般 constructor の theorem-facing bound** を整える。

つまり、sample だけではなく、任意の

$$
W:\text{PrimePowerWitnessProvider}(T)
$$

と

$$
c(n,p)
$$

について、`ofWitnessProviderWeight` で作った provider が weighted hit mass bound に入る theorem を別名で用意する。

既存の `PrimePowerChannelProvider.weightedHitMass_le_const_applyAtToSourceControlled` はすでに使えるはずじゃが、route 名が一般的すぎる。そこで alias を足す。

候補名：

```lean
theorem PrimePowerChannelProvider.witnessProviderWeight_hitMass_le_const
```

または namespace を考えるなら、

```lean
theorem PrimePowerWitnessProvider.weightOfBase_hitMass_le_const
```

意味は、

$$
W.weightOfBase(c)
$$

から作った provider で、

$$
\mathrm{weightedHitMass}\le C
$$

が出る、というものじゃ。

この alias があると、次の解析風 weight へ進むときに theorem 名から route が読める。

## 9. さらにその先

Phase AZ まで行ったら、次に初めて

$$
c(n,p)
$$

の中身を考え始めるのがよい。

現段階では (c(n,p)) は任意の有理 toy weight じゃ。
次に考える候補は、

$$
c(n,p)=\frac{a(p)}{b(n)}
$$

のような抽象形。

ただし、まだ (\log) には入らぬ方がよい。
まずは有理 toy version として、

$$
0\le c(n,p),
\qquad
\sum_{q\in index(n)} c(n,p(q))\le 1
$$

を仮定する形で十分じゃ。

本物の

$$
\frac{\Lambda(q)}{\log n}
$$

はさらに後でよい。

## 10. 総括

Phase AX は、base prime (p) 依存 weight を **provider 化する標準入口** を作った段階じゃ。

これで、

$$
W:\text{PrimePowerWitnessProvider}
$$

が選ぶ witness から (p) を読み、

$$
c(n,p)
$$

で weight を作り、

$$
PrimePowerChannelProvider
$$

まで流せるようになった。

山で言えば、各道標から base prime (p) を読む案内人ができ、さらにその (p) に応じた通行料を受付へ直接登録できるようになった。
次は sample でこの新しい受付ルートを実際に通し、さらにその次で一般 theorem 名として整えるのが見通しよいぞい。
