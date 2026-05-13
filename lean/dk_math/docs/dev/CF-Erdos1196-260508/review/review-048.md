# review

## 1. 結論

うむ、Phase AW は **base-prime weight から label weight を生成する橋** が閉じた段階じゃ。
前回 Phase AV で `PrimePowerWitnessProvider` が入り、各 indexed label $q$ に対して

$$
q=p^k
$$

という witness を選べるようになった。今回 Phase AW では、その witness の base prime $p$ を読み取り、

$$
c(n,p)
$$

という base-prime weight から、

$$
w(n,q)
$$

という通常の label weight を作れるようになった。これは $\Lambda(q)=\log p$ 型の重みへ向かう重要な橋じゃ。

## 2. 今回の主役

追加された中心 API はこれじゃ。

```lean
PrimePowerWitnessProvider.weightOfBase
PrimePowerWitnessProvider.weightOfBase_of_mem
PrimePowerWitnessProvider.weightOfBase_primeWitnessDependent
```

定義としては、

$$
q\in T.index(n)
$$

なら、provider が選んだ witness

$$
L=W.label(n,q,hq)
$$

から $L.p$ を取り出し、

$$
w(n,q)=c(n,L.p)
$$

とする。index 外では $0$ にする。

Lean では、

```lean
def weightOfBase
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (c : ℕ → ℕ → ℚ) :
    ℕ → ℕ → ℚ :=
  fun n q =>
    if hq : q ∈ T.toDivisorTransitionKernel.index n then
      c n ((W.label n q hq).p)
    else
      0
```

じゃな。

これはまさに、base prime $p$ に依存する重みを、既存の $q:\mathbb{N}$ label route に戻す変換器じゃ。

## 3. 何が強くなったか

今回の主定理は、

```lean
weightOfBase_primeWitnessDependent
```

じゃ。

これは、base-prime weight $c(n,p)$ が index 上で非負なら、

$$
T.PrimeWitnessDependentWeight(\mathrm{W.weightOfBase}(c),c)
$$

を得る。

つまり、

$$
w(n,q)=c(n,p)
$$

という形で定義された weight が、既存の `PrimeWitnessDependentWeight` route にちゃんと乗ることを一般定理として示した。

これで導線はこうなる。

$$
\text{PrimePowerWitnessProvider}
$$

$$
\to
w(n,q)=c(n,p)
$$

$$
\to
\text{PrimeWitnessDependentWeight}
$$

$$
\to
\text{ofPrimeWitnessDependentWeight}
$$

$$
\to
\text{PrimePowerChannelProvider}
$$

$$
\to
\mathrm{weightedHitMass}\le C
$$

かなり見通しが良くなったぞい。

## 4. `weightOfBase_of_mem` が効いている

今回の `[simp]` 補題、

```lean
weightOfBase_of_mem
```

は重要じゃ。

index 上では、

$$
\mathrm{W.weightOfBase}(c)(n,q)=c(n,(W.label(n,q,hq)).p)
$$

と簡約できる。

これがないと、`PrimeWitnessDependentWeight` の非負性結論で

$$
0\le \mathrm{W.weightOfBase}(c)(n,q)
$$

を示すとき、仮定

$$
0\le c(n,(W.label(n,q,hq)).p)
$$

と形が合わぬ。History でも、ここは明示的な書き換えが必要だったと記録されておる。

この補題は今後もかなり使うはずじゃ。

## 5. sample の意味

sample theorem は、

```lean
sampleTenPrimePowerWitnessProvider_weightOfBase_primeWitnessDependent
```

じゃ。

これは sample の base-prime weight

$$
c(n,p)=
\begin{cases}
1 & n=10,\ p=2,\\
0 & \text{otherwise}
\end{cases}
$$

から作った label weight が、`PrimeWitnessDependentWeight` を満たすことを確認している。

状態 $10$ の labels は $2,5$。witness provider はそれぞれ

$$
2=2^1,\qquad 5=5^1
$$

を返す。したがって、

$$
w(10,2)=c(10,2)=1
$$

$$
w(10,5)=c(10,5)=0
$$

となる。

これは前に手定義した `sampleTenToyWeight` と同じ形を、今度は witness provider から構成できることを示している。
つまり、手書き重みから **witness-driven weight** へ昇格したわけじゃ。

## 6. 現在地

いまの階層はこうじゃ。

| 層                                              | 状態   |
| ---------------------------------------------- | ---- |
| `PrimePowerLabel` sidecar                      | 完了   |
| `PrimePowerWitnessProvider`                    | 完了   |
| witness → base prime $p$ 取り出し                  | 完了   |
| `weightOfBase`                                 | 今回完了 |
| `weightOfBase` → `PrimeWitnessDependentWeight` | 今回完了 |
| witness-driven provider constructor            | 未    |
| witness-driven hit mass bound sample           | 未    |
| `PrimePowerLabel` 本格 index 化                   | 未    |
| analytic $\Lambda(q)/\log n$                   | 未    |

ここまでで、 $\Lambda(q)=\log p$ の **(p) を読むための骨格** はかなり整った。

## 7. 次の一手: Phase AX

次は History の通り、

```lean
PrimePowerChannelProvider.ofWitnessProviderWeight
```

を作るのが自然じゃ。

目的は、

$$
W:\text{PrimePowerWitnessProvider}(T)
$$

と base-prime weight

$$
c(n,p)
$$

から直接 `PrimePowerChannelProvider` を作ることじゃ。

候補はこう。

```lean
def PrimePowerChannelProvider.ofWitnessProviderWeight
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (c : ℕ → ℕ → ℚ)
    (hc_nonneg :
      ∀ n q (hq : q ∈ T.toDivisorTransitionKernel.index n),
        0 ≤ c n ((W.label n q hq).p))
    (hsub :
      (T.withWeight
        (W.weightOfBase c)
        (T.vonMangoldtLikeWeight_nonneg
          (T.vonMangoldtLikeWeight_of_primeWitnessDependent
            (W.weightOfBase_primeWitnessDependent c hc_nonneg)))).SubProbability) :
    PrimePowerChannelProvider :=
  PrimePowerChannelProvider.ofPrimeWitnessDependentWeight
    T
    (W.weightOfBase c)
    c
    (W.weightOfBase_primeWitnessDependent c hc_nonneg)
    hsub
```

少し長いが、これで導線が一本になる。

$$
c(n,p)
\to
w(n,q)=c(n,p(q))
\to
PrimePowerChannelProvider
$$

じゃ。

## 8. Phase AY の先読み

Phase AX が閉じたら、次は sample を通す。

つまり、

```lean
sampleTenWitnessProviderWeightChannelProvider
```

のような provider を作り、

$$
\mathrm{weightedHitMass}\le 1
$$

まで通す。

候補 theorem は、

```lean
sampleTenWitnessProviderWeight_hitMass_le_one
```

じゃな。

これが閉じると、

$$
\text{witness provider}
+
\text{base-prime weight}
\Rightarrow
\text{hit mass bound}
$$

が concrete に通る。

この段階で、手定義 toy weight route はほぼ完成じゃ。

## 9. その先の大きな判断

Phase AX / AY のあとで、いよいよ二択になる。

一つ目は、今のまま $q:\mathbb{N}$ label + witness provider route を継続する道。

二つ目は、`PrimePowerLabel` を index 型として持つ別 kernel を作る道。

わっちの見立てでは、まだ一手か二手は今の route でよい。
理由は、既存の `DivisorTransitionKernel` / `SourceControlledChainFamily` / `WeightProvider ℕ` がすべて $q:\mathbb{N}$ label で整っているからじゃ。

今すぐ full refactor すると、せっかく整えた山道を掘り返すことになる。
まずは witness provider route で hit mass bound まで通し、そのあと必要なら `PrimePowerLabel` index kernel を別ルートとして作るのが賢い。

## 10. 総括

Phase AW は、base prime $p$ を読む仕組みが、ついに重み生成へ接続された段階じゃ。

これまでは、

$$
q=p^k
$$

という witness を持つところまでだった。
今回からは、その witness の $p$ を使って、

$$
w(n,q)=c(n,p)
$$

を一般に作れる。

山で言えば、各道標の詳細札から base prime $p$ を読み取り、その $p$ に応じて通行料を計算する仕組みができた。
次は、その仕組みを受付 `PrimePowerChannelProvider` に直接つなぐ標準フォームを作る番じゃな。
