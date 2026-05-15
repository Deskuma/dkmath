# review

うむ。DKMK-006D は **かなり大きい接続完了** じゃ。
前回 DKMK-006C では `FullExponentSlotCoverage`、つまり「各 base prime fiber がちょうど n.factorization(p) 個ある」という等号側の coverage 仮定を置いた。今回 DKMK-006D では、その仮定から実際に

$$
\sum_{q\in Full(n)}\log p(q)=\log n
$$

を導き、さらに `FullChannelLogCostComplete` へ接続した。これで、coverage が供給された後の **Markov equality bridge** は no-sorry でかなり閉じたと言ってよい。

## 1. 今回、何が閉じたか

今回追加された中心は新ファイルじゃ。

```lean
DkMath.NumberTheory.PrimitiveSet.FullChannelLogSum
```

ここで、次の流れが実装された。

```text
FullExponentSlotCoverage
  → Σ log basePrime = log n
  → FullChannelLogCostComplete
  → fullGlobalLogCapacityMarkovShadow
```

docs にもこの到達経路が明記されておる。つまり、まだ `FullExponentSlotCoverage` 自体は仮定 interface だが、それが得られた後の Markov equality route は閉じた。

## 2. 数学的な核

今回の数学的な核は二つじゃ。

第一に、有限集合 \(I\) 上の base map pOf について、

$$
\sum_{i\in I}\log(pOf(i))=\sum_{p\in pOf(I)}\#{i\in I\mid pOf(i)=p}\log p
$$

という fiber regrouping を入れた。

Lean ではこれが、

```lean
sum_log_base_eq_sum_image_multiplicity_mul_log
```

じゃ。

これは、重複あり route の multiplicity 語彙を、ついに等号側の有限和へ接続した補題じゃな。

第二に、自然数の素因数分解について、

$$
\sum_{p\in n.factorization.support}n.factorization(p)\log p=\log n
$$

を証明した。

Lean ではこれが、

```lean
sum_factorization_mul_log_eq_log_nat
```

じゃ。

実装では `Nat.prod_factorization_pow_eq_self` と `Real.log_prod` を使って、積の復元から log 和へ進んでいる。これはかなり正攻法じゃ。

## 3. `FullExponentSlotCoverage` から log equality へ

今回の一番大事な橋は、

```lean
fullExponentSlotCoverage_sum_log_base_eq_log_nat
```

じゃ。

これは、coverage 仮定のもとで

$$
\sum_{q\in C.channels(n)}\log(W.basePrimeOf(n,q))=\log n
$$

を出す。

流れはこうじゃ。

まず有限和を base prime ごとに束ねる。

$$
\sum_{q\in C.channels(n)}\log p(q)=\sum_{p\in image(pOf)}m(p)\log p
$$

次に `FullExponentSlotCoverage` で、

$$
m(p)=n.factorization(p)
$$

へ置き換える。

さらに、coverage のもとで base prime の image が factorization support と一致することを示す。

```lean
fullExponentSlotCoverage_image_basePrime_eq_factorization_support
```

これにより右辺が

$$
\sum_{p\in n.factorization.support}n.factorization(p)\log p
$$

になり、最後に

$$
\sum_{p\in n.factorization.support}n.factorization(p)\log p=\log n
$$

で閉じる。

この流れは実に美しい。selected route で使っていた「重複を指数予算で抑える」考えが、full route では「重複数が指数そのものに一致する」へ昇格しておる。

## 4. `FullChannelLogCostComplete` への接続

今回、最終的に

```lean
fullChannelLogCostComplete_of_fullExponentSlotCoverage
```

が追加された。

これは、

$$
FullExponentSlotCoverage \Longrightarrow FullChannelLogCostComplete
$$

を示す補題じゃ。

前回 DKMK-006B では、

$$
FullChannelLogCostComplete \Longrightarrow MarkovShadow
$$

を閉じていた。

したがって今回により、

$$
FullExponentSlotCoverage \Longrightarrow MarkovShadow
$$

までの橋が、ほぼ合成可能になった。

これは大きい。
これで「全 exponent slot が埋まるなら Markov equality が出る」という DkMath kernel route の主張が Lean 上で筋道化された。

## 5. 本線への近づき方

既存の Markov route の核心は、

$$
\sum_{q\mid n}\Lambda(q)=\log n
$$

じゃった。

DkMath route では、これをいきなり \(\Lambda\) で言わず、

$$
q=p^k,\quad \mathrm{cost}(q)=\log p
$$

として作ってきた。

今回 DKMK-006D で、full exponent-slot coverage のもとでは、

$$
\sum \mathrm{cost}=\log n
$$

が出るようになった。

つまり、

$$
\Lambda(q)
$$

を直接持ち込まずとも、prime-power witness と exponent slot の完全性から、von Mangoldt 的な log 総和等式を再構成できることが示されたわけじゃ。

これは、DkMath kernel branch の哲学である

$$
\text{Capacity first, Markov later}
$$

をかなり強く実現しておる。

## 6. 今回の実装の評価

実装方針はかなり良い。

特に、

```lean
sum_log_base_eq_sum_image_multiplicity_mul_log
```

を一般補題として切ったのがよい。これは今後、Erdős route 以外でも使える可能性がある。base map による finite sum の regrouping は、valuation / multiplicity 系の汎用武器じゃ。

また、

```lean
sum_factorization_mul_log_eq_log_nat
```

を独立補題として置いたのも良い。これは DkMath kernel の full equality route だけでなく、今後の \(\Lambda\)-shadow や analytic route でも基礎定理として使える。

さらに、base-prime image と factorization support の一致を二方向に分けて示している点も安全じゃ。

```lean
fullExponentSlotCoverage_image_basePrime_subset_factorization_support
fullExponentSlotCoverage_factorization_support_subset_image_basePrime
fullExponentSlotCoverage_image_basePrime_eq_factorization_support
```

これは Lean 的に後で再利用しやすい。

## 7. 何がまだ残っているか

今回で、次は明確になった。

残っている本丸は、

$$
FullExponentSlotCoverage
$$

そのものをどう供給するかじゃ。

docs でも、次の課題として `FullExponentSlotCoverage` 自体を canonical/full channel enumeration から供給できるか確認し、必要なら explicit slot \((p,k)\) 形式の補助 interface を追加すると書かれている。

つまり、今の状態はこうじゃ。

```text
FullExponentSlotCoverage があれば:
  Σ log basePrime = log n
  → FullChannelLogCostComplete
  → MarkovShadow
```

しかし、まだ

```text
canonical/full channel enumeration
  → FullExponentSlotCoverage
```

が未踏じゃ。

## 8. 次の設計の分岐

ここから先は二つのルートがある。

### ルート A. 既存 `T.index n` を深掘りする

`T.index n` が本当に

$$
{p^k\mid p\text{ prime},,1\le k\le n.factorization(p)}
$$

を表しているなら、その性質を証明して `FullExponentSlotCoverage` を供給する。

この場合、既存 kernel の意味づけを強化することになる。

### ルート B. explicit slot set を別に作る

$$
(p,k)
$$

の finite set を直接作る。

例えば、

$$
p\in n.factorization.support,\quad 1\le k\le n.factorization(p)
$$

を状態空間として持つ slot set を作り、そこから label \(q=p^k\) へ写す。

この方が等号証明は自然じゃ。
ただし既存 `PrimePowerWitnessProvider` の `q`-label route との接続補題が必要になる。

わっちの見立てでは、まずルート B の補助 interface を作る方が安全じゃ。等号計算は slot 形式のほうが圧倒的に素直だからの。そこで得たものを、後から `T.index n` や `FullPrimePowerChannelSet` に橋渡しすればよい。

## 9. 今回の到達点

DKMK-006D により、DkMath kernel branch は次の段階に到達した。

```text
selected route:
  multiplicity ≤ factorization
  → SubMarkovShadow

full route:
  multiplicity = factorization
  → finite log regrouping
  → Σ factorization(p) log p = log n
  → FullChannelLogCostComplete
  → MarkovShadow
```

これは非常に良い。
ここまで来ると、DkMath kernel は単なる Markov kernel の言い換えではない。

むしろ、

$$
\text{exponent slot coverage}
$$

から

$$
\text{log-capacity equality}
$$

を作り、その正規化像として Markov shadow を得る、という独自の構造になっておる。

## 10. 総合判定

DKMK-006D は **FullExponentSlotCoverage から Markov equality への橋を閉じた重要フェーズ** じゃ。

まだ coverage 自体は仮定 interface だが、そこから先は no-sorry で Markov shadow へ到達できる。

つまり、未踏部分はかなり狭まった。

残る山は、

$$
\text{全 exponent slot が本当に channels に入る}
$$

をどう供給するか。

ここを取れば、DkMath kernel route は既存 Markov route の核心等式

$$
\sum_{q\mid n}\Lambda(q)=\log n
$$

を、DkMath の言葉で再構成したことになる。

ぬしよ、これはかなり良い。
別尾根が、ついに本線の稜線へ手を掛けたぞい。
