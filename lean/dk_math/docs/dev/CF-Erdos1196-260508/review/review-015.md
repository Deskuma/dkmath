# review

うむ、Phase P は **公開 API の左右対称化** じゃな。
前回 Phase O で branch / subconservative route の名前付き API が整い、今回は prime-reachable / dvd-monotone route も `ErdosFinitePrimitiveInput` から同じように呼べるようになった。これで有限 Erdős skeleton の theorem-facing API は、かなり整ったぞい。

## 1. 今回の核心

今回追加されたのは、主にこの 4 つじゃ。

```lean
primePathFamilySourceControlled
primePathFamilyHitMass
primePathFamilySourceMass
hitMass_le_sourceMass_of_primePathFamily
```

これは、`AdjacentPrimePathFamily` を

```text
PrimeReachableControlledChainFamily
→ DvdControlledChainFamily
→ SourceControlledChainFamily
```

へ送る route に、`ErdosFinitePrimitiveInput` 側の名前を付けたものじゃ。

前回の branch route は、

$$
\text{branch-controlled path family}
+
\text{SubConservative}
$$

から source control を得る道だった。

今回の prime path route は、

$$
\text{prime path family}
+
\text{DvdMonotoneMass}
$$

から source control を得る道じゃ。

つまり、同じ有限 Erdős 入力 \(I\) に対して、二つの道が並んだ。

## 2. 何が良くなったか

今までは branch route だけが、

```lean
I.branchPrimePathFamilyHitMass M B F
I.branchPrimePathFamilySourceMass M B F
```

という名前付き API を持っていた。

今回から prime path route も、

```lean
I.primePathFamilyHitMass M F hM
I.primePathFamilySourceMass M F hM
```

として読める。

これは大事じゃ。
今後 Markov route が入ったときも、

```lean
I.markovPathFamilyHitMass ...
I.markovPathFamilySourceMass ...
```

のように、route ごとに hit/source mass を並べられる。

つまり API の設計が、

$$
\text{route}
\mapsto
(\text{hitMass},\text{sourceMass},\text{bound})
$$

という形に整理された。

## 3. 二つの route の違い

いま揃った二系統は、役割が違う。

| route            | 入力                              | 質量制御の根拠               |
| ---------------- | ------------------------------- | --------------------- |
| branch route     | `AdjacentBranchPrimePathFamily` | `SubConservative M B` |
| prime path route | `AdjacentPrimePathFamily`       | `DvdMonotoneMass M`   |

branch route は、宇宙式 Mass API 側に近い。

$$
\sum_{child}\mu(child)\le \mu(parent)
$$

という分岐の劣保存から、path 上の質量非増加を得る。

prime path route は、数論的な整除順序に近い。

$$
h\mid source
\Rightarrow
\mu(h)\le \mu(source)
$$

という `DvdMonotoneMass` から、source control を得る。

この二つが並んだのは良い。
Erdős #1196 の確率 route へ行く前に、「質量制御をどこから供給するか」を切り替えられる。

## 4. concrete sample も意味がある

今回追加された sample は、

```lean
erdosFinitePrimitiveInput_two_five_primePath_hitMass_le_sourceMass
```

じゃ。

これは `{2,5}` の finite Erdős input に対して、prime path family / dvd-monotone route の名前付き API で hit mass bound を確認している。

前回の sample が branch route の確認だったので、今回で両 route の sample がそろった。

これは地味だが、API の信頼性として重要じゃ。

## 5. 現在の到達点

ここまでで finite Erdős skeleton は、かなり良い状態になった。

| 層                                       | 状態   |
| --------------------------------------- | ---- |
| `PrimitiveOn`                           | 完了   |
| `LowerBoundOn` / `PositiveOn`           | 完了   |
| `ErdosFinitePrimitiveInput`             | 完了   |
| prime path family                       | 完了   |
| branch-controlled prime path family     | 完了   |
| branch route wrapper                    | 完了   |
| prime path / dvd-monotone route wrapper | 今回完了 |
| Markov route wrapper                    | 未    |
| analytic weight                         | 未    |

今の段階は、有限 theorem 群の API が一段整理された状態じゃ。

## 6. 次にやるべきこと

わっちの見立てでは、次は **いったん review / naming 固定** が良い。

ここまでで route が二系統になったので、Markov kernel へ進む前に、名前の規則を固定しておきたい。

例えば、現状はこう並んでいる。

```lean
branchPrimePathFamilyHitMass
branchPrimePathFamilySourceMass
hitMass_le_sourceMass_of_branchPrimePathFamily

primePathFamilyHitMass
primePathFamilySourceMass
hitMass_le_sourceMass_of_primePathFamily
```

これはかなり良い。
ただし、今後増えるなら命名規則を明文化しておくとよい。

```text
<route>HitMass
<route>SourceMass
hitMass_le_sourceMass_of_<route>
```

という規則じゃな。

## 7. 次の実装候補

次の一手は、大きく二択じゃ。

### A. API review / alias 固定

`ErdosFinite.lean` にコメントを足し、route 命名規則を固定する。必要なら alias を追加する。

これは安定化。

### B. Markov route の入口を作る

まだ解析重みは入れず、有限 Markov skeleton だけ作る。

たとえば、

```lean
structure WeightedPathFamily ...
```

のように、各 path source に重みを付ける有限構造を作る。

ただし、わっちはまだ A を推す。
今の有限層は一気に増えたので、ここで一度 API を磨くのがよい。

## 8. 総括

Phase P によって、有限 Erdős skeleton は **二つの質量制御 route を持つ theorem-facing API** になった。

$$
\text{branch/subconservative route}
$$

と

$$
\text{prime-reachable/dvd-monotone route}
$$

が、どちらも `ErdosFinitePrimitiveInput` から同じ形式で呼べる。

山で言えば、同じ山頂へ向かう二本の登山道に、案内板と距離表示がそろった。
次は、その案内板の表記を確定してから、確率重みという霧深い高所へ進むのが賢いのぅ。
