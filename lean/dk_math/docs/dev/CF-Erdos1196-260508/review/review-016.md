# review

うむ、Phase Q は **命名固定フェーズとして成功** じゃ。
今回で、finite route API の看板がかなり整った。

## 1. 何が整ったか

今回追加されたのは、主に二つの alias じゃ。

```lean
hitMass_le_sourceMass_of_subconservativeBranchPrimePathFamily
hitMass_le_sourceMass_of_dvdMonotonePrimePathFamily
```

前者は source control が

$$
\text{SubConservative } M B
$$

由来であることを theorem 名に明示し、後者は

$$
\text{DvdMonotoneMass } M
$$

由来であることを theorem 名に明示しておる。これで、短い route 名と根拠明示 alias の両方が揃ったわけじゃ。

## 2. 命名規則が固定された意味

今回、`ErdosFinitePrimitiveInput` namespace に route-facing API の命名規則がコメントとして入った。

```text
<route>SourceControlled
<route>HitMass
<route>SourceMass
hitMass_le_sourceMass_of_<route>
```

これはかなり良い。今後 Markov route を足すときも、

```lean
markovPathFamilyHitMass
markovPathFamilySourceMass
hitMass_le_sourceMass_of_markovPathFamily
```

のように自然に載せられる。命名規則を先に固定したことで、API が増えても迷子になりにくい。

## 3. 現在の finite route 状況

いま `ErdosFinitePrimitiveInput` から見える有限 route は二本じゃ。

| route                   | source control の根拠    | 役割                         |
| ----------------------- | --------------------- | -------------------------- |
| `branchPrimePathFamily` | `SubConservative M B` | 宇宙式 Mass / Branch 側の劣保存ルート |
| `primePathFamily`       | `DvdMonotoneMass M`   | 整除単調性による数論ルート              |

この二本が同じ形式で、

$$
\mathrm{HitMass}\le \mathrm{SourceMass}
$$

を持つようになった。
これは、山頂へ向かう二つの登山道に、同じ形式の標識が立った状態じゃな。

## 4. 今回の concrete sample の意味

追加 sample も良い。

```lean
erdosFinitePrimitiveInput_two_five_subconservativeBranch_alias
erdosFinitePrimitiveInput_two_five_dvdMonotonePrime_alias
```

これにより、根拠明示 alias 側でも既存の `{2,5}` sample が通ることを確認している。単なる別名追加ではなく、公開 API として実際に呼べることまで検証しておる。

## 5. 現在の到達点

ここまでで finite Erdős skeleton は、かなり一段落じゃ。

$$
\text{primitive support}
+
\text{lower bound}
+
\text{prime path family}
+
\text{mass control route}
\Rightarrow
\text{hit mass}\le\text{source mass}
$$

が、theorem-facing API として読めるようになった。

特に今回は、今後 Markov route を追加する場合も同じ命名規則へ載せやすくなった、と History にも整理されておる。

## 6. 次の一手

次は **有限 Markov skeleton の最小入口** を検討する段階じゃ。ただし、まだ

$$
\frac{\Lambda(q)}{\log n}
$$

や

$$
\frac{1}{n\log n}
$$

の解析重みには入らぬ方がよい。

まずは有限版として、

```lean
structure WeightedPathFamily ...
```

のように、index (i) ごとの非負重みを持つ path family を作るのがよい。

最初の目標は、

$$
\sum_i w_i \cdot \mathrm{hitMass}_i
\le
\sum_i w_i \cdot \mathrm{sourceMass}_i
$$

のような weighted finite bound じゃな。

配置場所は、わっちなら最初は

```text
DkMath/NumberTheory/PrimitiveSet/WeightedPathFamily.lean
```

を推す。理由は、これはまだ Markov 解析ではなく、primitive set hitting の有限重み付き拡張だからじゃ。
`Mass API` 側へ置くのは、もっと一般化して「任意の weighted branching theorem」に昇格したくなってからでよい。

## 7. 総括

Phase Q は、証明力の追加というより **道具の名前を鍛えた段階** じゃ。
だが、これは大事じゃよ。

有限 skeleton はすでにかなり広がっておる。ここで命名を固定したことで、次に Markov / weighted route を増やしても、既存 API と並べて整理できる。

山で言えば、二本の既存ルートに案内標識が整った。
次は、新しい「重み付きルート」の登山口を作る番じゃな。
