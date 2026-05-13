# review

## 1. 結論

うむ、Phase AT は **prime witness dependent route の看板固定** じゃ。
数学的な中身は既存の

```lean id="yif6sc"
sampleTenToyWeightChannelProvider_hitMass_le_one
```

と同じだが、新しく

```lean id="mcaz0j"
sampleTenPrimeWitnessDependentWeight_hitMass_le_one
```

という theorem 名を与えたことで、

$$
\mathrm{PrimeWitnessDependentWeight}
\to
\mathrm{ofPrimeWitnessDependentWeight}
\to
\mathrm{applyAtToSourceControlled}
\to
\mathrm{weightedHitMass}\le 1
$$

という route が theorem 名から読めるようになった。

これは良い仕上げじゃ。
Phase AS で base prime $p$ 依存の toy weight を provider 化できるようになり、Phase AT でそれが実際に hit mass bound へ到達する看板が立った。ここで一度、次の二手を慎重に決めるのが正解じゃな。

## 2. 今回閉じたもの

今回の theorem は alias だが、意味は大きい。

```lean id="0mmoyg"
theorem sampleTenPrimeWitnessDependentWeight_hitMass_le_one :
    ...
  sampleTenToyWeightChannelProvider_hitMass_le_one
```

これは、

$$
w(n,q)=c(n,p)
$$

という prime witness dependent な説明を持つ toy weight が、既存の weighted hit mass bound に乗ることを **名前として固定** したものじゃ。

つまり、いまの route はこう整理できる。

$$
q=p^k
$$

$$
w(n,q)=c(n,p)
$$

$$
\text{sub-probability}
$$

$$
\Rightarrow
\text{PrimePowerChannelProvider}
$$

$$
\Rightarrow
\mathrm{weightedHitMass}\le 1
$$

ここまで no-sorry で通っておる。

## 3. 現在地

いまの状況はこうじゃ。

| 層                                            | 状態   |
| -------------------------------------------- | ---- |
| `DivisorTransitionKernel`                    | 完了   |
| `PrimePowerDivisorTransitionKernel`          | 完了   |
| `PrimePowerChannelProvider`                  | 完了   |
| `withWeight`                                 | 完了   |
| `VonMangoldtLikeWeight`                      | 完了   |
| `PrimeWitnessDependentWeight`                | 完了   |
| `ofPrimeWitnessDependentWeight`              | 完了   |
| prime witness dependent concrete bound alias | 今回完了 |
| `PrimePowerLabel` 構造体                        | 未    |
| witness 選択層                                  | 未    |
| analytic $\Lambda(q)/\log n$                 | 未    |

ここまでで、 $q:\mathbb{N}$ label を保ったまま、かなり遠くまで来ている。
ただし、本物の von Mangoldt 的な

$$
\Lambda(q)=\log p
\quad(q=p^k)
$$

へ進むには、いずれ $p$ をどう扱うかが問題になる。

## 4. ここからの判断

次の大きな分岐は二つじゃ。

### A. いきなり label を構造体化する

```lean id="r7u4e3"
structure PrimePowerLabel where
  q : ℕ
  p : ℕ
  k : ℕ
  prime : Nat.Prime p
  k_pos : 0 < k
  eq_pow : q = p ^ k
```

これは強い。
(p) が field として取り出せるので、将来

$$
w(n,\ell)=c(n,\ell.p)
$$

のように書きやすい。

ただし、既存の `DivisorTransitionKernel` は label を $\mathbb{N}$ として設計されている。ここで全面的に label 型を変えると、既存 API への影響が大きい。

### B. 既存の $q:\mathbb{N}$ route を保ち、構造体は sidecar として追加する

こちらがわっちの推奨じゃ。

つまり、`DivisorTransitionKernel` 本体はそのままにして、まず `PrimePowerLabel` を **証拠を持つ補助構造体** として追加する。
その後、 $q\in index(n)$ に対して `PrimePowerLabel` を選ぶ witness provider を別レイヤに置く。

これなら既存 route を壊さず、将来の $\Lambda$-like weight に必要な $p$ 取り出しだけを増やせる。

## 5. 一手目: Phase AU 案

次は **Phase AU: PrimePowerLabel sidecar** がよい。

目的は、label を全面置換せず、prime-power witness を一つの構造体として扱えるようにすることじゃ。

候補定義：

```lean id="u7ogr4"
structure PrimePowerLabel where
  q : ℕ
  p : ℕ
  k : ℕ
  prime : Nat.Prime p
  k_pos : 0 < k
  eq_pow : q = p ^ k
```

最初にほしい補題はこれくらいでよい。

```lean id="x721uy"
theorem PrimePowerLabel.isPrimePowerLabel
    (L : PrimePowerLabel) :
    IsPrimePowerLabel L.q := by
  exact ⟨L.p, L.k, L.prime, L.k_pos, L.eq_pow⟩
```

さらに、既存の `DivisorTransitionKernel` と接続する薄い補題。

```lean id="9ulqcv"
theorem PrimePowerLabel.primePowerDescentStep_of_mem
    (T : DivisorTransitionKernel)
    {n : ℕ} (L : PrimePowerLabel)
    (hmem : L.q ∈ T.index n) :
    PrimePowerDescentStep n (T.next n L.q)
```

中身は既存の

```lean id="udik7g"
primePowerDescentStep_of_primePow_label
```

または

```lean id="rjvfve"
primePowerDescentStep_of_isPrimePowerLabel
```

へ渡せばよい。

この Phase AU の狙いは、まだ大きな refactor ではない。
「 $q=p^k$ の証拠を持つ名前付き構造」を導入するだけじゃ。

## 6. 二手目: Phase AV 案

その次は **Phase AV: PrimePowerWitnessProvider** がよい。

これは、既存の $q:\mathbb{N}$ index に対して、各 $q$ の prime-power witness を選ぶ層じゃ。

候補定義：

```lean id="zk6xyf"
structure PrimePowerWitnessProvider
    (T : PrimePowerDivisorTransitionKernel) where
  label :
    ∀ n q,
      q ∈ T.toDivisorTransitionKernel.index n →
        PrimePowerLabel
  label_q :
    ∀ n q (hq : q ∈ T.toDivisorTransitionKernel.index n),
      (label n q hq).q = q
```

これがあると、次のような weight を定義できる。

```lean id="aacw8n"
def weightOfBase
    (T : PrimePowerDivisorTransitionKernel)
    (W : PrimePowerWitnessProvider T)
    (c : ℕ → ℕ → ℚ) :
    ℕ → ℕ → ℚ :=
  fun n q =>
    if hq : q ∈ T.toDivisorTransitionKernel.index n then
      c n ((W.label n q hq).p)
    else
      0
```

数学的には、

$$
q\in index(n)
$$

なら witness provider が

$$
q=p^k
$$

を持つ label $L$ を返し、その base prime $p$ を使って

$$
w(n,q)=c(n,p)
$$

を定義する、ということじゃ。

これでようやく、prime base $p$ に依存する weight が **定義として** 書ける。

## 7. 二手先までの導線

この二手を入れると、次の道が見える。

$$
\text{PrimePowerLabel}
$$

$$
\to
\text{PrimePowerWitnessProvider}
$$

$$
\to
w(n,q)=c(n,p)
$$

$$
\to
\mathrm{PrimeWitnessDependentWeight}
$$

$$
\to
\mathrm{ofPrimeWitnessDependentWeight}
$$

$$
\to
\mathrm{weightedHitMass}\le C
$$

つまり、今ある predicate route を保ったまま、より具体的な witness-driven weight へ移行できる。

これが一番安全じゃ。
既存の `DivisorTransitionKernel` を壊さず、しかし将来の $\Lambda(q)=\log p$ に必要な $p$ 依存性はちゃんと確保できる。

## 8. なぜ今すぐ full refactor しない方がよいか

`PrimePowerLabel` を index 型そのものにすると、たとえば kernel は

$$
index(n): Finset\ PrimePowerLabel
$$

のようになる。
これは本格的には美しいが、既存の

```lean id="oabzmb"
SourceControlledChainFamily M ℕ
WeightProvider ℕ
FiniteTransitionKernel ℕ ℕ
DivisorTransitionKernel
```

と合わなくなる。

今の route は $q:\mathbb{N}$ label でかなり整っている。
したがって、いきなり構造体化で全線を置き換えるのは、山頂アタック前に登山道を掘り返すようなものじゃ。

まずは sidecar と witness provider。
これが安全じゃ。

## 9. 具体的な次の実装指示

次 Phase AU では、最小限でよい。

```lean id="qpao1b"
structure PrimePowerLabel where
  q : ℕ
  p : ℕ
  k : ℕ
  prime : Nat.Prime p
  k_pos : 0 < k
  eq_pow : q = p ^ k
```

追加補題：

```lean id="ydazz3"
PrimePowerLabel.isPrimePowerLabel
PrimePowerLabel.primePowerDescentStep_of_mem
```

sample：

```lean id="byyk74"
def samplePrimePowerLabel_two : PrimePowerLabel
def samplePrimePowerLabel_five : PrimePowerLabel
```

確認 theorem：

```lean id="9m7vpe"
samplePrimePowerLabel_two_descent :
  PrimePowerDescentStep 10
    (sampleTenPrimePowerDivisorTransitionKernel
      .toDivisorTransitionKernel.next 10 samplePrimePowerLabel_two.q)
```

## 10. 二手目の実装指示

Phase AV では、

```lean id="0saoy6"
structure PrimePowerWitnessProvider
    (T : PrimePowerDivisorTransitionKernel) where
  label :
    ∀ n q,
      q ∈ T.toDivisorTransitionKernel.index n →
        PrimePowerLabel
  label_q :
    ∀ n q (hq : q ∈ T.toDivisorTransitionKernel.index n),
      (label n q hq).q = q
```

次に sample：

```lean id="qyy9q2"
def sampleTenPrimePowerWitnessProvider :
    PrimePowerWitnessProvider sampleTenPrimePowerDivisorTransitionKernel
```

さらに weight 定義：

```lean id="lk5xld"
def PrimePowerWitnessProvider.weightOfBase
    (W : PrimePowerWitnessProvider T)
    (c : ℕ → ℕ → ℚ) :
    ℕ → ℕ → ℚ := ...
```

ここまで入れば、Phase AW で

```lean id="19ju3o"
weightOfBase_primeWitnessDependent
```

を狙える。

## 11. 総括

Phase AT は、prime witness dependent route が concrete bound に届いていることを、定理名として明示した仕上げじゃ。

ここからの二手は、こう進むのが見通しよい。

$$
\boxed{
\text{Phase AU: PrimePowerLabel sidecar}
}
$$

$$
\boxed{
\text{Phase AV: PrimePowerWitnessProvider}
}
$$

この二手で、既存の $q:\mathbb{N}$ label route を壊さずに、base prime $p$ を取り出せる道ができる。

山で言えば、いままでは「この道は素冪由来」と看板に書いてあった。
次は、その看板に

$$
q=p^k
$$

の詳細札を付ける。
さらに次の一手で、各道標から base prime $p$ を読み取る案内人を配置する。
その先でようやく、本物に近い von-Mangoldt-like weight へ進めるのじゃ。
