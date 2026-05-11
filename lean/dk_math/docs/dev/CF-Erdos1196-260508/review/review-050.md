# review

## 1. 結論

うむ、Phase AY は **witness-provider-driven weight route の concrete 開通** じゃ。
Phase AX で作った

```lean
PrimePowerChannelProvider.ofWitnessProviderWeight
```

を、今回ついに sample で実際に使い、

$$
\text{PrimePowerWitnessProvider}\\
\to
\text{base-prime toy weight}\\
\to
\text{weightOfBase}\\
\to
\text{PrimePowerChannelProvider}\\
\to
\mathrm{weightedHitMass}\le 1
$$

まで no-sorry で通した。

これはかなり大きい。
これまでの「手定義 toy weight route」と同じ bound を、今度は **prime-power witness から base prime \(p\) を読んで weight を作る route** として通せたわけじゃ。

## 2. 今回閉じた主導線

今回追加された主な定理・定義はこれじゃ。

```lean
sampleTenToyPrimeBaseWeight_nonneg_on_index
sampleTenPrimePowerWitnessProvider_weightOfBase_eq_sampleTenToyWeight
sampleTenWitnessProviderWeightKernel_subProbability
sampleTenWitnessProviderWeightChannelProvider
sampleTenWitnessProviderWeightChannelProvider_channelProviderAt_subProbability
sampleTenWitnessProviderWeight_hitMass_le_one
```

流れとしては、まず sample の base-prime weight

$$
c(n,p)
$$

が witness-provider index 上で非負であることを示した。
次に、

$$
W.\mathrm{weightOfBase}(c)
$$

で作った label weight が、既存の手定義 toy weight `sampleTenToyWeight` と一致することを固定した。

ここがよい。
つまり、新 route が既存 route と同じ重みを再構成していることが確認された。

## 3. 重要な一致定理

今回かなり効いているのはこれじゃ。

```lean
sampleTenPrimePowerWitnessProvider_weightOfBase_eq_sampleTenToyWeight
```

数学的には、

$$
\mathrm{sampleTenPrimePowerWitnessProvider.weightOfBase}(\mathrm{sampleTenToyPrimeBaseWeight})\\ = \mathrm{sampleTenToyWeight}
$$

を示している。

これは単なる確認ではない。
これにより、以前の手書き toy weight が、実は

$$
q=p^k
$$

の witness から base prime \(p\) を取り出して作られた weight と一致する、という意味づけが得られた。

つまり、

$$
w(10,2)=1,\qquad w(10,5)=0
$$

という手定義が、

$$
w(n,q)=c(n,p(q))
$$

という構造的な定義へ昇格したわけじゃ。

## 4. sub-probability も通った

次に、

```lean
sampleTenWitnessProviderWeightKernel_subProbability
```

で、`W.weightOfBase c` で置き換えた kernel が sub-probability であることを示した。

これは今後の一般化で重要じゃ。
`ofWitnessProviderWeight` は provider を作るために sub-probability 証明を要求する。今回、その実例が閉じた。

状態 \(10\) では labels \(2,5\) に対して、

$$
w(10,2)=1,\qquad w(10,5)=0
$$

なので総量は \(1\)。
それ以外の状態では index が空なので総量は \(0\)。したがって、

$$
\sum_{q\in index(n)} w(n,q)\le 1
$$

が成立する。

## 5. weighted hit mass bound まで到達

最後に、

```lean
sampleTenWitnessProviderWeight_hitMass_le_one
```

が追加された。

これは、witness-provider-driven weight で作った channel provider を `SourceControlledChainFamily` に適用し、

$$
\mathrm{weightedHitMass}\le 1
$$

まで通す theorem じゃ。

つまり、今回で concrete route は完全にこうなった。

$$
\text{sampleTenPrimePowerWitnessProvider}
+
\text{sampleTenToyPrimeBaseWeight}
$$

から、

$$
\text{W.weightOfBase(c)}
$$

を作り、

$$
\text{PrimePowerChannelProvider.ofWitnessProviderWeight}
$$

で provider 化し、

$$
\text{applyAtToSourceControlled}
$$

で source-controlled family に載せ、

$$
\mathrm{weightedHitMass}\le 1
$$

まで到達した。

これは実に良い。
わっちの目にも、ここは「使える道」としてかなり固まってきたぞい。

## 6. Lean 的な注意点

今回の失敗事例も大事じゃ。

`sampleTenWitnessProviderWeightKernel_subProbability` では、dependent proof を含む `withWeight` の目標に対して、weight 関数の等式で直接 `rw` しようとしても厳しかった。そこで `weightOfBase` の定義を unfold して直接計算する形にした。

これは正しい判断じゃ。
依存型の proof term を含む構造では、見た目上同じ重みでも definitional equality として扱いづらいことがある。ここでは無理に抽象化せず、sample では計算で閉じる方が堅い。

また compatibility 証明でも、pipeline 表記と `simp` の噛み合わせが悪くなったので、通常の field 表記へ戻したのもよい。Lean では読みやすさと `simp` の相性を優先するのが勝ちじゃ。

## 7. 現在地

現時点の到達点はこうじゃ。

| 層                                   | 状態   |
| ----------------------------------- | ---- |
| `PrimePowerLabel` sidecar           | 完了   |
| `PrimePowerWitnessProvider`         | 完了   |
| `weightOfBase`                      | 完了   |
| `ofWitnessProviderWeight`           | 完了   |
| witness-provider sample provider    | 今回完了 |
| witness-provider hit mass bound     | 今回完了 |
| 一般 theorem-facing bound alias       | 未    |
| 解析風 weight \(c(n,p)\)                 | 未    |
| `PrimePowerLabel` index kernel 別ルート | 未    |

つまり、witness-provider-driven weight route は、sample で完全に開通した。
ここからは **一般 theorem 名として整えるか** 、 **解析風 weight に進むか** の判断になる。

## 8. 次の一手: Phase AZ

次は History の通り、 **`ofWitnessProviderWeight` route の一般 bound alias** が自然じゃ。

既に一般 theorem としては、

```lean
PrimePowerChannelProvider.weightedHitMass_le_const_applyAtToSourceControlled
```

が使える。

しかし theorem 名だけを見ると、これは一般の channel provider 用であって、

$$
\text{W.weightOfBase(c)}
$$

由来であることが見えない。

そこで、route 名を明示する alias を作るとよい。

候補はこうじゃ。

```lean
theorem PrimePowerChannelProvider.witnessProviderWeight_hitMass_le_const
```

または、より witness provider 側に寄せて、

```lean
theorem PrimePowerWitnessProvider.weightOfBase_hitMass_le_const
```

わっちの推しは後者じゃ。
理由は、主役が

$$
\text{W.weightOfBase(c)}
$$

だからじゃ。

## 9. Phase AZ の形

狙う theorem は概念的にはこう。

```lean
theorem PrimePowerWitnessProvider.weightOfBase_hitMass_le_const
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (c : ℕ → ℕ → ℚ)
    ...
    :
    (PrimePowerChannelProvider.ofWitnessProviderWeight
      W c hc_nonneg hsub
      |>.applyAtToSourceControlled n F hcompat).weightedHitMass S ≤ C
```

必要な仮定は次じゃ。

$$
c(n,p)\ge 0
$$

$$
\text{W.weightOfBase(c)}\text{ が sub-probability}
$$

$$
F\text{ と provider の index が compatible}
$$

$$
S\text{ primitive}
$$

$$
\forall q\in F.\text{index},\quad \mu(F.\text{source}(q))\le C
$$

これを既存 theorem へ渡す alias にする。

実装自体は短いはずじゃ。
ただし theorem 文が長くなりがちなので、まずは `PrimePowerChannelProvider` 側の alias として軽く置くのもありじゃ。

## 10. その次: Phase BA の先読み

Phase AZ で一般 alias を置いたら、次は **解析風 toy weight \(c(n,p)\)** を考える段階じゃ。

まだ本物の \(\log\) は入れず、まずは有理 toy model がよい。

例として、

$$
c(n,p)=\frac{a(p)}{b(n)}
$$

のような形を抽象化する。

Lean 的には、まず構造体ではなく predicate がよい。

```lean
def BasePrimeToyWeight
    (c : ℕ → ℕ → ℚ) : Prop :=
  ∀ n p, 0 ≤ c n p
```

または、kernel index 上の sub-probability まで含めて、

```lean
def BasePrimeSubProbability
    (W : PrimePowerWitnessProvider T)
    (c : ℕ → ℕ → ℚ) : Prop :=
  (T.withWeight (W.weightOfBase c) ...).SubProbability
```

ここは少し設計が必要じゃ。
焦って \(\log\) に入るより、まず \(c(n,p)\) の非負性と総量制御を theorem-facing に分けるのが賢い。

## 11. さらに先の分岐

Phase AZ / BA のあとで、次の二択になる。

一つ目は、今の \(q:\mathbb{N}\) label + witness provider route を続け、解析風 weight だけを強くする道。

二つ目は、`PrimePowerLabel` を index にした別 kernel を作る道。

いまはまだ一つ目を推す。
理由は、既存 route がきれいに通っており、`weightOfBase` によって \(p\) 依存性も表現できているからじゃ。

`PrimePowerLabel` index kernel は、将来 \(p,k\) を定義的に多用したくなった時に、別登山道として作ればよい。

## 12. 総括

Phase AY は、witness-provider-driven weight route の **実走テスト成功** じゃ。

これで、

$$
\text{witness provider}
+
\text{base-prime toy weight}
\Rightarrow
\mathrm{weightedHitMass}\le 1
$$

が concrete に通った。

山で言えば、各道標の \(q=p^k\) 札から base prime \(p\) を読み、そこから通行料を計算し、受付に登録して、実際に通行量制限を突破した。
次はこのルートを sample 専用ではなく、一般 theorem 名として案内板に載せる番じゃな。
