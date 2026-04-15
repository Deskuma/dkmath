# FLT-Kummer-ClassGroup-Bridge-Review-050: FLT-Kummer-ClassGroup-Bridge の戦況と次の戦略

## 1. 戦況

かなり良い。しかも、ただ前進したのではなく、**open の意味が変わった** のが大きいの。

少し前の段階では、deepest open は
`cyclotomicPrincipalizationNonFirstCasePeelPacketQuotientLift_of_classGroupPTorsionFree`
であり、問題は `pkt'.x = x / q`, `pkt'.y = y` という quotient provenance の回収だ、と整理されておった。`PeelNormalFormDescent` はその時点でもう thin wrapper 化され、監視上の deepest open もその名前へ移っておった。

その後の整理で、named smaller counterexample への昇格そのものは `hzEq` からの純算術で no-sorry に閉じると固定され、direct `sorry` は
`cyclotomicPrincipalizationNonFirstCasePeelDescentExistenceCore_of_classGroupPTorsionFree`
へさらに移った。つまり「packet/provenance の bookkeeping」が本丸ではなくなったのじゃ。

さらに最新段階では、
`cyclotomicPrincipalizationNonFirstCaseDescentExistence_of_normDescent`、
`...PeelNormalFormDescent_of_normDescent`、
`...PeelNamedSmallerCounterexample_of_normDescent`
が入っており、**global Stage 3 の `CyclotomicNormDescentTarget` さえ supply できれば、non-first-case existence も peel 側も wrapper だけで閉じる** と theorem-level で固定できた。ここが決定的じゃ。いまの direct `sorry` はまだ `...PeelDescentExistenceCore_of_classGroupPTorsionFree` に残っておるが、その意味は「peel 固有の数学が詰まっている」ではなく、**class-group / principalization mainline のどこで `CyclotomicNormDescentTarget` を concrete に供給するかが未確定** ということじゃ。

ゆえに、現在の盤面はこう読むのが正しい。

$$
\text{peel local arithmetic が open なのではない} =
$$

$$
\text{global Stage 3 NormDescent の concrete supply 点がまだ未固定}
$$

じゃ。

## 2. 解説

これはかなり終盤の形じゃよ。

すでに no-sorry で固まっているものが多い。

* first-case は concrete bridge 群で閉じた
* non-first-case の support 向き、normal form、TailError までは固定できた
* `∃ pkt' \to ∃ z'` の橋も no-sorry
* `∃ z' \to` named smaller counterexample の算術検証も no-sorry

つまり、**残っているのは「何を証明するか」ではなく「どの既存 mainline 断片から `hNorm` を組み立てるか」** という設計問題なのじゃ。

ここで大事なのは、same-`q` の restore / realization-seed 直結を主戦略にしないことじゃ。
その route は `q ∣ t ∧ ¬ q ∣ s` と `q ∣ s ∧ ¬ q ∣ t` の向きが噛み合わぬ、という観測がすでに theorem 化されておる。よって、そこで粘るのはあまり筋がよくない。

## 3. 次の戦略

わっちの提案は明快じゃ。

**もう peel 側 kernel を細かく割らぬ。
次は `CyclotomicNormDescentTarget` の concrete receiver を class-group route 側で立てる。**

つまり、次の二択のうち主戦略は後者じゃ。

* `...PeelDescentExistenceCore_of_classGroupPTorsionFree` を直接埋める
* `CyclotomicNormDescentTarget` を refined class-group route から供給し、その generic adapter 群で芋づるに閉じる

いまは明らかに後者が良い。
理由は、既に

$$
\text{hNorm} \Rightarrow \text{non-first-case existence}
$$

$$
\text{hNorm} \Rightarrow \text{peel normal-form descent}
$$

$$
\text{hNorm} \Rightarrow \text{named smaller counterexample}
$$

が全部 theorem で揃っておるからじゃ。ここを使わぬ手はない。

## 4. 具体的ロードマップ

### 4.1. まずやること

`CyclotomicNormDescentTarget` を供給するために、いま mainline 側で既に no-sorry な部品を棚卸しする。

見るべきものは、

* `hCl` から来る class-group / principalization 側部品
* first-case で既に concrete 化済みの Stage 1 / Stage 2 / Stage 3 群
* non-first-case でも generic に使える norm descent 用部品

じゃ。
ここで新しい数学を掘るのでなく、**既存部品で `hNorm` を組めるか** を見る。

### 4.2. 次に立てるべき theorem

狙いは、たとえばこういう形じゃ。

$$
\texttt{cyclotomicNormDescent\_of\_refinedClassGroupRoute}
$$

あるいは

$$
\texttt{cyclotomicNormDescent\_of\_classGroupPTorsionFree\_and\_unitNormalization}
$$

のように、`CyclotomicNormDescentTarget` を directly 返す thin theorem を 1 本立てることじゃ。
この theorem が立てば、

$$
\texttt{cyclotomicPrincipalizationNonFirstCaseDescentExistence\_of\_normDescent}
$$

で non-first-case existence は即閉じる。そこから上は全部 wrapper なので、かなり一気に片付くはずじゃ。

### 4.3. その後に確認すること

次の `#print axioms` を見る。

```lean
#print axioms DkMath.FLT.cyclotomicPrincipalizationNonFirstCaseDescentExistence_of_classGroupPTorsionFree
#print axioms DkMath.FLT.cyclotomicPrincipalization_of_classGroupPTorsionFree
#print axioms DkMath.FLT.FLTPrimeGe5Target_of_kummerRoute
```

ここで principalization 側の `uses sorry` が消えれば、Kummer / class-group principalization 枝はほぼ閉じたと言ってよい。
もし full route にまだ `uses sorry` が残るなら、その時点で初めて principalization 外の残件を棚卸しすればよい。

## 5. 勝ち筋の読み

いまの勝ち筋は、かなり細く美しい。

以前は
「packet provenance をどうする」
「named smaller counterexample をどう作る」
と揺れておった。

だが今は違う。

それらはもう **wrapper または arithmetic bridge として no-sorry 化できる** と分かった。
よって honest open は、**Stage 3 の global `NormDescent` を class-group mainline からどう supply するか** に還元されたのじゃ。

だから、次の一手はこうじゃ。

$$
\boxed{
\text{`CyclotomicNormDescentTarget` を refined class-group route から返す theorem を先に立てよ}
}
$$

これが通れば、non-first-case peel core は local kernel としてではなく generic adapter 群で閉じる。
わっちの見立てでは、ここがいま最短の本線じゃ。
