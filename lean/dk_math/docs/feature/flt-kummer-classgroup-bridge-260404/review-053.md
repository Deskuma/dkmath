# 2024-04-26: `hCl + hUnit ⟹ hNorm` の Stage 3 receiver が pure arithmetic に直接閉じました

## 1. いま何が起きたのか

要するに、前に残っていた

$$
\text{hCl} + \text{hUnit} \Longrightarrow \text{hNorm}
$$

の Stage 3 receiver 問題は、もう mainline としては解けた、ということじゃ。

今回の差分では `cyclotomicNormDescentNonFirstCaseGNPowerReceiver_of_classGroupPTorsionFree` が、`bodyInvariant_of_NoPowOnGN triominoCosmicNoPowOnGN_default` を使って

$$
GN\,p\,\(z-y)\,y = s^p
$$

という仮定そのものから矛盾を出し、`False.elim` で最終 witness を返す形に差し替わった。これにより、その下流にある

* `cyclotomicNormDescentNonFirstCaseUnitNormalizedReceiver_of_classGroupPTorsionFree`
* `cyclotomicNormDescent_of_classGroupPTorsionFree_and_unitNormalization`
* その先の principalization / descent existence 系 wrapper

がまとめて no-sorry 化した、というのが今回の本質じゃ。

つまり、前回までわっちが「残っているのは pure arithmetic receiver 1 本だ」と言っておったが、その 1 本が今回閉じたわけじゃな。
しかも、build だけでなく `RegularPrimeRoute.lean` 側の no-sorry 監視でも Stage 3 receiver 群が no-sorry セクションへ移され、`RegularPrimeRouteSorry.lean` 側では sorry 監視が old peel core 系だけに絞られておる。これはかなり大きい。

## 2. 戦況の詳細分析

ここをじっくり読むと、戦況は 3 段で変わったのじゃ。

### 2.1. 以前の状態

最初は `hCl + hUnit ⟹ hNorm` が direct open だった。
その後、global receiver を first / non-first に割り、

$$
\text{global Stage 3 open} \to \text{non-first-case branch open}
$$

へ押し下げた。さらに non-first-case 側を unit-normalized chosen-factor receiver に分け、そこから `NormEqGN` と `UnitAbsorb` を no-sorry で concrete 化して、

$$
z-\zeta y = \text{unitFactor}\cdot \beta^p
\Longrightarrow
\exists s,\ GN,p,(z-y),y = s^p
$$

までは no-sorry に届く、と fixed した。

### 2.2. 今回の変化

今回ついに、その先の pure arithmetic residue

$$
\exists s,\ GN\,p\,(z-y)\,y = s^p
\Longrightarrow
\exists g',\ g' \cdot GN\,p\,g'\,y = (x/q)^p
$$

が、既存の no-pow body invariant への即時矛盾として閉じた。
なので、「円分体側」「unit normalization 側」「norm 計算側」「receiver 側」と順に押し下げてきた最後の open が消えたことになる。

### 2.3. いま残っているもの

最新報告では、`CyclotomicPrincipalization.lean` に残る direct `sorry` は

$$
\texttt{cyclotomicPrincipalizationNonFirstCasePeelDescentExistenceCore\_of\_classGroupPTorsionFree}
$$

の 1 箇所だけ、と明記されておる。
つまり honest open は、もう Stage 3 receiver 群ではない。
いまの未整理は old peel core mainline の残骸 1 本に局所化された、と見てよい。

これはかなり良い状態じゃ。
なぜなら、残っている `sorry` が「証明の核心」ではなく、「古い mainline 配線が新しい no-sorry chain にまだ置換されていない」可能性が高いからじゃ。

## 3. どういう意味で前進なのか

ここがいちばん大事じゃ。

前は、
「まだ class-group principalization の本体が開いている」
と読めた。

今は違う。
いまは

$$
\text{class-group} + \text{unit normalization} \to \text{global/non-first-case norm route}
$$

までは no-sorry mainline で通る、と言ってよい。
つまり、新しい mainline はもう勝っておる。
残っているのは、old peel core の theorem 名と配置がまだ昔のまま残っていることじゃ。

この違いは大きい。
もし残差が「新しい数学の不足」なら、さらに深掘りが要る。
だが今の形は、「既に閉じた mainline で old peel core を置換できるか」を検査する局面じゃ。
これは戦い方がまるで違う。

## 4. いまの進捗感

どんぶり勘定で言えば、Kummer / class-group principalization 局所戦線はもう **96〜97%** くらいと見てよい。
前回の 93〜95% より一段上がった感じじゃ。理由は、mainline の deepest Stage 3 receiver が消え、残件が old peel core 1 本になったからじゃ。

FLT の regular-prime / Kummer route 全体としても、かなり 9 割に近い空気じゃが、そこは principalization 外の残件があるかもしれぬので、わっちはまだ **85〜90% 台前半** くらいで見ておくのが誠実だと思う。
ただ、少なくとも principalization branch の景色は、かなり終盤じゃ。

## 5. 次の戦略

ここからの最善手は、もう pretty clear じゃ。

### 5.1. 第一手

`cyclotomicPrincipalizationNonFirstCasePeelDescentExistenceCore_of_classGroupPTorsionFree` が、
いま no-sorry 化された global / non-first-case norm route で **thin wrapper に置換できるか** をまず検査する。

最新報告の「次の課題」も、まさにそこを言っておる。
つまり新しい theorem を増やすのでなく、

$$
\text{old peel core} \stackrel{?}{=} \text{new no-sorry norm route の薄い包装}
$$

かどうかを見るのじゃ。

### 5.2. 第二手

もし置換できるなら、その old peel core theorem 自体を

* no-sorry wrapper に書き換える
* あるいは deprecated / legacy 扱いにして、mainline から外す

のどちらかにする。
そうすれば `CyclotomicPrincipalization.lean` から direct `sorry` が消える。
これはかなり気持ちよい節目になるはずじゃ。

### 5.3. 第三手

そのあと `#print axioms` を改めて見て、

* `cyclotomicPrincipalization_of_classGroupPTorsionFree`
* `FLTPrimeGe5Target_of_kummerRoute`

にまだ `uses sorry` が残るかを確認する。
もし消えておれば、Kummer / class-group principalization branch は実質閉じた、と言ってよい。
もし残るなら、それは principalization 本体ではなく、別の legacy route か監視名の残骸じゃ。

## 6. 具体的に何を見ればよいか

わっちなら次に見るのはこれじゃ。

`cyclotomicPrincipalizationNonFirstCasePeelDescentExistenceCore_of_classGroupPTorsionFree` の proof body が、いまの

* `cyclotomicNormDescent_of_classGroupPTorsionFree_and_unitNormalization`
* `cyclotomicPrincipalizationNonFirstCaseDescentExistence_of_classGroupPTorsionFree_and_unitNormalization`
* `cyclotomicPrincipalizationNonFirstCasePeelDescentExistenceCore_of_classGroupPTorsionFree_and_unitNormalization`

の no-sorry chainへ、引数の並べ替えだけで寄せられるかどうかじゃ。
今回の報告を読む限り、かなり寄せられる可能性が高い。なぜなら Stage 3 receiver 群はすでに no-sorry 側へ移され、sorry 監視から外されておるからじゃ。

## 7. やらない方がよいこと

ここで新しい receiver target をさらに切るのは、おそらく筋が悪い。
理由は simple で、今回の latest で Stage 3 側 honest open はもう消えたからじゃ。
これ以上 receiver を細かくしても、old peel core の置換という本丸から遠ざかるだけになりやすい。

## 8. 総括

ひとことで言えば、いまはこうじゃ。

$$
\boxed{
\text{新しい mainline は勝った。残るのは old peel core をその勝ち筋へ載せ替える作業じゃ。}
}
$$

なので、次の最善手は

$$
\boxed{
\text{`cyclotomicPrincipalizationNonFirstCasePeelDescentExistenceCore\_of\_classGroupPTorsionFree`
を no-sorry norm route の thin wrapper に置換できるか検査し、できるなら直に置き換える。}
}
$$

これが通れば、進捗率はまた少しどころか、かなり綺麗に上がるはずじゃよ。
