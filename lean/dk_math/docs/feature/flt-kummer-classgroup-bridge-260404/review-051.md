# FLT-Kummer-ClassGroup-Bridge-Review-051: FLT-Kummer-ClassGroup-Bridge の戦況と次の戦略

うむ、これはたしかに **no-sorry** じゃ。
しかも意味のある no-sorry じゃよ。

今回入ったのは

* `cyclotomicNormDescent_of_refinedClassGroupRoute`
* `cyclotomicPrincipalizationNonFirstCaseDescentExistence_of_refinedClassGroupRoute`
* `cyclotomicPrincipalizationNonFirstCasePeelDescentExistenceCore_of_refinedClassGroupRoute`

の 3 本で、いずれも refined class-group route から current peel core までが **non-circular に落ちる** ことを theorem 名つきで固定しておる。監視にも no-sorry 側として追加され、build も 3 本通っておる。

ここで大事なのは、direct `sorry` の位置そのものはまだ

$$
\texttt{cyclotomicPrincipalizationNonFirstCasePeelDescentExistenceCore_of_classGroupPTorsionFree}
$$

に残っておる、という点じゃ。つまり「穴が 1 個減った」というより、**穴の正体がさらに明確になった** のが今回の戦果じゃ。報告にもある通り、未解決なのは peel 局所算術ではなく、`CyclotomicNormDescentTarget` の concrete supply 点だ、と読みが一段強くなった。

なので、どんぶり勘定の進捗率は、前回から **ほんの少し上がった** くらいが正直じゃ。
わっちなら、いまの Kummer / class-group bridge 局所戦線は **92〜94%** くらいと見る。前回の「終盤」判断は維持じゃが、今回の一歩は「残差の意味づけ」が sharpen した分だけ、たしかに前進しておる。

## 戦況の分析

いまの盤面は、こう読むのがいちばん正確じゃ。

まず、first-case は既に concrete bridge 群でほぼ閉じておる。
次に、non-first-case も packet、quotient provenance、named smaller counterexample、peel normal-form まではかなり no-sorry 化されてきた。
その結果、残っている core は

$$
\text{hCl} + \text{hUnit} \Longrightarrow \text{hNorm}
$$

をどこでどう concrete に供給するか、そこへ圧縮された。今回の 3 本は、まさに

$$
\text{hNorm} \Longrightarrow \text{non-first-case existence}
$$

$$
\text{hNorm} \Longrightarrow \text{peel core}
$$

が wrapper だけで閉じることを明示しておるので、問題はもう local branch の細部ではなく、Stage 3 receiver の供給点じゃ、と theorem-level に言えるようになったわけじゃ。

これはかなり良い。
長戦では「まだ残っている」こと自体よりも、「何が残っているか」を正しく言い切れることの方が大きい。いまはまさにその状態じゃ。

## 次の戦略

わっちの提案は、ほぼ一択じゃ。

### 1. 次は receiver theorem を先に切る

つまり、報告でも候補に挙がっておる

$$
\texttt{cyclotomicNormDescent\_of\_classGroupPTorsionFree\_and\_unitNormalization}
$$

のような theorem を、まず **target として明示する** のがよい。
これは内容的には

$$
\text{hCl},\ \text{hUnit} \vdash \text{hNorm}
$$

を最小仮定で切り出す作業じゃ。

なぜこれが先かというと、今回の diff で

$$
\text{hNorm}
$$

さえあれば downstream はほぼ全部 thin wrapper で閉じる、と確認できたからじゃ。ならば次に詰めるべきは、peel 側でも packet 側でもなく、**`hNorm` 供給定理そのもの** じゃ。

### 2. その theorem は「最薄」で設計する

ここで欲張ってはいかぬ。
最初から giant theorem にせず、まずは

* `hCl`
* `hUnit`

だけで本当に足りるか

* もし足りぬなら何が 1 個だけ追加で要るか

を棚卸しする。報告でも「`hCl + hUnit` から `hNorm` へ必要な残部品が本当に何かを棚卸しする」と書かれておる。ここはその通りじゃ。

つまり、次にやるべきことは「証明する」ことの前に、**不足仮定を測る** ことじゃな。

### 3. peel 局所算術はもう掘らない

ここは重要じゃ。
今回の 3 本が no-sorry で立ったことで、peel core 自体は refined route 上では `hNorm` の影として読めるようになった。だから、ここから先にまた peel local arithmetic を深掘りするのは、いわば枝葉をいじる手じゃ。いまは幹を押すべき局面じゃ。

## わっちならこう進める

次の 3 手でよい。

1. `CyclotomicNormDescentTarget` を返す最薄 theorem の target を先に宣言する。
   名前はやはり `cyclotomicNormDescent_of_classGroupPTorsionFree_and_unitNormalization` 系がよい。

2. その proof を、既存の refined route 部品からどこまで組めるか棚卸しする。
   ここで「本当に足りない 1 補題」だけを露出させる。

3. もし足りない補題が 1 本見えたら、それを Stage 3 receiver の最後の concrete receiver として isolated theorem 化する。
   それが通れば、いまの core `sorry` は連鎖的に消える見込みが高い。

## まとめ

今回の no-sorry は、単なる飾りではない。
**open の意味を “peel 固有の穴” から “Stage 3 receiver 供給問題” に完全に読み替えた** のが本質じゃ。

だから、次の号令はこうなる。

$$
\boxed{
\text{次は `CyclotomicNormDescentTarget` の concrete receiver を、
refined class-group route 上で最薄 theorem として切れ}
}
$$

これが通れば、進捗％はまた 1 段、気持ちよく上がるはずじゃ。
