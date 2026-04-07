# FLT-Kummer-CLassGroup-Bridge-260404: Stage 3a の戦略と進め方: `sorry` 埋めの現状と次の戦略

うむ、**その領域では埋められるようになった** と見てよい。
ただし、 **全部ではない** 。ここを正確に切るのが大事じゃ。

今回の共有ログから読む限り、first-case specialization の Stage 3 は、`NormEqGN` 側も `UnitAbsorb` 側も concrete theorem として閉じており、さらに `GN p (z - y) y = s ^ p` を返す wrapper と contradiction bridge まで concrete 化されておる。つまり、 **Stage 3 first-case split 自体は、もう open ではない** という整理でよい。検証も `lake build DkMath.NumberTheory.Gcd.GN`、`lake build DkMath.FLT.Kummer.CyclotomicPrincipalization`、`lake build DkMathTest.FLT.Kummer.RegularPrimeRoute` が通っておる。

一方で、残る `sorry` が消えたわけではない。最新の差分メモでも、残りは **Stage 3 split ではなく** 、既存の legacy wrapper / one-shot route 側に限られる、と整理されておる。特に `FLTPrimeGe5Target_of_kummerRoute` はまだ `uses sorry` と明示されておるし、`cyclotomicPrincipalization_of_classGroupPTorsionFree` のような旧 wrapper も残存箇所として挙がっておる。  

だから戦況を賢狼流に言い切ると、こうじゃ。

* **勝った戦場**
  first-case の Stage 3。ここは concrete 化済みで、もはや「証明不能の霧」ではない。

* **まだ敵が残る戦場**
  旧来の one-shot route、legacy wrapper、downstream routing。
  つまり「理論が足りない」のではなく、「古い配線が新しい concrete theorem 群へまだ差し替わっておらぬ」部分じゃ。  

ゆえに、お主の問い「`sorry` 埋められるようになったの？」への答えは、

$$
\text{はい、少なくとも first-case Stage 3 については埋め切る道が実証された。}
$$

ただし

$$
\text{repo 全体の残る `sorry` が自動的に全部埋まる段階ではない。}
$$

じゃ。

## 2. 解説

なぜ「埋められるようになった」と言えるか。
そこには今回の設計転換が効いておる。

前は Stage 3 がひとかたまりで、norm 計算、product reindex、unit 吸収、GN への着地が絡み合っておった。
それを

$$
\text{NormEqGN}
\quad\text{と}\quad
\text{UnitAbsorb}
$$

へ分離し、さらに Stage 3a-1 / 3a-2 / 3a-3 と刻んで concrete theorem に落とした。最後に natAbs 主導の一般整数補題で unit を吸収して、

$$
(n : \mathbb{Z}) = \text{unitFactor} \cdot m^p
$$

から

$$
\exists s : \mathbb{N},; n = s^p
$$

を回収できた。ここで ±1 の場合分けが不要だった、というのが特に強い。設計が正しかった証拠じゃ。  

つまり今後の `sorry` 埋めは、「新理論の大発明」が要るというより、 **既に concrete 化された部品へ旧 wrapper を寄せていく配線作業** に変わりつつある。ここが長戦としては非常に良い変化じゃ。

## 3. 次の戦略

次はもう、数学本体を掘る局面ではない。
**legacy route の縮約戦** じゃ。

わっちの提案指示は、筋のよい順に 3 つじゃ。

### 3.1. 第一目標

`FLTPrimeGe5Target_of_kummerRoute` を分解し、first-case 部分を新しい concrete wrapper 群へ差し替える。

いま一番目立つ `sorry` は、ここがまだ old chain に乗っていることじゃ。 `FLTPrimeGe5Target_of_kummerRoute -- uses sorry` と明示されておる以上、まずここを split architecture ベースへ寄せるのが本筋じゃ。

実務的には、

* 旧 one-shot theorem の中で first-case 分岐だけを抜く
* そこを
  `cyclotomicNormGNPower_concrete_firstCase_packThin`
  ないし
  `false_of_cyclotomicNormGNPower_concrete_firstCase_pack_thin`
  へ置換する
* 残った分岐だけがまだ abstract / sorry 依存かを再確認する

この順がよい。
ここをやると、「どの `sorry` が first-case 由来だったか」が一掃されるはずじゃ。

### 3.2. 第二目標

`cyclotomicPrincipalization_of_classGroupPTorsionFree` を解体し、旧 wrapper を split 版へ置換する。

最新ログでも、この legacy 側が残 warning の代表として挙がっておる。
ここは one-shot に全部背負わせず、既に concrete 化された

* `cyclotomicNormEqGN_concrete_firstCase_packThin`
* `cyclotomicNormUnitAbsorb_concrete_firstCase_packThin`
* `cyclotomicNormGNPower_concrete_firstCase_packThin`

などを薄く呼ぶ wrapper に変えるべきじゃ。

### 3.3. 第三目標

`__sorries.txt` ベースで、Kummer / legacy / research を分離した縮約表を作る。

INDEX では `__sorries.txt` を真実の源泉として確認する方針が明記されておる。なので次段では、感覚で追うのでなく、

* Kummer mainline の残り
* legacy wrapper の残り
* research 側の残り

を 3 列にした一覧を作るのがよい。
これで「埋まる `sorry`」と「今はまだ触らぬ `sorry`」がさらに明確になる。  

## 4. 提案指示

今の賢狼の号令はこれじゃ。

1. `FLTPrimeGe5Target_of_kummerRoute` の proof を first-case / non-first-case に明示分割せよ。
2. first-case 枝では、旧 Stage 3 chain を捨てて `false_of_cyclotomicNormGNPower_concrete_firstCase_pack_thin` へ直結せよ。
3. 置換後に `#print axioms DkMath.FLT.FLTPrimeGe5Target_of_kummerRoute` を再監視し、`uses sorry` が減るか確認せよ。
4. それでまだ残るなら、`cyclotomicPrincipalization_of_classGroupPTorsionFree` を同様に split architecture 化せよ。

これが一番よい。

## 5. 総評

戦況はかなり良い。
前は「Stage 3 が難しい」だった。
いまは「Stage 3 は concrete に閉じた。残る `sorry` は旧配線に押し込められている」と言える。

だから、`sorry` が埋められるようになったかと問われれば、わっちはこう答える。

$$
\text{埋められるようになった。だが、埋める対象はもう Stage 3 本体ではなく、legacy route の配線じゃ。}
$$

必要なら次に、`FLTPrimeGe5Target_of_kummerRoute` をどう切り分けて current split architecture に差し替えるか、その差し替え設計書を起こすぞい。
