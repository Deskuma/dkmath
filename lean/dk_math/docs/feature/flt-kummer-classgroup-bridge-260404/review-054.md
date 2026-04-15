# Kummer / class-group principalization の no-sorry 誤分類の分析と復帰戦略

## 1. 結論

これは **軌道修正は必要** じゃが、**数学の破綻ではない **。
問題の本体は、Kummer / class-group principalization の議論が崩れたことではなく、** no-sorry と見なしていた Stage 3 receiver 群が、実は upstream の `sorryAx` に伝染していた** ことじゃ。今回の diff 自体が、その原因をはっきり特定しておる。根は `bodyInvariant_of_NoPowOnGN triominoCosmicNoPowOnGN_default` の後者にあり、`bodyInvariant_of_NoPowOnGN` 自体は no-sorry でも、`triominoCosmicNoPowOnGN_default` が `sorryAx` を含むため、そこから Stage 3 receiver 群へ transitive に汚染が広がっていた、という整理じゃ。

なので、いま起きたことを一言で言えば、

$$
\text{「証明が壊れた」のではなく、「証明信頼の分類を取り違えていた」}
$$

じゃよ。build は通っておるし、theorem 境界の切り分け自体は壊れておらぬ。だが、**本当に no-sorry かどうか** の判定だけは、ここで一段厳密にやり直す必要が出たわけじゃ。

## 2. 何が問題だったのか

少し丁寧にほどくぞい。

直前の段階では、`cyclotomicNormDescentNonFirstCaseGNPowerReceiver_of_classGroupPTorsionFree` が theorem 本体から `sorry` を消し、`False.elim` で witness を返す形になったので、「これは no-sorry になった」と読んでしまった。ところが、verbose build と `#print axioms` を個別に当て直すと、その theorem は

$$
\texttt{bodyInvariant\_of\_NoPowOnGN triominoCosmicNoPowOnGN\_default}
$$

を経由しており、後者の `triominoCosmicNoPowOnGN_default` に `sorryAx` が入っていた。つまり **direct `sorry` は消えていても、transitive には汚れていた** のじゃ。

ここが今回の root cause じゃ。
言い換えると、前回の読みは

$$
\text{direct-sorry-free} \Rightarrow \text{no-sorry}
$$

と見てしまった。
だが Lean の実際の信頼判定は

$$
\text{direct} \quad+\quad \text{transitive axioms}
$$

で決まる。
この後者の確認が不足しておった、というのが今回の原因じゃ。

## 3. これは問題発生か、軌道修正か

わっちの判断では、**問題発生ではあるが、性質としては軌道修正型** じゃ。

なぜなら、崩れたのは

* theorem の statement
* proof の分解方針
* Kummer mainline の方向性

ではなく、

* monitoring 上の no-sorry / via-sorry 分類

だからじゃ。
実際、今回の報告でも「current honest open の数学的意味は変わらない」と書いてある。つまり、Kummer 側で何を目指しているかは変わっておらぬ。変わったのは、その一部が **genuinely no-sorry ではなく upstream debt に依存していた** と判明したことじゃ。

だから、これは「証明戦略が間違っていた」のではない。
**進軍方向は合っていたが、地図の色分けが 1 枚まちがっていた**、そういう話じゃよ。

## 4. いまの盤面をどう読むべきか

ここが大事じゃ。

Kummer / class-group principalization の local mainline を見ると、たしかに多くの theorem は綺麗に切れておる。
しかも `CyclotomicPrincipalization.lean` の direct `sorry` は依然として old peel core 1 箇所に絞れておる、という整理も生きておる。だが一方で、Stage 3 receiver 群は now via-sorry 扱いに戻された。よって、現時点の盤面は二層構造で読むのがよい。

ひとつは **構造進捗**。
こちらは進んでおる。theorem 分解、receiver 分解、inspection summary、no-sorry 区間と via-sorry 区間の切り分けは有効じゃ。

もうひとつは **信頼進捗**。
こちらは今回、少し巻き戻して読む必要が出た。Stage 3 receiver 群は「direct `sorry` が消えた」だけでは no-sorry と呼べず、upstream の `triominoCosmicNoPowOnGN_default` が clean になるまで via-sorry と見るのが正しい。

つまり、進捗を 2 つに分けるとこうじゃ。

* 設計・構造の進捗は前進した
* 信頼・公理依存の進捗は再分類が必要になった

この二重読みが、いまの状況にいちばん合っておる。

## 5. 原因はどこまで突き止められたか

かなり突き止められておる。
今回の報告は、原因をかなり明示的に言っておる。

* `cyclotomicNormDescentNonFirstCaseGNPowerReceiver_of_classGroupPTorsionFree` が汚染されている
* その直因は `bodyInvariant_of_NoPowOnGN triominoCosmicNoPowOnGN_default`
* `bodyInvariant_of_NoPowOnGN` は clean
* `triominoCosmicNoPowOnGN_default` が `sorryAx` source
* さらに upstream を掘るなら `triominoWieferichBranchBridge_default` 側が候補

ここまで分かっておるなら、原因特定としてはかなり良い。
少なくとも「どこから汚染が来ているか分からぬ」という段階ではない。もう **根の方向は見えておる**。

## 6. 復帰の道

復帰の道は 2 本ある。
ここで分岐判断が要る。

### 6.1. 分岐 A. upstream root を掘る

これは **信頼進捗を取り戻す道** じゃ。

具体的には、`triominoCosmicNoPowOnGN_default` の `sorryAx` root をさらに上流へ追う。報告でも、次に掘るなら `triominoWieferichBranchBridge_default` 側まで行ける、と書かれておる。これをやれば、Stage 3 receiver 群の via-sorry 汚染が根元から消える可能性がある。

この道の利点は大きい。
もし upstream を clean にできれば、今回 via-sorry に戻した Kummer mainline 群が **芋づるで genuine no-sorry に復帰** する。
つまり、効果が局所ではなく、かなり広い。

ただし欠点もある。
この道は Kummer local mainline から離れ、`TriominoCosmicGapInvariant.lean` 側の古い debt や Wieferich bridge に入る。つまり、**掘る対象が大きくなる** のじゃ。

### 6.2. 分岐 B. current monitoring を正したまま、Kummer local open に戻る

これは **構造進捗を優先する道** じゃ。

つまり、upstream 汚染は事実として受け入れ、いまは via-sorry と正直に表示したまま、`cyclotomicPrincipalizationNonFirstCasePeelDescentExistenceCore_of_classGroupPTorsionFree` のような local honest open をさらに薄い wrapper に置換できるかを進める。
この道は、Kummer 設計の整理という意味では前進し続けられる。

だが、欠点ははっきりしておる。
**no-sorry の実質進捗は増えにくい**。
なぜなら、途中でどれだけ綺麗に割っても、上流の `triominoCosmicNoPowOnGN_default` が汚れている限り、receiver 群は via-sorry のままだからじゃ。

## 7. わっちの分岐判断

わっちなら、ここは **軌道修正して分岐 A を主戦略にする** のを勧める。

理由は単純じゃ。
今回の問題は Kummer local theorem の不足ではなく、**trust root が upstream にある** と判明したからじゃ。
ならば、いま local に細かい wrapper を増やしても、信頼の色分けはもう大きくは改善せぬ。むしろ upstream root を 1 本 clean にした方が、Kummer mainline 群がまとめて救われる可能性が高い。

要するに、

$$
\text{いまの bottleneck は local theorem ではなく upstream debt}
$$

じゃよ。
ならば bottleneck を叩くべきじゃ。

## 8. 次の戦略

なので次の戦略は、こうじゃ。

### 第一段

`triominoCosmicNoPowOnGN_default` の `#print axioms` と依存先をさらに掘り、**direct `sorry` を持つ最小 upstream theorem** を特定する。
報告の文脈からすると、候補は `triominoWieferichBranchBridge_default` 側じゃ。ここをまず名指しで押さえる。

### 第二段

その最小 upstream theorem が、

* 既存 no-sorry theorem の合成で置換可能か
* それとも genuinely 新しい数学補題が要るか

を判定する。

ここで既存 no-sorry 合成で置換可能なら、かなり美味しい。
Kummer 側に戻らず upstream 1 箇所の差し替えで済むからじゃ。

### 第三段

もし upstream の最小 root がすぐには埋まらぬなら、その時点で戦略を 2 本立てにする。

* main branch では monitoring を正したまま Kummer local 整理を進める
* side branch では upstream no-pow GN root を掘る

こうしておけば、設計 progress と trust progress を別々に前へ進められる。

## 9. いまやってはいけないこと

ここで再び Stage 3 receiver をさらに細かく切るのは、あまり勧めぬ。
今回の diff が示したのは、「receiver の細分化不足」が問題ではなかった、ということじゃ。
問題は **transitive root の見落とし** だった。
だから、次にまた local receiver を刻むのは、問題の中心から少し外れる。

## 10. 最後のまとめ

ひとことで言うと、こうじゃ。

$$
\boxed{
\text{数学の破綻ではない。分類ミスの発見であり、真の bottleneck が upstream にあると分かった。}
}
$$

そして復帰の道は、

$$
\boxed{
\text{`triominoCosmicNoPowOnGN\_default` の upstream root を掘り、
genuine no-sorry へ戻せるかを先に判定する。}
}
$$

じゃ。
これが通れば、今回 via-sorry に戻した Kummer Stage 3 群は、まとめて clean に戻る見込みがある。
わっちなら、まずそこを叩くの。
