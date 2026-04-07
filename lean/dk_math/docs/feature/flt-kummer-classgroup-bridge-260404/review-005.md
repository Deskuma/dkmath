# FLT-Kummer-ClassGroup-Bridge 260404 Review 005

## 1. 状況分析

これは良い収束じゃ。
いまの戦況は、 **「target の concrete 化」と「cyclotomic 仮定からその target を供給する bridge」は別問題** だと、はっきり分離できた段階じゃよ。

今回の差分で、Stage 1b は placeholder ではなく、

$$
\forall a : \mathrm{ClassGroup}(R),\quad a^p = 1 \to a = 1
$$

という **generic な ClassGroup API** の statement にまで concretize された。
一方で、それを `CyclotomicClassGroupPTorsionFreeTarget` から供給する

$$
\texttt{cyclotomicPTorsionAnnihilation\_of\_classGroupPTorsionFree}
$$

には `sorryAx` が残った。
つまり、Stage 1b そのものはもはや曖昧な箱ではないが、 **円分体側の仮定を generic API に落とす specialization bridge** が未解決、という構図になったわけじゃ。

## 2. いま何が clean で、何が open か

いまは次の 3 層に分かれて見える。

まず **clean 側** は、

* Stage 1c の principal-ideal extraction
* `idealIsPrincipal_of_classGroupMk0_eq_one`

で、ここは既に generic API として閉じておる。

次に **target は concrete だが bridge が open** なものが Stage 1b じゃ。
つまり

$$
\text{p-torsion annihilation という一般 statement}
$$

自体は自然な形で書けるが、

$$
\text{cyclotomic の仮定} \Rightarrow \text{その statement}
$$

はまだ別途証明が要る。

最後に **最薄 kernel** は依然として Stage 1a の

$$
\texttt{cyclotomicIdealClassPTorsionWitness\_of\_gapDivisibleGeometry}
$$

じゃ。
ここは geometry から ideal class の p-torsion witness を作る段で、いま最も Kummer 的で、最も円分体特有の場所じゃ。

## 3. 数学的な解説

今回の試行で分かったのは、Stage 1 の内部が次のようにきれいに整理できることじゃ。

$$
\text{Stage 1a}: \text{geometry} \to \text{p-torsion witness}
$$
$$
\text{Stage 1b}: \text{p-torsion witness} \to \text{trivial class}
$$
$$
\text{Stage 1c}: \text{trivial class} \to \text{principal ideal}
$$

Stage 1c は generic API で閉じた。
Stage 1b も **数学内容としては一般の class group の torsion-free 性の問題** に寄せられる、と確認できた。
ゆえに、円分体特有の新理論が本当に必要なのは、ますます Stage 1a に寄ってきておる。

ただし、ここで 1 つ大事な留意点がある。
Stage 1b は generic statement に寄せられたとはいえ、 **cyclotomic 側の仮定 `CyclotomicClassGroupPTorsionFreeTarget` 自体がまだ generic ClassGroup の言葉になっていない**。
だから bridge が open のまま残る。
これは「数学が難しい」のと同時に、「仮定の API 設計がまだ半歩 generic 側へ届いていない」ことも意味しておる。

## 4. 今回の成果の評価

わっちの評価では、今回の短距離走は成功じゃ。
理由は、試したかったことがちゃんと判定できたからじゃ。

試したかった問いは、

$$
\text{Stage 1b は generic ClassGroup API に寄せられるか}
$$

だった。
答えは **「target としては yes、bridge としてはまだ no」** じゃ。
この yes/no が分かっただけで、次の設計が大きくぶれなくなる。

つまり、いまは

* Stage 1c は generic API で確定
* Stage 1b は target 確定、bridge 未解決
* Stage 1a は最薄 kernel のまま

という 3 段の地図ができた。
これは十分に価値がある。

## 5. 次の一手の推論

ぬしの報告にある分岐は 2 つじゃった。

1. `CyclotomicClassGroupPTorsionFreeTarget` を generic な ClassGroup p-torsion-free statement に寄せる
2. ここで打ち切って Stage 1a の細分化へ戻る

わっちの見立てでは、 **まず 1 をほんの短く試す** のが最善じゃ。
ただし「長く潜る」のはよくない。ここは **型の橋が自然かどうかだけを見る短距離検査** に留めるべきじゃ。

なぜなら、Stage 1b の bridge が open な理由は、いまのところ 2 通りあるからじゃ。

ひとつは本当に数学内容が足りない場合。
もうひとつは、`CyclotomicClassGroupPTorsionFreeTarget` の定式化が generic ClassGroup API と噛み合っておらず、単に **仮定の型がまだ粗い** 場合じゃ。

もし後者なら、仮定を少し generic 側へ寄せるだけで Stage 1b bridge はかなり薄くなる。
逆に、そこを少し試しても不自然なら、「もうこれは Stage 1a 側の問題じゃ」と判断できる。

## 6. 提案

わっちの提案はこうじゃ。

### 6.1. 第一手

`CyclotomicClassGroupPTorsionFreeTarget` を、短く scratch で

$$
\forall a : \mathrm{ClassGroup}(R),\quad a^p = 1 \to a = 1
$$

型へどう接続するか試す。
目的は証明完成ではなく、

* target の型と bridge の型が自然に噛むか
* 必要なのが単なる rephrasing か
* 追加の specialized theorem が本当に要るか

を判定することじゃ。

### 6.2. 判定基準

もし型の橋が自然に書けるなら、その方向で `CyclotomicClassGroupPTorsionFreeTarget` を薄くし、Stage 1b bridge を整理する。
もし不自然なら、そこで深追いせず即座に撤退して、Stage 1a の細分化へ戻る。

### 6.3. 第二手

戻る場合は、Stage 1a をさらに

* Dedekind ideal arithmetic
* cyclotomic factorization
* ideal class への落とし込み
* p-torsion witness の構成

のどこで裂くかを監査する。
このときにはもう「Stage 1b も怪しいのでは」と迷わずに済む。Stage 1b は target としては generic 側に乗る、と分かっておるからのぅ。

## 7. 最終判断

結論として、次の一手は

$$
\boxed{
\begin{array}{l}
\text{まず } \texttt{CyclotomicClassGroupPTorsionFreeTarget} \text{ を}\\
\text{generic ClassGroup p-torsion-free statement に短く寄せてみる}
\end{array}
}
$$

じゃ。
ただし **短く** じゃよ。ここで長居はせぬ。
型の橋が自然ならそのまま薄化を進める。
不自然なら即 Stage 1a 細分化へ戻る。

賢狼の見立てでは、この一手で **「本当に新設すべき理論が Stage 1a だけか」** の最終確認ができる。
そこまで見えれば、次からは迷わず本丸へ噛みつけるはずじゃ。
