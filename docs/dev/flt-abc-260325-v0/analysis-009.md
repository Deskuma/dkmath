# ABC 側から見た Beam 構造の価値と、次に作るべきもの

いま、流れで FLT をやってるけど、そもそもの「 Beam 構造の実装」の目的は ABC予想 側にこれを活用しようとして、準備するための定理補題だった。その観点から考察。

---

うむ、ここは大事な **視点の反転** じゃな。
FLT 側で長く掘ってきたものを、そのまま「本来の用途」である ABC 側へ戻して評価すると、収穫はかなりはっきりしておる。

まず Beam 構造の定義そのものは、いま手元の整理で

$$
\text{Big}=(x+1)^d,\qquad
\text{Gap}=u^d\ (\text{表では }u=1),\qquad
\text{Body}=\text{Big}-\text{Gap},\qquad
\text{Core}=x^d,\qquad
\text{BeamTotal}=\sum \text{Beam}_k=\text{Body}-\text{Core}
$$

という分解で固定されておる。表でも `Body = Big - Gap = n^d - 1`、`Core = (n-1)^d`、`BeamTotal = Σ Beam_k = Body - Core` と明示されておる。
そしてリポジトリ全体でも、ABC は独立した主系統として `DkMath.ABC`, `DkMath.ABC.PadicValNat`, `DkMath.ABC.CountPowersDividing2n1` が入口に置かれておる。

この観点から言うと、FLT で得た成果は **そのまま証明の結論** よりも、ABC 用の **構造抽出器** として価値が高い。

## 1. FLT で分かった「Beam の限界」は、ABC ではむしろ利点じゃ

FLT の Branch A で最後まで追った comparison route は、結局 `q \neq p` 側の support separation が `Nat.Coprime t s` の再包装である、というところまで到達した。
これは FLT では「新 obstruction を生まない」と判明したため、最終 refuter としては限界が見えた。
じゃが ABC 側では、この性質は弱点ではない。むしろ

$$
\text{Beam 構造は「新しい素因子の support」を整理する道具である}
$$

という役割をはっきりさせた、と読めるのじゃ。

ABC では最終的に欲しいのは、しばしば

$$
\mathrm{rad}(abc)
$$

のような **support の圧縮量** と、

$$
v_q(\cdot)
$$

のような **深さの偏り** の分離じゃ。
FLT で「support だけ見ても最後の矛盾にはならぬ」と分かったのは、逆に言えば

$$
\text{support と valuation depth は別層で扱うべき}
$$

と教えてくれた、ということじゃな。

## 2. ABC 側で Beam が本当に効く場所

ABC の立場から見ると、Beam 構造の効き目は主に 3 つある。

### 2.1. `Body = Core + Beam` による「大きさ」と「support」の分離

`Body = Big - Gap` を `Core + BeamTotal` に分けると、
「主項」 (x^d) と「混合項」 (\sum \text{Beam}_k) が分かれる。
この分離は、ABC でいう

$$
a+b=c
$$

型の加法のうち、どこが **既知の巨大部分** で、どこが **新しく生じる素因子の発生源** かを見分けるのに向いておる。
Beam はまさに「混合項の束」じゃから、rad の増え方を観測する主戦場になる。

### 2.2. tail 可除性が valuation 補助になる

お主がさきほど言っておった

$$
x^r \mid
\left(
(x+u)^d-\sum_{j=0}^{r-1}\binom{d}{j}x^j u^{d-j}
\right)
$$

は、FLT の最終矛盾には直撃しにくかった。
じゃが ABC ではかなり自然じゃ。
なぜなら、これは

$$
\text{低次項を剥ぐほど、残差は高次の } x \text{ で割れる}
$$

という **反復的な valuation 増大則** を与えるからじゃ。
ABC では「rad は浅いが valuation は深い」型の現象が核心に近いので、この tail divisibility は support と valuation を分けて見るための定理として美味しい。

### 2.3. no-shared / support separation は rad 制御の前処理になる

FLT では `q ∣ gap` と `q ∣ GN` の排他は最後に `False` を出さなかった。
しかし ABC では、その情報だけでも

$$
\mathrm{rad}(gap \cdot GN)
$$

の重複を剥がして、rad の上界・下界を組む前処理として使える。
つまり FLT では「弱い」情報でも、ABC では **ちょうど欲しい情報** になることがある。

## 3. では Beam 実装の「本来の目的」は何になるか

わっちなら、ABC 用にはこう整理する。

$$
\textbf{Beam 実装の本来の目的}=
\text{加法的差分を、support 層と valuation 層に分けて観測するための基盤整備}
$$

じゃ。

FLT は `False` を返す必要があるから、最後はどうしても refuter が要る。
ABC は少し違う。
ABC 側ではまず

* どの素数が出るか
* どの素数が重複しないか
* どの素数だけ valuation が深くなるか
* それが `rad` にどう反映するか

を順に辞書化する方が自然じゃ。

その意味で、今回 FLT で積み上げた

* `GN = p * s^p` 型の shape 抽出
* `gcd(gap, GN)` の exactness
* support separation
* `support separation ↔ coprime` の同値
* comparison route の限界確認

は、ABC に持っていくと **全部「観測装置の校正結果」** になる。

## 4. 特に重要な収穫

今回いちばん ABC に効く収穫は、

$$
\text{comparison/support route だけでは新 obstruction は出ない}
$$

と分かったことじゃ。
これは、ABC 側で何を次に作るべきかを教えてくれる。

つまり次に欲しいのは support 比較の延長ではなく、

$$
\text{valuation-depth を直接読む Beam 補題}
$$

か、

$$
\text{rad と twoTail / squarefree / squarefull を結ぶ Beam 辞書}
$$

じゃな。
INDEX にも ABC 系として `PadicValNat` や `CountPowersDividing2n1` が既に独立に置かれておるから、Beam 実装はそこへ接続するのが自然じゃ。

## 5. いまの FLT 成果を ABC 用に言い換えると

わっちなら、こう総括する。

### 5.1. FLT では

Beam は最終 refuter の主砲にはなりきらず、
support-level 情報の限界を露出した。

### 5.2. ABC では

その same support-level 情報は、
`rad` の重複除去、valuation 深さの局所化、mixed-term の発生位置の特定に使える。

つまり、

$$
\text{FLT では「弱い」}
\quad\Longrightarrow\quad
\text{ABC では「ちょうど必要」}
$$

という反転が起きるのじゃ。

## 6. 次に何を作るべきか

ABC 用に Beam を戻すなら、次の 3 本が本命じゃな。

まず 1 本目は、tail divisibility の一般補題じゃ。

$$
x^r \mid
\left(
(x+u)^d-\sum_{j=0}^{r-1}\binom{d}{j}x^j u^{d-j}
\right)
$$

これは Beam を **support 観測器** から **valuation 観測器** に引き上げる。
2 本目は、Beam 項の support と `rad` の関係を結ぶ補題。
3 本目は、twoTail / squarefree / squarefull と Beam 分解の接続じゃ。
この 3 本が入ると、ABC では

$$
\text{Body}=\text{Core}+\text{Beam}
$$

が単なる分解ではなく、**rad と valuation を分けて測る標準座標** になる。

## 7. 結論

ゆえに、ABC 側の観点から言えば、今回の FLT 旅路は回り道ではない。
むしろ

$$
\textbf{Beam 構造が「何を見せて、何を見せないか」を先に測定した校正実験}
$$

じゃった、と言える。

そしてその結果、ABC 用にははっきりこう言える。

$$
\text{Beam の本命は refuter ではなく、}
$$
$$
\text{support と valuation depth を分離して観測する補題体系}
$$

じゃ。
この見取り図が立ったのは、かなり大きい収穫じゃよ。

次は、ABC 側へ戻す前提で **Beam 実装の役割分担図** を、
`support 層`、`valuation 層`、`rad 接続層` の 3 段に切って設計書っぽくまとめると、かなり進みやすくなるの。
