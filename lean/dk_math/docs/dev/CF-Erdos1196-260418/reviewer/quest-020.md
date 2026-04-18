# ABC予想の形への「かなり近づいた」定理スキーマ

うむ、**かなり近づいた** と言ってよい。
ただし、**「ABC予想そのものをもう示した」ではなく、「ABC予想が主張する不等式の形に、かなり近い定理スキーマが Lean 上に立った」** という意味じゃ。

今回の差分の本体は、`rad c` 側の budget から直接

$$
c \le \bigl(\mathrm{rad}(a*b*c)\bigr)^{\,1+\delta+\gamma}
$$

を作り、その後 `\delta+\gamma \le \varepsilon` を使って既存の analytic bridge へ流す route を入れたことじゃ。具体的には `radAbcBound_of_pi_targetRadTail` がこの growth bound を与え、`quality_le_of_pi_targetRadTail_of_radAbc` がそれを `quality \le 1+\varepsilon` へ送っておる。さらに `quality_le_of_not_bad_with_targetRadTail_on_radAbc` で `¬Bad` 版 wrapper まで入った。ここは、まさに **ABC予想の「(c) を (\mathrm{rad}(abc)^{1+\varepsilon}) 型で抑える」形** に近い。

数学的に見ると、今回の route はかなり自然じゃ。
`ABC038` 側で元から使っている分解

$$
c = \pi\mathrm{SqRad}(c),\mathrm{rad}(c),\mathrm{twoTail}(c)
$$

に対して、

$$
\pi\mathrm{SqRad}(c) \le \mathrm{rad}(a*b)^\delta,
\qquad
\mathrm{twoTail}(c) \le \mathrm{rad}(c)^\gamma
$$

を入れる。すると

$$
c \le \mathrm{rad}(a*b)^\delta \cdot \mathrm{rad}(c)^\gamma \cdot \mathrm{rad}(c)
$$

となり、各 radical を `\mathrm{rad}(a*b*c)` へ持ち上げれば

$$
c \le \bigl(\mathrm{rad}(a*b*c)\bigr)^{\,1+\delta+\gamma}
$$

が出る。
この「(+1) は (\mathrm{rad}(c)) そのもの、(\delta) は (\pi\mathrm{SqRad}) 側、(\gamma) は tail 側」という分解は、とても ABC 的じゃ。今回はそれを theorem 名つきで固定できたのが大きい。

なので、お主の問いにまっすぐ答えるなら、

**はい、主張のカタチにはかなり近づいた。**

ただし、まだそのまま ABC予想の完成形ではない。
理由は、今回の route がまだ次の仮定を要しておるからじゃ。

* `¬Bad` から来る
  $$
  \pi\mathrm{SqRad}(c) \le \mathrm{rad}(a*b)^\delta
  $$
* target-rad tail budget
  $$
  \mathrm{twoTail}(c) \le \mathrm{rad}(c)^\gamma
  $$
* 指数整理
  $$
  \delta+\gamma \le \varepsilon
  $$
* さらに analytic bridge 側の
  $$
  1 < \mathrm{rad}(a*b*c)
  $$
  のような補助仮定

つまり今あるのは、

$$
\text{「ABC予想の最終形そのもの」}
$$

ではなく、

$$
\text{「ABC予想の最終形にかなり似た quality bound を導く中間定理群」}
$$

じゃな。

じゃが、ここは過小評価せぬほうがよい。
前回までの route は

$$
\text{channelCount}
\to
\mathrm{rad}(c)
\to
\mathrm{rad}(u*v)
\to
\text{TailBound}
\to
\text{quality}
$$

という、やや transport 依存の流れが主じゃった。
今回の差分で、それとは別に

$$
\text{channelCount}
\to
\mathrm{rad}(c)
\to
\mathrm{rad}(a*b*c)
\to
\text{quality}
$$

という **analytic 直結 route** が立った。
これは、前回までの「橋の前庭」から一歩進んで、**本丸の不等式の形へ直接向かう通路** が見えた、ということじゃ。

現況を賢狼ふうにまとめると、こうじゃ。

* **Yes**
  形としてはかなり近い。
* **No**
  まだ ABC予想そのものを閉じたわけではない。
* **But**
  いまや `c ≤ rad(abc)^{1+\delta+\gamma}` という骨格が theorem 名で立ったので、
  「ABC の形に寄せる」段から
  「どの仮定を削れば本体に近づくか」を検討する段へ入った。

つまり今は、

**「橋を作っていた段階」から、「本丸の門に合う形へ石を削る段階」へ移った**

と見てよいぞい。

次に見るべき本当の焦点は二つじゃ。
ひとつは、この `rad(abc)` 直結 route の **concrete sample** を 1 本足して、仮定の手触りを確かめること。
もうひとつは、`ABC038` 側の convenience theorem 群のどこにこの route を差し込むのが最も薄いか、つまり **既存 theorem をどこで置換・補強できるか** を見極めることじゃ。

## 登山ルート

> Q.
> いままで実装してきた、アプローチとはまた違った登山ルートが開拓されたと見るべきなのか？
> それとも、既存アプローチの登山ルートで阻んでいた崖を登りきれたという状況なのだろうか？

わっちの見立てでは、 **両方** じゃ。
ただし、階層が違う。

## 1. 大局では「別ルートの開拓」

ABC 形式化全体という大きな地図で見るなら、これは **今までの主登山ルートとは違う側面から登る新ルート** じゃ。

従来の本線は、`ABC038` やその周辺で既に持っている

* `¬Bad`
* `TailBound`
* analytic bridge
* quality bound

という既存 machinery を中心に進んでおった。
そこへ今回、新しく

$$
\text{PrimitiveWitnessFamily}
\to
\text{channelCount}
\to
\mathrm{rad}(c)\text{ 下界}
$$

という spine を持ち込み、さらに

$$
\mathrm{rad}(c)\text{ budget}
\to
\mathrm{rad}(abc)\text{ analytic bridge}
\to
\text{quality}
$$

まで繋いだ。これは、以前の「bad set / tail / analytic」主導の見方とはかなり違う入口じゃ。
その意味では、 **新しい登山ルートを一本開拓した** と言ってよい。

## 2. しかし局所では「既存ルートの崖を登りきった」

一方で、今回の差分は単なる別働隊ではない。
なぜなら最終的に接続した先は、完全に既存の `ABC038` machinery だからじゃ。

今回入った

* `radAbcBound_of_pi_targetRadTail`
* `quality_le_of_pi_targetRadTail_of_radAbc`
* `quality_le_of_not_bad_with_targetRadTail_on_radAbc`

は、どれも **既存の quality bridge に接続するための中間補題** じゃ。
特に `quality_le_of_pi_targetRadTail_of_radAbc` は、既存の `quality_le_of_sqprod_pow_bound_analytic_axiom_to_lemma` へそのまま流し込んでおる。つまり、新ルートで登ってはいるが、山頂直下では既存の尾根道へ合流しているわけじゃな。

この意味では、 **既存アプローチで長く阻んでいた「`rad(c)` から quality へどう入るか」という崖を、別角度から登り切って既存尾根に合流した**、とも言える。

## 3. どちらが本質に近いか

問いに一番短く答えるなら、こうじゃ。

**大局では新ルート、局所では既存ルートへの合流成功。**

もう少し噛み砕くと、

* `PrimitiveWitnessFamily`・`channelCount`・`supportMass`・`rad(c)` budget という発想は、これまでの ABC コアの主導語彙ではなかったので **新ルート**
* しかし最終的に `ABC038` の quality bound へ流したので、単なる独立峰ではなく **既存ルートの崖を別方向から突破した**

という構図じゃ。

## 4. なぜ「単なる別ルート」では済まないのか

もし今回の成果が本当に別ルートなだけなら、既存 `ABC038` 群とは平行線のままで終わるはずじゃ。
じゃが実際には、前回まで transport route で苦しんでいた

$$
\mathrm{rad}(c) \to \mathrm{rad}(u*v)
$$

をいったん脇へ置き、今回

$$
\pi\mathrm{SqRad}(c)\text{ budget}
\quad+\quad
\mathrm{twoTail}(c)\le (\mathrm{rad}(c))^\gamma
$$

から直接

$$
c \le \bigl(\mathrm{rad}(abc)\bigr)^{1+\delta+\gamma}
$$

を作って、そのまま analytic bridge へ入った。
これは「別ルートを眺めている」のではなく、**既存本線の核心障害物を別の道具で越えた** ということじゃ。

## 5. いまの到達点を登山で喩えるなら

たぶん、いちばん正確な喩えはこれじゃ。

**新しい支尾根を開いて登り始めたら、それが思った以上に山頂直下の既存主稜線へ繋がっていた。
そして今、その合流点に立った。**

つまり、

* まだ山頂そのものではない
* しかし単なる偵察路でもない
* 主稜線への合流点が実際に確保できた

という状況じゃな。

## 6. 数学的に何が起きたかを一行で言うと

これまでの route は主に

$$
\text{bad / tail / transport}
$$

主導で、`rad(c)` は中間情報に留まりがちじゃった。
今回の route は

$$
\text{primitive channels}
\to
\text{channelCount}
\to
\mathrm{rad}(c)\text{ budget}
\to
\mathrm{rad}(abc)\text{ growth}
\to
\text{quality}
$$

という流れを作った。
だから、 **「rad(c) 側から本丸へ入る道」が現実化した** のじゃ。

## 7. わっちの最終判断

ゆえに、どちらか一方だけで表すなら不正確じゃ。

* 「全く別ルート」だけでは足りぬ。既存 quality machinery に合流しておるから。
* 「既存ルートの崖を少し登っただけ」でも足りぬ。入口の発想自体が新しいから。

わっちならこう言う。

**これは、新ルートの開拓に成功し、その新ルートが既存本線の難所突破に実際に効くことまで示せた段階じゃ。**

かなり良い位置まで来ておるぞい。

### 別働隊と合流して崖を登りきれた

うむ、まさにそんな感じじゃ。
その喩えはかなり合っておる。

これまでの主隊は、既存の `ABC038` 系の尾根道、つまり

* `¬Bad`
* `TailBound`
* analytic bridge
* quality bound

を登っておった。
しかし途中で、`rad(c)` や primitive-channel 的な情報をどう本線に流し込むか、という崖があった。

そこで別働隊として、

$$
\text{PrimitiveWitnessFamily}
\to
\text{channelCount}
\to
\mathrm{rad}(c)\text{ budget}
$$

のルートを開いた。
最初は「別の尾根かもしれぬ」と見えたが、実際にはその先で

$$
c \le \bigl(\mathrm{rad}(abc)\bigr)^{1+\delta+\gamma}
$$

という形を経由して、既存の analytic bridge に合流できた。
だから今の状態は、

**別働隊が先に登って、主隊が越えられずにいた崖の上にロープを垂らし、そこで本隊と合流した**

という感じじゃな。

大事なのは、この別働隊が単なる偵察では終わらなかったことじゃ。
本当に合流点を作れたから、もう「面白い別案」ではなく、既存アプローチの有効な補給路・突破路になった。
そこが今回の価値じゃよ。

ただし、まだ山頂そのものではない。
合流して崖を越えた、というのが今の到達点で、その先にまだ summit ridge が残っておる。
じゃが、越えられぬと思っていた断崖に、ちゃんと通れるルートが付いたのは大きいのぅ。
