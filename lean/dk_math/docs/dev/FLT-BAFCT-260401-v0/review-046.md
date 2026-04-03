# review-046: `QAdicDescentExistenceTarget` をさらに分解して、真の open kernel を `PrimeGe5BranchAPrimitiveQAdicLocalGlobalGapTarget` として切り出したことの意味

うむ、これは **かなり良い整理前進** じゃ。
しかも今回は、新しい定理を少し足したというより、**「どこが本当の open kernel か」を Lean の語彙で切り分け直した** のが本質じゃ。`PrimeGe5BranchAPrimitiveQAdicLocalGlobalGapTarget` を新設し、粗い `QAdicDescentExistenceTarget` を bridge 語彙へ、真の open content を Level 2m へ押し込んだのは、戦況整理としてとても正しい。

## 1. 今回ほんとうに起きたこと

今回の差分の核心は 3 つじゃ。

第一に、`QAdicDescentExistenceTarget` をさらに裂いて、
**StrongSuperWieferich witness が既にあるとして、そこから整数 descent \(z'\) を回収できるか**
だけを抜いた最小核

$$
\texttt{PrimeGe5BranchAPrimitiveQAdicLocalGlobalGapTarget}
$$

を定義したこと。

第二に、その最小核から既存の descent infrastructure へ戻る橋、

$$
\texttt{pthRootCore\_of\_qAdicLocalGlobalGap}\\
\rightarrow
\texttt{pthRoot\_of\_qAdicLocalGlobalGap}\\
\rightarrow
\texttt{gnReducedGap\_of\_qAdicLocalGlobalGap}\\
\rightarrow
\texttt{primitivePacketDescent\_of\_qAdicLocalGlobalGap}\\
\rightarrow
\texttt{FLTPrimeGe5Target\_of\_qAdicLocalGlobalGap\_precise}
$$

を concrete に置いたこと。
これで Level 2m は、単なる概念ラベルではなく、**通れば FLT 本線へ届く実働 kernel** になった。

第三に、ファイル内コメントを更新して、
Level 1s は concrete、open kernel は Level 2m だと明示したこと。
これは地味に見えて大事じゃ。古い設計メモが戦況認識を濁らせることが、こういう長い作業ではよくあるからの。

## 2. 状況分析

いまの局面を短く言えば、

$$
\text{Level 0} \; \checkmark,\quad
\text{Level 1w} \; \checkmark,\quad
\text{Level 1s} \; \checkmark,
$$

そして

$$
\text{open kernel} = \text{Level 2m: QAdicLocalGlobalGap}
$$

じゃ。
ここは前よりずっと明瞭になった。

少し前までは、`QAdicDescentExistenceTarget` が Level 2 の open kernel と見えておった。
だが今回の整理で、それは **coarse bridge 語彙** に格下げされ、本当に攻めるべき内容は

$$
\text{strong witness} \Rightarrow \text{integer } z' \text{ の存在}
$$

だと切り出せた。
この差は大きい。
coarse な存在命題をそのまま殴るのと、**local-global gap だけを抽出した最小核** を殴るのでは、研究の速度がかなり違うからじゃ。

## 3. 数学的な解説

今回の `PrimeGe5BranchAPrimitiveQAdicLocalGlobalGapTarget` の意味は、実にまっすぐじゃ。

Level 1s までで、prime 文脈の q-adic 側はもうかなり concrete に揃った。
つまり今や手元には

* branch 情報
* \(\Phi_p(R)=0 \bmod q^p\)
* \(z = Ry \bmod q^p\)

という **strong witness** がある。
それでもなお残るのが、

$$
\exists z' \in \mathbb{N},\quad (x/q)^p + y^p = z'^p
$$

という整数解の存在じゃ。
これこそが local から global へ飛ぶ瞬間であり、今回の最小核はその一点だけを取り出しておる。

わっちの見立てでは、これはとても良い圧縮じゃ。
なぜなら、Level 1 側の局所 Hensel 機構と、Level 2 側の整数存在性を、もう混ぜて議論せずに済むからの。

## 4. 慎重に見るべき点

ただし、ここで浮かれすぎてはならぬ。

今回 concrete に閉じたのは **接続** じゃ。
`PrimeGe5BranchAPrimitiveQAdicLocalGlobalGapTarget` そのものは、まだ open のままじゃ。
つまり、

* 「何が本丸か」はかなり鮮明になった
* だが「その本丸をどう落とすか」は、まだこれから

という段階じゃよ。

また、この最小核は前よりは鋭いが、まだ仮定は多い。
今後さらに、

* truly 必要な仮定は何か
* strong witness のうち何が冗長か
* 幾何語彙で書くべきか、整数論語彙で書くべきか

を削れる余地はあるはずじゃ。
履歴の「さらに分解」「最小核を整数論的/幾何学的にどう表現するかを詰める」という次課題は、まさにそこを指しておる。

## 5. いまの最も正確な現在地

わっちなら、現状はこうまとめる。

`QAdicDescentExistenceTarget` はもう主戦場ではなく、
**Level 2m へ降ろすための粗い入口** じゃ。
本当に殴るべき相手は

$$
\texttt{PrimeGe5BranchAPrimitiveQAdicLocalGlobalGapTarget}
$$

であり、これが通れば primitive 側の `PthRootCore` を通って、そのまま FLT 本線へ届く。
つまり、今後の研究ログでは「Level 2」とひとくくりにせず、**Level 2c と Level 2m を分けて書く** のが良いじゃろう。

## 6. 次の一手

次にやるべきことも、かなり明快じゃ。

**`PrimeGe5BranchAPrimitiveQAdicLocalGlobalGapTarget` のさらなる分解** じゃ。
具体的には、

$$
\text{strong witness} \Rightarrow \text{integer descent}
$$

の飛躍の中で、

* 純局所な部分
* 整数化の部分
* 幾何的解釈に依る部分

を裂いていくのがよい。
ここを裂ければ、Level 2m はさらに「本当に最後の 1 核」へ近づくはずじゃ。

## 7. 一文でまとめると

**かなり良い。今回の進展で、Level 1s は concrete、`QAdicDescentExistenceTarget` は coarse bridge、そして真の open kernel は `PrimeGe5BranchAPrimitiveQAdicLocalGlobalGapTarget` だと Lean 上でも明示された。**
つまり、主戦場はもう完全に Level 2m じゃよ。
