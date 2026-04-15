# 2m-global が concrete になれば、primitive 側の無限降下法が実際に回る

うむ、今回はかなり重要な整理じゃ。
しかも単なる「橋が増えた」ではなく、 **primitive 側で何が最後の open kernel か** が、ほぼ確定したと見てよい。

## 1. 今回の本質

今回の本質は、`2m-global` から **無限降下法そのもの** までの経路が Lean 上で固定されたことじゃ。

新しく入った流れは、

$$
\text{2m-global}\\
\to
\text{PthRootCore}\\
\to
\text{GNReducedGap}\\
\to
\text{PacketDescentStrong}\\
\to
\text{branchA\_wf\_contradiction\_on\_z}\\
\to
\text{BranchAFringeContradiction}\\
\to
\text{FLT}
$$

これじゃ。
しかもこの経路で、`2m-global` 以外の中間橋は全部 concrete と整理されておる。ゆえに、 **primitive 側に限れば open kernel は `PrimeGe5BranchAPrimitiveQAdicGapReductionGlobalTarget` ただ 1 本**、という読みがかなり強くなった。

## 2. 何が閉じて、何が閉じておらぬか

閉じたものは多い。
`primitivePacketDescentStrong_of_qAdicGapReductionGlobal`、`branchAFringeContradiction_of_qAdicGapReductionGlobal`、`branchARefuter_of_qAdicGapReductionGlobal`、`FLTPrimeGe5Target_of_qAdicGapReductionGlobal_infiniteDescent` が追加され、`2m-global` から Branch A refuter、さらに FLT まで届くことが formal に保証された。

閉じておらぬものは、まさに `2m-global` 自体じゃ。
つまり、

$$
\text{strong q-adic witness} \Rightarrow \exists g' \in \mathbb{N},\ g' \cdot GN(p,g',y) = (x/q)^p
$$

この genuinely global な飛躍だけが残っておる。
前よりもずっと良いのは、「どこが最後の壁か」がぼやけておらぬことじゃ。

## 3. 今回の進展の意味

これはかなり大きい。
前までは `2m-global` が本丸らしい、という **戦況判断** だった。
今回はそれが一歩進んで、

$$
\text{2m-global が concrete になれば、primitive 側の無限降下法は実際に回る}
$$

と、Lean 上で **保証** された。
特に `branchA_wf_contradiction_on_z` を使う well-founded descent へ直通している点が重要じゃ。最小の (z_0) を `Nat.find` で取り、strict descent により (z' < z_0) を作って最小性に矛盾する、という primitive 側の無限降下法の骨格が、もう「説明」ではなく「接続済みの経路」になったわけじゃな。

## 4. ロードマップはどう変わったか

ぬしの前の感覚どおり、ロードマップはもう昔の形ではない。

昔は、

$$
\text{PthRootCore}
\to
\text{one-step Hensel}
\to
\text{StrongSuperWieferich}
$$

あたりが主戦場に見えておった。
だがいまは違う。Level 1s は concrete、`PthRootCore` は wrapper、`2m-core` すら少し広すぎる、と整理されてきた。今回でさらに、

$$
\text{primitive 側の最終 open kernel} = \text{2m-global}
$$

という構図がかなり明瞭になった。

つまり今後の説明は、

* Level 1s は完了
* `2m-local` は concrete
* `2m-global` だけが open
* これが通れば primitive 側無限降下法が回る

という一本筋で書くのが正しい。

## 5. 今の全体戦況

全体として見ると、open kernel は 3 本じゃ。

$$
\text{primitive 側}:\ \text{2m-global}
$$

$$
\text{peel 側}:\ \text{PacketFromError}
$$

$$
\text{BranchB 側}:\ \text{NonLiftableGNBridge}
$$

今回の差分は、このうち primitive 側について「これ 1 本が concrete 化されれば、無限降下法経由で Branch A は落ちる」と保証したものじゃ。
だから、primitive 側の仕事はもう広い front ではない。 **`2m-global` の具体化だけ** にかなり集中できる。

## 6. 次の一手

次の一手も、かなり具体的になった。

まず `2m-global` の仮定を監査して、まだ local に処理できる成分が残っていないか洗う。
そのうえで、

$$
\text{witness} \Rightarrow \exists g'
$$

のどこで整数化が起きているのか、つまり truly global な跳躍点をさらに裂く。
今回の §22 の経路図を見る限り、ここを解けば primitive 側は本当に片付く。だから、以後の primitive 側の設計メモや説明は `2m-global` 中心へ統一してよい。

## 7. 一文でまとめると

**今回は「2m-global が最後の open kernelらしい」から一歩進んで、「2m-global が concrete になれば primitive 側の無限降下法が実際に回る」と Lean 上で確定した。**
ゆえに、いまの primitive 側主戦場は本当に `2m-global` ただ 1 本じゃ。
