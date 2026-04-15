# review-032: 局所定理群の完成と exact product の整理

## 1. 状況分析

うむ、これは **かなり大きな前進** じゃ。
今回で branchA_hensel_lift_exists の sorry が埋まり、群論的 lift によって \( \omega \in ZMod(q) \) から \( \omega_k \in ZMod(q^k) \) を実際に構成できるようになった。しかも build は通っており、対象ファイルの本質的 sorry は branchA_GN_cyclotomic_ring_identity の 1 本だけになった。

これは単に sorry が 1 個減った、という話ではない。
前までは

\( \text{fringe bundle} \to \text{hLift} \to \text{local valuation theory} \)

の最初の矢が仮定つきじゃった。
今はその矢が実装されたので、既に通っていた局所結果、特に central theorem 側を **fringe bundle からそのまま使える** 段になったのじゃ。central theorem 自体は一つ前の段で既に sorry-free になっておるから、主線はほぼ開通したと見てよい。  

## 2. 数学的解説

いま本当に確定した数学は、かなり強い。

全体側では既に

\( v_q(z^p-y^p)=p\,v_q(s) \)

があり、これは Kummer valuation の全体量じゃ。
因子側では、distinguished factor

\( \delta := (z : ZMod(q^k)) - \omega_k \cdot (y : ZMod(q^k)) \)

について

\( v_q(\delta.val)=p\,v_q(s) \)

が出ている。つまり、全体の ( q )-進深度が distinguished factor 1 本へ **ちょうど一致して集中する** ことが分かったわけじゃ。これは「割れる」「下界がある」ではなく、exact equality じゃよ。

ここで大事なのは、残っている branchA_GN_cyclotomic_ring_identity が、もはやこの主張の blocker ではないことじゃ。
以前は exact product

\( GN = (z-\omega_k y)\prod_{i=2}^{p-1}(z-\omega_k^i y) \)

を取りたかった。だが \( ZMod(q^k) \) は \( k > 1 \) で整域ではないので、その route は重かった。実際、そこで止まったことは記録済みじゃ。ところが review-030 路線で、exact product を捨てて

\( GN = \delta \cdot U,\quad U \text{ は unit} \)

という local factorization だけで central theorem を閉じられた。
だから、数学の本体はもう exact product には依存しておらぬ。  

## 3. 次の作業の選択

賢狼の判定は、こうじゃ。

$$
\boxed{
\begin{array}{l}
\text{次は terminal case へ進む前に、}\\
\text{残る branchA\_GN\_cyclotomic\_ring\_identity の扱いを整理して、}\\
\text{restore file を sorry-free にするのが最善じゃ。}
\end{array}
}
$$

ただし、ここで言う「整理」は、exact product を無理に証明し切ることではない。
**statement 自体を local factorization 版へ弱化する** か、あるいは exact product 版を appendix 的補強定理として別管理に落とす、という意味じゃ。

その理由は 2 つある。

ひとつは、いま残る sorry がその 1 本だけで、しかも主線の blocker ではないからじゃ。ここを設計的に掃除すれば、restore 側全体が clean になる。

もうひとつは、terminal case に入るときに「局所 valuation 理論は完全に clean」という土台がある方が、はるかに見通しが良いからじゃ。いまはもう

\( v_q(\delta.val)=p\,v_q(s) \)

まで取れておるので、降下 1 step ごとの valuation 減少を exact に追える。よって、その次の本命は terminal case でよい。ただしその前に、不要になった exact product theorem をどう扱うか決めて、ファイルを clean にしておくのが賢い。  

## 4. 実務的な順番

わっちなら順番はこうする。

まず、branchA_GN_cyclotomic_ring_identity を主線から外す。
つまり名前を残すなら local factorization 版に statement を差し替える。exact product を残したいなら appendix 用ファイルか別 theorem 名へ逃がす。

そのあとで terminal case に入る。
ここではもう、distinguished factor の exact valuation を武器にして

\( s \mapsto s' = s/q \)

の降下で何が必ず減るかを追える。ここが次の本丸じゃ。

## 5. 総括

ひとことで言えば、こうじゃ。

**Hensel lift existence が埋まったことで、局所 valuation 理論は fringe bundle から直接使える段になった。数学の主線はほぼ完成しており、残る exact product theorem は本筋ではない。だから次はその theorem の statement 整理で file を sorry-free にし、その直後に terminal case へ進むのが最も筋がよい。**

かなり良い流れじゃよ。
もう「証明の材料集め」ではなく、**仕上げの順番を選ぶ段** に入っておる。
