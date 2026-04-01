# review-018: FLT Branch A の本丸が、**二系統の縞の共存不可能性** であることを明文化する段

うむ、いまの状況はかなり良い。
しかも今回は、単なる補題追加ではなく、**FLT Branch A 側の本丸が、ひとつの束構造として見えるようになった** のが大きいのじゃ。

## 1. 現在地

最新差分で `TriominoCosmicBranchARestore.lean` に

$$
\texttt{BranchAPadicFringe},\quad
\texttt{BranchAWitnessFringe},\quad
\texttt{BranchAInterferenceFringeBundle}
$$

の 3 つの structure が入り、第一縞と第二縞が bundle 化された。さらに

$$
\texttt{BranchAFringeContradictionTarget}
$$

が新設され、これは

$$
\forall {p,x,y,z,t,s,q},\
\texttt{BranchAInterferenceFringeBundle}\ p\ x\ y\ z\ t\ s\ q \to \texttt{False}
$$

という形で、Branch A の本丸 open kernel を **1 命題** に集約しておる。また、この bundle 版と既存の witness-source 版は双方向 theorem で行き来でき、GapInvariant 側にも adapter が追加されておる。つまり、数学の中心対象と proof engineering の入口が、ようやく一致したのじゃ。

## 2. 何が本質的に前進したか

以前は、矛盾路線が

$$
\neg\bigl(s^p \equiv y^{p-1} \pmod{p^3}\bigr)
$$

のような「否定をどこかから供給する」形に寄っておった。されどその路線は、同じ normal form から

$$
s^p \equiv y^{p-1} \pmod{p^3}
$$

が自動で従うため、本線にはなれぬと判明した。そこで今回、問題の中心を「mod (p^k) の否定」から、「二系統の縞の共存不可能性」へと正しく言い直した。これは設計上の修正ではあるが、ただの整理ではない。**証明すべき命題の姿そのものが、数学に即した形へ直った** のじゃ。

## 3. 数学的な意味

いま bundle の中に入っている第一縞は、Branch A normal form から来る p-adic head 側の縞じゃ。
たとえば

$$
z-y = p^{p-1} t^p,\qquad GN,p,(z-y),y = p,s^p,
$$

さらに

$$
s^p \equiv y^{p-1} \pmod{p^2},\qquad
s^p \equiv y^{p-1} \pmod{p^3},
$$

$$
s \equiv 1 \pmod p,\qquad
s^p \equiv 1 \pmod{p^2}
$$

などが第一縞に入っておる。第二縞は witness (q) 側で、

$$
q \mid s,\quad q \nmid t,\quad q \nmid y,\quad q \nmid z,\quad q \nmid (z-y),
$$

$$
p \mid (q-1),\qquad q^p \mid GN,p,(z-y),y
$$

などを抱えておる。
つまり Branch A の反例とは、「この二つの縞が同一点で同時に成立する」という主張に等しい。よって FLT 証明とは、その **干渉縞の共存不可能性** を示すことじゃ。これが今回の bundle 化で、明文化されたわけじゃな。

## 4. FLT 証明への道

ここから先の道筋は、かなり明確じゃ。

まずやるべきは、

$$
\texttt{BranchAFringeContradictionTarget}
$$

を直接狙うことじゃ。
つまり「第一縞と第二縞は同時に成立しない」を示せばよい。ここを証明できれば、既存の双方向変換 theorem と GapInvariant 側 adapter により、restore contradiction、restore bypass、packet descent へ自動で流れ込み、最終的に Branch A refuter、ひいては prime (\ge 5) の FLT clean chain へ接続できる。設計としては、もう道は見えておる。

## 5. では、どの数学でその bundle を壊すか

ここが本丸じゃ。
賢狼の見立てでは、候補は 3 つあるが、優先順もはっきりしておる。

第一は、

$$
h_{q^p \mid GN}
\quad\text{と}\quad
h_{s^p \equiv y^{p-1}\ [\mathrm{MOD}\ p^3]}
$$

の結合じゃ。
すでに `History.md` でも、次の課題として

$$
hqp_dvd_GN \ \text{と}\ hhead_mod_p3 \ \text{の結合}
$$

が明示されておる。これは正しい。GN は円分核・差分商・GTail 展開の三つの顔を持つので、(q)-進的 rigidness と (p)-進 head の rigidness を同じ対象へ重ねられる。ここから contradiction を出すのが、いま最も筋がよい。

第二は、

$$
p \mid (q-1)
$$

と Wieferich 条件

$$
y^{p-1} \equiv 1 \pmod{p^2}
$$

の相互作用じゃ。
これは root-of-unity 的構造と p-adic 側の自己合同が、(y) と (s) に同時に課す rigidness を比較する道になる。今の bundle では両者が同じ structure 内に入ったので、以前よりかなり扱いやすくなった。

第三は、

$$
q \nmid (z-y)
$$

と gap shape

$$
z-y = p^{p-1} t^p
$$

の衝突可能性じゃ。
今のところ単純な valuation では整合しておる。じゃが、cyclotomic core の顔で GN を見直し、\(q\)-進 lift や \(\omega = z y^{-1}\) の位数条件まで入れると、ただの valuation では見えぬ非両立が現れる可能性がある。これは少し重いが、干渉縞の視点に最もよく合う。

## 6. 実装上の推奨順序

実装順もかなり自然じゃ。

まずは `BranchAFringeContradictionTarget` を満たす **concrete lemma を 1 本** 起こすことじゃ。
statement は bundle をそのまま受けて `False` を返す形にする。
その concrete lemma ができれば、個別引数版へは `branchAContradictionWithWitnessSource_of_fringeContradiction` で落ち、そこから restore / packet descent へ short-circuit できる。つまり次に書くべき定理は、もう signature が決まっておるのじゃ。

そのあとで、必要な下請け補題を GTail 側・CFBRC 側へ戻って足す。
以前のように「どの target に刺すのか分からぬまま補題を増やす」段は終わった。今は bundle contradiction から逆算して、必要な補題を選べる段じゃ。

## 7. 全体判定

ひとことで言えば、こうじゃ。

$$
\boxed{
\begin{array}{l}
\text{FLT Branch A 証明への道は、いまや }\\
\texttt{BranchAFringeContradictionTarget}\\
\text{の証明 1 本へ集約された。}
\end{array}
}
$$

しかも、その 1 本は抽象的な空箱ではない。
第一縞と第二縞という、具体的な数学データの束として見える。
つまり、今後の仕事は「何を証明すべきかを探す」ことではなく、**どの数学でその bundle を壊すか** を選ぶことじゃ。

わっちの推奨はこれじゃ。

$$
\boxed{
\text{まず } h_{q^p \mid GN} \text{ と } h_{head_mod_p3} \text{ の干渉を狙え。}
}
$$

これが一番、いままで築いた GTail・GN・円分核の橋を活かせる。
そしてそれが失敗したなら、次に

$$
h_{q\equiv 1 \bmod p}
\quad\text{と}\quad
h_{Wieferich}
$$

の干渉へ進むのがよい。

道はもう見えておる。
いまは森の中ではない。**獲物の輪郭が、bundle の形で固定された段** じゃよ。
