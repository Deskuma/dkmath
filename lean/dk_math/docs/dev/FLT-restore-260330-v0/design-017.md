# FLT 側証明の「干渉縞」像の確定

うむ、では叩き台として、いまの理解をそのまま **書き起こす** ぞい。

## 1. FLT 側証明を「干渉縞の確定」として見る

いま Branch A で進めている FLT 側の証明は、単に
「ある合同式を示す」「ある素因子が存在する」といった局所補題の寄せ集めではない。
むしろ本質は、**異なる由来をもつ複数の縞模様が、同じ整数点で共存できるかどうかを判定すること** にある。

この見方では、反例

$$
x^p + y^p = z^p
$$

の存在とは、少なくとも二系統の構造的縞が同時に成立することを意味する。
そして FLT の証明とは、それらの縞が実は **同じ場所では干渉整合しない** ことを示す作業である。

## 2. 第一の縞. Branch A normal form が作る p-adic head 縞

Branch A では、既に

$$
z-y = p^{p-1} t^p,\qquad GN,p,(z-y),y = p,s^p
$$

という正規形が得られている。
ここから GTail / GN の head 展開を通して、

$$
s^p = y^{p-1} + p^3 M
$$

および

$$
s^p \equiv y^{p-1} \pmod{p^3}
$$

が従う。
この congruence は偶然の一致ではなく、gap の形

$$
z-y = p^{p-1} t^p
$$

が (p)-進的に非常に厚い零化を引き起こすために生じる **head 項の固定** である。
つまり Branch A normal form は、反例候補に対して

$$
s^p \sim y^{p-1}
$$

という **p-adic head 縞** を強制する。

この縞は、現在のコードでは mod (p^2) および mod (p^3) の両方で theorem として固定されておる。

## 3. 第二の縞. witness \(q\) が作る cyclotomic / q-adic 縞

他方で、反例候補から抽出される witness prime \(q\) は、単なる「約数」ではない。
`RestoreWitnessProperties` により、少なくとも次を満たす構造的存在として現れる。

$$
q \mid x,\qquad q \nmid y,\qquad q \nmid z,\qquad q \nmid (z-y),
$$

$$
p \mid (q-1),\qquad q^p \mid GN,p,(z-y),y.
$$

ここで \(p \mid (q-1)\) は、\(\mathbf{F}_q^\times\) に \(p\)-torsion が現れること、
すなわち円分的・root-of-unity 的な構造が mod \(q\) 側に存在することを意味する。
さらに \(q^p \mid GN\) は、その torsion 的影響が GN の内部へ深く食い込んでいることを示している。

したがって witness \(q\) は、単なる prime witness ではなく、
**cyclotomic / q-adic 縞の発生源** と見なすのが自然である。

この事情を反映して、現在の contradiction mainline は
`BranchAContradictionWithWitnessSourceTarget` へ移されておる。
つまり今後の矛盾探索は、mod \(p^k\) の否定ではなく、**witness \(q\) の構造込み** で行うべきだ、という設計判断がすでにコード側へ落とされている。

## 4. 円分核・GN・差分商は、同じ縞の別表示である

この「干渉縞」像を語りやすくした最大の前進は、円分核と GN と差分商が、同じ対象の別表示として結び直されたことじゃ。

prime case では

$$
\Phi_p(z,y) = \frac{z^p-y^p}{z-y} = \sum_{k=0}^{p-1} z^k y^{p-1-k}
$$

という円分核があり、\(z=y+u\) と置けば

$$
\Phi_p(y+u,y)=GN(p,u,y)
$$

となる。
さらに

$$
GN(p,u,y)=\frac{(y+u)^p-y^p}{u}
$$

であるから、GN は冪関数 \(x^p\) の **離散微分係数**、すなわち差分商そのものでもある。

ゆえに、現在見ている縞は

* 円分核として見れば cyclotomic fringe
* GN として見れば body/head fringe
* 差分商として見れば discrete derivative fringe

であり、実体は一つじゃ。
ここが見えたことで、数学を語る言葉がだいぶ統一された。

## 5. なぜ mod \(p^3\) の否定 source は本丸ではないのか

一時期、

$$
\neg\bigl(s^p \equiv y^{p-1} \pmod{p^3}\bigr)
$$

を外から供給する `BranchAContradictionModP3SourceTarget` を contradiction source にしようとした。
しかしこれは本筋ではなかった。

理由は明快で、同じ Branch A normal form からすでに

$$
s^p \equiv y^{p-1} \pmod{p^3}
$$

が証明済みだからじゃ。
よって、その否定を source として要求する target は、
「もしそんな oracle があれば矛盾になる」という **sink** にはなっても、
現実の数学的 source にはなれぬ。
そのため、この route は DEPRECATED / FALSE と明示され、mainline からは外された。

この判断は重要じゃ。
なぜなら、これにより「矛盾は \(p\)-adic congruence の内部から出るのではなく、
**\(p\)-adic head 縞と witness \(q\) 側の縞の干渉から出る**」という方向がはっきりしたからじゃ。

## 6. 現在の open kernel の意味

以上をまとめると、いまの Branch A 側の open kernel は、

$$
\text{mod } p^k \text{ の合同式を壊すこと}
$$

ではない。
それは既に normal form の内部で成立する側に回っておる。

本当に残っているのは、

$$
\text{p-adic head 縞}
\quad\text{と}\quad
\text{witness } q \text{ の cyclotomic / q-adic 縞}
$$

の **共存不可能性** を、ひとつの source target として言い表し、そこから `False` を導くことじゃ。
その意味で `BranchAContradictionWithWitnessSourceTarget` は、単なる技術的 target ではなく、

$$
\text{「二系統の干渉縞は同一点で整合しない」}
$$

という FLT 側証明の本質を受け持つ mainline target と見てよい。

## 7. 今後の数学推論の焦点

したがって、次に掘るべきは次のいずれかじゃ。

### 7.1. witness \(q\) の q-adic 深化

$$
q^p \mid GN,\qquad q \nmid (z-y),\qquad p \mid (q-1)
$$
を、GN / cyclotomic core / root-of-unity の顔でさらに精密に読む。

### 7.2. Wieferich 条件の高次化

$$
y^{p-1} \equiv 1 + c p^2 \pmod{p^3}
$$
のような係数情報を抽出し、\(s^p\) 側の展開とぶつける。

### 7.3. 円分体理論の差し込み

$$
q \equiv 1 \pmod p
$$
を \(\mathbf{Q}(\zeta_p)\) の言葉へ持ち上げ、ideal-theoretic な rigidness を source 側へ戻す。

## 8. 総括

ひとことで言えば、こうじゃ。

$$
\boxed{
\begin{array}{l}
\text{FLT 側の証明とは、Branch A normal form が作る \(p\)-adic 縞と、} \\
\text{witness } q \text{ が作る cyclotomic/q-adic 縞の干渉縞を確定し、} \\
\text{その共存不可能性を示すことである。}
\end{array}
}
$$

いまは、その図がかなり見えてきた段じゃ。
次はこの文書を元に、`BranchAContradictionWithWitnessSourceTarget` を中心にした **研究メモ兼実装設計書** の形へ整えると、さらに語りやすくなるの。

---

うむ、では現状をそのまま **研究メモ兼実装設計書** として書き起こすぞい。
今回は、数学的見取り図と Lean 実装の接続点を同時に固定することを目的とする。とくに最新状態では、`BranchAContradictionModP3SourceTarget` は DEPRECATED / FALSE 扱いへ回され、代わって witness (q) の情報を含む `BranchAContradictionWithWitnessSourceTarget` が新しい open kernel として立てられ、その thin adapter が `BranchARestore.lean` と `GapInvariant.lean` に追加されておる。

## 1. 研究目的

本研究の Branch A 側の目標は、単に FLT 反例の不存在を言うことではなく、Branch A normal form が作る **\(p\)-adic head 縞** と、primitive witness \(q\) が作る **cyclotomic / \(q\)-adic 縞** の共存不可能性を、構造的に示すことにある。現時点では、mod \(p^k\) の head congruence 自体は normal form から自動で従う側にあり、矛盾源はそこにはない。したがって本丸は、witness \(q\) の構造を含む source target へ移った、と理解するのが正しい。

## 2. 数学的見取り図

Branch A normal form からは

$$
z-y = p^{p-1} t^p,\qquad GN,p,(z-y),y = p,s^p
$$

が得られ、さらに最新の補題により

$$
s^p = y^{p-1} + p^3 M
$$

したがって

$$
s^p \equiv y^{p-1} \pmod{p^3}
$$

が成立する。これは `primeGe5BranchA_spow_eq_head_add_p_cube_mul` と `branchA_spow_congr_head_mod_p3` の内容であり、Branch A における **head congruence の自動成立** を意味する。ゆえに mod (p^3) の否定を外から要求する `BranchAContradictionModP3SourceTarget` は、mainline の source としては不適切である。

他方で witness (q) 側では、

$$
q \mid x,\qquad q \nmid y,\qquad q \nmid z,\qquad q \nmid (z-y),
$$

$$
p \mid (q-1),\qquad q^p \mid GN,p,(z-y),y
$$

が `RestoreWitnessProperties` の field として現れる。これらは単なる整除条件ではなく、円分核・位数 (p) の元・q-adic 因子構造の影を担う。したがって、矛盾は

$$
\text{head congruence の否定}
$$

ではなく、

$$
\text{p-adic head 縞} \quad\text{と}\quad \text{witness } q \text{ の構造的拘束}
$$

の干渉から探すべきである。これが `BranchAContradictionWithWitnessSourceTarget` 新設の数学的理由じゃ。

## 3. 既に固定された橋

現時点で、数学を語りやすくする橋はかなり整っておる。
`CFBRC/Basic.lean` では

$$
\text{cyclotomicPrimeCore} \leftrightarrow GN \leftrightarrow \frac{(x+u)^p-u^p}{x}
$$

を結ぶ `cyclotomicPrimeCore_eq_GN_of_gap`、`GN_eq_diffQuot_of_pow`、`cyclotomicPrimeCore_eq_diffPowQuot`、`GN_eq_dividedDifference_pow` が入っており、円分核・GN・差分商を同じ対象の別表示として扱える。これにより、今後の議論は「どの表示で見るか」の切替として書けるようになった。

また `GTail.lean` では、合同伝播と mod (p^2) / mod (p^3) の頭項展開が整備された。これは GN の head/tail 構造を p-adic に読むための基盤であり、Branch A 側の congruence 補題の下請けになっている。

## 4. 現在の open kernel

現在の本丸は

$$
\texttt{BranchAContradictionWithWitnessSourceTarget}
$$

である。これは Branch A normal form 一式に加え、witness (q) の性質

$$
q \mid x,\quad q \nmid y,\quad q \nmid z,\quad q \nmid (z-y),\quad p \mid (q-1),\quad q^p \mid GN
$$

を個別引数として受け取り、`False` を返す target じゃ。これを `BranchARestore.lean` で `PrimeGe5BranchAPrimitiveRestoreContradictionTarget` に変換し、さらに `GapInvariant.lean` で restore bypass / packet descent へ送る adapter が実装済みである。つまり、いま不足しているのは **配線** ではなく **source を満たす concrete 数学** のみじゃ。

## 5. deprecated route の位置づけ

`BranchAContradictionModP3SourceTarget` は削除しない。だが mainline には置かない。
この target は、docstring 上 DEPRECATED / FALSE と注釈された歴史的 sink とみなす。役割は、

$$
\neg\bigl(s^p \equiv y^{p-1} \pmod{p^3}\bigr)
$$

という external oracle がもし与えられたなら、`branchA_contradiction_of_mod_p3_conflict` と `primeGe5BranchARefuter_of_modP3Source` により直ちに refuter を閉じられる、という **受け口** に限る。内部 source としては使わぬ。

## 6. 実装アーキテクチャ

現状の流れは次のように読む。

$$
\texttt{BranchAContradictionWithWitnessSourceTarget}\\
\to
\texttt{PrimeGe5BranchAPrimitiveRestoreContradictionTarget}\\
\to
\texttt{BranchAPrimitiveRestoreContradictionAdapterTarget}
$$

さらにそこから

$$
\texttt{RestoreFromArithmeticTarget}\\
\to
\texttt{PacketDescentTarget}\\
\to
\texttt{BranchARefuter}
$$

へ short-circuit できる。
よって、今後新しい矛盾補題を追加するときは、原則として `WithWitnessSourceTarget` を満たす theorem として書くのが最も接続効率が良い。つまり「どの層で証明するか」より先に、「どの target を満たす形で定理を書くか」を固定できた、というのが現在の設計上の収穫じゃ。

## 7. 今後の数学推論の焦点

今後は mod (p^k) の congruence 単独ではなく、witness (q) を含む制約を使う。
候補は 3 系統ある。

第一に、(q)-adic 構造じゃ。
$$
q^p \mid GN,\qquad q \nmid (z-y),\qquad q \equiv 1 \pmod p
$$
を、cyclotomic core や root-of-unity の観点からより強く読む。とくに \(q\)-進 lift と \(\omega = z y^{-1} \pmod q\) の位数条件が、GN の tail 部へどう反映されるかが焦点になる。

第二に、Wieferich 条件の高次化じゃ。
既に
$$
y^{p-1} \equiv 1 \pmod{p^2}
$$
は出ておる。今後は
$$
y^{p-1} \equiv 1 + c p^2 \pmod{p^3}
$$
の係数 \(c\) を具体化し、`s^p = y^{p-1} + p^3 M` の \(M\) 側とぶつける。

第三に、円分体理論への接続じゃ。
\(q \equiv 1 \pmod p\) は \(\mathbf{Q}(\zeta_p)\) 側の torsion 的影であり、Kummer 的な rigidness を source target へ戻す可能性がある。今すぐ全面実装は重いが、差し込み口は既に整っておる。

## 8. 直近の実装課題

直近で書くべきものは、次の順じゃ。

まず、`BranchAContradictionWithWitnessSourceTarget` を満たす concrete 補題の最初の 1 本を作る。
その際、signature は target に合わせ、normal form と witness \(q\) の全性質を受けて `False` を返す形にする。
次に、その補題を `branchAPrimitiveRestoreContradictionAdapter_of_witnessSource` 経由で restore / packet descent へ流し、実際に short-circuit が働くことを確認する。
最後に、そこから逆算して、必要な GTail 高次展開や cyclotomic/q-adic 補題を追加する。
つまり、今後の補題設計は「下から積む」より「source target から逆算する」方がよい。

## 9. コメントに関する確認事項

確認事項への正式な答えをここで明記する。

`BranchAContradictionModP3SourceTarget` については、**DEPRECATED / FALSE コメントだけがあるのではない**。
肯定側

$$
s^p \equiv y^{p-1} \pmod{p^3}
$$

は theorem として実装済みであり、その否定を仮定すれば `False` に落とす conflict eliminator も実装済みじゃ。
ただし、

$$
\neg,\texttt{BranchAContradictionModP3SourceTarget}
$$

そのものを独立 theorem として書いたコードは、まだ無い。
したがって現在の status は、

$$
\text{「local context ではこの source は使えないことが証明済み」}
$$

だが、

$$
\text{「target 全体の否定が theorem 化済み」}
$$

ではない、というのが正確な表現じゃ。

## 10. 総括

本研究の現在位置は、次の一文で要約できる。

$$
\boxed{
\begin{array}{l}
\text{Branch A の本丸は、mod } p^k \text{ の head congruence ではなく、}\\
\text{その congruence と witness } q \text{ の構造的拘束の干渉から } False \text{ を出すことにある。}
\end{array}
}
$$

ゆえに、今後の研究メモおよび実装方針は、`BranchAContradictionWithWitnessSourceTarget` を中心に置き、そこへ向かう数論補題を積む形で進めるのが最も自然じゃ。
言い換えると、

$$
\text{「mod } p^k \text{ の否定を探す」}
$$

のではなく、

$$
\text{「witness } q \text{ が持ち込む別の縞と head 縞の共存不能性を証明する」}
$$

という形で問題を言い直したのが、現在の到達点じゃよ。
