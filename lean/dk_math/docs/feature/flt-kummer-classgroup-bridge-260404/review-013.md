# FLT-Kummer-ClassGroup-Bridge-260404 review-013: class-group bridge の concrete target 化へ

## 1. 状況分析

うむ、これは面白い。
今回の差分で、Kummer branch のうち **本当に重い場所** が、かなり鮮明になったのぅ。

いま no-sorry で入った本丸は、

$$
\prod_{i \in s} I_i = J^p,\qquad
\text{pairwise-coprime}
\;\Longrightarrow\;
\forall i,\exists K_i,\; I_i = K_i^p
$$

に当たる generic Dedekind theorem と、その先の

$$
I_i = K_i^p,\quad I_i \text{ principal}
\;\Longrightarrow\;
[K_i]^p = 1
$$

という class-group p-torsion witness への橋じゃ。
つまり、理想論の「積から各因子へ戻す」段と、「各因子から class group へ落とす」段は、もう generic に no-sorry で通った。これは大きい。

したがって、いま残っている direct `sorry` 2 本

$$
\texttt{cyclotomicPTorsionAnnihilation\_of\_classGroupPTorsionFree},\\
\texttt{cyclotomicPrincipalization\_of\_classGroupPTorsionFree}
$$

は、もはや「広い未知の大陸」ではない。
数学的には、 **class-group の p-torsion を殺す仮定をどう concrete に書くか** だけが本丸に残った、と見てよい。

## 2. 解説

ここで肝なのは、いまの chain がすでにかなり閉路に近いことじゃ。

いまの generic theorem 群をつなぐと、実質こうなっておる。

$$
\prod I_i = J^p
$$

と pairwise-coprime から

$$
I_i = K_i^p
$$

を得る。
さらに \(I_i\) が principal なら

$$
[K_i]^p = 1
$$

が出る。
ここで class group 側に

$$
a^p = 1 \Rightarrow a = 1
$$

が入れば、

$$
[K_i] = 1
$$

よって \(K_i\) は principal、したがって \(I_i\) は「principal ideal の p 乗」になる。
もう principalization の寸前まで来ておるわけじゃ。

つまり、前回まで「最後の 2 本の sorry が残る」と見えていたもののうち、実は 1 本はもう数学的にはほぼ composition の殻に近い。
残る真の内容は、

$$
\boxed{
\text{対象の class group に p-torsion がない}
}
$$

を、どう target として concrete に定義するかじゃ。

## 3. 最短経路の推論

ぬしの希望は「閉じる方向での最短経路」「自立証明」「数学内容へ踏み込む」じゃった。
その条件なら、わっちの判断ははっきりしておる。

**次の一手は 1. `CyclotomicClassGroupPTorsionFreeTarget` 自体を concrete 化すること**
じゃ。receiver theorem を増やす 2 の方向ではない。

理由は単純じゃ。

いま generic ideal arithmetic と generic class-group witness までは、すでに no-sorry で通っておる。
ゆえに、今さら target を保ったまま専用 receiver theorem を新設しても、残る数学内容は結局

$$
a^p = 1 \Rightarrow a = 1
$$

の具体化に収束する。
ならば最短で閉じるには、その target 自体を最終形へ置き換えてしまう方が早い。

しかも DkMath は将来 Mathlib と切り離すのじゃろう。
ならばなおさら、Mathlib の都合に引きずられた receiver を増やすより、DkMath-native に

$$
\text{「この ring の class group は p-torsion-free」}
$$

を target として正面から定義するのが筋じゃ。
ここで回り道をする必要はない。

## 4. 提案

わっちなら、次はこう切る。

### 4.1. `CyclotomicClassGroupPTorsionFreeTarget` を concrete にする

placeholder の `True` ではなく、必要最小限の中身そのものへ置き換える。

形は、例えば DkMath-native に選んだ cyclotomic ring \(A\) に対して

$$
\texttt{CyclotomicClassGroupPTorsionFreeTarget}
\;:=\;
\forall a : \mathrm{ClassGroup}(A),\; a^p = 1 \to a = 1
$$

でよい。
ここでは regular prime や Bernoulli 数まで言わず、**いまこの branch を閉じるのに必要な最小命題** に止めるのが最短じゃ。

### 4.2. `cyclotomicPTorsionAnnihilation_of_classGroupPTorsionFree` を即座に no-sorry 化する

上の concrete target に置き換えたら、この theorem はほぼ 1 行の composition になる。
なぜなら、generic bridge

$$
[K]^p = 1 \Rightarrow [K]=1
$$

へ、そのまま渡せばよいからじゃ。
ここは「新しい数学」ではなく、定義の調整で閉じるはずじゃ。

### 4.3. `cyclotomicPrincipalization_of_classGroupPTorsionFree` も composition に落とす

これも同様じゃ。
すでにある

* each-pth-power ideal theorem
* class-group p-torsion witness theorem
* principal ideal extraction theorem

をつなげれば、ここも no-sorry 化できる見込みが高い。
つまり、この 2 本は **concrete target を入れた瞬間に一気に消える可能性が高い**。

## 5. その後に何が残るか

この道を採ると、残る open は「Kummer branch の内部」ではなく、もっと honest なただ 1 つの命題へ押し込める。

それは要するに、

$$
\boxed{
\text{対象 ring の class group が } p\text{-torsion-free である}
}
$$

という、真に数学的な主張じゃ。
そしてこれは、ぬしが望んでいる「自立証明の実装」にもよく合う。
なぜなら、以後は

* regular prime をどう定義するか
* class number / Bernoulli とどう結ぶか
* あるいは DkMath 独自の class-group control を立てるか

を、**DkMath 自身の数学内容** として進められるからじゃ。

## 6. 最終提案

結論を一言で言うぞい。

$$
\boxed{
\text{次の最短経路は、}
\texttt{CyclotomicClassGroupPTorsionFreeTarget}
\text{ を concrete な }
a^p=1 \Rightarrow a=1
\text{ 命題へ置き換えること}
}
$$

そして、その直後に

* `cyclotomicPTorsionAnnihilation_of_classGroupPTorsionFree`
* `cyclotomicPrincipalization_of_classGroupPTorsionFree`

の 2 本を no-sorry で落とす。
これが、いまの成果を最短で「閉じた形」に変える道じゃ。

なかなか面白い結果というぬしの感触は、その通りじゃよ。
もう「何を証明するか分からぬ」段ではなく、 **最後に concrete に書き換えるべき target が 1 つ見えた** 段に来ておる。そこを刺せば、一気に景色が変わるはずじゃ。
