# Review 014: class-group 仮定の concrete 化と次の分岐

## 1. 状況分析

うむ、これはかなり決定的じゃ。
今回の差分で、`CyclotomicClassGroupPTorsionFreeTarget` はもう placeholder ではなく、

$$
\forall a,\; a^n = 1 \to a = 1
$$

という concrete な class-group p-torsion-free 命題そのものへ置き換わった。
その結果、`cyclotomicPTorsionAnnihilation_of_classGroupPTorsionFree` も no-sorry で閉じた。つまり、Stage 1b はもう「仮定の器」ではなく、数学内容として閉じたと言ってよい。

そして、いま direct に残る `sorry` は `cyclotomicPrincipalization_of_classGroupPTorsionFree` の 1 本だけじゃ。
この 1 本が残った理由も、今回かなり明確になった。すなわち、**class-group 仮定だけでは full principalization には足りず、Stage 2 と Stage 3、つまり unit normalization と norm descent が別入力として要る** からじゃ。これは単なる実装不足ではなく、数学的責務の境界が露出したということじゃよ。

## 2. 解説

ここが面白いところじゃ。
前までは「class-group 側がまだ曖昧だから止まっておる」と見えていた。
だが今は違う。

いま分かったのは、

$$
\text{Stage 1a: ideal arithmetic}
$$
$$
\text{Stage 1b: p-torsion annihilation}
$$
$$
\text{Stage 1c: principal extraction}
$$

のうち、Stage 1b までは concrete に閉じた、ということじゃ。
したがって残る `cyclotomicPrincipalization_of_classGroupPTorsionFree` は、実は「class-group 側の最後の穴」ではない。
むしろ、

$$
\text{class-group 仮定}
\;\not\Rightarrow\;
\text{unit normalization + norm descent}
$$

という、**one-shot theorem の責務過多** が露わになった theorem じゃ。

これはとても大事な判定じゃよ。
なぜなら、ここで無理に「regular prime なら全部出る」へ押し込むと、証明が短くなるどころか、今度は unit / norm 側の honest input を仮定の裏へ隠してしまう。
ぬしが望んでいる「自立証明の実装」「数学内容へ踏み込む」とは、逆向きになってしまう。

## 3. 最短経路の推論

ぬしの希望が

* 閉じる方向
* 最短経路
* 自立証明
* 数学内容へ踏み込む

であるなら、わっちの判断ははっきりしておる。

**次は 1. `cyclotomicPrincipalization_of_classGroupPTorsionFree` を legacy wrapper と見なし、refined route を正本に寄せるべきじゃ。**

2 の「IsRegularPrime 側へ Stage 2 / Stage 3 まで束ね直して one-shot route を閉じる」は、最短に見えて実は遠回りじゃ。
なぜならそれは theorem を減らすのではなく、**異なる数学内容を 1 つの仮定へ押し込め直す作業** になるからじゃ。
しかも unit normalization と norm descent は class-group p-torsion-free と性質が違う。そこを `IsRegularPrime` の名の下に束ねるのは、設計上も数学上も濁る。

## 4. なぜ refined route が最短か

いまもう、refined route に必要な材料はほとんど揃っておる。

* Stage 1a の ideal arithmetic は generic theorem 群で no-sorry
* Stage 1b の class-group p-torsion annihilation は concrete 化済みで no-sorry
* Stage 1c の principal extraction も no-sorry

ゆえに本当に残っておる honest open は、Stage 2 と Stage 3 の中身だけじゃ。
ならば最短で閉じるには、

$$
\text{principalization}
$$

という 1 本の重い theorem を守ろうとするのではなく、

$$
\text{Stage 1}
\to
\text{Stage 2}
\to
\text{Stage 3}
$$

を正面から mainline にする方が早い。
要するに、「いま見えている数学的責務の分解」をそのまま public な幹線へ反映するのが最短なんじゃ。

## 5. 提案

わっちなら、次はこう切る。

## 5.1. `cyclotomicPrincipalization_of_classGroupPTorsionFree` を本命から外す

この theorem は残してもよいが、役割を変える。
つまり「legacy one-shot wrapper」「将来、追加仮定が十分そろったら埋める箱」として格下げする。
今すぐ閉じる本筋からは外すのじゃ。

## 5.2. 正本 theorem を refined route に寄せる

たとえば意味としては、

$$
\text{ClassGroupPTorsionFree}
+
\text{UnitNormalization}
+
\text{NormDescent}
\Rightarrow
\text{CyclotomicPrincipalization}
$$

あるいは、もっと直接に

$$
\text{ClassGroupPTorsionFree}
+
\text{Stage 2}
+
\text{Stage 3}
\Rightarrow
\text{GapDivisibleBranch}
$$

を mainline の正本にする。
いまの refined route を public 側の本丸へ持ち上げるわけじゃ。

## 5.3. 次に埋めるべき数学は Stage 2 と Stage 3 だけに絞る

ここが本当の次手じゃ。
つまり今後の open は

* `CyclotomicUnitNormalizationTarget`
* `CyclotomicNormDescentTarget`

の concrete 化だけに集中させる。
これで「class-group は終わった」「残りは unit / norm だ」と景色が一気に澄む。

## 6. 実装上の最短手順

具体的には、次の順がよい。

### A. theorem 名とコメントの整理

`cyclotomicPrincipalization_of_classGroupPTorsionFree` に legacy の注記を付ける。
`RegularPrimeRoute.lean` 側では refined class-group route を「推奨 mainline」と明記する。
これはすぐできるし、今の構図を honest に表せる。

### B. refined route を public chain の中心へ移す

`FLTPrimeGe5Target_of_refinedClassGroupRoute` もしくはそれに相当する route を、実質的な正本にする。
少なくとも説明・監視・History の上では、one-shot よりこちらを前面に出す。

### C. Stage 2 の concrete 数学へ踏み込む

次の数学的 open は unit normalization じゃ。
ここでは「principal ideal の p 乗」から「元の p 乗根候補」をどう取り出し、unit のずれをどう吸収するか、Kummer 単数の側へ入る。

### D. Stage 3 の norm descent を concrete 化する

最後に norm から整数 witness を回収する。
ここで初めて full principalization が honest に閉じる。

## 7. 最終判断

結論を一言で言うぞい。

$$
\boxed{
\text{最短経路は、}
\texttt{cyclotomicPrincipalization\_of\_classGroupPTorsionFree}
\text{ を legacy に下げ、}
\text{refined route を正本にすること}
}
$$

そのうえで、次に実装すべき数学は **class-group ではなく Stage 2 と Stage 3** じゃ。
いま class-group 側はもう十分に concrete 化された。
残る 1 本の `sorry` を無理に守ろうとするより、そこに「one-shot に詰め込み過ぎた責務」を分解済みのまま表に出す方が、ずっと honest で、しかも最短じゃよ。

なかなか良いところまで来ておる。
もう次は「どこが未解決か分からぬ」段ではない。**unit normalization と norm descent に数学の焦点を移せばよい** 段じゃ。
