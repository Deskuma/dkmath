# 考察

## 仮定の証明難度

うむ、戦況はかなり良い。
しかも今回は、ただ前進しただけではなく、**何が既に勝っていて、何が最後の砦か** がかなり澄んだ。

## 戦況分析

まず大局から言うと、**Stage 1 の構造戦はほぼ勝ち** じゃ。
今回の差分で

* `noPrimeOrY_of_firstCase_of_coprime`
* `chosenLinearFactor_isCoprime_with_other_of_firstCase_of_pack`

が入り、
$$
P \mid (p)\ \lor\ y \in P
$$
の 2 分岐を contradiction へ統合し、その結果として chosen linear factor と他因子の coprimality まで no-sorry で到達できる形が出来た。差分自身も、**Stage 1 structure is complete pending 2 deep cyclotomic targets** と整理しておる。

加えて、前回の修正で \(P \mid (p)\) 分岐の target の向きが正され、
もはや狙うべきは
$$
P \le (\zeta-1)
$$
ではなく
$$
P = (\zeta-1)
$$
だと定まった。さらに \((\zeta-1)\) が prime ideal を生成する方向も no-sorry で mainline に降りてきた。これはかなり大きい。

つまり、今の戦況を一言で言えば

$$
\boxed{
\text{Stage 1 は「未完成」ではなく、「deep cyclotomic target 2 本待ち」の段}
}
$$

じゃよ。

## 何が残敵か

残る open は、もう広くない。ほんに次の 2 本だけじゃ。

$$
\texttt{PrimeOverPEqualsZetaMinusOneTarget}
$$

$$
\texttt{IntegerInZetaMinusOneIdealDivisibleByPTarget}
$$

ぬしの差分どおり、前者は
$$
(p) = (\zeta-1)^{p-1}
$$
型の **ramification**、後者は
$$
N(\zeta-1)=p
$$
型の **norm theory** に対応する。

## 解説

いまの論理はもうかなり完成しておる。

共通 prime ideal \(P\) を仮定すると、既存 no-sorry 群により

$$
P \mid (p)\ \lor\ y \in P
$$

へ落ちる。
そして

* \(y \in P\) 分岐は既に閉じた
* \(P \mid (p)\) 分岐も、上の 2 target が入れば閉じる

ので、coprimality theorem そのものはもう完成済みじゃ。
したがって、今のボトルネックは generic ideal arithmetic でも local factorization でもない。**actual cyclotomic number theory の深部 2 点だけ** なんじゃ。

## Mathlib を踏まえた見立て

official docs を見ると、かなり近い部品は既にある。
特に cyclotomic ring of integers 側には

* `IsPrimitiveRoot.zeta_sub_one_prime'`
* `IsPrimitiveRoot.norm_toInteger_sub_one_of_prime_ne_two`
* `IsPrimitiveRoot.norm_toInteger_sub_one_of_prime_ne_two'`
* `IsPrimitiveRoot.prime_dvd_of_dvd_norm_sub_one`
* `IsPrimitiveRoot.toInteger_sub_one_dvd_prime'`
* `IsPrimitiveRoot.finite_quotient_span_sub_one`

が並んでおる。 ([Lean Community][1])

ここから見える戦況判断は、かなりはっきりしておる。

### 1. target 2 のほうが近い

$$
\texttt{IntegerInZetaMinusOneIdealDivisibleByPTarget}
$$

の方は、norm API にかなり近い。
docs に `norm_toInteger_sub_one_of_prime_ne_two` 系と `prime_dvd_of_dvd_norm_sub_one` が見えておるので、
$$
n \in (\zeta-1)
\Rightarrow
(\zeta-1)\mid n
\Rightarrow
p \mid N(n)
\Rightarrow
p \mid n
$$
という橋は、かなり自然に見える。 ([Lean Community][1])

### 2. target 1 のほうが重い

$$
\texttt{PrimeOverPEqualsZetaMinusOneTarget}
$$

の方は、ramification / ideal factorization の uniqueness を要する。
docs には `zeta_sub_one_prime'` は見えるが、**「\(P \mid (p)\) なら唯一の prime ideal 因子として \(P=(\zeta-1)\)」をそのまま返す表面 API は、少なくとも見えていない**。
なので、こちらは ideal-level の adapter をもう一段書く必要がありそうじゃ。 ([Lean Community][1])

## 総評

いまの戦況を誇張なく言えば、

* **構造戦は勝ち**
* **残敵は deep cyclotomic 2 本**
* しかもその 2 本は対称ではなく、**norm 側のほうが先に落ちそう**

という状態じゃ。

わっちの見立てでは、いま最も現実的な評価はこうじゃ。

$$
\boxed{
\text{Stage 1 の残りは 2 target だが、先に崩れるのは norm 側}
}
$$

つまり、戦況は優勢。
もう「どこを攻めるべきか分からぬ」段ではない。
**次の勝負どころが ramification と norm の 2 本に見えている**。それ自体が、大きな前進じゃよ。

[1]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/NumberField/Cyclotomic/Basic.html "Mathlib.NumberTheory.NumberField.Cyclotomic.Basic"

## 自力証明の筋

うむ。
**結論から言えば、わっちは「自力で書ける見込みはある」と見る。**
ただし 2 本は難度が違う。

$$
\texttt{IntegerInZetaMinusOneIdealDivisibleByPTarget}
$$

は **かなり高い見込み**、
$$
\texttt{PrimeOverPEqualsZetaMinusOneTarget}
$$

は **書ける可能性は十分あるが、少し重い**、という見立てじゃ。

いまの戦況自体、そこまで削れておる。
Stage 1 の coprimality の構造はもう完成しており、残る open はまさにその 2 target だけだと、ぬしの差分も示しておる。

Mathlib 側にも近い部品はすでにある。
公式 docs には、\(\zeta-1\) について

* `IsPrimitiveRoot.toInteger_sub_one_dvd_prime'`
* `IsPrimitiveRoot.norm_toInteger_sub_one_of_prime_ne_two'`
* `IsPrimitiveRoot.zeta_sub_one_prime'`
* `IsPrimitiveRoot.subOneIntegralPowerBasis`

が並んでおる。つまり、**\(\zeta-1\) が \(p\) を割ること、\(\mathrm{Norm}(\zeta-1)=p\) であること、\(\zeta-1\) が prime であること** までは、Mathlib の表側に見えておる。 ([Lean Community][1])

だから、「無いなら自分で書くしかない」は、その通りじゃ。
待っておっても、ここは閉じぬ。
そして幸い、**完全な暗闇ではなく、既存 API の少し先を自分で橋渡しする段** に来ておる。

## 1. target 2 は、自力証明の見込みが高い

これは

$$
\texttt{IntegerInZetaMinusOneIdealDivisibleByPTarget}
$$

じゃな。
内容は

$$
(n : \mathcal O_K)\in (\zeta-1)
\;\Longrightarrow\;
p \mid n
$$

じゃ。

これは、かなり自然な norm 証明になる。
骨格はこうじゃ。

$$
(n) \subseteq (\zeta-1)
\quad\text{ではなく}\quad
n \in (\zeta-1)
\Rightarrow
(\zeta-1)\mid n
$$

として、ある \(a\in\mathcal O_K\) があって

$$
n = (\zeta-1)a
$$

と書く。
そこへ norm を取ると

$$
N(n)=N(\zeta-1)N(a)
$$

じゃ。
ここで \(n\) は整数なので

$$
N(n)=n^{[K:\mathbf Q]}
$$

となる。
さらに Mathlib に見えている結果で

$$
N(\zeta-1)=p
$$

が使える。
すると

$$
p \mid n^{[K:\mathbf Q]}
$$

ゆえに素数性から

$$
p \mid n
$$

じゃ。

この証明は、数学としてはかなり素直じゃし、Mathlib 側にも `norm_toInteger_sub_one_of_prime_ne_two'` が見えておるので、**bridge を自分で書けば届く公算が高い**。 ([Lean Community][1])

わっちの見込みでは、これは **高確率で自力証明できる**。
詰まるとすれば、norm の型変換、

* `K` の元の norm
* `𝓞 K` 上の元の norm
* `n : ℕ` を `𝓞 K` へ入れたときの norm

の繋ぎじゃ。
されど、これは「深い新理論」ではなく **API 接続の骨折り仕事** に近い。

## 2. target 1 も自力証明は可能性が高いが、少し重い

こっちは

$$
\texttt{PrimeOverPEqualsZetaMinusOneTarget}
$$

で、

$$
P \mid (p),\quad P \text{ prime}
\;\Longrightarrow\;
P=(\zeta-1)
$$

を言いたいのじゃな。

これは要するに、\((p)\) の prime ideal factorization が cyclotomic prime case で **完全分岐** することを使う話じゃ。
ぬしの修正どおり、「\(P \subseteq (\zeta-1)\)」ではなく「**\(P=(\zeta-1)\)** 」が正しい狙いじゃ。

自力証明の骨格は、わっちは次の 2 route があると見る。

### 2.1. ideal factorization / valuation route

本筋はこれじゃ。

* まず \((\zeta-1)\) が prime ideal を生成することを使う
  これはすでに `zeta_sub_one_ideal_isPrime` で mainline に降りておる。
* 次に \((\zeta-1)\mid (p)\) を使う
  これは `toInteger_sub_one_dvd_prime'` から既に adapter を作っておる流れに近い。
* その上で、「\((p)\) を割る prime ideal は \((\zeta-1)\) しかない」と示す

この最後の一歩が重い。
ここは ideal factorization の一意性、あるいは prime ideal の valuation を使って、

$$
(p)=u\cdot(\zeta-1)^{p-1}
$$

型を出すのが王道じゃ。

Mathlib の表側 docs だけでは、この形の theorem は見えておらぬ。
だからここは **自分で補題を作る覚悟が要る**。

### 2.2. discriminant / power basis route

もう一つは、`subOneIntegralPowerBasis` を使って \(\zeta-1\) が integral power basis の生成元になっていることを土台に、
その minimal polynomial / Eisenstein 性から \((p)\) の分岐を直接読みに行く route じゃ。
Mathlib docs に `subOneIntegralPowerBasis` は見えておる。 ([Lean Community][1])

この route は美しいが、Lean 実装は少し長くなる。
なので、いまの DkMath の進行速度を考えると、まずは 2.1 の **valuation / ideal factorization 寄り** が現実的じゃろう。

## 3. だから、見込みはこうじゃ

率直に言うぞい。

* target 2 は **かなり書ける見込みが高い**
* target 1 も **書ける可能性は十分ある**
* ただし target 1 は、target 2 より **1 段深い**
  つまり「norm の橋」ではなく「ramification の橋」を自分で架ける必要がある

じゃ。

だから「賢狼は証明できるか」と問われれば、
**yes、ただし順番が大事** と答える。

## 4. いま取るべき戦略

わっちなら、こう攻める。

### 4.1. まず target 2 を先に落とす

これは見込みが高い。
しかも落ちれば、「\((\zeta-1)\) ideal に入る整数は \(p\) で割れる」という非常に使いやすい武器になる。
Stage 1 だけでなく、後の descent にも効く可能性がある。

### 4.2. そのあと target 1 を攻める

target 1 は重いが、target 2 が落ちていれば、
「\((\zeta-1)\) が \(p\) を支配する ideal」という感触が Lean 上でも具体化するので、次の設計がしやすい。

### 4.3. もし target 1 が重すぎたら

ここが大事じゃ。
**target 1 を丸ごと証明しなくても、Stage 1 を閉じるのに必要な弱い形へ落とす手もある。**

たとえば、ほんとうに必要なのは

$$
P \mid (p),\ z-\zeta y\in P
\Rightarrow
z-y \in (\zeta-1)
\Rightarrow
p \mid \mathrm{gap}
$$

という contradiction route が通ることじゃ。
ならば
$$
P=(\zeta-1)
$$
そのものより弱い

$$
P \mid (p),\ hP\ \text{prime},\ hP_{\mathrm{chosen}}
\Rightarrow
z-\zeta y \in (\zeta-1)
$$

のような **specialized theorem** で十分な場合もある。
ここは target 1 をそのまま掘るより短いかもしれぬ。

## 5. 結論

ひとことで言えば、こうじゃ。

$$
\boxed{
\text{自力証明の見込みはある。}
\text{まず norm 側 target 2 はかなり現実的、ramification 側 target 1 は少し重いが十分射程内。}
}
$$

そして、待っていても仕方ない、というぬしの言葉はその通りじゃ。
ここは **Mathlib を待つ段ではなく、DkMath 側で橋を先に作る段** じゃよ。

わっちの実戦的な提案は 1 つじゃ。

$$
\boxed{
\text{次は target 2 を自力で落とす。}
\text{その後、target 1 は必要なら弱い specialized 形へ落としてでも先へ進む}
}
$$

これがいちばん勝ち筋が太い。

## 仮定の真偽判定

うむ。
作業を始める前に **「その仮定、ほんに真か？」** を疑うのは、たいへん筋が良い。
いまの戦況なら、疑うべき仮定はかなり絞れておる。

## 1. 今の戦況

まず前提として、Stage 1 の **構造そのもの** はかなり完成に近い。
今回の更新で、

* `noPrimeOrY_of_firstCase_of_coprime`
* `chosenLinearFactor_isCoprime_with_other_of_firstCase_of_pack`

が入り、Stage 1 の coprimality ルート自体は **2 つの deep target を仮定すれば no-sorry で完成** した。
つまり、残っているのは generic ideal arithmetic ではなく、深い cyclotomic 仮定 2 本だけじゃ。

その 2 本は、いまこうなっておる。

$$
\texttt{PrimeOverPEqualsZetaMinusOneTarget}
$$

$$
\texttt{IntegerInZetaMinusOneIdealDivisibleByPTarget}
$$

しかも前者は最近、`P \subseteq (\zeta-1)` ではなく
$$
P = (\zeta-1)
$$
へ修正された。
この修正自体は論理方向として正しいが、同時に **仮定が強くなった** ことも意味しておる。

## 2. どの仮定が「偽」の可能性を疑うべきか

### 2.1. いちばん疑うべきは target 1 の「等号」

いちばん危ういのは、これじゃ。

$$
P \mid (p),\ P\ \text{prime}
\;\Longrightarrow\;
P = (\zeta-1)
$$

これは **たぶん真であろう方向** ではある。
されど、いまの proof で **本当に必要なのは等号そのものか？** と問うと、そこは怪しい。

実際、`noPrimeOverP_of_firstCase_of_chosenFactorInP` で欲しいのは、要するに

$$
z-\zeta y \in P
\quad\Longrightarrow\quad
z-\zeta y \in (\zeta-1)
$$

へ運ぶことじゃ。
そのために必要なのは、厳密には

$$
P \le (\zeta-1)
$$

あるいはもっと弱く

$$
P \mid (p),\ z-\zeta y \in P
\;\Longrightarrow\;
z-\zeta y \in (\zeta-1)
$$

のような **membership transfer** で十分な可能性が高い。
つまり、今の target 1 は **真でも強すぎる** かもしれぬ。
そして「強すぎる仮定」は、実装上しばしば「証明不能」ではなく「不要に重い」原因になる。

わっちの見立てでは、**まず疑うべきは「偽」そのものより「過剰」** じゃ。

### 2.2. target 2 は、偽より「真だが橋がまだ無い」側

もう一方は

$$
(n : \mathcal O_K)\in (\zeta-1)
\;\Longrightarrow\;
p \mid n
$$

じゃ。
これはかなり自然で、むしろ **真である見込みが高い**。
Mathlib docs にも \(\zeta-1\) について

* `zeta_sub_one_prime'`
* `norm_toInteger_sub_one_of_prime_ne_two'`
* `finite_quotient_span_sub_one`
* `toInteger_sub_one_dvd_prime'`

が見えておるので、quotient か norm のどちらかで導ける気配がかなり濃い。 ([Lean Community][1])

したがって、target 2 は「偽の可能性を疑う」より、**真だがまだ adapter / bridge が無い** と見るのが自然じゃ。

### 2.3. もう一つ疑うべきは「first case」の使い方

ここは地味に大事じゃ。
今の combiner は

$$
\neg, p \mid \mathrm{gap}
$$

を first case 的に使っておる。
だが古典的な FLT の first case は普通

$$
p \nmid xyz
$$

の形じゃ。
ゆえに、**この branch で使っている \(\neg p \mid \mathrm{gap}\) が、どこから本当に supply されるのか** は、仮定の真偽というより「供給源の確認」が必要じゃ。
もしここが “まだ branch 仮定として置いているだけ” なら、それはそれでよい。
されど、pack から自動に出るつもりで話が進んでいるなら、そこは危ない。

## 3. わっちの判定

現時点での判定を率直に言うぞい。

### 3.1. 「偽」の危険が高い順

1. **target 1 の等号版**
   $$
   P = (\zeta-1)
   $$
   は、真だとしても **強すぎる可能性が高い**。
   まずは「本当に等号が必要か」を疑うべきじゃ。

2. **first case の gap 版の供給源**
   これは命題自体が偽というより、**供給の想定がズレている危険** がある。

3. **target 2**
   これは偽の危険は比較的低い。
   むしろ真で、norm / quotient の橋がまだ無いだけと見る方が自然じゃ。 ([Lean Community][1])

## 4. 次の戦略

作業前の「仮定の falsification check」として、わっちならこうする。

### A. target 1 を弱い形へ落としても Stage 1 が回るかをまず検査

いまの `PrimeOverPEqualsZetaMinusOneTarget` を一旦やめて、次のような弱い仮定で足りるかを試す。

$$
\texttt{PrimeOverPChosenFactorToZetaMinusOneTarget}:
\quad
P \mid (p) \to z-\zeta y \in P \to z-\zeta y \in (\zeta-1)
$$

あるいは少し強くても

$$
P \mid (p) \to P \le (\zeta-1)
$$

までで十分かを確認する。
もしこれで `noPrimeOverP_of_firstCase_of_chosenFactorInP` が通るなら、**等号 target は過剰だった** と分かる。
これは「仮定が偽か」を調べるより、はるかに賢い検査じゃ。

### B. target 2 は norm route で短く試す

target 2 は、ほんに真っぽい。
だから falsification より、短い norm skeleton を起こしてみるのがよい。

骨格はこれじゃ。

$$
n \in (\zeta-1)
\Rightarrow
\exists a,\ n=(\zeta-1)a
$$

$$
N(n)=N(\zeta-1)N(a)
$$

$$
N(\zeta-1)=p
$$

$$
N(n)=n^{[K:\mathbf Q]}
$$

よって

$$
p \mid n^{[K:\mathbf Q]}
\Rightarrow
p \mid n
$$

じゃ。
この route が Lean で繋がるなら、target 2 は「仮定」ではなくすぐ theorem に降ろせる。 ([Lean Community][1])

### C. gap first case は supply source を明示する

$$
\neg p \mid \mathrm{gap}
$$

が branch assumption なのか、既存 theorem から出るのかを、ここで一度明文化しておく。
ここを曖昧にしたまま deep target を掘ると、後で「仮定は真だったが branch 側が空中戦だった」という事故になる。

## 5. ひとことでまとめると

$$
\boxed{
\text{いま疑うべきは「target 2 が偽か」ではなく、
target 1 の等号版が強すぎないか、そして gap-first-case の供給が曖昧でないか、じゃ}
}
$$

わっちの勘では、

* target 2 は **かなり真っぽい**
* target 1 は **真でも過剰**
* まず弱い形に落として Stage 1 が回るか検査するのが最善

じゃよ。

これをやってから本格実装に入るのが、いちばん賢い。
