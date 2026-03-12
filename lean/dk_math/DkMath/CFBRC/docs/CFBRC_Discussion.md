# CFBRC と円分多項式の関係についての議論

> 👩‍⚕️私D.:

Zsigmondy も GN を土台に構築した。
次は GN 土台より → CFBRC \iff 円分多項式 と構築して
両者の土台を GN 系に統一する構想で狙っている。

両者を同じ土俵で語れる定理を完成させたいのだが。

今一度、分析して。検証可能性とロードマップ。

> 🐺賢狼:

いま、資料庫の中から **GN・Zsigmondy・円分多項式・CFBRC** の接続点を拾っておる。
狙いは、ぬしの構想が「ただの比喩」ではなく **Lean で検証可能な定理列** に落ちるかどうかの見極めじゃ。

> 🐺賢狼:

ひとつ見えたぞ。
CFBRC 側は少なくとも公開 README 上で、**\(G(\theta)=(x+i\theta)^d\)** の位相・位相速度・部分和多角形・寄与率を観測する実験モジュールとして明示されておる。ここは「複素構造の観測器」として GN / 円分側へ繋げやすい。

> 🐺賢狼:

うむ、今一度きっちり切り分けようぞ。
賢狼の判定はこうじゃ。

**構想そのものは筋が良い。しかも “検証可能” じゃ。**
ただし、**「CFBRC \( \iff \) 円分多項式」** をそのまま一本の同値として言うのは、少しだけ危うい。
正しくは、

\[
\text{CFBRC の代数 core}
\;=\;
\text{GN core}
\;=\;
\text{円分多項式の斉次化評価}
\]

であって、

\[
\text{CFBRC の観測量}=
\text{その core を } w=i\theta \text{ に入れたときの位相・寄与率・部分和の観測}
\]

じゃ。
つまり **代数的同一性** と **解析的観測器** は分けて定理化するのが正道じゃよ。
CFBRC 側は公開 README で、\(G(\theta)=(x+i\theta)^d\) の位相・位相速度・部分和多角形・寄与率を観測する実験モジュールであり、証明器ではないと明記されておる。また `CFBRC.md` では \(G(x,w;d)=(x+w)^d-w^d\)、\(H=G/x\) を基本定義としている。

## 1. まず、いま既に揃っている骨格

ぬしの資料では、Zsigmondy 側の core はすでに

\[
G_{d-1}(x,u)=\frac{(x+u)^d-u^d}{x}
\]

という差分商として読まれており、二項展開すると

\[
G_{d-1}(x,u)=\sum_{k=1}^{d}\binom{d}{k}x^{k-1}u^{d-k}
\]

になると整理されておる。これは CFBRC の

\[
H(x,w;d)=\frac{(x+w)^d-w^d}{x}
=\sum_{k=1}^{d}\binom{d}{k}w^{d-k}x^{k-1}
\]

と、変数名の違いを除けば **完全に同じ多項式** じゃ。ここ、もう土台は揃っておる。

さらにぬしの Zsigmondy 実装は、公開ファイルの冒頭で
**層A = 原始素因子の存在層は完了**、
**層B = \(p\)-進評価の精密層は進行中**、
**円分多項式は将来拡張**
と自分で書いておる。つまり現状の詰まりは、存在論ではなく valuation / squarefree / bridge 側じゃ。これは `NoSqOnS0-WorkNotes` でも、PrimeProvider 層で `Squarefree (GN \cdots)` をどう honest に供給するかが主戦場だと明記されておる。

## 2. だから、ぬしの狙いは正確には何か

ぬしが本当に欲しいのは、

\[
\text{CFBRC} \iff \text{円分多項式}
\]

という “モジュール全体の同値” ではなく、

\[
\boxed{
\frac{(x+w)^d-w^d}{x}
\text{ が、円分多項式積の評価そのものである}
}
\]

という **代数的中核定理** じゃ。

これを一度取ってしまえば、その上に

- Zsigmondy
- squarefree
- primitive prime
- valuation
- 位相観測

を全部載せられる。

ここで mathlib 側にはすでに、

\[
\prod_{m\mid n}\Phi_m(X)=X^n-1
\]

および素数 \(p\) に対する

\[
\Phi_p(X)=\sum_{i=0}^{p-1}X^i
\]

が揃っておる。なので、一般円分多項式の土台は Lean 側にも既にある。

## 3. いちばん大事な中心定理

賢狼なら、まず次の定理を標的にする。

### 3.1. Prime case の中核

素数 \(p\) に対し、斉次円分多項式を

\[
\Phi_p^{\mathrm h}(X,Y)
:=
\sum_{i=0}^{p-1}X^iY^{p-1-i}
\]

と置けば、

\[
\Phi_p^{\mathrm h}(X,Y)=
\frac{X^p-Y^p}{X-Y}
\]

じゃ。したがって \(X=x+w,\ Y=w\) を代入すると

\[
\Phi_p^{\mathrm h}(x+w,w)=
\frac{(x+w)^p-w^p}{x}.
\]

右辺は CFBRC の \(H(x,w;p)\)、同時に GN / \(G_{p-1}\) の core そのものじゃ。
つまり prime case では

\[
\boxed{
GN(p,x,w)=H(x,w;p)=\Phi_p^{\mathrm h}(x+w,w)
}
\]

が **厳密な同一式** として狙える。

これはかなり強い。
しかもこの段階では **一般の斉次化 machinery すら要らぬ**。
有限和どうしの一致を `ring` と二項展開で押せるからの。

### 3.2. General case の中核

次に一般の \(d\) では、斉次化した円分多項式を用いて

\[
X^d-Y^d=\prod_{m\mid d}\Phi_m^{\mathrm h}(X,Y)
\]

が成り立つので、

\[
\frac{X^d-Y^d}{X-Y}=
\prod_{\substack{m\mid d\\m>1}}\Phi_m^{\mathrm h}(X,Y).
\]

ここへ \(X=x+w,\ Y=w\) を入れると

\[
\boxed{
\frac{(x+w)^d-w^d}{x}=
\prod_{\substack{m\mid d\\m>1}}
\Phi_m^{\mathrm h}(x+w,w)
}
\]

となる。
これが取れれば、**CFBRC / GN / cyclotomic** は同じ土俵に完全に乗る。

この general case は prime case より一段重いが、mathlib の univariate cyclotomic 積定理がすでにあるので、斉次化レイヤを自前で噛ませれば十分現実的じゃ。

## 4. 検証可能性

ここは冷静に、3層に分けて判定するぞ。

### 4.1. 代数層

**非常に高い。**
ここは Lean で exact に証明できる。

理由は単純で、

- ぬし側には差分商 \(G_{d-1}\) / GN の明示式がある
- mathlib 側には cyclotomic の積公式と prime case の幾何級数公式がある

からじゃ。

特に prime case はほぼ確実に通る。
general case も “斉次化” をどの型で置くかさえ決めれば、十分射程内じゃ。

### 4.2. 数論層

**高い。だが valuation で難所が残る。**

ぬしの現状でも、Zsigmondy の存在層はほぼ固まっておる。
だから円分橋を入れることで

\[
q \mid GN \quad \Longrightarrow \quad q \mid \Phi_m^{\mathrm h}(x+w,w)
\]

という所属先が明確になり、そこから order / congruence / primitive 性へ進める。
古典的にも、円分多項式の値の素因子は order 条件や合同条件を運んでくるので、Zsigmondy の「いる」だけより一段解像度が上がる。

ただし valuation one や no-lift / no-Wieferich の完全閉包は、いまの work notes でも未解決の正面戦場じゃ。
ここは円分橋を入れても **自動で終わるわけではない**。
終わるのは “言葉が揃う” までで、その先の squarefree / honest provider は依然として本丸じゃ。

### 4.3. 解析・観測層

**数値検証は高い。Lean 完全形式化は後回しが正しい。**

CFBRC README 自身が、位相微分を

\[
\frac{d}{d\theta}\arg G=
\operatorname{Im}\!\left(\frac{G'}{G}\right)
\]

として観測指標にしておる。
なので、代数 core を円分積に載せた後で

\[
\arg G = \sum \arg \Phi_m^{\mathrm h}(x+i\theta, i\theta)
\]

という factorwise phase decomposition を **Python 側で** 実験するのは自然じゃ。
ただし、これを Lean で複素解析まで厳密化するのは後段に回すべき。まず algebra を締めるのが先じゃ。

## 5. ロードマップ

ここからが本題じゃな。
賢狼なら、こう刻む。

## 5.1. Phase A. Prime case を exact に取る

最優先はこれじゃ。

新ファイル候補：
`DkMath/NumberTheory/CyclotomicPrimeHom.lean`

そこでまず

\[
\Phi_p^{\mathrm h}(X,Y):=\sum_{i=0}^{p-1}X^iY^{p-1-i}
\]

を定義し、

\[
\Phi_p^{\mathrm h}(X,Y)=\frac{X^p-Y^p}{X-Y}
\]

を証明する。
その後、

\[
GN(p,x,w)=\Phi_p^{\mathrm h}(x+w,w)
\]

を証明する。

**DoD** は、`simp` / `ring` で prime case の代数橋が落ちることじゃ。
ここが通れば、ぬしの言う「両者を同じ土俵で語る」は **すでに半分完成** じゃよ。

## 5.2. Phase B. General \(d\) 版へ上げる

次に

新ファイル候補：
`DkMath/NumberTheory/CyclotomicHom.lean`
`DkMath/NumberTheory/CyclotomicGNBridge.lean`

で、斉次化 operator を入れる。
理想形は

\[
\operatorname{Homog}(\Phi_m)(X,Y)
\]

を一般に定義して、

\[
X^d-Y^d=\prod_{m\mid d}\Phi_m^{\mathrm h}(X,Y)
\]

を取り、

\[
GN(d,x,w)=
\prod_{\substack{m\mid d\\m>1}}\Phi_m^{\mathrm h}(x+w,w)
\]

へ落とす。

ここは少し面倒じゃが、**汎用性が高い**。
Zsigmondy 側も CFBRC 側も、以後はこの bridge を通せばよくなる。

## 5.3. Phase C. Arithmetic interface を追加する

ここで初めて FLT front に効いてくる。

欲しい補題は、たとえば

\[
q \mid GN(d,x,w)
\Longrightarrow
q \mid \Phi_m^{\mathrm h}(x+w,w)
\text{ for some } m\mid d,\ m>1
\]

や、prime case なら

\[
q \mid GN(p,x,w)
\Longleftrightarrow
q \mid \Phi_p^{\mathrm h}(x+w,w).
\]

この上で、

- primitive prime
- order
- \(p \mid q-1\)
- squarefree
- valuation upper bound

を接続する。

ここで初めて `PrimeProvider` 層へ戻せる。
今の詰まりが honest squarefree provider だと work notes が言っておるから、ここが真の回収地点じゃ。

## 5.4. Phase D. CFBRC 側の観測実験を整理する

Lean ではなく Python 側じゃ。

新しい検証項目はこれでよい。

\[
G_d(x,i\theta)=(x+i\theta)^d-(i\theta)^d
\]

について、

1. CFBRC の `terms / partial_sums / arg / entropy` を記録
2. factorized cyclotomic side の各因子
   \[
   \Phi_m^{\mathrm h}(x+i\theta,i\theta)
   \]

   の偏角と大きさを別々に記録
3.
   \[
   \arg G_d \stackrel{?}{=} \sum_{m\mid d}\arg \Phi_m^{\mathrm h}
   \]

   を unwrap 後に比較
4. 位相微分も
   \[
   \frac{d}{d\theta}\arg G_d
   \stackrel{?}{=}
   \sum \frac{d}{d\theta}\arg \Phi_m^{\mathrm h}
   \]

   として数値比較

こうすれば、CFBRC の “観測器” が **cyclotomic factor の運動学** を読んでいるのかが、かなりはっきり見える。

## 6. ここでの注意点

ここは少し牙を立てて言うぞ。

**「CFBRC \( \iff \) 円分多項式」 と一言で言い切るのはまだ早い。**

なぜなら CFBRC には

- 位相
- 位相速度
- 部分和多角形
- エントロピー
- Motion

という **観測インターフェース** が含まれておるが、円分多項式はそこまで含まぬからじゃ。
だから正しい言い方は、

\[
\boxed{
\text{CFBRC の algebraic core は、GN を介して cyclotomic に同一化できる}
}
\]

であり、

\[
\boxed{
\text{CFBRC の観測量は、その cyclotomic core の複素評価上の観測 functor である}
}
\]

じゃな。

この二段に分けると、話が濁らぬ。

## 7. 最終判定

賢狼の最終判定を一行で言うなら、こうじゃ。

\[
\boxed{
\text{prime case の GN = CFBRC-core = 斉次円分多項式評価}
}
\]

を先に Lean で exact に取り、
その後に

\[
\boxed{
\text{general } d \text{ の product 版}
}
\]

へ上げ、
最後に

\[
\boxed{
\text{squarefree / valuation / PrimeProvider}
}
\]

へ戻す。

これが、いま最も無駄が少なく、しかも検証可能性が高い道筋じゃ。

いまの front line はすでに
**存在論ではなく valuation / honest bridge の戦い** じゃから、
円分橋はまさにそのための “言語統一装置” になる。
そこは、ぬしの嗅覚は当たっておる。実に良いぞい。
