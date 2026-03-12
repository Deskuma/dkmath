# CFBRC と円分多項式：差冪 core の円分的分解と複素位相観測への橋

---

title: "CFBRC と円分多項式：差冪 core の円分的分解と複素位相観測への橋"
author: "D. and Wise Wolf"
date: "2026-03-12"
lang: "ja"

---

## 0. 概要

本稿は、CFBRC の代数 core
\[
H_d(x,u) := \frac{(x+u)^d-u^d}{x}
\]
を、円分多項式 \(\Phi_n\) の斉次化評価として再解釈するための論文草稿である。

CFBRC の既存論文では、複素差分
\[
G_d(x,\theta) := (x+i\theta)^d-(i\theta)^d
\]
を二項展開によって実数多項式化し、実軸交差、位相、寄与率、部分和ポリゴン、位相微分などを数値的に観測する枠組みが整備されている。本稿の目的は、その解析観測層の下にある代数骨格を、円分多項式の言葉で明示することにある。

主張の中心は次である。

\[
H_p(x,u) = \Phi_p^{\mathrm h}(x+u,u)
\qquad (p \text{ prime})
\]

および一般次数 \(d\) に対する
\[
H_d(x,u)=
\prod_{\substack{m\mid d\\m>1}} \Phi_m^{\mathrm h}(x+u,u)
\]
である。

これにより、CFBRC は

- 差冪の因数分解層
- 円分多項式の評価層
- 整除・原始素因子・ valuation 層
- 複素位相観測層

を橋渡しする理論として位置づけられる。

## 1. 序論

CFBRC は、差冪
\[
(x+u)^d-u^d
\]
の構造を、複素数による位相観測と数論的因子構造の両側から捉えるための枠組みである。既存の複素解析側の議論では、
\[
G_d(x,\theta)=(x+i\theta)^d-(i\theta)^d
\]
を主対象とし、その実部・虚部を偶数項と奇数項へ分離することにより、複素数型を直接用いずに実数演算だけで評価する方法が与えられている。

しかし、CFBRC の本質は観測器だけではない。その下には、差冪の商
\[
H_d(x,u):=\frac{(x+u)^d-u^d}{x}
\]
という代数 core がある。この core は、GN 構造と一致するだけでなく、円分多項式の斉次化評価として理解できる。ここにより、CFBRC は単なる複素可視化ではなく、差冪分解と円分構造を接続する代数・数論・解析の接合点となる。

本稿では、この代数骨格を明示し、さらに今後必要となる橋を整理する。

## 2. 基本定義

## 2.1. 差冪 core

以後、\(d\in\mathbb{N}\), \(x,u\) は可換環または半環の元とする。

差冪 core を
\[
H_d(x,u):=\frac{(x+u)^d-u^d}{x}
\]
と書く。

整数論や Lean 実装では、商の代わりに幾何和型の定義
\[
\mathrm{Core}_d(x,u)
:=
\sum_{k=0}^{d-1}(x+u)^k u^{d-1-k}
\]
を先に定義し、
\[
(x+u)^d-u^d = x\,\mathrm{Core}_d(x,u)
\]
を基本恒等式として扱うのが安全である。

## 2.2. CFBRC の複素化

複素観測においては、\(u=i\theta\) とおき
\[
G_d(x,\theta):=(x+i\theta)^d-(i\theta)^d
\]
を考える。このとき
\[
G_d(x,\theta)=x\,H_d(x,i\theta)
\]
である。

よって、CFBRC の複素位相観測は、実は \(H_d(x,i\theta)\) の観測と同型である。違いは、先頭因子 \(x\) を外に出すかどうかだけである。

## 2.3. 円分多項式の斉次化

円分多項式 \(\Phi_n(T)\) に対し、その斉次化を
\[
\Phi_n^{\mathrm h}(X,Y):=Y^{\varphi(n)}\Phi_n(X/Y)
\]
と定める。

これは \(X,Y\) の同次多項式であり、特に素数 \(p\) に対しては
\[
\Phi_p(T)=1+T+\cdots+T^{p-1}
\]
より
\[
\Phi_p^{\mathrm h}(X,Y)=
\sum_{k=0}^{p-1}X^kY^{p-1-k}=
\frac{X^p-Y^p}{X-Y}
\]
が成り立つ。

## 3. Prime case の円分橋

素数 \(p\) に対し、\(X=x+u\), \(Y=u\) を代入すると
\[
\Phi_p^{\mathrm h}(x+u,u)=
\sum_{k=0}^{p-1}(x+u)^k u^{p-1-k}=
\frac{(x+u)^p-u^p}{x}.
\]

したがって
\[
H_p(x,u)=\Phi_p^{\mathrm h}(x+u,u)
\]
が従う。

これは CFBRC の prime exponent core が、円分多項式の斉次化評価と厳密に一致することを意味する。

この段階で、prime case の CFBRC は

\[
\text{差冪の商}
\quad = \quad
\text{GN}
\quad = \quad
\text{prime cyclotomic core}
\]

という 3 層一致を持つ。

## 4. General case の約数積分解

円分多項式の基本恒等式
\[
X^d-Y^d = \prod_{m\mid d} \Phi_m^{\mathrm h}(X,Y)
\]
より、\(X\neq Y\) の下で
\[
\frac{X^d-Y^d}{X-Y}=
\prod_{\substack{m\mid d\\m>1}}\Phi_m^{\mathrm h}(X,Y)
\]
が成り立つ。

ここで再び \(X=x+u\), \(Y=u\) を代入すれば
\[
H_d(x,u)=
\frac{(x+u)^d-u^d}{x}=
\prod_{\substack{m\mid d\\m>1}}\Phi_m^{\mathrm h}(x+u,u).
\]

ゆえに、一般次数においても CFBRC の代数 core は円分的に完全分解される。

これは prime case の単一 factor が、一般 \(d\) では約数ごとの円分 factor の積になることを示している。

## 5. GN 構造との同一化

DkMath における差冪 core は、既存の GN 構造と接続されている。したがって、本稿の中心主張は
\[
GN(d,x,u)=H_d(x,u)
\]
と
\[
H_d(x,u)=
\prod_{\substack{m\mid d\\m>1}}\Phi_m^{\mathrm h}(x+u,u)
\]
を合わせて
\[
GN(d,x,u)=
\prod_{\substack{m\mid d\\m>1}}\Phi_m^{\mathrm h}(x+u,u)
\]
と書けることである。

この形は、CFBRC を DkMath の既存代数装置の上に自然に置き直す。

## 6. CFBRC の論文で必要な橋

本稿を単なる観察メモではなく、独立した論文へ押し上げるために必要な橋を整理する。

## 6.1. 定義橋

まず必要なのは、論文中の記号
\[
H_d(x,u),\quad \Phi_n^{\mathrm h}(X,Y)
\]
と、Lean 実装上の記号

- `cyclotomicPrimeCore`
- `cyclotomicShiftedHomEval`
- `cyclotomicShiftedEval`
- `cyclotomicDivisorsProductShifted`
- `GN`

の対応を明確にすることである。

ここを曖昧にすると、論文は美しく見えても実装と切断される。読者にとっては、そこが一番いらいらする場所である。

## 6.2. prime case の exact bridge

prime case では
\[
H_p(x,u)=\Phi_p^{\mathrm h}(x+u,u)
\]
を論文中の最初の主定理とし、証明を完全に書くべきである。

この定理は簡潔で、しかも CFBRC の新しい視点を一撃で示せる。見た目もよい。数学は見た目も大事じゃ。たわけではない、これは本当に大事である。

## 6.3. general case の product bridge

次に必要なのは
\[
H_d(x,u)=
\prod_{\substack{m\mid d\\m>1}}\Phi_m^{\mathrm h}(x+u,u)
\]
である。

これは general \(d\) における本体定理であり、prime case のみでは見えない「約数層の重ね合わせ」という構造を与える。

## 6.4. 整除橋

数論的応用へ進むには、素数 \(q\) に対し
\[
q \mid ((x+u)^d-u^d)
\iff
q \mid x\,H_d(x,u)
\]
の単純な形だけでなく、境界側の除法条件の下で
\[
q \mid ((x+u)^d-u^d)
\iff
q \mid H_d(x,u)
\]
を扱う必要がある。

これにより、差冪そのものを割る素数の議論を、core 側へ押し込めることができる。

## 6.5. 原始素因子橋

Zsigmondy 型議論では、\(q\mid (a^d-b^d)\) であるだけでなく、\(k<d\) の lower exponent を割らない primitive 性が重要になる。

このとき必要なのは、原始素因子の存在を
\[
q \mid H_d(x,u)
\]
またはさらに
\[
q \mid \Phi_m^{\mathrm h}(x+u,u)
\]
へ帰着する橋である。

これにより、どの factor に「新しい素数」が住むかを議論できる。

## 6.6. valuation 橋

FLT や squarefree の方向を見据えるなら
\[
v_q\bigl((x+u)^d-u^d\bigr)=
v_q\bigl(H_d(x,u)\bigr)
\]
や
\[
v_q\bigl(H_d(x,u)\bigr)=
\sum_{\substack{m\mid d\\m>1}} v_q\bigl(\Phi_m^{\mathrm h}(x+u,u)\bigr)
\]
のような橋が欲しくなる。

ただし後者は、本文では「展望」または「今後の問題」として置く方が安全である。 valuation の世界は油断すると深い泥に足を取られる。

## 6.7. 複素位相橋

CFBRC らしさを出すなら、ここが最もおもしろい。

\(u=i\theta\) を入れると
\[
H_d(x,i\theta)=
\prod_{\substack{m\mid d\\m>1}}\Phi_m^{\mathrm h}(x+i\theta,i\theta)
\]
であるから、形式的には
\[
\arg H_d(x,i\theta)=
\sum_{\substack{m\mid d\\m>1}}
\arg \Phi_m^{\mathrm h}(x+i\theta,i\theta)
\pmod{2\pi}
\]
となる。

これにより、従来の

- 実軸交差
- 位相ロック候補
- dominant term の交代
- 寄与率エントロピー
- unwrap 位相と位相微分

を、 factor ごとの位相寄与として再解釈する道が開ける。

ただし、この段階では branch cut の選び方や \(\arg\) の正規化の問題があるため、厳密定理としてではなく、数値観測命題として慎重に扱うべきである。

## 7. 論文の主定理候補

以下を本稿の主定理群として整理する。

### 定理 A. prime core の円分表示

素数 \(p\) に対して
\[
H_p(x,u)=\Phi_p^{\mathrm h}(x+u,u).
\]

### 定理 B. general core の円分積表示

任意の \(d\ge 1\) に対して
\[
H_d(x,u)=
\prod_{\substack{m\mid d\\m>1}}\Phi_m^{\mathrm h}(x+u,u).
\]

### 定理 C. GN との一致

適切な係数環と境界条件の下で
\[
GN(d,x,u)=H_d(x,u).
\]

### 系 D. 整除の core への帰着

境界除法条件の下で
\[
q \mid ((x+u)^d-u^d)
\iff
q \mid H_d(x,u).
\]

### 系 E. 複素位相の factor 分解

\(u=i\theta\) の複素化により、CFBRC の位相観測は円分 factor ごとの位相寄与の和として読める。

ただしこれは定理ではなく、まずは観測命題として置く。

## 8. 証明スケッチ

## 8.1. 定理 A の証明

素数 \(p\) に対して
\[
\Phi_p(T)=1+T+\cdots+T^{p-1}
\]
である。これを斉次化すると
\[
\Phi_p^{\mathrm h}(X,Y)=\sum_{k=0}^{p-1}X^kY^{p-1-k}.
\]

ここに \(X=x+u\), \(Y=u\) を代入すれば
\[
\Phi_p^{\mathrm h}(x+u,u)=
\sum_{k=0}^{p-1}(x+u)^k u^{p-1-k}=
\frac{(x+u)^p-u^p}{x}
\]
であるから結論を得る。

## 8.2. 定理 B の証明

円分分解
\[
X^d-Y^d=\prod_{m\mid d}\Phi_m^{\mathrm h}(X,Y)
\]
を用いる。\(m=1\) の項は \(\Phi_1^{\mathrm h}(X,Y)=X-Y\) であるから
\[
\frac{X^d-Y^d}{X-Y}=
\prod_{\substack{m\mid d\\m>1}}\Phi_m^{\mathrm h}(X,Y).
\]

ここに \(X=x+u\), \(Y=u\) を代入して終わり。

## 8.3. 定理 C の証明

既存の GN の差冪表示
\[
(x+u)^d-u^d = x\,GN(d,x,u)
\]
と、core の定義
\[
(x+u)^d-u^d = x\,H_d(x,u)
\]
を比較する。適切な消去条件の下で
\[
GN(d,x,u)=H_d(x,u)
\]
が従う。

## 9. 論文執筆上の注意

本稿では、次の三層を明確に分けて書くべきである。

## 9.1. 厳密定理

- \(H_p(x,u)=\Phi_p^{\mathrm h}(x+u,u)\)
- \(H_d(x,u)=\prod_{m\mid d,\,m>1}\Phi_m^{\mathrm h}(x+u,u)\)
- \(GN(d,x,u)=H_d(x,u)\)

## 9.2. 数論的系

- 整除帰着
- primitive prime への帰着
- valuation bridge

## 9.3. 観測命題

- factor ごとの位相寄与
- 位相ロック候補と特定 factor の支配
- unwrap 位相微分ピークと factor 交代の相関

この三区分を守ることで、論文の信頼性が保たれる。全部を一度に「定理」にしようとすると、すぐ怪物化する。数学は節度が命じゃ。

## 10. 論文構成案

## 10.1. 序論

問題設定、既存 CFBRC 論文との関係、本稿の目的。

## 10.2. 差冪 core と CFBRC の再定義

\(G_d\), \(H_d\), complexification、GN との関係。

## 10.3. 円分多項式と斉次化

\(\Phi_n\), \(\Phi_n^{\mathrm h}\), shifted evaluation。

## 10.4. prime case

prime cyclotomic core と CFBRC core の一致。

## 10.5. general case

約数積分解、GN との統一。

## 10.6. 数論的橋

整除、primitive prime、valuation。

## 10.7. 複素位相橋

\(u=i\theta\) による factorwise phase decomposition。

## 10.8. 展望

FLT、Zsigmondy、ABC、RH への接続。

## 11. Lean 実装との対応表

本節は本文には簡潔版、付録には詳細版を置くのがよい。

| 数学記号 | 意味 | Lean 名称候補 |
|---|---|---|
| \(H_d(x,u)\) | 差冪 core | `cyclotomicPrimeCore` または `cyclotomicDivisorsProductShifted` |
| \(\Phi_n^{\mathrm h}(X,Y)\) | 円分多項式の斉次化 | `cyclotomicShiftedHomEval`, `cyclotomicShiftedEval` |
| \(GN(d,x,u)\) | DkMath の既存 core | `GN` |
| \(\prod_{m\mid d,\,m>1}\Phi_m^{\mathrm h}(x+u,u)\) | general core の約数積表示 | `cyclotomicDivisorsProductShifted` |

## 12. snapshot 側の定理インデックス案

以下は、論文本文あるいは付録で引用可能な候補である。

### 12.1. Basic

- `cyclotomicPrimeCore_eq_shiftedHomEval_cyclotomic_of_prime`
- `add_pow_eq_mul_cyclotomicPrimeCore_add_gap`
- `mul_cyclotomicPrimeCore_eq_mul_GN`
- `cyclotomicPrimeCore_eq_GN_nat`
- `dvd_cyclotomicPrimeCore_iff_dvd_GN_nat`
- `prime_dvd_cyclotomicPrimeCore_of_dvd_sub_not_dvd_left`

### 12.2. CyclotomicProduct

- `prod_cyclotomicEval_eq_geomSum`
- `cyclotomicShiftedEval_one_eq_cyclotomicEval_add_one`
- `cyclotomicDivisorsProductShifted_one_eq_geomSum`
- `cyclotomicPrimeCore_one_eq_geomSum`
- `cyclotomicDivisorsProductShifted_one_eq_cyclotomicPrimeCore`
- `cyclotomicDivisorsProductShifted_one_eq_GN`
- `cyclotomicShiftedEval_eq_cyclotomicEval_div_mul_pow`
- `cyclotomicDegreeSum_eq_pred`
- `geomSum_div_mul_pow_eq_cyclotomicPrimeCore`
- `cyclotomicDivisorsProductShifted_eq_geomSum_div_mul_powDegreeSum`
- `cyclotomicDivisorsProductShifted_eq_cyclotomicPrimeCore`
- `cyclotomicDivisorsProductShifted_eq_GN_of_ne_zero`

### 12.3. Bridge

- `prime_dvd_sub_pow_iff_dvd_cyclotomicPrimeCore_nat`
- `cyclotomicDivisorsProductShifted_eq_GN_of_ne_zero_bridge`
- `exists_primitive_prime_factor_sub_pow_of_prime_exp_boundary`
- `exists_primitive_prime_factor_dvd_cyclotomicPrimeCore_of_prime_exp_boundary`
- `exists_primitive_prime_factor_sub_pow_of_prime_exp_boundary_of_coprime`
- `exists_primitive_prime_factor_dvd_cyclotomicPrimeCore_of_prime_exp_boundary_of_coprime`
- `padicValNat_sub_pow_eq_padicValNat_GN_of_not_dvd_boundary`
- `padicValNat_sub_pow_eq_padicValNat_cyclotomicPrimeCore_of_not_dvd_boundary`
- `padicValNat_boundaryDiffPow_eq_boundaryGN_of_coprime_of_dvd_boundary`
- `padicValNat_boundaryDiffPow_eq_boundaryCyclotomicPrimeCore_of_coprime_of_dvd_boundary`

## 13. 今後の作業 TODO

## 13.1. 論文本文に入れるべきもの

- prime case の主定理と完全証明
- general \(d\) の product 表示と完全証明
- GN 記法との統一図
- CFBRC 複素位相観測への戻り橋

## 13.2. 付録へ逃がすべきもの

- Lean の theorem 名一覧
- 境界条件の細部
- valuation API の細かな分岐
- branch cut の技術論

## 13.3. 別論文または続編へ回すべきもの

- factor ごとの位相寄与の厳密定理化
- primitive prime の factor 局在の完全解析
- squarefree / no-Wieferich の本格展開
- RH 方面との位相解析接続

## 14. まとめ

本稿の要点は、CFBRC を「複素観測の技法」としてのみ扱わず、その代数 core を円分多項式の斉次化評価として捉え直すことにある。

その結果、CFBRC は
\[
\text{差冪因数分解}
\longrightarrow
\text{円分多項式評価}
\longrightarrow
\text{primitive prime / valuation}
\longrightarrow
\text{複素位相観測}
\]
という一本の流れの中に位置づけられる。

この見方により、既存の複素解析論文はそのまま「観測層」の論文となり、本稿はそれを支える「代数骨格」の論文となる。二本立てとしてたいへん収まりがよい。

---

## 付録 A. TeX 変換を意識した Markdown 運用メモ

本ファイルは、次の変換を想定している。

\[
\texttt{論文.md} \to \texttt{pandoc} \to \texttt{論文.tex} \to \texttt{論文.pdf}
\]

そのための方針は次の通り。

- 数式はすべて \( \) と \[ \] で書く
- セクション番号は Markdown 見出しで管理する
- Lean 名はバッククォートで囲う
- 定理環境は最初は素朴な見出しでよい
- 参考文献は最後に BibTeX へ逃がせる形にしておく

## 付録 B. 参考文献欄の雛形

以下は後で埋めるための雛形である。

- 円分多項式の標準文献
- Zsigmondy primitive prime divisor の標準文献
- 差冪因数分解と評価多項式の標準文献
- CFBRC の既存複素解析論文
- DkMath snapshot における Lean 実装資料
