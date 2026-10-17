# Kummer の証明を GN・GTail・イデアルへ翻訳する研究ノート

- **日付**：2026-10-15  
- **対象**：DkMath / CosmicFormula / GN / GTail / Kummer / FLT regular  
- **位置付け**：研究構想と証明課題の整理。新規 Lean ビルドによる完成認定ではない。  
- **参照正本**：[leanprover-community/flt-regular](https://github.com/leanprover-community/flt-regular)  
- **照合資料**：DkMath snapshot `__snapshot-dk_math-lean-code-261015-0136.tar.gz`、直近の研究対話。  
- **Commit Hash** : `fcbcb43abe062d9f0d49c43e454f259982b995af`

## 0. 研究目的と核心

**主題**：正則素数に対する Fermat の最終定理の Kummer 証明を参照し、宇宙式の GN・GTail の保存・分解構造から、その各段階（円分因子、イデアル、素イデアルの付値、類群、単元、降下）を説明・形式化し直す。

既存定理の記号的な言い換えだけではなく、**「GN の因子を整数環へ移したとき、なぜイデアルが必要なのか」**を構造として同定する。

研究の道筋は次のとおり。

```text
宇宙式 Big / Body / Gap
    ↓ 多項式の展開・GTail の切断
GN と二項係数の可除性
    ↓ 素数次数の円分殻・ノルム
円分因子（共役方向への分解）
    ↓ 主イデアルへ輸送
素イデアルの support・分岐・冪
    ↓ 正則性（類群の p-torsion）
単元倍の p 乗への復元
    ↓ 単元合同と Case I / II
FLT regular の矛盾または降下
```

**区別**：二項係数の付値を桁上がりで数える「Kummer の定理」と、正則素数に対する FLT の「Kummer の証明」は異なる話題である。本研究は両者を GN・GTail を媒介に接続するものであり、片方だけではもう片方を証明しない。

## 1. Big の内部：次数を固定するまで成分分割は自由

基本的な加法を `Big = Body + Gap` とする。例えば `77 = 70 + 7`。

任意の正整数次数 $d$ に対し、非負実数上で

$$
A=77,\quad G=7,\quad u=\sqrt[d]{G},\quad
x=\sqrt[d]{A}-u
$$

と置けば、常に

$$
A-G=(x+u)^d-u^d=x\,GN_d(x,u)
$$

が成立する。ただし

$$
GN_d(x,u)=\sum_{k=1}^{d}\binom dk x^{k-1}u^{d-k}
$$

という**多項式**として定義し、$x=0$ の場合も意味を持たせる。

$d=2$ では $u=\sqrt7$、$x=\sqrt{77}-\sqrt7$。ここで $70=(\sqrt{70})^2$ でもあるが、**宇宙式の座標 $x$ は $\sqrt{70}$ ではない**。差の平方と平方の差を混同しない。

整数座標 $x,u\in\mathbb Z$ を要求すると、可能な次数と値が厳しく制限される。例えば $70=a^2-b^2$ の整数解は存在しない（平方剰余 mod $4$ は $0,1$ であり、平方の差は $2\pmod4$ にならない）。このような存在条件を素数冪合同式／CRT wheel で解析する。ただし有限個の局所合同条件を満たすことは、整数解の存在の十分条件ではない。

## 2. 二項係数を開く：Carry と GN の最初の橋

素数 $p$、$n$ の $p$ 進桁 $n=\sum_i a_i p^i$（$0\le a_i<p$）に対し、**桁多項式**を

$$
D_{p,n}(T)=\sum_i a_i T^i
$$

と定義する。すると

$$
D_{p,n}(p)=n,\qquad D_{p,n}(1)=S_p(n)
$$

である。$p=(p-1)+1$ と見て、

$$
\begin{aligned}
n-S_p(n)
&=\sum_{i\ge1} a_i(p^i-1)\\
&=(p-1)\sum_{i\ge1}a_i GN_i(p-1,1).
\end{aligned}
$$

Legendre の公式と合わせると

$$
\boxed{v_p(n!)=\frac{n-S_p(n)}{p-1}
=\sum_{i\ge1}a_i GN_i(p-1,1)}.
$$

ここで $p-1$ は**基数の差分**であり、元々の `77 = 70 + 7` における数値の Gap と同一視しない。

二つの整数 $a,b$ の加法では

$$
\boxed{S_p(a)+S_p(b)=S_p(a+b)+(p-1)C_p(a,b)}
$$

となり、$C_p(a,b)$ は基数 $p$ の桁上がり総数。Kummer の定理により

$$
\boxed{C_p(a,b)=v_p\binom{a+b}{a}}.
$$

さらに各桁から次の桁への桁上がりを $c_j\in\{0,1\}$ と書くと、

$$
\boxed{D_{p,a}(T)+D_{p,b}(T)-D_{p,a+b}(T)
=(p-T)\sum_{j\ge0} c_j T^j}.
$$

この**Carry 多項式**を $K_{p;a,b}(T)=\sum_j c_jT^j$ と名付ければ、$K_{p;a,b}(1)$ が Kummer の付値である。

例：$70+7=77$ では $C_2(70,7)=2$、$C_3(70,7)=1$。実際、$v_2\binom{77}{7}=2$、$v_3\binom{77}{7}=1$。

加法の結合律から

$$
K_{p;a,b}(T)+K_{p;a+b,c}(T)
=K_{p;b,c}(T)+K_{p;a,b+c}(T)
$$

という**Carry 補正の結合順序保存則**も得られる。これは GTail の分割・再結合との比較対象となる。

## 3. 素数次数 $p$：交差項の一斉可除性

素数 $p$ と $1\le k\le p-1$ について、

$$
v_p\binom pk=1.
$$

ゆえに整数係数多項式として

$$
(x+u)^p=x^p+u^p+pH_p(x,u),\qquad xu\mid H_p(x,u)
$$

となる。したがって

$$
GN_p(x,u)=x^{p-1}+puR_p(x,u),\qquad
GN_p(x,u)\equiv x^{p-1}\pmod p.
$$

これは二項係数のパッキングを開くと見える Frobenius 合同式の背景である。ただし**各交差項の付値**と**交差項の総和の付値**は異なり得る。

七次では

$$
\boxed{(x+u)^7-x^7-u^7
=7xu(x+u)(x^2+xu+u^2)^2}.
$$

例えば $x=1,u=2$ では $3^7-1-2^7=6\cdot7^3$。係数が持つ基本の $7$ に、因数評価による追加の $7$ が現れる。GTail はこの付値がどの切断や再結合で見えるかを研究する入口となる。

## 4. 中核恒等式：GN と円分ノルムの一致

素数 $p$、原始 $p$ 乗根 $\zeta=\zeta_p$ に対して

$$
\begin{aligned}
GN_p(x,u)
&=\frac{(x+u)^p-u^p}{x}\\
&=\prod_{j=1}^{p-1}(x+u-\zeta^j u)\\
&=N_{\mathbb Q(\zeta_p)/\mathbb Q}
\bigl(x+(1-\zeta_p)u\bigr).
\end{aligned}
$$

最初の商は多項式恒等式の略記であり、$x=0$ にも多項式として拡張される。整数 $x,u$ なら $x+(1-\zeta)u$ は代数的整数である。

**解釈**：GN は整数側の多項式値であると同時に、円分整数環内で共役一次因子を掛け合わせた**ノルム**である。これが宇宙式とイデアルの第一接点。

三次の具体例：$\omega^2+\omega+1=0$ とすると

$$
GN_3(2,1)=13=(3-\omega)(3-\omega^2)
=N_{\mathbb Q(\omega)/\mathbb Q}(3-\omega).
$$

## 5. FLT への座標変換とイデアル化

奇素数 $p$ の仮想的反例 $a^p+b^p=c^p$ に対して

$$
x=a+b,\qquad u=-b
$$

と置けば

$$
\boxed{(a+b)GN_p(a+b,-b)=c^p}.
$$

円分体では

$$
\boxed{GN_p(a+b,-b)=\prod_{j=1}^{p-1}(a+\zeta^j b)}.
$$

円分整数環 $R=\mathbb Z[\zeta_p]$ の主イデアルへ移すと

$$
\boxed{(c)^p=(a+b)\prod_{j=1}^{p-1}(a+\zeta^j b)}.
$$

ここで $(\alpha)$ は**主イデアル**であり、元の数値とは区別する。

主イデアル化は乗法を保存する：$(\alpha\beta)=(\alpha)(\beta)$。一方、一般に $(\alpha+\beta)\ne(\alpha)+(\beta)$。したがって、**宇宙式の加法分割から、因数分解を経て、イデアルの乗法構造へ輸送する**のが正確な橋である。

異なる円分因子 $\alpha_i=a+\zeta^i b$ について

$$
\alpha_i-\alpha_j=b(\zeta^i-\zeta^j).
$$

原始性などの適切な仮定の下で、異なる因子の共通素イデアルは分岐素イデアル $\mathfrak p=(1-\zeta)$ に関係するものへ限定される。$pR=\mathfrak p^{p-1}$。**Case I（$p\nmid abc$）と Case II（$p\mid abc$）の分岐・互いに素性の証明が必要であり、積が $p$ 乗というだけで個々の因子が $p$ 乗とは言えない。**

## 6. 類群・単元は何を妨げるのか

互いに素性と素イデアルの一意分解により、ある円分因子に対して

$$
(\alpha)=I^p
$$

を得たとする。しかし一般には $I$ が主イデアルとは限らない。

- **類群の障害**：$[I]^p=1$ であっても $[I]\ne1$ があり得る。
- **正則素数条件**：$p\nmid h_{\mathbb Q(\zeta_p)}$、すなわち類群に非自明な $p$-torsion がない。この条件なら $I=(\gamma)$ と結論できる。
- **単元の障害**：したがって $\alpha=\varepsilon\gamma^p$（$\varepsilon\in R^\times$）となるが、**単元 $\varepsilon$ が $p$ 乗とは限らない**。

したがって Kummer の Case I の合同条件、Case II の Kummer 補題・降下処理を飛ばすことはできない。

特に **正則性は PID 性より弱い**。$p=7$ に対して DkMath に記述されている整数環 PID・類数1の結果は強い特殊条件であり、一般の正則素数定理と混同しない。

## 7. GTail と素数冪 wheel の研究範囲

GTail の切断を

$$
(x+u)^d=\sum_{k=0}^{r-1}\binom dk x^ku^{d-k}
+x^rGTail(d,r,x,u)
$$

とする（$0\le r\le d$）。特に $r=1$ は GN に対応し、素数次数では円分殻・ノルムとの直接接続を持つ。

$1<r\le d$ の任意の GTail にも同じ円分ノルム分解がある、とは**現段階では主張しない**。切断後の因子・素数冪付値・素イデアル support を個別に調べる。

整数座標では、各交差項の $q$-進付値（$x,u>0$）は

$$
v_q\left(\binom dk x^ku^{d-k}\right)
=v_q\binom dk+k v_q(x)+(d-k)v_q(u).
$$

一方、実際の項の和では相殺による追加付値が生じ得る。$q$ と次数 $d$ は一般には独立であり、$d=q=p$ のときに素数次数固有の一斉可除性が現れる。

各素数冪 $q^e$ での可解性を wheel／CRT で束ね、**成分の整数格子制約**と**係数の可除性制約**を別々に監査する。

## 8. Lean の参照正本と DkMath 資産

### 参照する flt-regular

- [`FltRegular/FltRegular.lean`](https://github.com/leanprover-community/flt-regular/blob/master/FltRegular/FltRegular.lean)：主定理の入口。
- [`FltRegular/NumberTheory/RegularPrimes.lean`](https://github.com/leanprover-community/flt-regular/blob/master/FltRegular/NumberTheory/RegularPrimes.lean)：正則素数を類数との互いに素性で定義。
- [`FltRegular/CaseI/Statement.lean`](https://github.com/leanprover-community/flt-regular/blob/master/FltRegular/CaseI/Statement.lean)：`exists_ideal`、`is_principal_aux`、`is_principal` を軸に、イデアル冪→元の冪へ。
- [`FltRegular/CaseII/InductionStep.lean`](https://github.com/leanprover-community/flt-regular/blob/master/FltRegular/CaseII/InductionStep.lean)：分岐素イデアル・降下の接続。
- [`FltRegular/NumberTheory/KummersLemma/`](https://github.com/leanprover-community/flt-regular/tree/master/FltRegular/NumberTheory/KummersLemma)：単元の障害を処理する Kummer の補題。

### DkMath に既存の接続部品（snapshot ソースを照合）

| ファイル                                                      | 定理・構造                                                       | 機能                             |
| ------------------------------------------------------------- | ---------------------------------------------------------------- | -------------------------------- |
| `DkMath/Lib/Cosmic/GTailCyclotomic.lean`                      | `GTail_one_eq_GTailCyclotomicShell`                              | $r=1$ の GTail と同次円分殻      |
| 同上                                                          | `GTailCyclotomicHomEval_prime_eq_shell`                          | 素数次数の円分多項式評価         |
| `DkMath/Lib/NumberTheory/IdealPowerFactor.lean`               | `exists_eq_pow_of_isCoprime_mul_eq_pow`                          | 互いに素なイデアル積から冪を抽出 |
| `DkMath/Lib/NumberTheory/ClassGroupTorsionBridge.lean`        | `classGroupPTorsionFreeAt_of_coprime_card`                       | 類数条件と $p$-torsion の橋      |
| `DkMath/Lib/NumberTheory/PrincipalIdealPower.lean`            | `exists_unit_mul_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt` | 主イデアル化と単元倍 $p$ 乗      |
| `DkMath/Lib/NumberTheory/UnitPowerSector.lean`                | `UnitPowerSectorSystem`                                          | 単元群 modulo $p$ 乗の剰余類     |
| `DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicSevenPID.lean` | `ringOfIntegers_isPrincipalIdealRing`、`classNumber_eq_one`      | $p=7$ の PID／類数1              |

**現状注意**：`DkMath/FLT/Kummer/CyclotomicPrincipalization.lean` には、確認した snapshot で `sorry` が残る箇所がある。形式化の入口が存在することは、FLT7 完成の証明ではない。上の既存定理はソースで確認したが、本研究ノート作成時に追加の Lean ビルド・公理監査は行っていない。

## 9. 実装・研究ロードマップ

| ID      | 実装・研究課題                   | 最小達成条件                                            |
| ------- | -------------------------------- | ------------------------------------------------------- |
| KGI-001 | `GN_p` と同次円分殻の対応        | 環上の多項式恒等式、符号付き座標を含む                  |
| KGI-002 | **GN = 円分ノルム**              | $\mathbb Z[\zeta_p]$ でのノルム等式                     |
| KGI-003 | 元の分解から主イデアル積への輸送 | 因子ごとの `Ideal.span` 等式                            |
| KGI-004 | 円分因子の共通素イデアル support | 分岐 $\mathfrak p=(1-\zeta)$ だけが例外である条件を明示 |
| KGI-005 | 理想の $p$ 乗抽出                | Case I / Case II の仮定を分離                           |
| KGI-006 | 類群 $p$-torsion と単元 sector   | $\alpha=\varepsilon\gamma^p$ を kernel-check            |
| KGI-007 | Kummer 補題・降下の翻訳          | 正則素数の場合の Case I / II を接続                     |
| KGI-008 | 任意 GTail への拡張              | 切断位置ごとの因子・付値・support を分類                |
| KGI-009 | Carry／wheel の統合              | 桁多項式と素数冪合同制約を対応させる                    |

**先行着手候補**：`DkMath.Lib.NumberTheory.CosmicIdealBridge`（仮称）。既存 `GTailCyclotomic` と `PrincipalIdealPower` の間を結び、まず KGI-002〜003 を完成させる。

## 10. 検証基準と未解決の問い

**証明済みの数学的事実**：Legendre・Kummer の桁上がり、素数次数の係数可除性、GN の円分ノルム表示、主イデアルの乗法性、類群の正則性に関する標準的な帰結。

**DkMath 側で確認済み**：上表の定理・構造のソース上の存在。新規総合定理の Lean 検証は未実施。

**未証明の研究仮説／課題**：任意 GTail の有用な円分／イデアル分解、GTail 切断と素イデアル support の保存則、Carry の正規化とイデアル付値の非自明な一般対応、FLT regular の全証明を GN 起点で再構築すること。

**問いの核心**：加法的な `Big = Body + Gap` から得た GN の因子分解を、円分体における乗法的な素イデアル分解へどこまで忠実に輸送できるか。そして、どの段階で「類群」「単元」「分岐」という追加の算術情報が不可避になるのか。

---

**結論**：Kummer を答えの参照地図とし、GN・GTail を出発点として同じ障害構造を再発見・再形式化する。数学的に確立した橋から順に Lean の核で固定し、FLT7 の到達点と未解決部分を混同しない。
