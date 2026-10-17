# FLT7 第四段：GN の source 保存原理 — 位相変換と係数環の境界

2026-10-16。[七乗剰余類の比較](SEVEN-UNIT-POWER-CLASS.md) が要求した source の対応を調べる。
今回は多項式としての正確な接続を作り、同じ位相での整数への直接降下には障害があることも証明した。

**正の結論**：現在の carrier は実三次係数の GN 因子そのものであり、その GN 全体は既存の軌道商に等しい。

**境界の結論**：現在の common-prime packet の選択位相を固定すると、この carrier は整数係数の GN source と等しくならない。
これは packet の仮定の下での限定的な排除であり、FLT7 の矛盾や、あらゆる位相・規格化による対応の不可能性ではない。

## 1. source の座標を固定する

GN の規約は

\[
(x+u)^p-u^p=x\,GN_p(x,u)
\]

である。位相 ξ の線形因子を

\[
\operatorname{source}(\xi;x,u)=x+(1-\xi)u
\]

と定義する。`phaseSource` は任意の可換環でこの元を表す。
端点 a,b を使えば

\[
\operatorname{source}(\xi;a-b,b)=a-\xi b.
\]

普通の FLT 座標の `a+ζⁱb` は `x=a+b,u=−b` であり、
今回の `a−ζⁱb` には `x=a−b,u=b` を使う。この二つの符号を区別する。

## 2. 環の写像は何を保存するか

環準同型 f は

\[
\boxed{f(\operatorname{source}(\xi;x,u))
=\operatorname{source}(f(\xi);f(x),f(u))}
\]

を満たす。`map_phaseSource` はこれを証明する。
既存の `map_GN` も GN 全体を同じように保存する。
この意味での係数環の拡大には、非零 gap や割り算は必要ない。

ただし、これは **元の像の等式** である。
f(ξ) だけを変更し、係数を元のままにしてよいとは言っていない。
非零 u については

\[
\operatorname{source}(\xi;x,u)=\operatorname{source}(\eta;x,u)
\iff\xi=\eta
\]

が成り立つ。`phaseSource_eq_iff_phase_eq` は一つの因子のこの識別を固定する。
全因子の積が位相の再添字付けで保たれることと、選ばれた一因子が同じ元であることは別の主張である。

## 3. 位相変換は係数も運ぶ

f(ζ)=ηᵏ なら

\[
f(\operatorname{source}(\zeta^i;x,u))
=\operatorname{source}(\eta^{ki};f(x),f(u)).
\]

`map_phaseSource_pow` はこの式を与える。
f(x)=x,f(u)=u を別途証明した場合だけ、係数を固定した位相変換として書ける。

既存六次環 C の回転 σ は

\[
\sigma(\zeta)=\zeta^2,\qquad
\sigma(\operatorname{ofReal}(a))=\operatorname{ofReal}(\operatorname{rotate}(a)).
\]

従って `rotate_realGNSource` の結論は

\[
\boxed{\sigma(A_i(x,u))=A_{2i}(\operatorname{rotate}(x),\operatorname{rotate}(u))}
\]

である。実三次生成元 α は `rotate(α)=α²−2α` に変わる。
テストでは、α を係数に持つ source について、この変化を省略すると等式が失敗することも確認した。

二次共役は実係数を固定するが、位相を逆元へ送る。
`star_realGNSource` は

\[
\operatorname{star}(A_i(x,u))=A_{6i}(x,u)
\]

を与える。これも一般には元の source 自身との等式ではない。

指数を mod 7 で揃える補題 `phaseSource_eq_of_pow_modEq` も追加した。
例えば `2*4≡1 mod 7` から同じ根の冪は得られるが、回転した係数が元へ戻ることまで供給するものではない。

## 4. 現在の carrier は実三次 GN の同じ元である

R を `SevenRealCubicInt` とする。現在の source は

\[
A=\operatorname{ofReal}(\operatorname{rotate}(\rho))-
\zeta^j\operatorname{ofReal}(\rho),
\qquad j=\operatorname{phaseInverseExponent}(c.\mathrm{phase}).
\]

現在の三つのアドレスの j は 1,4,5 であり、いずれも非自明である。
これを実三次係数の

\[
x_R=\operatorname{rotate}(\rho)-\rho,\qquad u_R=\rho
\]

で書けば

\[
\boxed{A=A_j(x_R,u_R)}.
\]

`currentLinearCarrier_eq_realGNSource` が、追加の source 等式を仮定せずこれを証明する。
ここで `realGNSource` は、実三次係数を C に埋め込んで評価した `phaseSource` である。

さらに、一般の位相積公式を使って

\[
\boxed{A\mid GN_7(\operatorname{ofReal}(x_R),\operatorname{ofReal}(u_R))}
\]

を得る。`currentLinearCarrier_dvd_real_GN` が対応する。
既存の有限幾何和との同一性から

\[
\boxed{GN_7(\operatorname{ofReal}(x_R),\operatorname{ofReal}(u_R))
=\operatorname{ofReal}(\operatorname{directOrbitQuotient}(p))}
\]

も証明した。`current_real_GN_eq_orbitQuotient` は gap の値で割らない有限恒等式である。

これらは、現在の source が GN の世界の外にあるのではなく、**係数環が実三次環である**ことを示す。
ここから `RamifiedPrincipalPowerPacket` の整数係数の仮定や、`x*GN=c⁷` という新しい方程式が自動で得られるわけではない。

## 5. 同じ位相での係数の一意性

C は R 上で基底 `1,ζ` を持つ二次代数である。
1≤i<7 では ζⁱ の虚座標は非零。
`zeta_pow_im_ne_zero` は、そのノルムが1で位数が奇数であることから証明する。
もし実側に属せば共役で固定され、平方が1になる。七乗も1なので元は1となり、原始性に反する。

この非零虚座標で係数を消去すると

\[
\operatorname{ofReal}(a)-\zeta^i\operatorname{ofReal}(b)
=\operatorname{ofReal}(c)-\zeta^i\operatorname{ofReal}(d)
\iff a=c\ \land\ b=d.
\]

`real_phase_endpoints_unique` はこの二座標の一意性を返す。
位相0では成り立たないため、非自明位相の条件は省略しない。

## 6. 整数 GN source へ降りるための必要十分条件

前章の `GNPhaseFactor x u i` は x,u が **整数** の source だった。
`GNPhaseFactor_eq_realGNSource` は、それが実三次 source の整数係数への制限に等しいことを証明する。

前節より、同じ非自明位相では

\[
\boxed{\operatorname{ofReal}(a)-\zeta^i\operatorname{ofReal}(b)
=GNPhaseFactor(x,u,i)
\iff a=(x+u)\ \land\ b=u}
\]

となる。右辺の整数は R への埋め込みで読む。
`real_phase_eq_integer_GN_iff` がこの判定を与える。
さらに存在形にまとめた `exists_integer_GN_source_iff` は

\[
\boxed{\text{同じ位相の整数 GN source 表示が存在}
\iff a,b\text{ がともに整数の像に属する}}
\]

を証明する。

したがって「係数環を拡大して同じ多項式を評価する」ことと、
「実三次係数が整数の像に属すと証明する」ことは、逆向きの別の課題である。
テストでは a=b=α の source が同じ位相で整数表示を持たないことを、具体的な第二座標から検証した。
これは仮想的な FLT 反例を入力としない境界の実例である。

## 7. 現在の packet では、同じ位相の直接降下を排除できる

`CurrentCommonPrimeCyclotomicPacket c` は、ある素数 q の剰余体で

\[
\tau=\frac{\operatorname{eval}(\operatorname{rotate}(\rho))}{\operatorname{eval}(\rho)},
\quad\operatorname{eval}(\rho)\ne0,\quad\tau\ne1
\]

という情報を保持している。

もし ρ が整数 n の像なら、Galois 回転は整数を固定するので `rotate(ρ)=ρ`。
すると上の商は1となり、τ≠1 に反する。
`current_rho_not_integer` は、この **common-prime packet の仮定の下で** ρ が整数ではないことを示す。
任意の実三次根パケット全体に対する無条件の主張ではない。

選択位相 j について前節の必要条件 b=u を適用すると

\[
\boxed{currentLinearCarrier(c)\ne GNPhaseFactor(x,u,j)
\quad\text{for all }x,u\in\mathbb Z,\quad
j=\operatorname{phaseInverseExponent}(c.\mathrm{phase})}.
\]

`currentLinearCarrier_ne_integer_GN_same_phase` がこの結論を与える。
単元補題、前章の条件付き source 比較、完成した FLT 終点は使わない。

この結果により、前章の source 等式を、同じ位相のまま整数係数に読み替えて供給する経路は使えないことが分かった。
一方、異なる位相と係数変換を伴う対応、単元倍を含む規格化、実三次係数の GN パケットなどを一括して排除したわけではない。

## 8. 次に渡すべき入力は何か

| 既に証明したこと | そこから自動では得られないこと |
|---|---|
| 環準同型は GN と個々の source の像を保存する | 係数が整数の像に入ること |
| 位相を Galois 変換できる | 実三次係数を固定できること |
| 現在の carrier は実三次 GN の因子 | 整数係数の保存パケットの構成 |
| 単元の七乗剰余類を比較できる | 比較する source と分岐因子の対応 |
| 同じ位相の直接的な整数表示は排除された | あらゆる変換経路の不可能性、FLT7 の矛盾 |

自然な次段は、実三次係数を保持した GN パケットの合同・単元解析を設計すること、
または source と分岐因子・単元剰余類を同時に追跡する係数変換を証明することである。
前章の整数合同に基づく七次単元 criterion は、実三次整数との合同だけを入力にして適用することはできない。
新しい係数環に移る場合は、その入力条件を別途証明する必要がある。

一般の source の写像則は p に依存しないので、FLT11・FLT13 にも再利用できる。
ただし、それぞれの係数環、単元解析、降下をこの章で構成したという意味ではない。
FLT7 の反復可能な降下は引き続き未完である。

## 9. 実装と検証

- `Lib/Cosmic/GNSourceTransport.lean`: source の写像則、位相添字の変換、係数固定の条件、位相の識別。
- `FLT/Kummer/SevenGNSource.lean`: 実三次 source、具体的回転と共役、整数降下の必要十分条件、現在の GN 因子接続と同じ位相の排除。
- `DkMathTest/FLT/Kummer/SevenGNSource.lean`: 位相だけの変更の失敗、係数を伴う回転、整数例、α の非整数例、位相0の例、公理 whitelist。
- `DkMathTest/FLT/Kummer/SevenGNSourceDependencyAudit.lean`: 正の GN 接続と係数環境界の二つの証明を、型・opaque 本体・構築子まで監査する。

公開入口は `DkMath.Lib` と `DkMath.FLT.Kummer`。
実行した検証の範囲と結果は [検証記録](evidence/validation-seven-gn-source.txt) を参照。
