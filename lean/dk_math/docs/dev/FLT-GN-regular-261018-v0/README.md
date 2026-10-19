# DkMath 宇宙式入れ子・可換輸送 実装計画

cid: `6ad3b3b2-9e6c-83e8-9c41-0a5f32082ac2`

**設計番号:** GN-Nested-State-Transport-261018-v0  
**状態:** IMPLEMENTED（一般 State 降下、p≥5 の正則素数 FLT、FLT11・FLT13 の整数／自然数終点）

2026-10-18 の実装範囲・条件・未解決境界は
[実装報告](IMPLEMENTATION-261018.md) に記録した。
11・13の算術 provider と State 排除の追加実装は
[続報](IMPLEMENTATION-1113-261018.md) に記録した。
NOTE-001 の位相係数剛性・一般 Case I・整数入口と FLT11/13 終点は
[NOTE-001 実装報告](IMPLEMENTATION-NOTE001-261018.md) に記録した。
NOTE-002 のセクション4・5（GN／古典的 Kummer の境界、交換可能な供給、三つの固定契約）は
[固定契約の実施報告](CONTRACTS-NOTE002-261018.md) に記録した。
整数版 FLT の対象は `a,b,c≠0` であり、符号・共通因子の制限を除いても非零条件は必要である。
IRR-001〜005 と37次 GN・二項係数・Bernoulli 証明書は
[非正則素数の教科書実装](IMPLEMENTATION-IRR-261018.md) に記録した。
ここで追加したのは障害の観測と局所消滅を条件とする輸送であり、無条件の FLT37 や37次類群の torsion 計算ではない。
NOTE-004 §5 IRR-006 のガロア位相輸送・分岐単元補正・実際のイデアル根の対応は
[Galois 輸送の教科書実装](IMPLEMENTATION-IRR006-261019.md) に記録した。
整数係数（一般には固定座標）を前提とし、37次の観測状態にも接続する。
NOTE-005 の三根・Frey モデル・GN 判別式・局所付値の翻訳は
[Frey 算術の教科書実装](IMPLEMENTATION-NOTE005-261019.md) に記録した。
実際のモデルと正規化条件を証明し、ガロア表現・モジュラー性・レベル降下との境界を保持する。
NOTE-006 §3 の中央席 Qₙ と Frey c₄、素因子の非特異な還元・合同類の接続は
[Legendre–Frey 補題の教科書実装](IMPLEMENTATION-NOTE006-LEGENDRE-261019.md) に記録した。
NOTE-006 §4 / IRR-007 の軌道ノルムと、奇素数での正式な最小性・良還元・乗法的還元は
[軌道ノルム・局所還元の教科書実装](IMPLEMENTATION-NOTE006-SECTION4-261019.md) に記録した。
NOTE-007 §5 の IRR-008（位相0障害の除去）、2を含む半安定性、中央席の j、指標部分群の入口は
[イデアルノルム・素数2・j の教科書実装](IMPLEMENTATION-NOTE007-261019.md) に記録した。
Artin 導手と非自明指標の算術的分類は別の未実装境界として保持する。
NOTE-008 の IRR-009（実際の37-torsion類群の指標射影・直和分解）、素数2の剰余分類、
Hensel住所からj深度への輸送と二曲線の素数での比較は
[指標射影・深度輸送の教科書実装](IMPLEMENTATION-NOTE008-261019.md) に記録した。
非零類の存在・Herbrand–Ribet・Artin導手・FLT37は引き続き別の境界である。
NOTE-009 の IRR-010（指標別位相輸送）、Bernoulli32の5乗指標ラベル同定、
任意の非零整数反例からの `Source.ofCounterexample` と半安定なFrey曲線への入口は
[指標輸送・反例入口の教科書実装](IMPLEMENTATION-NOTE009-261019.md) に記録した。
対象指標成分の非零性・Artin導手・一般FLTの終点は別の境界として残る。
NOTE-010 §4以降の、同じFrey曲線の実際のE[p]・Krull連続ガロア作用、標準torsion表示へのアダプタ、
Pascal差分恒等式は [残余ガロア表現の入口](IMPLEMENTATION-NOTE010-261020.md) に記録した。
次元2・行列式・局所慣性作用・Artin導手は次の接続境界である。
元の設計書と議事録は設計・検討時点の記録として保持する。

## 1. 基本目的

宇宙式の Big・Gap・Core 間の分割と再結合を、階層間で輸送できる汎用補題として形式化する。

その上で、GN の分岐情報を失わず Kummer の状態降下へ接続する。

実装は次の三層に分離する。

1. **CoreNested** — 代数的な入れ子・経路独立性
2. **RamifiedGNPhaseBridge** — Gap・GN・円分位相の分岐情報保存
3. **RegularStateTransport** — Kummer による条件付き状態再構成と深度降下

## 2. 数学的保存核

差分 Core を

\[
C_d(t,u)=(t+u)^d-t^d
\]

とする。

最優先の入れ子恒等式は、

\[
C_d(t,a+b)=C_d(t,a)+C_d(t+a,b)
\]

である。

分割順序を交換しても、

\[
C_d(t,a)+C_d(t+a,b)
=C_d(t,b)+C_d(t+b,a)
\]

が成立する。

これを GN に移せば、

\[
(a+b)GN_d(a+b,t)
=aGN_d(a,t)+bGN_d(b,t+a)
\]

を得る。

以上は可換環上の代数定理であり、FLT の仮定を必要としない。

## 3. GN–Kummer 接続

奇素数 \(p\) と円分整数環において、

\[
x^p+y^p=(x+y)GN_p(x+y,-y)
\]

を保持する。

分岐素元を \(\lambda=1-\zeta_p\) とし、\(x+y=\lambda q\) と正規化する。

全位相商の中で、\(\lambda\nmid y\) の下では特別な一位相 \(i_0\) を一意に選べる。

その可除性集中を

\[
\lambda^{p+k}\mid x^p+y^p
\iff \lambda^k\mid Q_{i_0}
\]

として定理化する。

ここでは Gap と GN の両方を保持し、位相0に集中した分岐情報を失わない。

## 4. State 輸送

一般化する状態は、

\[
x^p+y^p=\varepsilon(\lambda^m z)^p
\]

であり、原始性と非分岐性を保持する。

目標は、

\[
\operatorname{State}_p(m+1)
\longrightarrow\operatorname{State}_p(m)
\]

という一段降下である。

この遷移は単なる等式変形ではない。類群の \(p\)-torsion-free 性、単元の \(p\) 乗化、位相商の互いに素性、三位相再構成を必要とする。

**保存対象は State の成立条件、減少対象は分岐深度** とする。

## 5. 実装順序

- NST-001：`CoreNested.lean` の新設
- NST-002：既存 `GTailTransport` との接続
- NST-003：FLT7 における分岐付値集中定理
- NST-004：一般素数 \(p\) の位相構造
- NST-005：一般 Kummer State 降下
- NST-006：FLT5・FLT3・FLT11・FLT13 への適用

## 6. 完成条件

すべての新規核心補題について Lean kernel 検証を行う。

`sorry`・`admit`・独自 `axiom` に依存せず、既存の FLT 完成定理を用いた循環証明を禁止する。

各段階で focused build、回帰検証、`#print axioms` 監査を実施する。

最初は代数的入れ子を独立に完成させ、その後に算術条件付きの状態降下へ進む。
