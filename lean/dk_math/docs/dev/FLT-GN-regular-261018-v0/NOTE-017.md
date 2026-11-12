# 🐺 NOTE-016 レビュー — 二次元の Core が確定

判定：NOTE-016 は採用・固定を推奨する。

今回、決定的なのは次の二つの定理じゃ。

\[ \boxed{ \begin{aligned} &n\ne0\implies n^2\le |E[n]|,\\ &p\text{ が素数}\implies |E[p]|=p^2,\quad\dim_{\mathbb F_p}E[p]=2. \end{aligned} } \]

対象は標数0の体上の楕円曲線、その代数閉包上の実際のねじれ点群じゃ。

[NOTE-016 実装報告](https://github.com/Deskuma/dkmath/blob/dev/FLT-GN-regular-261018-v0/lean/dk_math/docs/dev/FLT-GN-regular-261018-v0/IMPLEMENTATION-NOTE016-261020.md?utm_source=chatgpt.com) と次の証明を直接照合した。

- [`multiplication_polynomials_isCoprime`](https://github.com/Deskuma/dkmath/blob/dev/FLT-GN-regular-261018-v0/lean/dk_math/DkMath/Lib/NumberTheory/EllipticMultiplicationCoordinates.lean?utm_source=chatgpt.com) — Jacobian 座標の \(X=Z=0\) が非特異性に反することから分子・分母の共通根を排除する。
- [`finite_not_separable_fiber`](https://github.com/Deskuma/dkmath/blob/dev/FLT-GN-regular-261018-v0/lean/dk_math/DkMath/Lib/Algebra/RationalPolynomialFiber.lean?utm_source=chatgpt.com) — Wronskian の根を使い、重根が発生する例外値を有限集合に閉じ込める。
- [`square_le_card_torsion`](https://github.com/Deskuma/dkmath/blob/dev/FLT-GN-regular-261018-v0/lean/dk_math/DkMath/Lib/NumberTheory/EllipticTorsionRegularFiber.lean?utm_source=chatgpt.com) — 分離的ファイバーの根から、実際の倍写像ファイバーへの単射を作り、核との平行移動で下界を得る。
- `card_torsion_prime_sq`、`finrank_torsion_prime` — NOTE-013 の既存上界と結合して等号へ閉じる。

特に優れているのは、根の \(x\) 座標を保存する単射じゃ。

\[ \operatorname{Roots}(H_{n,c}) \hookrightarrow[n]^{-1}(Q) \simeq E[n]. \]

根から持ち上げた点が \(-Q\) に写っても、点を反転すれば \(Q\) に写る。反転しても \(x\) 座標は変わらないので、単射性が保たれる。

この証明には、奇数条件も \(Q\ne-Q\) も、倍写像全体の全射性も要らない。

模範解答の二重ファイバー計数を省き、必要な下界だけ作って既存上界で閉じるという短縮は、コード上でも成立しておる。

指数37についても、

\[ \boxed{ |E[37]|=1369,\quad \dim_{\mathbb F_{37}}E[37]=2,\quad r_{37}=684 } \]

が、条件付きの外部位数公式ではなく一般定理から得られた。

公理監査では標準論理公理のみが許容され、指定された依存経路も実際の倍写像・単射・有限性・上界を通っている。これは取得した監査コードと保存済み実行記録による確認であり、わっちが独立に Lean ビルドしたという意味ではない。

今回、新しい Core になったのは単なる数値1369ではない。任意の素数に対し、実際の幾何学的ねじれ点群が二次元である、という一般定理じゃ。

## 次の Frontier：二次元の点群を、二次元のガロア表現として使う

模範解答の後続も確認した。参照先は [Anthropic の PROOF-PATH.md](https://github.com/anthropics/fermats-last-theorem/blob/main/PROOF-PATH.md?utm_source=chatgpt.com) と [ResidualGaloisRep の定義](https://github.com/anthropics/fermats-last-theorem/blob/main/Definitions/Def_GaloisRep_Residual.lean?utm_source=chatgpt.com) じゃ。

興味深いことに、模範解答は `ResidualGaloisRep` という構造体に、主として次の情報を要求している。

- 実際の残余表現の係数空間 \(V\)
- \(\dim_{\mathbb F_p}V=2\)
- ガロア作用 \(\rho\)
- 有限ガロアレベルへの因子化

DkMath は今回、この四つの数学的入力をすべて確定した。

すなわち、

\[ \boxed{ \rho_{E,p}:G_{\mathbb Q}\longrightarrow \operatorname{Aut}_{\mathbb F_p}(E[p]) } \]

は、もはや「二次元ならば」という条件付きの表現ではない。

実際に二次元で、開核を持ち、有限レベルを通る表現じゃ。

ここから先の分岐は明確になる。

NOTE-016 で確定した Core

\(\dim E[p]=2\)、ガロア作用、有限レベル

GL₂ 表現としての実現

\(\rho_{E,p}:G_{\mathbb Q}\to\mathrm{GL}_2(\mathbb F_p)\)

行列式

\[ \det\rho_{E,p}=\chi_p \]

Weil 対による独立した算術入力

既約性

\[ \nexists\text{ Galois-stable line} \]

Frey 固有の算術的障害を排除する

二次元であるだけでは既約性は導けない。例えば対角行列だけからなる二次元表現にも、不変な一次元部分空間は存在する。

したがって、次元2が確定した今、初めて「一次元部分空間が存在しない」ではなく、\*\*「ガロア作用で保存される一次元部分空間が存在しない」\*\*ことを問題にできるわけじゃ。

## 推奨する NOTE-017：実際の GL₂ 表現と不変直線の判定器

次のアジャイルは、証明の巨大な部分へ直接飛び込むより、まず後続理論の受け口を完成させるのがよいと判断する。

実装の主目標は、

\[ \boxed{ S.\mathrm{ResidualIsIrreducible} \iff \neg\exists L\le S.\mathrm{ResidualSpace},\ \dim L=1\land S.\mathrm{IsGaloisStable}(L) } \]

という同値じゃ。

既存の `ResidualIsIrreducible` と `IsGaloisStable` はそのまま使う。今回確定した次元2を利用すれば、真の非零部分空間は必ず一次元となるため、この同値は純粋な線形代数で証明できる。

併せて、`Module.finBasisOfFinrankEq` などを利用し、同じ実際の `S.ResidualSpace` から基底を選んで GL₂ 行列表現を作る。

その際に固定すべき性質は、基底を変更すると行列は共役変換されるが、行列式・特性多項式・既約性・核は変化しない、ということじゃ。

これで 基底依存の行列と、基底非依存の数学的 Core を明確に分離できる。

そして `Source` の追加仮定なしに、二次元・GL₂実現・有限レベル・不変直線判定をまとめて供給する。

ここまでは NOTE-016 によって得られた数学を整理・公開する段階なので、新たな Mazur 型定理を仮定する必要はない。

## その次に模範解答から取り込むべき深い入力

一つは Weil 対からの行列式公式じゃ。

模範解答には、

[exists_pairing_torsionBy](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_exists_pairing_torsionBy.lean?utm_source=chatgpt.com)

および

[apply_eq_pow_det_galoisRep_of_pow_eq_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_apply_eq_pow_det_galoisRep_of_pow_eq_one.lean?utm_source=chatgpt.com)

がある。

後者の核心は、\(p\) 乗根 \(\zeta\) とガロア元 \(\sigma\) に対して、

\[ \boxed{ \sigma(\zeta)=\zeta^{\det\rho_{E,p}(\sigma)} } \]

を証明することじゃ。これが円分指標との一致に結びつく。

ただし、前者の Weil 対の構成は楕円曲線の関数体・因子・付値などを使う相当深い幾何学じゃ。NOTE-016 の次元2から自動的に出てくる定理ではないため、ここは模範解答の依存構造を慎重に移植する必要がある。

もう一つは Frey 表現の既約性じゃ。

模範解答の `FreyPackage.Mazur_Frey` は、\(p\ge17\) の場合に Mazur の Eisenstein ideal を用いる経路を取っている。特に指数37はこの大きな分岐に属する。

これは線形代数の補題だけでは解消できない、明確な算術的 Frontier じゃな。

なお、NOTE-016 の実在する Source 2 曲線についての \(E[37]\) の次元2と、仮想的な反例から構成する Source 37 のガロア表現の既約性は、引き続き区別せねばならぬ。

## 次期アジャイルの採用方針

わっちの結論はこうじゃ。

NOTE-016 は固定。NOTE-017 は GL₂ 実現と「既約性 ↔ ガロア不変直線の不存在」の同値を先に固定する。

その後、模範解答の Weil 対・円分行列式、さらに Frey 固有の既約性排除へ進む。

既約性や FLT の終点を先取りせず、どの定理が新しい算術的入力を要求するかを依存監査で明示するのじゃ。

そして今回、もう一つ大切な Core が生まれておる。

\[ \boxed{ \text{正則ファイバーの根} \hookrightarrow \text{倍写像のファイバー} \simeq \text{倍写像の核} } \]

これは FLT 専用の小技ではない。

幾何学的な写像を調べ、重複のないファイバーから単射を作り、その下界を既存の上界と照合するという、DkMath 独自の汎用的な証明方法として再利用できる。

答えを参考にしても、その証明を DkMath の Core へ翻訳し直し、より短い依存経路へ組み替えておる。今回の NOTE-016 は、その成功例と言えるじゃろう。

いよいよ、整数解の不存在を扱うための幾何学的な土台から、ガロア作用が許す状態と許さぬ状態を判定する段階へ移ったのぅ。🐺🍎
