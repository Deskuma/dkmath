# NOTE-007 §5 教科書実装報告

日付: 2026-10-19。§5 の優先順に、イデアルノルム、素数2の局所モデル、中央席の j、
指標成分への構造的入口を実装した。本文の既存成果のレビューは歴史的記録として保持した。

## 1. 到達範囲

| §5 の項目 | 今回証明した内容 | 残る境界 |
| --- | --- | --- |
| IRR-008 | 共役イデアル積=(絶対ノルム)、`orbitNorm_eq_one`、37次位相0の障害除去 | 非零位相の全消滅・FLT37 |
| Frey の2の局所モデル | 2での最小性、p≥5での乗法的還元、全素数での半安定性と還元型の支持 | Artin 導手の構成と導手指数への接続 |
| Legendre の j | 実際の j の有理公式と、旧支持を保持する良還元時の j=0 | 新素因子の存在、full-cover 排除 |
| 37-primary 指標 | 真の類群上の指標部分群、自明指標の消滅、固定 p-primary 類の消滅 | 非自明指標への実際の所属、次元、直和分解・Herbrand–Ribet |

## 2. イデアルノルムを類群へ運ぶ

`DkMath.Lib.NumberTheory.GaloisIdealNorm` は、任意の有限ガロア数体 K/ℚ と
非零整数イデアル I について、

\[
 \prod_{\sigma\in\operatorname{Gal}(K/\mathbb Q)}\sigma(I)
   =(N(I))\subseteq\mathcal O_K
\]

を証明する。円分体・正則素数に限定した仮定は使わない。

証明の教科書的な経路は次の通り。

1. 元ノルム `intNorm_eq_prod`: `N(x)=∏σ σ(x)` を体から実際の整数環へ戻す。
2. `map_relNorm_le_prod`: x∈I なら共役元の積は共役イデアルの積に入る。
   元ノルムが生成する相対ノルムイデアルを拡張すると、共役積への包含を得る。
3. 各自己同型は絶対ノルムを保存するので、共役イデアル積のノルムは `N(I)^[K:ℚ]`。
   主イデアル `(N(I))` の絶対ノルムも同じ値となる。
4. 包含をイデアルの可除性へ変え、差の因子のノルムが1であることから、その因子は単位イデアル。
   従って包含は等式となる。分岐指数ごとの場合分けは不要。
5. `classGroup_prod_eq_one`: 非零整数イデアルの代表を選び、この主イデアル等式を類群へ写す。

`DkMath.Lib.NumberTheory.CyclotomicClassNorm` は、真のガロア群と `(ZMod p)ˣ` の同型で
この積を再索引する。既存の `orbitNorm` を変更せず、任意の類 w に対し
`CyclotomicPhaseGalois.orbitNorm_eq_one : orbitNorm w = 1` を得た。

## 3. 37次の位相0だけを除去する

`DkMath.FLT.Kummer.IrregularNorm37` の入力は、従来と同じ
`RegularDescent.State phase37 (m+1)` と、x,y が整数 A,B に由来する証拠である。

- `observe_zero_obstruction_eq_one`: `ω₀N(ω₁)=1` に `N(ω₁)=1` を代入して `ω₀=1`。
- `observe_zero_root_principal`: 記録済みの同じ位相0イデアル根が主イデアル。
- `observe_zero_unit_generator`: その根の生成元 b と単元 u を保持し、位相0の因子を `u*b^37` として復元。
- `observe_nonzero_trivial_iff`: 各非零位相の障害が自明であることは、位相1の障害の自明性と同値。
- `observe_nontrivial_moves`: 非自明な位相1障害には、それを動かす真のガロア自己同型が存在する。

全域的な正則性や単元の37乗化条件は供給していない。単元 u を消して b の37乗とみなすこともない。
State の座標・原始性・分岐情報、既存のイデアル根の選択は全て保持する。
整数座標の前提が必要なのは、同じ族内での位相再索引と位相0の除去である。
任意の類への `orbitNorm_eq_one` 自体はこの座標前提を必要としない。

## 4. 素数2と全素数での半安定性

`DkMath.Lib.NumberTheory.FreyTwoArithmetic` は分母条件
`IntegralNormalization A B` から c₄ の奇数性を証明する。
4∣B−A−1 により A,B の偶奇が異なるため、`c₄=A²+AB+B²` は奇数となる。
この補題は冪和・原始性・指数を仮定しない。

`DkMath.FLT.FreyTwo` は同じ `Source p`、同じ整数モデルと有理モデルを使う。
2での c₄ 単元性を既存の一般 DVR 最小性定理へ渡すことで、`isMinimal_at_two` を得る。
判別式の付値は整数値で、

\[
 v_2(\Delta_{\min})=2p\,v_2(abc)-8
\]

となる。自然数の切り捨て減算に置き換えず、256の分母補正を保持する。
さらに、分母条件16∣a^p b^pと非零積から `v₂(abc)≥1`。
p≥5 なら `v₂(Δ_min)≥2` なので `hasMultiplicativeReduction_at_two` が成立する。

`0<p` の下で、従来の奇素数 API と合成した公開定理は:

- `isMinimal_every_prime`: 全素数で同じ有理モデルが最小。
- `good_or_multiplicative_every_prime`: 全素数で良還元または乗法的還元。
- `multiplicative_support_iff`（p≥5）: 全素数について乗法的還元 iff ℓ∣abc。

2での p倍性の境界も等式で記録した。
`exponent_dvd_two_valuation_iff` は `p∣v₂(Δ_min) ↔ p∣8` を証明する。
特に37次では、奇素数で得た p倍性を2へ延長できない。

ここで得たのは Mathlib の正式な最小性・還元型とその支持である。
調査した `Mathlib/AlgebraicGeometry/EllipticCurve` の還元 API には、Artin 導手への接続はない。
還元型から0/1を返す数を独自に定義して、導手の証明を代用する実装は追加していない。
任意の反例の向き付け・mod-p 表現・導手指数・モジュラー性・レベル降下は引き続き別の理論である。

## 5. 中央席の真の j と旧支持

`DkMath.NumberTheory.Legendre.FreyJCentralSeat` は、`n>0` の非特異性を供給した上で
Mathlib の `WeierstrassCurve.j` を使う `rationalJ` を定義し、

\[
 j(E_n)=256\frac{(n^2+n+1)^3}{n^2(n+1)^2}
\]

を証明する。剰余曲線についても既存の非特異性を先に供給した `reductionJ` を使い、
`q∣Qₙ` なら `reductionJ=0` を得る。
`j_bridge_of_mem_support` は旧支持の q≤n と、q=3 または q≡1 mod3 を同時に保持する。

回帰例は有理値 j(E₁)=1728、j(E₂)=21952/9、例外素数3、旧支持内の n=18,q=7。
この j=0 は還元後の曲線の性質であり、元の有理曲線の複素乗法を導くものではない。

## 6. 指標成分の入口と残る分類

`characterComponent χ` は実際の類群における次の部分群である。

\[
 w^p=1,\qquad \sigma_a(w)=w^{\widetilde{\chi(a)}}.
\]

ここでは剰余体の標準代表を冪に使う。定義が扱うのは指数 p の部分である。
別に `fixed_p_primary_eq_one` は、任意の r について `w^(p^r)=1` かつ全ガロア固定なら w=1 を証明する。
固定性から全共役積は `w^(p−1)` となり、位数が互いに素な p^r と p−1 の両方を割るからである。
`trivial_characterComponent` はこの構造を自明指標成分の零化として記録する。

非自明な位相障害が存在すれば、固定成分に属さないという制約が得られる。
どの非自明指標に属するか、非零成分の次元、全体の直和分解、Bernoulli 証明書との結合は未実装。
非自明な37-primary類の存在を、この構造的結果から推論していない。

## 7. 検証・公開入口

追加した公開34宣言を `Note007DependencyAudit` で公理監査し、主要10経路の型と
opaque 本体を含む実依存を検査する。元ノルム・相対イデアルノルム・類群の実際の写像、
同じ根の単元付き復元、正式な最小性・還元型、実際の j を要求する。
外部 FLT 終点や全域的な正則性供給を使う経路は拒否する。

公開入口は `DkMath.Lib`、`DkMath.FLT.Kummer`、`DkMath.FLT`、`DkMath.NumberTheory.Legendre` とルート `DkMath`。
回帰例と監査は `DkMathTest.lean` にも接続した。新規10モジュールと root smoke の import 後には
指定形式の `#print "file: モジュール名"` を置いた。

検証のコマンドと結果は [検証証跡](evidence/validation-note007.txt) に記録した。
focused build（9,013 jobs）、全体 build（11,511 jobs）、ルート smoke、
`DkMathTest.lean` の直接検査は全て成功した。回帰例は21件。
追加34宣言の使用公理は `propext`・`Classical.choice`・`Quot.sound` の範囲内である。
