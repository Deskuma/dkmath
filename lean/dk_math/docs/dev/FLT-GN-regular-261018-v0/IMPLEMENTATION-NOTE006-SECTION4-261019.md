# NOTE-006 §4 / IRR-007 実装報告

日付: 2026-10-19。対象は NOTE-006 §4 の二つの次期研究項目。
§3 の Legendre–Frey 接続は既存実装を保持し、今回は軌道ノルムと奇素数の局所還元を追加した。

## 1. IRR-007: 全位相積を固定点と非零軌道へ分解する

`DkMath.Lib.NumberTheory.GaloisPhaseOrbitNorm` は一般素数 p について、

- `nonzeroPhaseEquiv`: `(ZMod p)ˣ ≃ {i : Fin p // i ≠ 0}`。
- `exists_phaseMul_one`: 非零位相 i は一意な a により `phaseMul a 1` と表される。
- `prod_eq_zero_mul_orbit`: 全位相積は位相0と、この単元群で数えた非零位相積の積。
- `zero_mul_orbit_norm`: 同変性と全積1から `ω₀ * ∏ a, σₐ(ω₁) = 1`。

を証明する。有限リストの重複を許す全射ではなく、本当の同値による再索引である。

`CyclotomicPhaseGalois.orbitNorm` は既存の真の円分体ガロア自己同型 `sigma` と
`ClassGroup.mulEquiv` による類群の積である。乗法保存・ガロア固定性・p-torsion の保存も証明した。
体の元の `Algebra.norm` と同一の型ではなく、類群に作用する全ガロア共役の積を意味する。

`zero_mul_orbitNorm` は実際の円分整数環上で整数係数の族に適用する。
`obstruction_int` を消費するので、λ の単元補正、イデアル根の写像、根の選択独立性は
IRR-006 の証明を通る。正則性や類群の p-torsion-free 条件は使わない。

37次の公開終点は `IrregularPrime37.observe_orbit_norm`。
入力は既存の `RegularDescent.State phase37 (m+1)` と、x=A, y=B が整数に由来する証拠である。
`observe_galois` と `product_obstruction_one` の合成により、

\[
  (\operatorname{observe}E).\omega_0\,
  N((\operatorname{observe}E).\omega_1)=1
\]

を得る。`observe_zero_fixed` も同じ整数座標の前提を保持する。
座標・原始性・分岐条件・記録済みイデアル根を変更せず、新たな37固有の類群算術を導入しない。

## 2. Frey: 単元 c₄ から最小性へ

`DkMath.Lib.NumberTheory.FreyLocalReduction` は Mathlib の正式な
`WeierstrassCurve.IsMinimal`、`HasGoodReduction`、`HasMultiplicativeReduction` を証明する。
新しい還元型の代理述語は設けていない。

一般の離散付値環 R とその分数体 K で、整モデル W の c₄ が単元とする。
任意の座標変換 C による整な競合モデル W′ について、

\[
 c_4(W')=u^{-4}c_4(W),\qquad \Delta(W')=u^{-12}\Delta(W).
\]

乗法的付値を v とすると、整性から `v(c₄(W′)) ≤ 1`、単元性から `v(c₄(W))=1`。
従って `v(u⁻¹)^4 ≤ 1`、すなわち `v(u⁻¹) ≤ 1` となり、
`v(Δ(W′)) ≤ v(Δ(W))` を得る。この全競合モデルに対する比較が最小性である。
加法的付値では不等号の意味が逆になり、最小判別式付値が最小となる。

- `isMinimal_of_isUnit_c4`: この比較による最小性。
- `hasMultiplicativeReduction_of_c4`: 加えて Δ が極大イデアルに入ると乗法的還元。
- `isMinimal_of_isUnit_discriminant` / `hasGoodReduction_of_isUnit_discriminant`:
  単元 Δ の別の経路から最小性と良還元を得る。良還元に c₄ の単元性は不要。

## 3. 整数モデルから同じ有理曲線へ

`primeIdeal ℓ = (ℓ)`、`LocalRing ℓ = Localization.AtPrime (primeIdeal ℓ)` を構成した。
これは ℤ_(ℓ) であり、完備化ではない。実際のℚへの標準埋め込み、整数からの写像の可換性、
同じℚがその分数体であることを供給した。整数 n の ℓ-非可除性と局所環の単元性、
可除性と極大イデアル所属の対応を使い、一般の最小性・還元定理を整数モデルへ輸送する。

既存の `DkMath.FLT.Frey.Source p` に対し、`0 < p`、素数 ℓ、`ℓ ≠ 2` の下で:

| 公開定理 | 結論 |
| --- | --- |
| `Source.hasMultiplicativeReduction` | ℓ∣abc なら、元の `rationalCurve` が乗法的還元を持つ |
| `Source.hasGoodReduction` | ℓ∤abc なら、同じ有理モデルが良還元を持つ |
| `Source.isMinimal_at_odd_prime` | 同じモデルが全ての奇素数で最小 |
| `Source.good_or_multiplicative` | 奇素数で良還元または乗法的還元 |
| `Source.hasMultiplicativeReduction_iff` | 乗法的還元の支持は正確に abc の奇素因子支持 |
| `Source.minimal_discriminant_valuation` | 最小性と `vℓ(Δ)=2p vℓ(abc)` |
| `Source.minimal_discriminant_exponent_dvd` | 最小性と `p ∣ vℓ(Δ)` を同じ有理モデルで束ねる |

`Source.curve_map` を使うので、整数除算の正当化は既存の `IntegralNormalization` を通る。
原始性・非零性・元の冪和等式は `Source` に保持される。ℓ=p もこの局所算術の範囲に含まれる。

## 4. 回帰例と依存監査

- 非零37位相の個数36、位相36への一意な作用、−1による位相1→36。
- 真の37次円分体の類群上のノルム固定性・torsion 保存・仮想 State のノルム式。
- 抽象群 `Multiplicative (ZMod 37)` の定数族: 恒等作用に関する同変性と全積1があっても各項は1とは限らない。
  これは実際の37次類群の非自明な類の構成ではない。
- 実在する p=1 解 `3+16=19` のモデル `[1,3,0,-3,0]`: Δ=3249, c₄=313。
  3・19で乗法的還元、5・313で良還元。313は c₄ を割るため、良還元の別経路も検査する。
- p=ℓ=37 の条件付き局所還元、最小判別式付値、p倍性。

`SectionFourDependencyAudit` は追加した公開35宣言の公理を検査し、主要7経路について
型・opaque 証明項を含む実依存の推移閉包を検査する。円分体の作用と全位相積、
実際の局所化・座標変換・Mathlib の最小性／還元型が証明経路に含まれることを要求する。
外部 FLT 終点、全域的な正則性供給、未証明の公理への依存を禁止する。

公開入口は `DkMath.Lib`、`DkMath.FLT.Kummer`、`DkMath.FLT` とルート `DkMath`。
回帰例・監査は `DkMathTest.lean` にも接続した。全新規 Lean ファイルは import 後に
`#print "file: モジュール名"` を置く。

検証コマンドと結果は [検証証跡](evidence/validation-note006-section4.txt) に記録した。
focused build（8,998 jobs）、公開入口と全テストの build（11,501 jobs）、
ルート smoke、`DkMathTest.lean` の直接検査は全て成功した。
追加35宣言の使用公理は `propext`・`Classical.choice`・`Quot.sound` の範囲内である。

## 5. 残る数学的境界

本実装は §4 が優先項目として挙げた軌道ノルムと奇素数の局所還元を扱う。
37-primary 類群の指標成分の分類、Herbrand–Ribet、非自明な37-torsion の具体的供給は含まない。
ノルム式から個々の障害の消滅や FLT37 の閉包を推論していない。

Frey 側の未実装境界は素数2での最小性・還元型、任意の整数反例の向き付け、
p-torsion ガロア表現の構成・不分岐性・有限平坦性、モジュラー性とレベル降下である。
奇素数での半安定性を、全素数での半安定性と同一視しない。
円分体ガロア群の類群作用と、絶対ガロア群の楕円曲線 p-torsion 作用の直接同一視も行わない。
