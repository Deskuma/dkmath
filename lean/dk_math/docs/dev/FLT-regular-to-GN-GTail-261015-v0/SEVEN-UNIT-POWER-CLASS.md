# FLT7 第三段：単元そのものから七乗剰余類の比較へ

2026-10-16。[共役位相の固定](SEVEN-CONJUGATE-PHASE.md) に続き、
同じ非零因子の二つの冪分解を比較する原理を公開 API にした。
提案どおり、単元や冪根を同じ元と証明する必要はない。
ただし、分岐因子の代表元を変える単元は、剰余類に残して比較する。

今回の実装には三つの層がある。

1. 一般の整閉整域に対する根の対応・単元冪剰余類・冪根の輸送。
2. GN の同じ一次単元の七乗性を使った、具体的六次環での比較。
3. 現在の carrier の実際の receiver を使う、source 等式を入力とした接続。

3 の source 等式は今回構成していない。FLT7 の降下や矛盾も結論しない。

## 1. 比較原理と同じ証人の向き

整閉整域 R、正の指数 n、非零の A と λ について

\[
A=\lambda\varepsilon\beta^n=\lambda\delta\gamma^n,
\qquad\varepsilon,\delta\in R^\times
\]

とする。λ を消すと、`βⁿ` と `γⁿ` は同伴になる。
Mathlib の `Associated.pow_iff` により、元の根も同伴である。
向きを選んで

\[
\boxed{\beta=t\gamma,\qquad\delta=\varepsilon t^n}
\]

となる同じ単元 t を得る。
`exists_root_and_unit_correction` は、この二つの等式を同じ証人で返す。
δ と ε の順序を入れ替えれば、対応する補正は t の逆元になる。

Dedekind 整域のイデアル分解による提案の証明も正しい。
今回の API はそれより弱い **整閉整域** の仮定で構成しており、PID 性、
類群の正則性、元の一意分解性をこの比較のためには要求しない。
指数は素数でなくてもよい。n≠0 を明示し、n=3,5,7,11,13 にも共通に使える。

## 2. 実際の単元商群へ接続する

既存の `PowerSubgroup` は、単元群の n 乗の像を

```lean
unitPowerSubgroup R n : Subgroup Rˣ
```

として持つ。今回の

```lean
sameUnitPowerClass_iff_quotient_eq
```

は、具体的な証人を持つ関係

```text
SameUnitPowerClass n ε δ := ∃ t : Rˣ, ε = δ*t^n
```

と、実際の商群 `Rˣ ⧸ unitPowerSubgroup R n` の等式を同値にする。
これにより固定した非零分解から

\[
\boxed{[\varepsilon]=[\delta]}
\]

を得る。さらに `δ=κⁿ` があれば、比較の証人 s を使って
`ε=(κs)ⁿ` を構成できる。
`exists_unit_pow_of_fixed_extraction` がこの輸送をまとめる。

A≠0 は省略しない。A=0、β=γ=0 なら任意の単元が同じ等式を満たし、
剰余類は決まらない。テストでは有限体 ZMod 29 上でこの反例を検証した。

## 3. 既存 API をどう整理したか

この独立性の中核は、既存の
`DkMath.NumberTheory.GapFocusing.UnitGauge` に既にあった。
その中立部分を `DkMath.Lib.Algebra.UnitPowerClass` へ移し、研究固有の依存なしで
再利用できるようにした。既存の研究名前空間は互換 wrapper として保持する。

今回追加したのは、実際の商群との同値、同じ証人による根・単元補正、
片側の冪性の輸送、および GN・現在の receiver への接続である。
独立性の中核自体を新しい数学的発見として数えていない。

## 4. 分岐因子が単元倍だけ違う場合

比較する表示が

\[
A=\lambda\varepsilon\beta^n=(w\lambda)\delta\gamma^n
\]

なら、固定した λ に揃えた比較先は `wδ` である。
従って正しい結論は

\[
\boxed{[\varepsilon]=[w\delta]=[w][\delta]}
\]

となる。`sameUnitPowerClass_of_rescaled_extraction` がこの形を扱う。
`[δ]=1` でも、`[ε]=1` となるためには w の補正を消す根拠が必要である。
これは比較原理の欠陥ではなく、比較する分岐因子の代表元を固定するという条件の意味である。

## 5. 今回の GN と現在の carrier で実際に起きる補正

前章の GN の表示は

\[
A=(\zeta^i-1)\delta_i\gamma_i^7,
\qquad\delta_i=\kappa_i^7.
\]

現在の carrier は `ramifiedUniformizer=1−ζ` を使う。一方で

\[
\zeta^i-1=-(1-\zeta)S_i,
\quad S_i=1+\zeta+\cdots+\zeta^{i-1}.
\]

従って、現在の分岐因子に揃えた GN 側の単元は **−Sᵢ·δᵢ** である。
`GNRamifierTwist` は、この −Sᵢ を具体的六次環の単元として保持する。
`GNRamifierTwist_spec` と `GNPhaseFactor_decomposition` が、符号も含む元の等式を証明する。

同じ非零 source A の別の表示 `A=(1−ζ)εβ⁷` に対し、
`unit_class_of_GN_source` は

\[
\boxed{[\varepsilon]=[-S_i]}
\]

を返す。ここでは前章の `GN_primary_unit_seventh` を実際に適用し、
**同じ Q の** δᵢ の剰余類を消している。

この結論から、一般位相でも

\[
\boxed{\varepsilon(-S_i)^{-1}=k^7}
\]

と復元できる。`unit_seventh_after_twist_of_GN_source` はこの根を返す。
既知の円分単元による補正を残したまま、未解析単元を取り除ける。
ε 自身を七乗としたい場合は、−Sᵢ も七乗であることが必要であり、
`unit_seventh_of_GN_source` はその仮定を明示して受け取る。

| 分岐因子の規約 | 比較で得る結論 |
|---|---|
| 両側とも同じ λ、GN 側の単元が δᵢ | `[ε]=[δᵢ]=1` |
| 現在の λ=1−ζ、GN 側は ζⁱ−1 | `[ε]=[−Sᵢ]` |
| 上の補正を除いた単元 | `ε·(−Sᵢ)⁻¹=k⁷` |

## 6. 第1位相と第2位相の具体的な差

第1位相では S₁=1。`GNRamifierTwist_one` は補正が −1 と証明する。
−1 は自分自身の七乗なので、この位相では ε 自身の七乗性を移せる。

第2位相では補正は `−(1+ζ)`。今回、この単元は **実際に七乗ではない** ことも証明した。
その二次相対ノルムは

\[
N(-(1+\zeta))=1+(\alpha-1)+1=1+\alpha.
\]

既存の実三次単元 `alphaAddOneUnit` の射影対数は `(2,5)`。
もし補正が七乗なら、そのノルムも単元の七乗になり、対数は `(0,0)` となるはずで、矛盾する。

```lean
GNRamifierTwist_two_norm
GNRamifierTwist_two_not_seventh
```

がこの二段階を証明する。これは一般位相の分岐因子の補正を省略できない具体例である。
第2位相が現在の反例パケットで実現することや、その位相を排除できたことを主張するものではない。

## 7. 現在の carrier への条件付き接続

`currentCarrier_unit_class_of_GN_source` は、実際の
`currentCarrier_ramified_element_receiver` から単元 ε と根 β を取り出す。
非零性は、現在の carrier が分岐素イデアルの二乗に属さないという既存定理から供給する。
元の `Fermat7Equation` も保持する。

追加の対応条件は

```text
currentLinearCarrier c = GNPhaseFactor x u i
```

という **同じ環内の source の等式** である。
これを入力にして、上の `[ε]=[−Sᵢ]` を、実際の receiver の単元に証明する。
根 β を GN の生成元と同一視したり、ε=δᵢ を要求したりしない。

この等式の構成は依然として未完である。現在の source は

\[
\operatorname{ofReal}(\operatorname{rotate}(\rho))-
\zeta^j\operatorname{ofReal}(\rho)
\]

という実三次整数を係数に持つ因子であり、通常の GN 一次パケットは整数 x,u を係数に持つ。
同じ六次環に住むことや、等しいノルムだけでは source の等式を結論できない。

今回、必要な対応条件は「単元そのものの同一性」から、
「source の元の等式と、既知の分岐因子補正」へ整理された。
その対応を供給する段階と、反復可能な降下を構成する段階は、引き続き独立の課題である。

## 8. ファイルと検証

- `DkMath/Lib/Algebra/UnitPowerClass.lean`: 一般の比較原理と実際の商群。
- `DkMath/NumberTheory/GapFocusing/UnitGauge.lean`: 旧名前空間の互換 API。
- `DkMath/FLT/Kummer/SevenUnitPowerClassBridge.lean`: 同じ GN 因子、分岐因子補正、第2位相の非七乗性、現在の receiver。
- `DkMathTest/FLT/Kummer/SevenUnitPowerClassBridge.lean`: 根の補正、商、冪根輸送、A=0 と異なる分岐因子の反例、位相1・2、全公開宣言の公理 whitelist。
- `DkMathTest/FLT/Kummer/SevenUnitPowerClassDependencyAudit.lean`: 型・opaque 本体・構築子を辿り、現在の receiver・GN 単元根・Lib 比較補題の実使用を確認。

公開入口は `DkMath.Lib` と `DkMath.FLT.Kummer`。
実行した検証の範囲は [検証記録](evidence/validation-seven-unit-power-class.txt) に残す。
