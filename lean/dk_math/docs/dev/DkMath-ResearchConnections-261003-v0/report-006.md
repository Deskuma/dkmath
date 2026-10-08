# DRC-006 — TraceOne residue-type classification

## Outcome A

二次関係 `ω² = a + bω` の根による再利用可能な三分類を実装した。
`Split a b` は異なる二根、`Inert a b` は根なし、`Ramified a b` は唯一の根を意味する。
体上のモニック二次関係についての因子型の分類であり、加法群や要素数による分類ではない。

作業開始時: branch `research/DkMath-ResearchConnections-261003-v0`、HEAD `b65289ad7`、作業ツリーは clean。
Lean / Mathlib v4.34.1 を使用。

## Audit and representation

- `DkMath.NumberTheory.TraceOneQuadratic` の既存キャリア、乗法 `τ²=s+τ`、signed discriminant `discr s = 1+4*s` を再利用した。
- `DkMath.Tromino.IntegralMod2Bridge` は既に Gaussian / Eisenstein の座標還元と異なる mod-2 乗法を保持している。Gaussian 側は `Zsqrtd (-1)` の `i²=-1` に対応する。
- Mathlib `QuadraticAlgebra.Defs/Basic/Discriminant` のキャリア `QuadraticAlgebra K a b`、乗法、根なしの場合の Field instance、既存 `discr a b = b²+4a` を採用した。
- Mathlib `QuadraticDiscriminant` の `discrim_eq_zero_iff` を用いて重根判定を導いた。独自の判別式定義は追加していない。
- `ZMod` の素数体と `fin_cases` による有限根検査を使用した。
- quotient / polynomial 側も調査した。`QuadraticAlgebra` の二次関係を直接使う形が最小であり、quotient の新規構築や多項式既約性 API の重複実装は不要だった。
- Mathlib の `QuadraticAlgebra.equivProd` は型の equivalence であり、積環への同型としては使用していない。

## Exact public endpoints

`DkMath.Lib.NumberTheory.QuadraticResidueType`:

- `split_iff_discr`: `Split a b ↔ IsSquare (QuadraticAlgebra.discr a b) ∧ discr a b ≠ 0`。
- `inert_iff_discr`: `Inert a b ↔ ¬ IsSquare (discr a b)`。
- `ramified_iff_discr`: `Ramified a b ↔ discr a b = 0`。
- 上記は任意の体、仮定 `[NeZero (2 : K)]` の下で成立する。
- `classification` は三種類の網羅性、`exclusive` は相互排他性を証明する。
- `inert_iff_isField` はこの根なし条件と実際の二次代数の `IsField` を結ぶ。
- `traceOne_mod_two_split`: `(a,b)=(0,1)` の二根は `0,1`。
- `traceOne_mod_two_inert`: `(a,b)=(1,1)` は根なし。
- `traceOne_mod_two_isField`: この mod-2 inert 二次代数は実際に体。
- `gaussian_mod_two_ramified`: `(a,b)=(-1,0)` は唯一の根 `1`。
- `gaussian_mod_two_nilpotent`: この Gaussian モデルの `e=(1,1)` は `e≠0` かつ `e²=0`。`e=1+i` が dual-number 型の平方零方向を与える。

`DkMath.NumberTheory.TraceOneResidueType`:

- `residueMap s q`: 既存 `TraceOneInt s` から `QuadraticAlgebra (ZMod q) s 1` への座標還元を環準同型として定義。
- `residueMap_surjective`: 全ての剰余座標対を得る。
- `residue_discr`: 既存 integral discriminant の還元と Mathlib 判別式が一致する。
- `split_of_even`, `inert_of_odd`, `mod_two_dichotomy`: 任意の整数 `s` の偶奇を二種類へ結ぶ。負の整数も含む。
- `odd_prime_classification`: `[Fact q.Prime] [NeZero (2 : ZMod q)]` の下で、既存 `discr s` の剰余を用いた split / inert / ramified の三判定をまとめる。

一般層は `DkMath.Lib`、TraceOne 層は `DkMath`、回帰は `DkMathTest` の public import に追加した。

## Model scope

要求で許容されている因子型に相当する根分類を選んだ。
Gaussian モデルは二次代数の乗法と非零平方零元まで検証した。
積環、有限拡大体、dual-number quotient への明示的な ring equivalence は今回の endpoint に含めていない。
加法同型や判別式の一致だけから環同型を主張していない。

## Validation

- `lake build DkMath.NumberTheory.TraceOneResidueType`: 成功。
- `lake build DkMathTest.NumberTheory.QuadraticResidueType`: 成功、1742 jobs。
- 回帰: mod 2 の負の偶数・奇数パラメータ、Gaussian ramified、mod 3 の split / inert / ramified を kernel-check。
- `#print axioms`: 判別式の三判定、網羅性、排他性、体条件、平方零元、環準同型、全射性、偶奇分類、奇素数分類を監査。依存は標準の `propext`, `Classical.choice`, `Quot.sound` の範囲。
- 通常の `lake build`: 成功、10342 jobs。
- `lake build DkMathTest`: 成功、10931 jobs。新規回帰を public test facade 経由でも検証。
- 新規 Lean ソースの `sorry` / `admit` / `axiom` / `unsafe` 検索: 該当なし。
- tracked diff と新規ファイルの whitespace check: 成功。

Focused / full build logs: `/tmp/drc-006-focused.log`, `/tmp/drc-006-full.log`, `/tmp/drc-006-test-facade.log`。
