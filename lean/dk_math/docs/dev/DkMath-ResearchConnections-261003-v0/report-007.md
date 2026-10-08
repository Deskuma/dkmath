# DRC-007 — Cyclotomic QR provenance lift

## Outcome A

既存の `PrimeTraceOneCoordinatePacket` から、実際の QR 積を選ぶ二次元の
quadratic subfield embedding、共役の QNR 積、相対ノルム、整数環への写像、
主イデアル輸送を実装した。所有権 cutoff は既存の仮定を保った条件付き接続を得た。

開始時: branch `research/DkMath-ResearchConnections-261003-v0`、HEAD `449cb1c83`、
作業ツリー clean。Lean / Mathlib v4.34.1。

## Audit and source packet

調査した主要 owner:

- `CyclotomicQRProduct`, `CyclotomicQRGaloisAction`: QR/QNR 集合、積、和 `Rpoly`、差 `Dpoly`。
- `CyclotomicQRGaussNormalization`: 選んだ primitive root による `quadraticGauss`、
  signed discriminant の平方関係、QR/QNR の Galois 符号作用。
- `CyclotomicQRTraceOneBridge`: integral Gauss-form、半座標抽出、
  `PrimeTraceOneCoordinatePacket` とその存在定理。
- `TraceOneQuadraticField`: 既存 `TraceOneRat`、`traceOneRatHom`、単射性、
  signed prime parameter における Field 構造。
- `CyclotomicQRUniversalTransport`, `CyclotomicQRUniversalTraceOneAnchor`:
  universal carrier と root-specialization、RZ anchor。
- `PrimeCyclotomicTraceOne`, `CFBRC.CyclotomicIdeal`: 既存の scalar compatibility。
- `Lib.NumberTheory.ConjugatePrimeIdealOwnership`: 共役 ownership と cutoff の一般輸送。
- `PrimeTraceOneDirectCyclotomicIdealOwnership`,
  `SevenRamifiedFusionOrientedCarrierValuationOwnership`: 現行次数六 carrier と
  oriented ownership の個別 endpoint。
- Mathlib `QuadraticAlgebra.lift`, `AlgHom.fieldRange/equivFieldRange`,
  `QuadraticAlgebra.det_toLinearMap_eq_norm`, `Algebra.norm_eq_of_algEquiv`,
  `NumberField.RingOfIntegers`, `Ideal.map_span` を再利用した。

元を識別するために使用した packet fields は以下の三つ:

1. `map_RZ`: RZ の像は `QR + QNR`。
2. `gauss_difference`: `G * SZ` の像は `QR - QNR`。
3. `half_relation`: `RZ = 2*AZ + SZ`。

`norm_eq` は元の識別には使わず、相対ノルムの値を与える後続定理に使った。
古い existential coordinate API のノルム等式だけからは、今回の元の識別はできない。
今回の packet は、primitive root / Gauss の符号選択を含む必要なデータを保持している。

## Exact element-level endpoint

新規 production module:
`DkMath.NumberTheory.CyclotomicQRProvenanceLift`。

任意の prime `p ≠ 2`、`[Field L] [Algebra ℚ L]`
`[IsCyclotomicExtension {p} ℚ L]`、選んだ `ζ` とその primitive-root proof に対して:

- `gaussTau ζ hζ = (1 + quadraticGauss ζ hζ)/2`。
- `gaussTau_relation`: この元は `t² = signedPrimeParameter p + t` を満たす。
- `gaussEmbedding`: 既存 `TraceOneRat (signedPrimeParameter p) →ₐ[ℚ] L`。
  `gaussEmbedding_injective` により単射。
- `gaussSubfield`: この埋め込みの `fieldRange` である明示的な `IntermediateField ℚ L`。
- `gaussSubfieldEquiv`: 既存 rational TraceOne companion とこの部分体との代数同型。
- `gaussSubfield_finrank`: `Module.finrank ℚ E = 2`。
- `integralEmbedding`: `TraceOneInt (signedPrimeParameter p) →+* L`。

`P` を既存 packet、`w=P.coord z y` とすると:

```text
integralEmbedding w        = eval [z,y] (qrFactorPoly ζ)
integralEmbedding (conj w) = eval [z,y] (qnrFactorPoly ζ)
```

これが `coord_image_eq_qr` と `conj_coord_image_eq_qnr` の正確な元等式。
QR/QNR factor polynomial は既存の指定集合上の積そのものであり、
余分な sign / unit / conjugation の同値類で置き換えていない。
`qr_mem_gaussSubfield` は QR 積の部分体への所属を証明する。

`integralEmbedding_discrAxis` は既存の `2τ-1` を選んだ Gauss 元へ送り、
`integralEmbedding_conj_discrAxis` はその共役を `-G` へ送る。
`gauss_mem_gaussSubfield` も得た。
`axis_images_distinct` は両者の像が異なることを証明する。
`coordinate_packet_unique` は同じ primitive root と provenance を持つ
二つの packet の評価座標が一致することを、埋め込みの単射性から導く。

部分体の ℚ 代数構造には inherited intermediate-field algebra を明示した。
公開 API を別モジュールから使う相対ノルムの回帰も通した。

## Relative norm and ideal transport

- `coord_relative_norm`: rational TraceOne 元の **`Algebra.norm ℚ`** は
  integer shell `GTailCyclotomicShell p (z-y) y` の rational cast。
  乗法行列の行列式を通じて得た相対ノルムである。
- `subfield_coord_relative_norm`: 同じ値を、実際の quadratic subfield に置いた元の
  `Algebra.norm ℚ` として証明した。ここでの norm は **`N_{E/ℚ}`**。
- `integerEmbedding`: integral coordinates から **`NumberField.RingOfIntegers L`**
  への環準同型。既存の有限 ℤ module と integrality の写像保存で構成した。
- `qrInteger`, `qnrInteger`: packet と根選択を保持する整数環内の元。
  `qrInteger_coe`, `qnrInteger_coe` がそれぞれの積との元等式を与える。
- `qrInteger_mul_qnrInteger`: 積は `norm w` の整数環への cast。
  元と共役の積の等式を環準同型で輸送して導いた。
- `map_coordinate_ideal`: `Ideal.map integerEmbedding (Ideal.span {w}) =
  Ideal.span {qrInteger ...}`。
- `qr_qnr_ideal_product`: QR/QNR 主イデアルの積は scalar norm の主イデアル。
- `qrInteger_mem_iff`: 任意の ambient ideal への QR 元の所属は、明示的な環写像に沿う
  `Ideal.comap` への coordinate の所属と同値。
- `qrInteger_not_mem_power`: 上記の実証済み QR/QNR norm pair を既存 ownership cutoff
  に渡す。共役の power membership 輸送、ideal power の拡張等式、収縮等式、
  base norm cutoff の仮定はすべて定理の引数として保持する。

## Boundaries and remaining data

- scalar norm の一致から元等式を推論していない。元等式は retained provenance から得た。
- ここでの QR 主イデアルは **QR half-product** の理想。
  既存 `cyclotomicLinearFactorIdeal` は **一つの linear factor** の理想であり、両者を同一視していない。
- `N_{L/E}` of a single linear factor と QR 積の同一視は今回の endpoint に含めていない。
  今回形式化した相対ノルムは実証済み quadratic element に対する `N_{E/ℚ}`。
- packet 自体は ambient prime ideal の選択や共役所属・拡張・収縮等式を与えない。
  ownership の無条件化にはこれらの追加データが必要であり、条件付き定理に明記した。
- 一般の ideal から principal element を復元していない。既知の coordinate が生成する
  主イデアルだけを写像で輸送した。
- generic field / integer-ring image と現行 `SevenCyclotomicDegreeSixInt.Ring`、
  historical / oriented variants の間の同一視は追加していない。
- signed discriminant、TraceOne companion、QR/QNR factor polynomial の既存定義を再利用した。

## Validation

- focused production build: 成功、8941 jobs。
- `lake build DkMathTest.NumberTheory.CyclotomicQRProvenanceLift`: 成功、8984 jobs。
  最終 production source も依存ターゲットとして再ビルド済み。
- 回帰: QR/QNR の正確な積の像、等しい axis norm と異なる Gauss 符号の像、
  packet 座標の一意性、部分体の次元 2、公開相対ノルム API、
  既存 `TraceOneScalar.coord_norm_eq_cyclotomicIdeal_absNorm` との整合、p=3/5/7 の signed parameter。
- `#print axioms`: 単射性、部分体同型・次元、両元等式、部分体相対ノルム、整数環写像、
  norm pair、ideal map/product/membership/cutoff、符号区別、座標一意性、既存 scalar endpoint。
  すべて `propext`, `Classical.choice`, `Quot.sound` の範囲で、`sorryAx` なし。
- 通常の `lake build`: 成功、10344 jobs。
- `lake build DkMathTest`: 成功、10933 jobs。公開 test facade も検証。
- 新規 Lean files の `sorry` / `admit` / `axiom` / `unsafe` 検索: 該当なし。
- tracked diff、新規 Lean files、新規 report の whitespace check: 成功。

既存依存 `ZsigmondyCyclotomicResearch.lean:147` の `sorry` warning は replay される。
上記で監査した新規 endpoint と scalar compatibility の公理依存には入っていない。

公開入口: production は `DkMath`、regression は `DkMathTest` に import を追加した。

Logs: `/tmp/drc-007-focused.log`, `/tmp/drc-007-regression.log`,
`/tmp/drc-007-full.log`, `/tmp/drc-007-test-facade.log`。
