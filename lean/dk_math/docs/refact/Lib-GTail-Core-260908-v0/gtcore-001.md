# GTCORE-001 Dependency Inversion

Date: 2026-09-10
Status: complete for the scoped GTCORE-001 checkpoint
Branch: `refact/DkMath-Lib-GTail-Core-260908-v0`
Source/build root: `lean/dk_math`

このメモは、`analysis-001.md` の dependency inversion 方針と
`analysis-002.md` の実装順を、GTCORE-002 の後の現行 workspace に対して検証・実装した
記録である。generic な `padicValNat` 補題を ABC 層から Lib 層へ移し、`GTailPadic`
が下位 provider に直接依存できる状態にした。

## 1. Candidate の扱い

添付文書が指摘した旧依存は、次の upward dependency であった。

```text
DkMath.Lib.Cosmic.GTailPadic -> DkMath.ABC.PadicValNat
```

今回の checkpoint では、generic な valuation API の canonical owner を
`DkMath.Lib.NumberTheory.PadicValNat` とした。ABC 側に残る
`DkMath.ABC.PadicValNat` は、既存 consumer の公開名を保つ compatibility facade と
して整理した。

## 2. 実装したもの

### Lower provider

`DkMath/Lib/NumberTheory/PadicValNat.lean` を追加した。次の 12 個の generic lemma を
`DkMath.Lib.NumberTheory` namespace で提供する。

```text
padicValNat_split
padic_val_two_of_odd
padic_val_two_of_even
padicValNat_eq_zero_iff
padicValNat_le_self
padicValNat_le_log
Vp_ge_one_iff
padicValNat_one_le_of_prime_dvd
padicValNat_le_iff_dvd
padicValNat_pow
padicValNat_pow'
dvd_padicValNat_pow
```

この provider は `Mathlib` のみに依存し、ABC・FLT・RH には依存しない。
`DkMath.Lib.lean` からも export した。

### Compatibility facade and dependency repair

- `DkMath/ABC/PadicValNat.lean` の旧 12 名は削除せず、lower provider を呼ぶ薄い
  wrapper として保持した。
- 旧 namespace には `deprecated` attribute を付けていない。global rename や既存
  consumer の一括移行も行っていない。
- `DkMath/Lib/Cosmic/GTailPadic.lean` は `DkMath.Lib.NumberTheory.PadicValNat`
  を直接 import し、valuation theorem の参照も lower namespace に変更した。
- aggregate build で旧 `DkMath.ABC` 名に依存していた
  `DkMath/CosmicFormula/CosmicFormulaBinom.lean` が露呈したため、そこには旧 facade
  への明示 import を追加した。これは hidden transitive import の修復であり、定理の
  statement・公開名の移行ではない。

### Regression

`DkMathTest/NumberTheory/PadicValNat.lean` を追加し、lower provider の
`padicValNat_pow` / `padicValNat_le_iff_dvd` と、旧 `DkMath.ABC.padicValNat_pow`
facade の利用を確認した。

## 3. 検証

### Focused builds

次の focused build はすべて成功した。

```bash
cd lean/dk_math
lake build DkMath.Lib.NumberTheory.PadicValNat
lake build DkMath.Lib.NumberTheory.PadicValNat \
  DkMath.ABC.PadicValNat DkMath.Lib.Cosmic.GTailPadic
lake build DkMathTest.NumberTheory.PadicValNat
lake build DkMath.CosmicFormula.CosmicFormulaBinom
```

### Aggregate / consumer build

GTCORE-000 で記録した core / facade / 主要 consumer 群を含め、次の build を実行した。

```bash
cd lean/dk_math
lake build DkMath DkMath.Lib DkMath.Lib.NumberTheory.PadicValNat \
  DkMath.ABC.PadicValNat DkMath.Lib.Cosmic.GTailPadic \
  DkMathTest.NumberTheory.PadicValNat \
  DkMath.CosmicFormula.CosmicFormulaBinom DkMath.CosmicFormula \
  DkMath.FLT.Three DkMath.FLT.Five DkMath.ABC \
  DkMath.NumberTheory.Primitive DkMath.CFBRC \
  DkMath.NumberTheory.Goldbach DkMathTest.NumberTheory.GoldbachGNFiber
```

最終結果は `Build completed successfully (9858 jobs).` である。出力中の既存 research
`sorry` / axiom diagnostics は既存依存のものとして現れたもので、今回の refactor
source には `sorry`・axiom・deprecated declaration を追加していない。

依存方向の source audit でも、`DkMath/Lib` 配下から
`DkMath.ABC.PadicValNat` を import する箇所は 0 件である。確認結果は
`GTailPadic -> DkMath.Lib.NumberTheory.PadicValNat`、旧 facade と
`CosmicFormulaBinom` は明示的に ABC compatibility surface を使う形になっている。

## 4. 今回は行っていないこと

- `GTCORE-004` 以降の prime-row / higher-tail / valuation surface の追加
- `GN` の global rename、既存 wrapper の deprecated 化
- ABC / FLT / Primitive / RH / CFBRC / Goldbach の広範な consumer migration
- valuation theorem の数学的拡張、研究段階の theorem や axiom の追加
- 既存 `DkMath.ABC` 公開名の削除・statement 変更

したがって、今回の checkpoint は generic valuation provider の層反転と旧 namespace
互換 facade の確立までで停止している。次段の実装は、添付文書の順序に従い
GTCORE-004 以降の個別 checkpoint で扱う。
