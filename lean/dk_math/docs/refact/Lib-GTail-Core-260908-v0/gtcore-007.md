# GTCORE-007 Cross-Project Replay

Date: 2026-09-10
Status: replay complete; source migration not started; deprecation deferred
Branch: `refact/DkMath-Lib-GTail-Core-260908-v0`
Source/build root: `lean/dk_math`
Replay commit: `7c12cd173`

このメモは、`analysis-001.md` の GTCORE-007
「cross-project replay」を、GTCORE-006 の compatibility wrapper を保持したまま
実施した記録である。今回の checkpoint では global rename、source theorem の変更、
`@[deprecated]` の導入は行わない。目的は canonical GTail core と legacy GN surface
の組み合わせが、主要な downstream import graph で破綻しないことを確認し、次の
移行単位を分類することである。

## 1. Replay scope

次の代表 target を replay した。

- GTail core / CosmicFormula compatibility / regression
- FLT3 / FLT5
- ABC representative aggregate
- Primitive aggregate
- Pascal core と regression
- CFBRC aggregate と RH-CFBRC focused target
- Goldbach aggregate と GN fiber regression

GTCORE-006 の判断を引き継ぎ、旧 `GN` / `GN_eq_sum` / `cosmic_id_csr'` は削除せず、
canonical `DkMath.Lib.Cosmic.GTail` の上にある compatibility surface として扱った。

## 2. Replay matrix

### 2.1 Core and arithmetic consumers

実行した command は次の通りである。

```bash
cd lean/dk_math
lake build DkMath.Lib DkMath.Lib.Cosmic.GTail \
  DkMath.CosmicFormula.CosmicFormulaBinom DkMath.CosmicFormula \
  DkMathTest.CosmicFormula.GTailCompatibility \
  DkMathTest.CosmicFormula.GTailCyclotomic \
  DkMath.FLT.Three DkMath.FLT.Five DkMath.ABC \
  DkMath.NumberTheory.Primitive DkMath.CFBRC \
  DkMath.NumberTheory.Goldbach DkMathTest.NumberTheory.GoldbachGNFiber
```

結果は `Build completed successfully (9025 jobs).` であった。

| Area | Target | Result |
|---|---|---|
| GTail / compatibility | `DkMath.Lib`, `DkMath.Lib.Cosmic.GTail`, `DkMath.CosmicFormula`, `DkMath.CosmicFormula.CosmicFormulaBinom` | PASS |
| regression | `DkMathTest.CosmicFormula.GTailCompatibility`, `GTailCyclotomic` | PASS |
| FLT | `DkMath.FLT.Three`, `DkMath.FLT.Five` | PASS |
| ABC | `DkMath.ABC` | PASS |
| Primitive | `DkMath.NumberTheory.Primitive` | PASS |
| CFBRC | `DkMath.CFBRC` | PASS |
| Goldbach | `DkMath.NumberTheory.Goldbach`, `DkMathTest.NumberTheory.GoldbachGNFiber` | PASS |

### 2.2 Pascal and RH-CFBRC supplement

analysis-002.md の追加条件を明示的に満たすため、次も別 replay した。

```bash
cd lean/dk_math
lake build DkMath.Lib.Cosmic.GTailPascal \
  DkMathTest.CosmicFormula.GTailPascal \
  DkMath.RH.CFBRC.EtaCriticalMirrorDefectCoefficientMargin \
  DkMathTest.RH.CFBRCEtaCriticalMirrorDefectCoefficientMargin
```

結果は `Build completed successfully (8720 jobs).` であった。

この結果は、GTail Pascal surface および現行 RH-CFBRC の代表的な focused target が、
GTCORE-006 の canonical signature / wrapper 状態で replay 可能であることを示す。
RH-CFBRC 全研究ファイルの semantic migration や RH の数学的結論を示すものではない。

## 3. What the replay establishes

- canonical `DkMath.CosmicFormula.GN {R} d x u` と `GTail d r x u` の d-first
  形は、FLT3 / FLT5 / ABC / Primitive / CFBRC / Goldbach の import graph を壊さない。
- `BodyN` を canonical `GN` に接続した状態でも、旧 consumer は wrapper 経由で build
  できる。
- Goldbach の legacy `GN 2` fiber と、独立した `Nat.choose` / Pascal overlap
  hierarchy は同時に replay できる。後者を GTail と同一視する変更は行っていない。
- Pascal と RH-CFBRC の追加 target も、canonical core の変更による compile failure を
  示さなかった。
- これは compatibility-preserving replay の成功であり、consumer 全面 migration、
  theorem dependency の完全な canonicalization、または新しい数学的結果を意味しない。

## 4. Migration inventory revealed by replay

`DkMath` と `DkMathTest` の Lean source に対する字面検索では、現時点で次の件数だった。
これらは declaration、docstring、wrapper、test を含むため、consumer 数そのものではない。

| Search pattern | Occurrences |
|---|---:|
| `DkMath.CosmicFormulaBinom.GN` | 406 |
| `GN_eq_sum` | 37 |
| `cosmic_id_csr` | 47 |
| `DkMath.CosmicFormula.GN` | 29 |

代表的な残存領域は次の通りである。

- `CosmicFormula` / `Analysis` / `BookOfMagic`
- `NumberTheory` / `Primitive` / `Zsigmondy`
- `FLT` / `ABC`
- `CFBRC` / RH-CFBRC bridge
- `Goldbach` と GN fiber

したがって、次の migration は単純な全置換ではなく、少なくとも次の分類を要する。

1. `GN d x u` をそのまま canonical `GN d x u` に置ける通常 consumer
2. `GN_eq_sum` の explicit sum shape に依存する proof
3. `cosmic_id_csr'` の旧 endpoint 名に依存する proof
4. Gnomon のように `GN 2 u x` と引数を交換する意味依存 consumer
5. `G` / `GZ` / `GC` の family 境界を持つ consumer
6. `R` を positional に渡していた旧 canonical-call site

## 5. Diagnostics and boundary

replay は exit code `0` で完了した。ただし既存コード由来の diagnostics は出力された。

- `ZsigmondyCyclotomicResearch` など既存 research declaration の `sorry` warning
- ABC / Goldbach / Eisenstein 等の既存 theorem に対する
  `[propext, Classical.choice, Quot.sound]` の axiom dependency diagnostics

これらは GTCORE-007 の source migration により追加されたものではなく、今回の replay
で既存対象が再表示されたものである。GTCORE-007 ではこれらを新しい GTail theorem の
正当化や migration 完了の根拠にはしない。

`@[deprecated]` は導入していない。既存の無関係な deprecated declaration は存在するが、
GTCORE-006 の GN compatibility wrapper 群については warning を発生させない境界を維持
している。

## 6. Decision

GTCORE-007 の replay acceptance は満たしたと判断する。

次の判断は次の通りである。

- canonical core と compatibility wrapper は現行 cross-project consumers に対して
  継続使用可能
- source global rename はまだ行わない
- `@[deprecated]` はまだ導入しない
- migration は領域別・意味別に分割し、各領域の focused build と proof-shape を
  確認してから進める

次の deprecation checkpoint に進むための条件は、少なくとも各 replacement の import
path、`R` argument policy、explicit sum proof の移行形、G/GZ semantic boundary、
warning 対応順序を確定することである。GTCORE-008 の FLT7 re-entry は、これらの
compatibility / migration 境界を保持したまま、別途 dependency graph を比較する。

## 7. Not done

- legacy GN consumer の global rename
- `GN_eq_sum` / `cosmic_id_csr'` の一括置換
- `G` / `GZ` / `GC` の一括 migration
- `@[deprecated]` の追加
- RH-CFBRC の研究 theorem の semantic migration
- 新しい数学的 theorem や Strong Goldbach / RH / ABC の結論
