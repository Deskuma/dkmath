# GTCORE-006 Compatibility Layer — Final Outcome

Date: 2026-09-10
Status: compatibility layer complete; trial replacement validated; deprecation deferred
Branch: `refact/DkMath-Lib-GTail-Core-260908-v0`
Source/build root: `lean/dk_math`
Evidence commit: `a4e39690a` (`refact: GTCORE-006: test refact replace`)

このメモは、`analysis-001.md` の GTCORE-006
「compatibility / deprecated layer」を、既存 consumer の全面移行を開始せずに
実施した記録である。対象は、旧 `GN` / `cosmic_id_csr'` endpoint と、Lib 側に
残る重複 alias の documented wrapper 化である。互換性を優先し、今回の checkpoint
では `@[deprecated]` を付けない判断に変更した。

今回の trial replacement では canonical `GN` を実 consumer の一部へ直接適用し、
全体の `DkMath` / `DkMathTest` build が通ることまで確認した。ただし、これは
global rename や全 downstream の移行完了を意味しない。互換 wrapper を残したまま、
どこまでが機械的に置換でき、どこからが意味・elaboration・証明形状の調整を要するか
を確定した checkpoint である。

## 1. Canonical replacement

`DkMath.Lib.Cosmic.GTail` に次の canonical theorem を追加した。

```lean
add_pow_eq_mul_GTail_one_add_gap
```

これは `CommSemiring` 上で全ての `d` に対して

```text
(x + u)^d = x * GTail d 1 x u + u^d
```

を与える。`d = 0` も含め、既存の generic prefix theorem
`add_pow_eq_prefix_add_xpow_mul_GTail` の `r = 1` specialization として実装した。
従って `GTail_one_eq_sum`、`GN_tail_rec`、`GN_zero_eval` とともに、旧 endpoint
の安定した置換先は lower Lib 側にある。

## 2. Compatibility wrappers

旧名は削除せず、既存 import と downstream proof を保ったまま canonical theorem
へ委譲する wrapper / alias として残した。現段階では deprecation warning を発生
させない。

- `DkMath.CosmicFormulaBinom.GN` は、旧引数順
  `{R} d x u` を保つ wrapper として残し、canonical
  `DkMath.CosmicFormula.GN` に委譲する。canonical 側も `{R} d x u` として、
  positional replacement の互換性を優先する。
- `DkMath.CosmicFormulaBinom.GN_eq_sum` は
  `DkMath.CosmicFormula.GTail_one_eq_sum` への compatibility theorem として残す。
- `DkMath.CosmicFormulaBinom.cosmic_id_csr'` は、証明を
  `add_pow_eq_mul_GTail_one_add_gap` への直接委譲に変更するが、旧公開名を維持する。
- `DkMath.Lib.Cosmic.GTail.GN_tail_decomposition` と
  `Gbinom_tail_rec` は `GN_tail_rec` の compatibility alias として維持する。
- `Gbinom_zero_eval` は `GN_zero_eval` の compatibility alias として維持する。

`cosmic_id_csr`、`G` / `GZ` / `GC` 系など、今回の endpoint と別の数学的 family は
機械的に変更していない。

### Canonical targets (not deprecated yet)

| # | 旧| 新|
|---|---|---|
|1|`DkMath.CosmicFormulaBinom.GN`|`DkMath.CosmicFormula.GN`|
|2|`DkMath.CosmicFormulaBinom.GN_eq_sum`|`DkMath.CosmicFormula.GTail_one_eq_sum`|
|3|`DkMath.CosmicFormulaBinom.cosmic_id_csr'`|`add_pow_eq_mul_GTail_one_add_gap`|
|4|`DkMath.Lib.Cosmic.GTail.GN_tail_decomposition`|`GN_tail_rec`|
| |`Gbinom_tail_rec`|`GN_tail_rec`|
|5|`Gbinom_zero_eval`|`GN_zero_eval`|

### Refactoring Note

see:

- [GN, G parameter order investigation](gn-g-parameter-order-investigation.md)

## 3. Trial replacement: confirmed results and remaining issues

今回の試行変更では、次の範囲を canonical surface に寄せた。

- `Defs.GN` を `{R} d x u` に固定した。`GTail d r x u` および legacy
  `CosmicFormulaBinom.GN d x u` と degree-first が一致し、通常の呼び出しでは `R`
  を `x` / `u` から推論できる。
- `CosmicFormulaBinom.GN` は旧公開名・旧引数順の compatibility wrapper として残し、
  canonical `CosmicFormula.GN` へ委譲した。
- `BodyN`、`CoreBeamGap`、`SquareGnomon`、`SquareBody` の代表的な consumer で、
  canonical `GN` または `GTail` の直接参照を試した。
- `GN_eq_G`、`G_eq_GN`、`cosmic_id_csr'` および `GN_eq_sum` は、canonical
  theorem を根にした既存公開面として維持した。
- compatibility regression で旧名と canonical 名の definitional compatibility および
  endpoint identity を確認した。

### 3.1 What the full-build trial establishes

全モジュールの成功は、今回変更した canonical signature と wrapper の組み合わせが、
現行 import graph と既存 theorem 群の範囲で elaboration を壊していないことを示す。
特に、`BodyN` の定義本体を canonical `GN` にしても、既存 consumer を wrapper 経由で
残せるため、段階移行の足場として機能する。

これは数学的な新結果ではなく、次の API 境界を build で確認した結果である。

```text
GTail d r x u
        ↓ r = 1
CosmicFormula.GN d x u
        ↓ compatibility wrapper
CosmicFormulaBinom.GN d x u
```

### 3.2 Issues exposed by the trial

単純な textual replacement だけでは全 consumer を移行できないことも確定した。

- canonical `GN` の `R` を implicit にしたため、旧試行のように `GN R ...` や
  `GN ℚ ...` と型を positional に渡す呼び出しは、そのままでは成立しない。必要な箇所は
  `(R := R)` / `(R := ℚ)` または named arguments に直す必要がある。
- `GN` を `GTail` の abbrev として残しても、tactic の `rw` が常に abbrev を展開して
  `GTail_one_eq_sum` を見つけるわけではない。`BodyN` / canonical `GN` を明示的に
  unfold してから `GTail_one_eq_sum` を使う証明形状が必要になる場合がある。
  `SquareGnomon` と `SquareBody` がこの実例である。
- `SquareGnomon` は式の意味上 `GN 2 u x` を使う。一般の `GN d x u` を機械的に
  置換すると `2 * u + x` になり、必要な `2 * x + u` と一致しない。これは API 順序の
  問題ではなく、Gnomon 用途で `x` と `u` を交換している数学的役割の問題である。
- `CosmicFormulaBinom.G` と `CosmicFormula.G` は同じ名前の文字列でも意味が異なる。
  前者は gap-normalized GN family、後者は body-normalized `GZ` alias であるため、
  `G` の global rename は実施できない。
- 現在も多数の FLT / ABC / Primitive / Goldbach / research consumer は旧
  `CosmicFormulaBinom.GN`、`GN_eq_sum`、`cosmic_id_csr'` を参照している。今回の
  full build 成功は wrapper が残る状態での互換性を示すもので、consumer 全面移行の
  完了を示さない。

したがって、canonical signature の採用自体は成立したが、deprecated warning を一斉に
有効化するには、残存 consumer の semantic role と proof-shape を個別に確認する必要が
ある。

## 4. Regression

新規 regression
`DkMathTest/CosmicFormula/GTailCompatibility.lean` を追加した。
次を kernel-checked に確認する。

- canonical `add_pow_eq_mul_GTail_one_add_gap`
- 旧 `CosmicFormulaBinom.GN` と canonical `CosmicFormula.GN` の definitional
  compatibility
- 旧 `GN_eq_sum` と `cosmic_id_csr'` の wrapper
- 旧 `Gbinom_tail_rec` と `Gbinom_zero_eval` の compatibility

旧名を実際に参照する regression でも、今回の wrapper は deprecation warning を
発生させない。

## 5. Verification

### Focused build

deprecation rollback 後の次の focused build は成功した。

```bash
cd lean/dk_math
lake build DkMath.Lib.Cosmic.GTail \
  DkMath.CosmicFormula.CosmicFormulaBinom \
  DkMath.CosmicFormula.CoreBeamGap \
  DkMathTest.CosmicFormula.GTailCompatibility
```

最終結果は `Build completed successfully (8668 jobs).` である。旧名の互換 wrapper を
含む regression でも、今回導入した deprecation warning は発生しない。

### Core / consumer replay

deprecation rollback 前には、互換層が既存 consumer の elaboration を壊していない
ことを確認するため、次を replay した。

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

最終結果は `Build completed successfully (9025 jobs).` である。これは deprecation
rollback 前の replay 記録であり、warning は今回撤回した staged deprecation による
ものである。既存の research `sorry` および既存 theorem の axiom dependency
diagnostics も出力されたが、今回追加した source / regression には `sorry`・`axiom`
を追加していない。

`git diff --check`、対象 source / regression の末尾空白監査、および対象 source /
regression の `sorry|axiom` 監査も成功した。

### Full module and test build after the trial replacement

現コミット `a4e39690a` に対して、リポジトリの build wrapper を再実行した。

```bash
cd lean/dk_math
./lean-build.sh
```

結果は `DkMath` の `9841` jobs 完了、exit code `0`、`build succeeded` である。
続けて regression を含む test 側も再実行した。

```bash
./lean-build.sh -T
```

結果は `DkMathTest` の `10043` jobs 完了、exit code `0`、`test build succeeded`
である。出力された `sorry` 警告は既存 research declaration に由来し、今回の
compatibility layer に新たな `sorry` / `axiom` は追加していない。

## 6. Not done / next boundary

- global `GN -> GTail` rename
- FLT / ABC / Primitive / RH / CFBRC / Goldbach consumer の downstream migration
- `G` / `GZ` / `GC` など別 family の一括 deprecation
- 旧 wrapper の削除
- `cosmic_id_csr` の別形 endpoint の機械的変更
- `@[deprecated]` の導入。canonical API と positional / named argument の互換性、
  downstream の移行範囲が安定した後の別 checkpoint で再評価する。
- 新しい数学的結論

したがって GTCORE-006 は、canonical lower-Lib theorem と deprecation なしの
compatibility layer を用意し、旧 API を保ったまま停止している。deprecation は
後続の実移行計画が定まり、warning を段階的に処理できる時点まで延期する。次の
境界は GTCORE-007 の cross-project replay / migration 検討である。
