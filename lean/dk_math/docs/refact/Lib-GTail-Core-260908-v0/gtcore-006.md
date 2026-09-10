# GTCORE-006 Compatibility / Deprecated Layer

Date: 2026-09-10
Status: complete for the scoped GTCORE-006 checkpoint
Branch: `refact/DkMath-Lib-GTail-Core-260908-v0`
Source/build root: `lean/dk_math`

このメモは、`analysis-001.md` の GTCORE-006
「compatibility / deprecated layer」を、既存 consumer の全面移行を開始せずに
実施した記録である。対象は、旧 `GN` / `cosmic_id_csr'` endpoint と、Lib 側に
残る重複 alias の documented wrapper 化および staged deprecation である。

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

## 2. Compatibility and staged deprecation

旧名は直ちに削除せず、既存 import と downstream proof を保ったまま次の
deprecation を付けた。

- `DkMath.CosmicFormulaBinom.GN` は、旧引数順
  `{R} d x u` を保つ wrapper として残し、canonical
  `DkMath.CosmicFormula.GN` へ deprecated 化した。canonical 側は
  `(R) x u d` の順であるため、Lean の警告には型・namespace の差も表示される。
- `DkMath.CosmicFormulaBinom.GN_eq_sum` は
  `DkMath.CosmicFormula.GTail_one_eq_sum` への compatibility theorem として残し、
  deprecated 化した。
- `DkMath.CosmicFormulaBinom.cosmic_id_csr'` は、証明を
  `add_pow_eq_mul_GTail_one_add_gap` への直接委譲に変更し、同 theorem への
  deprecated wrapper とした。
- `DkMath.Lib.Cosmic.GTail.GN_tail_decomposition` と
  `Gbinom_tail_rec` は `GN_tail_rec` の deprecated alias とした。
- `Gbinom_zero_eval` は `GN_zero_eval` の deprecated alias とした。

`cosmic_id_csr`、`G` / `GZ` / `GC` 系など、今回の endpoint と別の数学的 family は
機械的に変更していない。

## 3. Regression

新規 regression
`DkMathTest/CosmicFormula/GTailCompatibility.lean` を追加した。
次を kernel-checked に確認する。

- canonical `add_pow_eq_mul_GTail_one_add_gap`
- 旧 `CosmicFormulaBinom.GN` と canonical `CosmicFormula.GN` の definitional
  compatibility
- 旧 `GN_eq_sum` と `cosmic_id_csr'` の wrapper
- 旧 `Gbinom_tail_rec` と `Gbinom_zero_eval` の compatibility

旧名を実際に参照する regression のため、focused build には意図した deprecation
warnings が出る。

## 4. Verification

### Focused build

次の build は成功した。

```bash
cd lean/dk_math
lake build DkMath.Lib.Cosmic.GTail \
  DkMath.CosmicFormula.CosmicFormulaBinom \
  DkMathTest.CosmicFormula.GTailCompatibility
```

最終結果は `Build completed successfully (8667 jobs).` である。

### Core / consumer replay

互換層が既存 consumer の elaboration を壊していないことを確認するため、次を
replay した。

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

最終結果は `Build completed successfully (9025 jobs).` である。出力された大量の
`CosmicFormulaBinom.GN` 等の deprecation warning は、今回の staged compatibility
signal であり、後続の downstream migration checkpoint で処理する。既存の research
`sorry` および既存 theorem の axiom dependency diagnostics も出力されたが、今回
新たに追加した source / regression には `sorry`・`axiom` を追加していない。

`git diff --check`、対象 source / regression の末尾空白監査、および対象 source /
regression の `sorry|axiom` 監査も成功した。

## 5. Not done

- global `GN -> GTail` rename
- FLT / ABC / Primitive / RH / CFBRC / Goldbach consumer の downstream migration
- `G` / `GZ` / `GC` など別 family の一括 deprecation
- 旧 wrapper の削除
- `cosmic_id_csr` の別形 endpoint の機械的変更
- 新しい数学的結論

したがって GTCORE-006 は、canonical lower-Lib theorem と staged compatibility
layer を用意し、旧 API を保ったまま停止している。次の境界は GTCORE-007 の
cross-project replay / migration 検討である。
