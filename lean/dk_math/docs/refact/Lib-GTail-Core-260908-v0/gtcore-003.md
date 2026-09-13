# GTCORE-003 Tail Filtration / Pascal Surface

Date: 2026-09-10
Status: complete for the scoped GTCORE-003 checkpoint
Branch: `refact/DkMath-Lib-GTail-Core-260908-v0`
Source/build root: `lean/dk_math`

このメモは、`analysis-001.md` と `analysis-002.md` の後段計画を、今回の
direct request「GTCORE-000 の次へ進む」に対して限定的に進めた記録である。
今回の対象は、改訂優先順で先に置かれた GTCORE-003 のうち、一般の `r ≤ s ≤ d`
における `GTail` の有限深さ分解と、薄い Pascal facade / regression である。

## 1. 実装したもの

### Public theorem

`DkMath.Lib.Cosmic.GTailPascal.lean` に次を追加した。

```lean
GTail_split_at
```

仮定 `r ≤ s` と `s ≤ d` の下で、次を kernel-checked theorem として提供する。

```text
GTail d r x u =
  (∑ k ∈ Finset.range (s - r),
    (Nat.choose d (r + k) : R) * x ^ k * u ^ (d - (r + k)))
    + x ^ (s - r) * GTail d s x u
```

証明は `GTail` の有限和を prefix と suffix に分け、suffix を `s - r` だけ
再添字化して `x ^ (s - r)` を因数化するもの。既存の `GTail` 定義・既存定理の
statement・既存の GN wrapper は変更していない。

### Public surface / regression

- `DkMath.Lib.lean` から `DkMath.Lib.Cosmic.GTailPascal` を export した。
- `DkMathTest/CosmicFormula/GTailPascal.lean` に `ℕ` と `ℤ` の concrete depth
  regression を追加した。
- 新しい module docstring と public theorem docstring に、これは有限代数恒等式で
  あり、Goldbach-specific theorem・valuation bridge・asymptotic statement では
  ないことを明記した。

## 2. 検証

### Focused build

次の build は成功した。

```bash
cd lean/dk_math
lake build DkMath.Lib.Cosmic.GTailPascal \
  DkMathTest.CosmicFormula.GTailPascal
```

### Facade and consumer build

次の facade / core / 既存 consumer を含む build も成功した。

```bash
cd lean/dk_math
lake build DkMath.Lib DkMath.Lib.Cosmic.GTailPascal \
  DkMathTest.CosmicFormula.GTailPascal \
  DkMath.Lib.Cosmic.GTail DkMath.Lib.Cosmic.GTailNat \
  DkMath.Lib.Cosmic.GTailCongruence DkMath.Lib.Cosmic.GTailPadic \
  DkMath.CosmicFormula DkMath.FLT.Three DkMath.FLT.Five \
  DkMath.ABC DkMath.NumberTheory.Primitive DkMath.CFBRC \
  DkMath.NumberTheory.Goldbach DkMathTest.NumberTheory.GoldbachGNFiber
```

最終結果は `Build completed successfully (9021 jobs).` である。build 出力には
既存 research / axiom diagnostics も含まれるが、GTCORE-003 の新規 source に
`sorry` や axiom は追加していない。

## 3. 今回は行っていないこと

添付文書の後段候補、および今回の direct request の非対象は保持した。

- GTCORE-001 dependency inversion
- GTCORE-002 exact boundary gcd
- `@[deprecated]` の追加
- `GN` の global rename、consumer rewrite、既存 statement の変更
- `DkMath/ABC/PadicValNat.lean` の移動または valuation provider 化
- Goldbach / FLT / ABC / RH / CFBRC の migration
- `GTail` core の既存 file への大規模書換え

したがって、今回の checkpoint は GTCORE-003 の load-bearing な有限分解 surface
までで停止している。次段では、この surface を前提に GTCORE-002 の boundary
gcd を検討できるが、別 checkpoint として扱う。
