# GTCORE-002 Exact Boundary GCD

Date: 2026-09-10
Status: complete for the scoped GTCORE-002 checkpoint
Branch: `refact/DkMath-Lib-GTail-Core-260908-v0`
Source/build root: `lean/dk_math`

このメモは、`analysis-001.md` の Candidate A と `analysis-002.md` の実装順を
現行 workspace に対して検証・実装した記録である。GTCORE-003 で追加した filtration
surface と独立に、`GTail_rec` の境界 head が自然数 gcd を完全に決めることを
general `r` で formalize した。

## 1. Candidate A の扱い

添付文書の research target

```text
gcd(x, GTail(d,r,x,u)) = gcd(x, choose(d,r) * u^(d-r))
```

は、`d r x u : ℕ` と `r ≤ d` だけで成立する exact theorem として実装できた。
さらに `Coprime x u` を仮定すると、`u^(d-r)` の因子を gcd から除去した形も
実装した。

この結果は `r = 1` の `GN` 専用 theorem ではなく、`GTail` 全体に対する theorem
である。既存の `GN` wrappers や下流の `gcd_GN_eq_prime` 等は移行していない。

## 2. 実装したもの

### Public boundary module

`DkMath.Lib.Cosmic.GTailBoundary.lean` を追加した。

```lean
gcd_GTail_eq_gcd_boundary
gcd_GTail_eq_gcd_choose
```

第一定理は次を kernel-checked にする。

```text
Nat.gcd x (GTail d r x u)
  = Nat.gcd x (Nat.choose d r * u ^ (d - r))
```

第二定理は `Nat.Coprime x u` の下で次を与える。

```text
Nat.gcd x (GTail d r x u) = Nat.gcd x (Nat.choose d r)
```

証明は `r = d` の終端 `GTail d d x u = 1` と、`r < d` の場合の
`GTail_rec`、および自然数 gcd の `x` 倍加法則による。第一定理は、適用範囲を
不必要に prime degree・positive input・coprime input に限定していない。

### Public surface / regression

- `DkMath.Lib.lean` から `DkMath.Lib.Cosmic.GTailBoundary` を export した。
- `DkMathTest/CosmicFormula/GTailBoundary.lean` に一般 boundary、coprime
  simplification、`r = d` endpoint の回帰を追加した。
- module / public theorem docstring に、これは有限 divisibility identity であり、
  prime-exponent theorem や downstream migration ではないことを明記した。

## 3. 検証

### Focused build

次の build は成功した。

```bash
cd lean/dk_math
lake build DkMath.Lib.Cosmic.GTailBoundary \
  DkMathTest.CosmicFormula.GTailBoundary
```

### Facade and consumer build

GTCORE-000 で記録した core / facade / 主要 consumer 群を含む build も成功した。

```bash
cd lean/dk_math
lake build DkMath.Lib DkMath.Lib.Cosmic.GTailBoundary \
  DkMathTest.CosmicFormula.GTailBoundary \
  DkMath.Lib.Cosmic.GTail DkMath.Lib.Cosmic.GTailNat \
  DkMath.Lib.Cosmic.GTailCongruence DkMath.Lib.Cosmic.GTailPadic \
  DkMath.CosmicFormula DkMath.FLT.Three DkMath.FLT.Five \
  DkMath.ABC DkMath.NumberTheory.Primitive DkMath.CFBRC \
  DkMath.NumberTheory.Goldbach DkMathTest.NumberTheory.GoldbachGNFiber
```

最終結果は `Build completed successfully (9022 jobs).` である。出力中の既存
research `sorry` / axiom diagnostics は既存依存のものとして現れたもので、今回の
GTCORE-002 source には `sorry`・axiom・deprecated declaration を追加していない。

## 4. 今回は行っていないこと

- `GTCORE-001` dependency inversion、`PadicValNat` の移動
- `GN` の global rename、既存 wrapper の deprecated 化
- FLT3 / FLT5 / ABC / Primitive / RH / CFBRC / Goldbach の consumer migration
- 既存の GN-specific gcd theorem の削除・statement 変更
- prime-row、valuation、cyclotomic、exceptional-prime theorem の追加

したがって、今回の checkpoint は general `GTail` の exact boundary gcd surface の
追加までで停止している。既存 consumer が新 theorem を使うこと自体は、別の移行
checkpoint で扱う。
