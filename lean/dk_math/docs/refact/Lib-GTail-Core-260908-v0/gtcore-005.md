# GTCORE-005 Cyclotomic Promotion Audit

Date: 2026-09-10
Status: complete for the scoped GTCORE-005 checkpoint
Branch: `refact/DkMath-Lib-GTail-Core-260908-v0`
Source/build root: `lean/dk_math`

このメモは、`analysis-001.md` の GTCORE-005
「cyclotomic promotion audit」を、解析系 CFBRC machinery を下位 Lib に導入せずに
実施した記録である。対象は、現行 `DkMath.CFBRC.CyclotomicProduct` にある代数的な
再利用核のうち、`GTail` の prime row と直接結び付く部分、および一般の
cyclotomic divisor-product 評価である。

## 1. Audit conclusion

現行 CFBRC 側には、次の二つの層が混在している。

- `Polynomial.prod_cyclotomic_eq_geom_sum` を評価した一般 `d` の divisor-product
  恒等式
- shifted homogeneous evaluation、`cyclotomicPrimeCore`、`GN`、および `u ≠ 0`
  の scaling をまとめた CFBRC 側の bridge

前者と、後者のうち prime cyclotomic shell と `GTail p 1` の代数的同一視は
analytic CFBRC machinery から独立している。この部分を
`DkMath.Lib.Cosmic.GTailCyclotomic` に昇格した。後者の shifted divisor-product の
全面移設は、今回の checkpoint では行っていない。

## 2. 実装したもの

### Lower Lib module

新規 module
`DkMath/Lib/Cosmic/GTailCyclotomic.lean` を追加し、import は次の二つだけにした。

```lean
import DkMath.Lib.Cosmic.GTail
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
```

従って、この module は `DkMath.CFBRC`、`CosmicFormulaBinom`、解析 package を
import しない。

### Promoted algebraic surface

`DkMath.Lib.NumberTheory` namespace に次を追加した。

```lean
cyclotomicEval
prod_cyclotomicEval_eq_geomSum
```

後者は、`d > 0` の下で

```text
∏ m ∈ d.divisors.erase 1, Φ_m(X) = ∑ i ∈ range d, X^i
```

の評価版を kernel-checked にしたものである。

`DkMath.CosmicFormula` namespace には次を追加した。

```lean
GTailCyclotomicHomEval
GTailCyclotomicShell
GTailCyclotomicShell_succ
add_pow_eq_mul_GTailCyclotomicShell_add_gap
GTail_one_eq_GTailCyclotomicShell_of_ne_zero
GTailCyclotomicHomEval_prime_eq_shell
GTail_one_eq_cyclotomicHomEval_of_prime
```

これにより、任意の素数 `p` と field 上の `x ≠ 0` に対して、

```text
GTail p 1 x u
  = homogeneousEval(Φ_p, x + u, u)
```

という prime-row bridge を、CFBRC package から独立して利用できる。
`GTail` の `r = 1` と cyclotomic shell の結び付けは、差冪恒等式と左因子消去を
用いている。`x = 0` の場合には、この checkpoint では division-free な
homogeneous shell theorem へ拡張していない。

### Public facade / regression

- `DkMath/Lib.lean` から `DkMath.Lib.Cosmic.GTailCyclotomic` を export した。
- `DkMathTest/CosmicFormula/GTailCyclotomic.lean` を追加した。
- regression では、`d = 5` の divisor-product 評価、任意素数の homogeneous
  bridge、および `p = 5` の shell identity を確認した。
- 既存 `DkMath.CFBRC` の定義・公開 theorem・wrapper は変更していない。

## 3. 検証

### Focused build

次の build は成功した。

```bash
cd lean/dk_math
lake build DkMath.Lib.Cosmic.GTailCyclotomic \
  DkMathTest.CosmicFormula.GTailCyclotomic
```

最終結果は `Build completed successfully (8657 jobs).` である。

### Core / consumer replay

`DkMath.Lib` と主要な既存 consumer の replay も成功した。

```bash
cd lean/dk_math
lake build DkMath.Lib DkMath.Lib.Cosmic.GTailCyclotomic \
  DkMathTest.CosmicFormula.GTailCyclotomic DkMath.CosmicFormula \
  DkMath.FLT.Three DkMath.FLT.Five DkMath.ABC \
  DkMath.NumberTheory.Primitive DkMath.CFBRC \
  DkMath.NumberTheory.Goldbach DkMathTest.NumberTheory.GoldbachGNFiber
```

最終結果は `Build completed successfully (9024 jobs).` である。build 出力中の
既存 research `sorry` / axiom diagnostics は既存依存のものであり、今回の新規
module と regression には `sorry`・axiom・deprecated declaration を追加していない。
`git diff --check` も成功した。

## 4. 今回は行っていないこと

- `DkMath.CFBRC.CyclotomicProduct` の shifted evaluator / divisors product の全面移設
- `cyclotomicPrimeCore` の既存 CFBRC namespace からの削除・rename・deprecated 化
- 既存 CFBRC consumer の import rewrite または global rename
- `u ≠ 0` の scaling、degree-sum、general-`d` divisors product と `GN` の
  compatibility wrapper の移行
- `GTail` と Goldbach overlap の同一視、FLT/ABC/RH への数学的帰結
- valuation、primitive divisor、analytic/asymptotic conclusion

したがって GTCORE-005 は、再利用可能な代数核を Lib surface に追加し、
CFBRC 側の既存 API を保ったまま停止している。shifted product 全体の移行や
deprecated policy は、後続の compatibility/deprecation checkpoint に残す。
