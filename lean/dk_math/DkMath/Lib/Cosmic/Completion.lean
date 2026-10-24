/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

-- GN 基礎
import DkMath.Lib.Cosmic.GTail
import DkMath.Lib.Cosmic.GNSuccessor
import DkMath.Lib.Cosmic.GNSupport
import DkMath.Lib.Cosmic.GTailCyclotomic
import DkMath.Lib.Cosmic.GTailBoundary
import DkMath.Lib.Cosmic.GTailCongruence
import DkMath.Lib.Cosmic.GTailNat
import DkMath.Lib.Cosmic.GTailPadic
import DkMath.Lib.Cosmic.GTailPascal

-- 完成算術
import DkMath.Lib.Algebra.BinomTail
import DkMath.Lib.Algebra.SquareCompletion
import DkMath.Lib.Cosmic.CompletionCoprime

-- 完成不足
import DkMath.Lib.Cosmic.PowerDifferenceCofactor
import DkMath.Lib.Cosmic.PowerDifferenceCofactorArithmetic
import DkMath.Lib.Cosmic.CompletionDefect

-- 可除性
import DkMath.Lib.NumberTheory.PowerDifferenceCofactorGcd
import DkMath.Lib.NumberTheory.PowerDifferenceCofactorStrongDivisibility
import DkMath.Lib.NumberTheory.CompletionDefectGcd

-- 原始三項
import DkMath.Lib.Cosmic.CompletionLoan

-- 素数住所
import DkMath.Lib.NumberTheory.PerfectPowerValuation
import DkMath.Lib.NumberTheory.PrimePowerCompensation
import DkMath.Lib.NumberTheory.PadicValNat
import DkMath.Lib.NumberTheory.BinomialPrimePower
import DkMath.Lib.NumberTheory.PrimeRatioOrder
import DkMath.Lib.NumberTheory.CyclotomicAddress
import DkMath.Lib.NumberTheory.CyclotomicLayerValuation
import DkMath.Lib.NumberTheory.PowerDifferenceCofactorValuation
import DkMath.Lib.NumberTheory.PowerDifferenceCofactorPrimeAddress
import DkMath.Lib.NumberTheory.HomogeneousCyclotomic
import DkMath.Lib.NumberTheory.HomogeneousCyclotomicAddress
import DkMath.Lib.NumberTheory.HomogeneousCyclotomicBoundary
import DkMath.Lib.NumberTheory.HomogeneousCyclotomicPrimeAddress

#print "file: DkMath.Lib.Cosmic.Completion"

/-!
# GN と完成算術の公開入口

[DkMath.Lib] GN-LIB-001〜007aで整備した一般核を、所有モジュールへの直接importで公開する。
このファイルは宣言を複製せず、既存の名前空間・仮定・証明をそのまま利用する薄い入口である。

```lean
import DkMath.Lib.Cosmic.Completion
```

## 六つの数学的な層

* **GN 基礎**：GTailによる二項展開、次数再帰、隣接支持、円分表示、合同式と付値。
* **完成算術**：Big・Body・Gapの再構成と三者gcd、二項尾項、平方完成と有限帯。
* **完成不足**：除算不要の有限和 R_n、自然数の不足 D_n、再帰、上界と正性。
* **可除性**：原始座標での強可除性、奇数次数のcoprime、偶数次数の精密gcd。
* **原始三項**：CompletionLoanの因子除去から、正の原始三項 A+B=C を構成する。
* **素数住所**：乗法位数、円分層、斉次評価、LTE、素数冪の深さを表す付値。
  GN-LIB-007aでは全素数付値による完全冪判定と、y=1の有限素数補填・集合外脱出を追加した。

R_nとD_nは `DkMath.Lib.Cosmic`、可除性の新しい一般核は
`DkMath.Lib.NumberTheory` にある。GNは `DkMath.CosmicFormula`、既存の位数・円分住所は
`DkMath.NumberTheory.GapFocusing` など、移管前からの名前を保持している。
ファイルの所有層と宣言の名前空間は同一とは限らない。

原始性、正次数、座標の大小、素数が分母を割らない条件などは各定理の型に残る。
とくに自然数差と有限付値の非零条件、2進LTEの補正を省略しない。
素数住所の分類だけから、新しい原始素数の存在やFLTの矛盾は導かない。
有限集合外の未完成付値の存在は、007aのy=1の特殊構成と独立な非完全冪性の証明に限定する。

`DkMath.Lib` 全体やFLT・Legendre等のconsumerはimportしない。
consumer側からこの入口をimportすることで、応用層への逆依存を防ぐ。
-/
