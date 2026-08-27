# XDP-010 result: coordinate-safe functional-equation edge reflection

XDP-010 の principal endpoint を実装した。XDP-009 の ordinary rectangle
と centered named term の型上の mismatch は、ordinary-to-centered wrapper
で修復した。

## 実装 API

* `PascalCenteredXiExplicitFormulaContourGeometry.lean`
  * `pascalOrdinaryToCentered`
  * centered / ordinary の相互逆写像 theorem
  * left edge reflection の centered-coordinate negation theorem
* `PascalCenteredXiExplicitFormulaContourTransport.lean`
  * raw ordinary rectangle contribution と canonical centered rectangle
    contribution を分離
  * 既存 ledger の rectangle contribution を canonical wrapper に移行
* `PascalCenteredXiExplicitFormulaFunctionalEquationReflection.lean`
  * fixed centered Xi negative-log-derivative の global oddness
  * `PascalCenteredEvenWeight` と quadratic specialization
  * weighted fixed-Xi integrand の oddness
  * combined decomposed observable
  * reflected-point conditional theorem for the combined observable
  * `1 < σ` から right edge の `s ≠ 0`, `s ≠ 1`, `ζ s ≠ 0`,
    `Gammaℝ s ≠ 0` を自動供給
  * right edge の fixed-Xi pointwise decomposition
  * orientation 付き left/right vertical contribution と
    `vertical pair = 2 * right contribution`
  * right contribution を combined decomposed observableへ書き換える主定理
  * top / bottom horizontal contributions は named definition のまま保持

## Gate status

* Gate 0: Green。centered / ordinary mismatch を canonical translation
  wrapper で修復した。
* Gate A: Green。fixed centered Xi kernel の evennessから、derivative
  transportを経て `pascalCenteredXiNegLogDeriv_neg` を証明した。
* Gate B: Green。functional-equation の正本を fixed Xi の combined observable
  に限定し、個別 zeta/Gamma/elementary reflection law は導入していない。
* Gate C: Green。even centered weight と quadratic weight を追加した。
* Gate D: Green。weighted fixed-Xi integrand の oddnessを追加した。
* Gate E: Green。right edge の `1 < re(s)` から factor nonzero と pointwise
  decomposition を自動供給した。
* Gate F/G: Green。left edge は fixed Xi のまま反射し、orientation reversal
  と affine negation を interval integral theorem で処理した。
* Gate H: Green。既存 right-edge prime-power pointwise endpoint を保持した。
* Gate I: Green。horizontal contributions は明示的な未評価項として残した。
* Gate J: Green。XDP-009 modules と public `DkMath.RH` import を再ビルドした。

## 数学的に閉じられない範囲

次は XDP-010 の対象外であり、コード中の module docstring にも明記した。

* horizontal-edge decay、`T → ∞`、rectangle deformation / residue provider
* crossed local charge の閉形式
* prime cutoff と interval integral の極限交換
* defect の符号・消滅、full explicit formula、RH

left edge では trivial zero / Gamma exceptional の個別 decomposition を
強制せず、cancellation 済み fixed Xi observable を使用している。これは
XDP-009 の singularity ledger を削除するものではなく、個別項の不正な
分離を避けるための coordinate-safe な適用範囲である。

## 検証

以下を `lean/dk_math` から実行して成功した。

```text
lake build DkMath.RH.CFBRC.PascalCenteredXiExplicitFormulaContourGeometry
lake build DkMath.RH.CFBRC.PascalCenteredXiExplicitFormulaContourTransport
lake build DkMath.RH.CFBRC.PascalCenteredXiExplicitFormulaFunctionalEquationReflection
```

公開 import 後の `./lb DkMath.RH`、主要 theorem の `#print axioms`、
`git diff --check` を最終検証とする。
