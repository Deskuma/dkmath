# XDP-009 result: symmetric contour transport and singularity ledger

実装対象は、XDP-008 の completed-zeta log-derivative decomposition と
prime-power endpoint を、critical-line symmetric rectangle の契約へ接続する
範囲で完了した。

## 実装した API

* `PascalCenteredXiExplicitFormulaContourGeometry.lean`
  * centered circle と ordinary critical circle の translation theorem
  * `1 < σ` を持つ symmetric rectangle の parameter contract
  * right / left / top / bottom の 4 edge と orientation 付き boundary integral
  * right edge の `1 < re(s)`、critical reflection による edge/interior の幾何
  * circle と rectangle の same-zero-set を明示的に要求する
    `PascalCenteredXiContourTransportWindow`
* `PascalCenteredXiExplicitFormulaSingularityLedger.lean`
  * `s = 0`, `s = 1`, nontrivial zeta zero, trivial/negative-even candidate,
    `Gammaℝ` exceptional locus の 5 クラス
  * ordinary zeta / archimedean / elementary の term-by-class risk table
  * `Gammaℝ` の totalized point valueを classical Laurent pole value や
    residue と同一視しない docstring を整備
* `PascalCenteredXiExplicitFormulaContourTransport.lean`
  * XDP-008 の 3 項を named term として定義
  * 各 term の 4-edge interval integrability、circle integrability、
    same-zero-set、orientation 済み積分差を受ける
    `PascalExplicitFormulaContourTransportProvider`
  * ordinary / archimedean / elementary の crossed local charge を分離
  * 3 つの provider identity を加える ledger theorem
  * 既存の prime-power endpoint を右 edge の `re(s) > 1` へ接続する
    pointwise adapter

## Gate 判定

* Gate A: Green。circle/ordinary translation、rectangle parameter、4 edge、
  reflection geometry を実装した。
* Gate B: Green。safe radius から rectangle の zero set を推論せず、
  `zero_mem_iff` を window/provider の明示的契約にした。
* Gate C: Green。5 location classes と 3 term の risk ledger を実装した。
* Gate D: Green。4 edge を別々の `IntervalIntegrable` として要求し、right
  edge の `1 < re(s)` を証明した。
* Gate E: Green。既存 endpoint の pointwise right-edge adapter を追加した。
  contour integral と cutoff limit の交換は主張していない。
* Gate F: F1 は未使用。現行 import 範囲では rectangle deformation / residue
  theorem の直接 API を確認できなかったため、F2 の conditional provider
  を実装した。
* Gate G: Green。ordinary / Gamma / elementary の local charge を separate
  fields とした。left-edge reflection の解析的証明や charge の closed form
  は行っていない。
* Gate H: Green。RH、zero classification、defect closure、固定 contour の
  explicit formula を追加していない。

## 数学的に閉じられない境界

以下は current Mathlib API と XDP-009 の入力だけでは証明できないため、
コードの module docstring と conditional provider の field に明記した。

1. symmetric rectangle と centered circle が同じ zeros を囲む具体的な
   `R, σ, T` の存在。
2. 各 decomposed term について、4 edge と circle の integral を結ぶ
   deformation/residue identity の存在証明。
3. crossed local charge の residue coefficient、符号、closed form。
4. `T → ∞`、prime-power cutoff、contour integral の交換。

従って本 checkpoint は provider を仮定した ledger transport までであり、
provider の存在を偽装する `sorry`、axiom、`native_decide` は追加していない。

## XDP-010 coordinate migration addendum

XDP-009 の初版では、centered-coordinate named term を ordinary rectangle
edge に直接渡せる型上の mismatch が残っていた。XDP-010 で
`pascalOrdinaryToCentered` とその相互逆写像を追加し、
`pascalExplicitFormulaCenteredRectangleContribution` を canonical wrapper
とした。従って transport ledger の rectangle contribution は ordinary edge
point を `s - criticalLineCenter` で centered coordinate に戻してから named
term を評価する。raw ordinary-coordinate contribution は低レベル監査用に
別名で保持している。

## 検証

`lean/dk_math` から次を実行し、成功した。

```text
lake build DkMath.RH.CFBRC.PascalCenteredXiExplicitFormulaContourGeometry
lake build DkMath.RH.CFBRC.PascalCenteredXiExplicitFormulaSingularityLedger
lake build DkMath.RH.CFBRC.PascalCenteredXiExplicitFormulaContourTransport
```

公開 import を追加したため、最終確認として `./lb` の対象 build、
`git diff --check`、主要 theorem の `#print axioms` を実行する。
