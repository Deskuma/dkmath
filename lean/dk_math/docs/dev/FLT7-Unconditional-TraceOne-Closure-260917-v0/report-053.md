# FLT7TC-005R47 — Source-sensitive calibration exclusion

## 実装結果

`instruction-053.md` の指定に従い、Astra-002 の scratch bridge を独立した
production module に昇格した。

追加した module:

`DkMath/FLT/Seven/PrimeTraceOneDirectRealCubicCalibrationExclusion.lean`

公開した唯一の endpoint は次の定理である。

```lean
directOrbitDeepJetWUnit_ne_calibration
```

入力は現行の `source`, `r`, `p`, `h`, `hc`, `eta`, `heta` を保持し、
結論は `directOrbitDeepJetWUnit ... eta ≠ directOrbitDeepJetRho`。
`C=1` 全体の矛盾へは拡張していない。

## 実装した証明内容

- `theta^35 * thetaSevenUnit^12` を、`theta^2 * thetaSevenUnit` と
  `7 = theta^3 * thetaSevenUnit` から regroup した。
- `p.source_eq_pow` と source tail から、元の七乗根の二次係数条件
  `(p.rho ^ 7).snd = (p.rho ^ 7).thd` を得た。
- 校正直線上の元 `(a,K,K)` の七乗係数差を指定された五次式で表した。
- `K != 0`, `7 | K` を整数環で処理してから `ZMod 7` へ移し、
  `thetaResidue != 0` と矛盾する内部補題を実装した。
- `W = rho` の仮定から現行 deep-jet normalization と gap scalarization を
  用いて `rho = (rho.fst,K,K)` を復元し、内部補題を適用した。

`PairedDeepJet`、`q % 7 = 1` bridge、degree-six phase bridge、追加 Hensel、
Thue solver、terminal FLT theorem は今回の module に追加していない。

## facade / client / audit

`DkMath/FLT/Seven.lean` に新 module の import を追加した。

追加した client:

- `DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicCalibrationExclusionApi.lean`
- `DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicCalibrationExclusionAxiom.lean`

client は facade 経由で公開 theorem を参照し、同じ theorem shape を適用する。

## 検証結果

Lean は並列実行せず、次の順で実行した。

1. `lake build DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicCalibrationExclusion`
   — exit 0。production module 単体 build 成功。
2. `lake build DkMath.FLT.Seven`
   — exit 0。facade build 成功。
3. `lake env lean DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicCalibrationExclusionApi.lean`
   — exit 0。公開 theorem の `#check` と client application 成功。
4. `lake env lean DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicCalibrationExclusionAxiom.lean`
   — exit 0。公開 theorem の依存公理は
   `[propext, Classical.choice, Quot.sound]`。`sorryAx` は出ていない。
5. 新規 source と client に対する placeholder scan — `sorry`, `admit`,
   `axiom`, `native_decide` の該当なし。
6. `git diff --check` と new report/source の whitespace check — 問題なし。
