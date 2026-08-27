# XDP-007 result: multiplicative approximate identity and quadratic realization

実装対象は、通常のコンパクト台 Mellin test function によって
`z ^ 2` を centered Mellin weight の極限として実現する bridge である。
この checkpoint では、distribution や hard zero-window indicator は導入していない。

## 実装した API

### Generic Mellin module

`DkMath.Analysis.MellinMultiplicativeApproxIdentity` に次を追加した。

* `centeredMellinBoxApprox ε x`

  `ε > 0` では

  ```text
  (2 * ε)⁻¹ * x^(-(1 : ℂ) / 2) 1_[exp (-ε), exp ε](x)
  ```

  を採用し、`ε ≤ 0` は Lean の totalization として `0` とする。
* `centeredMellinBoxApprox_support_subset`

  positive width では support が
  `Icc (exp (-ε)) (exp ε)` に含まれる。
* `centeredMellinBoxApprox_continuousOn`

  同じ閉区間上の `ContinuousOn` を証明した。
* `mellinConvergent_centeredMellinBoxApprox`

  全 Mellin parameter に対する積分の収束を示した。
* `centeredMellinSpectralWeight_centeredMellinBoxApprox_eq_logAverage`

  `x = exp t` の区間置換により、centered Mellin weight が

  ```text
  (2 * ε)⁻¹ ∫ t in Icc (-ε) ε, exp (t * z)
  ```

  という log-average に一致することを示した。
* `tendsto_centeredMellinSpectralWeight_centeredMellinBoxApprox_one`

  `ε → 0⁺` で上の log-average が `1` に収束することを示した。
* `tendsto_centeredMellinBoxApprox_quadraticWeight`

  各 `z` について

  ```text
  z ^ 2 * H_ε(z) → z ^ 2
  ```

  を示した。

証明では `intervalIntegral.integral_deriv_smul_comp'` による指数関数の
区間置換を使った。従って、有限区間の ordinary box family については
全 Mellin parameter が admissible である。

### CFBRC bridge

`DkMath.RH.CFBRC.PascalCenteredXiMellinQuadraticRealizationBridge` に次を追加した。

* `tendsto_pascalCenteredXiZeroDiskMellinBoxQuadraticMoment_secondMoment`

  有限 `pascalCenteredXiZeroDiskFinset R` 上で `tendsto_finsetSum` を使い、
  `z ^ 2 * H_ε(z)` の極限を
  `pascalCenteredXiZeroDiskSecondMoment R` へ lift した。
* `tendsto_pascalCenteredXiNormalizedMellinBoxSecondDifferenceOuterContourMass_tau`

  各 fixed `ε > 0` について、XDP-006 の normalized outer-contour
  `τ → 0` theorem を box family に特殊化した。support、endpoint order、
  `ContinuousOn` は generic module の API から供給される。
* `tendsto_pascalCenteredXiMellinBoxQuadraticNormalizedContourTarget`

  fixed-`ε` contour limit の target を `ε → 0⁺` で
  `-pascalCenteredXiZeroDiskSecondMoment R` へ送った。
* `pascalCenteredXiMellinBoxQuadraticLimit_eq_fixedSecondContourTarget`

  safe radius の既存 `z ^ 2` fixed contour theorem と同じ scalar であることを
  確認した。新しい residue 計算は行っていない。

## 数学的境界

この実装が閉じるのは次の iterated limit である。

```text
fixed ε > 0:
  τ → 0  normalized outer contour  →  -M_ε

then:
  ε → 0⁺  (-M_ε)  →  -M₂
```

`(ε, τ)` の product-filter による joint limit は主張していない。
また、ordinary compact-support box の Mellin weight は有限 ε で一般に
恒等的に `1` ではないので、global exact interpolation や Dirac identity
として読むことはできない。mirror self-duality の optional corollary は
主要求 acceptance set (A--H) に不要であり、未実装の half-power
conjugation shortcut を導入せず保留した。blocked candidate は
`centeredMellinBoxApprox_mellinCriticalMirror` であり、これを閉じるには
positive real の reciprocal interval equivalence と
`Complex.inv_cpow` / `Complex.conj_cpow` による half-power identity を
追加の補助 lemma として固定する必要がある。この保留は数学的矛盾ではなく、
既存 checkpoint の principal endpoint に不要な補助 API を増やさないための
明示的な境界である。

従って、本 checkpoint は RH、defect vanishing、prime-side explicit formula、
zero classification を証明しない。explicit-formula 接続は指示書どおり
XDP-008 以降の frontier に残る。

## shortcut / axiom audit

box の log-average は有限区間積分の change-of-variables から導出し、
有限 Xi 和は `tendsto_finsetSum` で処理した。`sorry`、`admit`、追加
`axiom`、`native_decide`、global exact `H_ε = 1`、joint limit のいずれも
proof shortcut として使用していない。全体 build に表示された既存 axiom
情報と `sorry` warning は既存 project declaration のものであり、
XDP-007 の新規 declaration にはない。
新規 principal declaration の `#print axioms` は標準的な
`propext`、`Classical.choice`、`Quot.sound` のみを表示した。

## 検証

次を実行し、XDP-007 の generic module と bridge は Green になった。

```text
lake env lean DkMath/Analysis/MellinMultiplicativeApproxIdentity.lean
lake env lean DkMath/RH/CFBRC/PascalCenteredXiMellinQuadraticRealizationBridge.lean
```

`./lean-build.sh`、`./lean-test.sh`、`git diff --check` は実行済みで、いずれも
成功した。wrapper が表示する既存 project 由来の `sorry` warning は別問題として
扱い、この checkpoint では新しい `sorry`、`admit`、`axiom`、`native_decide` を
導入していない。
