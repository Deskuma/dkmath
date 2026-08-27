# XDP-006 — Mellin centered dilation / second-difference 実装結果

実施日: 2026-08-12

## 結果

XDP-006 の Green API を実装した。

追加した module は次の二つである。

```text
DkMath/Analysis/MellinCenteredDilation.lean
DkMath/RH/CFBRC/PascalCenteredXiMellinSecondDifferenceBridge.lean
```

public aggregation には次を追加した。

```text
DkMath/Analysis.lean
DkMath/RH.lean
```

## Gate A — pinned Mathlib scaling API audit

採用した scaling theorem は、pinned Mathlib の
`mellin_comp_mul_left` である。これは正の実数 `a` に対して

```lean
mellin (fun t => h (a * t)) s = (a : ℂ) ^ (-s) • mellin h s
```

を与える。`mellinDilate λ h x = h (x / λ)` を `a = λ⁻¹` として
適用し、`λ > 0` から `λ⁻¹ > 0` を供給した。`Complex.inv_cpow` と
positive real の `Complex.arg` normalization により、結果を
`(λ : ℂ) ^ s * mellin h s` に整理している。

従って、独自の positive-ray change-of-variables proof は再実装していない。
`λ > 0` は inverse scale の positivity、support interval の順序、
および positive-real complex `cpow` branch の normalization に使われる。
Mellin の totalized value `0` を convergence の代用にした equality は
追加していない。収束条件は既存の Mellin theorem と XDP-004/005 の
compact-support contract に委ねている。

## Generic Mellin Core

`mellinDilate` について次を実装した。

- `support_mellinDilate_subset`
- `continuousOn_mellinDilate_of_support_subset`
- `mellin_mellinDilate`

さらに `λ = exp τ` に対して、centered half-weight を除いた dilation が

```text
centeredMellinDilatedSpectralWeight h τ z
  = exp (τ z) * centeredMellinSpectralWeight h z
```

となる exact theorem を実装した。

patched definition

```text
centeredMellinSecondDifferenceWeight h τ z
```

は `τ = 0` で `z² * H_h(z)` を値として持つ。`τ ≠ 0` では exact に

```text
((exp (τ z) - 2 + exp (-τ z)) / τ²) * H_h(z)
```

である。

## Pointwise limit and differentiability

pure complex kernel について、Mathlib の
`Complex.exp_sub_sum_range_succ_isLittleO_pow` と
`IsLittleO.tendsto_div_nhds_zero` を用いて

```text
complexExpSecondDifferenceKernel τ z → z²
```

を証明した。`τ = 0` の patched value と limit target の一致も証明に
含めている。

この結果との exact composition により、重み付きの主 theorem

```text
Q_{τ,h}(z) → z² * centeredMellinSpectralWeight h z
```

を実装した。`z²` 単独へ弱めたり、`H_h = 1` を仮定したりしていない。
また、同じ positive compact-support contract から patched second
difference weight が `Differentiable ℂ` であることを示した。

## Fixed-Xi bridge

`pascalCenteredXiZeroDiskWeightedMoment` は有限 `Finset` の和なので、
pointwise limitを `tendsto_finsetSum` で有限 weighted moment limitへ
transport した。この theorem 自体には safe radius hypothesis を付けて
いない。

safe radius を仮定する contour theorem は既存の
`pascalCenteredXiNormalizedWeightedOuterContourMass_eq` へ thin application
し、principal-part subtraction や Cauchy integral proof を再実装していない。
さらに normalized contour family の limitを finite moment limit と合成した。
contour 側の符号は既存 theorem 通り `-` を保持している。

有限集合上で `centeredMellinSpectralWeight h z = 1` を仮定した場合に限る
quadratic moment → `pascalCenteredXiZeroDiskSecondMoment` の conditional
adapter も追加した。これは interpolation の存在を主張しない。

## 明示的な数学的境界

XDP-006 で閉じた exact endpoint は

```text
Q_{τ,h}(z) → z² * H_h(z)
```

である。ordinary compact-support Mellin transformから global に
`H_h(z) = 1` を得ること、従って `Q_{τ,h} → z²` を実現することは、
本 phase の theorem からは数学的に従わない。この named realization gap
を XDP-007 に残すことを module docstring と本報告に明記した。

したがって本実装は provider theorem、defect vanishing、prime-side
transport、または RH theorem ではない。

## Validation

実施済みの validation:

```text
lake env lean DkMath/Analysis/MellinCenteredDilation.lean
lake env lean DkMath/RH/CFBRC/PascalCenteredXiMellinSecondDifferenceBridge.lean
lake build DkMath.Analysis.MellinCenteredDilation
./lean-build.sh
./lean-test.sh
git diff --check
```

`./lean-build.sh` と `./lean-test.sh` は成功した。新規 module の
`sorry/admit/axiom/native_decide` audit も空であり、既存 unrelated module
の `sorry` warning だけが build/test log に残っている。
