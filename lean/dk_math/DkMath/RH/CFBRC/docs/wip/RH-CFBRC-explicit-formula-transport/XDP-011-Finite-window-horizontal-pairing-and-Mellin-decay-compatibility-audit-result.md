# XDP-011 — 有限窓水平 pairing / Mellin decay compatibility audit 結果

作成日: 2026-08-12

## 結論

XDP-011 の principal finite-window endpoint は Green である。固定された
finite height の centered rectangle について、even centered weight の下で
上下の水平辺を exact に pairing し、四辺の寄与を

```text
2 × right-edge decomposed contribution
+ 2 × finite top-horizontal contribution
```

へ還元した。ここで有限高さの水平寄与を `0` としたり、固定された
same-zero-set window のまま `T → ∞` を取ったりはしていない。

## 1. 実装した declaration

実装 module は
`DkMath.RH.CFBRC.PascalCenteredXiExplicitFormulaHorizontalPairing` であり、
主な declaration は次の通り。

- `pascalCenteredXiBottomHorizontalIntegrand`
- `pascalCenteredXiTopHorizontalIntegrand`
- `pascalCenteredXiBottomHorizontalIntegrand_reflected`
- `pascalCenteredXiBottomHorizontalContribution_eq_top`
- `pascalCenteredXiHorizontalPair_eq_two_top`
- `pascalCenteredXiRectangleContribution`
- `pascalCenteredXiRectangleContribution_eq_two_right_decomposed_add_two_top`
- `centeredMellinSpectralWeight_centeredMellinBoxApprox_even`
- `centeredMellinSecondDifferenceWeight_centeredMellinBoxApprox_even`
- `PascalCenteredXiMellinWeightVerticalDecayProvider`
- `not_same_zero_set_window_of_zero_outside_ball_inside_rectangle`

## 2. 水平辺の exact sign と orientation

ordinary coordinate の反射を centered coordinate へ移す theorem は
`pascalOrdinaryToCentered_bottomEdge_reflected_eq_neg_topEdge` である。
従って integrand の pointwise reflection は

```text
bottom (1 - u) = - top u
```

となる。top は `σ → 1 - σ`、bottom は `1 - σ → σ` の orientation で
積分されるため、反射による minus sign は interval orientation の反転で
相殺される。形式化された結論は
`pascalCenteredXiBottomHorizontalContribution_eq_top` であり、続いて
`pascalCenteredXiHorizontalPair_eq_two_top` が
`top + bottom = 2 * top` を与える。

## 3. 有限矩形の principal identity

exact な principal theorem は

```lean
pascalCenteredXiRectangleContribution_eq_two_right_decomposed_add_two_top
```

である。これは
`pascalExplicitFormulaCenteredRectangleContribution` の四辺展開、
XDP-010 の
`pascalCenteredXiVerticalPair_eq_two_right_decomposed`、および上記の
水平 pairing を組み合わせる。水平項は finite `T` の named contribution
のままであり、`I_H = 0` は主張していない。

## 4. Mellin weight の evenness

`centeredMellinSpectralWeight_centeredMellinBoxApprox_even` は
log-average の interval substitution `t ↦ -t` により Green である。
さらに
`centeredMellinSecondDifferenceWeight_centeredMellinBoxApprox_even` は
`τ = 0` の patched branch と `τ ≠ 0` の kernel branch を分けて Green
である。mirror self-duality や XDP-007 の未閉鎖 API は仮定していない。

## 5. imaginary-direction decay の境界

weight-only decay は **conditional/provider** と記録する。
`PascalCenteredXiMellinWeightVerticalDecayProvider` は、top edge 上の
Mellin second-difference weight が `T → +∞` で `0` へ tendsto することを
契約として表すが、その provider の存在 theorem は追加していない。

従ってこれは full horizontal integrand の decay theorem ではない。
full Xi-weighted decay には、少なくとも次が別途必要である。

- Xi negative-log-derivative の一様な horizontal growth bound
- zero または near-zero を避ける高さ列
- `u ∈ [1 - σ, σ]` 上の一様性と有限区間積分との接続

これらは本 phase では未証明であり、数学的に閉じられない境界としてこの
module の provider docstring に明記した。

## 6. fixed-window と `T → ∞`

`PascalCenteredXiContourTransportWindow` の `zero_mem_iff` は、固定円と
finite rectangle が同じ centered-Xi zero set を囲む契約である。従って固定
`R, σ` のまま rectangle height を無制限に増やす shortcut は licensed でない。

形式化した obstruction theorem
`not_same_zero_set_window_of_zero_outside_ball_inside_rectangle` は、円の
外側にある centered-Xi zero が rectangle interior に入るなら、同じ
`zero_mem_iff` を持つ window は矛盾することを示す。これは、そのような
zero の存在を主張する theorem ではなく、localization contract と
arbitrary `T → ∞` の自動両立を禁止する型レベルの監査である。

## 7. limit-order ledger

```text
T → ∞ under fixed same-zero-set window: NOT LICENSED
X → ∞ under right-edge pointwise evaluation: GREEN pointwise only
X-limit ↔ interval integral exchange: OPEN
T-limit ↔ rectangle transport: OPEN / localization conflict
τ → 0 then ε → 0⁺: existing Green chain
```

joint limit、limit permutation、prime cutoff convergence と interval integral
の交換は導入していない。

## 8. no-circularity audit

- left edge は fixed Xi のままで、未証明の residue/deformation provider を使わない。
- right edge のみ XDP-010 の decomposed observable へ transport する。
- Mellin weight の tendsto provider を Xi log-derivative の decay と同一視しない。
- rectangle deformation、crossed local charge の closed form、prime cutoff と
  積分の極限交換、defect vanishing、RH は導入していない。
- 新規 code に `sorry`、`admit`、`axiom`、`native_decide` を追加していない。

## 9. 検証

次を実行して検証した。

```text
lake build DkMath.RH.CFBRC.PascalCenteredXiExplicitFormulaHorizontalPairing
```

新 module とその依存は pinned toolchain で build できる。公開 surface には
`DkMath.RH` から import を追加した。最終 wrapper build と `#print axioms`
監査では、principal declarations に project の通常の
`[propext, Classical.choice, Quot.sound]` 以外を要求しないことを確認する。
`git diff --check` も通過させる。既存 unrelated file にある
`declaration uses sorry` warning は XDP-011 の新規 code とは区別する。

## 10. XDP-012 への handoff

finite rectangle の圧縮は完了したが、次の load-bearing provider は未閉鎖で
ある。候補は finite-height の適切な高さ列による horizontal analytic control、
実際の rectangle deformation / residue provider、または right-edge interval
上の prime cutoff の uniform / dominated transport である。`T → ∞` を自動的な
次手とはしない。
