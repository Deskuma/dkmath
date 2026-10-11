# Step 023 — source element factorization inventory

Date: 2026-10-10. Branch `feature/GTail-SelectiveGap-FLT7-261009-v0`.
Base HEAD `400e6079a95a491605dcf798c86eadd74a20e24c`.
Prerequisites review-022 / report-022 / source-inventory-022 を確認。
review は static source review であり独立 rebuild ではない。

## Exact source and sign conventions

Existing `SevenCyclotomicDegreeSixInt.Ring` = `QuadraticAlgebra SevenRealCubicInt (-1) (alpha-1)`。
ζ=⟨0,1⟩、ofReal は actual algebraMap。
`zeta_quadratic_relation`: ζ²−ofReal(alpha−1)*ζ+1=0。
`ofReal_alphaSubOne_cubic_relation`: t³+t²−2t−1=0, t=ofReal(alpha−1)。
`zeta_pow_seven`, `zeta_ne_one`, `zeta_isPrimitiveRoot` は既存 theorem。
real cubic `alpha_cube` は alpha³=2alpha²+alpha−1。
座標 equivalence は additive only、順序 (re.fst,re.snd,re.thd,im.fst,im.snd,im.thd)。
今回は座標から新 ring を作らず、actual source relations を直接使う。

Factors は `(c+g:R)−ζ^(i.val+1)*(c:R)`。既存 F0 は
`ofReal((c+g:ℕ):SevenRealCubicInt)−ζ*ofReal(c:SevenRealCubicInt)`。
scalar natural casts と actual ofReal の一致を Lean simp で検証する。
`evalCyclotomicFromSeventhRoot_zeta` と map_sub/mul/pow/natCast は factor 評価用。

## Existing exact shell and overlapping factorization

`GTail_one_eq_GTailCyclotomicShell` は任意 CommSemiring、任意 d,x,u について成立。
`GTailCyclotomicShell d x u = ∑ k∈range d, (x+u)^k*u^(d-1-k)`。
証明は recurrence 比較であり gap cancellation、field、x≠0 は不要。
今回 Fin7 sum は同じ七項を逆順に並べたもの。range/Fin 展開後 ring で確認する。
GTailNat / GTailSeven の定義・recursion・degree-seven bodies を確認したが、
既存 homogeneous shell theorem が最も小さく、g=0 を正しく含む reusable API。

`CyclotomicQRTraceOneBridge.map_primeCyclotomicShellPoly_eq_qr_mul_qnr` は
Field、Algebra ℚ、IsCyclotomicExtension、prime p と supplied primitive root の MvPolynomial identity。
その基礎 `CyclotomicQRProduct.primitiveRoots_product_poly_eq_shell` も Field を要求する。
Mathlib `Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots`、`IsPrimitiveRoot.geom_sum_eq_zero`
は genuine domain/primitive-root infrastructure の reusable route。
`SevenRamifiedFusionCyclotomicDegreeSixDomain.ringIsDomain` は actual source の IsDomain instance、
fraction carrier への injective map による証明。ただし追加 heavy oriented owners を import する。
`CyclotomicPrincipalization.CyclotomicLocalFactorizationContext.linear_factor_mul_eq_sub_pow`
は supplied ζ^p=1 による一因子の幾何和×因子=冪差であり、六因子 shell そのものではない。
古い packet/support ideal product theorem と今回の element product を取り違えない。

## Cheapest verified route and cancellation budget

Domain を追加 import せず、quadratic relation と cubic relation の線形結合で七項和零を証明。
一般 CommRing の z について、七項和零から六 factor product=homogeneous shell を
explicit finite expansion / linear_combination で証明する。
Sympy の整数 polynomial division は certificate 探索のみ。生成された二つの relation multipliers と
27-term product multiplier を Lean が再検証する。外部計算結果の axiom 化はない。
ζ^7=1、ζ≠1 だけから ζ−1 を消去する推論は採用しない。
自然 GTail は existing shell theorem を使うので g の除法・消去はない。

Primary gate: unconditional actual source element product for arbitrary c,g。
この focused build 成功後に optional incidence を追加。
Incidence は nonzero c cancellation と `IsOfFinOrder.pow_inj_mod`、Step021 `seventhRoot_orderOf`。
`orderOf_pos_iff`, `div_mul_cancel₀`, `mul_left_inj'`, `pow_mul` は actual source names を確認。
36-case finite lookup は q43 に限定せず、指数だけの Fin6 arithmetic を検証。

## Dependencies and non-goals

新 owner は Step022 owner と GTailCyclotomic の二 direct imports。
新 test は今回 owner 一つ。FLT facade、Domain、Kummer、QR bridge の追加 import はしない。
旧 source ring / signed-packet owners / root drivers / ledger の編集は不要。
核への所属は local residue incidence であり、factor principal ideal=kernel、exact valuation、
principalization、unit/class extraction、integral Eisenstein map、FLT7 descent は証明しない。
Step023 のみで停止。逐次 focused builds、process-local LEAN_NUM_THREADS=2、追加 proof options なし。
