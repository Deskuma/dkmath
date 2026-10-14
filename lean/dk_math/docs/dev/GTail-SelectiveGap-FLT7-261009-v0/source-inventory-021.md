# Step 021 — six supplied root slots: source inventory

Date: 2026-10-10. Branch `feature/GTail-SelectiveGap-FLT7-261009-v0`.
Base HEAD `5945b33ec83eaecbc7d8f7c1d06476191f0dbe71`.
review-020 / report-020 / source-inventory-020 を確認。review は static source review で、独立 Lean rebuild ではない。

## Exact APIs and prerequisites

| Source | Reused symbols / overlap | Input boundary |
| --- | --- | --- |
| `GTailCyclotomicPrimeAddress` | `seventhRootKernel`, membership iff, isMaximal/isPrime, comap_intCast/cardQuot, `seventhRootKernel_ne`, `evalCyclotomic_linearFactor_eq_zero_iff` | Fact prime q、supplied scalar root certificates。separation は actual integral element の Step020 theorem |
| `GTailCyclotomicLocalEval` | actual degree-six RingHom、`gtailCyclotomicLinearFactor` | source は `QuadraticAlgebra SevenRealCubicInt (-1) (alpha-1)`。signed packet 不要 |
| `GTailSevenPairedResidue` | Tail ratio pow_seven/ne_zero/ne_one | q∤c,g、q|T。Q divisibility / Fermat equation 不要 |
| `GTailSevenPrimeOrder` | `orderOf_eq_prime` の既存利用、prime-order field units 証明 | order-seven を Fin6 injectivity に使う。order3/7 intersection の証明を複製しない |
| `SevenRamifiedFusionGlobalOrientedPrimeFactorization` | `cyclicEval/Kernel`, `cyclicConjugateEval/Kernel`, `rotateEquiv_zeta`, `rotateEquiv_ofReal` | actual supplied `CyclotomicLinearPrimeAddress p q`、Fin3 real-Galois phase。今回の Fin6 ascending power slots と異なる input/index |
| `SevenRamifiedFusionCyclotomicConjugatePrimePair` | `star_zeta`, `star_zetaInv`, `star_ofReal`、旧 packet conjugate evaluation | degree-six quadratic conjugation。star_zeta の結論は actual `zetaInv`、逆元の具体表示。q3 Eisenstein conjugation ではない |

Mathlib `GroupTheory/OrderOfElement.lean`：`orderOf_eq_prime hr7 hr1` は Fact prime7 の下で order7。
`pow_injOn_Iio_orderOf` は任意 monoid で order 未満の自然指数の冪が単射。
指数 i.val+1 は1..6、identity 比較の0も order7 未満。
単純な monoid cancellation の誤用はせず、この実 theorem で ne_one / injectivity を示す。
非零冪は prime-field `pow_ne_zero`、七乗等式は pow_mul と hr7。
Fin の equality は `Fin.ext` と指数の arithmetic。
`Ideal.isCoprime_of_isMaximal`（Ideal/Operations）は異なる maximal ideals に対して IsCoprime。
`.sup_eq` で sup=top を得る。Step015 の proof pattern と同じであり、intersection reconstruction を含まない。

## Import plan / exceptions

新 production の唯一の直接 import は Step020 `GTailCyclotomicPrimeAddress`。
新 test は production と既存 ramified q7 owner を直接 import。
旧 global-oriented factorization / conjugate-pair owners は source inspection のみで、新 direct dependency にしない。
既存 carrier closure と新 declaration の packet-free input を区別する。
neutral trace module の FLT 逆依存を増やさない。closure 実測値は report。

root order / injectivity は q-prime や hr0 を使わない範囲ではそれらを前提に加えない。
actual kernels / maximality は Fact prime q と非零 root certificates を要求する。
q7 で supplied 非自明七乗根は存在せず、q13 Gap ratio1 は API の hr1 を満たさない。
q3 repeated / q5 inert は別 degree-two Eisenstein phenomena。

## Deferred equalities

今回六つの roots は explicit powered roots。任意 admissible root の網羅性を示す
optional root-classification theorem は実装せず、「全 admissible roots」の分類とは呼ばない。
Galois covariance も defer：ζ↦ζ² の一致だけでは whole RingHom equality は足りず、
`rotateEquiv_ofReal` の base rotation と alpha の β evaluation を整合させる証明が必要。
star の whole-map covariance も今回主張しない。

六 kernel の pairwise comaximality だけでは product=(q) を示さない。
将来には `⋂ i, K_i = Ideal.span {(q:R)}` の signed degree-six coordinate interpolation / CRT 等による
別の equality が必要。今回 intersection equality / product theorem を試行していない。
Eisenstein→degree-six integral hom、ideal transfer、exact valuations、class/unit powers、descent は未実装。
