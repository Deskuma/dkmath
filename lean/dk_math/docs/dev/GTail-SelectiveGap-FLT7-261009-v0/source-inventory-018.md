# Step 018 — source inventory

Date: 2026-10-10. Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`.
Base HEAD: `f7ab00db4fbef28bd199c4537db0a193c4480c42`.
Prerequisites: review-017, report-017, report-011 を確認。review-017 の評価はソースレビューであり、独立した Lean 実行結果として扱わない。

## Carrier comparison

| Carrier | 定義関係 | 既存 map / 今回の利用 | 今回まだ得られないもの |
| --- | --- | --- | --- |
| `TraceOneInt (-1)` | τ²=τ−1、α(a,b)=⟨a,b⟩、norm α=Q | `eisensteinResidueRingHom t ht : TraceOneInt (-1) →+* ZMod q`。kernel `eisensteinResidueIdeal`、選択 α と α² の向き付き支持 | この整環から degree-six 整環への RingHom / ideal transfer |
| `SevenCyclotomicDegreeSixInt.Ring` | `QuadraticAlgebra SevenRealCubicInt (-1) (alpha-1)`、ζ²−ofReal(alpha−1)ζ+1=0、ζ⁷=1 | `ofReal` と既存 `localEval address : Ring →+* ZMod q` | 今回の自然数 Q/T 前提から address を構成し、その canonical ratio を今回の r と一致させる橋 |
| `SevenRealCubicInt` | alpha³=2alpha²+alpha−1 | `ofReal`。既存 address の `evalAlphaRoot` は alpha を beta=1+ratio+ratio⁻¹ に評価 | 今回の任意 Tail ratio から、基底関係を確認した汎用評価 RingHom |
| `ZMod q` | q-prime の有限体 | 今回の t=−a/b と r=(c+g)/c。二根の codomain が同じ | integral source rings の同一視、ideal の同一視、unit class、descent |

## Exact neutral overlap

- `Lib/Cosmic/GTail.lean`: `add_pow_eq_mul_GTail_one_add_gap` は任意 CommSemiring の `(x+u)^d = x*GTail d 1 x u + u^d`。今回は自然数式を cast し、q|T を使う。g を除算しない。
- `Lib/Cosmic/GTailNat.lean`: `GTail_not_dvd_of_head_unit_of_prime_dvd_x` は gap-divisor/head-unit による Tail exclusion。`Lib/Cosmic/GTailSeven.lean` の `selectedBody_seven_interior` は `7*x*u*(x+u)*(x²+x*u+u²)²`。これを今回新しい element factorization に強めていない。
- `GTailSevenPrimeOrder`: `seven_dvd_prime_sub_one_of_gtail` 内部で同じ比 r と七乗・非零・非自明性を既に証明。`prime_ne_three_of_gtail` と `twentyOne_dvd_prime_sub_one_of_quadratic_gtail` を再利用。orderOf 議論は複製しない。Step011 の order-three ratio は a/b、今回の Eisenstein root t は −a/b であり、t 自身を order-three root と呼ばない。
- `GTailSevenEisensteinResidue`: `gtailSevenResidueRoot`、`gtailSevenResidueRoot_polynomial`、conjugate polynomial / nonzero evaluation を再利用。
- `GTailSevenResidueIdeal`: `eisensteinResidueRingHom`、kernel、`gtailSevenNormCoord_mem_residueIdeal` と `gtailSevenNormCoord_not_mem_conjugate_residueIdeal`。`GTailSevenIdealSquareAddress`: `gtailSevenNormCoord_split_square_address` の既存三項結論を利用。

## Existing degree-six residue map: full input boundary

`FLT/Seven/SevenRamifiedFusionCyclotomicPrimeAddress.lean` の
`QuotientPrimeMuSevenAddress (p : RamifiedSignedRootDepthPacket) (q : ℕ)` は
`prime : Nat.Prime q` と `dividesQuotientRoot : (q : ℤ) ∣ p.quotientRoot` を持つ。
ratio はこの p の signed roots から再構成される unit で、任意の seventh root を格納する field ではない。
`evalAlphaRoot` はこの address の beta を用いた real-cubic RingHom。
`SevenRamifiedFusionCyclotomicDegreeSixCarrier.localEval` はこの base evaluation と
private `ratio_quadratic_relation` により乗法を検証し、ζ を canonical ratio に送る。
したがって既存 compatible residue map は存在する。しかし今回の neutral hypotheses は p、quotientRoot divisibility、自然数比と signed-root 比の一致を供給しない。
既存 map の直接適用を装う adapter は追加しない。

`SevenRamifiedFusionCyclotomicRamifiedPrime` の `ramifiedEval : Ring →+* ZMod 7` は ζ↦1、
`ramifiedPrime=ker ramifiedEval=span{ramifiedUniformizer}`。
`ofReal_seven_eq_uniformizer_pow_six_mul_unit` はこの degree-six carrier の七分岐であり、
TraceOneInt(-1) の q=3 ramified ideal / square とは別物。

## FLT owner and Mathlib feasibility

`GTailPrimeAllocationAudit.not_prime_dvd_coordinate_product_of_quadratic` は coprimality から座標積単元を、
`not_prime_dvd_endpoint_of_quadratic` は正確な Fermat equation から c 単元を、
`prime_focused_support_exclusive` は q≠7 と sum balance を加えて Gap/Tail 排他性を与える。
`GTailPrimeOrderAudit.twentyOne_dvd_prime_sub_one_of_focused_tail` はこれらから Step011 を受け取る既存 owner。
今回の型付き根は neutral API で直接得られるため、同じ前提導出を繰り返す任意 owner は省略した。これは signed-depth address adapter の欠落を解消しない。

Mathlib `RingTheory/Polynomial/Cyclotomic/Basic.lean` の実ソースで
`Polynomial.cyclotomic_prime (R) (p)` と `Polynomial.cyclotomic_prime_mul_X_sub_one` を確認。
前者は prime p の Φp を `∑ i ∈ range p, X^i` とするため、今回の七項式は Φ7 の根条件に対応する。
実際の Polynomial.eval 版は追加せず、今回の Lean 結論は七項の明示式。追加 import の性能比較は実施していない。

Q(sqrt(-3)) と Q(ζ7) の embedding 不可能性は今回の Lean 定理ではない。
将来検討する場合は体構造を別途形式化する課題とする。
