# Step 022 — six-coordinate interpolation inventory

Date: 2026-10-10. Branch `feature/GTail-SelectiveGap-FLT7-261009-v0`.
Base HEAD `568d80ffb777f80f4409ef5d237b9be881f0fcbe`.
review-021 / report-021 / source-inventory-021 を確認。review は static inspection、独立 Lean rebuild ではない。

## Original carrier and actual evaluation

`SevenCyclotomicDegreeSixInt.Ring` は既存 `QuadraticAlgebra SevenRealCubicInt (-1) (alpha-1)`。
`coordinates : Ring ≃+ (Fin6 → ℤ)` の順序は
(re.fst,re.snd,re.thd,im.fst,im.snd,im.thd)。inverse は二つの signed triples を再構成。
これは additive equivalence であり、multiplicative compatibility は仮定しない。

既存 `ofReal_alpha` は1+ζ+zetaInv、`zeta_mul_zetaInv=1`、`zeta_pow_seven=1`。
Step019 `evalCyclotomicFromSeventhRoot` の実式は
x0+x1*β+x2*β²+s*(y0+y1*β+y2*β²)、β=1+s+s⁻¹。
source の quadratic sign (-1,alpha−1) と signed triple multiplication を保持。

Step020 は actual root kernel、Step021 は六 admissible powers の injectivity / comaximality。
欠けていたのは all-six vanishing から all-six integer coordinates の零 residue を得る generic reconstruction。
今回その欠落を六係数への integral basis change と degree≤5 root bound で埋める。

## Coefficient candidates and verification plan

instruction の M/N は未証明 candidate として読み、実装では Matrix hierarchy を導入しない。
`sixPowerCoefficients v` の六行が M、`sixPowerCoordinates w` が N に対応する transparent vector maps。
両合成が identity であることを任意 CommRing で fin_cases / ring により証明する。
これにより特徴数によらず復元可能。det M=−1 自体の theorem は実装せず、その値を前提にも使わない。

value identity は s⁻¹=s⁶、七項和零を使う。
補助的な symbolic calculation で差の因子を探索した後、Lean の linear_combination が arbitrary signed coordinates の identity を再検証する。
差は (s⁷−1)*(s⁶*y2+s⁵*x2+2*s*y2+2*x2+y1+2*y2)
+ (1+s+...+s⁶)*(x1+2*x2+y2)。外部計算結果を axiom として使わない。

## Exact Mathlib APIs

- `Polynomial.finsetSum_coeff`, `Polynomial.coeff_monomial`, `Fin.val_inj`：六 monomial coefficients の抽出。
- `Polynomial.natDegree_sum_le_of_forall_le`, `Polynomial.natDegree_monomial_le`：degree bound5。
- `Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero`（Algebra/Polynomial/Roots）：
  polynomial p、injective f:ι→field、全 f(i) での評価零、natDegree p<Fintype.card ι から p=0。
  Step021 `sixSlotRoot_injective` を f に使い card(Fin6)=6 を確認する。
- `ZMod.intCast_zmod_eq_zero_iff_dvd`：signed integer residues と q divisibility の iff。
- `Ideal.mem_span_singleton`, `Ideal.mem_iInf`：scalar membership / all-six membership。
- `coordinates.injective`, `coordinates.apply_symm_apply`：実 quotient coordinates から actual element を作る。
  `coordinates_natCast_mul` は quadratic re/im と real triple mul を使い別途検証。
- `Ideal.isCoprime_iff_sup_eq`, `Ideal.prod_eq_iInf_of_pairwise_isCoprime`（Ideal/Operations）：
  Finset family の pairwise IsCoprime から finite product=bounded iInf。
  univ membership bridge を明示し、intersection gate 成功後に product gate を適用する。

## Existing signed-packet overlap

`SevenRamifiedFusionGlobalOrientedPrimeFactorization` の `cyclicKernel/cyclicConjugateKernel` は
supplied `CyclotomicLinearPrimeAddress p q` の Fin3 phases。
`globalCyclicOrientedFactorIdeal_eq_span_ofReal_load` / `globalOrientedPrimeFactorizationPacket` は
signed routing packet / prime support family / selected load を使った既存 global contracts。
`SevenRamifiedFusionPrimeLoadGlobalFactorization.globalLoadFactorIdeal_eq_span_load` も
selected zeroth gcd load と supplied support family の product contract。
`SevenRamifiedFusionCyclotomicConjugatePrimePair.realPrimeFiberIdeal_eq_conjugateProduct` は
実際に証明された packet-specific real-prime fibre の two-kernel product。
これらを bare-root 六 kernel の equality として利用しない。

## Dependency / proof scope

新 owner は Step021 一 import、新 test はその owner のみ。
old global factorization / packet owners の変更や追加 direct import、new ring / new equivalence、Matrix framework、public facade は不要。
既存 degree-six owner 自体の大きい closure は report の実測件数で区別する。
作業の proof scope は basis identities → value polynomial → root interpolation → scalar lattice → intersection → optional finite product。
全 clean build、recursion-limit 引き上げ、new axiom で gate を代替しない。

三つの scalar ideals は異なる型：ℤ の(q)、degree-two Eisenstein の scalar(q)、今回 degree-six の scalar(q)。
今回の equality は最後の型だけ。class/unit theory、Eisenstein→degree-six map、packet construction、valuation/descent は対象外。
