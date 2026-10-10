# Step 020 — packet-free kernel address inventory

Date: 2026-10-10. Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`.
Base HEAD: `43ecfd6e4f575e376166d7e0195a4f7c625bfd72`.
review-019 / report-019 / source-inventory-019 を確認。review は static GitHub inspection で、独立した Lean 実行証拠ではない。

## Exact owners and overlap

| Owner / source carrier | Existing API | Hypotheses and Step020 reuse |
| --- | --- | --- |
| `GTailCyclotomicLocalEval` / actual degree-six ring | `evalRealFromSeventhRoot`, `evalCyclotomicFromSeventhRoot`, zeta/ofReal/cast endpoints | `[Fact (Nat.Prime q)]`, scalar r≠0、r⁷=1、r≠1。bare-root kernel の評価として直接使用 |
| same owner / natural Tail factor | `gtailCyclotomicLinearFactor`, `gtailCyclotomicEval`, `gtailCyclotomicLinearFactor_mem_ker` | q∤c,g、q|T。F=(c+g)−ζ*c の canonical-root membership を再利用 |
| `GTailSevenPairedResidue` / scalar finite field | `gtailSevenTailRatio`, pow_seven/ne_one/ne_zero | natural r=(c+g)/c の admissibility。新しい order3/7 proof を作らない |
| `CyclotomicLinearPrimeAddress` / actual degree-six ring | `eval`, `evalKernel`, `mem_evalKernel_iff`, `eval_surjective`, `evalKernel_isMaximal`, `evalKernel_comap_ofReal`, `evalKernel_comap_intCast`, `evalKernel_cardQuot` | `p : RamifiedSignedRootRoutingPacket`、`a.quotientAddress : p.signedDepth.QuotientPrimeMuSevenAddress q`。旧 API は bare-root input を受け取らない。既存 proof pattern を別 input contract で検証 |
| `SevenRamifiedFusionGlobalOrientedPrimeFactorization` / same packet-specific ring | `rotateHom`, `rotateEquiv`, `cyclicEval`, `cyclicKernel`, `cyclicConjugateEval/Kernel`, real contraction and phase transport theorems | supplied `CyclotomicLinearPrimeAddress p q` の三 real-Galois phases と conjugate orientations。今回その hierarchy、ideal powers、product を構築しない |
| `GTailSevenResidueIdeal` / **different** `TraceOneInt (-1)` | `eisensteinResidueIdeal`, `eisensteinResidueRingHom`, kernel membership | t²−t+1=0 を必要とする degree-two map。共通 ZMod q から degree-six ideals に transfer しない |

## Coordinate and prime-kernel APIs

Degree-six source は `QuadraticAlgebra SevenRealCubicInt (-1) (alpha-1)`。
`zeta=⟨0,1⟩`、`ofReal` は existing algebraMap。
base alpha³=2alpha²+alpha−1、ζ²=−1+(alpha−1)ζ、ζ⁷=1。
Step019 の signed coordinate evaluation は x0+x1*β+x2*β²、β=1+r+r⁻¹、
degree-six value は evalReal(re)+r*evalReal(im)。今回 source definitions は変更しない。

Mathlib 実 API を確認し利用：
- `RingHom.mem_ker`, `RingHom.ker_isMaximal_of_surjective`（Ideal/Maps）、IsMaximal.isPrime。
- `Ideal.mem_comap`, `Ideal.mem_span_singleton`、`ZMod.intCast_zmod_eq_zero_iff_dvd`。
- `ZMod.natCast_zmod_val` は q-prime Fact から供給される NeZero q の下で val representative を復元。
- `Submodule.cardQuot_apply`, `RingHom.quotientKerEquivOfSurjective`, `Nat.card_congr`, `Nat.card_zmod` は旧 packet quotient proof と同じ実 API。
- `eq_div_iff` と `ZMod.natCast_eq_zero_iff` は c-unit cancellation。
- Optional comparison の unit inverse / scalar inverse coercion を確認。`Units.val_inv_eq_inv_val` も実ソースを確認したが、この ZMod の beta 展開は定義的に一致し、その rewrite は不要だった。

## Minimal direct import graph

production `GTailCyclotomicPrimeAddress` → `GTailCyclotomicLocalEval` 一 import。
必要な Mathlib ideal/card APIs はこの既存 closure で供給される。
production から old linear-address/global-oriented owners への追加直接 import はない。
test は新 owner、既存 ramified q7 owner、旧 linear-address owner を import。
最後の import は supplied actual packet address 上の extensional comparison example のみ。
full Seven facade は使用しない。Step019 neutral trace module から FLT への逆依存は追加しない。
closure / cycle の実測値は report に記録する。

## Optional comparison boundary

旧 a を実際に引数として渡す一般 example で、その canonical scalar ratio を新評価の r として指定する。
β の unit-inverse/scalar-inverse 一致を確認して RingHom ext equality を検証する。
この example は q43 tuple から packet を構成しない。旧 evalKernel との equality を別 public theorem として追加していない。
optional natural T⇔r⁷=1 converse は今回実装・検証しない。唯一性には不要。

Unsupported: distinct source rings の embedding、Eisenstein ideal transfer、全 prime ideals の分類、
六 kernel product、ideal valuations、class group、unit-power extraction、primitive next tuple と descent。
