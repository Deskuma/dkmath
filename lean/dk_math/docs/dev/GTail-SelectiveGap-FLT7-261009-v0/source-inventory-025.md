# Step 025 — exact selected square-depth inventory

Date: 2026-10-10. Branch `feature/GTail-SelectiveGap-FLT7-261009-v0`.
Base HEAD `8dbcac8169005b23f1f370d73e289e71b85ce26a`.
review-024 / report-024 / source-inventory-024 を確認。review は static inspection、独立 build ではない。

## Carrier and preceding contracts

R=`SevenCyclotomicDegreeSixInt.Ring` は既存 quadratic algebra over signed real cubic integers。
coordinates は additive equivalence。今回新 ring/coordinate equivalence は作らない。
Step023 natural F_i の actual element product=GTail と inverse-slot unique incidence を受信。
Step022 actual six-kernel product=(q) は Step024 forward direction 内で利用済み。
Step024 public7 theorems を確認：nonzero scalar injectivity、scalar(q)*K membership iff q² divisibility、
finite excess lemma、inverse-slot product=(q)、excess square⇒scalar product membership、
guarded square exclusion、first-order certificate。
新 reverse proof は maximal kernel saturation が鍵であり、merely prime の unrestricted square cancellation はしない。

## Exact APIs and proof gates

Mathlib `RingTheory/Ideal/Operations.lean` を確認。
`Ideal.IsMaximal.exists_inv_pow (I)[I.IsMaximal] (hx:x∉I) n`:
∃y,∃i∈I^n,y*x+i=1。
その proof は `Ideal.IsMaximal.exists_inv` の actual Bézout witness を取り、幾何 recurrence と
`Ideal.pow_mem_pow` で powered ideal 内の witness を構成する。
この式は principal(x) と I^n の comaximality の具体的証拠であり、domain assumption はない。
`Ideal.IsMaximal.mul_mem_pow I h`: a*b∈I^n ⇒ a∈I ∨ b∈I^n。
proof は上の exists_inv_pow witness を b 倍し、ideal add/mul closure で b membership を示す。
今回その existing theorem を n=2 だけで受信し、hU:U∉J で disjunction の左側を除く。
new generic square-saturation lemma は CommRing/maximal J のみ。unit U、nonprincipal J、zero divisors を排除しない。
`IsCoprime.pow_right` も source確認したが、existing maximal-power saturation が最短。

Gates:
1. generic maximal square saturation を単独 focused build。成功するまで natural factors は追加しない。
2. `Finset.univ.erase i` の五 cofactor factors を unique-slot iff と
   `sixInverseSlot_involutive.injective` で全部 outside selected J とする。
   `Ideal.IsPrime.prod_mem_iff` は prime instance、finite family product membership iff ∃member。
   `Finset.mem_erase` と実際の IsPrime instance で cofactor outside を得る。
   `Finset.prod_erase_mul` と Step023 actual product で U_i*F_i=scalarT。
3. actual RingHom の `map_natCast` / `ZMod.natCast_eq_zero_iff` で scalar q∈J。
   `Ideal.mul_mem_mul`, `pow_two`, `Ideal.mul_mem_left` で q² multiple scalarT∈J²。
   generic square saturation を適用し reverse theorem、Step024 forward proof と合わせ bounded iff。
4. q43 c9 g4 / g1165 の全六 factors を generic theorem で検証し regressions。
5. public axiom/source/import/whitespace checks。

## Old signed-depth overlap

`SevenRamifiedFusionOrientedCarrierValuationOwnership.carrier_mem_orientedKernelPower_iff`
と July30 U1.2 report
`DkMath/FLT/Seven/docs/FLT7-FUSION-004B-U1-2-ORIENTED-CARRIER-VALUATION-OWNERSHIP-REPORT.md`
を comparison-only で確認。旧結果は p.signedDepth carrier と s:p.QuotientPrimeSupport に対する
all-k cutoff、padicValNat(s,Int.natAbs quotientRoot) を扱う。
今回 F_i と旧 signed carrier、bare-root K と旧 oriented kernel、natural GTail と signed quotientRoot の
typed identifications はない。旧 theorem を今回 F_i の証明として直接適用しない。

## Import budget and non-goals

新 owner は Step024 direct import 一つ、新 test は今回 owner 一つ。
existing IsMaximal saturation と ideal finite-product APIs は既に available。
old Domain / oriented valuation / full facade を新 import せず、signed packet synthesis をしない。
process-local LEAN_NUM_THREADS=2 の逐次 focused builds。limit options/clean builds なし。
q|T、q∤c,g を維持した q² level iff に限り、all-k valuations、principalization、units/class、
Eisenstein integral map、primitive tuple/descent は扱わない。
