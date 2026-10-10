# Step 026 — formal GTail shell derivative inventory

Date: 2026-10-10. Branch `feature/GTail-SelectiveGap-FLT7-261009-v0`.
Base HEAD `ef7ee2d424f1862fd4029f98d5f49e6ddd096247`.
review-025 / report-025 / source-inventory-025 を確認。review は static inspection、独立 rebuild ではない。

## Existing carrier and exact native shell

Actual source R は既存 degree-six quadratic algebra over SevenRealCubicInt。
F_h(c,g)=(c+g:R)−ζ^(h+1)*c、U_i は Finset.univ.erase i の五 factors の actual R product。
Step025 cofactor nonmembership、source cofactor*factor=GTail、selected square iff を保持。
Step023 arbitrary X,Y:R の homogeneous value identity と natural GTail shell を確認。
`GTail_one_eq_GTailCyclotomicShell` は CommSemiring recurrence identity、g=0 も含む。
新 polynomial は exactly Σ j:Fin7,X^(6-j.val)*C(c^j.val)（degree6）。
その eval を Step023 natural homogeneous sum と結び、original GTail への cast equality を証明する。
formal derivative は X に関する Polynomial.derivative、c は定数。

## Exact Mathlib names and smallest proof gates

`Mathlib.Algebra.Polynomial.Derivative` を targeted direct import。
`Polynomial.derivative_mul`, `derivative_pow`, `derivative_X_sub_C`,
`derivative_prod_finset`, `eval_multiset_prod_X_sub_C_derivative` を source確認。
`Polynomial.eval_finsetSum`（old eval_finset_sum alias は deprecated）、eval_prod、eval_mul、eval_sub、eval_C、eval_X、
`Polynomial.evalRingHom`, C_pow、C_mul、C_ofNat は typed constants / evaluation 用。

Phase1: formal shell polynomial eval/natural cast、(X-Cc)*shell=X⁷-C(c⁷) は Fin7 expansion/ring。
congrArg Polynomial.derivative に derivative_mul/pow を適用して shell+(X-Cc)*shell'=7X⁶。
Tail support で eval shell=0、x=c+g に specialization して g*eval shell'=7*x⁶。
この段階で g の division はしない。

Phase2: source value identity in R を Polynomial(ZMod q) identity として直接 rewrite しない。
Step023 private `product_of_geom` の checked algebraic certificate は generic CommRing だが private。
public endpoint は actual R 固定。旧 owner の編集禁止を守り、同 certificate を新 owner の private generic helper として
再検証し、A=Polynomial(coefficient ring)、z=C(s)、X=Polynomial.X、Y=C(c) と型を明示して適用する。
これにより genuine polynomial shell=∏(X-C(s^(h+1)*c)) を一般 coefficient ring で証明。
certificate のコピーは新 axiom ではなく独立 Lean recheck。大きい cyclotomic/field owner の追加 import は不要。

selected s=sixSlotRoot r (sixInverseSlot i)。七項和零は Step018 の supplied root theorem。
actual factor membership からその factor polynomial の eval zero を typed RingHom formula で得る。
`Finset.prod_erase_mul` で selected linear polynomial を isolate、derivative_mul と derivative_X_sub_C を適用。
その因子の eval zero と derivative1 により eval shell' は五他因子の値の積。
actual evalCyclotomicFromSeventhRoot(U_i) も RingHom map_prod / actual factor evaluation で同じ積になる。
この matching は derivative-of-product theorem の special factorization case であり、membershipだけからの仮定ではない。

Phase3: g-unit による division、uniform formula。
非identity seventh root は q≠7 を含意する。ZMod7 の universally checked s⁷=s と hr7/hr1 による contradiction を使う。
prime q の7 divisibility iff で (7:ZModq)≠0。cとgの unit guards、r*c=c+g で endpoint非零。
式から cofactor residue非零を証明。Step025 nonmember theorem は再定義せず比較する。

## Derivative overlap and exclusions

Existing `CosmicDerivativePolynomial` は real polynomial HasDerivAt の analytic bridge。
`CosmicDerivativePower.powerKernel_eq_GN_swap` / `sub_pow_eq_u_mul_powerKernel` は real finite difference/GN compatibility。
`CosmicFormulaDerivativeBridge` は real quadratic cosmic-unit reconstruction。
これらは finite-field formal shell/cofactor API ではなく、Mathlib umbrella/analysis owners の追加 import はしない。
neutral Lib derivative owner は今回不要。new direct owner import は Step025 plus Polynomial.Derivative のみ。

## Scope and budget

q-prime、q∤c,g、q|T を canonical ratio branch の theorem に維持。
formal polynomial identities は arbitrary CommRing で成立、zero endpointsも含む。
q²|T は derivative nonzero を妨げないが、simple mod-q root から ideal-square exclusion を推論しない。
Step025/024 を sequential focused regression、process-local LEAN_NUM_THREADS=2。
new all-k valuation/Hensel/unit/class/packet/descent APIs、旧 source owner/facade編集、resource-limit option は対象外。
