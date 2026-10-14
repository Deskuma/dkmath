# Source inventory 013 — Eisenstein residue orientation

Date: 2026-10-10 (JST). Initial clean HEAD `728922b30389fc19203f662b86887535390c2683`, branch `feature/GTail-SelectiveGap-FLT7-261009-v0`. Review 012 (static approval), reports 012/011 and live sources inspected. Step 013 only.

## Carriers and existing symbols

`DkMath.NumberTheory.TraceOneQuadratic.TraceOneInt s` has integral fst/snd. Its implemented product is ⟨xf*yf+s*xs*ys, xf*ys+xs*yf+xs*ys⟩; `fst_mul`, `snd_mul`, `traceOne_ext` expose coordinates. `ofInt s n=⟨n,0⟩`, `conj x=⟨xf+xs,-xs⟩`, `norm x=xf²+xf*xs-s*xs²`. `traceOne_mul_conj x` is x*conj x=ofInt s (norm x), an element equality. `traceOne_norm_mul` is the existing multiplicative integer norm equality.

`Lib.NumberTheory.EisensteinCoordinates.eisensteinCoord m n=⟨m,-n⟩`; `norm_eisensteinCoord` gives m²-mn+n² and `norm_eisensteinCoord_mul_sq` supplies the existing element-factor norm readout. Step 012 `gtailSevenNormCoord a b` reverses the second argument sign to get ⟨a,b⟩. `gtailSevenNormCoord_eq`, `norm_gtailSevenNormCoord`, `dvd_quadratic_iff_dvd_gtailSevenNormCoord` are reused directly; no ring/norm modification.

## Lattice overlap and why the scalar adapter is small

Existing `TraceOneLatticeLanding.traceOne_conj_coordinates s c d` gives the literal conjugate; `traceOne_dvd_iff_norm_dvd_mul_conj_coordinates {s} {alpha beta}` requires norm beta≠0 and equates beta∣alpha with norm beta dividing both coordinates of alpha*conj beta. `traceOne_dvd_iff_polynomial_norm_dvd_mul_conj_coordinates` expands those coordinates. `traceOne_dvd_imp_norm_dvd_norm` is only the necessary forward norm condition.

`EisensteinLatticeLanding.eisenstein_dvd_iff_norm_dvd_conjugate_coordinates {a b c d : ℤ}` requires eisensteinCoord c d≠0 and uses norm(beta)∣(ac-ad+bd) and norm(beta)∣(bc-ad). Its `_via_generic` variant derives the same condition through the general TraceOne criterion; `_polynomial_` spells out c²-cd+d². `eisenstein_dvd_imp_norm_dvd_norm` is forward only. `eisenstein_norm_divisibility_not_sufficient` is the already established nonscalar example beta=eisensteinCoord(-2)1, alpha=eisensteinCoord(-1)2.

No existing exact scalar q/natural-input α iff was found by targeted ofInt/dvd/scalar search. New `scalar_dvd_gtailSevenNormCoord_iff` is a concrete Step 012 adapter: project a scalar quotient witness to the two coordinates and reconstruct its integral pair in reverse, using `Int.ofNat_dvd`. It covers q=0 too; no nonzero-divisor hypothesis or general lattice reconstruction API is duplicated. The old lattice owners are inspected but not imported because this direct scalar proof does not require their more general nonzero-norm kernel.

## Residue overlap and receiver differences

Targeted TraceOne/ZMod/root-evaluation searches found `NumberTheory.TraceOneResidueType.residueMap (s:ℤ) (q:ℕ) : TraceOneInt s →+* QuadraticAlgebra (ZMod q) (s:ZMod q) 1`. It retains both reduced coordinates; `residueMap_surjective` and `residue_discr` support its existing field/split/ramified classification. `Lib.NumberTheory.QuadraticResidueType.Split` asserts two distinct roots of r²=a+b*r, `Inert` no root, `Ramified` a unique root. Mathlib `QuadraticAlgebra.lift` packages evaluation at a supplied relation into an algebra hom.

The new receiver is an unbundled scalar evaluation `(z.fst:ZMod q)+(z.snd:ZMod q)*t`, with addition and relation-guarded multiplication proved from existing coordinates. It does not recreate the coordinate-reduction RingHom or classification hierarchy; no existing chosen ratio/evaluation endpoint for Step 012 α was found. Those broader owners were source-inspected only. Full RingHom packaging is optional and omitted.

`Mathlib.Algebra.Field.ZMod` supplies `Field (ZMod q)` under `Fact (Nat.Prime q)`; `ZMod.natCast_eq_zero_iff n q` identifies natural cast zero with q∣n. `Mathlib.Tactic.FieldSimp` clears the denominator under explicit b≠0, and `LinearCombination` proves coordinate polynomial identities. Natural coordinates use Int.cast_natCast; negative conjugate coordinates use Int.cast_neg. No internet/corpus proof search is needed.

## Prior FLT support and dependency direction

Step 010 `FLT.Seven.not_prime_dvd_coordinate_product_of_quadratic` requires prime q, Nat.Coprime a b and q∣Q, and derives ¬q∣a*b*(a+b). Step 011 `twentyOne_dvd_prime_sub_one_of_focused_tail` additionally requires exact Fermat7Equation, sum relation, q≠7 and tail support; it derives b-unit locally. Its neutral `three_dvd_prime_sub_one_of_quadratic` uses q≠3 and both coordinate units. These sources were inspected, not imported into the new neutral owner.

Step 012 `focused_gtail_eq_norm_square` casts the natural exact focused product; it supplies no residue orientation or element-square reconstruction. Step 013 does not alter it. No optional FLT adapter is added: the neutral theorem already exposes the exact b-unit assumption, while the prior owner shows how to recover it. An adapter would be an input-presentation connection, not new FLT arithmetic.

## New imports and exact graph audit

Production imports only GTailSevenNormReadout, Mathlib.Algebra.Field.ZMod, Mathlib.Tactic.FieldSimp and Mathlib.Tactic.LinearCombination. Test imports only this new neutral module. Comment-stripped header traversal (ordinary/public/private/meta imports; installed Mathlib sources and external terminals) yields 1198/1199 source names and 11/12 local DkMath/DkMathTest modules. DFS over the local union's 12 vertices finds no cycle; neutral closure has zero FLT modules. Evidence `.lake/build/gtail-step013/imports.json`. These counts are source names, not build jobs or a closure-wide sorry audit.

Prime-field instance is needed for the ratio and denominator arguments. q∤b is essential for root extraction; q≠3 is used only for conjugate-slot nonzero/distinctness. Generic eval add/mul/conj need no primality (mul needs the polynomial relation). Scalar divisibility and conjugation have no prime/unit premises. All new public signatures and checks are in report-013.
