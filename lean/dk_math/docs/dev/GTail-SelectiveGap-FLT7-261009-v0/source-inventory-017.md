# Source inventory 017 — ideal-square support

Date: 2026-10-10 (JST). Initial clean HEAD `d51ce5d48ccf06eaeee84d4bc9bed40caf4e1f5b`, branch `feature/GTail-SelectiveGap-FLT7-261009-v0`. Static-only review016 and reports012/015/016/frontier, current neutral owners and source-only FLT receivers inspected. Step017 only.

## Existing selected element and integral carrier

`TraceOneQuadratic.TraceOneInt (-1)` is the existing integral pair ring, norm:ℤ, ofInt(-1)n=⟨n,0⟩, tau(-1)=⟨0,1⟩ and conjugation⟨f+s,-s⟩. Its product has fst=xf*yf-xs*ys and snd=xf*ys+xs*yf+xs*ys. traceOne_mul_conj and traceOne_norm_mul are the existing element/norm multiplicative identities.

Step012 `gtailSevenNormCoord (a b:ℕ)` uses eisensteinCoord (a:ℤ) (-(b:ℤ)) and equals⟨a,b⟩. `norm_gtailSevenNormCoord` gives cast Q, `norm_gtailSevenNormCoord_sq` gives cast Q² via norm multiplicativity. `dvd_quadratic_iff_dvd_gtailSevenNormCoord` identifies natural q∣Q with integer qcast∣normα. `selectedBody_seven_interior_eq_norm_square` reads the actual selected integer Body as7ab(a+b)*norm(α²); it does not give element reconstruction for arbitrary normQ² values.

Step013 `eisensteinResidueEval` casts signed fst/snd. Its root-guarded multiplicativity and conjugation laws give the actual scalar slot. Canonical ratio uses prime ZMod, q∣Q and q∤b; its q≠3 zero/nonzero distinction is already checked.

## Existing ideal receivers reused

Step014 `eisensteinResidueRingHom t ht`, `eisensteinResidueIdeal t ht`, `mem_eisensteinResidueIdeal_iff`, `norm_cast_eq_eisensteinResidue_product` are the guarded map/kernel/norm-product. `prime_dvd_norm_iff_mem_eisensteinResidueIdeals (hq:Nat.Prime q) t ht z` gives `(q:ℤ)∣norm z ↔ z∈P_t∨z∈P_(1-t)`, requiring a supplied root. `_isMaximal hq t ht` licenses prime membership through existing instances. Canonical `gtailSevenNormCoord_mem_residueIdeal` / `_not_mem_conjugate_residueIdeal` provide the actual natural α orientation.

Step015 `eisensteinResidueIdeals_inf_eq_scalar hq t ht htdiff` equates the INTERSECTION of separated kernels with `eisensteinScalarIdeal q`. `scalar_dvd_traceOne_neg_one_iff n z` and `mem_eisensteinScalarIdeal_iff q z` require both arbitrary integer coordinate divisors. Its product formula is not used to turn mere norm support into scalar divisibility at split primes.

Step016 `eisensteinThreeRoot`, `eisensteinThreeRamifiedIdeal`, `eisensteinThreeGenerator=1+τ=⟨1,1⟩`, norm3, ππ=3τ and τ(1-τ)=1 are checked in the same ring. `mem_eisensteinThreeRamifiedIdeal_iff_dvd z` identifies P=(π) for arbitrary signed z. `eisensteinThreeRamifiedIdeal_mul_self` is P*P=eisensteinScalarIdeal3. This is the actual ramified product gate used for square support.

Targeted comparison with these owners finds base membership/orientation and scalar ideal factorization, but no previous generic norm3-to-embedded3-dividing-z² or oriented split square-address endpoint. New production composes existing APIs rather than duplicating norm, ring, lattice or valuation proofs.

## Exact Mathlib APIs

`Ideal.mul_mem_mul {r s} (hr:r∈I) (hs:s∈J) : r*s∈I*J` in Ideal.Operations: used for actual ideal products, not closure under multiplication inside one ideal.

`Ideal.IsPrime.mem_or_mem (hI:I.IsPrime) : x*y∈I → x∈I∨y∈I` in Ideal.Prime: used after the Step014 checked maximality supplies the prime instance. In a square both disjuncts are the same base membership. `Ideal.mem_span_singleton` gives scalar-principal membership↔embedded scalar divisibility; no confusion with integer norm divisibility.

At3, both addresses in the norm iff coincide after rewriting the membership iff to eval, where1-2=2 has no dependent proof argument. New `three_dvd_norm_iff_mem_ramifiedIdeal` makes this reusable. No invalid kernel proof-term rewrite is needed.

## Carrier distinctions and hypotheses

1. `(q:ℤ)∣norm z` is integer norm-value support and normally gives a disjunction of slots.
2. `z*z∈P_t*P_t` is element membership in an actual ideal square, not equality of its principal ideal with that ideal square.
3. `ofInt(-1)q∣z*z` is ring-element scalar divisibility, equivalently scalar-principal membership requiring BOTH coordinate divisors.
4. Exact ideal-adic exponent (membership inP² but notP³), chosen cyclotomic prime packet, unit-power class and descent are not established.

The generic first square-membership theorem needs no prime/separation. Conjugate exclusion needs prime q and base exclusion but no separation premise itself. The combined scalar exclusion uses the separated intersection equality. Canonical α adapter explicitly uses q-prime Fact, q≠3, q∣Q and q∤b. Ramified generic theorem needs only3∣integer norm, no positivity/natural/Fermat assumptions.

## Optional FLT reader: source-only comparison and omission

Step010 `not_prime_dvd_coordinate_product_of_quadratic` requires prime q, Nat.Coprime a b and q∣Q; focused allocation additionally consumes exact Fermat/sum and positivity for the squared budget. Step011 `prime_square_dvd_gap_of_not_twentyOne` requires positive a,b, primitive pair, Fermat7Equation, sum relation, prime q≠7, q∣Q and21∤q-1, returning q²∣g and q∤GTail.

Atq=3 the latter source contract would yield9∣g, while the neutral adapter gives scalar3∣α² independently. A new conjunction owner would duplicate these receivers without a typed transport between the integral ideal and natural gap factors. It is omitted. These source-only comparisons are not a new FLT-facing compiled theorem or an assumed positive Fermat example.

## Imports and graph

New production imports ONLY `GTailSevenRamifiedThreeIdeal`; it reuses transitive residue/split APIs and Mathlib ideal operations/prime infrastructure. New test imports ONLY new production. Seven public theorems, no new definitions or FLT owner.

Comment-stripped import-header closure: production1368 source names/16 local modules, test1369/17. DFS local union17 vertices: no cycle, neutral closure has zero FLT modules. Evidence `.lake/build/gtail-step017/imports.json`. Counts include external terminals, not build jobs or a complete closure hole/axiom audit.
