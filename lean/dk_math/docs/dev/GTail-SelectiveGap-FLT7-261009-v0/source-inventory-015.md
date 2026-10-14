# Source inventory 015 — split scalar-prime ideals

Date: 2026-10-10 (JST). Initial clean HEAD `ecbb96c9dfbb086f17bbc4eac94e6fda2d435836`, branch `feature/GTail-SelectiveGap-FLT7-261009-v0`. Static-only review014, report/inventory014, prior012–013 frontier and actual current APIs inspected. Step015 only.

## Existing carriers and reused maps

`TraceOneQuadratic.TraceOneInt (-1)` is the existing integral pair ring with fst/snd:ℤ. `ofInt s n=⟨n,0⟩`, `tau s=⟨0,1⟩`, `traceOne_ext` is coordinate extensionality; fst/snd_mul expose the actual scalar product. `conj`, `norm`, `traceOne_mul_conj`, `traceOne_norm_mul` remain unchanged. Step012 α is a natural-coordinate specialization of this integral carrier, not its full set of elements.

Step014 `eisensteinResidueRingHom {q} t ht : TraceOneInt(-1) →+* ZMod q` requires ht:t²-t+1=0. `_apply` is definitionally Step013 `eisensteinResidueEval t z`; `_ofInt` maps integral scalars to their casts, `_tau` maps the generator to t. `eisensteinResidue_conjugate_root t ht` supplies the1-t proof. `eisensteinResidueIdeal t ht : Ideal (TraceOneInt(-1))` is RingHom.ker, and `mem_eisensteinResidueIdeal_iff` exposes zero evaluation. `_isMaximal hq t ht` reuses the proved surjection and prime-field codomain. Step014 canonical orientation uses natural Q, b-unit and q≠3, but does not cover arbitrary integral z.

Step013 `eisensteinResidueEval` is fst cast+snd cast*t; its zero/conjugate/nonzero receivers and canonical ratio use natural coordinates. `scalar_dvd_gtailSevenNormCoord_iff` concerns only α(a,b): natural q,a,b. New scalar criterion is therefore required for arbitrary signed z (and is stated even for arbitrary n:ℤ). Its proof uses explicit integral quotient pairs, not a new lattice hierarchy.

## Existing lattice and residue overlap

`TraceOneLatticeLanding.traceOne_dvd_iff_norm_dvd_mul_conj_coordinates` handles arbitrary parameter s and beta∣alpha under norm(beta)≠0, via BOTH conjugate-product coordinates. `traceOne_dvd_imp_norm_dvd_norm` is only necessary. `EisensteinLatticeLanding.eisenstein_dvd_iff_norm_dvd_conjugate_coordinates` has beta≠0 and the explicit two polynomial-coordinate divisors; the existing norm-only counterexample remains relevant. Targeted scalar/ofInt/splitting searches found no arbitrary scalar pair iff or the chosen-root ideal intersection/product already implemented. Old lattice kernels are inspected, not imported or modified.

`NumberTheory.TraceOneResidueType.residueMap (s:ℤ) (q:ℕ)` has codomain QuadraticAlgebra (ZMod q) (s:ZMod q)1 and retains both residue coordinates. Existing split/ramified predicates and Mathlib QuadraticAlgebra.lift describe roots/reduction; they do not already provide this integral ideal intersection. No additional composed map, new ring of integers or cyclotomic carrier is introduced.

## Exact Mathlib ideal APIs

Source-inspected declarations:

- `Ideal.mem_span_singleton {x y : α}` under CommSemiring: x∈span{y} ↔ y∣x. Orientation is the embedded scalar divides z.
- `Ideal.mem_inf`: membership is conjunction; ideal extensionality applies to ALL integral z.
- `CharP.intCast_eq_zero_iff (ZMod q) q z.fst/snd` connects integer-coordinate cast zero to `(q:ℤ)` divisibility. `ZMod.natCast_eq_zero_iff 3 q` is used separately for the prime-three exception.
- `ZMod.intCast_surjective` chooses an integral representative n of a residue root. The witness tau(-1)-ofInt(-1)n distinguishes the kernels by actual membership, not merely by differing values of homs at tau.
- `Ideal.isCoprime_of_isMaximal [I.IsMaximal] [J.IsMaximal] (ne:I≠J) : IsCoprime I J` in Ideal.Operations; `.sup_eq` gives I⊔J=⊤.
- `Ideal.mul_eq_inf_of_coprime (h:I⊔J=⊤) : I*J=I⊓J` in the same module. Its orientation is product-to-inf, then the proved inf-to-scalar equality. No hand-waved ideal factorization or missing comaximality premise.

## Generic and exception contracts

Main reconstruction/inf/product APIs take prime hq, a supplied root ht and explicit `htdiff:t≠1-t`. They never assert root existence. Arbitrary signed integral z is used in reconstruction, and the scalar quotient criterion permits negative/zero n. The principal scalar ideal is existing Ideal.span{ofInt(-1)(q:ℤ)}.

A separate root-separation theorem proves q≠3 implies htdiff using4(t²-t+1)=(2t-1)²+3, then q∣3 and primality. No q≠7/oddness/natural-coordinate/FLT assumptions occur. A small product adapter consumes q≠3 and this checked separation. Distinct kernels themselves need no prime assumption once a root and htdiff are supplied; their witness uses integer-cast surjectivity. Comaximality and product additionally use prime-field maximality.

At q=3, t=2=1-t and z=⟨1,1⟩ lies in both kernels but is not scalar-divisible by3: the intersection formula without separation is false. This does not refute the standalone product formula at q=3; no ramified square formula is claimed. q=5 has no root, confirmed by a small finite test.

## Imports, stages and graph

Production imports only `GTailSevenResidueIdeal` and `Mathlib.RingTheory.Ideal.Operations`. Operations was already in the Step014 source closure; its direct import documents the APIs actually consumed. Test imports only the new production. One definition and9 public theorems; no FLT owner/facade/root driver addition.

Intersection was built successfully before adding the distinctness/comaximality/product gate; the completed production was rebuilt successfully. Comment-stripped import-header traversal: production1365 source names/13 local modules, test1366/14. DFS local union14 vertices finds no cycle, and neutral closure has no FLT modules. Evidence `.lake/build/gtail-step015/imports.json`; external terminals are included, counts are not build jobs or a global hole audit.
