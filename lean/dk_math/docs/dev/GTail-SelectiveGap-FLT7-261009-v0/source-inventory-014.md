# Source inventory 014 — bundled residue kernels

Date: 2026-10-10 (JST). Initial clean HEAD `622961480df6f99d7d51b6a4cb3a700cbd334d1d`, branch `feature/GTail-SelectiveGap-FLT7-261009-v0`. Review 013 (static-only approval), report/source-inventory 013, Steps 010–012 frontier statements and actual source APIs inspected.

## Existing integral carrier and norm

`DkMath.NumberTheory.TraceOneQuadratic.TraceOneInt (-1)` is the implemented integral pair ring. `ofInt s n=⟨n,0⟩`, `tau s=⟨0,1⟩`, `conj z=⟨z.fst+z.snd,-z.snd⟩`, `norm z=z.fst²+z.fst*z.snd-s*z.snd² : ℤ`. `traceOne_mul_conj z` gives the element equation z*conj z=ofInt s (norm z); `traceOne_norm_mul` gives norm multiplicativity. fst/snd zero/one/add/mul lemmas expose the existing coordinates. No new ring or norm is defined.

Step 012 `gtailSevenNormCoord a b` uses eisensteinCoord (a:ℤ) (-(b:ℤ)); `gtailSevenNormCoord_eq` identifies it with ⟨a,b⟩. `norm_gtailSevenNormCoord` and `dvd_quadratic_iff_dvd_gtailSevenNormCoord` connect natural Q and the integer norm value. They do not assert ring-element divisibility.

## Existing root evaluation and lattice boundary

Step 013 `eisensteinResidueEval {q} t z : ZMod q` casts integral fst/snd and reads fst+snd*t. `eisensteinResidueEval_add` holds for every parameter; `eisensteinResidueEval_mul` needs t²-t+1=0; `eisensteinResidueEval_conj` replaces t by1-t. These laws are reused verbatim by the new bundled map.

`gtailSevenResidueRoot q a b [Fact (Nat.Prime q)]` is -a/b. `gtailSevenResidueRoot_polynomial hQ hb` and its conjugate variant supply the guarded root proofs under q∣Q and ¬q∣b. `eisensteinResidueEval_gtailSevenNormCoord_zero hb`, `_conjugate hb` (value2a+b), `_conjugate_ne_zero hq3 hQ hb`, and `gtailSevenResidueRoot_ne_conjugate` supply the orientation. The nonzero/distinctness statements need q≠3; root and first-slot constructions do not.

`scalar_dvd_gtailSevenNormCoord_iff q a b` requires both coordinate divisors, even q=0. Existing `TraceOneLatticeLanding.traceOne_dvd_iff_norm_dvd_mul_conj_coordinates` requires norm(beta)≠0 and both conjugate-product coordinates divisible by norm(beta). `traceOne_dvd_imp_norm_dvd_norm` is necessary only. `EisensteinLatticeLanding.eisenstein_dvd_iff_norm_dvd_conjugate_coordinates` uses beta≠0, and `eisenstein_norm_divisibility_not_sufficient` is an existing norm-only counterexample. These owners are source-inspected only, not imported into the new module.

## Composition overlap and chosen implementation

`NumberTheory.TraceOneResidueType.residueMap (s:ℤ) (q:ℕ) : TraceOneInt s →+* QuadraticAlgebra (ZMod q) (s:ZMod q) 1` retains both reduced coordinates, with `residueMap_surjective` and `residue_discr`. It imports `Lib.NumberTheory.QuadraticResidueType`, whose Split/Inert/Ramified are two distinct/no/unique roots of r²=a+b*r. Its classification is not an ideal-factorization theorem. At s=-1 the polynomial relation is the same one, including the repeated-root characteristic-three boundary.

Mathlib `QuadraticAlgebra.lift : {u : A // u*u=a•1+b•u} ≃ (QuadraticAlgebra R a b →ₐ[R] A)` evaluates re•1+im•u. With R=A=ZMod q, s=-1 and the supplied root, its scalar evaluation composed with residueMap can represent the same coordinate function. No already-composed Step 013 chosen-root map was found by targeted residueMap/comp/lift search.

The chosen implementation packages the already checked Step 013 laws directly. Its function agrees **definitionally** with eisensteinResidueEval (`eisensteinResidueRingHom_apply := rfl`). This avoids redoing the multiplication proof and avoids importing the broader residue/classification owners. Static import closure of the new direct module is1364 names; union with the existing residueMap owner's closure would be1684 (320 extra, including2 local owners). This is a hypothetical source-dependency comparison, not a build/performance result or a checked composition implementation. Thus composition does not supply a smaller dependency path in this checkout.

## Mathlib kernel, casts and maximality APIs

`Mathlib.RingTheory.Ideal.Maps` supplies `RingHom.ker f : Ideal R` as comap f ⊥ and `RingHom.mem_ker : r∈ker f ↔ f r=0`. The new ideal is precisely this kernel. `RingHom.map_mul` transports the existing z*conj z equality. `CharP.intCast_eq_zero_iff (ZMod q) q (norm z)` connects residue cast zero with `(q:ℤ)∣norm z`, in the reverse rewrite direction used by the new criterion. This is the integer norm, not a natural cast shortcut.

`ZMod.intCast_surjective` gives an integer representative of every residue, used with ofInt to prove the new hom surjective without prime assumptions. `RingHom.ker_isMaximal_of_surjective f hf` needs a DivisionRing codomain; under Nat.Prime q the existing ZMod field instance supplies it. The optional maximality theorem is separately compiled; a q=43 test installs it as an instance and obtains IsPrime via the existing IsMaximal instance API.

## New owners and graph

Production direct imports: `DkMath.Lib.NumberTheory.GTailSevenEisensteinResidue` and `Mathlib.RingTheory.Ideal.Maps`. Test imports only the new production module. Two definitions,14 public theorems; no FLT owner is created.

Comment-stripped import-header traversal across current local/Mathlib sources and external terminals: production1364 names/12 local modules, test1365/13. DFS local union13 vertices: no cycle. Neutral closure: zero FLT modules. Evidence `.lake/build/gtail-step014/imports.json`; source counts are not build jobs or a complete closure axiom audit.

Root proof parameter is required for every hom/kernel; root existence for arbitrary q is not inferred. Norm-product and hom/surjection/scalar membership are not prime-dependent. Prime norm-divisor disjunction and maximality are prime-dependent. Canonical orientation additionally needs q∣Q, b-unit and (for conjugate exclusion/distinctness) q≠3. No principal ideal product, unit class, cyclotomic transfer or descent map is supplied.
