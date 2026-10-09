# Source inventory 016 — ramified three principal kernel

Date: 2026-10-10 (JST). Initial clean HEAD `b4543fe0c6383899be70ecb3d05f0b2542fedabe`, branch `feature/GTail-SelectiveGap-FLT7-261009-v0`. Static-only review015, report/inventory015 and actual source APIs inspected. Step016 only.

## Existing ring, signs and residue contracts

`NumberTheory.TraceOneQuadratic.TraceOneInt s` has fst/snd:ℤ. `ofInt s n=⟨n,0⟩`, `tau s=⟨0,1⟩`, `mul x y=⟨xf*yf+s*xs*ys,xf*ys+xs*yf+xs*ys⟩`, `conj x=⟨xf+xs,-xs⟩`, `norm x=xf²+xf*xs-s*xs²`. Coordinate projection lemmas and traceOne_ext expose the implemented ring. At s=-1 the relation is τ²=τ-1, not the alternate τ²=-τ-1 convention. New π=1+τ has literal pair⟨1,1⟩, norm3 and conj⟨2,-1⟩.

Step014 `eisensteinResidueRingHom {q} t ht` and `eisensteinResidueIdeal t ht` are the actual map/kernel in this integral ring. `mem_eisensteinResidueIdeal_iff t ht z` is membership↔eval t z=0; Step013 `eisensteinResidueEval t z` casts signed integral fst/snd to ZMod q. Its add/mul/conj laws are unchanged. The root proof `(2:ZMod3)^2-2+1=0` is now a public small computation; P is the existing kernel specialized to it.

Step015 `eisensteinScalarIdeal q := Ideal.span {ofInt(-1)(q:ℤ)}` supplies the correct scalar principal ideal, and `mem_eisensteinScalarIdeal_iff q z` requires both integer coordinate divisors. Its split inf/product require separated roots; they are NOT used to infer this repeated-root product. The new source does not invoke mul_eq_inf_of_coprime.

## Existing lattice landing and overlap

`TraceOneLatticeLanding.traceOne_dvd_iff_norm_dvd_mul_conj_coordinates {s:ℤ} {alpha beta:TraceOneInt s} (hNorm:norm beta≠0)` gives beta∣alpha iff norm beta divides both coordinates of alpha*conj beta. We import and reuse this exact kernel at beta=π and alpha=z, with normπ=3 and explicit3≠0. No norm-to-element converse is assumed.

The coordinate calculations at beta=π give fst(z*conjπ)=2*z.fst+z.snd and snd=-z.fst+z.snd. Both3-divisors are equivalent to3∣z.fst-z.snd: the second is the negative of the difference, and the first is3*z.fst-(z.fst-z.snd). Thus the old nonzero-norm quotient reconstruction proves π∣z for arbitrary signed z.

`EisensteinLatticeLanding.eisenstein_dvd_iff_norm_dvd_conjugate_coordinates {a b c d:ℤ} (hbeta:eisensteinCoord c d≠0)` supplies the same precise lattice condition in eisensteinCoord(m,n)=⟨m,-n⟩ signs. At our π its second Eisenstein coordinate is-1, not+1. Its norm-only nondivisibility countercheck remains unchanged. Source-only inspection avoids an unnecessary extra owner import.

Targeted ramified/three/principal searches in the neutral Eisenstein and TraceOne owners found no prior common-kernel principal equality or P²=(3) endpoint. The generic norm/lattice APIs already provide the algebraic foundation and are reused. No new order, PID/UFD or field-classification hierarchy is introduced.

## Exact Mathlib ideal APIs

`Ideal.mem_span_singleton {x y}` under CommSemiring gives x∈span{y}↔y∣x. Ideal extensionality then gives P=span{π} from the full arbitrary-element iff.

`Ideal.span_singleton_mul_span_singleton (r s)` requires the usual two-sided span instance and gives span{r}*span{s}=span{r*s}. The existing commutative ring supplies the instance. `Ideal.span_singleton_le_span_singleton` is span{x}≤span{y}↔y∣x. We prove both inclusions for span{ππ}=span{scalar3} using integral witnesses τ and1-τ.

The also-inspected `Ideal.span_singleton_eq_span_singleton` API requires IsDomain and Associated; we do not need a new domain/unit instance because the two direct inclusions suffice. No coprime product=intersection theorem is consumed.

`CharP.intCast_eq_zero_iff (ZMod3)3(z.fst-z.snd)` translates the kernel congruence to integral divisibility. A typed intermediate iff normalizes natural-cast3 versus literal integer3 before rewriting. At root2=-1 the evaluation is fst-snd. This is not a natural-coordinate-only argument.

## Ownership, imports and graph

New production imports only `GTailSevenSplitIdeal` (scalar ideal/existing residue owners) and `TraceOneLatticeLanding` (generic quotient criterion). Test imports only the new production. Two definitions and15 public theorems. No FLT owner or facade addition.

Principal-kernel equality was compiled before the ideal-product stage. Exact root/generator/unit identities use small decide computations; generic kernel and ideal statements use lattice/divisibility/extensionality, not finite enumeration of elements.

Comment-stripped import-header closure: production1367 source names/15 local modules, test1368/16. DFS local union16 vertices: no cycle. Neutral closure has no FLT module. Evidence `.lake/build/gtail-step016/imports.json`; source counts include external terminals and are not build jobs or a closure-wide axiom audit.

Historical q=3 intersection failure remains true while the separately checked product now succeeds. Step015 q=43 split and q=5 inert calibrations are replayed unchanged. No q-general ideal valuations, cyclotomic maps, norm-square inversion or descent contracts are supplied.
