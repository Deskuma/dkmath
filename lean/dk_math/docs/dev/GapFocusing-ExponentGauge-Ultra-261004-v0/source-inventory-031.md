# Source inventory 031 - Finite cofactor-window sieve

The live checkout starts clean after committed checkpoint 030. Instruction-031
is the bounded acceptance contract. Earlier modules and reports are reused.

## Existing wheel and reduced-residue receivers

- PrimorialUniverse.FiniteReservationEscape defines IsFinitePrimeBasis,
  finitePrimeBasisProduct and ReservedByPrimeBasis.
- PrimorialUniverse.WheelSurvivor proves
  not_reserved_iff_coprime_finitePrimeBasisProduct. This supplies the thin bridge
  for absolute cofactor-window integers. Its one-period survivor set also
  imposes positivity and q<M; that upper bound is inappropriate for these
  windows, so the exclusion predicate is lifted by coprimality instead.
- WheelProjection defines canonical reduction modulo the product and exact
  enlarged-wheel fibers. Its period-coordinate APIs are not weighted bounds
  for an arbitrary partial cofactor interval.
- Legendre.PrimorialWheelBridge identifies projected square-shell escapes
  under its existing finite-basis coverage hypotheses. It does not bound Q.
- ParitySafeReducedResidue gives carrier-specific reduced quotient intervals.
  Their rough-active hypotheses do not automatically identify the 030 windows.
- ParitySafeMobiusWave.card_filter_coprime_Ioc_eq_sum_moebius_div is an exact
  signed cardinal identity requiring A<=B and M>0. It estimates neither the
  weighted log sum nor the accumulated short-window errors. Reversed windows
  must not be treated as a signed count without that endpoint hypothesis.
- Mathlib finite products/logarithms and coprime_prod_right_iff support the
  weighted carrier inclusion with no distribution premise.

## Chosen receiver

Use the exact 030 endpoints A=max(base/k,width), B=top/k, filtering Icc(A+1,B)
by coprimality with the existing finitePrimeBasisProduct S. Require every basis
element to be prime and <=width. Then filtering this carrier by primality is
exactly gnomonCofactorWindowPrimes. The independent raw log sum contains neither
primality nor carry membership. Cap it by G to retain the previous bound if a
coarse wheel adds too much mass.

The exact nonprime residual is exposed only as an error identity, not used as
a computation oracle in the bound definition. Diagnostics compare bases with
products 6,30,210,2310 where all basis primes satisfy the cutoff hypothesis.
The primary fixed basis is {2,3,5}. No general sieve framework is introduced.
