# MG-004C review and v0 campaign closure

## Verdict

**APPROVED — Outcome A: SQUARE/CORE LANDING ESTABLISHED**

`DkMath.Lib.NumberTheory.TraceOnePowerLanding` correctly adds the final neutral receiver layer planned for the v0 campaign.

The primary theorem

```text
traceOne_sq_core_landing_iff
```

is an exact criterion under `norm beta ≠ 0`:

```text
∃ gamma, alpha = beta * gamma^2
<->
∃ m n,
  (alpha * conj beta).fst = norm beta * (m^2 + s*n^2)
  ∧
  (alpha * conj beta).snd = norm beta * (2*m*n + n^2).
```

The reverse direction reconstructs the square witness and uses the already-approved generic nonzero-norm cancellation theorem.  No square-root provider, UFD/PID assumption, Euclidean-domain infrastructure, or application-specific existence theorem is smuggled into the result.

The norm-power helper is appropriately generic in the exponent, while the main Core-image criterion remains square-specific.  This keeps the substantive theorem concrete without adding a decorative arbitrary-power wrapper.

The regression

```text
(1 : TraceOneInt 0) ∣ ⟨2,0⟩
```

but

```text
¬ ∃ gamma, ⟨2,0⟩ = 1 * gamma^2
```

correctly certifies that integer-lattice landing is strictly weaker than square/Core-image landing.

## v0 campaign status

This closes the planned generic chain as far as current production mathematics supports it:

```text
GN gcd firewall
-> primitive/coprime gauge stage
-> generic transition/path API
-> raw common-scale normalization
-> finite synchronized-refinement transport
-> Norm divisibility receiver
-> coordinate divisibility
-> integer-lattice landing
-> square/Core-image landing
```

The one unresolved structural gap is intentional and already audited:

```text
unconditional concrete primitive-shape GNGaugeTransition provider
```

MG-003C found no such provider in current production.  The q-adic FLT route has the relevant shape but remains conditional/open at the local-to-global integer descent boundary.  Therefore MG-002 remains deferred and no decorative transition provider should be added to this branch.

## Merge boundary

The branch should now be considered **COMPLETE / READY FOR PR TO `develop`**.

At review time it is ahead of `develop` and not behind it.  No further application bridge should be added to this v0 branch.

Future work should begin on a new branch and choose one of two independent directions:

1. **Primitive-provider research** — attack or sharpen a genuine unconditional primitive-shape transition source, with the q-adic reduced-gap/local-to-global boundary as the strongest currently identified candidate.
2. **Application receivers** — reuse the completed neutral lattice/Core receiver in ABC, FLT, Petal, or another application where a factorization packet is already independently supplied.

The first direction closes the missing link in the full MultiGauge chain; the second can already proceed conditionally without changing the generic theory.

## Final decision

No `instruction-009.md` is added on this branch.  Continuing the same branch would mix the completed generic theory with application/provider research and weaken the architectural boundary established by MG-003A through MG-004C.
