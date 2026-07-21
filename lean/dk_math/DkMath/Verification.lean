/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

-- Explicit finite collisions and their generic logical consequences.
import DkMath.Verification.Collision

#print "file: DkMath.Verification"

/-!
# DkMath verification certificates

`DkMath.Verification` is the public entry point for reusable verification
certificates extracted from concrete mathematical case studies.

The central design principle is to separate two layers:

1. a domain-specific layer that constructs explicit witnesses, and
2. a domain-independent layer that derives generic logical consequences from
   those witnesses.

This separation allows a concrete verification project to expose a small,
auditable certificate without forcing downstream users to import the entire
domain implementation.

## Public API

The current public surface provides collision certificates:

* `DkMath.Verification.CollisionCertificate`
* `DkMath.Verification.CollisionCertificate.notInjective`
* `DkMath.Verification.CollisionCertificate.noLeftInverse`

A `CollisionCertificate f` records two distinct inputs having the same image
under a function `f`.

From that finite witness alone, the library derives:

* `f` is not injective;
* `f` admits no set-theoretic left inverse.

## Verification pattern

A domain adapter typically follows this pattern:

```lean
def domainCertificate :
    DkMath.Verification.CollisionCertificate f :=
  {
    left := x₁
    right := x₂
    left_ne_right := by
      ...
    map_eq := by
      ...
  }

theorem domain_notInjective :
    ¬ Function.Injective f :=
  domainCertificate.notInjective

theorem domain_noLeftInverse :
    ¬ ∃ g, Function.LeftInverse g f :=
  domainCertificate.noLeftInverse
```

The expensive or domain-specific work is concentrated in the construction of
`domainCertificate`. The consequences are then obtained from the generic
verification layer.

## Applications

The first public application is the three-variable Jacobian verification
package in:

`DkMath.Hackathon.JacobianCounterexample3`

That package constructs an explicit collision for its normalized polynomial
map and exposes it through a thin verification adapter.

The same certificate layer may be reused for finite computations, algebraic
maps, combinatorial projections, state transitions, decoding functions, or
any other setting where two provably distinct inputs share one output.

## Trust boundary

This module certifies only the mathematical propositions encoded in Lean.

A collision certificate proves the existence of the supplied witnesses and
the logical consequences derived from them. It does not certify historical
priority, authorship, publication status, external review, or claims that
have not been represented by Lean definitions and theorems.

## Design direction

Future verification certificates should remain:

* small enough to inspect directly;
* independent of unnecessary domain imports;
* composed from explicit witnesses whenever practical;
* accompanied by focused axiom-audit targets;
* reusable across unrelated mathematical domains.

This file is intentionally a thin public import surface. Certificate
definitions and their generic consequences live in focused submodules under
`DkMath.Verification`.
-/
