# GWSS-003F2 synthesized whole-source assembly closure — implementation report

Date: 2026-08-22

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-guinand-weil-source-rank-audit-260820-v0`

Base HEAD before this stage: `bd840bf27a1cb88b94ff4a8a54e636776b1437cb`.
No commit, push, PR, CI, or later GWSS stage was performed.

## Scope

This stage implements only GWSS-003F2.  The supplied 0039 document is the
bounded implementation contract; the user request is to implement that
contract and to maintain the Lean docstrings.  No Guinand--Weil or Weil
positivity infrastructure, height limit, new source-rank family, zero
avoidance, DkReal route, or RH deduction was started.

The global objective remains

```text
zero configuration -> independent source -> off-critical detector
  -> arithmetic control -> centered-coordinate uniqueness -> RH
```

The current representation boundary is the finite synthesized witness

```text
h_target(z) = sum_i c_i H_{epsilon,tau_i}(z)
```

with every selected `tau_i` nonzero.  The previous 0038 label was treated as
an open representation gap, not as a proved obstruction.

## Implemented API

The focused module is
`DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessGeneralTauSourceBridgeAudit.lean`.
It now contains:

* unconditional synthesized top-feature rectangle integrability and the
  actual top-horizontal bridge;
* the synthesized deoriented vertical source and the oriented whole source
  `VerticalSource - I * TopSource`;
* the whole source feature
  `VerticalAggregate - I * TopAggregate`;
* a normalized whole-source identity under explicit interval-integrability
  inputs for the two aggregate functions;
* coefficient-scalar transport for vertical fibres, top fibres, vertical and
  top aggregates, the whole feature, the deoriented vertical source, and the
  whole source;
* the off-critical `q.im` specialization of both whole-feature and whole-source
  transport;
* the finite arithmetic approximant scalar transport, retaining the cutoff
  and all four finite terms;
* an exact finite approximant / whole-source assembly theorem under the named
  vertical finite-ledger equality.

The existing synthesized vertical rectangle-integrability theorem is now
unconditional by finite-sum closure of the single-basis certificates.  The
new public declarations have docstrings recording the orientation and the
formal boundary; they do not claim positivity, source rank, or RH.

## Exact orientation

The implementation uses the finite-ledger convention

```text
WholeSource = VerticalSource - I * TopSource
finite approximant = 2 * I * WholeSource
```

The `I` factor is not inserted into the deoriented vertical amplitude.  The
top-horizontal term remains explicit and is not removed or replaced by an
exact zeta endpoint.

## Remaining load-bearing API gap

The representation layer is not fully closed by the currently exported
interfaces.  Two exact providers are still absent:

1. interval-integrability of the synthesized vertical and top aggregate
   functions as functions of the logarithmic feature variable; and
2. the public finite-ledger identity identifying

```text
2 * prime-cutoff + 2 * archimedean + 2 * elementary
  = 2 * I * deoriented vertical source
```

for the arbitrary synthesized witness.  The module exposes the exact
`..._of_integrable` whole-feature theorem and the exact
`..._of_vertical_ledger` approximant assembly theorem with these facts as
named hypotheses.  This keeps the missing source identity visible instead of
manufacturing it through the zero-moment formula, an `X -> infinity` equality,
or an unproved integral exchange.

Accordingly the single primary classification is:

```text
TARGET-WITNESS-WHOLE-SOURCE-ASSEMBLY-API-GAP
```

This is an interface gap, not an obstruction and not a source-rank result.
The following sub-results are nevertheless found:

```text
synthesized vertical rectangle integrability: FOUND
synthesized top-horizontal feature and bridge: FOUND
synthesized whole feature: FOUND
whole-source normalized representation: FOUND under named aggregate-integrability inputs
finite approximant / whole-source identity: FOUND under named vertical-ledger input
coefficient and q.im source transport: FOUND
independent shifted-energy dominance: NOT FOUND
```

The next unresolved mathematical target remains an independent shifted-energy
order/asymmetry provider only after the missing representation APIs are
supplied.  That later target is outside this assignment.

## Verification

Focused verification passed:

```text
lake env lean DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessGeneralTauSourceBridgeAudit.lean
```

`git diff --check` passed.  The edited Lean module contains no `sorry`,
`admit`, `native_decide`, or new `axiom` declaration.
