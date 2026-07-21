# <Case Title> Demo Contract

This contract defines the stable presentation surface for videos, talks,
README examples, and external review. Keep it synchronized with the
[`case landing page`](BREAKING_MATH_CASE_TEMPLATE.md) and
[`provenance record`](PROVENANCE_TEMPLATE.md).

## Demo Goal

- **One-sentence goal:** `<what the audience should understand>`
- **Verified result shown:** `<exact summit theorem>`
- **Target duration:** `<duration or not applicable>`

## Audience

- **Primary audience:** `<mathematicians | Lean users | general technical audience | other>`
- **Expected background:** `<background>`
- **Terms requiring definition:** `<terms>`

## Public Import

```lean
import DkMath.Hackathon.<CaseName>
```

- **Aggregator file:** `DkMath/Hackathon/<CaseName>.lean`
- **Root import status:** `<public from DkMath | project aggregator only>`

## Ordered Theorem Surface

List the exact presentation order.

```lean
#check DkMath.Hackathon.<CaseName>.<demoTheoremOne>
#check DkMath.Hackathon.<CaseName>.<demoTheoremTwo>
#check DkMath.Hackathon.<CaseName>.<demoSummitTheorem>
```

Demo theorems should normally be direct aliases or thin compositions of
completed theorems. Do not hide new symbolic computation, large proof search,
or other heavy mathematical work in the presentation layer.

## What Each Theorem Establishes

| Order | Exact Lean identifier | Exact proposition | Plain-language meaning |
| --- | --- | --- | --- |
| 1 | `<DkMath.Hackathon.<CaseName>.<demoTheoremOne>>` | `<proposition>` | `<meaning>` |
| 2 | `<DkMath.Hackathon.<CaseName>.<demoTheoremTwo>>` | `<proposition>` | `<meaning>` |

Mark source reports and optional interpretation explicitly; do not present them
as consequences of a theorem unless the theorem actually states them.

## Trust and Axiom Statement

```lean
#print axioms DkMath.Hackathon.<CaseName>.<demoSummitTheorem>
```

- **Exact output:** `<output>`
- **Allowed foundations:** `<list>`
- **Unexpected assumptions:** `<none or list>`
- **Trust statement for presentation:** `<short statement>`

## Presentation Sequence

| Time or step | Visual or command | Narration claim | Supporting theorem |
| --- | --- | --- | --- |
| `<time>` | `<visual>` | `<claim>` | `<exact identifier>` |

Recommended flow:

1. State the exact object, formula, or finite data.
2. Show the local identity or witness certificate.
3. Show the global consequence or verified identity.
4. Show the summit theorem and axiom audit.
5. Label any source history, interpretation, or deferred work separately.

## Claims Allowed

- **Lean proved:** `<exact claims backed by listed theorems>`
- **External sources reported:** `<claims attributed to sources>`
- **DkMath independently reconstructed:** `<claims>`
- **DkMath interpretation:** `<claims or not applicable>`

Every spoken or written claim should fit one of these categories.

## Claims Not Allowed

- `<claim exceeding the exact Lean theorem>`
- `<unverified source or priority claim>`
- `<interpretation presented as source fact>`
- `<deferred result presented as complete>`

## Fallback if a Theorem Name Changes

1. Stop using the stale identifier.
2. Locate the replacement in the project aggregator.
3. Confirm that its exact proposition matches the intended claim.
4. Re-run `#check`, the focused build, and `#print axioms`.
5. Update this contract and the case landing page together.

Do not replace a missing Demo alias with an unreviewed heavy proof inside a
presentation file.

## Build or Check Commands

Run from `lean/dk_math`:

```sh
lake build DkMath.Hackathon.<CaseName>
lake build DkMathTest.Hackathon.<CaseName>.CheckAxioms
```

Optional temporary public check:

```lean
import DkMath.Hackathon.<CaseName>

#check DkMath.Hackathon.<CaseName>.<demoTheoremOne>
#check DkMath.Hackathon.<CaseName>.<demoTheoremTwo>
#check DkMath.Hackathon.<CaseName>.<demoSummitTheorem>
```

- **Last check date:** `<date>`
- **Result:** `<success | failure | not run>`
- **Warnings relevant to this case:** `<warnings or none>`
