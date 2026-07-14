# Demo Contract

## DkMath — Cosmic Formula Inversion

This document defines the exact behavior, content, timing, formal dependencies, and acceptance conditions of the public hackathon demonstration.

The demo must present one coherent path through:

```text
mathematical input
→ visual construction
→ arithmetic conclusion
→ Lean theorem
→ verified build
```

The demo is not an independent source of mathematical truth.

Its formal claims must come from the accepted Lean theorem surface.

Its visual claims must remain within the boundaries established by:

```text
MATHEMATICAL_CONTRACT.md
DECISIONS.md
VISUAL_STORYBOARD.md
RISKS_AND_STOPPING_RULES.md
```

---

## 1. Demo Objective

The demo must show that a repository-aware AI development workflow can transform a fixed mathematical contract into:

```text
reusable Lean theorems
a concrete verified example
a visual explanation
a reproducible build
```

The central public result is:

> Start with a finite set of primes, multiply them into `P`, choose a coprime offset `u`, and consider `P + u`. Every prime divisor of `P + u` lies outside the original finite prime set.

The same completed boundary is represented by the Cosmic Formula:

$$
P(P+2u)+u^2=(P+u)^2
$$

The demo must connect these two structures without claiming that the geometry causes the factorization.

---

## 2. Demo Classification

```text
PRIMARY DEMO TYPE:
  verified mathematical developer-tool demonstration

PRIMARY FORMAL SYSTEM:
  Lean 4

PRIMARY LIBRARY:
  DkMath

PRIMARY IMPLEMENTATION AGENT:
  Codex

PRIMARY VISUAL SYSTEM:
  Manim

TARGET AUDIENCE:
  hackathon judges
  developers
  Lean users
  mathematically curious viewers

TARGET DURATION:
  approximately 60–90 seconds for the complete submission segment

PRIMARY MANIM SEQUENCE:
  approximately 45–60 seconds
```

The project may also provide:

```text
a shorter trailer
a longer technical walkthrough
a raw Codex development recording
static screenshots
```

These are supporting artifacts.

The primary demo contract governs the judge-facing path.

---

## 3. Fixed Demo Data

The demo must use exactly the following values.

$$
S=\{2,3,5,7\}
$$

$$
P=2\cdot3\cdot5\cdot7=210
$$

$$
u=11
$$

$$
P+u=221
$$

$$
221=13\cdot17
$$

The Cosmic Formula values are:

$$
P(P+2u)=210\cdot232=48720
$$

$$
u^2=11^2=121
$$

$$
(P+u)^2=221^2=48841
$$

$$
48720+121=48841
$$

The fixed facts include:

$$
\gcd(210,11)=1
$$

$$
13\notin\{2,3,5,7\}
$$

$$
17\notin\{2,3,5,7\}
$$

No public demo artifact may silently replace these values.

---

## 4. Demo Thesis

The demo must communicate the following sequence.

```text
A finite prime set is selected.

Its members are multiplied into P.

A coprime offset u is introduced.

Body and Gap complete the Cosmic Formula square.

The completed boundary has value P + u.

That value factors into primes outside the original finite set.

Codex implements the theorem bridge.

Lean verifies the formal result.
```

The intended viewer conclusion is:

> The project demonstrates a controlled path from mathematical interpretation to repository-aware implementation, formal verification, and visual explanation.

---

## 5. Formal Demo Dependencies

The primary demo depends on the following Lean modules.

```text
DkMath.Hackathon.FinitePrimeEscape
DkMath.Hackathon.CosmicCompletion
DkMath.Hackathon.Demo
```

The intended dependency graph is:

```text
existing DkMath and Mathlib
        ↓
FinitePrimeEscape.lean
        ↓
CosmicCompletion.lean
        ↓
Demo.lean
        ↓
visual and submission demo
```

`FinitePrimeEscape.lean` and `CosmicCompletion.lean` may remain independent if no formal dependency is required between them.

`Demo.lean` must import both and combine their public theorem surfaces.

---

## 6. Required Public Lean Definitions

The concrete demo should expose stable declarations equivalent to:

```lean
def demoPrimeSet : Finset ℕ := {2, 3, 5, 7}

def demoP : ℕ := 210

def demoU : ℕ := 11

def demoBoundary : ℕ := 221
```

Optional definitions include:

```lean
def demoBody : ℕ := 48720

def demoGap : ℕ := 121

def demoBig : ℕ := 48841
```

Definitions should be added only when they improve readability across multiple theorems.

The exact declaration names may be refined during repository audit.

Once the public demo checkpoint is accepted, the names become presentation-stable.

---

## 7. Required Public Lean Theorems

The final demo should expose theorem surfaces equivalent to the following.

### Product

```lean
theorem demo_product :
    ∏ p ∈ demoPrimeSet, p = demoP
```

### Coprimality

```lean
theorem demo_coprime :
    Nat.Coprime demoP demoU
```

### Boundary

```lean
theorem demo_boundary :
    demoP + demoU = demoBoundary
```

### Factorization

```lean
theorem demo_factorization :
    demoBoundary = 13 * 17
```

### Prime Facts

```lean
theorem demo_thirteen_prime :
    Nat.Prime 13
```

```lean
theorem demo_seventeen_prime :
    Nat.Prime 17
```

### Freshness

```lean
theorem demo_thirteen_fresh :
    FreshPrimeFactor demoPrimeSet demoBoundary 13
```

```lean
theorem demo_seventeen_fresh :
    FreshPrimeFactor demoPrimeSet demoBoundary 17
```

If no `FreshPrimeFactor` predicate is introduced, use an equivalent conjunction.

### Cosmic Completion

```lean
theorem demo_cosmic_completion :
    demoP * (demoP + 2 * demoU) + demoU ^ 2 =
      (demoP + demoU) ^ 2
```

### Numerical Completion

```lean
theorem demo_cosmic_completion_numeric :
    48720 + 121 = 48841
```

### Optional End-to-End Bundle

```lean
theorem demo_complete :
    Nat.Coprime demoP demoU ∧
    demoBoundary = 13 * 17 ∧
    FreshPrimeFactor demoPrimeSet demoBoundary 13 ∧
    FreshPrimeFactor demoPrimeSet demoBoundary 17 ∧
    demoP * (demoP + 2 * demoU) + demoU ^ 2 =
      (demoP + demoU) ^ 2
```

The exact bundle may be omitted if separate theorems are clearer for the demo.

---

## 8. General Theorem Reuse Requirement

The concrete demo must visibly reuse the general theorem surface.

Required pattern:

```text
general finite-prime theorem
→ specialization to demo data
```

and:

```text
general Cosmic Formula theorem
→ specialization to demo data
```

The demo must not establish all public results only through:

```text
norm_num
decide
native_decide
```

Automation may prove:

```text
explicit arithmetic
explicit primality
explicit membership
explicit factorization
```

The structural theorem must come from the general facade.

---

## 9. Demo Verification Commands

The final project must document the exact commands required to verify the demo.

Expected focused commands:

```bash
lake build DkMath.Hackathon.FinitePrimeEscape
```

```bash
lake build DkMath.Hackathon.CosmicCompletion
```

```bash
lake build DkMath.Hackathon.Demo
```

If an aggregate module is later created:

```bash
lake build DkMath.Hackathon
```

Optional broader gate:

```bash
lake build DkMath
```

Source checks:

```bash
rg -n "sorry|admit" DkMath/Hackathon
```

```bash
git diff --check
```

The final commands must reflect the actual repository working directory.

---

## 10. Demo Success State

The final formal screen must show a real successful verification state.

Approved success text:

```text
Lean build succeeded

No sorry in the hackathon modules

Verified by Lean
```

The demo must not use a fabricated success screen.

The code shown and the build shown must correspond to the same accepted branch state.

---

## 11. Primary Demo Structure

The primary judge-facing demo has five sections.

```text
Section A:
  question and finite prime input

Section B:
  Cosmic Formula completion

Section C:
  fresh-factor reveal

Section D:
  Codex and Lean verification

Section E:
  broader inverse-projection direction
```

Recommended timing:

| Section | Content | Target |
|---|---|---:|
| A | finite set, product, offset | 12–15 s |
| B | Body, Gap, completed square | 20–25 s |
| C | `221 = 13 × 17`, freshness | 10–15 s |
| D | Codex and Lean verification | 10–15 s |
| E | future direction and close | 5–10 s |

Target total:

```text
approximately 60–80 seconds
```

---

## 12. Section A — Mathematical Input

### Required Visual Content

```text
S = {2, 3, 5, 7}
P = 2 × 3 × 5 × 7 = 210
u = 11
gcd(210, 11) = 1
```

### Required Narration Meaning

> Begin with a finite set of primes. Multiply them into `P`, and choose an offset `u` that is coprime to `P`.

### Formal Anchors

```text
demoPrimeSet
demo_product
demo_coprime
```

### Prohibited Implication

Do not imply that `11` belongs to the original set.

---

## 13. Section B — Cosmic Formula Completion

### Required Visual Content

$$
\mathrm{Body}=P(P+2u)
$$

$$
\mathrm{Gap}=u^2
$$

$$
\mathrm{Big}=(P+u)^2
$$

and:

$$
P(P+2u)+u^2=(P+u)^2
$$

For the demo:

$$
210\cdot232+11^2=221^2
$$

### Required Narration Meaning

> The Cosmic Formula separates a Body and a square Gap. Adding the Gap completes a square whose side is `P + u`.

### Formal Anchors

```text
cosmicCompletion
demo_cosmic_completion
```

### Visual Requirement

The completed side label `P + u = 221` must remain visible long enough to become the bridge to the factorization scene.

---

## 14. Section C — Fresh-Factor Reveal

### Required Visual Content

$$
P+u=221
$$

$$
221=13\cdot17
$$

$$
13,17\notin S
$$

The factors `13` and `17` must appear outside the original set boundary.

### Required Narration Meaning

> The completed boundary factors as thirteen times seventeen. Both prime factors lie outside the original finite prime set.

### Formal Anchors

```text
demo_factorization
demo_thirteen_prime
demo_seventeen_prime
demo_thirteen_fresh
demo_seventeen_fresh
```

### General Theorem Overlay

A concise general statement may appear:

$$
q\mid P+u\Longrightarrow q\notin S
$$

Required small-print conditions:

```text
q prime
P is the product of S
gcd(P, u) = 1
```

### Meaning Boundary

Do not say:

```text
the Gap creates 13 and 17
```

Use:

```text
the completed boundary has the fresh factors 13 and 17
```

---

## 15. Section D — Codex and Lean Verification

### Required Elements

```text
a brief Codex implementation view
actual Lean theorem names
actual successful build output
verified result caption
```

### Suggested Sequence

```text
1. show project instruction or theorem contract
2. show Codex editing the hackathon module
3. show one Lean failure or repair moment
4. show final theorem
5. show successful build
```

### Required Narration Meaning

> The mathematical contract is fixed first. Codex then investigates DkMath, implements the missing bridge, and Lean verifies the result.

### Agent Meaning Boundary

Do not say:

```text
Codex invented the theorem from nothing
```

Prefer:

```text
Codex inspected and implemented the formal bridge under a fixed contract
```

---

## 16. Section E — Broader Direction

### Required Meaning

The finite theorem is the entry point to:

```text
bounded projection
exact inverse
optional DkReal reconstruction
```

Suggested closing text:

```text
Next:
bounded projection and verified inverse reconstruction
```

Suggested narration:

> This finite theorem is the first public step toward Cosmic Formula inverse projection.

### Formal Boundary

This section must be marked as:

```text
next phase
future work
stretch milestone
```

unless the corresponding Lean theorems have already been accepted.

---

## 17. Optional Projection Extension

Only include this extension if the selected projection theorem builds.

Possible unsigned route:

$$
x=\frac{P}{P+u}
$$

$$
0\le x<1
$$

$$
P=\frac{ux}{1-x}
$$

Possible signed route:

$$
x=-\frac{P}{P+u}
$$

$$
-1<x\le0
$$

$$
P=-\frac{ux}{1+x}
$$

Only the convention accepted in `DECISIONS.md` may appear.

Do not show both as competing public APIs.

---

## 18. Optional DkReal Extension

Only include after a verified DkReal bridge exists.

Required sequence:

```text
projected value
→ nested rational intervals
→ inverse-mapped macro intervals
→ width below one
→ at most one integer candidate
```

Required formal text:

$$
\operatorname{width}(I)<1
$$

Required conclusion wording:

```text
at most one integer candidate
```

Do not say:

```text
exactly one candidate
```

unless existence is also proved.

---

## 19. Supporting Collatz Footage

The recorded Collatz cp-320 footage may appear as supporting evidence.

Recommended duration:

```text
5–12 seconds
```

Suggested placement:

```text
after the main theorem is understood
```

Suggested caption:

```text
The same workflow was tested on a much larger active DkMath branch.
```

Required limitation:

```text
No Collatz convergence claim is made.
```

The footage may demonstrate:

```text
large-repository navigation
substantial Lean editing
proof repair
build success
genuine-obstruction isolation
```

It must not replace the Cosmic Formula demo.

---

## 20. Demo Narration Contract

The narration must include the following meanings.

```text
finite prime set
product P
coprime offset u
Body and Gap
completed boundary P + u
fresh factors 13 and 17
Codex implementation
Lean verification
future inverse-projection direction
```

The narration may use different wording but must not omit the coprimality condition when stating the general theorem.

---

## 21. Suggested Primary Narration

```text
Start with a finite set of primes:
two, three, five, and seven.

Their product is P, equal to two hundred ten.

Now choose a coprime offset, eleven.

The Cosmic Formula forms a Body,
P times P plus twice the offset,
and a square Gap, u squared.

Body plus Gap completes a square
whose side is P plus u:
two hundred twenty-one.

That boundary factors as thirteen times seventeen.

Both prime factors lie outside the original finite prime set.

We fix this theorem contract first.
Codex then investigates DkMath and implements the formal bridge.
Lean verifies the result.

This is the first step toward verified Cosmic Formula inverse projection.
```

The final narration should fit the target duration without rushing equations.

---

## 22. Short Demo Narration

For a shorter edit:

```text
Take the finite prime set two, three, five, and seven.

Its product is two hundred ten.

Add a coprime offset, eleven.

The Cosmic Formula completes the square:
Body plus Gap equals two hundred twenty-one squared.

The boundary two hundred twenty-one factors as thirteen times seventeen,
and both primes lie outside the original set.

Codex implements the theorem in DkMath.
Lean verifies it.
```

---

## 23. On-Screen Text Contract

Required text:

```text
Finite prime set

Product P = 210

Coprime offset u = 11

Body

Gap

Completed boundary P + u = 221

221 = 13 × 17

Fresh prime factors

Verified by Lean
```

Optional text:

```text
Implemented by Codex

Visualized with Manim

Next: inverse projection
```

Avoid long paragraphs.

---

## 24. Code Display Contract

The final demo should display no more than two or three Lean declarations at once.

Preferred selections:

```lean
theorem exists_fresh_prime_factor ...
```

```lean
theorem demo_thirteen_fresh ...
```

```lean
theorem demo_cosmic_completion ...
```

The code panel should show:

```text
module path
theorem name
theorem statement
short proof body or folded proof
```

The proof body may be shortened visually if the actual source remains linked and available.

---

## 25. Build Output Contract

The displayed build output must contain the actual target name.

Example:

```text
lake build DkMath.Hackathon.Demo
```

Approved final status:

```text
Build completed successfully
```

Optional additional checks:

```text
No sorry
git diff --check passed
```

Do not show unrelated warnings as if they belong to the new module.

---

## 26. Visual–Formal Alignment Table

This table must be updated after implementation.

| Demo element | Required formal anchor | Final name |
|---|---|---|
| finite set | definition | pending |
| product equals `210` | theorem | pending |
| coprimality | theorem | pending |
| boundary equals `221` | theorem | pending |
| factorization | theorem | pending |
| `13` prime | theorem | pending |
| `17` prime | theorem | pending |
| `13` fresh | theorem | pending |
| `17` fresh | theorem | pending |
| Cosmic completion | theorem | pending |
| successful verification | build gate | pending |

No `pending` value may remain in the final demo contract.

---

## 27. Demo Data Synchronization

The following values must be checked in both Lean and Manim.

```text
primes:
  2, 3, 5, 7

product:
  210

offset:
  11

boundary:
  221

fresh factors:
  13, 17

Body:
  48720

Gap:
  121

Big:
  48841
```

Synchronization may be manual for the MVP.

Automatic Lean-to-Python extraction is not required.

The integration report must confirm equality of the values.

---

## 28. Required Demo Artifacts

The completed project should contain:

```text
Lean demo module
Manim source
rendered primary video
source or screenshot of successful Lean build
one or more theorem screenshots
one project thumbnail
submission description
reproduction commands
```

Optional artifacts:

```text
long technical walkthrough
raw Codex recording
Collatz supporting excerpt
interactive prototype
```

---

## 29. OBS Recording Contract

Record at least the following moments.

```text
Codex receives the current checkpoint instruction
Codex inspects existing DkMath APIs
Codex edits the target Lean files
Lean reports a local proof failure
Codex repairs the proof
focused build succeeds
final report is produced
```

If the first audit session performs no source edits, record:

```text
document reading
repository search
theorem map formation
audit report
```

The implementation recording begins with the later bounded implementation checkpoint.

---

## 30. Demo Reproduction Contract

The public documentation must explain:

```text
how to clone the repository
how to checkout the branch
how to build the demo theorem
how to render the Manim scene
where to find the final video
```

Expected repository commands:

```bash
git clone https://github.com/Deskuma/dkmath.git
cd dkmath
git switch hackathon/cosmic-formula-inversion
```

Exact Lean and Manim setup commands must be tested before submission.

---

## 31. Demo Environment Contract

The demo should run locally without requiring:

```text
network services
API keys
database setup
authentication
cloud deployment
```

Required environments:

```text
Lean toolchain
DkMath repository dependencies
Python
Manim
video playback
```

The workflow itself is the product.

A web application is not required.

---

## 32. Demo Quality Requirements

### Mathematical Quality

```text
all displayed arithmetic is correct
all general claims include their essential assumptions
freshness is not called primitiveness
existence is not called uniqueness
future work is clearly labelled
```

### Formal Quality

```text
displayed theorem names are real
displayed source matches the accepted branch
build output is real
new public modules contain no sorry
```

### Visual Quality

```text
equations are readable
colors have stable meanings
transitions preserve continuity
the completed boundary is visually central
```

### Agent Quality

```text
Codex work is bounded by a checkpoint
repository reuse is visible
a genuine obstruction is reported when reached
```

### Submission Quality

```text
the project can be understood without reading the whole repository
reproduction instructions are clear
limitations are explicit
```

---

## 33. Demo Non-Goals

The demo does not attempt to show:

```text
a proof of the infinitude of primes
a primitive-prime-divisor theorem
prime distribution
prime density
a Collatz proof
a proof of any open conjecture
formal Euclidean dissection
cryptographic security
aperiodic tiling
all of DkMath
complete DkReal reconstruction unless implemented
```

The demo must remain a short verified route through the library.

---

## 34. Prohibited Statements

Do not state:

```text
The Gap creates new primes.
```

Do not state:

```text
This is a new proof that infinitely many primes exist.
```

Do not state:

```text
Codex solved the theorem independently.
```

Do not state:

```text
The inverse projection is complete.
```

unless all required inverse laws are formally verified.

Do not state:

```text
DkMath proves Collatz.
```

Approved alternatives:

```text
The completed boundary has prime factors outside the original finite set.
```

```text
Codex implemented the formal bridge under a fixed theorem contract.
```

```text
Lean verified the encoded mathematical claim.
```

```text
Inverse projection is the next research phase.
```

---

## 35. Demo Failure Conditions

The demo is not acceptable if:

```text
the Lean theorem has not built
the Manim values differ from Lean
the coprimality condition is omitted from the general claim
the geometry is described as causing prime factorization
the demo uses provisional theorem names
the build output is simulated
the Collatz footage implies convergence
the main sequence exceeds the submission time without justification
```

---

## 36. Demo Stopping Rules

Stop expanding the demo when:

```text
the central theorem is understandable
the square completion is visually clear
the factor reveal is readable
the Lean verification is visible
the project identity is clear
the target duration is satisfied
```

Stop optional work immediately when:

```text
projection delays the required render
DkReal delays submission packaging
interactive controls add deployment complexity
visual polish threatens reproducibility
```

A complete simple demo is preferred over an incomplete ambitious demo.

---

## 37. Demo Review Checklist

Before acceptance, confirm:

```text
[ ] fixed data matches ADR-006

[ ] general theorem is reused

[ ] Cosmic Formula theorem is reused

[ ] every visual claim has a formal anchor or is marked interpretive

[ ] theorem names are final

[ ] build command is final

[ ] build output is real

[ ] Manim constants match Lean

[ ] narration preserves the arithmetic–geometry boundary

[ ] fresh is not called primitive

[ ] future work is labelled

[ ] Collatz limitation is explicit

[ ] video duration is acceptable

[ ] captions are readable

[ ] reproduction instructions are tested
```

---

## 38. Minimum Demo Acceptance

The minimum public demo is accepted when:

```text
1. Demo.lean builds.

2. The general finite prime escape theorem is used.

3. The general Cosmic Formula completion theorem is used.

4. The fixed example is verified.

5. The main Manim sequence renders.

6. The video shows the theorem and successful Lean verification.

7. The project limitations are stated accurately.
```

---

## 39. Strong Demo Acceptance

The stronger demo additionally includes:

```text
a verified bounded projection
an exact inverse formula
a projection animation
a concise DkReal future-work explanation
a short recorded Codex repair sequence
```

These additions must not weaken the clarity of the minimum demo.

---

## 40. Stretch Demo Acceptance

The stretch demo additionally includes:

```text
verified DkReal interval reconstruction
width transport
at-most-one integer candidate
inverse reconstruction animation
```

This level is optional.

Its absence does not make the hackathon project incomplete.

---

## 41. Final Demo Script Structure

Recommended final edit:

```text
00:00–00:05
Project question and finite prime set

00:05–00:15
Product P and coprime offset u

00:15–00:35
Body, Gap, and Cosmic Formula completion

00:35–00:47
Boundary factorization and fresh-prime comparison

00:47–01:00
Codex implementation and Lean verification

01:00–01:08
Inverse-projection direction and project close
```

A shorter edit may omit the final future-work section.

---

## 42. Final Closing Text

Preferred closing:

```text
DkMath — Cosmic Formula Inversion

A fixed mathematical contract.
Repository-aware Codex implementation.
Lean verification.
Manim explanation.
```

Optional final line:

```text
Next: bounded projection and verified reconstruction.
```

---

## 43. Demo Contract Change Procedure

Any change to the demo must record:

```text
what changed
why it changed
which Lean theorem is affected
which visual scene is affected
which narration line is affected
whether the fixed demo data changed
whether the mathematical contract changed
```

Changes to fixed data require a new ADR.

Codex may propose a demo change.

Codex may not silently apply one that changes mathematical meaning.

---

## 44. Demo Contract Summary

The required public path is:

```text
S = {2, 3, 5, 7}
→ P = 210
→ u = 11
→ gcd(P, u) = 1
→ Body + Gap = Big
→ P + u = 221
→ 221 = 13 × 17
→ 13 and 17 lie outside S
→ Lean verifies the theorem
```

The central algebraic identity is:

$$
P(P+2u)+u^2=(P+u)^2
$$

The central arithmetic theorem is:

$$
q\mid P+u\Longrightarrow q\notin S
$$

under the required prime, product, and coprimality assumptions.

The demo succeeds when the viewer can see:

```text
what the mathematical claim is
what Codex implemented
what Lean verified
what Manim explains
what remains future work
```

The demo must remain short, exact, reproducible, and faithful to the verified theorem surface.
