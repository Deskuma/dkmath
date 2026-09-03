# DkMath NumberTheory Primitive Conservation Kernel

cid: `6a97a02e-3248-83e8-8f75-3ed7eceeee9d`

Project branch: `wip/number-theory-primitive-conservation-kernel-260903-v0`

Base branch: `develop`

Start date: 2026-09-03

## 1. Project position

この project は、DkMath に既に存在する

- Cosmic Formula / Core-Beam-Gap
- `squareBody P = P(P+2) = (P+1)^2 - 1`
- finite prime basis / primorial synchronization
- wheel survivor / fresh-prime refinement
- finite-world fresh prime direction
- GN prime closure

を再利用し、次の意味論を theorem family として固定する。

```text
finite known support
        ↓
coarse primorial anchor
        ↓
complete prime closure inside the anchor
        ↓
square conservation window
        ↓
escape from old support
        ↓
fresh primitive direction
        ↓
observer refinement
```

本 project の第一目標は、素数だけに限定された新しい定義を発明することではない。

まず自然数上で既に証明可能な形として、

> old prime support から escape した点が square conservation window 内にあるなら、その escape は fresh prime direction として認証される

という有限算術構造を固定する。

その後、同じ pattern が GN / Petal / CF2D / RH finite source に現れることを確認できた段階で、より一般的な `Primitive` 保存核へ抽象化する。

## 2. Mathematical source

### 2.1 Square Body

既存 canonical definition:

```lean
DkMath.NumberTheory.Primitive.squareBody
```

数学的には

$$
\operatorname{squareBody}(P)=P^2+2P=P(P+2).
$$

既存 theorem:

$$
\operatorname{squareBody}(P)+1=(P+1)^2.
$$

従って

$$
1<m\le P(P+2)
$$

が composite なら、必ず

$$
\exists p\le P,\quad p\text{ prime},\quad p\mid m
$$

となる。

この theorem は既に `DkMath.NumberTheory.Primitive.SquareBody` に存在する。

### 2.2 Coarse primorial anchor

有限 prime basis `S` に対して

$$
P_S:=\prod_{p\in S}p
$$

を取る。

`DkMath.NumberTheory.PrimorialUniverse.FinitePrimeSynchronization` は、この積を有限 basis の共通周期として扱う。

代表例:

$$
\{2,3,5\}\mapsto 30.
$$

ここで重要なのは、生成 basis

$$
S=\{2,3,5\}
$$

と、anchor `30` 以下で回収される complete prime support

$$
\{p\mid p\text{ prime},\ p\le30\}
$$

を区別することである。

前者は coarse anchor を生成する情報、後者は square certification に使用する complete support である。

### 2.3 `30` world regression

`P = 30` なら

$$
\operatorname{squareBody}(30)=30\cdot32=960,
$$

$$
960+1=31^2=961.
$$

従って、30 以下の complete prime support を持てば、960 以下の composite point は必ずその support の prime divisor を持つ。

この意味で

```text
{2,3,5}
  ↓ product
30
  ↓ complete prime closure up to 30
{2,3,5,7,11,13,17,19,23,29}
  ↓ square Body
960 = 31^2 - 1
```

という二段階 closure を canonical regression とする。

`gcd(n,30)=1` だけで 960 以下の primality を判定するとは主張しない。例えば `49` は wheel survivor だが composite である。

## 3. Fine unit-depth coordinate

Primorial anchors

$$
2,6,30,210,\ldots
$$

は coarse discrete lattice である。

これに対し、任意の実数または自然数 `q` に対して zero-conjugate quadratic

$$
Z_q(x)
:=
\left(x-\frac q2\right)^2
-
\left(\frac q2\right)^2
$$

を考える。

平方差により

$$
Z_q(x)=x(x-q).
$$

従って roots は

$$
0,\ q,
$$

midpoint は

$$
\frac q2,
$$

unit-depth は

$$
D(q):=-\left(\frac q2\right)^2.
$$

同じ `q` は square Body 側で

$$
\operatorname{squareBody}(q)+1=(q+1)^2
$$

を決める。

従って `q` は

```text
zero-conjugate root separation
half-unit q/2
unit-depth -(q/2)^2
square certification anchor
```

を同時に与える fine coordinate として扱える。

## 4. Coarse-to-fine principle

`q ≤ P` なら

$$
q(q+2)\le P(P+2).
$$

従って

$$
\operatorname{squareBody}(q)
\le
\operatorname{squareBody}(P).
$$

この単調性により、一つの coarse anchor `P` の complete prime support は、その内部の全 fine anchor `q ≤ P` に対する square certification に再利用できる。

代表例として `P = 30` の support は

```text
q = 6   -> 7^2 boundary
q = 10  -> 11^2 boundary
q = 12  -> 13^2 boundary
...
q = 30  -> 31^2 boundary
```

を一つの coarse world 内に包含する。

## 5. Primitive conservation reading

本 project では、まず次の concrete pattern を固定する。

```text
old support
+
bounded square conservation window
+
escape from old support
⇒
fresh prime / primitive direction
```

既存 `SquareBody.lean` には既に、square Body 内の large prime divisor に対して

- square-lift exclusion
- uniqueness of a large prime direction
- old-generated cofactor
- fresh-prime-direction packaging

が実装されている。

したがって新 project はこれらを再証明せず、coarse primorial / fine depth / complete prime closure の意味論を橋渡しする。

## 6. Existing DkMath anchors

Implementation 開始前に current tree を再確認する。

```text
DkMath/CosmicFormula/CoreBeamGap.lean
DkMath/CosmicFormula/CosmicFormulaBinom.lean
DkMath/NumberTheory/Primitive/SquareBody.lean
DkMath/NumberTheory/Primitive/FinitePrimeWorld.lean
DkMath/NumberTheory/PrimorialUniverse/FinitePrimeSynchronization.lean
DkMath/NumberTheory/PrimorialUniverse/WheelSurvivor.lean
DkMath/NumberTheory/PrimorialUniverse/FreshPrimeLift.lean
DkMath/NumberTheory/PrimorialUniverse/FiniteReservationEscape.lean
DkMath/NumberTheory/StructuralArithmetic.lean
DkMath/NumberTheory/GNPrimeClosure.lean
```

Potentially relevant square-anchor modules:

```text
DkMath/NumberTheory/PrimorialUniverse/SquareAnchor*.lean
DkMath/NumberTheory/Legendre/PrimorialWheel*.lean
```

Do not duplicate a theorem if an existing square-anchor theorem already gives the required statement.

## 7. Proposed theorem surface

### PCK-001 — Half-unit zero-conjugate core

Candidate owner:

```text
DkMath/CosmicFormula/HalfUnitZeroConjugate.lean
```

Candidate declarations:

```lean
def halfUnitDepth (q : ℝ) : ℝ :=
  -((q / 2) ^ 2)

def zeroConjugateUniverse (q x : ℝ) : ℝ :=
  (x - q / 2) ^ 2 - (q / 2) ^ 2

theorem zeroConjugateUniverse_eq_mul

theorem zeroConjugateUniverse_zero

theorem zeroConjugateUniverse_anchor

theorem zeroConjugateUniverse_eq_zero_iff

theorem zeroConjugateUniverse_midpoint_eq_depth
```

The first implementation may use a more generic ring-level theorem if repository reconnaissance shows an existing suitable owner/API.

### PCK-002 — Fine square-anchor nesting

Candidate owner:

```text
DkMath/NumberTheory/Primitive/SquareBodyFineAnchor.lean
```

Candidate declarations:

```lean
theorem squareBody_mono

theorem squareBoundary_mono

theorem prime_of_fineAnchor_disjoint_under_coarseAnchor
```

### PCK-003 — Complete prime support

Candidate semantic predicate:

```lean
def PrimeCompleteUpTo (S : Finset ℕ) (P : ℕ) : Prop :=
  ∀ ⦃p : ℕ⦄, p ∈ S ↔ Nat.Prime p ∧ p ≤ P
```

Before adding this definition, search for an existing equivalent predicate/API.

### PCK-004 — Square escape to fresh prime

Target semantic theorem:

```lean
theorem freshPrime_of_squareBody_escape ...

theorem freshPrimeDirection_of_squareBody_escape ...
```

The proof should reuse existing `prime_of_supportDisjointFrom_le_squareBody` or `prime_of_supportDisjointFrom_primeScalesUpTo_le_squareBody`.

### PCK-005 — Finite prime-knowledge expansion

Candidate operator:

```lean
def squarePrimeExpansion
    (S : Finset ℕ) (P : ℕ) : Finset ℕ :=
  S ∪
    (Finset.Icc (P + 1) (squareBody P)).filter
      (fun n => SupportDisjointFrom S n)
```

Target theorem, subject to exact endpoint conventions:

```lean
theorem squarePrimeExpansion_complete
    (hS : PrimeCompleteUpTo S P) :
    PrimeCompleteUpTo
      (squarePrimeExpansion S P)
      (squareBody P)
```

This is a finite closure theorem. It does not assert a new asymptotic prime-distribution theorem.

### PCK-006 — Primorial coarse anchor bridge

Given a finite prime basis `S0`, let

$$
A=\operatorname{finitePrimeBasisProduct}(S0).
$$

After obtaining complete prime support up to `A`, transport it to every fine anchor `q ≤ A`.

### PCK-007 — canonical `30` regression

Fix the exact arithmetic chain

$$
\{2,3,5\}\to30\to960\to961=31^2.
$$

The regression must distinguish

- basis `{2,3,5}`,
- period/product `30`,
- complete prime support up to `30`,
- square certification window up to `960`.

### PCK-008 — Primitive kernel dichotomy

Reuse existing large-prime split theorems to expose the semantic form

```text
square-window point
  = old-generated
or
  = unique fresh prime direction × old-generated cofactor
```

Do not weaken existing exact theorems merely for a prettier wrapper.

## 8. Future RH / Prime Harmony bridge

This project does not prove RH and does not import RH modules into the NumberTheory core.

Future bridge only after the finite arithmetic core is closed:

```text
fine anchor q
  ↓
unit-depth -(q/2)^2
  ↓
complete prime support ≤ q
  ↓
Prime Harmony / PHZ / von Mangoldt finite source
  ↓
CFBRC finite source provenance
```

The old `wip/RH-CFBRC-finite-provider-frontier-260825-v0` branch remains historical frontier material; this project is not based on that diverged branch.

## 9. Non-goals / firewalls

The first campaign does not claim:

- RH or an RH-equivalent theorem;
- Legendre conjecture;
- prime infinitude from wheel geometry alone;
- that `gcd(n, P#) = 1` is a complete primality criterion over an arbitrary large range;
- that every survivor is prime;
- that a continuous real `PrimeGauge` is ordinary ring-theoretic primality;
- a generic `PrimitiveKernel` abstraction before multiple concrete domains justify it;
- a new prime factorization algorithm more efficient than existing methods.

No `sorry`, `admit`, project-specific axiom, or hidden RH/prime-existence assumption is introduced.

## 10. Checkpoint plan

```text
PCK-000  reconnaissance / exact existing theorem inventory
PCK-001  half-unit zero-conjugate algebra
PCK-002  fine square-anchor nesting
PCK-003  complete-prime-support adapter
PCK-004  square escape -> fresh prime direction
PCK-005  finite square prime expansion
PCK-006  primorial coarse -> fine anchor bridge
PCK-007  canonical 30 -> 960 regression
PCK-008  primitive kernel dichotomy wrapper
PCK-009  campaign closeout / generic abstraction audit
```

Only after PCK-009 should a new RH bridge project be opened.

## 11. Verification policy

Each Lean checkpoint must run at least:

```text
lake build <new-or-modified-module>
git diff --check
```

Public aggregator changes require building the affected aggregator.

Every new load-bearing theorem should be checked for unexpected axioms using `#print axioms` where practical.

## 12. Reporting

Each checkpoint writes

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveConservationKernel-260903-v0/report-NNN.md
```

with at least:

- Outcome
- repository/branch/starting HEAD
- changed files
- theorem surface
- exact reused Mathlib/DkMath theorems
- build result
- axiom/sorry audit
- deferred frontier
- next authorization

The repository is the source of truth. Conversation summaries are advisory only.
