# DkMath

DkMath is an experimental Lean 4 mathematics library developed through number-theory research by D. and Wise Wolf (AI-GPT).

## Cosmic Formula

An identity designated as the "Cosmic Formula"

$$
\Large
N+1=(P+1)^2
$$

$$
N = P(P+2)
$$

$$
x=P
$$

$$
f(x) = (x+1)^2 - x(x+2) = 1
$$

A project exploring new perspectives on number-theoretic objects, taking this identity as a starting point.

$$
\large
(x+u)^d-u^d=x\ GN_d(x,u)
$$

$$
\large
x\,GN_d(x,u):=x\,\sum_{k=0}^{d-1}\binom{d}{k}x^{d-1-k}\,u^{k}
$$

e.g.

$$
\begin{array}{lc}
x\ GN_1(x,u) =& x \qquad \cancel{+ u - u}\\
x\ GN_2(x,u) =& x^2 + 2xu \qquad \cancel{+ u^2 - u^2}\\
x\ GN_3(x,u) =& x^3 + 3x^2u + 3xu^2 \qquad \cancel{+ u^3 - u^3}\\
x\ GN_4(x,u) =& x^4 + 4x^3u + 6x^2u^2 + 4xu^3 \qquad \cancel{+ u^4 - u^4}\\
\end{array}
$$

---

現在の公開面では、まず **Lean の kernel まで閉じた成果** を前面に置き、その研究過程から一般化・再利用できた数学を `DkMath.Lib.*` へ昇格する方針を採っている。

> [!IMPORTANT]
> この README で「completed / 完了」と記すものは、DkMath 内で対象 theorem の Lean proof が閉じ、所定の build / axiom audit が記録されていることを意味する。
> 歴史的な新規性、外部査読、数学界での受容を意味しない。

## Verified completed results

### FLT3 — Fermat's Last Theorem for exponent 3

$$
\Large
x,y,z\in\mathbb N_{>0}
\quad\Longrightarrow\quad
x^3+y^3\ne z^3
$$

現在の独立 public surface は `DkMath.FLT.Three`。最終 endpoint は次である。

```lean
DkMath.FLT.Three.fermatThree_no_positive_solution
```

proof route は概略、

```text
positive solution
  -> gcd normalization
  -> primitive cubic packet
  -> signed 3-adic routing
  -> Eisenstein arithmetic
  -> unit-sector exclusion
  -> strict descent
  -> contradiction
```

となる。旧 `DkMath.FLT.Main` の `FLT_d3_by_padicValNat` / `hS0_not_sq` / `NoSqOnS0` を proof step として使用しない独立 tower である。

- Public Lean API: [`DkMath.FLT.Three`](./lean/dk_math/DkMath/FLT/Three.lean)
- Final implementation report: [`FLT3-Unconditional report-014`](./lean/dk_math/docs/dev/FLT3-Unconditional-260904-v0/report-014.md)
- Standalone exhibition project: <https://github.com/Deskuma/flt3_dk_math_lean4>

### FLT5 — Fermat's Last Theorem for exponent 5

$$
\Large
x,y,z\in\mathbb N_{>0}
\quad\Longrightarrow\quad
x^5+y^5\ne z^5
$$

public surface は `DkMath.FLT.Five`。主要 endpoint は次である。

```lean
DkMath.FLT.Five.flt5Target
DkMath.FLT.Five.fermatFive_no_positive_solution
```

proof route は GN5、5-adic factor splitting、golden order、unit classes、zero-sector strict descent を通る。

- Public Lean API: [`DkMath.FLT.Five`](./lean/dk_math/DkMath/FLT/Five.lean)
- Axiom audit entry point: [`DkMathTest/FLT/Five/CheckAxioms.lean`](./lean/dk_math/DkMathTest/FLT/Five/CheckAxioms.lean)
- Standalone exhibition project: <https://github.com/Deskuma/flt5_dk_math_lean4>
- Explanatory documents are also published in the standalone project.

For both completed FLT endpoints, the recorded endpoint axiom surface is:

```text
propext
Classical.choice
Quot.sound
```

with no `sorryAx` or DkMath-defined axiom in the audited endpoint.

### Infinitely many primes from the Cosmic Formula boundary

DkMath also contains a Lean proof route from the Cosmic Formula boundary structure to Euclid's infinitude of primes.

With

$$
\text{cosmicN}(P)=P(P+2),
$$

we have

$$
\text{cosmicN}(P)+1=(P+1)^2.
$$

The formal route constructs a prime outside any finite set of primes from the boundary term and derives:

```lean
DkMath.CosmicFormula.euclid_from_cosmic_boundary
```

and the Comparator challenge endpoint:

```lean
InfinitudeOfPrimes
```

- Proof guide: [`DkMath/Samples/Prime/README.md`](./lean/dk_math/DkMath/Samples/Prime/README.md)
- Lean source: [`DkMath/Samples/Prime/A.lean`](./lean/dk_math/DkMath/Samples/Prime/A.lean)

## DkMath.Lib — reusable mathematics promoted from research

DkMath の現在の設計上の主語は、個別研究で得た補題をそのまま増やし続けることではなく、研究依存性を外せる部分を **中立な再利用可能 API** として `DkMath.Lib.*` へ昇格することである。

```lean
import DkMath.Lib
```

で、現在 aggregator に載っている promoted layer をまとめて import できる。

なお、`DkMath.Lib.*` 配下には generalization 側から直接 import されている neutral module もあり、すべてが aggregator に載っているわけではない。

### Cosmic / GTail kernel

GN 系で繰り返し現れた二項展開の tail は、現在 `GTail` として一般化されている。

$$
\begin{aligned}
(x+u)^d &\;=\; \sum_{j < r}\binom dj x^j u^{d-j}\\
&\qquad +x^r\,\text{GTail}(d,r,x,u).
\end{aligned}
$$

標準 GN は $r=1$ specialization である。

$$
GN_d(x,u)=\text{GTail}(d,1,x,u).
$$

現在の promoted modules には次がある。

- `DkMath.Lib.Cosmic.GTail` — general tail decomposition
- `GTailBoundary` — exact gcd / boundary structure
- `GTailCongruence` — congruence and prime-divisibility consequences
- `GTailCyclotomic` — cyclotomic shell bridge
- `GTailNat` — natural-number divisibility
- `GTailPadic` — `padicValNat` consequences
- `GTailPascal` — finite-depth Pascal filtration

GN5 hackathon work is therefore best viewed as one of the major origins of this reusable layer rather than as the final abstraction itself.

### Number-theory kernels

The `DkMath.Lib.NumberTheory.*` namespace currently contains reusable components for:

- `padicValNat` utilities;
- coprime power-factor splitting;
- ideal $p$-th-power extraction and class-group $p$-torsion interfaces;
- principal-ideal to element-power bridges;
- unit power sectors;
- `TraceOneInt` lattice landing and square/power-image criteria;
- neutral Eisenstein coordinates and lattice landing;
- squarefree residual extraction.

See [`DkMath.Lib README`](./lean/dk_math/DkMath/Lib/README.md) for the current module map.

## Cosmic Formula and GN

The project began from the identity called the Cosmic Formula:

$$
N+1=(P+1)^2,
\qquad
N=P(P+2).
$$

A higher-degree gap-normalized form is

$$
(x+u)^d-u^d=x\,GN_d(x,u).
$$

The research history started from these structures, but current reusable code increasingly expresses their neutral algebra through `DkMath.Lib.Cosmic.GTail` rather than fixed-degree GN-only APIs.

## Active research — not completed general claims

### FLT odd-prime generalization

The current generalization architecture has progressed well beyond the older `PrimeProvider`-only description. The latest bounded closeout reaches:

```text
PrimeAdicFactorPacket
  -> exact GTail p-adic split
  -> arbitrary-prime QR/QNR TraceOne coordinates
  -> primitive coordinates
  -> prime-discriminant maximal order / Dedekind domain
  -> discriminant-axis strip
  -> conjugate-coprime residual ideals
  -> residual principal ideal = idealRoot^p
  -> [classGroupPTorsionFreeAt]
  -> unit * element^p
  -> unit-sector normalization
```

This is **not** a general FLT proof. The explicit remaining frontiers are:

1. the class-group $p$-torsion / principalization hypothesis;
2. nonzero unit-sector elimination in the real branch $p\equiv1\pmod4$;
3. the `p = 3` carrier/API bridge if it is to be folded into the same generic facade.

- Current closeout: [`FLT Prime Generalization summary-026`](./lean/dk_math/docs/refact/FLT-Prime-Generalization-260911-v0/summary-026.md)
- FLT subsystem guide: [`DkMath/FLT/README.md`](./lean/dk_math/DkMath/FLT/README.md)

Other research directories (ABC, Goldbach, CF2D, RH, Legendre, Primitive Conservation, MultiGauge, etc.) remain active experimental workspaces. Their presence in the repository must not be read as a completed proof claim unless a completed public endpoint and audit are explicitly documented.

## Project history

OpenAI Build Week work on Cosmic Formula inversion / GN5 was an important development stage. It led into the completed FLT5 tower and, later, into extraction of neutral kernels now living under `DkMath.Lib.*`.

The repository also contains the separate **Breaking Math Verification** hackathon project and its reusable verification certificate API. These are retained as project history and tooling examples rather than as the main description of DkMath's current mathematical core.

- Hackathon index: [`DkMath/Hackathon/README.md`](./lean/dk_math/DkMath/Hackathon/README.md)
- Verification docs: [`docs/verification/README.md`](./lean/dk_math/docs/verification/README.md)

## Repository guide

- Root `README.md` — public project overview and completed headline results.
- [`docs/PROJECT_STATUS.md`](./docs/PROJECT_STATUS.md) — authoritative dated technical status.
- [`lean/dk_math/README.md`](./lean/dk_math/README.md) — Lean implementation entry point and build guide.
- [`lean/dk_math/DkMath/FLT/README.md`](./lean/dk_math/DkMath/FLT/README.md) — FLT-specific current / legacy route map.
- [`lean/dk_math/DkMath/Lib/README.md`](./lean/dk_math/DkMath/Lib/README.md) — promoted reusable-library map.
- `lean/dk_math/docs/dev/*`, `docs/feature/*`, `docs/refact/*` — dated research records. These are historical snapshots unless explicitly marked current.

## Branches

> [!IMPORTANT]
> `main` may lag active development. `nightly` is the public latest-development branch; `develop` may contain more immediate work in progress.

For the exact state used by this documentation refactor, see the snapshot provenance in [`docs/PROJECT_STATUS.md`](./docs/PROJECT_STATUS.md).

## Language

Japanese is the primary project communication language. Public theorem names, Lean APIs, and concise English descriptions are kept where useful; older documents may contain mixed Japanese/English text.

## License

MIT License. For research use, cite the relevant theorem names and source paths together with the repository revision used.
