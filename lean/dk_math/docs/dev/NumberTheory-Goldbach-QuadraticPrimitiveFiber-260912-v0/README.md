# Goldbach Quadratic Primitive Fiber — Astra Research Branch

Date: 2026-09-12  
Branch: `research/NumberTheory-Goldbach-QuadraticPrimitiveFiber-260912-v0`  
Status: research kickoff; no production theorem migration requested

This branch investigates whether the degree-two specialization of the canonical GTail boundary kernel gives a genuinely stronger finite structure for the Goldbach fixed-center fiber.

The working theme is:

```text
Goldbach fixed center
  -> degree-two GN / GTail boundary
  -> primitive scale normalization
  -> parity normalization
  -> coprime reflected endpoints
  -> separated left/right obstruction supports
  -> exact LL/LR/RR overlap decomposition
  -> LR product-modulus CRT geometry
  -> information-gain audit against the existing capacity theorem
```

The investigation is deliberately separated from production implementation. The authoritative task specification is `instruction-000.md`.

## Required research record

Astra must leave incremental reports `report-000.md` through `report-005.md` (or more if the investigation branches), a scratch Lean target, and a reproducible Python numerical experiment. Reports must be committed as the work progresses; a final chat summary is not a substitute for the research record.

## Current boundary

The existing Goldbach implementation already proves exact fixed-center GN equivalence, finite obstruction completeness, CRT full-period counting, survivor/capacity equivalence, overlap conservation, and the Pascal pair residual. Strong Goldbach remains unproved.

The recent GTail core refactor adds a general exact boundary gcd theorem whose degree-two specialization motivates this branch. The main question is not whether the primitive/parity reformulation is elegant, but whether it creates **strict information gain** over the existing Goldbach CRT/capacity ledger.

No production file under `DkMath/NumberTheory/Goldbach/**` or `DkMath/Lib/**` should be modified during this research pass.
