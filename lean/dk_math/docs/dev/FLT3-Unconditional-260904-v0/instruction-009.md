# instruction-009 — Eisenstein Unit Classes Modulo Cubes

cid: 6a9aa2b0-937c-83e8-aa29-b3474c8acdf9

Branch: wip/flt3-unconditional-260904-v0

Prerequisite: FLT3U-006B completed with Outcome A.

Checkpoint role: FLT3U-007.

## 1. Mission

EisensteinCubeUpToUnitPacket の

$$
\beta=\varepsilon\gamma^3,
\qquad
\varepsilon\in E^\times
$$

に現れる Eisenstein unit を完全分類し、cube factor を吸収した三つの canonical sector

$$
1,\qquad \tau,\qquad \tau^2
$$

へ正規化する。

この checkpoint では sector exclusion、exact cube 化、strict descent へ進まない。

## 2. Read first

必須:

    lean/dk_math/DkMath/FLT/Three/EisensteinCubeExtraction.lean
    lean/dk_math/DkMath/FLT/Three/EisensteinSubstrate.lean
    lean/dk_math/DkMath/FLT/Three/EisensteinEuclidean.lean
    lean/dk_math/docs/dev/FLT3-Unconditional-260904-v0/report-008.md

architecture 参考のみ:

    lean/dk_math/DkMath/FLT/Seven/QuadraticUnits.lean

FLT7 module を production import しない。

## 3. Proposed module

第一候補:

    DkMath/FLT/Three/EisensteinUnitSectors.lean

direct import:

    import DkMath.FLT.Three.EisensteinCubeExtraction

だけで足りるならこれを優先する。

禁止:

    DkMath.FLT.Main
    DkMath.FLT.Basic
    DkMath.FLT.Core
    DkMath.FLT.GEisensteinBridge
    DkMath.FLT.Five.*
    DkMath.FLT.Seven.*
    Mathlib.NumberTheory.FLT.Three

## 4. Unit iff norm one

Concrete Eisenstein norm は positive-definite であり、U006A で domain / Euclidean structure は完成している。

まず production theorem として

$$
\operatorname{IsUnit}(x)
\iff
N(x)=1
$$

を固定する。

Forward direction:

x * y = 1 for a unit inverse y, norm multiplicativity, norm nonnegativityより

$$
N(x)N(y)=1
$$

なので

$$
N(x)=1.
$$

Backward directionは既存

    eisenstein_isUnit_of_norm_eq_one

を再利用する。

候補:

    theorem eisenstein_isUnit_iff_norm_eq_one
        {x : EisensteinInt} :
        IsUnit x ↔ norm x = 1

## 5. Solve norm-one coordinates exactly

For

$$
x=r+s\tau
$$

the equation

$$
N(x)=r^2+rs+s^2=1
$$

has exactly six integer solutions.

Use

$$
4N(x)=(2r+s)^2+3s^2
$$

to bound s, then finite integer cases.

Mandatory coordinate classification:

$$
(r,s)\in
\{(1,0),(-1,0),(0,1),(0,-1),(-1,1),(1,-1)\}.
$$

Equivalent element classification:

$$
x\in
\{1,-1,\tau,-\tau,\tau^2,-\tau^2\}.
$$

Recall current convention:

$$
\tau^2=\tau-1,
$$

so

$$
\tau^2=(-1,1).
$$

Do not accidentally use the classical omega coordinate sign convention.

Suggested theorem:

    theorem eisenstein_norm_eq_one_iff_six_units
        (x : EisensteinInt) :
        norm x = 1 ↔
          x = 1 ∨
          x = -1 ∨
          x = eisensteinTau ∨
          x = -eisensteinTau ∨
          x = eisensteinTau ^ 2 ∨
          x = -(eisensteinTau ^ 2)

Exact disjunction order may differ.

## 6. Complete unit classification

Combine sections 4 and 5:

    theorem eisenstein_isUnit_iff_six_units
        {x : EisensteinInt} :
        IsUnit x ↔
          ...

Also provide a Units-facing theorem for

    epsilon : EisensteinIntˣ

classifying its coerced value.

Candidate:

    theorem eisensteinUnit_cases
        (epsilon : EisensteinIntˣ) :
        (epsilon : EisensteinInt) = 1 ∨
        ...

This is the public classification surface U007 needs.

## 7. Cube behavior of tau

Existing substrate already provides

$$
\tau^3=-1,
$$

$$
\tau^6=1.
$$

Add only thin helpers actually needed for sign absorption.

Mandatory practical identity:

$$
(\tau\gamma)^3=-\gamma^3.
$$

Candidate:

    theorem tau_mul_cube_absorbs_neg
        (gamma : EisensteinInt) :
        (eisensteinTau * gamma) ^ 3 = -(gamma ^ 3)

Prove via mul_pow and eisenstein_tau_cube.

Do not create a general roots-of-unity theory.

## 8. Three canonical sectors

Define a finite sector type.

Candidate:

    inductive EisensteinUnitSector
      | one
      | tau
      | tauSq
      deriving DecidableEq, Repr

Define representative:

    def EisensteinUnitSector.rep :
        EisensteinUnitSector → EisensteinInt
      | .one => 1
      | .tau => eisensteinTau
      | .tauSq => eisensteinTau ^ 2

Prove representative norm:

$$
N(\operatorname{rep}(s))=1.
$$

and optionally IsUnit representative.

## 9. Unit modulo cube normalization

Every Eisenstein unit differs from exactly one chosen representative by a cube-unit factor, at least as an existence theorem.

Mandatory existence surface:

$$
\forall\varepsilon\in E^\times,\quad
\exists s,\exists\delta,
\quad
\operatorname{IsUnit}(\delta)
\land
\varepsilon=\operatorname{rep}(s)\delta^3.
$$

Lean candidate:

    theorem exists_sector_mul_cube_of_unit
        (epsilon : EisensteinIntˣ) :
        ∃ sector : EisensteinUnitSector,
          ∃ delta : EisensteinInt,
            IsUnit delta ∧
            (epsilon : EisensteinInt) =
              sector.rep * delta ^ 3

If convenient, prefer

    delta : EisensteinIntˣ

instead of an element plus IsUnit proof.

Expected finite proof:

- +1       -> sector one, delta = 1
- -1       -> sector one, delta = tau
- +tau     -> sector tau, delta = 1
- -tau     -> sector tau, delta = tau
- +tau^2   -> sector tauSq, delta = 1
- -tau^2   -> sector tauSq, delta = tau

because

$$
\tau^3=-1.
$$

Do not require uniqueness of sector in this checkpoint unless it is essentially free.

Existence is mandatory.

## 10. Normalize beta factorization to sector form

Starting packet:

$$
\beta=\varepsilon\gamma^3.
$$

From

$$
\varepsilon=\rho\delta^3
$$

obtain

$$
\beta=\rho(\delta\gamma)^3.
$$

Create a downstream packet that forgets the arbitrary unit and retains only the canonical sector.

Candidate:

    structure EisensteinCubeSectorPacket
        (a b c : ℕ) : Type where
      cubeUpToUnit : EisensteinCubeUpToUnitPacket a b c
      sector : EisensteinUnitSector
      gamma : EisensteinInt
      beta_eq :
        cubeUpToUnit.conjugateCoprime.stripped.beta =
          sector.rep * gamma ^ 3

The new gamma is the adjusted gamma after absorbing delta.

The old epsilon / gamma remain reachable through cubeUpToUnit for audit, but downstream U008 should use the normalized sector and new gamma.

## 11. Constructor

Mandatory:

    noncomputable def eisensteinCubeSectorPacket_of_cubeUpToUnit
        (p : EisensteinCubeUpToUnitPacket a b c) :
        EisensteinCubeSectorPacket a b c

Classical.choice is acceptable for the finite existential sector normalization.

A primitive-solution wrapper is optional if short.

## 12. Preserve the decisive stripped data

The normalized sector packet must still expose through its parent packet:

$$
\beta_{\rm snd}=3A^3,
$$

$$
N(\beta)=B^3,
$$

$$
\gcd(A,B)=1,
$$

$$
3\nmid B.
$$

Do not duplicate these as fields unless a thin theorem wrapper materially improves U008.

## 13. Optional sector representative coordinate formulas

If cheap, expose:

$$
\operatorname{rep}(1)=(1,0),
$$

$$
\operatorname{rep}(\tau)=(0,1),
$$

$$
\operatorname{rep}(\tau^2)=(-1,1).
$$

These will make U008 coordinate arithmetic simpler.

## 14. Important boundary

Do not eliminate tau / tauSq sectors in this checkpoint.

Even though U008 is expected to use

$$
\beta_{\rm snd}=3A^3
$$

plus sector coordinate formulas and

$$
3\nmid B
$$

to rule out nontrivial sectors, that argument belongs to FLT3U-008.

U007 ends with three sectors still alive.

## 15. Non-goals

Do not implement:

- sector tau contradiction
- sector tauSq contradiction
- exact beta = gamma^3
- coordinate factorization A^3 = r*s*(r+s)
- pairwise coprimality of r,s,r+s
- smaller primitive FLT3 solution
- strict descent
- well-founded closure
- final FLT3 theorem

NoSqOnS0 adapters are unchanged.

## 16. Required report

Create:

    report-009.md

Record:

1. IsUnit iff norm = 1 theorem
2. exact six norm-one coordinate solutions
3. six-unit element classification
4. Units-facing classification theorem
5. tau cube sign-absorption theorem
6. sector type and representatives
7. representative norm / unit facts
8. unit modulo cube normalization theorem
9. normalized EisensteinCubeSectorPacket
10. constructor surface
11. actual imports
12. focused build result
13. axiom audit
14. exact U008 sector-exclusion gate
15. Outcome A / B / C

## 17. Verification

focused build:

    lake build DkMath.FLT.Three.EisensteinUnitSectors

Major classification / constructor theorems: #print axioms.

Required:

- no new sorry
- no project-specific axiom
- no completed FLT3 shortcut
- no FLT5 / FLT7 production import
- no provisional GEisenstein descent dependency

## 18. Completion condition

FLT3U-007 is complete when every cube-up-to-unit packet produces

$$
\beta=\rho\gamma^3
$$

with

$$
\rho\in\{1,\tau,\tau^2\},
$$

while retaining the stripped identity

$$
\beta_{\rm snd}=3A^3.
$$

Stop there.

FLT3U-008 will use the sector-specific second-coordinate formulas to exclude the nontrivial sectors.
