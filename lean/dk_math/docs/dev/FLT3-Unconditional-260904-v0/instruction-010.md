# instruction-010 — Sector Arithmetic Exclusion and Exact Cube Sector

cid: 6a9aa2b0-937c-83e8-aa29-b3474c8acdf9

Branch: wip/flt3-unconditional-260904-v0

Prerequisite: FLT3U-007 completed with Outcome A.

Checkpoint role: FLT3U-008.

## 1. Mission

EisensteinCubeSectorPacket の三 sector

$$
1,\qquad \tau,\qquad \tau^2
$$

を、stripped packet の exact second coordinate

$$
\beta_{\rm snd}=3A^3
$$

および

$$
3\nmid B
$$

と比較する。

目標は tau / tauSq sector を有限算術で排除し、唯一残る one sector から

$$
\beta=\gamma^3
$$

と

$$
rs(r+s)=A^3
$$

を production theorem として固定することである。

この checkpoint ではまだ strict descent を構成しない。

## 2. Read first

必須:

    lean/dk_math/DkMath/FLT/Three/EisensteinUnitSectors.lean
    lean/dk_math/DkMath/FLT/Three/EisensteinCubeExtraction.lean
    lean/dk_math/DkMath/FLT/Three/EisensteinSubstrate.lean
    lean/dk_math/docs/dev/FLT3-Unconditional-260904-v0/report-009.md

直接 import は原則として

    import DkMath.FLT.Three.EisensteinUnitSectors

のみ。

禁止:

    DkMath.FLT.Main
    DkMath.FLT.Basic
    DkMath.FLT.Core
    DkMath.FLT.GEisensteinBridge
    DkMath.FLT.Five.*
    DkMath.FLT.Seven.*
    Mathlib.NumberTheory.FLT.Three

## 3. Proposed module

第一候補:

    DkMath/FLT/Three/EisensteinSectorExclusion.lean

## 4. Fix gamma coordinates

For a sector packet p, write

$$
\gamma=r+s\tau.
$$

Use

    r := p.gamma.fst
    s := p.gamma.snd

or local abbreviations only.

Do not introduce a second coordinate structure.

Existing cube formula:

$$
\gamma^3=
\left(r^3-3rs^2-s^3\right)
+
\left(3rs(r+s)\right)\tau.
$$

Reuse eisenstein_cube_coords / eisenstein_cube_snd.

## 5. Sector-specific second-coordinate formulas

Prove exact formulas for each representative.

### one sector

$$
(\gamma^3)_{\rm snd}=3rs(r+s).
$$

This is already eisenstein_cube_snd.

### tau sector

Since

$$
\tau(u+v\tau)=(-v)+(u+v)\tau,
$$

for gamma cubed obtain

$$
(\tau\gamma^3)_{\rm snd}
=
r^3+3r^2s-s^3.
$$

Mandatory theorem.

Modulo 3 this is

$$
(\tau\gamma^3)_{\rm snd}
\equiv
r^3-s^3
\equiv
r-s
\pmod3.
$$

### tauSq sector

Since

$$
\tau^2=(-1,1),
$$

obtain

$$
(\tau^2\gamma^3)_{\rm snd}
=
r^3-3rs^2-s^3.
$$

Mandatory theorem.

Modulo 3 again:

$$
(\tau^2\gamma^3)_{\rm snd}
\equiv
r^3-s^3
\equiv
r-s
\pmod3.
$$

Verify signs in the trace-one convention. Do not copy omega-basis formulas.

## 6. Norm gamma equals B

Every sector representative has norm one.

From

$$
\beta=\rho\gamma^3,
$$

$$
N(\rho)=1,
$$

$$
N(\beta)=B^3,
$$

derive

$$
N(\gamma)^3=B^3.
$$

Since Eisenstein norm is nonnegative and B is natural, prove the exact integer equality

$$
N(\gamma)=B.
$$

Mandatory theorem surface, for example:

    theorem EisensteinCubeSectorPacket.gamma_norm_eq_B
        (p : EisensteinCubeSectorPacket a b c) :
        norm p.gamma = (p...B : ℤ)

Use injectivity / monotonicity of cube on integers or a short nlinarith argument with nonnegativity.

Do not merely prove equality of absolute values.

## 7. Mod-3 norm lemma

Prove the elementary coordinate lemma:

If

$$
3\mid(r-s),
$$

then

$$
3\mid r^2+rs+s^2.
$$

Equivalent modulo-3 proof:

$$
r\equiv s
\Longrightarrow
r^2+rs+s^2
\equiv 3r^2
\equiv0.
$$

Use Int divisibility or ZMod 3, whichever is smallest.

Candidate:

    theorem three_dvd_eisenstein_norm_of_three_dvd_sub
        {r s : ℤ}
        (h : (3 : ℤ) ∣ r - s) :
        (3 : ℤ) ∣ norm (eisensteinCoord r s)

This theorem is central to excluding both nontrivial sectors.

## 8. Exclude tau sector

Assume

    p.sector = .tau

Then p.beta_eq plus beta_snd from the stripped parent gives

$$
(\tau\gamma^3)_{\rm snd}=3A^3.
$$

Hence 3 divides the left side.

Using the tau-sector modulo-3 formula, derive

$$
3\mid r-s.
$$

Then section 7 gives

$$
3\mid N(\gamma).
$$

Using

$$
N(\gamma)=B
$$

derive

$$
3\mid B,
$$

contradicting existing

$$
3\nmid B.
$$

Mandatory theorem:

    theorem tau_sector_false
        (p : EisensteinCubeSectorPacket a b c)
        (hsector : p.sector = .tau) :
        False

or equivalent.

## 9. Exclude tauSq sector

Exactly the same structure.

Mandatory:

    theorem tauSq_sector_false
        (p : EisensteinCubeSectorPacket a b c)
        (hsector : p.sector = .tauSq) :
        False

Do not duplicate large proofs unnecessarily. A shared helper taking a sector-specific mod-3 second-coordinate theorem is acceptable.

## 10. Force one sector

With the inductive sector type having exactly three constructors, derive

$$
p.sector=\text{one}.
$$

Mandatory:

    theorem sector_eq_one
        (p : EisensteinCubeSectorPacket a b c) :
        p.sector = .one

This is the primary exclusion result.

## 11. Exact cube

Rewrite p.beta_eq using sector_eq_one and rep(.one)=1 to obtain

$$
\beta=\gamma^3.
$$

Mandatory theorem:

    theorem beta_eq_cube
        (p : EisensteinCubeSectorPacket a b c) :
        p.cubeUpToUnit.conjugateCoprime.stripped.beta =
          p.gamma ^ 3

No unit factor remains.

This is the first exact-cube theorem in the unconditional FLT3 tower.

## 12. Exact cubic product identity

Use

$$
\beta_{\rm snd}=3A^3
$$

and

$$
(\gamma^3)_{\rm snd}=3rs(r+s)
$$

to cancel 3 in integers and obtain

$$
rs(r+s)=A^3.
$$

Mandatory theorem:

$$
r\,s\,(r+s)=A^3.
$$

Candidate:

    theorem gamma_coordinate_product_eq_A_cube
        (p : EisensteinCubeSectorPacket a b c) :
        p.gamma.fst * p.gamma.snd *
          (p.gamma.fst + p.gamma.snd) =
        (p...A : ℤ) ^ 3

Exact association may be normalized by ring.

This identity is the launch point for U009.

## 13. Preserve norm identity

Also retain / expose

$$
r^2+rs+s^2=B.
$$

A thin theorem wrapper from gamma_norm_eq_B and eisenstein_norm_coords is useful:

    theorem gamma_coordinate_norm_eq_B ...

This gives U009 both equations:

$$
rs(r+s)=A^3,
$$

$$
r^2+rs+s^2=B.
$$

## 14. Optional nonzero facts

If immediate from

$$
A>0
$$

and the product identity, expose

$$
r\ne0,\qquad
s\ne0,\qquad
r+s\ne0.
$$

These will be useful for strict descent and pairwise coprimality.

Only add if short.

Do not start sign normalization or absolute-value descent here.

## 15. Production packet

Create a thin exact-cube packet for downstream descent.

Candidate:

    structure EisensteinExactCubePacket
        (a b c : ℕ) : Type where
      sectorPacket : EisensteinCubeSectorPacket a b c
      sector_one : sectorPacket.sector = .one
      beta_eq_cube :
        sectorPacket.cubeUpToUnit.conjugateCoprime.stripped.beta =
          sectorPacket.gamma ^ 3
      coordinate_product :
        sectorPacket.gamma.fst * sectorPacket.gamma.snd *
          (sectorPacket.gamma.fst + sectorPacket.gamma.snd) =
        (sectorPacket...A : ℤ) ^ 3
      coordinate_norm :
        norm sectorPacket.gamma =
          (sectorPacket...B : ℤ)

Fields may be reduced if theorem wrappers avoid duplication.

Mandatory is that U009 can consume one object without re-running sector cases.

Constructor:

    def / noncomputable def
      eisensteinExactCubePacket_of_sectorPacket ...

Since sectorPacket is already chosen noncomputably, this constructor itself should not need new choice.

## 16. Non-goals

Do not implement:

- pairwise coprimality of r, s, r+s
- splitting each into signed cubes
- sign normalization
- smaller primitive FLT3 triple
- strict decrease proof
- well-founded descent
- final FLT3 theorem
- positive-natural normalization
- NoSqOnS0 changes

## 17. Required report

Create:

    report-010.md

Record:

1. tau-sector second-coordinate formula
2. tauSq-sector second-coordinate formula
3. gamma norm = B theorem
4. mod-3 norm divisibility lemma
5. tau sector contradiction
6. tauSq sector contradiction
7. sector = one theorem
8. beta = gamma^3 exact theorem
9. rs(r+s)=A^3 theorem
10. coordinate norm = B theorem
11. exact-cube packet surface
12. actual imports
13. focused build result
14. axiom audit
15. exact remaining U009 descent-reconstruction gate
16. Outcome A / B / C

## 18. Verification

focused build:

    lake build DkMath.FLT.Three.EisensteinSectorExclusion

Major theorems / packet constructor: #print axioms.

Required:

- no new sorry
- no project-specific axiom
- no completed FLT3 shortcut
- no FLT5 / FLT7 production import
- no provisional GEisenstein descent dependency

## 19. Completion condition

FLT3U-008 is complete when every sector packet is forced into the one sector and yields

$$
\beta=\gamma^3,
$$

$$
r\,s\,(r+s)=A^3,
$$

$$
r^2+rs+s^2=B,
$$

with the original

$$
\gcd(A,B)=1,
\qquad
3\nmid B.
$$

Stop there.

FLT3U-009 will analyze the signed factors r, s, r+s and reconstruct a strict smaller primitive cubic counterexample.
