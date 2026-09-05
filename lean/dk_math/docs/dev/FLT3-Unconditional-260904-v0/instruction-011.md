# instruction-011 — Origin-Preserving Signed Cube Factorization

cid: 6a9aa2b0-937c-83e8-aa29-b3474c8acdf9

Branch: wip/flt3-unconditional-260904-v0

Prerequisite: FLT3U-008 completed with Outcome A.

Checkpoint role: FLT3U-009A.

## 1. Mission

FLT3U-008 の exact cube identities

$$
r\,s\,(r+s)=A^3,
$$

$$
r^2+rs+s^2=B,
$$

$$
\gcd(A,B)=1
$$

から、三つの signed factors

$$
r,\qquad s,\qquad r+s
$$

の absolute values が pairwise coprime な natural cubes であることを証明する。

同時に、現在の SignedThreeAdicPacket で失われている original triple provenance を最小限の public wrapper で回復し、descent measure

$$
A<a\,b\,c
$$

を kernel-checked に固定する。

この checkpoint ではまだ signed roots を正の FLT3 triple に並べ替えない。
それは FLT3U-009B の責務とする。

## 2. Why provenance repair is mandatory

現在の

    SignedThreeAdicPacket a b c

は type parameter として a,b,c を持つが、field には

    packet.distinguished = a / b / c

という relation を保持していない。

さらに

    signedThreeAdicPacket_of_primitive_solution

は Nonempty から Classical.choice で packet を選ぶため、後段から
「distinguished が original a,b,c のいずれか」と推論することはできない。

strict descent でこの gap を無視してはならない。

004A を破壊的に書き換えず、origin-preserving wrapper を追加する。

## 3. Read first

必須:

    lean/dk_math/DkMath/FLT/Three/SignedThreeAdic.lean
    lean/dk_math/DkMath/FLT/Three/SignedThreeAdicPowerSplit.lean
    lean/dk_math/DkMath/FLT/Three/EisensteinSectorExclusion.lean
    lean/dk_math/docs/dev/FLT3-Unconditional-260904-v0/report-010.md

禁止:

    DkMath.FLT.Main
    DkMath.FLT.Basic
    DkMath.FLT.Core
    DkMath.FLT.GEisensteinBridge
    DkMath.FLT.Five.*
    DkMath.FLT.Seven.*
    Mathlib.NumberTheory.FLT.Three

## 4. Add origin-preserving routing wrapper

Modify

    DkMath/FLT/Three/SignedThreeAdic.lean

by adding a public wrapper without changing the existing packet fields.

Candidate:

    structure SignedThreeAdicOriginPacket
        (a b c : ℕ) : Type where
      packet : SignedThreeAdicPacket a b c
      distinguished_cases :
        packet.distinguished = a ∨
        packet.distinguished = b ∨
        packet.distinguished = c

A stronger orientation-indexed equality is acceptable if Lean code remains simpler.

Mandatory constructor from the same private routing branches already used in
exists_signedThreeAdicPacket_of_primitive_solution:

    noncomputable def
      signedThreeAdicOriginPacket_of_primitive_solution
        {a b c : ℕ}
        (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
        (hab : Nat.Coprime a b)
        (hEq : a^3 + b^3 = c^3) :
        SignedThreeAdicOriginPacket a b c

Prefer constructing this inside SignedThreeAdic.lean where packet_of_a / packet_of_b /
packet_of_c and the mod-9 routing theorem are still available.

Do not attempt to prove provenance for an arbitrary SignedThreeAdicPacket.

## 5. Distinguished bounded by original product

For positive a,b,c, prove from distinguished_cases:

$$
\operatorname{distinguished}\le abc.
$$

Candidate theorem:

    theorem SignedThreeAdicOriginPacket.distinguished_le_product
        (p : SignedThreeAdicOriginPacket a b c)
        (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
        p.packet.distinguished ≤ a * b * c

Use only positivity and the three cases.

## 6. Proposed main module

Add:

    DkMath/FLT/Three/EisensteinDescentFactors.lean

Direct import:

    import DkMath.FLT.Three.EisensteinSectorExclusion

The updated SignedThreeAdic origin wrapper is visible transitively.

## 7. Build an origin-preserving exact-cube source

From a primitive solution, first choose the origin-preserving packet p0.

Then construct the existing chain from exactly p0.packet:

    signedThreeAdicPowerSplit_of_packet p0.packet
      -> eisensteinRamifierStrippedPacket_of_powerSplit
      -> eisensteinConjugateCoprimePacket_of_stripped
      -> eisensteinCubeUpToUnitPacket_of_conjugateCoprime
      -> eisensteinCubeSectorPacket_of_cubeUpToUnit
      -> eisensteinExactCubePacket_of_sectorPacket

Do not call the old
signedThreeAdicPowerSplit_of_primitive_solution
because that would make a second independent packet choice and lose provenance again.

Flatten the data needed for descent into one source packet.

Suggested surface:

    structure EisensteinDescentFactorSource
        (a b c : ℕ) : Type where
      origin : SignedThreeAdicOriginPacket a b c
      A B : ℕ
      r s : ℤ
      A_pos : 0 < A
      B_pos : 0 < B
      coprime_A_B : Nat.Coprime A B
      three_not_dvd_B : ¬ 3 ∣ B
      distinguished_eq :
        origin.packet.distinguished = 3 * A * B
      product_eq :
        r * s * (r + s) = (A : ℤ)^3
      norm_eq :
        r^2 + r*s + s^2 = (B : ℤ)

It is acceptable to additionally retain the exact packet for audit, but U009A public
theorems should not require reopening the entire nested chain.

Constructor:

    noncomputable def
      eisensteinDescentFactorSource_of_primitive_solution ...

No new mathematical choice beyond the existing split/cube choices is introduced.

## 8. Nonzero signed factors

From

$$
r\,s\,(r+s)=A^3
$$

and

$$
A>0
$$

prove:

$$
r\ne0,\qquad
s\ne0,\qquad
r+s\ne0.
$$

Mandatory wrappers or a conjunction theorem.

Consequently:

$$
|r|_{\rm nat}>0,\quad
|s|_{\rm nat}>0,\quad
|r+s|_{\rm nat}>0.
$$

## 9. Product of absolute factors

Take natAbs of product_eq and prove exact natural identity

$$
|r|\,|s|\,|r+s|=A^3.
$$

Candidate:

    theorem abs_factor_product_eq_A_cube
        (p : EisensteinDescentFactorSource a b c) :
        p.r.natAbs * p.s.natAbs * (p.r + p.s).natAbs =
          p.A ^ 3

Use Int.natAbs_mul and the positivity of A.

Do not introduce Real absolute values.

## 10. Pairwise coprimality of the three absolute factors

This is the central arithmetic step.

Prove:

$$
\gcd(|r|,|s|)=1,
$$

$$
\gcd(|r|,|r+s|)=1,
$$

$$
\gcd(|s|,|r+s|)=1.
$$

Preferred theorem surface:

    Nat.Coprime p.r.natAbs p.s.natAbs
    Nat.Coprime p.r.natAbs (p.r + p.s).natAbs
    Nat.Coprime p.s.natAbs (p.r + p.s).natAbs

Reason:

Any common divisor d of the relevant pair divides all needed linear combinations, hence
divides the Eisenstein norm

$$
B=r^2+rs+s^2.
$$

The same d also divides

$$
|r\,s\,(r+s)|=A^3.
$$

Since

$$
\gcd(A,B)=1,
$$

also

$$
\gcd(A^3,B)=1,
$$

so d=1.

For pairs (r,r+s) and (s,r+s), reduce to a common divisor of r and s by subtraction before applying the same argument.

Use Nat.Coprime / natAbs / divisibility APIs. Do not invoke prime factorization manually.

## 11. Generic natural cube split

Using the product identity and pairwise coprimality, prove existence of positive R,S,T : Nat such that

$$
|r|=R^3,
$$

$$
|s|=S^3,
$$

$$
|r+s|=T^3.
$$

Use Mathlib generic

    exists_eq_pow_of_mul_eq_pow

as in SignedThreeAdicPowerSplit.

Suggested staged split:

1. split |r| from |s|*|r+s|;
2. split |s| from |r+s|.

Do not reimplement prime valuation factorization.

## 12. Root positivity

Because r,s,r+s are nonzero and their absolute values are positive, prove

$$
R>0,\qquad S>0,\qquad T>0.
$$

These positivity facts are mandatory for U009B.

## 13. Pairwise coprimality of cube roots

From pairwise coprimality of their cubes derive

$$
\gcd(R,S)=1,
$$

$$
\gcd(R,T)=1,
$$

$$
\gcd(S,T)=1.
$$

Use Nat.coprime_pow_left/right_iff or the current equivalent API.

## 14. Root product equals A

From the three cube identities and

$$
|r|\,|s|\,|r+s|=A^3
$$

derive

$$
RST=A.
$$

Suggested method:

$$
(RST)^3=A^3
$$

then Nat power injectivity.

This theorem is mandatory.

## 15. Signed cube factor packet

Package the result.

Candidate:

    structure EisensteinSignedCubeFactors
        (a b c : ℕ) : Type where
      source : EisensteinDescentFactorSource a b c
      R S T : ℕ
      R_pos : 0 < R
      S_pos : 0 < S
      T_pos : 0 < T
      abs_r_eq : source.r.natAbs = R^3
      abs_s_eq : source.s.natAbs = S^3
      abs_sum_eq : (source.r + source.s).natAbs = T^3
      coprime_RS : Nat.Coprime R S
      coprime_RT : Nat.Coprime R T
      coprime_ST : Nat.Coprime S T
      root_product_eq : R * S * T = source.A

Constructor from source, and thin constructor directly from primitive solution.

## 16. Strict measure precursor

Using origin provenance and

$$
\operatorname{distinguished}=3AB,
$$

prove

$$
A<abc.
$$

Detailed chain:

$$
A<3AB
$$

because A,B>0, then

$$
3AB=\operatorname{distinguished}\le abc.
$$

Mandatory theorem:

    theorem source_A_lt_original_product
        (p : EisensteinDescentFactorSource a b c)
        (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
        p.A < a * b * c

or carry the original positivity inside source if preferred.

Then for signed cube factor packet:

$$
RST<abc.
$$

This is the exact strict-decrease numerical fact U009B will use after sign routing.

## 17. Critical stop gate

If pairwise coprimality fails, do not weaken the theorem silently.

Report the exact common divisor obstruction and stop Outcome B.

If provenance cannot be retained through the exact-cube chain without a second independent choice, do not identify two packets propositionally by proof irrelevance.

The same origin.packet must feed the entire downstream chain.

## 18. Non-goals

Do not implement yet:

- choosing signs of R,S,T
- constructing x^3+y^3=z^3 from the signed relation
- permuting the roots into a positive FLT3 triple
- the final strict descent packet
- strong induction / well-founded closure
- FLT_d3_unconditional
- positive-natural gcd normalization
- final public API

## 19. Required report

Create:

    report-011.md

Record:

1. provenance gap and exact wrapper added
2. origin-preserving packet constructor
3. exact-cube chain from the same origin.packet
4. flattened descent source fields
5. nonzero factor theorems
6. natAbs product = A^3
7. all three pairwise coprimality theorems
8. generic cube extraction used
9. R,S,T positivity
10. root pairwise coprimality
11. R*S*T=A
12. A < a*b*c
13. actual imports
14. focused build results
15. axiom audit
16. exact remaining sign-routing task for U009B
17. Outcome A / B / C

## 20. Verification

Focused builds:

    lake build DkMath.FLT.Three.SignedThreeAdic
    lake build DkMath.FLT.Three.EisensteinDescentFactors

Major provenance / factor constructors: #print axioms.

Required:

- no new sorry
- no project-specific axiom
- no completed FLT3 shortcut
- no FLT5 / FLT7 production import
- no GEisenstein provisional descent dependency

Classical.choice already inherent in exact cube extraction is acceptable.

## 21. Completion condition

FLT3U-009A is complete when a positive primitive solution produces positive pairwise-coprime roots R,S,T with

$$
|r|=R^3,
$$

$$
|s|=S^3,
$$

$$
|r+s|=T^3,
$$

$$
RST=A,
$$

and the strict measure precursor

$$
RST=A<abc.
$$

Stop there.

FLT3U-009B will use the signed equality r+s=(r+s) to permute R,S,T into a new positive primitive FLT3 solution whose product is exactly A and hence strictly smaller than abc.
