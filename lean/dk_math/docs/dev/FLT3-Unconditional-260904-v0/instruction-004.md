# instruction-004 — Signed Three-Adic Routing and Exact Power Split

cid: 6a9aa2b0-937c-83e8-aa29-b3474c8acdf9

Branch: wip/flt3-unconditional-260904-v0

Prerequisite: FLT3U-003 completed with Outcome A.

Checkpoint role: FLT3U-004A.

## 1. Mission

primitive FLT3 counterexample を mod 9 で signed orientation へ正規化し、ramified prime 3 の natural-number ownership を exact に固定する。

この checkpoint の最終出力は

$$
\operatorname{carrier}=3^2 A^3,
$$

$$
\operatorname{residual}=3 B^3,
$$

$$
\operatorname{distinguished}=3AB
$$

という exact power split である。

Eisenstein ramifier lambda 自体を除去して beta を構成するのは次の FLT3U-004B とする。

## 2. Critical distinction

FLT3U-001 / U002 の primitive prime q と、今回の ramified prime 3 を混同しない。

U001 / U002:

    q is prime
    q != 3
    q divides GN3
    v_q(GN3) is a positive multiple of 3

これは non-ramified split-prime / Hensel load である。

U004A:

    prime 3
    ramified axis lambda = 1 + tau
    residual has exact 3-adic depth 1
    remaining 3-adic load belongs to carrier

これは global ramifier ownership である。

二つは後続の norm / conjugate factorization で合流する。

## 3. Read first

必須:

    lean/dk_math/DkMath/FLT/Three/EisensteinSubstrate.lean
    lean/dk_math/DkMath/FLT/Three/CubicValuationDepth.lean
    lean/dk_math/docs/dev/FLT3-Unconditional-260904-v0/report-003.md
    lean/dk_math/DkMath/FLT/PhaseLift.lean

参考として architecture のみ読む:

    lean/dk_math/DkMath/FLT/Five/SignedFiveAdic.lean
    lean/dk_math/DkMath/FLT/Five/SignedFiveAdicPowerSplit.lean

FLT5 module を production import してはならない。

必要なら Petal / gcd の current theorem を調査する。

候補:

    gcd_sub_S0_nat_eq_gcd_sub_three
    gcd_sub_S0_nat_dvd_three
    coprime_sub_S0_nat_of_coprime_of_not_dvd_three

exact identifier / namespace は current source を正本とする。

## 4. Proposed modules

第一候補:

    DkMath/FLT/Three/SignedThreeAdic.lean
    DkMath/FLT/Three/SignedThreeAdicPowerSplit.lean

最初の module が signed orientation と common packet を所有する。

二つ目が exact cube split のみを所有する。

一ファイルに収めた方が十分小さい場合は統合してよいが、mod-9 routing と power extraction の責務は theorem surface 上で分離する。

## 5. Primitive input

入口は positive primitive solution:

$$
a^3+b^3=c^3,
$$

$$
a,b,c>0,
$$

$$
\gcd(a,b)=1.
$$

既存 coprime_cb_of_eq 等を使って必要な pairwise coprimality を回収する。

completed FLT3 theorem は使用しない。

## 6. Mod-9 routing theorem

primitive cubic solution では cubes modulo 9 の有限分類から、3 は a,b,c のちょうど一つに所属する。

この事実を Lean で有限分類として証明する。

推奨:

- residues modulo 9
- Fin 9 / ZMod 9
- norm_num, decide, interval_cases

のいずれか最小の方法。

巨大な abstract congruence framework は作らない。

最終的に次の三 orientation のいずれかへ送る。

### Branch A — a is distinguished

Assume / derive:

$$
3\mid a.
$$

Use

$$
c^3-b^3=a^3.
$$

Set

$$
\operatorname{carrier}=c-b,
$$

$$
\operatorname{residual}=c^2+cb+b^2=S_0(c,b),
$$

$$
\operatorname{distinguished}=a.
$$

Eisenstein signed coordinate:

$$
\alpha=(-c,-b).
$$

Then

$$
N(\alpha)=\operatorname{residual}
$$

and

$$
\alpha_{\rm snd}-\alpha_{\rm fst}=\operatorname{carrier}.
$$

### Branch B — b is distinguished

Symmetric to Branch A.

Use

$$
c^3-a^3=b^3,
$$

$$
\operatorname{carrier}=c-a,
$$

$$
\operatorname{residual}=c^2+ca+a^2,
$$

$$
\operatorname{distinguished}=b.
$$

A natural signed coordinate is

$$
\alpha=(-c,-a).
$$

Again require

$$
N(\alpha)=\operatorname{residual},
$$

$$
\alpha_{\rm snd}-\alpha_{\rm fst}=\operatorname{carrier}.
$$

### Branch C — c is distinguished

Assume / derive:

$$
3\mid c.
$$

Use

$$
a^3+b^3=(a+b)(a^2-ab+b^2)=c^3.
$$

Set

$$
\operatorname{carrier}=a+b,
$$

$$
\operatorname{residual}=a^2-ab+b^2,
$$

$$
\operatorname{distinguished}=c.
$$

For Nat implementation, define the positive sum residual in a subtraction-safe form, for example

$$
a^2+b^2-ab,
$$

with the required nonnegativity/factorization proof, or use an equivalent current API if one exists.

Signed coordinate:

$$
\alpha=(-a,b).
$$

Then

$$
N(\alpha)=\operatorname{residual},
$$

$$
\alpha_{\rm snd}-\alpha_{\rm fst}=\operatorname{carrier}.
$$

## 7. Common signed packet

Do not expose three unrelated downstream APIs.

Normalize the branches into one common packet.

Candidate information:

    structure SignedThreeAdicPacket (a b c : ℕ) : Type where
      carrier : ℕ
      residual : ℕ
      distinguished : ℕ
      alpha : EisensteinInt
      carrier_pos : 0 < carrier
      residual_pos : 0 < residual
      distinguished_pos : 0 < distinguished
      factorization :
        carrier * residual = distinguished ^ 3
      alpha_norm :
        norm alpha = (residual : ℤ)
      alpha_signed_gap :
        alpha.snd - alpha.fst = (carrier : ℤ)
      three_dvd_carrier :
        3 ∣ carrier
      three_dvd_distinguished :
        3 ∣ distinguished
      residual_mod_nine :
        residual % 9 = 3

The exact structure may include an orientation tag or reconstruction evidence if needed.

Do not store redundant fields merely to mirror FLT5.

## 8. Residual exact depth one

For every normalized branch prove:

$$
\operatorname{residual}\equiv3\pmod9.
$$

Hence:

$$
3\mid\operatorname{residual},
$$

$$
9\nmid\operatorname{residual}.
$$

If current padicValNat API makes it short, also expose

$$
v_3(\operatorname{residual})=1.
$$

The mod-9 theorem is mandatory.

The padic equality is optional only if it would add substantial API overhead.

## 9. Exact common gcd

Prove for the normalized packet:

$$
\gcd(\operatorname{carrier},\operatorname{residual})=3.
$$

Recommended route:

1. primitive coordinate coprimality,
2. existing cubic boundary/S0 gcd theorem where available,
3. show both carrier and residual are divisible by 3,
4. show every common prime divisor must be 3.

For sum orientation, prove the analogous gcd fact directly if no current theorem exists.

Do not assume gcd = 3 as a packet input.

## 10. Exact power split

From

$$
\operatorname{carrier}\cdot\operatorname{residual}
=
\operatorname{distinguished}^3,
$$

$$
\gcd(\operatorname{carrier},\operatorname{residual})=3,
$$

and exact residual 3-adic depth one, extract positive coprime A,B with

$$
\operatorname{carrier}=3^2A^3,
$$

$$
\operatorname{residual}=3B^3,
$$

$$
\operatorname{distinguished}=3AB.
$$

Candidate structure:

    structure SignedThreeAdicPowerSplit
        (a b c : ℕ) : Type where
      packet : SignedThreeAdicPacket a b c
      A B : ℕ
      A_pos : 0 < A
      B_pos : 0 < B
      coprime_A_B : Nat.Coprime A B
      carrier_eq :
        packet.carrier = 3 ^ 2 * A ^ 3
      residual_eq :
        packet.residual = 3 * B ^ 3
      distinguished_eq :
        packet.distinguished = 3 * A * B
      three_not_dvd_B :
        ¬ 3 ∣ B

Exact multiplication association may follow simp normal form.

## 11. Power extraction method

Prefer generic Nat unique-factorization / coprime-power lemmas already available in Mathlib.

If a thin general lemma

    coprime factors whose product is a cube are cubes

is missing from current imports, add the smallest local/general helper required.

Do not import FLT5 Reduction solely for its fifth-power helper.

Do not prove the split by nonconstructive external number theory.

## 12. Bridge to U004B

The power-split packet must expose exactly what the next ramifier stripping needs.

From

$$
\alpha_{\rm snd}-\alpha_{\rm fst}
=
\operatorname{carrier}
=
9A^3,
$$

and

$$
N(\alpha)=3B^3,
$$

U004B will construct beta with

$$
\alpha=\lambda\beta,
$$

$$
N(\beta)=B^3.
$$

With the signed alpha convention chosen above, solving

$$
\lambda(u+v\tau)=\alpha
$$

should give

$$
\beta_{\rm snd}=\frac{\operatorname{carrier}}3=3A^3.
$$

Do not construct beta in this checkpoint.

But verify in report that the chosen sign convention indeed makes the future beta second coordinate positive 3*A^3.

If not, report the exact sign and do not hide it.

## 13. Non-goals

Do not implement:

- lambda divisibility / quotient beta
- lambda irreducibility or primality
- conjugate coprimality
- EuclideanDomain / PID / UFD for EisensteinInt
- cube extraction beta = epsilon * gamma^3
- unit classification
- sector arithmetic
- strict descent
- final FLT3 theorem
- Hensel recursion

Do not alter old NoSqOnS0 adapters.

## 14. Required report

Create:

    report-004.md

Record:

1. exact mod-9 classification theorem
2. exact three orientation implementation
3. common SignedThreeAdicPacket surface
4. residual mod 9 = 3 proof
5. whether padicValNat residual = 1 was added
6. gcd carrier residual = 3 theorem
7. SignedThreeAdicPowerSplit surface
8. exact A/B equations
9. proof that 3 does not divide B
10. signed alpha convention
11. confirmation of future beta.snd sign
12. actual imports
13. focused build results
14. axiom audit
15. Outcome A / B / C

## 15. Verification

Focused builds:

    lake build DkMath.FLT.Three.SignedThreeAdic
    lake build DkMath.FLT.Three.SignedThreeAdicPowerSplit

or actual module names if combined.

Audit principal theorems with #print axioms.

Required:

- no new sorry
- no project-specific axiom
- no completed FLT3 theorem shortcut
- no FLT5 production import
- no provisional GEisenstein descent dependency

## 16. Completion condition

FLT3U-004A is complete when every positive primitive FLT3 counterexample produces a common signed packet and a power-split packet with

$$
\operatorname{carrier}=9A^3,
$$

$$
\operatorname{residual}=3B^3,
$$

$$
\operatorname{distinguished}=3AB,
$$

$$
\gcd(A,B)=1,
$$

$$
3\nmid B,
$$

and the packet carries an Eisenstein alpha satisfying

$$
N(\alpha)=\operatorname{residual},
$$

$$
\alpha_{\rm snd}-\alpha_{\rm fst}=\operatorname{carrier}.
$$

Stop there.

FLT3U-004B will strip lambda and construct the ramifier-free beta packet.
