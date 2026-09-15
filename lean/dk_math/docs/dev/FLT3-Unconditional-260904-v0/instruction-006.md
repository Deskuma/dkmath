# instruction-006 — Eisenstein Conjugate Coprimality

cid: 6a9aa2b0-937c-83e8-aa29-b3474c8acdf9

Branch: wip/flt3-unconditional-260904-v0

Prerequisite: FLT3U-004B completed with Outcome A.

Checkpoint role: FLT3U-005.

## 1. Mission

EisensteinRamifierStrippedPacket の beta と conjugate beta が、ramifier を除去した後には common nonunit divisor を持たないことを production theorem として証明する。

この checkpoint では UFD/PID を構築しない。

狙いは norm と conjugate difference のみで、

$$
d\mid\beta,\quad d\mid\overline\beta
$$

なら

$$
N(d)\mid B^3
$$

かつ

$$
N(d)\mid 27A^6
$$

を得て、

$$
\gcd(B^3,27A^6)=1
$$

から d を unit に強制することである。

これが FLT3U-006 の cube extraction gate になる。

## 2. Read first

必須:

    lean/dk_math/DkMath/FLT/Three/EisensteinRamifierStripped.lean
    lean/dk_math/DkMath/FLT/Three/EisensteinSubstrate.lean
    lean/dk_math/docs/dev/FLT3-Unconditional-260904-v0/report-005.md

architecture 参考のみ:

    lean/dk_math/DkMath/FLT/Five/SignedGoldenConjugateCoprime.lean

FLT5 production module を import してはならない。

## 3. Proposed module

第一候補:

    DkMath/FLT/Three/EisensteinConjugateCoprime.lean

直接 import は原則として

    DkMath.FLT.Three.EisensteinRamifierStripped

のみ。

必要な Mathlib の generic algebra import が暗黙に不足する場合だけ追加する。

禁止:

    DkMath.FLT.Main
    DkMath.FLT.Basic
    DkMath.FLT.Core
    DkMath.FLT.GEisensteinBridge
    DkMath.FLT.Five.*
    Mathlib.NumberTheory.FLT.Three

## 4. Relative-prime predicate

current EisensteinInt にはまだ GCDMonoid / PID / UFD structure を仮定しない。

したがってこの checkpoint では、element common-divisor 形式の relation を使う。

候補:

    def EisensteinRelPrime (x y : EisensteinInt) : Prop :=
      forall d : EisensteinInt, d ∣ x -> d ∣ y -> IsUnit d

name は既存 namespace と衝突しないものを選ぶ。

この relation は後続で EuclideanDomain / PID を導入した際に Mathlib の coprime notion へ橋渡しできればよい。

この checkpoint で Bezout coefficients を要求しない。

## 5. Norm divisibility helper

generic helper を証明する。

$$
d\mid x
\quad\Longrightarrow\quad
N(d)\mid N(x).
$$

理由は x = d*k と norm multiplicativityだけでよい。

候補:

    theorem eisenstein_norm_dvd_of_dvd
        {d x : EisensteinInt} (h : d ∣ x) :
        norm d ∣ norm x := by
      ...

No domain assumption is required.

## 6. Unit from unit norm

TraceOneInt (-1) では

$$
d\overline d = N(d)
$$

が embedded integer equalityとして既にある。

次を production theorem として用意する。

候補:

    theorem eisenstein_isUnit_of_norm_eq_one
        {d : EisensteinInt} (h : norm d = 1) :
        IsUnit d

可能なら general wrapper:

$$
N(d)=1\ \lor\ N(d)=-1
\quad\Longrightarrow\quad
d\text{ is a unit}
$$

としてもよい。

ただしこの norm は positive-definite なので、必要なら次を先に証明してもよい。

$$
0\le N(d).
$$

その場合 natAbs = 1 から norm = 1 に固定できる。

最小 proof を選ぶ。

unit classification 六個はまだ証明しない。

## 7. Conjugate difference formula

任意の

$$
x=(r,s)
$$

について current conjugation は

$$
\overline x=(r+s,-s).
$$

従って

$$
x-\overline x=(-s,2s).
$$

production theorem として固定する。

候補:

    theorem eisenstein_sub_conj_coords (x : EisensteinInt) :
      x - conj x =
        eisensteinCoord (-x.snd) (2 * x.snd)

この差の norm は

$$
N(x-\overline x)=3s^2.
$$

も mandatory。

候補:

    theorem eisenstein_norm_sub_conj (x : EisensteinInt) :
      norm (x - conj x) = 3 * x.snd ^ 2

## 8. Packet-specialized difference norm

stripped packet p では

$$
\beta_{\rm snd}=3A^3.
$$

したがって

$$
N(\beta-\overline\beta)
=
3(3A^3)^2
=
27A^6.
$$

mandatory theorem:

$$
N(\beta-\overline\beta)
=
27A^6.
$$

Lean normal form は

    3 ^ 3 * (A : ℤ) ^ 6

または

    27 * (A : ℤ) ^ 6

のどちらでもよい。

後続の Nat coprimality proof が簡単な形を選ぶ。

## 9. Common divisor divides both integer masses

stripped packet p と common divisor d を仮定する。

$$
d\mid\beta,
$$

$$
d\mid\overline\beta.
$$

then

$$
d\mid\beta-\overline\beta.
$$

標準 ring divisibility の sub closure を使う。

norm divisibilityから

$$
N(d)\mid N(\beta)=B^3
$$

and

$$
N(d)\mid N(\beta-\overline\beta)=27A^6.
$$

を得る。

Int divisibility を Nat に移す際は natAbs を使ってよい。

## 10. Coprimality of the two masses

004A power split には

$$
\gcd(A,B)=1
$$

and

$$
3\nmid B
$$

がある。

これから

$$
\gcd(B^3,27A^6)=1
$$

を Nat.Coprime として証明する。

候補 theorem:

    theorem powerSplit_coprime_B3_threeCube_A6
        (s : SignedThreeAdicPowerSplit a b c) :
        Nat.Coprime
          (s.B ^ 3)
          (3 ^ 3 * s.A ^ 6)

必要なら intermediate:

$$
\gcd(B,3)=1,
$$

$$
\gcd(B,A)=1.
$$

既存 Nat.Coprime pow/mul API を使う。

finite prime factorization を手書きしない。

## 11. Force common divisor norm to one

common divisor d の norm について

$$
|N(d)|_{\rm nat}
\mid B^3
$$

and

$$
|N(d)|_{\rm nat}
\mid 27A^6.
$$

前節の Nat.Coprime から

$$
|N(d)|_{\rm nat}=1.
$$

を得る。

その後 unit-norm theorem に接続して

$$
\operatorname{IsUnit}(d)
$$

を得る。

ここが U005 の数学的核。

## 12. Main theorem

mandatory:

    theorem beta_relPrime_conj
        (p : EisensteinRamifierStrippedPacket a b c) :
        EisensteinRelPrime p.beta (conj p.beta)

または namespace-qualified equivalent。

この theorem は UFD/PID instance を仮定しないこと。

## 13. Packet

後続 U006 が一つの input だけを受け取れるよう、薄い packet を追加する。

候補:

    structure EisensteinConjugateCoprimePacket
        (a b c : ℕ) : Type where
      stripped : EisensteinRamifierStrippedPacket a b c
      relPrime :
        EisensteinRelPrime stripped.beta (conj stripped.beta)

constructor:

    def eisensteinConjugateCoprimePacket_of_stripped
        (p : EisensteinRamifierStrippedPacket a b c) :
        EisensteinConjugateCoprimePacket a b c

primitive solution からの thin wrapper は短い場合のみ追加する。

## 14. Optional lambda nondivisibility

instruction-005 で optional だった

$$
\lambda\nmid\beta
$$

が、今回の norm helper で短く証明できるなら追加してよい。

route:

$$
\lambda\mid\beta
\Rightarrow
N(\lambda)=3\mid N(\beta)=B^3
\Rightarrow
3\mid B,
$$

contradiction.

ただし U005 completion gate には必須ではない。

## 15. Do not overclaim

EisensteinRelPrime beta (conj beta) は、この段階では

    every common divisor is a unit

という意味である。

まだ以下を主張しない。

- gcd beta (conj beta) = 1 in a GCDMonoid
- Ideal.span beta + Ideal.span conj beta = top
- Bezout identity
- prime factor multisets are disjoint

これらは U006 で採用する algebraic infrastructure に応じて bridge を作る。

## 16. Non-goals

実装しない。

- EuclideanDomain instance
- PID / UFD instance
- ideal factorization
- complete unit classification
- beta = epsilon * gamma^3
- unit sector classification
- sector exclusion
- strict descent
- well-founded closure
- final FLT3 theorem

NoSqOnS0 adapters は変更しない。

## 17. Required report

作成:

    report-006.md

最低限記録する。

1. chosen relative-prime predicate
2. norm-divisibility helper
3. unit-from-norm theorem
4. beta - conj beta coordinate formula
5. norm difference = 27*A^6
6. Nat.Coprime (B^3) (27*A^6)
7. common-divisor norm argument
8. main beta/conjugate relative-prime theorem
9. packet surface
10. whether lambda nondivisibility was added
11. actual imports
12. focused build result
13. axiom audit
14. exact remaining algebraic gate for U006
15. Outcome A / B / C

## 18. Verification

focused build:

    lake build DkMath.FLT.Three.EisensteinConjugateCoprime

主要 theorem に #print axioms。

Required:

- no new sorry
- no project-specific axiom
- no completed FLT3 shortcut
- no FLT5 production import
- no provisional GEisenstein descent dependency
- no unproved UFD/PID assumption

## 19. Completion condition

FLT3U-005 is complete when every stripped packet p yields

$$
\forall d,\quad
d\mid\beta
\land
d\mid\overline\beta
\Longrightarrow
\operatorname{IsUnit}(d).
$$

Equivalently via the chosen predicate:

$$
\operatorname{EisensteinRelPrime}
(\beta,\overline\beta).
$$

Stop there.

FLT3U-006 will use this certificate plus

$$
N(\beta)=B^3
$$

to implement unit-times-cube extraction.
