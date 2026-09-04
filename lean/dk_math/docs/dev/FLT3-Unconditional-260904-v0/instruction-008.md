# instruction-008 — Coprime Cube Extraction

cid: 6a9aa2b0-937c-83e8-aa29-b3474c8acdf9

Branch: wip/flt3-unconditional-260904-v0

Prerequisite: FLT3U-006A completed with Outcome A.

Checkpoint role: FLT3U-006B.

## 1. Mission

EisensteinEuclidean.lean が与える EuclideanDomain structure と、
EisensteinConjugateCoprimePacket が与える beta / conj beta の relative-prime certificate を接続し、

$$
\beta=\varepsilon\gamma^3
$$

を production theorem として抽出する。

この checkpoint では complete unit classification、unit sector exclusion、strict descent へ進まない。

## 2. Read first

必須:

    lean/dk_math/DkMath/FLT/Three/EisensteinEuclidean.lean
    lean/dk_math/DkMath/FLT/Three/EisensteinConjugateCoprime.lean
    lean/dk_math/DkMath/FLT/Three/EisensteinRamifierStripped.lean
    lean/dk_math/docs/dev/FLT3-Unconditional-260904-v0/report-007.md

generic theorem の使用例として architecture のみ読む:

    lean/dk_math/DkMath/FLT/Seven/QuadraticCoprimeFactor.lean

FLT7 module を production import しない。

## 3. Proposed module

第一候補:

    DkMath/FLT/Three/EisensteinCubeExtraction.lean

direct import:

    import DkMath.FLT.Three.EisensteinEuclidean

これだけで conjugate packet まで見えるなら最小面として採用する。

必要なら generic gcd/power theorem を含む Mathlib import を明示追加してよい。

禁止:

    DkMath.FLT.Main
    DkMath.FLT.Basic
    DkMath.FLT.Core
    DkMath.FLT.GEisensteinBridge
    DkMath.FLT.Five.*
    DkMath.FLT.Seven.*
    Mathlib.NumberTheory.FLT.Three

## 4. GCDMonoid instance

EuclideanDomain から concrete Eisenstein GCDMonoid を導入する。

候補:

    noncomputable instance traceOneNegOneGCDMonoid :
      GCDMonoid EisensteinInt :=
      EuclideanDomain.gcdMonoid EisensteinInt

既存 instance synthesis と衝突する場合は actual Mathlib API を正本にして最小修正する。

generic TraceOneInt s へ instance を広げない。

## 5. Bridge relative-prime to gcd unit

U005 では

    EisensteinRelPrime beta (conj beta)

を

    every common divisor is a unit

として証明済み。

GCDMonoid 導入後は gcd が両方を割るので、

$$
\operatorname{IsUnit}(\gcd(\beta,\overline\beta))
$$

を thin theorem として得る。

候補:

    theorem isUnit_gcd_of_eisensteinRelPrime
        {x y : EisensteinInt}
        (h : EisensteinRelPrime x y) :
        IsUnit (gcd x y) := by
      exact h (gcd x y) (gcd_dvd_left x y) (gcd_dvd_right x y)

exact theorem names は current Mathlib API に合わせる。

Bezout identity を再証明しない。

## 6. Embedded integer cube identity

stripped packet p は

$$
N(\beta)=B^3
$$

を持つ。

existing traceOne_mul_conj gives

$$
\beta\overline\beta=\operatorname{ofInt}(B^3).
$$

これを ring power の形へ変換する。

mandatory theorem:

$$
\beta\overline\beta=(B:EisensteinInt)^3.
$$

候補:

    theorem EisensteinRamifierStrippedPacket.beta_mul_conj_eq_cube
        (p : EisensteinRamifierStrippedPacket a b c) :
        p.beta * conj p.beta =
          (p.powerSplit.B : EisensteinInt) ^ 3

Nat -> Int -> EisensteinInt coercion normal form は current instances に合わせる。

必要なら generic helper:

    theorem eisenstein_intCast_pow_three (B : ℕ) :
      ((B ^ 3 : ℕ) : EisensteinInt) =
        (B : EisensteinInt) ^ 3

を追加する。

過剰な coercion API は作らない。

## 7. Generic coprime cube extractor

Mathlib の generic theorem

    exists_associated_pow_of_mul_eq_pow

を最優先で使う。

Expected input:

$$
\operatorname{IsUnit}(\gcd(x,y)),
$$

$$
xy=z^3.
$$

Expected output は current Mathlib exact shape を確認して使用する。

再実装して prime factorization を手書きしない。

まず associated form を production theorem として固定してよい。

候補:

    theorem associated_cube_of_coprime_mul_eq_cube
        {x y z : EisensteinInt}
        (hcop : IsUnit (gcd x y))
        (hpow : x * y = z ^ 3) :
        ∃ gamma : EisensteinInt,
          Associated x (gamma ^ 3)

orientation は generic theorem の actual output に合わせる。

## 8. Convert Associated to unit-times-cube

最終形は explicit unit を保持する。

推奨:

    ∃ epsilon : EisensteinIntˣ,
      ∃ gamma : EisensteinInt,
        x = (epsilon : EisensteinInt) * gamma ^ 3

multiplication orientation は commutative ring なのでどちらでもよいが、以降は

$$
x=\varepsilon\gamma^3
$$

へ統一する。

Associated から unit witness を取り出す current API を使う。

unit を bare EisensteinInt + IsUnit field として持つより、

    epsilon : EisensteinIntˣ

を優先する。

理由は U007 の complete unit classification の入力が Units 型なら自然だからである。

## 9. Main packet

後続 U007 / U008 が一つの object を受け取れるように packet を作る。

候補:

    structure EisensteinCubeUpToUnitPacket
        (a b c : ℕ) : Type where
      conjugateCoprime : EisensteinConjugateCoprimePacket a b c
      epsilon : EisensteinIntˣ
      gamma : EisensteinInt
      beta_eq :
        conjugateCoprime.stripped.beta =
          (epsilon : EisensteinInt) * gamma ^ 3

必要なら norm relation は theorem wrapper として導けるので duplicated field にしない。

## 10. Constructor from conjugate-coprime packet

mandatory:

    noncomputable def eisensteinCubeUpToUnitPacket_of_conjugateCoprime
        (p : EisensteinConjugateCoprimePacket a b c) :
        EisensteinCubeUpToUnitPacket a b c

または theorem existence + Classical.choice でもよい。

generic extractor 自体が existential なので noncomputable choice は許容する。

primitive solution から直接 packet へ送る thin wrapper は、短く import boundary を増やさない場合のみ追加する。

## 11. Norm consequences — optional narrow theorems

beta_eq と beta_norm から

$$
N(\varepsilon)N(\gamma)^3=B^3
$$

を導ける。

しかし U007 unit classification 前に norm epsilon を勝手に 1 と仮定しない。

Eisenstein unit なら positive-definite norm と inverse から N(epsilon)=1 は証明可能だが、今回の completion gate には不要。

短く閉じる場合のみ:

    theorem norm_unit_eq_one (epsilon : EisensteinIntˣ) :
      norm (epsilon : EisensteinInt) = 1

を追加してよい。

complete six-unit classification はまだ禁止。

## 12. Preserve coordinate information

cube packet は stripped packet を丸ごと保持するため、後続は同時に

$$
\beta_{\rm snd}=3A^3
$$

と

$$
\beta=\varepsilon\gamma^3
$$

を利用できる。

この二式の座標比較が U007/U008/U009 の入口になる。

gamma の座標 r,s をこの checkpoint で分解しない。

## 13. Do not extract exact cube yet

unit epsilon は一般に cube とは限らない。

したがって今回

$$
\beta=\gamma^3
$$

を主張してはならない。

U007 で units modulo cubes を分類し、
U008 で sector arithmetic を行った後に exact cube sector を選別する。

この境界は厳守する。

## 14. Non-goals

実装しない:

- six Eisenstein units の完全分類
- unit modulo cube sectors
- epsilon elimination
- coordinate sector congruences
- gamma coordinate factor split
- strict smaller primitive solution
- well-founded descent
- final FLT3 theorem
- NoSqOnS0 adapter changes

## 15. Required report

作成:

    report-008.md

最低限記録する。

1. concrete GCDMonoid instance
2. EisensteinRelPrime -> IsUnit(gcd) bridge
3. beta * conj beta = B^3 ring-power theorem
4. actual generic Mathlib extractor used
5. associated cube intermediate theorem
6. Associated -> Units witness conversion
7. EisensteinCubeUpToUnitPacket surface
8. beta = epsilon * gamma^3 theorem
9. whether unit norm = 1 helper was added
10. actual imports
11. focused build result
12. axiom audit
13. exact remaining unit-sector gate for U007
14. Outcome A / B / C

## 16. Verification

focused build:

    lake build DkMath.FLT.Three.EisensteinCubeExtraction

主要 theorem / packet constructor に #print axioms。

Required:

- no new sorry
- no project-specific axiom
- no completed FLT3 shortcut
- no FLT5 / FLT7 production import
- no provisional GEisenstein descent dependency

Classical.choice from existential extraction is acceptable.

## 17. Completion condition

FLT3U-006B is complete when every conjugate-coprime packet yields

$$
\exists \varepsilon\in E^\times,\ \exists\gamma\in E,
\qquad
\beta=\varepsilon\gamma^3.
$$

and this is packaged together with the stripped data, especially

$$
\beta_{\rm snd}=3A^3.
$$

Stop there.

FLT3U-007 will classify the finite Eisenstein unit sectors modulo cubes.
