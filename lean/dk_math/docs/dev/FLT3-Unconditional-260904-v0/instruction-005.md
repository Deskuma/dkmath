# instruction-005 — Eisenstein Ramifier Stripping

cid: 6a9aa2b0-937c-83e8-aa29-b3474c8acdf9

Branch: wip/flt3-unconditional-260904-v0

Prerequisite: FLT3U-004A completed with Outcome A.

Checkpoint role: FLT3U-004B.

## 1. Mission

SignedThreeAdicPowerSplit が与える signed Eisenstein element alpha から、ramifier

$$
\lambda=1+\tau
$$

を exactly 一回除去し、ramifier-free element beta を production packet として構成する。

この checkpoint の主終端は

$$
\alpha=\lambda\beta,
$$

$$
N(\beta)=B^3,
$$

$$
\beta_{\rm snd}=3A^3
$$

である。

UFD/PID、conjugate coprimality、unit times cube extraction、strict descent へは進まない。

## 2. Read first

必須:

    lean/dk_math/DkMath/FLT/Three/EisensteinSubstrate.lean
    lean/dk_math/DkMath/FLT/Three/SignedThreeAdic.lean
    lean/dk_math/DkMath/FLT/Three/SignedThreeAdicPowerSplit.lean
    lean/dk_math/docs/dev/FLT3-Unconditional-260904-v0/report-004.md

確認済み substrate:

$$
\lambda=1+\tau,
$$

$$
N(\lambda)=3,
$$

$$
\lambda^2=3\tau.
$$

## 3. Coordinate algebra

TraceOneInt (-1) の multiplication は、座標

$$
x=(r,s),
\qquad
y=(u,v)
$$

に対して

$$
(xy)_{\rm fst}=ru-sv,
$$

$$
(xy)_{\rm snd}=rv+su+sv.
$$

特に

$$
\lambda=(1,1)
$$

なので

$$
\lambda(u,v)=(u-v,\ u+2v).
$$

従って

$$
\alpha=(r,s)
$$

が

$$
s-r=3v
$$

を満たせば

$$
v=\frac{s-r}{3},
\qquad
u=r+v
$$

により

$$
\lambda(u,v)=\alpha
$$

となる。

004A packet は

$$
s-r=\operatorname{carrier}=9A^3
$$

を持つため、

$$
v=3A^3
$$

を division-free に選べる。

## 4. Proposed module

第一候補:

    DkMath/FLT/Three/EisensteinRamifierStripped.lean

直接 import:

    DkMath.FLT.Three.SignedThreeAdicPowerSplit

だけで足りるならそれを優先する。

以下を import しない。

    DkMath.FLT.Main
    DkMath.FLT.Basic
    DkMath.FLT.Core
    DkMath.FLT.GEisensteinBridge
    DkMath.FLT.Five.*
    Mathlib.NumberTheory.FLT.Three

## 5. Stripped packet

第一候補 surface:

    structure EisensteinRamifierStrippedPacket
        (a b c : ℕ) : Type where
      powerSplit : SignedThreeAdicPowerSplit a b c
      beta : EisensteinInt
      alpha_eq :
        powerSplit.packet.alpha =
          eisensteinRamifier * beta
      beta_norm :
        norm beta = (powerSplit.B : ℤ) ^ 3
      beta_snd :
        beta.snd = 3 * (powerSplit.A : ℤ) ^ 3
      three_not_dvd_B :
        ¬ 3 ∣ powerSplit.B

three_not_dvd_B が powerSplit から直接取れるだけなら、重複 field を置かず theorem wrapper にしてよい。

必要なら beta_fst formula も packet または theorem として追加する。

候補:

$$
\beta_{\rm fst}
=
\alpha_{\rm fst}+3A^3.
$$

## 6. Explicit beta construction

powerSplit を s とする。

定義候補:

$$
v:=3A^3
$$

as an integer.

$$
u:=\alpha_{\rm fst}+v.
$$

$$
\beta:=(u,v).
$$

Lean では Nat/Int coercion を明示し、truncated subtraction を使わない。

重要:

004A は既に

$$
\alpha_{\rm snd}-\alpha_{\rm fst}
=
\operatorname{carrier}
=
9A^3
$$

を持つ。

これを使って

$$
\alpha_{\rm snd}
=
\alpha_{\rm fst}+9A^3
$$

へ変形し、coordinate extensionality だけで

$$
\lambda\beta=\alpha
$$

を閉じる。

ring division は不要である。

## 7. Exact second coordinate

mandatory theorem:

$$
\beta_{\rm snd}=3A^3.
$$

さらに

$$
0<\beta_{\rm snd}
$$

を Int 上で使いやすい theorem として追加してよい。

004A の future_signed_beta_snd_pos はこの実構成に置き換わる。

古い sign contract theorem は削除しなくてよい。

## 8. Norm stripping

004A から

$$
N(\alpha)=\operatorname{residual}=3B^3.
$$

U003 から

$$
N(\lambda)=3.
$$

alpha_eq と norm multiplicativity から

$$
3B^3
=
3N(\beta)
$$

を得る。

Int 上で 3 を cancel して

$$
N(\beta)=B^3
$$

を証明する。

この theorem は packet field または public theorem として mandatory。

## 9. Ramified load is exhausted

004A には

$$
3\nmid B
$$

がある。

従って

$$
3\nmid B^3.
$$

beta_norm により

$$
3\nmid N(\beta).
$$

を theorem として固定する。

候補:

    theorem three_not_dvd_beta_norm
        (p : EisensteinRamifierStrippedPacket a b c) :
        ¬ (3 : ℤ) ∣ norm p.beta := by
      ...

実際の divisibility domain は Int / Nat のどちらが後続で扱いやすいかに合わせてよい。

可能ならさらに、UFD/PID や irreducibility を使わずに

$$
\lambda\nmid\beta
$$

を証明する。

理由:

もし

$$
\beta=\lambda\gamma
$$

なら norm multiplicativity により

$$
N(\beta)=3N(\gamma),
$$

よって 3 が N(beta) を割り、上と矛盾する。

これは lambda の primality を必要としない。

この theorem は後続の conjugate coprimalityで有用なので、短く閉じるなら追加する。

## 10. Constructor theorem

powerSplit から stripped packet を構成する theorem / noncomputable def を実装する。

第一候補:

    def eisensteinRamifierStrippedPacket_of_powerSplit
        {a b c : ℕ}
        (s : SignedThreeAdicPowerSplit a b c) :
        EisensteinRamifierStrippedPacket a b c := by
      ...

構成は explicit coordinate formula なので、可能なら computable def とする。

Classical.choice は不要なはずである。

positive primitive solution から直接 stripped packet へ送る thin wrapper は、import boundary を広げず短い場合のみ追加する。

## 11. Normal-form theorem surface

後続 U005 が orientation を reopen しなくて済むよう、最低限以下を一つの packet から読めるようにする。

$$
\alpha=\lambda\beta,
$$

$$
N(\beta)=B^3,
$$

$$
\beta_{\rm snd}=3A^3,
$$

$$
\gcd(A,B)=1,
$$

$$
3\nmid B,
$$

$$
\lambda\nmid\beta
$$

最後の lambda nondivisibility は実装可能なら mandatory に格上げしてよい。

coprime_A_B は powerSplit 経由で読めれば duplicated field は不要。

## 12. Conjugation bridge — optional narrow helper

U005 の準備として、scope を増やさず短く閉じるなら

$$
N(\beta)=\beta\overline{\beta}
$$

の embedded integer formを rewrite しやすい wrapper として追加してよい。

ただし gcd / IsCoprime / ideal coprimalityにはまだ進まない。

## 13. Non-goals

この checkpoint では実装しない。

- EuclideanDomain instance
- IsDomain/PID/UFD completion unless absolutely required for existing ring arithmetic
- lambda primality / irreducibility
- beta and conjugate beta coprimality
- ideal factorization
- beta = epsilon * gamma^3
- complete unit classification
- sector exclusion
- strict descent
- well-founded induction
- final FLT3 theorem

NoSqOnS0 adapter を変更しない。

## 14. Important stop gate

もし explicit coordinate quotient beta が

$$
\alpha=\lambda\beta
$$

を満たさない orientation が見つかった場合、符号を patch して隠さない。

report に orientation と actual quotient coordinates を記録し、Outcome B として止める。

同様に beta.snd が

$$
3A^3
$$

でなく負符号になる場合も exact sign を報告する。

004A の common signed convention が正しければ、全 orientation で同じ正符号になるはずである。

## 15. Required report

作成:

    report-005.md

最低限記録する。

1. exact beta definition
2. alpha = lambda * beta theorem
3. beta fst/snd formulas
4. beta.snd = 3*A^3
5. beta norm = B^3
6. 3 does not divide norm beta
7. whether lambda does not divide beta was proved
8. actual imports
9. focused build result
10. axiom audit
11. remaining exact gate for U005
12. Outcome A / B / C

## 16. Verification

focused build:

    lake build DkMath.FLT.Three.EisensteinRamifierStripped

主要 theorem について #print axioms を確認する。

Required:

- no new sorry
- no project-specific axiom
- no completed FLT3 theorem shortcut
- no FLT5 production import
- no GEisenstein provisional descent dependency

## 17. Completion condition

FLT3U-004B is complete when SignedThreeAdicPowerSplit yields a stripped packet with

$$
\alpha=\lambda\beta,
$$

$$
N(\beta)=B^3,
$$

$$
\beta_{\rm snd}=3A^3,
$$

$$
3\nmid B,
$$

and preferably

$$
\lambda\nmid\beta.
$$

Stop there.

FLT3U-005 begins with conjugate coprimality of beta after this exact ramifier removal.
