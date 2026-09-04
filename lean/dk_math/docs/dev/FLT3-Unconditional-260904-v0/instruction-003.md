# instruction-003 — Eisenstein Coordinate Substrate

cid: 6a9aa2b0-937c-83e8-aa29-b3474c8acdf9

Branch: wip/flt3-unconditional-260904-v0

Prerequisite: FLT3U-002 completed with Outcome A.

## 1. Mission

FLT3 strict descent に使う Eisenstein arithmetic の production substrate を、既存の DkMath.NumberTheory.TraceOneQuadratic.TraceOneInt (-1) 上で固定する。

この checkpoint では UFD/PID、conjugate coprimality、cube extraction、strict descent へ進まない。

目的は、今後の全 checkpoint が同じ coordinate convention を共有できるように、concrete Eisenstein coordinate type、basis element、conjugation、norm、norm multiplicativity、ramifier candidate above 3、cube coordinate formula、S0 / GN3 norm bridge を一つの小さな module にまとめることである。

## 2. Coordinate convention — critical

current TraceOneInt (-1) は

    tau^2 = tau - 1

を満たす。

したがってこれは

$$
\tau^2-\tau+1=0
$$

という trace-one basis である。

古典的な

$$
\omega^2+\omega+1=0
$$

basis と符号規約を混同しないこと。

current norm formula は

$$
N(r+s\tau)=r^2+rs+s^2.
$$

従って FLT3 の

$$
S_0(c,b)=c^2+cb+b^2
$$

は自然に

$$
N(c+b\tau)
$$

へ入る。

この convention では cube の第二座標は

$$
(r+s\tau)^3_2=3rs(r+s)
$$

である。

以前の classic omega-basis に現れる 3rs(r-s) をそのまま移植しない。

## 3. Read first

必須:

    lean/dk_math/DkMath/NumberTheory/TraceOneQuadratic.lean
    lean/dk_math/DkMath/FLT/Three/PrimitiveCubicLiftPacket.lean
    lean/dk_math/DkMath/FLT/Three/CubicValuationDepth.lean
    lean/dk_math/docs/dev/FLT3-Unconditional-260904-v0/report-000.md
    lean/dk_math/docs/dev/FLT3-Unconditional-260904-v0/report-002.md

参考:

    lean/dk_math/DkMath/FLT/GEisensteinBridge.lean

ただし既存 GEisensteinBridge の provisional descent frames / pred steps を production arithmetic descent と見なさない。

## 4. Proposed module

第一候補:

    DkMath/FLT/Three/EisensteinSubstrate.lean

直接 import は原則として次の最小面を優先する。

    import DkMath.FLT.Three.CubicValuationDepth
    import DkMath.NumberTheory.TraceOneQuadratic

必要なら明示的な lower-level import を追加してよいが、以下は禁止。

    DkMath.FLT.Main
    DkMath.FLT.Basic
    DkMath.FLT.Core
    DkMath.FLT.MathlibBridge.FLT34
    Mathlib.NumberTheory.FLT.Three

## 5. Concrete type surface

既存 type を再実装しない。

必要なら local/public abbreviation を置いてよい。

候補:

    abbrev EisensteinInt :=
      DkMath.NumberTheory.TraceOneQuadratic.TraceOneInt (-1)

または namespace 内で existing fully-qualified type をそのまま使う。

補助 constructor は実用上必要なら追加する。

候補:

    def eisensteinCoord (r s : ℤ) : EisensteinInt := ⟨r, s⟩

過度な wrapper layer は作らない。

## 6. Basis and ring identities

current API から少なくとも以下を使える theorem surface として固定する。

### E1. Basis equation

$$
\tau^2=\tau-1.
$$

既存 traceOne_tau_sq を s = -1 に specialize するだけでよいなら thin theorem にする。

### E2. Conjugation

For

$$
z=r+s\tau,
$$

$$
\overline z=(r+s)-s\tau.
$$

既存 conj の exact coordinate formula を theorem として使いやすくする。

### E3. Norm

$$
N(r+s\tau)=r^2+rs+s^2.
$$

既存 traceOneNorm_neg_one を production-facing theorem として reuse / specialize する。

### E4. Multiplicativity

$$
N(xy)=N(x)N(y).
$$

既存 traceOne_norm_mul を直接利用する。

alias のみ大量に増やさず、後続 FLT3 module が実際に必要とする specialization のみ追加する。

## 7. Basic unit axis

basis element tau (-1) について、安価に閉じるなら次を固定する。

$$
N(\tau)=1,
$$

$$
\tau^3=-1,
$$

$$
\tau^6=1.
$$

少なくとも tau が explicit unit behavior を持つことを arithmetic identity として示す。

この checkpoint では「全 unit は六個」という unit classification を証明しない。

その完全分類は FLT3U-007 の責務である。

## 8. Ramifier candidate above 3

この trace-one convention では、norm 3 の自然な候補は

$$
\lambda:=1+\tau.
$$

実装候補:

    def eisensteinRamifier : EisensteinInt := 1 + tau (-1)

最低限次を証明する。

$$
N(\lambda)=3.
$$

可能ならさらに

$$
\lambda^2=3\tau
$$

を固定する。

これは後続の exact ramified routing で 3 と ramifier exponent を接続するための重要 identity である。

また既存 x * conj x = ofInt (norm x) から

$$
\lambda\overline{\lambda}=3
$$

の embedded-integer version を得られるなら追加してよい。

この checkpoint では lambda が prime / irreducible であることは要求しない。

## 9. Cube coordinate formula

最重要 production theorem の一つ。

任意の r s : ℤ に対して

$$
(r+s\tau)^3
=
(r^3-3rs^2-s^3)
+
3rs(r+s)\tau
$$

を coordinate equality として証明する。

候補 theorem surface:

    theorem eisenstein_cube_coords (r s : ℤ) :
      (⟨r, s⟩ : EisensteinInt) ^ 3 =
        ⟨r ^ 3 - 3 * r * s ^ 2 - s ^ 3,
          3 * r * s * (r + s)⟩ := by
      ...

または fst / snd theorem に分けてもよい。

後続 descent では特に

$$
((r+s\tau)^3).snd=3rs(r+s)
$$

を直接 rewrite できる theorem が必要である。

計算は ring normalization で閉じ、古典 basis の r-s を持ち込まない。

## 10. S0 norm bridge

Nat coordinates c b を Int coordinates へ埋め込み、

$$
N(c+b\tau)=c^2+cb+b^2
$$

を S0_nat c b と接続する。

望ましい theorem:

$$
N(\langle c,b\rangle)= (S_0(c,b):\mathbb Z).
$$

Lean の exact coercion orientation は current API に合わせる。

Nat の truncated subtraction を norm 定義に持ち込まない。

eisensteinNormNat の truncated-subtraction form より、今回の production arithmetic では TraceOneInt (-1) の Int norm を正本にする。

## 11. GN3 norm bridge

既存 GN_three_sub_eq_S0_nat または同等の current production theorem と S0 norm bridge を合成し、b ≤ c の下で

$$
(GN_3(c-b,b):\mathbb Z)=N(c+b\tau)
$$

を得る theorem を追加する。

orientation は後続 FLT3 module が rewrite しやすい方を選ぶ。

この theorem は CubicValuationDepth の high-lift data を Eisenstein norm world へ送る最初の direct bridge となる。

## 12. Optional factorization bridge

scope を増やさず短く閉じるなら、

$$
(c-b)N(c+b\tau)=c^3-b^3
$$

の Int version を追加してよい。

ただし cube_sub_eq_mul_sub_S0 の単なる重複 alias になるなら不要。

## 13. Explicit non-goals

この checkpoint では実装しない。

- EuclideanDomain instance
- PID / UFD instance
- ideal factorization
- lambda の irreducibility / primality
- exact ramifier ownership in an FLT3 solution
- conjugate coprimality
- beta = epsilon * gamma^3 extraction
- complete unit classification
- sector exclusion
- strict descent
- final FLT3 theorem
- old GEisensteinDescentFrame repair

TraceOneInt (-1) に未証明の UFD/PID instance を axiom として与えない。

## 14. Required report

作成:

    report-003.md

最低限記録する。

1. actual chosen type / alias
2. exact coordinate convention
3. basis equation
4. norm and conjugation theorem surface
5. tau unit identities actually proved
6. ramifier definition and identities
7. cube coordinate theorem
8. S0 norm bridge
9. GN3 norm bridge
10. actual imports
11. build result
12. axiom audit
13. remaining algebraic gaps for FLT3U-004 / U005
14. Outcome A / B / C

特に report には

    cube snd = 3*r*s*(r+s)

であることを明記する。

## 15. Verification

focused build:

    lake build DkMath.FLT.Three.EisensteinSubstrate

主要 theorem に対して #print axioms を確認する。

確認事項:

- no new sorry
- no project-specific axiom
- no completed FLT3 shortcut dependency
- no provisional GEisensteinCandidate.step dependency
- current TraceOneInt (-1) ring structure only from kernel-checked source

## 16. Completion condition

FLT3U-003 は、後続 module が TraceOneInt (-1) 上で

$$
N(c+b\tau)=S_0(c,b)=GN_3(c-b,b)
$$

を利用でき、

$$
\lambda=1+\tau,\qquad N(\lambda)=3
$$

および

$$
((r+s\tau)^3).snd=3rs(r+s)
$$

を production theorem として直接 rewrite できる時点で完了する。

そこで停止する。

exact ramifier routing は FLT3U-004 の責務とする。
