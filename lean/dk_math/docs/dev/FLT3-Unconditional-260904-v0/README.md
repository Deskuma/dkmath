# DkMath FLT3 Unconditional

cid: 6a9aa2b0-937c-83e8-aa29-b3474c8acdf9

Project branch: wip/flt3-unconditional-260904-v0

Base branch: develop

Base commit at project start: 99ff6fcefed5bb1775e0a685cee9025fd7fdcc69

Start date: 2026-09-04

## 1. Project goal

このプロジェクトの最終目標は、DkMath 内で Fermat exponent 3 を外部の NoSq 仮定なしに完全に閉じることである。

現行の中心定理 FLT_d3_by_padicValNat は、正の互いに素な自然数 a,b,c に対して

$$
a^3+b^3\ne c^3
$$

を示すが、原始素因子 q ごとの追加条件

$$
q^2\nmid S_0(c,b)
$$

を hS0_not_sq として要求する。

本プロジェクトは、この仮定を一般定理として証明することを目的としない。

現行 NumberTheory/GNPrime 層には

$$
GN_3(17,1)=343=7^3
$$

という明示的な square-lift 例が存在する。したがって primitive cubic GN shell に対する universal no-lift claim は偽である。

正しい目標は、FLT3 counterexample の文脈で生じる原始素因子について

    NoLift branch
      q^2 ∤ S0
      → 既存 padic upper/lower contradiction

    Lift branch
      q^2 ∣ S0
      → primitive non-ramified cubic GN packet
      → finite q-adic depth / Eisenstein ownership
      → strict descent
      → contradiction

の両枝を閉じることである。

## 2. Current mathematical spine

仮想 FLT3 解から

$$
c^3-b^3=a^3
$$

を得る。

さらに

$$
c^3-b^3=(c-b)S_0(c,b)
$$

かつ

$$
S_0(c,b)=GN_3(c-b,b).
$$

既存の primitive-prime witness q は

$$
q\mid c^3-b^3,
\qquad
q\nmid c-b
$$

を満たす。

したがって primitive valuation transport により

$$
v_q(c^3-b^3)=v_q(GN_3(c-b,b)).
$$

また完全立方側から q が a を割れば

$$
3\le v_q(a^3)
$$

を得る。

NoLift branch では既存の padicValNat_upper_bound_d3 が

$$
v_q(c^3-b^3)\le1
$$

を与え、直ちに矛盾する。

Lift branch は実在し得るため、ここを Eisenstein descent で閉じるのが本プロジェクトの本丸である。

## 3. Existing anchors to reuse

実装前に current source を必ず確認すること。

主要候補:

- DkMath/FLT/Main.lean
  - FLT_d3_by_padicValNat
  - FLT_d3_by_padicValNat_of_NoSqOnS0
- DkMath/FLT/PhaseLift.lean
  - cube_sub_eq_mul_sub_S0
  - exists_prime_factor_cube_diff
  - padicValNat_lower_bound_of_dvd_d3
  - padicValNat_upper_bound_d3
- DkMath/NumberTheory/PrimitiveBeam.lean
  - primitive_prime_dvd_GN
  - primitive_prime_padic_eq_GN
- DkMath/Petal/PrimitiveBridge.lean
  - degree-three S0 / GN valuation bridge
- DkMath/FLT/GEisensteinBridge.lean
  - S0_eq_eisensteinNorm_shift
  - GN3_sub_eq_S0
  - GN3_sub_eq_eisensteinNorm_shift
  - GEisensteinDescentFrame
- DkMath/NumberTheory/GNThreeQuadratic.lean
- DkMath/NumberTheory/GNThreePrimeArithmetic.lean
  - not_nine_dvd_GN_three_of_coprime
  - non-ramified prime divisor is 1 mod 3
  - prime_not_dvd_cubic_boundary_derivative
  - explicit GN 3 17 1 = 343 regression
- DkMath/NumberTheory/GNThreeHenselLift.lean
- DkMath/NumberTheory/GNThreeHenselDepth.lean
  - unique finite lift digit at every positive depth
  - derivative stability under power-sized shifts

## 4. Dependency boundary

このプロジェクトは独立した DkMath proof route とする。

禁止:

- Mathlib の既成 FLT exponent-3 theorem を証明本体に利用すること
- Mathlib.NumberTheory.FLT.Three または同等の完成 theorem への production dependency
- hS0_not_sq / NoSqOnS0 を最終定理の未証明入力として残すこと
- universal q^2 ∤ GN3 を再び仮定または主張すること
- Hensel の lift 一意性だけを contradiction と誤認すること

許可:

- Mathlib の一般的な ring / gcd / ideal / UFD / Euclidean domain / Eisenstein integer API
- DkMath の既存 GN / primitive prime / padicValNat / Petal bridge
- 既存 FLT3 conditional route を NoLift branch の consumer として再利用すること

## 5. New module ownership

新規実装は原則として

    DkMath/FLT/Three/

配下に置く。

古い NoSqOnS0 adapter 群へ新しい本体を押し込まない。

既存 GEisensteinBridge は再利用候補だが、strict arithmetic descent をその generic frame に無理に埋め込まない。

## 6. Checkpoint discipline

各 checkpoint は一つの数学的義務だけを閉じる。

- 既存定理の alias だけを大量に作らない
- theorem surface を先に固定する
- generic abstraction は実際に二箇所以上で必要になるまで延期する
- counterexample / failed universal claim は削除せず、境界条件として記録する
- checkpoint ごとに report-NNN.md を残す

最初は instruction-000.md の reconnaissance を行い、report-000.md で current workspace の正確な再利用面を確定する。

その後 instruction-001.md の Primitive Cubic Lift Packet に進む。

## 7. Final target

primitive version:

    theorem FLT_d3_unconditional
        {a b c : ℕ}
        (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
        (hab : Nat.Coprime a b) :
        a ^ 3 + b ^ 3 ≠ c ^ 3

full positive-natural version:

    theorem fermatThree_no_positive_solution
        (a b c : ℕ)
        (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
        a ^ 3 + b ^ 3 ≠ c ^ 3

後者には primitive normalization / gcd reduction が必要である。

## 8. Project principle

FLT3 を完全に閉じる。

ただし勝利条件は theorem 名ではなく、Lean の依存グラフ上で

    no hS0_not_sq
    no NoSqOnS0 provider
    no imported completed FLT3 theorem
    no project-specific axiom / sorry

となることである。
