# instruction-088 — PRIM-L068 Collision Pair-Overlap Cancellation / Depth-Residual Capacity Elimination

## 0. 作業先

- repository: `Deskuma/dkmath`
- branch: `wip/number-theory-primitive-structure-260822-v2`
- base HEAD at review: `69dccbc75d4c7424e849b9a2437d7bc504cc4e85`
- Lean / Mathlib: current checkout (`Lean 4.32.2`) を維持する。upgrade しない。

前 checkpoint `PRIM-L067` は **Outcome A+ — FIFTH-DIRECTION PACKET / FIFTH-POWER GATE / EXTRA SUPPORT CHARGE COMPLETE** として受理する。

L067 により、five-direction collision seat は actual five-prime packet と `p^5 < squareBody n` gate を持ち、support-cost ledger も

```text
2 * TerminalKeys.card
+ 3 * Collision.card
+ FiveDirection.card
<= SupportExcess
```

まで強化された。

しかし次に fifth-wave capacity を作る前に、L058 以来 RHS に残っていた

```lean
paritySafeRechargeExactDepthResidualPairCapacityExcess
```

は、実は collision seat 上の pair-overlap ledger の一部分として exact に回収できる。

collision seat の support card を `k` とすると、`k >= 4` なので

```text
choose(k,2)
= (k - 1)
+ 1
+ (choose(k - 1,2) - 1).
```

ここで

- `choose(k,2)` = その seat の pair-overlap mass
- `k-1` = local support cost
- `1` = collision seat 自身の baseline
- `choose(k-1,2)-1` = L058 depth residual pair capacity local term

である。

したがって今回の bounded target は、**pair-overlap を collision seats とその外側へ exact split し、collision 側の exact identityを用いて `DepthResidualPairCapacityExcess` を L065/L067 frontier から完全に消去すること**である。

fifth-wave counting、sixth direction、residual recursion、analytic estimate、descent、full-cover contradiction、Legendre/RH 結論には進まない。

---

## 1. 新規 module

推奨:

```text
DkMath.NumberTheory.Legendre.ParitySafeCollisionPairOverlapCancellation
```

file:

```text
lean/dk_math/DkMath/NumberTheory/Legendre/ParitySafeCollisionPairOverlapCancellation.lean
```

import はまず

```lean
DkMath.NumberTheory.Legendre.ParitySafeFifthDirectionGate
```

のみで試す。

facade `DkMath.NumberTheory.Legendre` に import を追加する。

---

## 2. 既存確定 API

### pair-overlap ledger

```lean
paritySafePrimePairOverlapCount
paritySafePrimePairOverlapCount_eq_supportExcess_add_residual
```

定義は

```text
PairOverlap
= sum r in squareAnchorOddPointCoprimeOffsets n,
    choose((paritySafeActiveSupport n r).card, 2).
```

### collision surface

```lean
paritySafeRechargeExactDepthFiberCollisionSeats
paritySafeRechargeExactDepthFiberCollisionSeats_subset_candidate
paritySafeRechargeExactDepthFiberCollision_support_card_ge_four
```

### L058 depth residual capacity

```lean
paritySafeRechargeExactDepthResidualPairCapacityExcess
```

局所項は

```text
choose((activeSupport n r).card - 1, 2) - 1.
```

### L065 frontier

```lean
two_mul_pairOverlap_add_threeCollision_le_threeSupportExcess_add_twoLowCostCapacity_add_twoDepthResidualCapacity
```

すなわち

```text
2*PairOverlap + 3*Collision
<= 3*SupportExcess
 + 2*LowCostResidualCapacity
 + 2*DepthResidualPairCapacityExcess.
```

### L067 strengthened collision support charge

```lean
three_mul_collision_add_fiveDirection_card_le_localSupportCost
```

および full-cover balance / totient / reduced quotient API は L065/L067 から再利用してよい。

---

## 3. L068.1 — collision-local support-cost ledgerを命名

既存 theorem 内で匿名 sum になっている collision local support cost を public quantity として固定する。

候補:

```lean
noncomputable def paritySafeDepthCollisionLocalSupportCost (n : ℕ) : ℕ :=
  ∑ r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n,
    ((paritySafeActiveSupport n r).card - 1)
```

L067 theorem の named consumer を追加してよい:

```lean
theorem three_mul_collision_add_fiveDirection_card_le_depthCollisionLocalSupportCost
    (n : ℕ) :
    3 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card ≤
        paritySafeDepthCollisionLocalSupportCost n := by
  ...
```

これは単なる既存 L067 theorem の wrapper でよい。

---

## 4. L068.2 — collision pair-overlap mass と outside-collision mass

定義する。

```lean
noncomputable def paritySafeDepthCollisionPairOverlapMass (n : ℕ) : ℕ :=
  ∑ r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n,
    Nat.choose (paritySafeActiveSupport n r).card 2
```

collision 外側:

```lean
noncomputable def paritySafePairOverlapOutsideDepthCollision (n : ℕ) : ℕ :=
  ∑ r ∈
      (squareAnchorOddPointCoprimeOffsets n \
        paritySafeRechargeExactDepthFiberCollisionSeats n),
    Nat.choose (paritySafeActiveSupport n r).card 2
```

必須 exact split:

```lean
theorem paritySafePrimePairOverlapCount_eq_outsideCollision_add_collisionMass
    (n : ℕ) :
    paritySafePrimePairOverlapCount n =
      paritySafePairOverlapOutsideDepthCollision n +
      paritySafeDepthCollisionPairOverlapMass n := by
  ...
```

使用する inclusion:

```lean
paritySafeRechargeExactDepthFiberCollisionSeats_subset_candidate
```

`Nat` subtraction で card を分解するのではなく、Finset の `sdiff` / disjoint union / sum partition で exact に証明する。

---

## 5. L068.3 — collision local pair identity

module-local helper または public theorem として、collision seat で

```lean
theorem paritySafeDepthCollision_localPairOverlap_eq_supportCost_add_one_add_residualCapacity
    {n r : ℕ}
    (hr : r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n) :
    Nat.choose (paritySafeActiveSupport n r).card 2 =
      ((paritySafeActiveSupport n r).card - 1) +
      1 +
      (Nat.choose ((paritySafeActiveSupport n r).card - 1) 2 - 1) := by
  ...
```

数学的には `k := support.card`, `4 <= k` と

```text
choose(k,2) = (k-1) + choose(k-1,2)
```

だけである。

L041 に同型の private helper があるが private なので依存しない。必要ならこの module 内で小さな choose helper を再証明してよい。generic combinatorial library は作らない。

`k >= 4` により `choose(k-1,2) >= 1` を保証し、`Nat` subtraction truncation を安全に扱うこと。

---

## 6. L068.4 — collision mass の exact decomposition

必須主定理その1:

```lean
theorem paritySafeDepthCollisionPairOverlapMass_eq_supportCost_add_collision_add_depthResidualCapacity
    (n : ℕ) :
    paritySafeDepthCollisionPairOverlapMass n =
      paritySafeDepthCollisionLocalSupportCost n +
      (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      paritySafeRechargeExactDepthResidualPairCapacityExcess n := by
  ...
```

推奨:

1. collision mass / support cost / residual capacity を unfold。
2. L068.3 を `Finset.sum_congr`。
3. `Finset.sum_add_distrib`。
4. constant `1` sum を collision card へ normalize。

これは **exact equality** とする。

---

## 7. L068.5 — depth residual capacity を frontier から cancellation

L065 の doubled frontier、L068.2 pair-overlap split、L068.4 collision exact identity を合わせる。

必須主定理その2:

```lean
theorem two_mul_outsideCollisionPairOverlap_add_twoCollisionSupportCost_add_fiveCollision_le_threeSupportExcess_add_twoLowCostCapacity
    (n : ℕ) :
    2 * paritySafePairOverlapOutsideDepthCollision n +
      2 * paritySafeDepthCollisionLocalSupportCost n +
      5 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card ≤
        3 * paritySafeSupportExcess n +
        2 * paritySafeLowCostResidualCapacity n := by
  ...
```

数学:

```text
P = P_out + P_col
P_col = S_col + C + D
2P + 3C <= 3S + 2L + 2D
```

なので

```text
2P_out + 2S_col + 5C <= 3S + 2L.
```

ここでは `omega` を使ってよい。

**この theorem では `DepthResidualPairCapacityExcess` が statement から完全に消えることが必須。**

---

## 8. L068.6 — readable fifth-charge frontier

L067 の

```text
3*C + F5 <= S_col
```

から

```text
6*C + 2*F5 <= 2*S_col
```

を使い、L068.5 から readable theorem を得る。

必須:

```lean
theorem two_mul_outsideCollisionPairOverlap_add_elevenCollision_add_twoFiveDirection_le_threeSupportExcess_add_twoLowCostCapacity
    (n : ℕ) :
    2 * paritySafePairOverlapOutsideDepthCollision n +
      11 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      2 * (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card ≤
        3 * paritySafeSupportExcess n +
        2 * paritySafeLowCostResidualCapacity n := by
  ...
```

係数確認:

```text
5*C + 2*S_col
>= 5*C + 6*C + 2*F5
= 11*C + 2*F5.
```

不等号の向きを誤らないこと。

---

## 9. L068.7 — full-cover frontier without DepthResidual/HigherResidual

full cover balance

```text
Candidate.card + SupportExcess = IncidenceCount
```

を使い、L068.6 を support-free にする。

必須 candidate form:

```lean
theorem two_mul_outsideCollisionPairOverlap_add_elevenCollision_add_twoFiveDirection_add_threeCandidate_le_fullCoverLowCostCapacity
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    2 * paritySafePairOverlapOutsideDepthCollision n +
      11 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      2 * (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card +
      3 * (squareAnchorOddPointCoprimeOffsets n).card ≤
        3 * paritySafeIncidenceCount n +
        2 * paritySafeLowCostResidualCapacity n := by
  ...
```

さらに totient form:

```text
2*OutsideCollisionPairOverlap
+ 11*Collision
+ 2*FiveDirection
+ 3*totient(2*n)
<= 3*IncidenceCount
 + 2*LowCostResidualCapacity.
```

reduced quotient interval rewrite も追加する。

**最終 full-cover theorem の RHS には次のいずれも残さないこと:** 

```text
DepthResidualPairCapacityExcess
HigherSupportResidualExcess
```

これが今回の主要 completion criterion である。

---

## 10. 意味

L068 が閉じれば、L058 以来 raw bottleneck と見えていた depth residual capacity は独立した外部 capacity ではなく、collision seats 自身が既に消費している pair-overlap mass の内部成分だったことが Lean 上で確定する。

最終 frontier は概念的に

```text
outside-collision pair overlap
+ heavy collision charge
+ exact reduced-residue candidate mass
<= incidence capacity
 + LowCost capacity
```

となる。

これは fifth/sixth direction の再帰を続けるより先に固定すべき cancellation である。

---

## 11. Non-goals

今回禁止:

- fifth product-wave capacity
- sixth direction / sixth-power gate
- higher-support residual recursion
- generic hypergraph / arbitrary-k direction library
- analytic sieve / PNT / Mertens
- asymptotic estimate
- descent / induction on `n`
- full-cover contradiction
- Legendre / RH conclusion

---

## 12. Outcome rubric

### A+

すべて:

1. named collision local support cost
2. collision pair-overlap mass
3. outside-collision pair-overlap mass
4. exact PairOverlap split
5. collision local choose identity
6. exact collision mass = support cost + collision card + depth residual capacity
7. depth residual capacity cancellation frontier
8. readable `11*Collision + 2*FiveDirection` frontier
9. full-cover candidate form
10. totient form
11. reduced quotient interval form
12. final RHS から `DepthResidualPairCapacityExcess` / `HigherSupportResidualExcess` が消える
13. facade import / module docs / report

### A

1–9 が閉じ、totient/reduced quotient consumer の一部だけ未完。

### B

exact collision mass decompositionまでは閉じるが cancellation frontier が未完。

### C

局所 identity または Finset partition に具体的 false beam が見つかる。counterexample と corrected statement を報告する。

### E

数学ではなく elaboration / theorem-name / Finset API の engineering block。最小再現と成立している数学 spine を報告する。

---

## 13. report

作成:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveStructure-260822-v0/
primitive-parity-safe-collision-pair-overlap-cancellation-260827.md
```

最低限:

- Outcome
- exact local/global collision decomposition
- pair-overlap sdiff split
- depth residual capacity cancellation
- `11*Collision + 2*FiveDirection` coefficient derivation
- full-cover/totient/reduced-quotient frontier
- final RHS から raw depth/higher residual term が消えたこと
- non-goals
