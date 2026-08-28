# instruction-093 — PRIM-L073 Second-Cancellation Redundancy / Frontier Closure Audit

## 0. 作業先

- repository: `Deskuma/dkmath`
- branch: `wip/number-theory-primitive-structure-260822-v2`
- base HEAD at review: `2c4b1eee105cb5f4c861047236a25980885d7aa7`
- Lean / Mathlib: current checkout を維持する。upgrade しない。

前 checkpoint `PRIM-L072` は **Outcome A+ — UNUSED RESIDUAL-PAIR ROUTING / LOWCOST REABSORPTION COMPLETE** として受理する。

L072 により、unused residual-pair mass は Near / ExactFourth へ再吸収され、full-cover frontier は

```text
2 * PairOverlapOutsideDepthCollision
+ 9 * Collision.card
+ 3 * FiveDirection.card
+ 3 * totient(2*n)
<=
3 * IncidenceCount
+ 2 * LowCostResidualMassAfterUnused
```

まで整理された。

しかしここで route saturation の可能性がある。

既存 exact identities をさらに展開すると、outside pair-overlap は outside support cost と outside residual mass に分解でき、outside residual mass 自体が

```text
Terminal.card + LowCostResidualMassAfterUnused
```

へ exact に戻るはずである。

もしこれが閉じるなら、L072 second-cancellation frontier は新しい full-cover obstruction ではなく、既存 terminal/collision support charge の再表現に還元される。

今回の bounded target は、**この redundancy / non-redundancy を Lean theorem として判定すること**である。

新しい capacity、wave counting、prime direction、descent は追加しない。

---

## 1. 新規 module

推奨:

```text
DkMath.NumberTheory.Legendre.ParitySafeSecondCancellationRedundancyAudit
```

file:

```text
lean/dk_math/DkMath/NumberTheory/Legendre/ParitySafeSecondCancellationRedundancyAudit.lean
```

import は原則として

```lean
import DkMath.NumberTheory.Legendre.ParitySafeUnusedResidualPairRouting
```

のみから開始する。

facade `DkMath.NumberTheory.Legendre` に import を追加する。

---

## 2. Outside support / residual masses を命名する

### L073.1 outside support cost

```lean
noncomputable def paritySafeSupportExcessOutsideDepthCollision
    (n : ℕ) : ℕ :=
  ∑ r ∈
      (squareAnchorOddPointCoprimeOffsets n \
        paritySafeRechargeExactDepthFiberCollisionSeats n),
    ((paritySafeActiveSupport n r).card - 1)
```

必須 exact split:

```lean
theorem paritySafeSupportExcess_eq_outsideCollision_add_collisionSupportCost
    (n : ℕ) :
    paritySafeSupportExcess n =
      paritySafeSupportExcessOutsideDepthCollision n +
      paritySafeDepthCollisionLocalSupportCost n
```

既存

```lean
paritySafeRechargeExactDepthFiberCollisionSeats_subset_candidate
```

と `sdiff` disjoint union を使う。

### L073.2 outside / collision residual pair mass

```lean
noncomputable def paritySafeResidualPairMassOutsideDepthCollision
    (n : ℕ) : ℕ :=
  ∑ r ∈
      (squareAnchorOddPointCoprimeOffsets n \
        paritySafeRechargeExactDepthFiberCollisionSeats n),
    Nat.choose ((paritySafeActiveSupport n r).card - 1) 2

noncomputable def paritySafeDepthCollisionResidualPairMass
    (n : ℕ) : ℕ :=
  ∑ r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n,
    Nat.choose ((paritySafeActiveSupport n r).card - 1) 2
```

必須:

```lean
theorem paritySafeResidualPairMass_eq_outsideCollision_add_collisionResidual
    (n : ℕ) :
    paritySafeResidualPairMass n =
      paritySafeResidualPairMassOutsideDepthCollision n +
      paritySafeDepthCollisionResidualPairMass n
```

および local Pascal identity から

```lean
theorem paritySafePairOverlapOutsideDepthCollision_eq_outsideSupport_add_outsideResidual
    (n : ℕ) :
    paritySafePairOverlapOutsideDepthCollision n =
      paritySafeSupportExcessOutsideDepthCollision n +
      paritySafeResidualPairMassOutsideDepthCollision n
```

を exact equality で閉じる。

generic combinatorics abstraction は作らず、L041/L068 と同型の local `Nat.choose` identity を必要最小限に再利用・局所化してよい。

---

## 3. Collision residual mass の actual decomposition

L068/L070/L071 の既存 identity から、collision residual part が

```text
Collision.card
+ DepthFiberExcess
+ UnusedResidualPairMass
```

であることを exact に固定する。

推奨 theorem:

```lean
theorem paritySafeDepthCollisionResidualPairMass_eq_collision_add_fiberExcess_add_unused
    (n : ℕ) :
    paritySafeDepthCollisionResidualPairMass n =
      (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      paritySafeRechargeExactDepthFiberExcess n +
      paritySafeDepthCollisionUnusedResidualPairMass n
```

証明経路は自由だが、新 counting はしない。

例えば

```text
CollisionPairOverlapMass
= CollisionSupportCost + CollisionResidualPairMass
```

を local Pascal identity から exact に作り、既存

```text
CollisionPairOverlapMass
= CollisionSupportCost
+ Collision.card
+ DepthFiberExcess
+ CollisionResidualPairSlack

CollisionResidualPairSlack
= UnusedResidualPairMass
```

と比較して `omega` でよい。

---

## 4. Outside residual mass の正体

ここが第一の主 target。

既存:

```text
ResidualPairMass
= LowCostResidualMass
+ Terminal.card
+ Collision.card
+ DepthFiberExcess

LowCostResidualMass
= UnusedResidualPairMass
+ LowCostResidualMassAfterUnused
```

および L073.2/L073.3 を組み合わせ、必ず

```lean
theorem paritySafeResidualPairMassOutsideDepthCollision_eq_terminal_add_lowCostAfterUnused
    (n : ℕ) :
    paritySafeResidualPairMassOutsideDepthCollision n =
      (paritySafeTerminalSurvivingFarProductKeys n).card +
      paritySafeLowCostResidualMassAfterUnused n
```

を狙う。

これが閉じない場合は Outcome B とし、exact に残る項を報告する。無理に theorem shape を変形して A 扱いしない。

続いて readable exact identity:

```lean
theorem paritySafePairOverlapOutsideDepthCollision_eq_outsideSupport_add_terminal_add_lowCostAfterUnused
    (n : ℕ) :
    paritySafePairOverlapOutsideDepthCollision n =
      paritySafeSupportExcessOutsideDepthCollision n +
      (paritySafeTerminalSurvivingFarProductKeys n).card +
      paritySafeLowCostResidualMassAfterUnused n
```

を必須とする。

---

## 5. Terminal charge を outside support へ局所化

terminal seats は candidate に属し、collision seats と disjoint である。

既存:

```text
TerminalFarProductSeats.card = TerminalKeys.card
TerminalFarProductSeats support cost = 2 * TerminalFarProductSeats.card
TerminalFarProductSeats ⟂ CollisionSeats
TerminalFarProductSeats ⊆ Candidate
```

を使い、terminal seats が `Candidate \ CollisionSeats` に含まれることを証明する。

必須:

```lean
theorem two_mul_terminalKeys_le_outsideDepthCollisionSupportCost
    (n : ℕ) :
    2 * (paritySafeTerminalSurvivingFarProductKeys n).card ≤
      paritySafeSupportExcessOutsideDepthCollision n
```

これは新 bound ではなく、L060V charge の support region を outside-collision 側へ exact に局所化するだけである。

---

## 6. Reduced support-charge frontier

既存 L067/L068:

```text
3 * Collision.card + FiveDirection.card
<= CollisionSupportCost
```

を 3 倍して、L073.5 と合わせる。

必須:

```lean
theorem twoTerminal_add_nineCollision_add_threeFiveDirection_le_outsideSupport_add_threeCollisionSupport
    (n : ℕ) :
    2 * (paritySafeTerminalSurvivingFarProductKeys n).card +
      9 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      3 * (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card ≤
        paritySafeSupportExcessOutsideDepthCollision n +
        3 * paritySafeDepthCollisionLocalSupportCost n
```

この theorem は **full-cover 仮定なし**で閉じること。

---

## 7. Second-cancellation frontier の redundancy 判定

まず L071 + L072 の exact split から、full cover を使わない second-cancellation form を public theorem として用意する。

推奨:

```lean
theorem twoOutsidePair_add_nineCollision_add_threeFiveDirection_le_threeSupport_add_twoAfterUnused
    (n : ℕ) :
    2 * paritySafePairOverlapOutsideDepthCollision n +
      9 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      3 * (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card ≤
        3 * paritySafeSupportExcess n +
        2 * paritySafeLowCostResidualMassAfterUnused n
```

次が今回の最重要 audit theorem。

```lean
theorem paritySafeSecondCancellationFrontier_iff_reducedSupportCharge
    (n : ℕ) :
    (2 * paritySafePairOverlapOutsideDepthCollision n +
        9 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
        3 * (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card ≤
      3 * paritySafeSupportExcess n +
        2 * paritySafeLowCostResidualMassAfterUnused n) ↔
    (2 * (paritySafeTerminalSurvivingFarProductKeys n).card +
        9 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
        3 * (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card ≤
      paritySafeSupportExcessOutsideDepthCollision n +
        3 * paritySafeDepthCollisionLocalSupportCost n)
```

L073.1 と L073.4 の exact identities を rewrite して `omega` で閉じる想定。

### 判定

この iff と L073.6 が閉じれば、second-cancellation frontier は **既存 support charge から無条件に成立する冗長 frontier** である。

その場合、module docstring / report に明記する:

```text
The L072 second-cancellation frontier contains no independent obstruction
beyond the already established terminal/collision support-charge ledger.
```

「誤り」「無意味」ではない。finite structure/API として有用だが、Legendre contradiction pressure としては route saturation した、という意味である。

---

## 8. Full-cover / totient form の closure audit

`hn : 0 < n`, `hfull : SquareOffsetsFullyCovered n` のもとで

```text
Candidate.card + SupportExcess = IncidenceCount
Candidate.card = totient(2*n)
```

を使う。

A+ では次の exact equivalence まで推奨する:

```lean
theorem paritySafeFullCoverSecondCancellationFrontier_iff_reducedSupportCharge
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    (2 * paritySafePairOverlapOutsideDepthCollision n +
        9 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
        3 * (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card +
        3 * Nat.totient (2 * n) ≤
      3 * paritySafeIncidenceCount n +
        2 * paritySafeLowCostResidualMassAfterUnused n) ↔
    (2 * (paritySafeTerminalSurvivingFarProductKeys n).card +
        9 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
        3 * (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card ≤
      paritySafeSupportExcessOutsideDepthCollision n +
        3 * paritySafeDepthCollisionLocalSupportCost n)
```

これが閉じれば、L072 の totient/reduced-quotient full-cover theorem は full-cover balance を経由した support-charge rewrite であり、独立な contradiction constraint ではないことが明確になる。

reduced quotient interval 形式については、新しい theorem が有用なら consumer を追加してよいが必須ではない。

---

## 9. Outcome 判定

### Outcome A+ — ROUTE SATURATION PROVED

以下を全て満たす:

1. support exact outside/collision split
2. residual exact outside/collision split
3. collision residual actual decomposition
4. `OutsideResidual = Terminal + LowCostAfterUnused`
5. `OutsidePair = OutsideSupport + Terminal + LowCostAfterUnused`
6. `2*Terminal <= OutsideSupport`
7. reduced support-charge theoremが full-cover 無しで成立
8. second-cancellation frontier iff reduced support charge
9. full-cover/totient frontierも同じ charge へ exact reduction

この場合、**L065--L072 の主 frontier route はここで saturation** と判定する。

次 checkpoint では同じ pair/support ledger の細分化を継続しない。

### Outcome B — INDEPENDENT REMAINDER FOUND

L073.4 または iff reduction が閉じず、exact に非消去 residual が残る場合。

その residual を名前付きで報告し、それが次の独立 bottleneck になる。

### Outcome C — ENGINEERING BLOCKER

数学的 shape は成立するが Lean elaboration / API shortage だけが障害の場合。

---

## 10. STOP

今回やらない:

- Near wave の新しい counting / estimate
- reduced quotient interval の大小評価
- L018 depth budget の新評価
- Fourth injectivity の新規開発
- fifth/sixth direction
- higher-support recursion
- generic hypergraph
- analytic sieve / prime counting
- descent
- full-cover contradiction
- Legendre/RH 結論

特に **Outcome A+ が出た後に同じ module で次の攻め筋へ進まない**。route saturation を report に固定して停止する。

---

## 11. レポート

推奨:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveStructure-260822-v0/
primitive-parity-safe-second-cancellation-redundancy-audit-260827.md
```

最低限記録:

- exact decompositions
- reduced support charge
- iff theorem の成否
- L072 frontier が独立 obstruction か redundancy か
- Outcome A+/B/C
- 次に同じ ledger を継続すべきか否か

A+ の場合は明確に

```text
Pair/support residual-refinement route is structurally complete but
contradiction-neutral at this frontier.
```

と記録する。
