# PRIM-L072 実装レポート

## 到達点

instruction-092 の bounded target を実装し、Outcome A+ と判定する。L071 で得た `UnusedResidualPairMass` を新しい prime direction と解釈せず、既存の canonical residual ledger の Near/Far に戻し、Far 側を既存の ExactFourth branch に送る routing を閉じた。

## 実装内容

追加した module は `ParitySafeUnusedResidualPairRouting.lean` である。global incidence は、collision seat ごとの unused-pair Finset を `(seat, pair)` にタグ付けした `Finset.biUnion` として定義した。seat tag による disjointness と image injectivity から、次を exact に証明した。

```text
UnusedResidualTripleIncidences.card = UnusedResidualPairMass
```

各 local unused pair が既存の `CanonicalResidualTripleIncidences` に属することも、L058 の erased-support API と active-support inclusion を用いて証明した。

## Near/Far routing

unused triple を既存 canonical Near/Far Finset で分割し、以下を証明した。

```text
UnusedNear ∩ UnusedFar = ∅
UnusedNear ∪ UnusedFar = UnusedAll
UnusedNear.card ≤ CanonicalNear.card
```

Far unused triple については、既存の product-wave selector、rough selector の singleton law、terminal/recharge split を順に適用した。terminal key なら terminal seat と collision seat の disjointness に反するため、far unused key は `paritySafeRechargeSurvivingFarProductKeys` に入る。

さらに、その dual-base pair が ExactDepth であると仮定すると、L058 reverse-key packet と fixed-seat residual-pair image により元の `(q,s)` が image に戻り、unused 仮定に反する。したがって、Far unused triple は必ず `paritySafeRechargeExactFourthDirectionPairs` に入る。

この routing map の injectivity から、

```text
UnusedFar.card ≤ ExactFourth.card
UnusedMass ≤ CanonicalNear.card + ExactFourth.card
UnusedMass ≤ LowCostResidualMass
```

を得た。

## LowCost cancellation frontier

```lean
paritySafeLowCostResidualMassAfterUnused n :=
  paritySafeLowCostResidualMass n -
    paritySafeDepthCollisionUnusedResidualPairMass n
```

と定義し、Nat subtraction の前提となる `UnusedMass ≤ LowCostMass` を先に証明した。その結果、

```text
LowCostResidualMass = UnusedResidualPairMass + LowCostResidualMassAfterUnused
```

が exact に成立する。L071 の full-cover frontier に代入して `2 * UnusedResidualPairMass` を cancellation し、最終 RHS から `UnusedResidualPairMass` と `CollisionResidualPairSlack` を除いた theorem を追加した。reduced quotient interval sum への rewrite 形も追加した。

## 形式上の境界

今回閉じたのは finite incidence routing、Near/Far partition、Far-to-ExactFourth inclusion/injection、LowCost remainder、L071 frontier の cancellation である。新しい prime/fifth/sixth direction、Near の新 counting、L018 の新 estimate、第四素数の一般 injectivity、descent、contradiction、Legendre/RH 結論は導いていない。instruction-092 の optional な n=58 regression は、既存の一般定理で target が閉じるため追加していない。

## 変更箇所と検証

- `DkMath/NumberTheory/Legendre/ParitySafeUnusedResidualPairRouting.lean`
- `DkMath/NumberTheory/Legendre.lean` に facade import を追加
- 本レポート

検証済み:

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeUnusedResidualPairRouting
lake build DkMath.NumberTheory.Legendre
```
