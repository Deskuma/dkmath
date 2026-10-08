# Instruction 006 — block support-excess localization / conservation

## 結果と判定範囲

38を既存の台帳へ正確に局在化し、generic block localization、readable frontier の消去同値、独立上限を受け取る有限ブロック矛盾原理を Lean に追加した。さらに実際の有限値から

```text
not (forall i in range 20, SquareOffsetsFullyCovered (20+i+1))
exists n in Icc 21 40, exists p, Nat.Prime p and n^2 < p < (n+1)^2
```

を証明した。

ただし、この有限被覆失敗は新しい38を使わない既存の収支式と既存 readable frontier からも導ける。今回の数値確認を「38が cancellation を突破した最初の障害」とは判定しない。**今回問われた新しい費用の消去後の効果は Outcome C**。有限ブロックの否定を定理として固定できたことと、新しい定量的障害を得たことを区別する。

全殻についての Legendre 予想、解析的推定、漸近評価は証明していない。

## 既存定理の監査と再利用

[Source inventory](source-inventory-006.md) に必須8モジュールと追加で発見した成熟した定理を記録した。Instruction の `lowerParitySafeFreshExcessChargeCount` と `lowerParitySafeFreshPair` の実際の名称は `lowerFreshSupportExcessChargeCount` と `lowerParitySafeFreshPairs`。別名や別の台帳は追加していない。

以下では全て既存 production quantities の有限ブロック総和を略記する。

| 記号 | Production quantity |
| --- | --- |
| A | `squareAnchorOddPointCoprimeOffsets.card` |
| I | `paritySafeIncidenceCount` |
| E | `paritySafeSupportExcess` |
| Q | `paritySafePrimePairOverlapCount` |
| O | `paritySafePairOverlapOutsideDepthCollision` |
| Eo | `paritySafeSupportExcessOutsideDepthCollision` |
| S | `paritySafeDepthCollisionLocalSupportCost` |
| C | `paritySafeRechargeExactDepthFiberCollisionSeats.card` |
| F | `paritySafeRechargeExactDepthFiveDirectionCollisionSeats.card` |
| D | `paritySafeRechargeExactDepthResidualPairCapacityExcess` |
| L | `paritySafeLowCostResidualCapacity` |
| H | `paritySafeTerminalSurvivingFarProductKeys.card` |
| M | `paritySafeLowCostResidualMassAfterUnused` |
| U | `paritySafeUncoveredCandidates.card` |

## 局所比較と最も鋭い直接局在化

全ての自然数 K、空 support を含めて

```text
K-1 <= choose(K,2)
```

が成立する。既存 `ParitySafePairResidual` は既に `Q=E+Residual` を証明しており、新しい shell inequality はこれを利用する。

要求された長い局在化は

```text
E <= O + S + C + D
```

だが、`ParitySafeSecondCancellationRedundancyAudit` に次の厳密な既存恒等式が見つかった。

```text
E = Eo + S
O = Eo + OutsideResidual
```

したがって、より鋭い直接上限は **`E <= O+S`**。衝突 baseline と depth residual の二項は不要である。これは既存 shell identities を再証明する変更ではなく、その不足していた比較と有限ブロックへの輸送である。

Instruction 005 の実際の証明済み定理 `mainBlock_support_excess_lower_bound` から

```text
full cover on shells 21..40 -> 38 <= Eo + S <= O + S
```

を導いた。38を新しい数値仮定として再導入していない。

## Collision / fifth-direction charging の向き

既存 charging は

```text
3C + F <= S
```

である。これは既に存在する collision/fifth seats が支払う最小費用であり、任意の余剰費用から collision 数を下から作る逆向きの injection ではない。

support cardinality の最小局所反例 K=2 は既存 n=13,r=6 の `{5,7}`。old shell12との比較で persistent={5}, fresh={7}、fresh excess charge=1、local residual=0、collision membership は偽。`fresh_charge_without_collision` と Instruction 005 の residual 反例を使い、この方向の課金ができないことを保存した。

対象ブロックでは全候補の active support が K<=3 であることを kernel 検証した。従って C=F=S=D=0。実際の excess106は全て衝突外であり、「全 excess は collision support 以下」という候補も明示的な否定定理で固定した。

## Incidence の消去と38の向き

既存 readable frontier のブロック和は

```text
2O + 11C + 2F + 3A <= 3I + 2L.
```

同時 full cover の厳密な収支 `I=A+E` を代入すると、これは次と同値になる。

```text
2O + 11C + 2F <= 3E + 2L.
```

`A+38<=I` は I の**下限**である。これを上式の右辺の I と置き換えて右辺を小さくすることはできない。E>=38を右辺の3Eに代入する操作も同じ問題を持つ。`lower_bound_substitution_false` は `38<=40` と `120<=3*40` が `120<=3*38` を含意しないという最小限の代数診断を記録する。

さらに最も強い既存 second cancellation では

```text
O = Eo + H + M,
E = Eo + S,
2O + 9C + 3F <= 3E + 2M
  iff
2H + 9C + 3F <= Eo + 3S.
```

となる。この最後の式は既存 `2H<=Eo` と `3C+F<=S` を足したもの。有限集合上のブロック同値を新しく証明したが、38という新しい正の定数は消去後の障害として残らない。

## N=20,T=20 の exact kernel calibration

| 実際の既存有限量 | 値 |
| --- | ---: |
| Lower candidate demand / old persistence cap / parity cap | 245 / 169 / 97 |
| Mandatory first slots / conditional fresh demand / conditional excess charge | 110 / 148 / 38 |
| Full candidate A | 490 |
| Incidence I | 418 |
| Support excess E=Eo | 106 |
| Pair overlap Q=O | 137 |
| Residual pair mass | 31 |
| Collision / fifth / collision support / depth residual capacity | 0 / 0 / 0 / 0 |
| Near first-prime budget | 0 |
| Anchor-coprime prime-square depth budget | 209 |
| Fourth gated dual-base capacity | 14 |
| LowCost capacity L | 223 |
| Terminal H | 17 |
| LowCost after unused M | 14 |
| Uncovered candidates U | 178 |

上段の148と38は元の同時 full-cover 仮定からの条件付き下限。他の表中の有限値は実際の candidate/support/capacity sets の等式である。Fourth の existential witnesses は同じ有限 active-prime set 内の bounded witnesses と同値に正規化し、ordinary `decide` で検証した。`native_decide` は使用していない。

計算を異なる段階で比較すると次のようになる。

| 段階 | 実際の値による検査 | 結果 |
| --- | --- | --- |
| Full-cover exact incidence balance | 490+106=418 | 不成立 |
| 38付き necessary balance | 490+38<=418 | 不成立。ただし490<=418も既に偽 |
| 元の full-cover readable frontier | 274+1470<=1254+446、すなわち1744<=1700 | 44不足 |
| Incidence 消去後の support frontier | 274<=318+446、すなわち274<=764 | 余裕490 |
| 最も強い second cancellation の reduced support charge | 34<=106 | 余裕72 |
| 38の直接局在化先 | 38<=106、38<=137 | 余裕68 / 99 |

従って、**同時 full cover は実際の全台帳値と両立しない**。一方、incidence を取り除いた support-only/cancellation inequalities 自体は成立し、38を吸収する。消去の同値は full-cover 仮定の下の定理であり、その仮定を外して full-cover balance と実測値を同時に成立させることはできない。

`mainBlock_not_fullyCovered` は005の38付き収支から、`mainBlock_not_fullyCovered_without_freshBound` は既存収支だけから、`mainBlock_not_fullyCovered_from_readable_frontier` は元の readable frontier の44不足から、それぞれ被覆失敗を証明する。三つを区別することで、新しい費用が必要だったという誤った帰属を避けた。

既存 cover/escaping equivalence と square-cell prime bridge を使い、`mainBlock_exists_prime_squareCell` は

```text
exists n in [21,40], exists p, Prime p and n^2 < p < (n+1)^2
```

を導く。これは有限存在定理であり、各 n の存在定理や全殻の Legendre 予想ではない。

## 消えない量と次の正確なターゲット

full cover を仮定しない既存台帳のブロック収支は

```text
I + U = A + E.
```

実際には `418+178=490+106`。消去で見落としてはならない量はこの**既存 uncovered-candidate deficit U**である。新しい residual currency を導入する必要はない。

汎用消費定理には二つの形を実装した。mandatory temporal excess bound を `b(N,T)` と略記すると、

```text
O+S <= B and B < b(N,T) -> not simultaneous full cover,
I < A+b(N,T) -> not simultaneous full cover.
```

いずれも N,T を固定しない本番定理。被覆失敗から square-cell prime を抽出する consumer も本番にある。

次の定量的ターゲットは、full-cover 仮定を使わずに指定ブロックの

```text
sum paritySafeIncidenceCount <= Ubound(N,T)
Ubound(N,T) < sum fullCandidate.card + b(N,T)
```

を供給すること。その厳密な閾値は今回の generic theorem が既に受け取れる。対象20ブロックでは418という exact upper value が供給できた。support excess の下限をさらに増やすだけでは、既存 cancellation を新しい residual/collision obstruction に変えることはできない。

## 指定された九問への回答

| 問 | 回答 |
| --- | --- |
| 1. Shell excess は常に pair mass 以下か | はい。空 support を含む K-1<=choose(K,2)、既存 Q=E+Residual。追加の full-cover 仮定は不要。 |
| 2. Outside/collision の正確な分割は | E=Eo+S、Q=O+collisionPairMass、collisionPairMass=S+C+D。Excess の直接上限は E<=O+S。 |
| 3. 38は局在化を生き残るか | 条件付き38<=Eo+Sとして正確に輸送される。しかし新しい cancellation obstruction には残らない。 |
| 4. Collision support を既存の charges に換えられるか | 既存の3C+F<=Sの向きでのみ可能。任意の費用から C/F を生成する逆向きは不可。main block では S=C=F=0。 |
| 5. Incidence 消去後の式は | 2O+11C+2F<=3E+2L。最も強い second cancellation は2H+9C+3F<=Eo+3S。新しい+38項はない。 |
| 6. 同時 full cover は数値的に可能か | 実際の全台帳値では不可能。既存収支でも readable frontier の44不足でも否定できる。support-only frontier は余裕490で成立する。 |
| 7. 得られた prime consequence は | ∃n∈[21,40], ∃p, Prime p ∧ n²<p<(n+1)²。既存 bridge 経由の Lean 定理。 |
| 8. 消去後の余裕はどこか | Eo=106が38を受け取り、collision は空。十一-collision式の余裕490は 3E-2O=44 と 2L=446。最強 reduced support charge の余裕72は Eo-2H=106-34。 |
| 9. 矛盾 frontier は新たに strict に動いたか | 有限被覆失敗を新しく定理化したが、38由来の strict cancellation gain はない。旧台帳だけでも同じ失敗が出るため、研究上の判定は C。 |

[Validation](validation-006.md) と [findings](findings-006.md) にビルド、公理監査、反例、段階別検証を記録する。

Outcome C — SUPPORT EXCESS IS ABSORBED BY CURRENT CANCELLATION
