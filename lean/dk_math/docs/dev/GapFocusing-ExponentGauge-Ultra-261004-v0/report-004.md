# Instruction 004 — Legendre persistence address bridge

既存の停止点から、**下側持続の完全な殻 address と、有限区間の重み付き incidence 上限・条件付き新規 incidence 下限**まで Lean で固定した。既存の残余容量 frontier を厳密に縮める結果には到達していない。

## 実装

- [CyclotomicPersistence.lean](../../../DkMath/NumberTheory/Legendre/CyclotomicPersistence.lean): 実際の整数同次円分値、位数、殻 address、間隔、有限回数、および固定座席の追加制約。
- [ParitySafePersistence.lean](../../../DkMath/NumberTheory/Legendre/ParitySafePersistence.lean): 既存 candidate/active support の下側部分、持続・新規の正確な分解、座席で重み付けした有限区間上限、条件付き charging。
- [LegendreCyclotomicPersistence.lean](../../../DkMathTest/NumberTheory/LegendreCyclotomicPersistence.lean): 11 個の名前付き回帰定理。成立しない候補不等式も否定定理として残した。

両 production module を `DkMath.NumberTheory.Legendre` から公開した。円分 evaluator は既存 `DkMath.CFBRC.cyclotomicShiftedEval` をそのまま使い、新しい Phi の定義は作っていない。[source inventory](source-inventory-004.md) に既存 API の正確な型を保存した。

## 正確に得た数学

既存 evaluator の shifted coordinates は `(x,u)=(1,n)` で、同次座標は `(n+1,n)`。整数の要素等式として

```text
cyclotomicShiftedEval 2 1 n = 2*n+1 = oddGnomon n.
```

下側 common support は「旧 support membership とこの整数値の q-divisibility」に等しい。奇素数については、余分な非消失仮定を外部に残さず

```text
q | oddGnomon n  <->  primeOrder q (n+1) n = 2.
```

成立する。持続なら q は n と n+1 のどちらも割らない。逆向きの分母消失 branch は比の位数が 0 になるため、位数 2 と両立しない。`dvd_cyclotomic_lower_iff_primeOrder_eq_two` は実際の整数同次値に対する iff、`mem_lower_commonSupport_iff_primeOrder_eq_two` は support への直接の iff である。

固定した奇素数 q の殻 address は完全に

```text
q | oddGnomon n
  <-> n ≡ (q-1)/2 (mod q)
  <-> ∃ k : Nat, n = (q-1)/2 + k*q.
```

したがって同じ q の二つの address は合同で、連続した遷移では持続できない。任意の開始 N と長さ T に対して

```text
|{i < T : q | oddGnomon (N+i)}| <= ceil(T/q).
```

Lean での上限 `shellFrequencyCap q T` は `if T=0 then 0 else (T-1)/q+1`。正の q では自然数による上の ceiling と等価であり、T=0 も含む。証明は address offsets を `i/q` の quotient block に単射で送る。長さ q の区間で高々一回、という定理も公開した。

さらに旧点 `n^2+r` の divisibility を併せると

```text
q | n^2+r  and  q | 2*n+1  -> q | 4*r+1.
```

これは殻だけを固定する address 則から一歩進み、座席 r を固定したときに可能な持続素数を絞る。

上側は既存の prime-threshold theorem を使い、後続閾値 n+1 が素数なら old support と successor parity-safe active support は disjoint と証明した。上側 common prime は 2 であり active support は 2 を除外するためである。上側 displacement `2*(n+1)` と、下側比 `(n+1)/n` の degree-2 address を同一視していない。

## incidence と charging の範囲

`R_n` を既存の successor parity-safe candidates のうち `r<n+1` の座席とする。これは旧 parity-safe candidates の像ではない。下側移送は奇数を加えるため旧点の奇偶を反転し、旧奇数 candidate は新奇数 candidate にならない。この境界も production theorem で固定した。

各 r において新 support は既存 `paritySafeActiveSupport (n+1) r`、比較対象は完全な旧 `squareOffsetPrimeSupport n r`。intersection を persistent、difference を fresh とし、同じ `R_n` 上で総和を取ると

```text
I_n = P_n + F_n,
I_n <= paritySafeIncidenceCount (n+1).
```

両方とも正確に証明済みである。fresh はこの下側移送と旧 bounded-prime support に対する新規性で、全次数を通じた primitive divisor という意味ではない。

`M=N+T` とし、固定座席 pool と有限区間 capacity を

```text
W_q(M) = {r in [1,M] : q | 4*r+1},
C(N,T) = sum_{q prime <= M, q != 2} |W_q(M)| * ceil(T/q)
```

と定めると、実際の下側 persistent incidence に対して

```text
sum_{i<T} P_(N+i) <= C(N,T),
sum_{i<T} I_(N+i) - C(N,T) <= sum_{i<T} F_(N+i).
```

成立する。既存 `SquareOffsetsFullyCovered (N+i+1)` を各後続殻で仮定すると、各 candidate は少なくとも一つの incidence を要するので

```text
sum_{i<T} |R_(N+i)| - C(N,T) <= sum_{i<T} F_(N+i).
```

まで得た。別の full-cover ledger を仮定していない。

回帰定理 `twenty_transition_fresh_lower_bound` は N=20,T=20 で `sum |R|=245`, `C=169` を kernel 計算し、**20 個の既存 full-cover 仮定の下で fresh lower incidence が少なくとも 76 必要**と証明する。この full-cover 仮定自体は供給していない。

## 厳密な限界と失敗した案

殻の回数だけをそのまま incidence の回数にする不等式は偽である。n=10,q=3 では successor の r=2 と r=8 の二つの実際の下側 parity-safe candidates に同じ q が持続する。一方、長さ一の prime-shell event は一回だけ。この候補の否定は `unweighted_single_prime_frequency_bound_false` として残した。

固定座席を用いた新しい temporal capacity は粗い全座席 weight より小さくなりうる。N=10,T=1 では 9 と 44 である。ただし 44 は今回の粗い temporal bound であり、既存の low-cost/depth residual capacity ではない。この比較だけを frontier gain と呼ぶことはできない。

fresh をそのまま support excess に課金する無条件の案も偽である。n=6 の下側移送で successor shell 7、r=2 に fresh q=3 があるが、**既存の全 `paritySafeSupportExcess 7` は 0**。一点に最初の一素数を新しく置くことは excess を作らない。

既存 full-cover frontier の右辺には `3*paritySafeIncidenceCount` と残余 mass/capacity が残る。今回の結果は下側 fresh の下限であり、fresh の上限、pair-overlap への単射、collision/residual fibers の縮小を与えない。そのため `paritySafePrimePairOverlapCount`, `paritySafeSupportExcess`, `paritySafeLowCostResidualCapacity`, `paritySafeRechargeExactDepthResidualPairCapacityExcess` のどれにも、strict な新上限を導いていない。

下側の有限 charging は一段前進したが、full-cover failure に至る残余容量の停止点は残った。Outcome P を選ぶ理由であった incidence の分解・既存台帳への containment は今回証明できた。残った問題を成立未確認の injection として仮定せず、Outcome B と判定する。

## 指定された八問への回答

| 問 | 回答 |
| --- | --- |
| 1. 下側持続は degree-2 cyclotomic layer か | はい。実際の整数要素等式と common-support iff を証明した。 |
| 2. 奇持続素数の比の位数は 2 か | はい。奇素数について iff。座標の非消失も持続から導いた。 |
| 3. 固定 q の殻 address は何か | `(q-1)/2 + k*q`, k は自然数。 |
| 4. 同じ q の繰り返しはどれだけ離れるか | 殻番号は mod q で合同。異なる番号なら少なくとも q、連続遷移は不可。 |
| 5. 有限区間の回数上限は何か | 任意の開始 N、長さ T で高々 ceil(T/q)。 |
| 6. 既存 capacity を厳密に縮めたか | いいえ。重み付き temporal sector bound は得たが、既存 residual frontier との strict 比較はない。 |
| 7. 新規 incidence の新下限を強制するか | はい、下側部分について。既存 simultaneous full cover の下で candidate 数 minus C。20 遷移では少なくとも 76。 |
| 8. 旧停止 frontier は実際に動いたか | 有限 charging の部分は進んだ。Legendre full-cover capacity/failure frontier の strict 改善は未達。 |

Instruction 003 の address は `(a,b,q)` を固定して次数 `r*q^k` を動かす。今回の address は degree 2 と q を固定し、殻を等差数列で動かす。この二つは別の定理である。

[検証記録](validation-004.md): focused modules、回帰、両 facade、DkMath の build は成功。39 production 宣言と 11 回帰宣言の全公理出力は標準三公理の部分集合で、新規の未証明依存はない。

Outcome B — EXACT ADDRESS BRIDGE, NO STRICT CAPACITY GAIN
