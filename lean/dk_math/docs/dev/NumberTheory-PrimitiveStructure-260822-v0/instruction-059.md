# instruction-059 — PRIM-L044 Far-Cofactor Half-Scale Return / Existing-Ledger Recharge Frontier

## 0. 作業先

- repository: `Deskuma/dkmath`
- branch: `wip/number-theory-primitive-structure-260822-v2`
- Lean / Mathlib: 現行 checkout (`Lean 4.32.2`) を維持する。upgrade しない。

前 checkpoint `PRIM-L043` は **Outcome A** として受理済み。

L043 では canonical far residual triple

```text
p := paritySafeCanonicalSupportPrime n r
p < q < s
2*n < p*q*s
p*q*s | n^2+r
```

に対する complementary cofactor

```text
t := (n^2+r)/(p*q*s)
```

について、

```text
0 < t
p*q*s*t = n^2+r
2*t < n+2
t < n
Nat.Coprime (2*n) t
```

および、任意の prime divisor `u | t` が同じ parity-safe active old-prime world / candidate supportへ戻ることを証明した。

さらに `1<t` なら、

```text
p^2 | n^2+r
or q^2 | n^2+r
or s^2 | n^2+r
or a fourth distinct active direction u appears
```

まで exact に閉じている。

今回の目的は、この closure を **generic fourth-direction hypergraphへ膨らませず**、既存 L018 depth ledgerへ戻せる部分を明示し、new-direction branchについては L043 が実は持っている **half-scale prime return** を露出させることである。

重要:

```text
t<n
```

は smaller-anchor `SquareOffsetsFullyCovered t` descent ではない。

また、cofactor `t` やその prime divisor `u` を residual incidence の injective coordinate として数えてはならない。

---

## 1. reconnaissance 結論

L043 の packet から、prime divisor `u | t` について

```text
u ≤ t
2*t < n+2
```

なので必ず

```text
2*u < n+2
```

が得られる。

従って L043 の old-support return は、実際にはより強く

```text
far cofactor prime
  -> same active old world
  -> same candidate support
  -> half-scale active prime
```

である。

一方、既存 ledgerへの charge は非対称である。

### depth branch

```text
p^2 | n^2+r
q^2 | n^2+r
s^2 | n^2+r
```

は、そのまま L018 の

```text
squareAnchorCoprimePrimeSquareOffsets
squareAnchorCoprimePrimeSquareDepthBudget
```

へ witness-level に戻せる。

### new-direction branch

`u` が fourth distinct directionなら support-size増加は得られるが、

```text
far residual incidence -> cofactor t
far residual incidence -> returned prime u
```

は一般に injective ではない。

数値偵察で次の arithmetic false beam がある。

```text
n = 62

62^2 + 41 = 3885 = 3*5*37*7
62^2 + 83 = 3927 = 3*11*17*7

124 < 3*5*37
124 < 3*11*17
```

従って二つの異なる far factorization が同じ cofactor `t=7`、同じ returned half-scale prime `u=7` を持つ。

これは Lean theorem の代替証明ではなく reconnaissance である。今回、実装負荷が軽ければ arithmetic theorem として固定する。

---

## 2. 新規 module

推奨:

```text
DkMath/NumberTheory/Legendre/ParitySafeFarTripleRecharge.lean
```

最低 import:

```lean
import DkMath.NumberTheory.Legendre.ParitySafeTripleFarCofactor
```

L043 -> L042 -> L041 から `LocalizedObstruction` / reduced-residue API は既に依存鎖に入っている。不要な broad import を追加しないこと。

facade:

```text
DkMath/NumberTheory/Legendre.lean
```

へ import を追加する。

---

## 3. PRIM-L044.1 — half-scale active-prime world

half-scale old-prime worldを finite setとして定義する。

推奨形:

```lean
noncomputable def paritySafeHalfScaleActivePrimes (n : ℕ) : Finset ℕ :=
  (squareAnchorOddActivePrimes n).filter
    (fun u => 2 * u < n + 2)
```

membership theorem:

```lean
@[simp] theorem mem_paritySafeHalfScaleActivePrimes
    {n u : ℕ} :
    u ∈ paritySafeHalfScaleActivePrimes n ↔
      u ∈ squareAnchorOddActivePrimes n ∧ 2 * u < n + 2
```

この checkpoint では prime-counting estimate や cardinal asymptotic を作らない。

---

## 4. PRIM-L044.2 — far cofactor itself returns to the coprime base world

L043 packet は

```text
0 < t
t < n
Nat.Coprime (2*n) t
```

を持つ。

既存

```lean
coprime_two_mul_iff_coprime_and_odd
```

を再利用し、cofactor 自身が canonical first-half coprime base offsetであることを閉じる。

主 theorem:

```lean
theorem paritySafeFarTripleCofactor_mem_coprimeBase
    {n r q s : ℕ}
    (hinc : (r, (q, s)) ∈ paritySafeCanonicalResidualTripleIncidences n)
    (hfar : (paritySafeCanonicalSupportPrime n r, (q, s)) ∈
      paritySafeTripleGateFarTriples n) :
    paritySafeFarTripleCofactor n r q s ∈
      squareAnchorCoprimeBaseOffsets n
```

数学的意味:

```text
far triple product
  -> complementary factor t
  -> first-half coprime packet coordinate at the SAME anchor n
```

これは `t` を新しい anchor にする定理ではない。

---

## 5. PRIM-L044.3 — every cofactor prime is half-scale

L043 の

```lean
paritySafeFarTripleCofactor_prime_divisor_return
```

を strengthening / wrapper し、prime divisor `u | t` に対して

```text
u ∈ paritySafeHalfScaleActivePrimes n
u ∈ paritySafeActiveSupport n r
```

を返す。

推奨 theorem:

```lean
theorem paritySafeFarTripleCofactor_prime_divisor_halfScale_return
    {n r q s u : ℕ}
    (hinc : (r, (q, s)) ∈ paritySafeCanonicalResidualTripleIncidences n)
    (hfar : (paritySafeCanonicalSupportPrime n r, (q, s)) ∈
      paritySafeTripleGateFarTriples n)
    (huprime : Nat.Prime u)
    (hut : u ∣ paritySafeFarTripleCofactor n r q s) :
    u ∈ paritySafeHalfScaleActivePrimes n ∧
      u ∈ paritySafeActiveSupport n r
```

証明核は新しい数論ではなく、

```text
u ≤ t
2*t < n+2
```

から `2*u<n+2` を得るだけでよい。

可能なら consumer-friendly packetとして

```text
Nat.Prime u
u ≤ t
2*u < n+2
u ≠ 2
¬u ∣ n
u ∣ n^2+r
```

を別 theorem にせず、必要な場合だけ local have で使う。

---

## 6. PRIM-L044.4 — depth branchを L018 ledgerへ exact recharge

L043 の depth disjunction は、単なる divisibility statementのまま止めず、既存 localized depth incidenceへ戻す。

`hinc` から `r ∈ squareAnchorCoprimeOffsets n` は取得できる。

したがって、例えば

```text
p^2 | n^2+r
```

は

```text
r ∈ squareAnchorCoprimePrimeSquareOffsets n p
```

へ移せる。

新しい巨大 predicate は作らず、L043 closureを次の形へ wrapperするのが望ましい。

概念形:

```lean
theorem paritySafeFarTripleCofactor_depthLedger_or_halfScaleNewDirection
    {n r p q s : ℕ}
    (hinc : (r, (q, s)) ∈ paritySafeCanonicalResidualTripleIncidences n)
    (hfar : (paritySafeCanonicalSupportPrime n r, (q, s)) ∈
      paritySafeTripleGateFarTriples n)
    (hp : p = paritySafeCanonicalSupportPrime n r)
    (ht : 1 < paritySafeFarTripleCofactor n r q s) :
    r ∈ squareAnchorCoprimePrimeSquareOffsets n p ∨
      r ∈ squareAnchorCoprimePrimeSquareOffsets n q ∨
      r ∈ squareAnchorCoprimePrimeSquareOffsets n s ∨
      ∃ u,
        Nat.Prime u ∧
        u ∣ paritySafeFarTripleCofactor n r q s ∧
        u ∈ paritySafeHalfScaleActivePrimes n ∧
        u ∈ paritySafeActiveSupport n r ∧
        u ≠ p ∧ u ≠ q ∧ u ≠ s ∧
        p * q * s * u ∣ n ^ 2 + r
```

引数順・結合順は Lean に合わせて調整可。

重要なのは、depth三分岐だけは **既存 L018 ledgerの実在 incidence** まで戻すこと。

---

## 7. PRIM-L044.5 — fourth direction は high-support witness だが global chargeではない

new-direction branchから、可能なら次を追加する。

```text
4 ≤ (paritySafeActiveSupport n r).card
```

理由:

```text
p, q, s, u
```

の4 distinct active directionsが同じ support に入る。

ただし、この theorem の証明が Finset bookkeepingだけで不自然に重くなる場合は optional とする。

より重要なのは report で次を区別すること。

```text
fourth direction exists
    !=
far residual incidence can be injected into active-prime directions
```

および

```text
support card >= 4
    !=
residual ledger universally disappears
```

---

## 8. PRIM-L044.6 — noninjective recharge false beam

実装負荷が軽ければ arithmetic theoremを追加する。

推奨:

```lean
theorem paritySafeHalfScaleReturn_false_beam_arithmetic :
    62 ^ 2 + 41 = 3 * 5 * 37 * 7 ∧
      62 ^ 2 + 83 = 3 * 11 * 17 * 7 ∧
      2 * 62 < 3 * 5 * 37 ∧
      2 * 62 < 3 * 11 * 17 ∧
      (62 ^ 2 + 41) / (3 * 5 * 37) = 7 ∧
      (62 ^ 2 + 83) / (3 * 11 * 17) = 7 ∧
      2 * 7 < 62 + 2 := by
  norm_num
```

目的は

```text
cofactor t
returned half-scale prime u
```

を residual incidence の injective charge keyとして扱えないことを固定すること。

actual residual-set membershipまで展開する必要はない。L043 false beamと同じく arithmetic obstructionでよい。

---

## 9. stronger-beam judgment

reportでは次を明示判定する。

1. far cofactor `t` は必ず `squareAnchorCoprimeBaseOffsets n` に戻るか。
2. `u | t`, `Prime u` なら必ず `2*u<n+2` まで強化できるか。
3. その `u` は half-scale active set と candidate support の双方に入るか。
4. depth三分岐を L018 `squareAnchorCoprimePrimeSquareOffsets` へ exact に戻せるか。
5. fourth directionから support card `>=4` を clean に得られるか。
6. `t` / `u` による global injective recharge は可能か。
   - arithmetic false beamにより通常は **No** とする。
7. 今回の結果だけで residual ledger の universal cardinal contradiction が出たか。
   - 通常は **No**。
8. smaller-anchor `SquareOffsetsFullyCovered t` が得られたか。
   - **No**。

---

## 10. Outcome 判定

### Outcome A — HALF-SCALE RETURN / DEPTH RECHARGE FRONTIER

以下が成立:

- `t ∈ squareAnchorCoprimeBaseOffsets n`
- every prime divisor `u | t` returns to `paritySafeHalfScaleActivePrimes n`
- same candidate support membership
- depth branch is translated to L018 prime-square incidence
- fourth direction remains explicit
- noninjective `t/u` recharge boundary is preserved

### Outcome B — HALF-SCALE RETURN ONLY

half-scale strengtheningと coprime-base returnは通るが、depth-ledger wrapperが既存 APIとの型合わせで clean に閉じない。

### Outcome C — NO NEW FRONTIER

half-scale claimが既に既存 theoremの定義的言い換えに過ぎず、downstream consumerを増やさない、または提案 theorem が偽。

Outcome C の場合は theoremを増やさず report-onlyで停止する。

---

## 11. report

作成:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveStructure-260822-v0/
  primitive-parity-safe-far-triple-half-scale-recharge-frontier-260826.md
```

最低限:

- Outcome
- theorem surface
- cofactor -> coprime base return
- prime divisor -> half-scale active return
- L018 depth recharge
- fourth-direction / high-support判定
- `(62,41)` / `(62,83)` arithmetic false beam
- global injectivity / cardinal contradiction未到達の境界
- smaller-anchor descent未到達の境界

---

## 12. build / audit

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeFarTripleRecharge
lake build DkMath.NumberTheory.Legendre
git diff --check
```

新規 Lean source:

```text
sorry
admit
axiom
native_decide
```

禁止 placeholder と trailing whitespace を監査する。

full repository build は不要。

---

## 13. 非目標

- `LegendreConjecture` の証明
- smaller-anchor full-cover reconstruction
- generic infinite descent
- fourth / fifth / general k-direction hypergraph
- far residual incidence -> cofactor / returned-prime の injectivity
- residual ledger の universal消滅
- global cardinal contradiction
- PNT / Mertens / Rosser--Schoenfeld / Jacobsthal / analytic sieve
- RH / CFBRC

今回の狙いは、L043 の

```text
large far triple
  -> small cofactor
  -> old-support return
```

を

```text
large far triple
  -> first-half coprime cofactor
  -> half-scale old-prime return
  -> existing depth ledger OR explicit fourth direction
```

へ exact に sharpen し、**どこまで既存 ledgerへ戻せて、どこから先が noninjective ownership 問題になるか**を Lean 上で固定することだけである。
