# instruction-071 — PRIM-L056 Exact Depth Seat Return / Fiber Multiplicity Ledger

## 0. 作業先

- repository: `Deskuma/dkmath`
- branch: `wip/number-theory-primitive-structure-260822-v2`
- base HEAD at review: `5bc0bfae5ec85838adf3b5c6b0a681b0b7986b8e`
- Lean / Mathlib: current checkout (`Lean 4.32.2`) を維持する。upgrade しない。

前 checkpoint `PRIM-L055` は **Outcome A+ — EXACT DEPTH / CANONICAL FOURTH DIRECTION** として受理する。

L055 までで far residual mass は exact に

```text
FarResidual.card
  = Terminal.card
  + ExactDepth.card
  + ExactFourth.card
```

へ分解された。

今回の bounded target は **Depth branch だけを既存 PRIM-L018 prime-square ledger へ戻すこと**である。

ただし重要な停止境界がある。

`ExactDepth` は `(b,t)` pair-coordinate の mass であり、L018 の
`PrimeSquareDepthBudget` は `(seat, prime-square direction)` の incidence mass である。
一つの shell seat に複数の exact depth pair が存在し得るため、根拠なく

```text
ExactDepth.card <= squareAnchorCoprimePrimeSquareDepthBudget n
```

を主張してはならない。

今回は

```text
exact depth pair
  -> unique shell seat
  -> at least one L018 prime-square witness at that seat
```

までを exact に閉じ、distinct depth seats は L018 budget へ charge できることを示す。
同時に、pair mass と seat mass の差を exact fiber ledger として残す。

---

## 1. 数学的核

L055 の exact shell point は

```text
P(n,b,t) := (b*t) * OddShellQuotient(n,b,t)
```

である。

exact pair では L053 の shell packet により

```text
n^2 < P <= n^2 + 2*n.
```

従って shell seat を

```text
r := P - n^2
```

と定義でき、

```text
1 <= r <= 2*n
n^2 + r = P
```

を得る。

さらに exact pair は reduced coordinate から来ているため、この `r` は
`paritySafe` candidate、少なくとも `squareAnchorCoprimeOffsets n` に戻る。

Depth branch では L055 より witness `(p,q)` と selector `s` のいずれかについて

```text
p^2 | P
or q^2 | P
or s^2 | P.
```

`p,q,s` はすべて active/nondivisor prime なので、上の `r` は対応する

```text
squareAnchorCoprimePrimeSquareOffsets n d
```

へ入る。

したがって **distinct shell seats** は L018 local depth budget に charge できる。

しかし pair-level では同じ seat が複数回現れ得るので、fiber multiplicity を消してはならない。

---

## 2. 新規 module

候補:

```text
DkMath.NumberTheory.Legendre.ParitySafeRechargeDepthSeatFiber
```

file:

```text
lean/dk_math/DkMath/NumberTheory/Legendre/ParitySafeRechargeDepthSeatFiber.lean
```

初期 import:

```lean
import DkMath.NumberTheory.Legendre.ParitySafeRechargeDepthFourthSplit
```

L018 API が import chain から見えない場合のみ

```lean
import DkMath.NumberTheory.Legendre.LocalizedObstruction
```

を追加する。

完成後 facade `DkMath.NumberTheory.Legendre` へ import を追加する。

---

## 3. L056.1 — exact seat coordinate

薄い定義:

```lean
def paritySafeRechargeExactSeat
    (n b t : ℕ) : ℕ :=
  paritySafeRechargeExactShellPoint n b t - n ^ 2
```

exact pair 用 packet を必須とする。

推奨:

```lean
theorem paritySafeRechargeExactPair_seat_packet
    {n b t : ℕ}
    (hbt : (b,t) ∈ paritySafeRechargeExactDualBasePairs n) :
    let r := paritySafeRechargeExactSeat n b t
    r ∈ squareAnchorOddPointCoprimeOffsets n ∧
      n ^ 2 + r = paritySafeRechargeExactShellPoint n b t := by
  ...
```

もし `squareAnchorOddPointCoprimeOffsets` への直接復元が重ければ、まず

```text
r ∈ squareAnchorCoprimeOffsets n
Odd (n^2+r)
```

を分離してよい。

優先する証明 route:

- L054 `paritySafeRechargeExactDualBasePairs_exists_recharge_key`
- reconstructed recharge key の `nextSeat`
- L049/L052 の existing seat/candidate packet

または L053 prime-admissible の shell/reduced dataから coordinate arithmetic で直接閉じる。
新しい generic reconstruction API は作らない。

---

## 4. L056.2 — depth pair returns to one L018 prime-square seat

必須 theorem:

```lean
theorem paritySafeRechargeExactDepth_mem_some_coprimePrimeSquareOffset
    {n b t : ℕ}
    (hbt : (b,t) ∈ paritySafeRechargeExactDepthDualBasePairs n) :
    let r := paritySafeRechargeExactSeat n b t
    ∃ d,
      d ∈ squareAnchorNondivisorPrimes n ∧
      r ∈ squareAnchorCoprimePrimeSquareOffsets n d := by
  ...
```

proof spine:

1. L055 `paritySafeRechargeExactDepth_selected_square_dvd_shellPoint` から `p/q/s` の square divisibility。
2. L056.1 で `shellPoint = n^2+r`。
3. exact witness / selector active packet から選んだ prime `d` が `squareAnchorNondivisorPrimes n`。
4. `r ∈ squareAnchorCoprimeOffsets n` と `d^2 | n^2+r` を L018 membership theoremへ入れる。

strongly preferred:

```lean
theorem paritySafeRechargeExactDepth_seat_depthMultiplicity_pos
    {n b t : ℕ}
    (hbt : (b,t) ∈ paritySafeRechargeExactDepthDualBasePairs n) :
    0 < squareAnchorCoprimeDepthMultiplicity n
      (paritySafeRechargeExactSeat n b t) := by
  ...
```

---

## 5. L056.3 — distinct depth-seat image

定義:

```lean
noncomputable def paritySafeRechargeExactDepthSeats
    (n : ℕ) : Finset ℕ :=
  (paritySafeRechargeExactDepthDualBasePairs n).image
    (fun bt => paritySafeRechargeExactSeat n bt.1 bt.2)
```

membership theorem を付ける。

必須:

```lean
theorem paritySafeRechargeExactDepthSeats_subset_coprimeOffsets
    (n : ℕ) :
    paritySafeRechargeExactDepthSeats n ⊆ squareAnchorCoprimeOffsets n := by
  ...
```

そして今回の first capacity consumer:

```lean
theorem paritySafeRechargeExactDepthSeats_card_le_coprimePrimeSquareDepthBudget
    (n : ℕ) :
    (paritySafeRechargeExactDepthSeats n).card ≤
      squareAnchorCoprimePrimeSquareDepthBudget n := by
  ...
```

推奨 proof:

- L056.2 で image の各 seat は local depth multiplicity `>=1`。
- `squareAnchorCoprimePrimeSquareDepthBudget_eq_sum_local_depthMultiplicity` を使う。
- image subset of coprime offsets と `Finset.sum_le_sum_of_subset_of_nonneg` / single-unit sum で閉じる。

この theorem は **seat card** についてであり、`ExactDepth.card` についてではないことを docstring で明示する。

---

## 6. L056.4 — exact pair fibers over seats

pair mass を失わないため、fiber を定義する。

```lean
noncomputable def paritySafeRechargeExactDepthPairsAtSeat
    (n r : ℕ) : Finset (ℕ × ℕ) :=
  (paritySafeRechargeExactDepthDualBasePairs n).filter
    (fun bt => paritySafeRechargeExactSeat n bt.1 bt.2 = r)
```

membership theorem を付ける。

exact fiber sum を必須とする。

候補1:

```lean
theorem paritySafeRechargeExactDepthPairs_card_eq_seatFiber_sum
    (n : ℕ) :
    (paritySafeRechargeExactDepthDualBasePairs n).card =
      ∑ r ∈ paritySafeRechargeExactDepthSeats n,
        (paritySafeRechargeExactDepthPairsAtSeat n r).card := by
  ...
```

候補2として `squareAnchorCoprimeOffsets n` 全体で sum してもよい。

この identity が今回の重要な境界である。

```text
Depth pair mass
  = sum over occupied depth seats of fiber multiplicity
```

L018 が直接支払うのは seat 側であり、fiber multiplicity は別義務として残る。

strongly preferred:

```lean
theorem paritySafeRechargeExactDepthPairsAtSeat_nonempty_of_mem_depthSeats ...
```

程度の薄い API は追加可。

---

## 7. L056.5 — global residual ledger synthesis

L041 + L046 + L055 を一つの exact identity に合成する。

必須:

```lean
theorem paritySafeResidualPairMass_eq_near_add_terminal_add_depth_add_fourth
    (n : ℕ) :
    paritySafeResidualPairMass n =
      (paritySafeCanonicalNearResidualTripleIncidences n).card +
      (paritySafeTerminalSurvivingFarProductKeys n).card +
      (paritySafeRechargeExactDepthDualBasePairs n).card +
      (paritySafeRechargeExactFourthDirectionPairs n).card := by
  ...
```

association は Lean が扱いやすい形へ調整可。

さらに strongly preferred:

```lean
theorem paritySafePrimePairOverlapCount_eq_supportExcess_add_near_add_terminal_add_depth_add_fourth
    (n : ℕ) :
    paritySafePrimePairOverlapCount n =
      paritySafeSupportExcess n +
      (paritySafeCanonicalNearResidualTripleIncidences n).card +
      (paritySafeTerminalSurvivingFarProductKeys n).card +
      (paritySafeRechargeExactDepthDualBasePairs n).card +
      (paritySafeRechargeExactFourthDirectionPairs n).card := by
  ...
```

これは新しい estimate ではないが、現在までの residual route を一つの global accounting surface に戻す重要な consumer theorem である。

---

## 8. False beam — pair mass is not seat mass

次の arithmetic beam を固定する。

```text
n = 58
point = 58^2 + 101 = 3465 = 3^2 * 5 * 7 * 11
```

同じ seat `r=101` に対し、少なくとも二つの far depth decompositions がある。

```text
(3,5,11), t=21:
  3*5*11*21 = 3465
  2*58 < 3*5*11
  b=15, b*t=315

(3,7,11), t=15:
  3*7*11*15 = 3465
  2*58 < 3*7*11
  b=21, b*t=315
```

両方で

```text
OddShellQuotient(58, b, t) = 11
3 | t
```

なので selected-prime depth は同じ prime `3` に由来する。

最低限 arithmetic theorem:

```lean
theorem paritySafeRechargeExactDepthSeat_noninjective_false_beam :
    58 ^ 2 + 101 = 3 ^ 2 * 5 * 7 * 11 ∧
      3 * 5 * 11 * 21 = 58 ^ 2 + 101 ∧
      3 * 7 * 11 * 15 = 58 ^ 2 + 101 ∧
      2 * 58 < 3 * 5 * 11 ∧
      2 * 58 < 3 * 7 * 11 ∧
      paritySafeRechargeOddShellQuotient 58 15 21 = 11 ∧
      paritySafeRechargeOddShellQuotient 58 21 15 = 11 ∧
      3 ∣ 21 ∧ 3 ∣ 15 := by
  norm_num [paritySafeRechargeOddShellQuotient]
```

もし軽く閉じるなら、A+ target として

```text
(15,21) ∈ ExactDepthPairs 58
(21,15) ∈ ExactDepthPairs 58
exactSeat 58 15 21 = 101
exactSeat 58 21 15 = 101
```

まで形式化してよい。

この beam の目的は、

```text
ExactDepthPairs -> (seat, depthPrime)
```

の naive injectivity を禁止することである。

**この counterexample があるので、今回 `ExactDepth.card <= DepthBudget` は mandatory target にしない。**

---

## 9. 禁止事項 / 非目標

今回は以下を行わない。

- `ExactDepth.card ≤ squareAnchorCoprimePrimeSquareDepthBudget` を根拠なく主張
- fiber card `≤1` を主張
- depth witness prime の uniqueness
- selected depth は必ず canonical `p` depth だとする主張
- fourth direction を fifth direction へ展開
- generic hypergraph / graph
- generic valuation tower
- smaller anchor / descent / induction
- analytic sieve / PNT / Mertens / asymptotic density
- terminal / near / fourth の新しい counting estimate
- global contradiction
- Legendre conjecture / RH proof claim

今回の目的は **Depth branch を既存 L018 ledgerへ正しい粒度で戻し、残る fiber multiplicity を隠さないこと**である。

---

## 10. Outcome 判定

### Outcome A+ — DEPTH SEAT RETURN / EXACT FIBER LEDGER

1. exact seat coordinate
2. exact seat candidate/coprime packet
3. depth pair -> some L018 prime-square seat
4. distinct depth-seat image
5. `DepthSeats.card ≤ L018 DepthBudget`
6. exact depth pair fiber sum
7. residual global ledger synthesis
8. n=58 noninjective depth-seat false beam

### Outcome A — DEPTH SEAT RETURN

1–6 を完成。
global ledger synthesis または strong false-beam membership の一部だけ未実装。

### Outcome B — SEAT RETURN ONLY

exact seat と L018 prime-square membership は閉じるが、fiber sum / seat capacity transport が Lean surface 上不自然。
その obstacle を report して停止する。

### Outcome C — FALSE

exact depth pair が parity-safe/coprime shell seat へ戻らない、または L055 square packet を L018 prime-square membership に接続できない具体的 counterexample が出た場合。

---

## 11. validation

最低限:

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeRechargeDepthSeatFiber
lake build DkMath.NumberTheory.Legendre
git diff --check
```

新規 source について

```text
sorry
admit
axiom
native_decide
```

を監査する。

---

## 12. report

候補:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveStructure-260822-v0/
primitive-parity-safe-recharge-depth-seat-fiber-260826.md
```

最低限:

1. Outcome
2. exact seat coordinate / packet
3. L018 prime-square return
4. depth-seat image capacity
5. exact fiber sum
6. global residual ledger synthesis
7. n=58 false beam
8. remaining fiber multiplicity gap
9. non-goals
10. validation

---

## STOP

今回の終了地点は次。

```text
ExactDepth pair
  -> exact shell seat r
  -> some L018 prime-square witness at r

DepthSeats.card <= L018 DepthBudget

ExactDepth.card
  = sum_r DepthFiber(r).card
```

ここで停止する。

次 checkpoint では、この fiber multiplicityを residual/pair support combinatorics で実際に抑えるか、Fourth branch を別 consumerへ送るかを比較する。

**fifth direction へは進まない。**
