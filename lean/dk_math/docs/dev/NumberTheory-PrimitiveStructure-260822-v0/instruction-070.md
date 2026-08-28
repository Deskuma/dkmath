# instruction-070 — PRIM-L055 Exact Recharge Depth / Canonical Fourth-Direction Split

## 0. 作業先

- repository: `Deskuma/dkmath`
- branch: `wip/number-theory-primitive-structure-260822-v2`
- base HEAD at review: `96d7544c7409bcd65c713040360b9777c58daf2f`
- Lean / Mathlib: current checkout (`Lean 4.32.2`) を維持する。upgrade しない。

前 checkpoint `PRIM-L054` は **Outcome A+ — EXACT RECHARGE DUAL-BASE / REVERSE RECONSTRUCTION** として受理する。

L054 までで recharge surviving key と exact dual-base pair は同一 cardinality ではなく、有限 image として exact に一致した。

```text
RechargeDualBaseImage(n)
  = ExactRechargeDualBasePairs(n)
```

従って

```text
Recharge.card = ExactDualBasePairs.card
FarResidual.card = Terminal.card + ExactDualBasePairs.card
```

まで閉じている。

今回の bounded target は、この exact recharge world をさらに

```text
selected-prime depth
      or
canonical fourth direction
```

へ exact partition することだけである。

PRIM-L044 では far cofactor `t > 1` に対して局所的に

```text
p^2 | point
or q^2 | point
or s^2 | point
or new prime direction u | t
```

という disjunction が得られていた。しかし当時は cofactor / returned prime を global coordinate として injective に扱えず、第四 branch は witness のまま止めた。

L054 では `(b,t)` 自体が actual recharge image の exact coordinate になったため、今回はこの disjunction を **exact finite partition** として回収する。

---

## 1. 数学的核

exact pair `(b,t)` について witness `(p,q)` を取り、

```text
s := paritySafeRechargeOddShellQuotient n b t
b = p*q
p < q < s
```

とする。

recharge なので `1 < t`。

さらに L053/L054 の shell/far 条件から

```text
2*n < b*s
n^2 < (b*t)*s <= n^2 + 2*n
```

である。

これだけから cofactor half-scale

```text
2*t < n+2
```

が従う。

証明は

```text
n*(2*t)
  = (2*n)*t
  < (b*s)*t
  = (b*t)*s
  <= n*(n+2)
```

を `0 < n` で cancel すればよい。

次に selected primes と cofactor の関係で二分する。

### Depth branch

```text
p | t  or  q | t  or  s | t
```

なら point `P := (b*t)*s = p*q*s*t` には

```text
p^2 | P  or  q^2 | P  or  s^2 | P
```

が入る。

### Fourth-direction branch

selected primes が誰も `t` を割らない場合、`1<t` なので `t` は prime divisor を持つ。
今回その prime を existential witness のままにせず、

```text
u := Nat.minFac t
```

として canonical に選ぶ。

`u` は prime、`u | t`。
また `t` は reduced base にあり `2*t<n+2` なので、`u` は same-anchor half-scale active prime へ戻る。

roughness

```text
a active, a < p -> a ∤ t
```

と `u | t` から `p <= u`。
第四 branch では `p ∤ t` なので `u != p`、従って

```text
p < u.
```

同様に `q ∤ t`, `s ∤ t` より

```text
u != q
u != s.
```

従って第四 branch では canonical cofactor prime `u` が、selected triple と異なる本物の fourth active direction になる。

---

## 2. 新規 module

候補:

```text
DkMath.NumberTheory.Legendre.ParitySafeRechargeDepthFourthSplit
```

file:

```text
lean/dk_math/DkMath/NumberTheory/Legendre/ParitySafeRechargeDepthFourthSplit.lean
```

初期 import:

```lean
import DkMath.NumberTheory.Legendre.ParitySafeRechargeExactDualBase
```

必要なら `ParitySafeFarTripleRecharge` の既存 API は import chain 経由で利用する。
直接 import を増やすのは elaboration 上必要な場合だけとする。

完成後 facade

```text
DkMath.NumberTheory.Legendre
```

へ import を追加する。

---

## 3. L055.1 — exact cofactor packet

まず exact pair から `t` の nonterminal / half-scale packet を公開する。

必須:

```lean
theorem paritySafeRechargeExactDualBasePair_cofactor_packet
    {n b t : ℕ}
    (hbt : (b,t) ∈ paritySafeRechargeExactDualBasePairs n) :
    1 < t ∧ 2 * t < n + 2 := by
  ...
```

推奨 proof:

- `mem_paritySafeRechargeExactDualBasePairs` から prime-admissible / over-anchor packet を取得
- `b ∈ paritySafeFarCofactorBaseOffsets n` から `b ≤ n`
- `n < b*t` から `1<t`
- prime-admissible の `2*n < b*s` と shell upper を使って `2*t<n+2`

reverse reconstructed key を使って既存 `paritySafeFarProductWaveCofactor_packet` へ戻してもよいが、今回の theorem は coordinate arithmetic だけで閉じる方を優先する。

---

## 4. L055.2 — selected-depth predicate / Finset

薄い predicate を置く。

```lean
def ParitySafeRechargeSelectedDepth
    (n b t p q : ℕ) : Prop :=
  let s := paritySafeRechargeOddShellQuotient n b t
  p ∣ t ∨ q ∣ t ∨ s ∣ t
```

次に exact universe を filter する。

```lean
noncomputable def paritySafeRechargeExactDepthDualBasePairs
    (n : ℕ) : Finset (ℕ × ℕ) :=
  (paritySafeRechargeExactDualBasePairs n).filter
    (fun bt =>
      ∃ p q,
        ParitySafeRechargeExactPairWitness n bt.1 bt.2 p q ∧
        ParitySafeRechargeSelectedDepth n bt.1 bt.2 p q)
```

membership theorem を付ける。

第四 branch は depth の complement として定義する。

```lean
noncomputable def paritySafeRechargeExactFourthDirectionPairs
    (n : ℕ) : Finset (ℕ × ℕ) :=
  (paritySafeRechargeExactDualBasePairs n).filter
    (fun bt =>
      ¬ ∃ p q,
        ParitySafeRechargeExactPairWitness n bt.1 bt.2 p q ∧
        ParitySafeRechargeSelectedDepth n bt.1 bt.2 p q)
```

この定義なら witness uniqueness を別途 prerequisite にしなくても partition が閉じる。

---

## 5. L055.3 — exact partition / card split

必須:

```lean
theorem paritySafeRechargeExactDepthFourth_disjoint
    (n : ℕ) :
    Disjoint
      (paritySafeRechargeExactDepthDualBasePairs n)
      (paritySafeRechargeExactFourthDirectionPairs n) := by
  ...
```

```lean
theorem paritySafeRechargeExactDepthFourth_union
    (n : ℕ) :
    paritySafeRechargeExactDepthDualBasePairs n ∪
        paritySafeRechargeExactFourthDirectionPairs n =
      paritySafeRechargeExactDualBasePairs n := by
  ...
```

card:

```lean
theorem paritySafeRechargeExactDualBasePairs_card_eq_depth_add_fourth
    (n : ℕ) :
    (paritySafeRechargeExactDualBasePairs n).card =
      (paritySafeRechargeExactDepthDualBasePairs n).card +
      (paritySafeRechargeExactFourthDirectionPairs n).card := by
  ...
```

さらに L054 terminal split と合成:

```lean
theorem paritySafeCanonicalFarResidual_card_eq_terminal_add_depth_add_fourth
    (n : ℕ) :
    (paritySafeCanonicalFarResidualTripleIncidences n).card =
      (paritySafeTerminalSurvivingFarProductKeys n).card +
      (paritySafeRechargeExactDepthDualBasePairs n).card +
      (paritySafeRechargeExactFourthDirectionPairs n).card := by
  ...
```

結合順は Lean が扱いやすい形へ調整可。

---

## 6. L055.4 — depth branch square-divisibility packet

座標上の shell point を薄く定義してよい。

```lean
def paritySafeRechargeExactShellPoint
    (n b t : ℕ) : ℕ :=
  (b * t) * paritySafeRechargeOddShellQuotient n b t
```

必須 theorem:

```lean
theorem paritySafeRechargeExactDepth_selected_square_dvd_shellPoint
    {n b t : ℕ}
    (hbt : (b,t) ∈ paritySafeRechargeExactDepthDualBasePairs n) :
    ∃ p q,
      ParitySafeRechargeExactPairWitness n b t p q ∧
      let s := paritySafeRechargeOddShellQuotient n b t
      p ^ 2 ∣ paritySafeRechargeExactShellPoint n b t ∨
      q ^ 2 ∣ paritySafeRechargeExactShellPoint n b t ∨
      s ^ 2 ∣ paritySafeRechargeExactShellPoint n b t := by
  ...
```

`b=p*q` と selected divisor of `t` だけで閉じる。

A+ target として、既存 L018 prime-square offset ledger へ実 seat を戻せるなら追加してよい。ただしそのために大きな reconstruction 層を増やさない。

---

## 7. L055.5 — canonical fourth prime

第四 branch の主役。

```lean
def paritySafeRechargeExactFourthPrime (t : ℕ) : ℕ :=
  Nat.minFac t
```

引数を `(n,b,t)` にしてもよいが、数学的には `t` だけの関数で十分。

必須 theorem packet の推奨形:

```lean
theorem paritySafeRechargeExactFourthPrime_packet
    {n b t p q : ℕ}
    (hbt : (b,t) ∈ paritySafeRechargeExactFourthDirectionPairs n)
    (hpq : ParitySafeRechargeExactPairWitness n b t p q) :
    let s := paritySafeRechargeOddShellQuotient n b t
    let u := paritySafeRechargeExactFourthPrime t
    Nat.Prime u ∧
      u ∣ t ∧
      u ∈ paritySafeHalfScaleActivePrimes n ∧
      p < u ∧
      u ≠ q ∧
      u ≠ s ∧
      p * q * s * u ∣ paritySafeRechargeExactShellPoint n b t := by
  ...
```

proof spine:

1. L055.1 から `1<t` と `2*t<n+2`。
2. `Nat.minFac_prime` / `Nat.minFac_dvd` 系 API で `u` prime, `u|t`。
3. exact pair の prime-admissible / base packet から `t≤n`, `Coprime (2*n) t`。
4. prime divisor `u` は `n` と 2 を割らないので active。
5. `u≤t` と `2*t<n+2` から half-scale。
6. roughness と `u|t` から `p≤u`。
7. fourth complement から `p∤t`, `q∤t`, `s∤t`。
8. `u|t` と prime equality で `u≠p,q,s`。
9. `p≤u` + `u≠p` から `p<u`。
10. `b=p*q`, `u|t` から quadruple product divisibility。

Mathlib の `Nat.minFac` API 名が異なる場合は、現 checkout の API を検索して合わせる。

`Nat.minFac` 自体が実装上不自然な場合のみ、`Nat.primeFactors t` の canonical minimumへ変更してよい。その場合 report に理由を書く。

---

## 8. A+ target — coordinate-level L044 recovery

実装が軽ければ、L044 の意味を exact coordinate で再掲する consumer theorem を追加する。

```lean
theorem paritySafeRechargeExactDualBase_depth_or_canonicalFourth
    {n b t : ℕ}
    (hbt : (b,t) ∈ paritySafeRechargeExactDualBasePairs n) :
    (b,t) ∈ paritySafeRechargeExactDepthDualBasePairs n ∨
      (b,t) ∈ paritySafeRechargeExactFourthDirectionPairs n := by
  ...
```

union theorem からほぼ即座でよい。

さらに fourth branch で `u` が canonical であることを前面に出す。

```text
old L044:
  some u exists

L055:
  u = minFac(t)
```

ここが今回の新情報である。

---

## 9. arithmetic witnesses / false beams

最低二つ。

### Depth witness

```text
n=17
p=3, q=5, s=7, t=3
b=15
17^2 + 26 = 3*5*7*3
```

ここでは `p|t` なので selected-prime depth branch。

### Fourth-direction witness / noninjective warning

```text
n=62
(3,5,37), t=7, b=15
(3,11,17), t=7, b=33
```

双方で canonical cofactor prime は `u=7`。

従って今回 canonical `u=minFac(t)` を導入しても

```text
recharge pair -> u
```

の global injectivity は主張してはならない。

これは L044 false beam を維持する。

---

## 10. 禁止事項 / 非目標

今回は以下を行わない。

- fourth-prime `u` 単独への global injection
- `(t,u)` や `(b,u)` の injectivity を根拠なく主張
- generic 4-hypergraph
- generic least-prime-factor theory の新設
- `t` prime / squarefree
- `p ∤ t` を recharge 全体へ拡張
- depth branch が必ず `p` depth だとする主張
- `u<q`, `q<u`, `u<s`, `s<u` の無根拠な order
- smaller anchor / descent / induction
- analytic sieve / PNT / Mertens / asymptotic density
- terminal branch counting
- global contradiction
- Legendre conjecture / RH proof claim

今回の目的は exact recharge mass を

```text
selected depth
+
canonical fourth direction
```

へ分解するところまで。

---

## 11. Outcome 判定

### Outcome A+ — EXACT DEPTH / CANONICAL FOURTH DIRECTION

1. exact cofactor `1<t`, `2*t<n+2`
2. depth/fourth exact Finset partition
3. exact card split
4. far residual terminal + depth + fourth exact split
5. depth square-divisibility packet
6. canonical `u=minFac(t)` fourth-prime packet
7. half-scale active return
8. `p<u`, `u≠q,s`, quadruple product divisibility
9. arithmetic witnesses

### Outcome A — EXACT DEPTH / FOURTH SPLIT

1–5 と exact partition/card split を完成。
第四 branch は `∃ u` の half-scale new-direction packetまでで停止し、`minFac` canonicalizationだけ未完。

### Outcome B — PARTITION ONLY

exact depth/fourth partition と card splitは閉じるが、coordinate-level prime return に API obstacle がある。
その theorem shape と obstacle を report して停止する。

### Outcome C — FALSE

exact pair で `t≤1`、`2*t<n+2` failure、または selected depth / genuinely new direction の exhaustive split を壊す concrete counterexample が出た場合。

---

## 12. validation

最低限:

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeRechargeDepthFourthSplit
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

## 13. report

候補:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveStructure-260822-v0/
primitive-parity-safe-recharge-depth-fourth-split-260826.md
```

最低限:

1. Outcome
2. exact cofactor half-scale packet
3. depth/fourth definitions
4. exact partition/card split
5. selected-depth square packet
6. canonical fourth prime packet
7. L044 との関係
8. false beam
9. 非目標
10. validation

を記録する。

---

## STOP

今回の終了地点は次。

```text
FarResidual.card
  = Terminal.card
  + ExactDepth.card
  + ExactFourth.card

ExactFourth pair
  -> t > 1
  -> u := minFac(t)
  -> u is half-scale active
  -> p < u
  -> u distinct from q,s
  -> p*q*s*u divides the exact shell point
```

ここで停止する。

次 checkpoint で初めて、Depth 側を L018 prime-square ledgerへ charge するか、Fourth 側を canonical 4-direction capacityへ送るかを比較する。