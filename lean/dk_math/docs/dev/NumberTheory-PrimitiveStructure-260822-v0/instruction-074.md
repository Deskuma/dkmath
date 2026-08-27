# instruction-074 — PRIM-L059 Depth-Collision / Fourth-Branch Four-Direction Gate

## 0. 作業先

- repository: `Deskuma/dkmath`
- branch: `wip/number-theory-primitive-structure-260822-v2`
- base HEAD at review: `91e2c78311ecd7ab2878b425cc0436a7d75ef14e`
- Lean / Mathlib: current checkout (`Lean 4.32.2`) を維持する。upgrade しない。

前 checkpoint `PRIM-L058` は **Outcome A（A+ の support-cost 1項目のみ未回収）— LOCAL RESIDUAL-PAIR CAPACITY** として受理する。

L058 の主成果は閉じている。

```text
DepthFiber(n,r).card
  <= choose (ActiveSupport(n,r).card - 1) 2

collision r
  -> ActiveSupport(n,r).card >= 4

DepthFiberExcess
  <= DepthResidualPairCapacityExcess
```

さらに L057/L058 の n=58 actual collision も維持されている。

今回、`DepthResidualPairCapacityExcess` をさらに同じ二項係数の恒等分解で再帰的に削ってはならない。その方向は既存 residual-pair mass の内部を再記述するだけになりやすく、独立な算術 gain を増やさない。

今回の bounded target は、L058 の **4方向 support** と L055 の **canonical fourth direction** を、L042 cubic gate の一段強い

```text
p^4 < squareBody n
```

へ合流させることだけである。

---

## 1. 数学的核

### Depth-collision 側

collision seat `r` では L058 より

```text
4 <= (paritySafeActiveSupport n r).card.
```

`r` は covered parity-safe candidate であり、canonical support prime

```text
p := paritySafeCanonicalSupportPrime n r
```

を持つ。

collision fiber から depth pair を一つ取り、その reverse key

```text
(p,(q,s))
```

を actual far residual incidenceへ戻せる。L042 の existing shell packet から

```text
p < q
p < s
q < s
p*q*s | n^2+r
n^2+r <= squareBody n
```

が得られる。

support card >=4 なので、active support には `p,q,s` と異なる第四 prime `u` が存在する。

```text
u ∈ paritySafeActiveSupport n r
u != p,q,s
```

canonical minimum より `p < u`。

`u` も point を割る。`p,q,s,u` は相異なる prime なので pairwise coprime であり、

```text
p*q*s*u | n^2+r
```

を得る。

従って

```text
p^4 < p*q*s*u <= n^2+r <= squareBody n.
```

### ExactFourth 側

L055 の fourth packet は exact fourth pair `(b,t)` と witness `(p,q)` に対し

```text
s := OddShellQuotient n b t
u := minFac t

p < q < s
p < u
u != q,s
p*q*s*u | ExactShellPoint n b t
```

を既に与える。

exact shell point は square shell 内なので同様に

```text
p^4 < squareBody n
```

が従う。

したがって Depth collision と ExactFourth は、構成理由は異なるが **同じ fourth-power first-prime gate** に入る。

---

## 2. 新規 module

候補:

```text
DkMath.NumberTheory.Legendre.ParitySafeFourDirectionGate
```

file:

```text
lean/dk_math/DkMath/NumberTheory/Legendre/ParitySafeFourDirectionGate.lean
```

初期 import:

```lean
import DkMath.NumberTheory.Legendre.ParitySafeRechargeDepthFiberResidualCapacity
```

L055/L042 API は import chain で見えるものを優先する。elaboration 上必要な場合のみ直接 import を追加する。

完成後 facade

```text
DkMath.NumberTheory.Legendre
```

へ import を追加する。

---

## 3. L059.1 — L058 support-cost cleanup

instruction-073 の A+ で唯一未回収だった support-cost consumer を先に閉じる。

必須:

```lean
theorem three_mul_depthFiberCollisionSeats_card_le_supportExcess
    (n : ℕ) :
    3 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card <=
      paritySafeSupportExcess n := by
  ...
```

proof spine:

1. collision seat `r` は depth seat、従って parity-safe candidate。
2. L058 `collision_support_card_ge_four` から
   `(activeSupport n r).card - 1 >= 3`。
3. `3 * card` を collision seats 上の `sum 3` として書く。
4. collision subset candidate で
   `sum_collision 3 <= sum_candidate (support.card - 1)`。
5. 右辺は `paritySafeSupportExcess n`。

この theorem は **collision seat count** の cost であり、`DepthFiberExcess` 全体を直接 SupportExcess へ charge するものではない、と docstring に明記する。

---

## 4. L059.2 — fourth-power gate prime universe

L042 cubic gate と平行な薄い定義を置く。

```lean
noncomputable def paritySafeFourDirectionGatePrimes
    (n : ℕ) : Finset ℕ :=
  (squareAnchorOddActivePrimes n).filter
    (fun p => p ^ 4 < squareBody n)
```

membership theorem:

```lean
@[simp] theorem mem_paritySafeFourDirectionGatePrimes
    {n p : ℕ} :
    p ∈ paritySafeFourDirectionGatePrimes n ↔
      p ∈ squareAnchorOddActivePrimes n ∧
      p ^ 4 < squareBody n := by
  ...
```

さらに gate refinement を必須とする。

```lean
theorem paritySafeFourDirectionGatePrimes_subset_tripleGatePrimes
    (n : ℕ) :
    paritySafeFourDirectionGatePrimes n ⊆
      paritySafeTripleGatePrimes n := by
  ...
```

active prime は `2 <= p` なので `p^3 < p^4`。従って fourth-power gate は cubic gate の genuine refinement である。

card corollary も軽ければ追加:

```lean
(paritySafeFourDirectionGatePrimes n).card <=
  (paritySafeTripleGatePrimes n).card
```

---

## 5. L059.3 — depth collision → actual four-direction packet

まず collision seat から四つの distinct active directions を **積の可除性まで**公開する。

推奨 shape:

```lean
theorem paritySafeRechargeDepthFiberCollision_fourDirection_packet
    {n r : ℕ}
    (hr : r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n) :
    let p := paritySafeCanonicalSupportPrime n r
    ∃ q s u,
      q ∈ paritySafeActiveSupport n r ∧
      s ∈ paritySafeActiveSupport n r ∧
      u ∈ paritySafeActiveSupport n r ∧
      p < q ∧ p < s ∧ p < u ∧
      q ≠ s ∧ q ≠ u ∧ s ≠ u ∧
      p * q * s * u ∣ n ^ 2 + r := by
  ...
```

`q<s` を保持できるなら追加してよい。

### 推奨 route

巨大な generic four-hypergraph を作らない。

1. collision fiber の nonempty から depth pair `bt` を一つ取得。
2. L058 reverse key / residual-pair packet で actual residual pair `(q,s)` を得る。
3. 必要なら薄い theorem として

   ```text
   depth pair at seat -> actual canonical far residual incidence
   ```

   をこの module 内で公開してよい。
4. L042 `paritySafeCanonicalResidualTripleIncidence_shell_packet` を再利用し、`p<q,s`, `p*q*s | point` を得る。
5. L058 `support.card >=4` と `p,q,s` distinct から
   `u ∈ activeSupport \ {p,q,s}` を一つ取る。
   - generic cardinal library は作らず、局所 `Finset` argument でよい。
6. canonical `p=min' activeSupport` から `p<u`。
7. `u ∈ activeSupport` から `u` prime / `u | point`。
8. `u` は `p,q,s` と異なる prime なので `Coprime (p*q*s) u`。
9. `p*q*s | point`, `u | point`, coprime から `p*q*s*u | point`。

Mathlib の coprime-divisor multiplication API 名は current checkout に合わせる。必要なら既存 DkMath の同種 proof を検索する。

---

## 6. L059.4 — depth collision canonical prime passes fourth gate

L059.3 の main arithmetic consumer。

必須:

```lean
theorem paritySafeRechargeDepthFiberCollision_canonicalPrime_mem_fourDirectionGate
    {n r : ℕ}
    (hr : r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n) :
    paritySafeCanonicalSupportPrime n r ∈
      paritySafeFourDirectionGatePrimes n := by
  ...
```

proof spine:

- collision seat は covered candidate。
- canonical prime は active。
- L059.3 の `p<q,s,u` から `p^4 < p*q*s*u`。
- product divisibility + positive point から `p*q*s*u <= n^2+r`。
- existing square-shell theoremから `n^2+r <= squareBody n`。

ここが DepthFiber collision から得る新しい **fourth-root scale restriction**。

---

## 7. L059.5 — ExactFourth first prime passes the same gate

L055 fourth packetを直接 consumer する。

必須:

```lean
theorem paritySafeRechargeExactFourth_firstPrime_mem_fourDirectionGate
    {n b t p q : ℕ}
    (hbt : (b,t) ∈ paritySafeRechargeExactFourthDirectionPairs n)
    (hwitness : ParitySafeRechargeExactPairWitness n b t p q) :
    p ∈ paritySafeFourDirectionGatePrimes n := by
  ...
```

proof spine:

1. `hwitness.1` から `p` active（triple gate membership を unpack）。
2. L055 `paritySafeRechargeExactFourthPrime_packet hbt hwitness` から
   `s,u`, `p<q<s`, `p<u`, quadruple divisibility。
3. exact pair / prime-admissible shell upperから
   `ExactShellPoint n b t <= squareBody n`。
4. `p^4 < p*q*s*u <= ExactShellPoint <= squareBody`。

この theorem は `u` の global injectivity を一切必要としない。

---

## 8. L059.6 — unified four-direction frontier

Depth collision と ExactFourth が同じ first-prime gate に入ることを consumer theorem / docstring で明示する。

無理に異種 domain の大きな sum type Finset を作る必要はない。
次の二本が揃えば数学的 frontier として十分:

```text
DepthCollision seat
  -> canonicalPrime ∈ FourDirectionGatePrimes

ExactFourth pair + witness(p,q)
  -> p ∈ FourDirectionGatePrimes
```

A+ target として薄くまとめるなら Prop-level theorem を追加してよい。

例:

```lean
theorem paritySafe_fourDirection_frontier ... :
  (...) ∨ (...) -> ∃ p, p ∈ paritySafeFourDirectionGatePrimes n := ...
```

ただし theorem shape が不自然なら追加しない。

---

## 9. strict refinement / regression witnesses

### 9.1 cubic gate から本当に縮むこと

推奨 arithmetic regression:

```text
n = 16
p = 5
squareBody 16 = 288
5^3 = 125 < 288
5^4 = 625 > 288
```

`5` は odd active prime at anchor 16 なので、軽く閉じるなら

```lean
theorem paritySafeFourDirectionGate_strict_refinement_witness :
    5 ∈ paritySafeTripleGatePrimes 16 ∧
      5 ∉ paritySafeFourDirectionGatePrimes 16 := by
  ...
```

を追加する。

この witness は fourth-power gate が単なる rename でないことを固定する。

### 9.2 existing examples

最低限どちらか:

```text
n=58, r=101 depth collision
  -> canonical prime ∈ FourDirectionGatePrimes 58
```

または canonical prime が軽く `3` と確定できるなら

```text
3 ∈ FourDirectionGatePrimes 58
```

ExactFourth 側は existing n=62 examplesの first prime `3` が gate を通ることを arithmetic regression として追加してよい。

---

## 10. 禁止事項 / 非目標

今回は以下を行わない。

- `DepthResidualPairCapacityExcess` の Pascal 型再帰分解
- generic 4-hypergraph / k-hypergraph library
- generic finite-set product theoryの新設
- fifth direction
- fourth-direction `u` 単独、`(p,u)`、`(t,u)` への global injection
- FourDirectionGatePrimes の PNT / sieve / asymptotic counting
- `FourDirectionGatePrimes.card` だけから collision seats / Fourth pairs を injectively bound する主張
- near / terminal の新 counting
- smaller anchor / descent / induction
- global contradiction
- Legendre conjecture / RH proof claim

特に

```text
Depth collision -> p ∈ FourDirectionGatePrimes
```

から

```text
CollisionSeats.card <= FourDirectionGatePrimes.card
```

を根拠なく主張してはならない。同じ canonical prime が複数 seat を所有し得る。

ExactFourth でも first-prime gate membership は cardinal injection を意味しない。

---

## 11. Outcome 判定

### Outcome A+ — FOUR-DIRECTION GATE

1. `3 * CollisionSeats.card <= SupportExcess` cleanup
2. `paritySafeFourDirectionGatePrimes` + membership
3. FourGate subset CubicGate
4. depth collision four-direction product packet
5. depth collision canonical prime ∈ FourGate
6. ExactFourth witness first prime ∈ FourGate
7. strict-refinement arithmetic witness
8. n=58 または n=62 regression
9. facade import / report

### Outcome A — FOURTH-POWER FRONTIER

2,3,5,6 を完成し、fourth-power gateへの両 branch 接続は閉じる。
L059.1 support-cost cleanup または explicit quadruple-product packetの一部が Lean surface 上 disproportionate なら report して停止。

### Outcome B — ONE-SIDED GATE

Depth collision または ExactFourth の片側だけ `p^4 < squareBody` が閉じる。
閉じない側の obstacle を concrete theorem shape とともに reportする。

### Outcome C — FALSE

collision support >=4 から canonical `p^4 < squareBody` が導けない concrete counterexample、または L055 Fourth packet が fourth-power gate に入らない counterexample が出た場合。

---

## 12. validation

最低限:

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeFourDirectionGate
lake build DkMath.NumberTheory.Legendre
git diff --check
```

変更 source について

```text
sorry
admit
axiom
native_decide
```

を監査する。

L056 public wrapperを追加修正する必要が無ければ既存実装をそのまま維持する。

---

## 13. report

候補:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveStructure-260822-v0/
primitive-parity-safe-four-direction-gate-260826.md
```

最低限:

1. Outcome
2. L058 review / support-cost cleanup
3. fourth-power gate definition
4. cubic gateとの refinement
5. depth collision four-direction packet
6. collision canonical prime gate
7. ExactFourth gate
8. arithmetic regressions
9. non-goals
10. validation

を記録する。

---

## STOP

今回の終了地点は次。

```text
Depth collision seat
  -> at least four active directions
  -> canonical p^4 < squareBody n
  -> canonical p ∈ FourDirectionGatePrimes n

ExactFourth pair
  -> p,q,s,u four distinct directions
  -> p^4 < squareBody n
  -> witness p ∈ FourDirectionGatePrimes n

FourDirectionGatePrimes n
  ⊆ TripleGatePrimes n
```

ここで停止する。

次 checkpoint で初めて、この stronger gate を使って four-direction branch の finite wave/capacity を作るか、near/terminal へ戻るかを比較する。