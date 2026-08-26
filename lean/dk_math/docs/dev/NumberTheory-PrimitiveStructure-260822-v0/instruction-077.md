# instruction-077 — PRIM-L060S Active-Support Membership Bridge / Terminal Exact-Support Closure

## 0. 作業先

- repository: `Deskuma/dkmath`
- branch: `wip/number-theory-primitive-structure-260822-v2`
- base HEAD at review: `718162df23013a7ecf2bf72b6b769e8cb9ebf41b`
- Lean / Mathlib: current checkout (`Lean 4.32.2`) を維持する。upgrade しない。

前 checkpoint `PRIM-L060R` は **Outcome P — ENGINEERING PARTIAL** として受理する。

現在 Lean で閉じている terminal spine は次である。

```text
terminal key
  -> canonical far residual seat

n^2 + nextSeat = p*q*s

n=16, key=(3,(7,13)), nextSeat=17
```

一方、proof decomposition 後も

```text
three_mem_activeSupport
activeSupport_cases
```

が local `maxHeartbeats 800000` で timeout した。

数学的 counterexample は出ていない。今回の診断では、Terminal 固有の素因数分解より前に、`paritySafeActiveSupport` の membership を point divisibility へ落とす公開 API が不足していることが主な engineering friction と判断する。

今回の bounded target は **combined ledger / seat injectivity へ戻らず**、この membership bridge を一段下で公開し、Terminal の exact support card `= 3` だけを閉じることとする。

---

## 1. 最重要方針

Terminal module 内で次を直接 unfold / simp し続けない。

```lean
paritySafeActiveSupport n r
```

まず定義元 `ParitySafeIncidenceBalance.lean` に、active support membership の薄い API を追加する。

既存 L035 には既に

```lean
@[simp] theorem mem_paritySafeActiveWaveOffsets_iff_dvd
    {n q r : ℕ} :
    r ∈ paritySafeActiveWaveOffsets n q ↔
      r ∈ squareAnchorOddPointCoprimeOffsets n ∧ q ∣ n ^ 2 + r := by
  simp [paritySafeActiveWaveOffsets, SquareOffsetForbiddenBy]
```

という同型 surface がある。

今回も同じ `SquareOffsetForbiddenBy` normalization を一度だけ定義元で閉じる。

---

## 2. L060S.1 — active-support membership bridge

修正対象:

```text
lean/dk_math/DkMath/NumberTheory/Legendre/ParitySafeIncidenceBalance.lean
```

`paritySafeActiveSupport` 定義直後に追加する。

必須 theorem:

```lean
@[simp] theorem mem_paritySafeActiveSupport_iff_dvd
    {n q r : ℕ} :
    q ∈ paritySafeActiveSupport n r ↔
      q ∈ squareAnchorOddActivePrimes n ∧
        q ∣ n ^ 2 + r := by
  simp [paritySafeActiveSupport, SquareOffsetForbiddenBy]
```

`SquareOffsetForbiddenBy` の actual simp normal form に合わせて theorem body は調整可。

### 診断 gate

この theorem 単体が通常 heartbeat で通らない場合は、Terminal proof を再試行しない。

その場合 Outcome E として、

- actual goal state / timeout location
- `SquareOffsetForbiddenBy` normalization のどこで重くなるか

を report して停止する。

**global heartbeat を上げて押し切らない。**

---

## 3. L060S.2 — terminal prime/order packet

修正対象:

```text
DkMath.NumberTheory.Legendre.ParitySafeTerminalSupportCost
```

Terminal support proof で nested filter unpack を繰り返さないため、key 自体の finite packet を一つだけ公開する。

候補:

```lean
theorem paritySafeTerminalSurvivingFarProductKey_prime_packet
    {n p q s : ℕ}
    (hkey : (p,(q,s)) ∈ paritySafeTerminalSurvivingFarProductKeys n) :
    p ∈ squareAnchorOddActivePrimes n ∧
      q ∈ squareAnchorOddActivePrimes n ∧
      s ∈ squareAnchorOddActivePrimes n ∧
      p < q ∧ q < s := by
  ...
```

推奨 route:

1. `mem_paritySafeTerminalSurvivingFarProductKeys.mp hkey`
2. surviving key を unpack
3. far triple key を `Finset.mem_filter.mp`
4. `mem_paritySafeTripleGateTriples.mp`
5. first prime は `TripleGatePrimes` membership から odd-active へ戻す

必要なら `p < s` も追加してよいが必須ではない。

この theorem では `activeSupport` を触らない。

---

## 4. L060S.3 — three terminal primes are in active support

既存 theorem:

```lean
paritySafeTerminalSurvivingFarProductKey_point_eq
```

と L060S.1 / L060S.2 だけを使う。

必須:

```lean
theorem paritySafeTerminalSurvivingFarProductKey_three_mem_activeSupport
    {n p q s : ℕ}
    (hkey : (p,(q,s)) ∈ paritySafeTerminalSurvivingFarProductKeys n) :
    let r := paritySafeFarProductWaveNextSeat n (p,(q,s))
    p ∈ paritySafeActiveSupport n r ∧
      q ∈ paritySafeActiveSupport n r ∧
      s ∈ paritySafeActiveSupport n r := by
  ...
```

proof spine:

- prime packet から `p,q,s ∈ squareAnchorOddActivePrimes n`
- point equation `n^2+r = p*q*s`
- divisibilityは `dvd_mul_left` / `dvd_mul_right` 等で直接構成
- `mem_paritySafeActiveSupport_iff_dvd.mpr`

### 禁止

この theorem 内で

```lean
rw [paritySafeActiveSupport]
unfold paritySafeActiveSupport
simp [paritySafeActiveSupport]
```

を行わない。

L060S.1 の public bridge のみ使用する。

---

## 5. L060S.4 — arbitrary active support member is one of p/q/s

必須:

```lean
theorem paritySafeTerminalSurvivingFarProductKey_activeSupport_cases
    {n p q s a : ℕ}
    (hkey : (p,(q,s)) ∈ paritySafeTerminalSurvivingFarProductKeys n)
    (ha : a ∈ paritySafeActiveSupport n
      (paritySafeFarProductWaveNextSeat n (p,(q,s)))) :
    a = p ∨ a = q ∨ a = s := by
  ...
```

proof spine:

1. `mem_paritySafeActiveSupport_iff_dvd.mp ha` から
   - `a` odd-active prime
   - `a ∣ n^2+r`
2. terminal point equationで `a ∣ p*q*s`
3. `Nat.Prime.dvd_mul` を二回
4. `Nat.dvd_prime` / prime divisibility equality で
   `a=p ∨ a=q ∨ a=s`

Terminal support を unfold しない。

Generic unique-factorization helper は作らない。

---

## 6. L060S.5 — subset/superset を分離

exact Finset equalityを先に作らない。

### lower subset

```lean
theorem terminal_three_subset_activeSupport ... :
    {p,q,s} ⊆ paritySafeActiveSupport n r := by
  ...
```

L060S.3 だけで閉じる。

### upper subset

```lean
theorem terminal_activeSupport_subset_three ... :
    paritySafeActiveSupport n r ⊆ {p,q,s} := by
  ...
```

L060S.4 と `simp only [Finset.mem_insert, Finset.mem_singleton]` 程度で閉じる。

名前は namespace に合わせて調整可。

---

## 7. L060S.6 — exact card = 3

今回の main target。

必須:

```lean
theorem paritySafeTerminalSurvivingFarProductKey_activeSupport_card_eq_three
    {n p q s : ℕ}
    (hkey : (p,(q,s)) ∈ paritySafeTerminalSurvivingFarProductKeys n) :
    let r := paritySafeFarProductWaveNextSeat n (p,(q,s))
    (paritySafeActiveSupport n r).card = 3 := by
  ...
```

推奨 proof:

1. L060S.2 から `p<q<s`、従って三点 distinct。
2. `{p,q,s}.card = 3` を局所 `simp` / `norm_num` で閉じる。
3. lower subset から
   `{p,q,s}.card ≤ activeSupport.card`。
4. upper subset から
   `activeSupport.card ≤ {p,q,s}.card`。
5. `omega`。

exact equality

```lean
paritySafeActiveSupport n r = {p,q,s}
```

は、この card theorem 後に `Finset.Subset.antisymm` が軽く閉じる場合のみ追加してよい。
必須ではない。

---

## 8. L060S.7 — n=16 support regression

既存 L041 には既に

```text
paritySafeActiveSupport 16 17 = {3,7,13}
```

の accepted witness があるため、再 enumeration はしない。

今回の general terminal theorem の consumer として最低限:

```lean
theorem paritySafeTerminalSupport_card_regression_16 :
    (paritySafeActiveSupport 16 17).card = 3 := by
  ...
```

terminal key membershipを軽く構成できるなら general theorem から出す。
重い場合は既存 L041 witness を `simpa` consumer してよい。

目的は general theorem と concrete accepted seat の整合確認であり、有限 prime enumeration を再実装することではない。

---

## 9. 今回やらないこと

L060S では以下へ進まない。

- `paritySafeTerminalFarProductSeats` image
- terminal key -> seat injectivity
- TerminalKeys.card = TerminalSeats.card
- terminal support cost `2*T ≤ SupportExcess`
- collisionとの disjointness
- combined `2*T+3*C ≤ SupportExcess`
- Near branch
- FourDirectionGate counting
- fifth direction
- generic factorization / hypergraph
- analytic estimate
- descent / global contradiction
- Legendre / RH

これらは `support.card=3` が compiled API として確立してから次 checkpoint で再開する。

---

## 10. heartbeat policy

今回の目的は heartbeat を上げることではなく **reduction path を短くすること**。

- L060S.1 membership bridge は通常 heartbeat で通す。
- L060S.3/L060S.4 もまず通常 heartbeat。
- 既存巨大 theoremを再-unfoldしない。
- `simp` は明示 lemma list を優先。
- global `set_option maxHeartbeats` は禁止。
- theorem-local heartbeat 追加は、bridge 使用後に残る小 theorem一個だけで必要性が明確な場合に限り、reportへ理由を記録する。

---

## 11. Outcome

### Outcome A+ — TERMINAL EXACT-SUPPORT CLOSURE

1. `mem_paritySafeActiveSupport_iff_dvd`
2. terminal prime/order packet
3. `p,q,s ∈ activeSupport`
4. arbitrary active member cases
5. lower / upper subset
6. terminal `activeSupport.card = 3`
7. n=16 regression
8. report / facade remains valid

### Outcome A — MEMBERSHIP BRIDGE + SUPPORT BOUNDS

1–5 が閉じるが、card normalization の軽微な Lean surface 障害のみ残る。

### Outcome E — MEMBERSHIP BRIDGE ENGINEERING BLOCK

L060S.1 の薄い membership bridge 自体が通常 heartbeatで閉じない、または `SquareOffsetForbiddenBy` normalization に予想外の大規模 reduction が必要。

その場合 Terminal theoremへ戻らず、具体的な elaboration obstacle を reportして停止する。

### Outcome C — FALSE

`activeSupport` membership と `odd-active ∧ point divisibility` が definition上同値でないことが判明する、または terminal pointに `p,q,s` 以外の active primeが入り得る具体的 counterexample が出る場合。

---

## 12. validation

最低限:

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeIncidenceBalance
lake build DkMath.NumberTheory.Legendre.ParitySafeTerminalSupportCost
lake build DkMath.NumberTheory.Legendre
git diff --check
```

修正 source について

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
primitive-parity-safe-terminal-exact-support-closure-260826.md
```

最低限:

1. Outcome
2. membership bridgeが通常 heartbeatで閉じたか
3. terminal prime/order packet
4. three-membership
5. arbitrary-member cases
6. subset decomposition
7. exact card=3
8. n=16 regression
9. heartbeat usageの有無
10. non-goals
11. validation

を記録する。

---

## STOP

今回の終了地点はここだけ。

```text
q ∈ ActiveSupport(n,r)
  <-> q ∈ OddActivePrimes(n) ∧ q | n^2+r

Terminal key (p,q,s)
  -> ActiveSupport(n,nextSeat).card = 3
```

ここで停止する。

次 checkpoint で初めて seat image / injectivity / disjoint weighted support-cost ledgerへ戻る。
