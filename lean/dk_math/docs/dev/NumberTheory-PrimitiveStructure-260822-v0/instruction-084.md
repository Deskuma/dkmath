# instruction-084 — PRIM-L064 Fourth Gated Dual-Base Capacity / Low-Cost Capacity Closure

## 0. 作業先

- repository: `Deskuma/dkmath`
- branch: `wip/number-theory-primitive-structure-260822-v2`
- base HEAD at review: `7b212bc618b24d0c18f9def0cda20d986e5e051a`
- Lean / Mathlib: current checkout (`Lean 4.32.2`) を維持する。upgrade しない。

前 checkpoint `PRIM-L063` は **Outcome A+ — NEAR FIRST-PRIME WAVE CAPACITY COMPLETE** として受理する。

現在 Lean では低コスト残余が

```text
LowCostResidual
  = Near
  + NonCollisionDepth
  + Fourth
```

と exact に定義され、

```text
Near.card
  <= NearFirstPrimeWaveBudget

NonCollisionDepth.card
  <= L018 prime-square depth budget
```

まで finite upper-control が付いた。

L063 の consumer は

```text
LowCostResidual
  <= NearFirstPrimeWaveBudget
   + L018DepthBudget
   + Fourth.card
```

であり、現在唯一 raw のまま残っている項は `Fourth.card` である。

今回の bounded target は **ExactFourth を既存 dual-base 座標 `(b,t)` の FourDirectionGate refinement へ包含し、Fourth に有限 upper capacity を付けること**だけである。

fifth direction、generic 4-hypergraph、new descent、asymptotic estimate、Near elimination、Legendre/RH 結論には進まない。

---

## 1. 既存確定 API

### L052 / L053 / L054

```lean
paritySafeRechargeOverAnchorDualBasePairs
paritySafeRechargePrimeAdmissibleDualBasePairs
paritySafeRechargeExactDualBasePairs

mem_paritySafeRechargePrimeAdmissibleDualBasePairs
mem_paritySafeRechargeExactDualBasePairs

paritySafeRechargeExactDualBasePairs_subset_primeAdmissible
paritySafeRechargePrimeAdmissibleDualBasePairs_subset_overAnchor
```

`ExactDualBasePairs` は recharge image の exact coordinate universe である。

### L055

```lean
paritySafeRechargeExactFourthDirectionPairs
mem_paritySafeRechargeExactFourthDirectionPairs
ParitySafeRechargeExactPairWitness
paritySafeRechargeExactFourthPrime
paritySafeRechargeExactFourthPrime_packet
```

### L059

```lean
paritySafeFourDirectionGatePrimes
mem_paritySafeFourDirectionGatePrimes
paritySafeRechargeExactFourth_firstPrime_mem_fourDirectionGate
```

ExactFourth pair `(b,t)` と exact witness `(p,q)` に対して、first prime `p` は必ず

```text
p ∈ paritySafeFourDirectionGatePrimes n
```

を満たす。

### L063

```lean
paritySafeLowCostResidualMass_le_nearWaveBudget_add_L018Depth_add_fourth
```

---

## 2. 新規 module

推奨:

```text
DkMath.NumberTheory.Legendre.ParitySafeFourthDualBaseCapacity
```

file:

```text
lean/dk_math/DkMath/NumberTheory/Legendre/ParitySafeFourthDualBaseCapacity.lean
```

`ParitySafeNearFirstPrimeWaveCapacity` を import してよい。

facade `DkMath.NumberTheory.Legendre` に import を追加する。

---

## 3. L064.1 — FourDirectionGate 付き dual-base upper universe

ExactFourth 自身を再定義しない。

既存 `primeAdmissible` universe の上に、exact ordered pair witness と first-prime FourDirectionGate 条件だけを要求する finite upper universe を定義する。

候補:

```lean
noncomputable def paritySafeFourthGateDualBasePairs
    (n : ℕ) : Finset (ℕ × ℕ) :=
  (paritySafeRechargePrimeAdmissibleDualBasePairs n).filter
    (fun bt =>
      ∃ p q,
        ParitySafeRechargeExactPairWitness n bt.1 bt.2 p q ∧
        p ∈ paritySafeFourDirectionGatePrimes n)
```

membership theorem:

```lean
@[simp] theorem mem_paritySafeFourthGateDualBasePairs
    {n b t : ℕ} :
    (b,t) ∈ paritySafeFourthGateDualBasePairs n ↔
      (b,t) ∈ paritySafeRechargePrimeAdmissibleDualBasePairs n ∧
      ∃ p q,
        ParitySafeRechargeExactPairWitness n b t p q ∧
        p ∈ paritySafeFourDirectionGatePrimes n := by
  ...
```

この universe は Fourth condition `¬ SelectedDepth` 自体は要求しない。

理由:
- ExactFourth を包含する upper universe として使うため。
- witness uniqueness や minFac coordinate injectivityを今回要求しないため。
- `p^4 < squareBody n` の genuine gate refinementだけを capacity に反映するため。

---

## 4. L064.2 — ExactFourth subset gated dual-base

必須:

```lean
theorem paritySafeRechargeExactFourthDirectionPairs_subset_fourthGateDualBase
    (n : ℕ) :
    paritySafeRechargeExactFourthDirectionPairs n ⊆
      paritySafeFourthGateDualBasePairs n := by
  ...
```

推奨 proof:

1. `hbt : bt ∈ ExactFourthDirectionPairs` を取る。
2. `mem_paritySafeRechargeExactFourthDirectionPairs.mp hbt` から
   - `bt ∈ ExactDualBasePairs`
   - depth-negation
   を得る。
3. `ExactDualBasePairs` membership から witness `p q` を一つ取る。
4. `paritySafeRechargeExactFourth_firstPrime_mem_fourDirectionGate hbt hwitness`。
5. `ExactDualBasePairs_subset_primeAdmissible` または membership packet の first component で prime-admissible membership。
6. gated membership theoremへ詰める。

**depth-negation は gated upper universe の membership には不要**。Fourth からの inclusion を証明するためだけに source 側で保持される。

---

## 5. L064.3 — finite cardinal upper bound

必須:

```lean
theorem paritySafeRechargeExactFourthDirectionPairs_card_le_fourthGateDualBase
    (n : ℕ) :
    (paritySafeRechargeExactFourthDirectionPairs n).card ≤
      (paritySafeFourthGateDualBasePairs n).card := by
  exact Finset.card_le_card
    (paritySafeRechargeExactFourthDirectionPairs_subset_fourthGateDualBase n)
```

また refinement chain を public にする。

```lean
theorem paritySafeFourthGateDualBasePairs_subset_exactDualBase
    (n : ℕ) :
    paritySafeFourthGateDualBasePairs n ⊆
      paritySafeRechargeExactDualBasePairs n := by
  ...
```

これは gated membership に exact witness があるので、`mem_paritySafeRechargeExactDualBasePairs.mpr` へ戻せる。

さらに:

```lean
theorem paritySafeFourthGateDualBasePairs_subset_primeAdmissible ...

theorem paritySafeFourthGateDualBasePairs_card_le_primeAdmissible ...
```

`subset_exactDualBase` が通れば

```text
Fourth
⊆ FourthGateDualBase
⊆ ExactDualBase
⊆ PrimeAdmissible
⊆ OverAnchor
```

という refinement chain を docstring / report に明示する。

### 注意

`FourthGateDualBasePairs = ExactFourthDirectionPairs` は主張しない。

selected-depth exact pairsでも first prime が FourDirectionGate に入る可能性があるため、この equality は一般には不要かつ未証明である。

---

## 6. L064.4 — optional fourth-prime packet surface

軽く通るなら、gated capacityとは別に ExactFourth の canonical fourth prime packet を consumer 向けに薄くまとめてよい。

候補:

```lean
theorem paritySafeRechargeExactFourthDirectionPair_exists_fourPrime_packet
    {n b t : ℕ}
    (hbt : (b,t) ∈ paritySafeRechargeExactFourthDirectionPairs n) :
    ∃ p q,
      ParitySafeRechargeExactPairWitness n b t p q ∧
      p ∈ paritySafeFourDirectionGatePrimes n ∧
      let s := paritySafeRechargeOddShellQuotient n b t
      let u := paritySafeRechargeExactFourthPrime t
      Nat.Prime u ∧
      u ∣ t ∧
      u ∈ paritySafeHalfScaleActivePrimes n ∧
      p < u ∧
      u ≠ q ∧
      u ≠ s ∧
      p*q*s*u ∣ paritySafeRechargeExactShellPoint n b t := by
  ...
```

これは L055 + L059 の existing packets の再包装だけ。

重い場合は optional。新しい factorization / uniqueness theorem は作らない。

---

## 7. L064.5 — LowCost capacity closure

Fourth raw card を gated capacity に置換する。

必須:

```lean
theorem paritySafeLowCostResidualMass_le_nearWaveBudget_add_L018Depth_add_fourthGateDualBase
    (n : ℕ) :
    paritySafeLowCostResidualMass n ≤
      paritySafeNearFirstPrimeWaveBudget n +
      squareAnchorCoprimePrimeSquareDepthBudget n +
      (paritySafeFourthGateDualBasePairs n).card := by
  ...
```

proof:

- L063 `paritySafeLowCostResidualMass_le_nearWaveBudget_add_L018Depth_add_fourth`
- L064.3 Fourth card bound
- `omega` または `Nat.add_le_add_left/right`

読みやすい capacity 名を定義してもよい:

```lean
noncomputable def paritySafeLowCostResidualCapacity (n : ℕ) : ℕ :=
  paritySafeNearFirstPrimeWaveBudget n +
  squareAnchorCoprimePrimeSquareDepthBudget n +
  (paritySafeFourthGateDualBasePairs n).card
```

その場合:

```lean
theorem paritySafeLowCostResidualMass_le_capacity (n : ℕ) :
    paritySafeLowCostResidualMass n ≤ paritySafeLowCostResidualCapacity n
```

を追加する。

---

## 8. L064.6 — finite upper-control frontier only

今回の到達点は以下。

```text
Near
  <= NearFirstPrimeWaveBudget

NonCollisionDepth
  <= L018 prime-square depth budget

Fourth
  <= FourthGateDualBasePairs.card

therefore

LowCostResidual
  <= LowCostResidualCapacity
```

L062 の lower frontier

```text
LowCostResidual + 3*Terminal + 5*Collision
  <= PairOverlap
  <= CoprimePairCapacity
```

との併記は report/docstring で行ってよいが、

```text
LowCostResidualCapacity + 3*T + 5*C <= CoprimePairCapacity
```

とは **推論してはならない**。

`LowCostResidual <= Capacity` は upper bound なので、lower frontier の左辺を Capacity に置換する方向は不正である。

---

## 9. 禁止 / 非目標

今回やらない:

- `Nat.minFac t` による global injectivity
- `(p,u)` だけで `(b,t)` を一意復元する主張
- generic ordered semiprime factorization library
- generic 4-uniform hypergraph
- fifth direction
- Fourth elimination
- asymptotic / harmonic / analytic estimate
- descent / recursion
- global contradiction
- Legendre's conjecture / RH conclusion

既存 L052/L053/L054/L055/L059 API を consumer として使う。

---

## 10. regression / sanity

新しい大きな数値 enumeration は不要。

軽く通る場合のみ refinement sanity として theorem-level relationsを追加:

```text
FourthGateDualBase ⊆ ExactDualBase
FourthGateDualBase ⊆ PrimeAdmissible
```

既存 `paritySafeFourDirectionGate_strict_refinement_witness` は prime-level regression なので再証明不要。

---

## 11. heartbeat 方針

- normal heartbeat first。
- `ExactFourth -> witness -> L059 gate` は既存 theorem consumer のため、原則 normal heartbeat。
- `activeSupport`, cofactor, `nextSeat` を unfold しない。
- global unlimited heartbeat 禁止。
- もし optional packet の再包装だけが重ければ optional を落としてよい。

---

## 12. Outcome 分類

### Outcome A+

以下すべて:

```text
FourthGateDualBase defined
ExactFourth ⊆ FourthGateDualBase
FourthGateDualBase ⊆ ExactDualBase / PrimeAdmissible
Fourth.card <= FourthGateDualBase.card
LowCostResidual <= NearWave + L018Depth + FourthGateDualBase.card
```

### Outcome A

Fourth gated capacity と card bound は閉じるが、LowCost transport だけ engineering obstacle。

### Outcome B

ExactFourth subset gated universe のみ閉じる。

### Outcome E

既存 witness / gate theorem の elaboration surface が engineering blocker。

### Outcome C

具体的に ExactFourth member が proposed gated universe に入らない counterexample が出た場合のみ。

---

## 13. STOP

以下まで来たら停止:

```text
Fourth <= FourthGateDualBaseCapacity

LowCostResidual
  <= NearWaveBudget
   + L018DepthBudget
   + FourthGateDualBaseCapacity
```

その後の次 checkpoint で初めて、

1. NearWaveBudget 自体の finite arithmetic compression
2. FourthGateDualBase の first-prime / fourth-prime fiber refinement
3. pair-capacity 側との gap comparison

のどれを選ぶか比較する。
