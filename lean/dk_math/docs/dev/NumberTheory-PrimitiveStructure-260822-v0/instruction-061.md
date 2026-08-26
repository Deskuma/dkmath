# instruction-061 — PRIM-L046 Far-Cofactor Wave Multiplicity / Actual Near-Far Residual Split

## 0. 作業先

- repository: `Deskuma/dkmath`
- branch: `wip/number-theory-primitive-structure-260822-v2`
- base HEAD at review: `9bc04faab02a8567800d35c312be8733d957d0e3`
- Lean / Mathlib: 現行 checkout (`Lean 4.32.2`) を維持する。upgrade しない。

前 checkpoint `PRIM-L045` は **Outcome A+ — EXACT COFACTOR-SUPPORT COMPLEMENT / LOCAL OWNERSHIP** として受理する。

L045 で得たもの:

```text
far residual triple (r,(q,s))
p := paritySafeCanonicalSupportPrime n r
t := paritySafeFarTripleCofactor n r q s

PrimeSupp(t) := Nat.primeFactors t

paritySafeActiveSupport n r
  = insert p (insert q (insert s PrimeSupp(t)))
```

さらに no-depth branch では

```text
PrimeSupp(t)
  = (((paritySafeActiveSupport n r).erase p).erase q).erase s
```

および fixed seat `r` 下の prime-support local injectivity まで閉じた。

L044 false beam `(62,41)/(62,83)` は、cofactor value `t=7` や returned prime `7` を seat を忘れた global injective key にできないことを示した。

今回の目的は、この非単射を **wave multiplicity** として正確に支払うことである。

核心は:

```text
same cofactor t can reappear at different seats
but every such seat r satisfies t | n^2+r
therefore r lies on squareWaveOffsets n t
```

である。

さらに fixed seat `r` では、cofactor **value** `t` が同じなら no-depth 仮定なしでも ordered residual pair `(q,s)` は一致するはずである。

従って far residual incidence は

```text
(r,(q,s)) ↦ (t,r)
```

へ単射し、その像は

```text
(t,r)
  with t in a finite first-half reduced cofactor world
       and r in squareWaveOffsets n t
```

へ入る。

これは `t` の global injectivityを主張するものではなく、noninjective reuse を既存 wave occupancy で支払う finite capacity statement である。

---

## 1. 数学的核

L043/L044 の far packet から

```text
0 < t
t < n
Nat.Coprime (2*n) t
p*q*s*t = n^2+r
```

がある。

したがって

```text
1 ≤ t
t ≤ n
Nat.Coprime (2*n) t
```

であり、また

```text
t | n^2+r
```

である。

よって `t` は canonical first-half finite world に属し、seat `r` は modulus `t` の square wave に属する。

L044 の false beam は

```text
n = 62
t = 7
r₁ = 41
r₂ = 83
```

で同じ `t` が二つの seat に現れる例だったが、実際

```text
41 ∈ squareWaveOffsets 62 7
83 ∈ squareWaveOffsets 62 7
```

となる。つまり false beam は、今回の wave budget の正しい複数 occupancy witness である。

---

## 2. 新規 module

候補:

```text
DkMath.NumberTheory.Legendre.ParitySafeFarCofactorWave
```

ファイル:

```text
lean/dk_math/DkMath/NumberTheory/Legendre/ParitySafeFarCofactorWave.lean
```

import はまず

```lean
import DkMath.NumberTheory.Legendre.ParitySafeFarTripleCofactorSupport
```

だけを使う。

facade:

```text
DkMath.NumberTheory.Legendre
```

へ新 module を import する。

---

## 3. actual near/far residual incidence split

L042 は triple-key world の near/far split を持つが、今回まず **actual residual incidence domain** を同じ境界で切る。

### L046.1 far actual incidences

```lean
noncomputable def paritySafeCanonicalFarResidualTripleIncidences
    (n : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  (paritySafeCanonicalResidualTripleIncidences n).filter
    (fun triple =>
      (paritySafeCanonicalSupportPrime n triple.1, triple.2) ∈
        paritySafeTripleGateFarTriples n)
```

同様に near 版を置く。

```lean
noncomputable def paritySafeCanonicalNearResidualTripleIncidences
    (n : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  (paritySafeCanonicalResidualTripleIncidences n).filter
    (fun triple =>
      (paritySafeCanonicalSupportPrime n triple.1, triple.2) ∈
        paritySafeTripleGateNearTriples n)
```

membership theoremを置く。

### L046.2 exact actual split

既存の

```text
paritySafeTripleGateNearFar_disjoint
paritySafeTripleGateNearFar_union
paritySafeCanonicalResidualTripleIncidence_mem_tripleGateTriples
```

を用い、

```lean
paritySafeCanonicalNearFarResidual_disjoint
paritySafeCanonicalNearFarResidual_union
```

を証明する。

その結果、L041 の exact cardinality と接続して

```lean
theorem paritySafeResidualPairMass_eq_near_add_far_card
    (n : ℕ) :
    paritySafeResidualPairMass n =
      (paritySafeCanonicalNearResidualTripleIncidences n).card +
      (paritySafeCanonicalFarResidualTripleIncidences n).card := by
  ...
```

を閉じる。

これは今回 strongly preferred。actual residual mass の near/far 分離を一度ここで固定し、以後 key-universe upper budget と actual incidence mass を混同しない。

---

## 4. cofactor value local injectivity — no depth hypothesis

L045 の support-local injectivity は no-depth branchを用いた。

今回はより強く、cofactor **値** が同じなら no-depthなしで pair が同じことを証明する。

概念形:

```lean
theorem paritySafeFarTripleCofactor_value_local_injective
    {n r q₁ s₁ q₂ s₂ : ℕ}
    (hinc₁ : (r,(q₁,s₁)) ∈ paritySafeCanonicalResidualTripleIncidences n)
    (hfar₁ : (paritySafeCanonicalSupportPrime n r,(q₁,s₁)) ∈
      paritySafeTripleGateFarTriples n)
    (hinc₂ : (r,(q₂,s₂)) ∈ paritySafeCanonicalResidualTripleIncidences n)
    (hfar₂ : (paritySafeCanonicalSupportPrime n r,(q₂,s₂)) ∈
      paritySafeTripleGateFarTriples n)
    (ht : paritySafeFarTripleCofactor n r q₁ s₁ =
      paritySafeFarTripleCofactor n r q₂ s₂) :
    q₁ = q₂ ∧ s₁ = s₂ := by
  ...
```

証明方針:

1. 両方の L043 factorization packetから

   ```text
   p*q₁*s₁*t₁ = n^2+r
   p*q₂*s₂*t₂ = n^2+r
   ```

   を得る。
2. `ht` で `t₁=t₂` とし、`0<t` と prime positivityを使って共通因子 `p` と `t` をcancelし、

   ```text
   q₁*s₁ = q₂*s₂
   ```

   を得る。
3. residual packetから `qᵢ,sᵢ` は prime、`qᵢ<sᵢ`。
4. `q₁ | q₂*s₂` を prime divisibilityで分ける。
   - `q₁=q₂` なら cancelして `s₁=s₂`。
   - `q₁=s₂` branch は ordered inequalities と product equalityで矛盾。

**重要:** この theorem に no-depth hypothesisを追加しない。数学的に不要なはずである。

もし current Nat cancellation APIだけが障害なら、局所 private lemma

```text
ordered_prime_pair_eq_of_mul_eq
```

をこの module 内に置いてよい。generic NumberTheory APIへ昇格させない。

---

## 5. finite cofactor world

L044 は `t ∈ squareAnchorCoprimeBaseOffsets n` を既に持つが、実際には `Nat.Coprime (2*n) t` まである。

今回、より正確な finite cofactor worldを置いてよい。

候補:

```lean
noncomputable def paritySafeFarCofactorBaseOffsets (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter (fun t => Nat.Coprime (2 * n) t)
```

membership:

```lean
@[simp] theorem mem_paritySafeFarCofactorBaseOffsets :
  t ∈ paritySafeFarCofactorBaseOffsets n ↔
    1 ≤ t ∧ t ≤ n ∧ Nat.Coprime (2*n) t := by
  ...
```

far packetから

```lean
theorem paritySafeFarTripleCofactor_mem_farCofactorBaseOffsets
    ... :
    paritySafeFarTripleCofactor n r q s ∈
      paritySafeFarCofactorBaseOffsets n := by
  ...
```

を置く。

`card = totient/2` 型の新しい totient 定理は今回は **非目標**。既存 API で数行なら optional だが、そのために combinatorics を増築しない。

---

## 6. cofactor wave upper incidence / budget

### L046.3 upper incidence

```lean
noncomputable def paritySafeFarCofactorWaveUpperIncidences
    (n : ℕ) : Finset (ℕ × ℕ) :=
  ((paritySafeFarCofactorBaseOffsets n).product (squareOffsets n)).filter
    (fun hit => hit.2 ∈ squareWaveOffsets n hit.1)
```

budget:

```lean
noncomputable def paritySafeFarCofactorWaveBudget (n : ℕ) : ℕ :=
  ∑ t ∈ paritySafeFarCofactorBaseOffsets n,
    (squareWaveOffsets n t).card
```

cardinality equality:

```lean
theorem paritySafeFarCofactorWaveUpperIncidences_card_eq_budget
    (n : ℕ) :
    (paritySafeFarCofactorWaveUpperIncidences n).card =
      paritySafeFarCofactorWaveBudget n := by
  ...
```

L042 の `paritySafeTripleProductWaveUpperIncidences` / budget proof patternを再利用してよい。

---

## 7. far residual incidence → `(t,r)` injection — 主定理

map:

```lean
def paritySafeFarCofactorWaveKey
    (n : ℕ) (triple : ℕ × (ℕ × ℕ)) : ℕ × ℕ :=
  (paritySafeFarTripleCofactor n triple.1 triple.2.1 triple.2.2,
    triple.1)
```

### image subset

far incidence `triple=(r,(q,s))` について:

- `t ∈ paritySafeFarCofactorBaseOffsets n`。
- `r ∈ squareOffsets n`。
- factorization `p*q*s*t=n^2+r` から `t | n^2+r`。
- よって `r ∈ squareWaveOffsets n t`。

したがって image は upper incidenceへ入る。

### injectivity

`(t₁,r₁)=(t₂,r₂)` なら

```text
r₁=r₂
t₁=t₂
```

である。seat equalityを代入後、L046.4 の cofactor-value local injectivityにより ordered pairも一致する。

これで domain triple 全体が一致する。

### cardinal bound

```lean
theorem paritySafeCanonicalFarResidualTripleIncidences_card_le_cofactorWaveBudget
    (n : ℕ) :
    (paritySafeCanonicalFarResidualTripleIncidences n).card ≤
      paritySafeFarCofactorWaveBudget n := by
  ...
```

これが今回の main finite-capacity theorem。

意味は:

```text
cofactor t is not globally unique
but its reuse multiplicity is paid by the t-wave occupancy
```

である。

---

## 8. exact wave arithmetic

既存

```text
card_squareWaveOffsets_eq_div_add_carry
```

を使い、`t>0` は finite cofactor world membershipから供給する。

```lean
theorem paritySafeFarCofactorWaveBudget_eq_div_add_carry
    (n : ℕ) :
    paritySafeFarCofactorWaveBudget n =
      ∑ t ∈ paritySafeFarCofactorBaseOffsets n,
        ((2*n) / t + squareWaveCarry n t) := by
  ...
```

ここで止める。

**今回は** この和を `O(n log n)` 的に評価したり、harmonic boundへ進めたりしない。

---

## 9. false beam を positive witnessへ戻す

L044 の arithmetic false beamを、今回の wave解釈へ接続する小 theoremを置く。

最低限:

```lean
theorem paritySafeFarCofactorWave_false_beam_62_7 :
    7 ∈ paritySafeFarCofactorBaseOffsets 62 ∧
      41 ∈ squareWaveOffsets 62 7 ∧
      83 ∈ squareWaveOffsets 62 7 := by
  ...
```

`norm_num` と membership theoremで閉じるなら追加する。

これは residual-incidence membershipを新たに証明する theoremではない。

意味は:

```text
same t = 7 at two arithmetic seats
  -> not an ownership failure
  -> both seats are exactly paid by the same 7-wave
```

という sanity check である。

---

## 10. strongly preferred: existing product-wave sideとの二重上界

今回の main theoremが軽く閉じた場合のみ、actual far residual cardinalityに既存 L042 の far product-wave upper boundも接続する。

候補:

```text
FarMass ≤ FarProductWaveBudget
FarMass ≤ FarCofactorWaveBudget
```

したがって概念的に

```text
FarMass ≤ min(FarProductWaveBudget, FarCofactorWaveBudget)
```

となる。

ただし `Nat.min` theoremを無理に作る必要はない。二本の inequality があれば十分。

既存 L042 の theoremを再利用できず、far-domain restrictionの bookkeepingが重いなら今回は省略してよい。

---

## 11. 禁止事項 / 非目標

今回は以下を行わない。

- `t` 単独の global injectivity
- cofactor prime support単独の global injectivity
- generic graph / hypergraph framework
- harmonic sum upper bound
- `O(n log n)` / PNT / analytic sieve
- smaller-anchor `SquareOffsetsFullyCovered t`
- induction / infinite descent
- residual mass の global contradiction
- Legendre conjecture の証明宣言

特に、cofactor-wave budgetが得られても、それだけで full-cover impossible とは主張しない。

---

## 12. Outcome 判定

### Outcome A — GLOBAL COFACTOR-WAVE MULTIPLICITY BUDGET

最低条件:

1. actual far residual incidence Finsetを定義。
2. no-depth不要の cofactor-value seat-local injectivityを証明。
3. finite cofactor base worldを定義し、全 far cofactorが入る。
4. `(t,r)` upper wave incidence / budgetを定義。
5. far residual incidenceから `(t,r)` への injectionを構成。
6. far residual cardinality `≤ cofactor wave budget` を証明。
7. exact `div + carry` budget formulaを証明。

### Outcome A+ — ACTUAL NEAR/FAR SPLIT + DUAL CAPACITY

Outcome A に加えて:

- actual near/far residual incidenceの disjoint union。
- `paritySafeResidualPairMass = near.card + far.card`。
- 可能なら existing far product-wave側の upper boundもactual far massへ接続。

### Outcome B — LOCAL VALUE INJECTIVITY ONLY

cofactor-value local injectivityは閉じたが、global image/codomain bookkeepingが重い場合。

この場合は injection theoremの型と障害点を reportし、generic abstractionを作らず停止する。

### Outcome C — VALUE LOCAL INJECTIVITY FAILS

同じ fixed seatで同じ positive cofactor valueを持つ異なる ordered residual pairが実際に可能、または current factorization theorem surfaceでは排除不能な場合。

この場合は具体的 false beam / missing lemmaを記録して停止する。

---

## 13. 検証

最低限:

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeFarCofactorWave
lake build DkMath.NumberTheory.Legendre
git diff --check
```

新規 source について:

```text
sorry
admit
axiom
native_decide
```

を監査する。

既存の repository-wide `sorry` は今回の判定対象外。

---

## 14. report

新規 report 候補:

```text
primitive-parity-safe-far-cofactor-wave-multiplicity-260826.md
```

必須記録:

- Outcome A/A+/B/C。
- actual near/far split の有無。
- no-depth不要の cofactor-value local injectivityが閉じたか。
- far cofactor base world の exact membership。
- far incidence → `(t,r)` injection の型。
- cofactor wave budget cardinal bound。
- exact `div + carry` formula。
- `(62,41)/(62,83)` false beamが同じ `t=7` wave occupancyとして回収できたか。
- existing product-wave sideとの dual boundを追加したか。
- global contradiction / smaller-anchor descent を主張していないこと。
