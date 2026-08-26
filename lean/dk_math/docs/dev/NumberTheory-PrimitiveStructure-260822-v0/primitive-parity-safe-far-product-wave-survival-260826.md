# PRIM-L049 実装レポート

## 判定

**Outcome A+ — UNIQUE FAR-KEY SURVIVAL / HALF-SCALE CONSUMER**

instruction-064 の bounded scope に従い、L048 の rough selector fiber を
explicit な next quotient / next seat に固定した。実装 module は

`DkMath.NumberTheory.Legendre.ParitySafeFarProductWaveSurvival`

であり、`DkMath.NumberTheory.Legendre` facade に import 済みである。

## 実装結果

### 1. next quotient / seat / shell fit

次を定義した。

```text
t₀ := n^2 / m + 1
r₀ := m*t₀ - n^2
```

対応する Lean API は
`paritySafeFarProductWaveNextQuotient`、
`paritySafeFarProductWaveNextSeat`、
`ParitySafeFarProductKeyFitsShell` である。

### 2–4. unique representative

far key の任意の wave hit について、
`paritySafeFarProductWaveCofactor_eq_nextQuotient` により cofactor が
`t₀` と一致することを証明した。

さらに
`mem_squareWaveOffsets_farKey_iff_eq_nextSeat` により、wave membership は

```text
shell fit ∧ r = r₀
```

と同値である。したがって
`squareWaveOffsets_farKey_eq_if_singleton` により wave 自体を `{r₀}` または
`∅` と exact に書き換えた。

next seat における cofactor 値についても、
`paritySafeFarProductWaveCofactor_nextSeat_eq_nextQuotient` を追加した。

### 5. explicit survival predicate

`ParitySafeFarProductKeySurvives` を定義した。内容は shell fit、
`Nat.Coprime (2*n) t₀`、および `p` より小さい active prime による
`t₀` の非除算であり、canonical support や wave membership は再導入していない。

### 6. rough fiber の exact 0/1 law

`mem_paritySafeFarProductWaveRoughOffsets_iff_survives_and_eq_nextSeat` により

```text
r ∈ roughOffsets key
  ↔ survives key ∧ r = r₀
```

を証明した。これから
`paritySafeFarProductWaveRoughOffsets_eq_if_survives` と
`paritySafeFarProductWaveRoughOffsets_card_eq_if_survives` を得て、各 fiber を
singleton または empty に固定した。

### 7. surviving far-key Finset と global count

`paritySafeSurvivingFarProductKeys` と membership simp theorem を追加した。
L048 の exact rough-fiber sum と 0/1 law を組み合わせ、

```text
FarResidual.card = survivingFarProductKeys.card
```

を `paritySafeCanonicalFarResidual_card_eq_survivingFarProductKeys_card` として
証明した。surviving key の数値評価や漸近評価は行っていない。

### 8. half-scale consumer（A+）

`paritySafeFarProductKeySurvives_nextQuotient_one_or_key_halfScale` により、
surviving key について

```text
t₀ = 1 ∨ 2*p < n+2
```

を証明した。`t₀ > 1` の場合は L048 の nontrivial cofactor floor と
L047 の `2*t < n+2` を next seat に transport している。

### 9. arithmetic sanity witnesses

`paritySafeFarProductWave_nextSeat_sanity_witnesses` に以下を `norm_num` で固定した。

```text
(n,key) = (16,(3,7,13))  → (t₀,r₀) = (1,17)
(n,key) = (62,(3,5,37))  → (t₀,r₀) = (7,41)
(n,key) = (62,(3,11,17)) → (t₀,r₀) = (7,83)
(n,key) = (17,(3,5,7))   → (t₀,r₀) = (3,26)
```

## Docstring と境界

module docstring と公開 definition/theorem の docstring に、唯一の shell
representative、rough selector の singleton/empty law、global exact count、
half-scale consumer の意味を記述した。

今回の成果は有限 shell arithmetic と exact survival count に限定している。
surviving key の asymptotic / harmonic evaluation、PNT・Mertens・analytic sieve、
generic rough-number library、hypergraph、smaller-anchor cover、induction、
global contradiction、Legendre/RH の証明は実装していない。

## 検証

以下を Lean 4.32.2 の現 checkout で実行し、いずれも exit code 0 で完了した。

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeFarProductWaveSurvival
lake build DkMath.NumberTheory.Legendre
git diff --check
```

新規 source の `sorry`、`admit`、`axiom`、`native_decide` と末尾空白を監査した。
commit、push、PR、CI は実施していない。
