# PRIM-L046 report — parity-safe far-cofactor wave multiplicity

## Outcome

**Outcome A+ — ACTUAL NEAR/FAR SPLIT / LOCAL COFACTOR-WAVE BUDGET**

L045 の exact cofactor support complement を、同じ cofactor 値が複数の seat に現れる
可能性を含む finite wave multiplicity bookkeeping へ拡張した。far residual incidence は
`(t,r)`、すなわち cofactor `t` と seat `r` に送られ、固定 seat では cofactor 値の一致が
ordered residual pair の一致を強制する。

これは actual residual mass の near/far 分割と、cofactor wave の有限上界である。
cofactor `t` の global injectivity、調和和評価、smaller-anchor cover、Legendre の証明は
この checkpoint の帰結ではない。

## 実装

追加 module:

```text
DkMath.NumberTheory.Legendre.ParitySafeFarCofactorWave
```

facade `DkMath.NumberTheory.Legendre` から import した。

主な theorem surface:

- `paritySafeCanonicalFarResidualTripleIncidences`
  と `paritySafeCanonicalNearResidualTripleIncidences`

  実在する canonical residual triple incidences を、canonical triple key の
  `paritySafeTripleGateFarTriples` / `paritySafeTripleGateNearTriples` membership で
  filter した actual near/far 集合。両方の simp membership theorem、disjointness、union
  を追加した。

- `paritySafeResidualPairMass_eq_near_add_far_card`

  L045 の residual pair mass を exact に
  `near.card + far.card` へ分解する。

- `paritySafeFarTripleCofactor_value_local_injective`

  同じ `n,r` にある二つの residual/far incidencesについて、cofactor 値が等しければ
  `q₁ * s₁ = q₂ * s₂` を得る。active prime 性、`q < s`、素数の divisibility を使い、
  ordered pair の equality `q₁ = q₂ ∧ s₁ = s₂` を no-depth hypothesis なしで証明した。

- `paritySafeFarCofactorBaseOffsets`
  と `mem_paritySafeFarCofactorBaseOffsets`

  `1 ≤ t ≤ n` かつ `Nat.Coprime (2*n) t` の finite cofactor world を定義した。
  `paritySafeFarTripleCofactor_mem_farCofactorBaseOffsets` により、far packet の実 cofactor
  がこの世界に入ることを示した。

- `paritySafeFarCofactorWaveUpperIncidences`
  と `paritySafeFarCofactorWaveBudget`

  `(t,r)` の upper incidence を
  `t ∈ baseOffsets n`、`r ∈ squareOffsets n`、`r ∈ squareWaveOffsets n t`
  で定義し、その card が cofactor wave budget の和に等しいことを証明した。

- `paritySafeCanonicalFarResidualTripleIncidences_card_le_cofactorWaveBudget`

  far residual incidence を `(t,r)` key へ写す map の image が upper incidence 集合に
  入ることを示した。上記 fixed-seat local injectivity により image map は injective で、
  actual far residual card が wave budget 以下となる。

- `paritySafeFarCofactorWaveBudget_eq_div_add_carry`

  各 wave の occupancy を、既存の square-wave arithmetic により
  `(2*n)/t + squareWaveCarry n t` として exact に展開した。

- `paritySafeFarCofactorWave_false_beam_62_7`

  L044 の beam を `7 ∈ baseOffsets 62`、`41 ∈ squareWaveOffsets 62 7`、
  `83 ∈ squareWaveOffsets 62 7` として固定した。同一 cofactor 値が複数 seat に再現する
  ため、cofactor 単独の global injective charge は得られない。

## judgment

1. actual near/far residual split は exact か。**Yes**。
2. residual pair mass は near/far card の和に分解できるか。**Yes**。
3. 固定 seat の equal-cofactor local injectivity は no-depth で成立するか。**Yes**。
4. far cofactor は finite same-anchor world に入るか。**Yes**。
5. actual far residual card を cofactor wave budget で上から抑えられるか。**Yes**。
6. wave budget を division plus carry へ exact に展開できるか。**Yes**。
7. cofactor `t` の global injectivity は得られたか。**No**。`(62,41)` と `(62,83)` の
   false beam が同じ `t = 7` の異なる seat を示す。
8. dual product-wave bound は追加したか。**No**。instruction-061 で optional とされた
   bookkeeping であり、今回の actual split と single-wave upper budget の受理に不要なため
   境界外に置いた。

## 境界

追加していないものは、cofactor の global injectivity、harmonic / `O(n log n)` 評価、
PNT・sieve、smaller-anchor `SquareOffsetsFullyCovered t`、descent、contradiction、
Legendre 予想、RH である。

従って今回の形式的な帰結は、

```text
actual residual mass
  = near residual card + far residual card
far residual incidence
  -> fixed-seat injective (cofactor, seat) key
  -> finite cofactor square-wave upper budget
  = sum ((2*n)/t + squareWaveCarry n t)
```

までで閉じる。

## 検証

Lean 4.32.2 の現行 checkoutで次を実行し、いずれも成功した。

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeFarCofactorWave
lake build DkMath.NumberTheory.Legendre
git diff --check
```

新規 source について `sorry`、`admit`、`axiom`、`native_decide` および末尾空白を監査した。
full repository build、commit、push、PR、CI は今回の依頼範囲に含めていない。
