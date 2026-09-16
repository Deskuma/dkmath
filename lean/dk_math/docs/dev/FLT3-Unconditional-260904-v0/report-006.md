# FLT3U-006 実装報告: Eisenstein Conjugate Coprimality

## 実装範囲

instruction-006 の FLT3U-005 checkpoint を実装した。005 の stripped packet
に対して、`beta` と `conj beta` の全共通約数が `IsUnit` であることを、
要素ベースの `EisensteinRelPrime` として証明した。

UFD/PID、ideal factorization、Bezout identity、unit/cube extraction、sector、
strict descent、最終 FLT3 定理はこの checkpoint の対象外である。

## 追加 module

[EisensteinConjugateCoprime.lean](../../../DkMath/FLT/Three/EisensteinConjugateCoprime.lean)
を追加した。実際の直接 import は次の一つだけである。

```text
import DkMath.FLT.Three.EisensteinRamifierStripped
```

指定された FLT3 Main/Basic/Core、GEisenstein bridge、FLT5 production module、
`Mathlib.NumberTheory.FLT.Three` は import していない。

## Relative-prime predicate and norm helpers

次の要素ベース relation を採用した。

```text
def EisensteinRelPrime (x y : EisensteinInt) : Prop :=
  ∀ d, d ∣ x → d ∣ y → IsUnit d
```

`eisenstein_norm_dvd_of_dvd` は `x = d * k` と norm multiplicativity から
`norm d ∣ norm x` を与える。

`eisenstein_isUnit_of_norm_eq_one` および
`eisenstein_isUnit_of_norm_eq_neg_one` は、共役を使った明示的な逆元により
norm `1`／`-1` から `IsUnit` を導く。norm の非負性により、main theorem では
`natAbs (norm d) = 1` を norm `1` に固定している。

## Conjugate difference

次を kernel-checked にした。

```text
x - conj x = eisensteinCoord (-x.snd) (2 * x.snd)
norm (x - conj x) = 3 * x.snd ^ 2
```

005 packet では `beta.snd = 3*A^3` を用いて、

```text
norm (beta - conj beta) = 27 * (A : ℤ)^6
```

を公開した。

## Coprimality argument

`powerSplit_coprime_B3_threeCube_A6` により、004A の
`Nat.Coprime A B` と `¬ 3 ∣ B` から

```text
Nat.Coprime (B ^ 3) (3 ^ 3 * A ^ 6)
```

を構成した。

共通約数 `d` が `beta` と `conj beta` を割るとき、`dvd_sub` により差も割る。
norm divisibility と `Int.dvd_natCast` により

```text
natAbs (norm d) ∣ B ^ 3
natAbs (norm d) ∣ 27 * A ^ 6
```

を得て、`Nat.eq_one_of_dvd_coprimes` から `natAbs (norm d) = 1`、さらに
`IsUnit d` を得る。これが main theorem
`beta_relPrime_conj` である。

## Packet surface

次を追加した。

- `EisensteinConjugateCoprimePacket`
- `eisensteinConjugateCoprimePacket_of_stripped`
- `eisensteinConjugateCoprimePacket_of_primitive_solution`

optional の `lambda ∤ beta` は追加していない。

## Verification

`lean/dk_math` から次を実行した。

```text
lake build DkMath.FLT.Three.EisensteinConjugateCoprime
```

focused build は `Build completed successfully (8715 jobs).` で終了した。
新規 module 自身の warning はない。一方、依存グラフ中の既存
`DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:147` の `sorry` warning
は継続している。

主要 theorem の `#print axioms` は `propext`、`Quot.sound`、必要な
`Classical.choice` のみで、`sorryAx` および project-specific axiom はない。
source の forbidden import、`sorry`、`axiom`、完結済み FLT3 shortcut も監査済みである。

## Outcome

Outcome A。すべての stripped packet `p` について、

```text
EisensteinRelPrime p.beta (conj p.beta)
```

を実装した。

U006 に残る algebraic gate は、この certificate と
`norm beta = B^3` から `beta = epsilon * gamma^3` を導く unit-times-cube
extraction である。これは本 report では実装していない。
