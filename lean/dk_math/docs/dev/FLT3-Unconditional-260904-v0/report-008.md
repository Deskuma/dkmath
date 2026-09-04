# FLT3U-008 実装報告: Coprime Cube Extraction

## 実装範囲

instruction-008 の FLT3U-006B checkpoint を実装した。007 の concrete
EuclideanDomain から GCDMonoid を導入し、006 の conjugate-coprime certificate
と `N(beta)=B^3` を Mathlib の generic coprime-power theorem に接続した。

complete unit classification、unit modulo cube sectors、epsilon elimination、
coordinate sector arithmetic、strict descent、最終 FLT3 定理は扱っていない。

## 追加 module と import

[EisensteinCubeExtraction.lean](../../../DkMath/FLT/Three/EisensteinCubeExtraction.lean)
を追加した。直接 import は次の一つだけである。

```text
import DkMath.FLT.Three.EisensteinEuclidean
```

この依存を通じて 006 の conjugate packet まで参照できる。FLT3 Main/Basic/Core、
GEisenstein bridge、FLT5、FLT7 の production module、
`Mathlib.NumberTheory.FLT.Three` は import していない。

## GCD bridge and cube identity

次の concrete GCDMonoid instance を追加した。

```text
traceOneNegOneGCDMonoid : GCDMonoid EisensteinInt
```

006 の要素ベース relation から、gcd が両因子を割ることを用いて

```text
EisensteinRelPrime x y → IsUnit (gcd x y)
```

を `isUnit_gcd_of_eisensteinRelPrime` として固定した。Bezout identity は
再証明していない。

また、`traceOne_mul_conj` と stripped packet の norm field から

```text
beta * conj beta = (B : EisensteinInt)^3
```

を `EisensteinRamifierStrippedPacket.beta_mul_conj_eq_cube` として証明した。
Nat → Int → `TraceOneInt (-1)` の埋め込みは座標 extensionality で確認している。

## Generic extraction

Mathlib の

```text
exists_associated_pow_of_mul_eq_pow
```

を実際に使用した。API の向きに合わせた associated intermediate theorem
`associated_cube_of_coprime_mul_eq_cube` を公開し、さらにその witness
`Units` を直接保持する

```text
∃ epsilon : EisensteinIntˣ, ∃ gamma : EisensteinInt,
  x = (epsilon : EisensteinInt) * gamma^3
```

を `exists_unit_mul_cube_of_coprime_mul_eq_cube` として構成した。
`Classical.choice` は existential extraction の noncomputable constructor でのみ
使用している。

## Production packet

次の packet と constructors を追加した。

```text
structure EisensteinCubeUpToUnitPacket (a b c : ℕ) where
  conjugateCoprime : EisensteinConjugateCoprimePacket a b c
  epsilon : EisensteinIntˣ
  gamma : EisensteinInt
  beta_eq : conjugateCoprime.stripped.beta =
    (epsilon : EisensteinInt) * gamma^3
```

- `eisensteinCubeUpToUnitPacket_of_conjugateCoprime`
- `eisensteinCubeUpToUnitPacket_of_primitive_solution`

により、stripped packet の `beta.snd = 3*A^3` と unit-times-cube factorization
を同時に保持する。

unit norm `N(epsilon)=1` helper は今回は追加していない。six units の完全分類や
epsilon の cube 化は U007 の対象である。

## Verification

`lean/dk_math` から次を実行した。

```text
lake build DkMath.FLT.Three.EisensteinCubeExtraction
```

focused build は `Build completed successfully (8717 jobs).` で終了した。
新規 module 自身の warning はない。一方、依存グラフ中の既存
`DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:147` の `sorry` warning
は継続している。

GCD bridge、norm cube identity、associated extractor、unit-times-cube extractor、
packet constructor の `#print axioms` は `propext`、`Classical.choice`、
`Quot.sound` のみであり、`sorryAx` や project-specific axiom はない。source の
forbidden import、`sorry`、`axiom`、完結済み FLT3 shortcut も監査済みである。

## Outcome

Outcome A。すべての conjugate-coprime packet から、

```text
beta = epsilon * gamma^3
```

を `epsilon : EisensteinIntˣ` とともに kernel-checked に抽出して packet 化した。

U007 に残る gate は Eisenstein units の modulo-cubes 分類と、それに基づく
epsilon の sector arithmetic／選別である。この checkpoint では exact cube、
sector exclusion、strict descent、最終 FLT3 定理を主張していない。
