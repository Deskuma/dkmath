# FLT3U-011 実装報告: Origin-Preserving Signed Cube Factorization

## 実装範囲

`instruction-011` の FLT3U-009A checkpoint を実装した。既存の
`SignedThreeAdicPacket` fields は変更せず、original triple の provenance を保持する
wrapper を追加し、その同一 packet から exact-cube chain を通して
`r`, `s`, `r+s` を pairwise-coprime な正の natural cubesへ分解した。

符号の選択、正の FLT3 triple への並べ替え、strict descent の完成、strong induction、
最終 FLT3 theorem はこの checkpoint の非対象として扱っていない。

## Provenance repair

[SignedThreeAdic.lean](../../../DkMath/FLT/Three/SignedThreeAdic.lean) に

```text
SignedThreeAdicOriginPacket
signedThreeAdicOriginPacket_of_primitive_solution
SignedThreeAdicOriginPacket.distinguished_le_product
```

を追加した。`distinguished` が original `a`, `b`, `c` のいずれかであることを
保持し、positive inputs から `distinguished ≤ a*b*c` を証明する。

plain `Nonempty` choice だけでは `SignedThreeAdicPowerSplit.packet = p` を回収でき
ないため、[SignedThreeAdicPowerSplit.lean](../../../DkMath/FLT/Three/SignedThreeAdicPowerSplit.lean)
にも `signedThreeAdicPowerSplit_with_packet` を追加した。これは既存の public
power-split type/fields を変更せず、packet equality を subtype で保持する。

## Same-origin exact-cube chain

[EisensteinDescentFactors.lean](../../../DkMath/FLT/Three/EisensteinDescentFactors.lean)
の `eisensteinDescentFactorSource_of_primitive_solution` は、次の chain を同一の
`origin.packet` から構成する。

```text
signedThreeAdicOriginPacket_of_primitive_solution
  -> signedThreeAdicPowerSplit_with_packet
  -> eisensteinRamifierStrippedPacket_of_powerSplit
  -> eisensteinConjugateCoprimePacket_of_stripped
  -> eisensteinCubeUpToUnitPacket_of_conjugateCoprime
  -> eisensteinCubeSectorPacket_of_cubeUpToUnit
  -> eisensteinExactCubePacket_of_sectorPacket
```

flattened `EisensteinDescentFactorSource` は origin、exact-cube packet、`A`, `B`,
`r`, `s`、positivity、`Nat.Coprime A B`、`3 ∤ B`、distinguished equality、

```text
r*s*(r+s) = A^3
r^2 + r*s + s^2 = B
```

を一つに保持する。

## Signed factors and cube roots

次を追加した。

```text
EisensteinDescentFactorSource.r_ne_zero
EisensteinDescentFactorSource.s_ne_zero
EisensteinDescentFactorSource.sum_ne_zero
EisensteinDescentFactorSource.abs_factor_product_eq_A_cube
EisensteinDescentFactorSource.coprime_abs_r_s
EisensteinDescentFactorSource.coprime_abs_r_sum
EisensteinDescentFactorSource.coprime_abs_s_sum
```

三つの pairwise coprimality は、共通因子を signed factors の線形結合で norm
`B` に送り、natAbs product と `A^3` にも送ったうえで `Coprime A B` を適用して
証明した。prime factorization は再実装していない。

Mathlib の `exists_eq_pow_of_mul_eq_pow` による generic split で

```text
|r| = R^3
|s| = S^3
|r+s| = T^3
```

を得て、非零性から `R`, `S`, `T` の positivity を証明した。cube の pairwise
coprimalityから `Nat.coprime_pow_left/right_iff` を使って
`Coprime R S`, `Coprime R T`, `Coprime S T` を得ている。

`EisensteinSignedCubeFactors` と
`eisensteinSignedCubeFactors_of_source`（および primitive-solution constructor）
はこれらを package 化し、cube identity と `|r||s||r+s|=A^3` から

```text
R*S*T = A
```

を保持する。

## Strict measure precursor

```text
EisensteinDescentFactorSource.source_A_lt_original_product
EisensteinSignedCubeFactors.strict_product_lt
```

を追加した。`A < 3*A*B = distinguished ≤ a*b*c` により `A < a*b*c`、さらに
`R*S*T=A` により `R*S*T < a*b*c` を kernel-checked に固定した。

## Verification

`lean/dk_math` から次を実行した。

```text
lake build DkMath.FLT.Three.SignedThreeAdic
lake build DkMath.FLT.Three.EisensteinDescentFactors
```

最終 focused build はそれぞれ `Build completed successfully (8712 jobs).`、
`Build completed successfully (8720 jobs).` で終了した。新規・変更 module 自身の
warning はない。一方、依存グラフ中の既存
`DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:147` の `sorry` warning は
継続している。

直接 import は新規 module では次の一つだけである。

```text
import DkMath.FLT.Three.EisensteinSectorExclusion
```

主要 provenance、factor、source、constructor の `#print axioms` は
`propext`、`Classical.choice`、`Quot.sound` のみであり、`sorryAx`、project-specific
axiom、FLT5/FLT7 production import、GEisenstein provisional descent dependency は
ない。source の forbidden import と `sorry`/`axiom` も監査済みである。

## Outcome

Outcome A。positive primitive solution から、同一 origin provenance を保ったまま
positive pairwise-coprime roots `R`, `S`, `T` と

```text
|r|=R^3, |s|=S^3, |r+s|=T^3, R*S*T=A< a*b*c
```

を得られる。

残る U009B gate は、`r+s` の符号関係を用いた root sign routing、positive FLT3
triple の再構成、およびその strict descent packet 化である。この checkpoint では
そこへ進まず停止する。
