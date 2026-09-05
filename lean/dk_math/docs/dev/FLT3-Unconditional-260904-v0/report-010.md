# FLT3U-010 実装報告: Sector Arithmetic Exclusion and Exact Cube Sector

## 実装範囲

`instruction-010` の FLT3U-008 checkpoint を実装した。009 の
`EisensteinCubeSectorPacket` に対して、exact second coordinate
`beta.snd = 3*A^3` と `3 ∤ B` を使い、`tau` と `tauSq` sector を有限算術で排除した。

この checkpoint では pairwise coprimality、signed factor の cube 分解、符号正規化、
小さい primitive FLT3 triple の再構成、strict descent、well-founded descent、最終
FLT3 theorem、positive-natural normalization、`NoSqOnS0` は扱っていない。

## 追加 module と import

[EisensteinSectorExclusion.lean](../../../DkMath/FLT/Three/EisensteinSectorExclusion.lean)
を追加した。直接 import は次の一つだけである。

```text
import DkMath.FLT.Three.EisensteinUnitSectors
```

FLT3 Main/Basic/Core、GEisenstein bridge、FLT5、FLT7、
`Mathlib.NumberTheory.FLT.Three` は import していない。

## Sector-specific arithmetic

trace-one convention で次を kernel-checked に追加した。

```text
eisenstein_tau_mul_cube_snd
eisenstein_tau_sq_mul_cube_snd
```

それぞれ

```text
(tau * gamma^3).snd   = r^3 + 3*r^2*s - s^3
(tau^2 * gamma^3).snd = r^3 - 3*r*s^2 - s^3
```

を与える。one sector は既存の `eisenstein_cube_snd` を再利用している。

また、`3 ∣ r-s` から `3 ∣ norm (r+s*tau)` を導く
`three_dvd_eisenstein_norm_of_three_dvd_sub` を追加した。cube 差の modulo-3
処理には `ZMod 3` を用い、`3 ∣ r^3-s^3` から `3 ∣ r-s` を得ている。

## Norm and sector exclusion

```text
EisensteinCubeSectorPacket.gamma_norm_eq_B
```

は sector representative の norm 1 と parent packet の `beta_norm = B^3` から
`norm gamma = B` を整数として証明する。cube の injectivity は odd exponent 3
で処理しており、絶対値だけの等式にはしていない。

```text
tau_sector_false
tauSq_sector_false
sector_eq_one
```

により、両 nontrivial sector では second-coordinate formula の modulo-3 条件
から `3 ∣ norm gamma`、さらに `norm gamma = B` から `3 ∣ B` が生じ、既存の
`three_not_dvd_B` と矛盾することを固定した。

## Exact cube and coordinate identities

```text
beta_eq_cube
gamma_coordinate_product_eq_A_cube
gamma_coordinate_norm_eq_B
```

を追加した。従って one sector packet から

```text
beta = gamma^3
r*s*(r+s) = A^3
r^2 + r*s + s^2 = B
```

を得られる。`EisensteinExactCubePacket` と
`eisensteinExactCubePacket_of_sectorPacket` は、sector = one、exact cube、
coordinate product、`norm gamma = B` を一つの downstream object にまとめる。

## Verification

`lean/dk_math` から次を実行した。

```text
lake build DkMath.FLT.Three.EisensteinSectorExclusion
```

focused build は `Build completed successfully (8719 jobs).` で終了した。新規
module 自身の warning はない。一方、依存グラフ中の既存
`DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:147` の `sorry` warning は
継続している。

主要定理と exact-cube packet constructor の `#print axioms` は
`propext`、`Classical.choice`、`Quot.sound` のみであり、`sorryAx` や
project-specific axiom はない。source の `sorry`、`axiom`、禁止 import、完結済み
FLT3 shortcut も監査済みである。

## Outcome

Outcome A。すべての sector packet が one sector に強制され、

```text
beta = gamma^3
r*s*(r+s) = A^3
r^2 + r*s + s^2 = B
```

が original packet の `gcd(A,B)=1` と `3 ∤ B` を保持したまま production theorem
として利用可能になった。

次の U009 gate は、`r`, `s`, `r+s` の pairwise coprimality、signed cube 分解、
小さい primitive cubic counterexample の再構成と strict decrease である。この
checkpoint ではそこへ進まず停止する。
