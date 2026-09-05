# FLT3U-005 実装報告: Eisenstein Ramifier Stripping

## 実装範囲

instruction-005 の 004B checkpoint として、004A の
`SignedThreeAdicPowerSplit` から ramifier
`eisensteinRamifier = 1 + eisensteinTau` を一回だけ除去した。
UFD/PID、共役 coprimality、unit times cube extraction、strict descent は扱っていない。

## 追加 module

[EisensteinRamifierStripped.lean](../../../DkMath/FLT/Three/EisensteinRamifierStripped.lean)
を追加した。直接 import は次の一つだけである。

```text
import DkMath.FLT.Three.SignedThreeAdicPowerSplit
```

指定された FLT3 Main/Basic/Core、GEisenstein bridge、FLT5 production module、
`Mathlib.NumberTheory.FLT.Three` は import していない。

## Coordinate construction

`lambda = (1,1)` に対する multiplication theorem
`eisenstein_ramifier_mul_coord` を追加し、

```text
lambda * (u,v) = (u-v, u+2*v)
```

を kernel-checked にした。

power split `s` から、truncated subtraction を使わずに

```text
v := 3 * (s.A : ℤ)^3
u := s.packet.alpha.fst + v
beta := (u,v)
```

として `eisensteinRamifierStrippedBeta` を定義した。
004A の `carrier = 9*A^3` と signed gap から
`alpha.snd = alpha.fst + 9*A^3` を導き、座標 extensionality により

```text
alpha = eisensteinRamifier * beta
```

を証明した。

## Production packet

次の surface を追加した。

```text
structure EisensteinRamifierStrippedPacket (a b c : ℕ) : Type where
  powerSplit : SignedThreeAdicPowerSplit a b c
  beta : EisensteinInt
  alpha_eq : powerSplit.packet.alpha = eisensteinRamifier * beta
  beta_norm : norm beta = (powerSplit.B : ℤ)^3
  beta_snd : beta.snd = 3 * (powerSplit.A : ℤ)^3
```

`beta_norm` は `N(lambda)=3`、004A の
`residual = 3*B^3`、および norm multiplicativity から導出した。
`eisensteinRamifierStrippedPacket_beta_snd_pos` により beta の第二座標の正性も
整数上で利用できる。

`three_not_dvd_B` は power split の既存 field から theorem wrapper
`eisensteinRamifierStrippedPacket_three_not_dvd_B` として公開した。

## Public constructors

- `eisensteinRamifierStrippedPacket_of_powerSplit`
- `eisensteinRamifierStrippedPacket_of_primitive_solution`
- `eisensteinRamifierStrippedPacket_beta_snd`
- `eisensteinRamifierStrippedPacket_beta_snd_pos`
- `eisensteinRamifierStrippedPacket_three_not_dvd_B`

## Verification

`lean/dk_math` から次を実行した。

```text
lake build DkMath.FLT.Three.EisensteinRamifierStripped
git diff --check
```

focused build は `Build completed successfully (8714 jobs).` で終了した。
新規 module 自身に warning はないが、依存グラフ中の既存
`DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:147` の `sorry` warning
は継続している。

主要 theorem の `#print axioms` は `eisenstein_ramifier_mul_coord` と
`beta_snd` で `[propext, Quot.sound]`／`[propext]`、constructor で
`[propext, Classical.choice, Quot.sound]` のみであり、`sorryAx` は含まれない。
新規 source に `sorry`、`axiom`、完結済み FLT3 shortcut はない。

## Outcome

004A の exact power split から、ramifier を exactly 一回取り除いた production
packet を構成できる。終端条件

```text
alpha = lambda * beta
N(beta) = B^3
beta.snd = 3*A^3
```

を満たす。次段の共役 coprimality、unit/cube classification、sector、strict
descent、最終 FLT3 定理は未実装であり、この checkpoint の non-goal として残した。
