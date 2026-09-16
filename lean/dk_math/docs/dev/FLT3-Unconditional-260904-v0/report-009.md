# FLT3U-009 実装報告: Eisenstein Unit Classes Modulo Cubes

## 実装範囲

`instruction-009` の FLT3U-007 checkpoint を実装した。trace-one convention の
Eisenstein 整数について、norm-one 元の完全な六元分類を証明し、符号を
`tau ^ 3 = -1` で cube factor に吸収して、unit を三つの sector のいずれかに
正規化する API を追加した。

この checkpoint では sector の排除、`beta` の exact cube 化、座標因数分解、
pairwise coprimality、strict descent、最終 FLT3 定理、`NoSqOnS0` は扱っていない。

## 追加 module と import

[EisensteinUnitSectors.lean](../../../DkMath/FLT/Three/EisensteinUnitSectors.lean)
を追加した。直接 import は次の一つだけである。

```text
import DkMath.FLT.Three.EisensteinCubeExtraction
```

FLT3 Main/Basic/Core、GEisenstein bridge、FLT5、FLT7、`Mathlib.NumberTheory.FLT.Three`
は import していない。source の `sorry`、`axiom`、完結済み FLT3 shortcut と、
指定された forbidden import も監査済みである。

## Unit classification

次の定理を追加した。

```text
eisenstein_isUnit_iff_norm_eq_one
eisenstein_norm_eq_one_iff_coords
eisenstein_norm_eq_one_iff_six_units
eisensteinUnit_cases
```

`norm x = 1` の座標を厳密に

```text
(1, 0), (-1, 0), (0, 1), (0, -1), (-1, 1), (1, -1)
```

へ分類し、それを
`1`, `-1`, `eisensteinTau`, `-eisensteinTau`, `eisensteinTau ^ 2`,
`-(eisensteinTau ^ 2)` の六元分類へ接続した。Units-facing theorem
`eisensteinUnit_cases` は `epsilon : EisensteinIntˣ` に対して同じ分類を公開する。

さらに

```text
tau_mul_cube_absorbs_neg
```

で `(eisensteinTau * gamma)^3 = -(gamma^3)` を固定した。

## Unit sectors and normalization

三つの代表元を持つ

```text
inductive EisensteinUnitSector
  | one | tau | tauSq
```

と `EisensteinUnitSector.rep` を追加した。各代表について
`EisensteinUnitSector.rep_norm` と `EisensteinUnitSector.rep_isUnit` を証明した。

```text
exists_sector_mul_cube_of_unit
```

は任意の unit を `sector.rep * delta^3` に分解し、`delta` が unit であることも
保持する。sector の一意性は要求していない。

## Production packet

`EisensteinCubeSectorPacket` は 008 の
`EisensteinCubeUpToUnitPacket`、選択した sector、調整後の `gamma`、および

```text
beta = sector.rep * gamma^3
```

を同時に保持する。noncomputable constructor
`eisensteinCubeSectorPacket_of_cubeUpToUnit` により、すべての cube-up-to-unit
packet を三 sector のいずれかへ正規化できる。元の packet が保持する
`beta.snd = 3 * A^3` も親 packet を通じて保持される。

## Verification

`lean/dk_math` から次を実行した。

```text
lake build DkMath.FLT.Three.EisensteinUnitSectors
```

focused build は `Build completed successfully (8718 jobs).` で終了し、新規 module
自身の warning はない。依存グラフ中の既存
`DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:147` の `sorry` warning は
継続している。

主要定理と constructor の `#print axioms` はすべて
`propext`、`Classical.choice`、`Quot.sound` のみであり、`sorryAx` や
project-specific axiom はない。

## Outcome

Outcome A。すべての cube-up-to-unit packet から、

```text
beta = rho * gamma^3
```

を `rho` が `1`, `eisensteinTau`, `eisensteinTau ^ 2` のいずれかであることと
ともに kernel-checked に抽出できるようになった。

次の U008 gate は、sector-specific な `beta.snd = 3 * A^3` と `3 ∤ B` を使って
`tau` および `tauSq` sector を排除することである。この報告の範囲ではその排除や
exact cube、descent、最終 FLT3 閉包を主張していない。
