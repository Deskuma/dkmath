# RH-CFBRC fixed Xi defect provider phase

## Overview

RH-CFBRC fixed Xi defect provider phase を続行する。

この handoff を会話コンテキストの正本とし、GitHub repository Deskuma/dkmath の
現状を最初に確認する。

PPW phase は PPW-023 complete Green で一旦終了。
現在の PPW branch は
wip/RH-CFBRC-prime-mirror-energy-260807-v0
で、handoff 作成前の verified implementation head は
58272bd1ff20e3848cbb25f7d0c4def54bcda985
(Add: PPW-023: fixed centered-Xi full second-moment defect functional)。

まずこの branch が develop へ merge 済みか確認する。
未 merge なら PPW-023 Green checkpoint として merge する。
merge 後の最新 develop から
wip/RH-CFBRC-fixed-xi-defect-provider-260812-v0
を派生して、以後は fixed Xi defect の独立 vanishing provider の証明探索へ集中する。

現在 Lean で証明済みなのは
PascalCenteredXiFixedDefectVanishesOnSafeRadii ↔ RiemannHypothesis
である。
RH 自体はまだ証明していない。

未解決の本体は
PascalCenteredXiFixedDefectVanishesOnSafeRadii
そのものを、RH を使わずに構成すること。

既存 Core として safe radius R では
0 ≤ pascalCenteredXiFixedSecondMomentDefectFunctional R
がある。
したがって独立に
pascalCenteredXiFixedSecondMomentDefectFunctional R ≤ 0
を出せれば vanishing が閉じる。

Prime / explicit formula、CF2D / ThreeElement、centered Xi symmetry / moment identity
の三候補を監査するが、RH-equivalent condition の名前替えを provider と呼んではならない。

既存 Green 層を再実装しない。
同じ scalar defect を independently constrain する theorem だけを探す。

## Handoff docs

handoff

- [symlink](./handoff-2026-08-12.md)
- [original](../RH-CFBRC-prime-mirror-energy/RH-CFBRC-PPW-phase-close-fixed-Xi-defect-provider-handoff-2026-08-12.md)
