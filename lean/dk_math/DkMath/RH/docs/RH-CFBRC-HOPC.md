# RH: CFBRC-HOPC 実装後の形式化コードについて

## はじめに

本メモは、`DkMath.RH` と `DkMath.CFBRC` の接続実装を通して、
HOPC-RH（位相直交・停留・曲率法）の数理的骨格を整理するための記録である。

今回の実装で焦点になったのは、次の 2 点である。

1. RH 側の観測量
   `hopcPrimeContributionSum (S := S) σ t = ∑_{p∈S} (log p - phaseVel(w_p))`
   を停留判定 API として固定すること。
2. CFBRC 側の素数存在（`boundaryDiffPow` を割り、境界変数を割らない素数）を
   RH 側の有限 Euler 積観測器 `eulerZetaFinite_onVertical` の
   `stationaryAt` / `nondegenerateStationaryAt` へ橋渡しすること。

この接続により、「差冪・円分・primitive prime」の算術情報と、
「位相速度・局所寄与・曲率」の解析情報を、Lean 上で同じ関数空間に置いて扱えるようになった。

## 数学的な知見

### 1. 停留判定の中心量は `hopcPrimeContributionSum`

有限集合 `S` 上で `w_p(σ,t) ≠ 0` が成り立つとき、

- `stationaryAt (fun v => eulerZetaFinite_onVertical S σ v) t`
- `hopcPrimeContributionSum (S := S) σ t = 0`

は同値になる（実装では `EulerZetaLemmas` の判定補題）。

つまり HOPC 観測器の停留は、局所寄与の総和零化として完全に読める。
この形は prime-local 解析と算術側 existence の両方と接続しやすい。

### 2. 非退化停留は「停留 + 曲率非零」の分離で扱える

`nondegenerateStationaryAt` は定義上

- 停留（phase velocity が 0）
- 曲率非零（`phaseCurv ≠ 0`）

の組である。実装上はこの 2 条件を分離供給できるようにし、
停留供給（local-zero 由来）と曲率供給（解析補題由来）を独立に合成した。

この分離により、算術側は主に「停留」へ責務を持ち、
曲率は解析側の別補題で差し替える運用が明確化された。

### 3. CFBRC 側の本質は「候補素数の選別規則」

`BoundarySide`（right/left）ごとに
`boundaryDiffPow side d x u` を割る素数を候補とし、
同時に境界変数（right なら `x`, left なら `u`）を割らない条件を課す。

この「divide + gap」条件が、CFBRC 側の primitive-prime existence と、
RH 側の `insert p S` 観測器で必要な witness 条件を一致させる鍵になった。

### 4. 正規化経路（`of_dvd` / `normalized` / `with_offdvd`）の意味

実装で追加した高位 wrapper は、同じ数学内容を前提の持ち方だけ変えている。

- `of_dvd`: `S` 上の除法条件 `hS_dvd` を明示入力
- `normalized`: `S` を `boundaryDiffPowDvdSet` に正規化して `hS_dvd` を自動化
- `with_offdvd`: `S` を保持しつつ、非除法側を別 provider で補完

これは「対象集合の設計」を理論の外に逃がさず、
Lean の型で前提管理するための重要な整理である。

### 5. 枝問題を避ける設計原則が維持できた

`arg` を直接主役にせず、`phaseVel` と `phaseCurv` で議論を進める方針により、
複素偏角の枝選択問題を証明の中心から外せた。
HOPC-RH の「位相を微分量で観測する」設計は、
実装レベルでも有効だったと言える。

## CFBRC-HOPC の実装

実装の要点は、次の 3 層で整理できる。

1. 判定層（RH）
   - `stationaryAt_insert_of_hopcPrimeContributionSum_eq_zero`
   - `nondegenerateStationaryAt_insert_of_hopcPrimeContributionSum_eq_zero_and_phaseCurv_ne_zero`
   - `..._iff_hopcPrimeContributionSum` 系同値補題

2. 供給層（provider）
   - `BoundaryInsertLocalLiftProvider`（停留供給）
   - `BoundaryInsertPhaseCurvProvider`（曲率供給）
   - split 入力を record 化する `...Provider_of_split`

3. 橋渡し層（CFBRC bridge）
   - primitive prime existence を `insert p S` へ上げる wrapper
   - prime-local 形成条件
     (`hopcPrimeContributionSum = 0 ∧ phaseCurv ≠ 0`)
     を直接返す RH-PF1 補題
   - RH-PF1 を `Filter.atTop` の eventually 形式へ持ち上げる RH-PF2 補題
   - `boundaryCore` / `boundaryDiffPow` の計算補題版 wrapper
   - `of_dvd` / `normalized` / `with_offdvd` の高位 API

この構造により、
「算術 existence（CFBRC）」→「局所寄与零化（HOPC）」→「停留/非退化停留（RH）」の経路が
API として明示化された。

今後の直接的な発展先は次の 2 つである。

- OP-001 系（witness 分離・off-dvd 補完 provider）の研究継続
- 曲率供給を解析補題として強化し、`phaseCurv ≠ 0` の供給源を体系化する
