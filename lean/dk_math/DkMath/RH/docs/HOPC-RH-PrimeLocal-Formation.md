# HOPC-RH 研究草稿: Prime-Local 寄与による非自明零点形成機構

Status: Working Draft (GitHub Markdown)
Scope: `DkMath.RH` + `DkMath.CFBRC` の既実装 API に基づく形式化整理
Non-claim: 本稿は RH の最終証明を主張しない

---

## Abstract

本稿は、HOPC-RH（Holo Orthogonal Phase–Curvature）で導入した位相観測量が、
「素数ごとの局所寄与（prime-local contribution）」の総和として表現される事実を、
Lean 実装済みの定理群で整理する。

中心命題は次である。

- 有限 Euler 積観測器の停留条件は
  `hopcPrimeContributionSum = 0` と同値である。
- CFBRC 側の primitive-prime existence（差冪を割り境界変数を割らない素数）を使うと、
  RH 側観測器で `stationaryAt` / `nondegenerateStationaryAt` の存在に接続できる。

これにより、非自明零点候補の形成機構に素数が構造的に関与することを、
「定義」「補題」「高位 wrapper」という形で追跡可能にする。

---

## 1. Formal Setup

### 1.1 観測器

- 局所因子: `w_p(σ,t) := exp((σ+it) log p) - 1`
- 局所位相速度寄与: `log p - phaseVel(w_p)`
- 有限和:
  `hopcPrimeContributionSum (S := S) σ t = ∑_{p∈S} (log p - phaseVel(w_p))`

### 1.2 停留・非退化停留

- `stationaryAt f t`: 位相速度が 0
- `nondegenerateStationaryAt f t`: `stationaryAt f t ∧ phaseCurv f t ≠ 0`

HOPC-RH の運用では、`arg` を主役にせず、
`phaseVel` / `phaseCurv` を直接扱う。

---

## 2. Core Formal Statements

以下は、実装済み API が与える数学的主張である。

### 2.1 停留判定の同値化（RH 層）

`w_p ≠ 0` 前提のもとで、有限 Euler 積観測器について

- `stationaryAt`
- `hopcPrimeContributionSum = 0`

が同値になる（`EulerZetaLemmas` の判定補題）。

これは「停留条件を prime-local 和の零化として読む」ための基礎である。

### 2.2 非退化化の分離（RH 層）

`nondegenerateStationaryAt_insert_of_hopcPrimeContributionSum_eq_zero_and_phaseCurv_ne_zero`
により、非退化性は

1. 寄与和零化（停留）
2. 曲率非零

の 2 入力に分離できる。
この分離が CFBRC 連携の実装設計を単純化した。

### 2.3 CFBRC から RH への witness bridge（CFBRCBridge 層）

`BoundarySide` ごとに

- `p ∣ boundaryDiffPow side d x u`
- かつ `p` が境界変数を割らない（gap 条件）

を満たす素数 witness を取り、`insert p S` 観測器へ持ち上げる wrapper が整備された。

結果として、

- `exists_stationaryAt_...`
- `exists_nondegenerateStationaryAt_...`

の存在定理群が、算術存在と位相観測を同一 API 上で接続する。

さらに RH-PF1 として、

- `exists_primeLocalFormation_insert_of_cfbRc_primitive_prime_boundary_bridge_of_local_split_and_phaseCurv`

を追加し、`stationaryAt` へ落とす前段の
「形成条件そのもの」

- `hopcPrimeContributionSum (insert p S) = 0`
- `phaseCurv(insert p S) ≠ 0`

を直接返す形式化を導入した。

続いて RH-PF2 として、

- `eventually_exists_primeLocalFormation_insert_of_cfbRc_primitive_prime_boundary_bridge_of_local_split_and_phaseCurv`

を追加し、`S` 一様の lift 仮定から
`Filter.atTop` 上の eventually 形成条件存在へ持ち上げる中間段を形式化した。

加えて RH-PF2w と RH-PF3 として、

- `eventually_exists_primeLocalFormationWitness_insert_of_cfbRc_primitive_prime_boundary_bridge_of_local_split_and_phaseCurv`
- `eventually_exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_local_split`
- `eventually_exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_local_split_and_phaseCurv`
- `eventually_exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_providerFamily`
- `eventually_exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_providerFamily_and_phaseCurvProviderFamily`
- `eventually_stationaryAt_of_cfbRc_primitive_prime_boundary_bridge_of_providerFamily`
- `hopcPrimeContributionTsum_eq_zero_of_boundaryDiffPow_factor0_with_offdvd_provider_and_providerFamily_sigma_gt_one`
- `tendsto_hopcPrimeContributionSum_atTop_of_boundaryDiffPow_factor0_with_offdvd_provider_and_providerFamily_sigma_gt_one`

を追加し、eventually 形成条件を witness 付きで回収しつつ、
`stationaryAt` / `nondegenerateStationaryAt` へ落とし込む高位 bridge を明示化した。
あわせて `eventually_exists_stationaryAt_..._of_local_split` は、
曲率仮定なし（`hS_lift` + `hsum_lift` のみ）へ前提を最小化した。
さらに PF3 provider-family から `eventually stationaryAt(S)` を回収し、
HOPC 無限側（`hopcPrimeContributionTsum` / `tendsto`）への接続補題を追加した。

---

## 3. Why Primes Are Structurally Central

本実装が示す「素数の深い寄与」は、単なる経験則ではなく以下の構造にある。

1. 観測量が最初から prime-local 和で定義される。
2. 停留判定がその和の零化と同値化される。
3. CFBRC の primitive-prime existence が witness として直接流入する。
4. witness を `insert p S` で注入すると、局所寄与の干渉条件が更新される。
5. 曲率条件を追加すると、停留候補から非退化候補へ絞り込みが可能になる。

この 1–5 が連鎖するため、「零点候補の形成機構に素数が効く」という命題は、
Lean では明示的な関数・補題・存在定理の形で確認できる。

---

## 4. API Stratification (Implemented)

同じ数学内容を、前提管理の違いで層化している。

- split/provider 層:
  - `BoundaryInsertLocalLiftProvider`
  - `BoundaryInsertPhaseCurvProvider`
  - `..._of_provider_and_phaseCurvProvider`
- 計算補題直結層:
  - `..._of_boundaryCore_factor0_and_phaseCurv`
  - `..._of_boundaryCore_local0_and_phaseCurv`
  - `..._of_boundaryDiffPow_local0_and_phaseCurv`
  - `..._of_boundaryDiffPow_factor0_and_phaseCurv`
- 前提正規化層:
  - `..._factor0_of_dvd_and_phaseCurv`
  - `..._factor0_normalized_and_phaseCurv`
  - `..._factor0_with_offdvd_and_phaseCurv`

解釈:

- `of_dvd`: 除法条件を明示入力
- `normalized`: 集合正規化で除法条件を自動化
- `with_offdvd`: 元の集合を保持し、非除法側を別 provider で補完

---

## 5. Mathematical Reading of the Current Frontier

現段階で形式化できているのは、
有限観測器上の「形成原理（formation mechanism）」である。

まだ未完なのは、次の遷移である。

- 有限 Euler 積で得た停留/非退化停留の情報を、
  無限側の零点構造へどこまで持ち上げられるか。
- `phaseCurv ≠ 0` の供給源を解析補題としてどこまで内製できるか。

従って本稿の立場は、
「RH が証明された」ではなく、
「prime-local contribution による零点形成機構を形式理論として固定した」
である。

---

## 6. Next Research Tasks

1. `phaseCurv` 供給の内製化
   - 解析仮定依存を減らし、曲率非零の計算補題を増強する。
2. finite-to-infinite 接続
   - `eventually stationary` / `tendsto` 系補題と形成原理を統合する。
3. witness/provider 分離の強化（OP-001 系）
   - off-dvd 補完と global witness 分離を更に高位 API 化する。

---

## 7. Reference Map

- 基本文書: `HOPC-RH.txt`
- 実装説明: `RH-CFBRC-HOPC.md`
- ロードマップ: `HOPC-RH-Roadmap.md`
- 未解決タスク: `HOPC-RH-OpenProblems.md`
- 履歴: `RH_Implements_History-02.md`
