# HOPC-RH Glossary

`DkMath.RH` で使う主要語彙を、実装名ベースで簡潔に整理する。

## 使い方

- 「定義」: `.lean` で実際に `def` されている語彙
- 「補題」: 定義同士の関係を与える API
- 「依存」: その語彙が参照している主要概念

## Core（位相ドリフト骨格）

### `vertical`（定義）

- 実装: `Defs.lean`
- 型: `ℝ → ℝ → ℂ`
- 意味: 縦線 `s = σ + i t`
- 依存: 複素数の実埋め込み

### `torque`（定義）

- 実装: `Defs.lean`
- 型: `ℂ → ℂ → ℝ`
- 意味: 位相変化の分子 `Re(z)Im(dz) - Im(z)Re(dz)`
- 依存: `Complex.re`, `Complex.im`

### `phaseVel`（定義）

- 実装: `Defs.lean`
- 型: `(ℝ → ℂ) → ℝ → ℝ`
- 意味: 位相速度 `Im((f'(t))/f(t))`
- 依存: `deriv`, 複素除算

### `driftFreeAt`（定義）

- 実装: `Defs.lean`
- 型: `(ℝ → ℂ) → ℝ → Prop`
- 意味: 点 `t` で位相ドリフトが消失している条件
- 依存: `torque`, `deriv`

### `phaseCurv`（定義）

- 実装: `Defs.lean`
- 型: `(ℝ → ℂ) → ℝ → ℝ`
- 意味: 位相速度の 1 次導関数（曲率様量）
- 依存: `phaseVel`, `deriv`

### `stationaryAt` / `nondegenerateStationaryAt`（定義）

- 実装: `Defs.lean`
- 意味:
  - `stationaryAt`: `phaseVel = 0`
  - `nondegenerateStationaryAt`: `stationaryAt ∧ phaseCurv ≠ 0`
- 依存: `phaseVel`, `phaseCurv`

## Euler 因子・局所寄与

### `eulerZeta_exp_s_log_p_sub_one`（定義）

- 実装: `EulerZeta.lean`
- 型: `ℕ → ℝ → ℝ → ℂ`
- 意味: `w_p(σ,t) = exp((σ+it)log p) - 1`
- 依存: `vertical`, `Complex.exp`, `Real.log`

### `eulerZetaPhaseVelLocal`（定義）

- 実装: `EulerZeta.lean`
- 型: `ℕ → ℝ → ℝ → ℝ`
- 意味: `w_p` への `phaseVel` 適用値
- 依存: `phaseVel`, `eulerZeta_exp_s_log_p_sub_one`

### `eulerZetaFactorPhaseVelFinite`（定義）

- 実装: `EulerZeta.lean`
- 型: `Finset {p // Nat.Prime p} → ℝ → ℝ → ℝ`
- 意味: 因子局所位相速度の有限和
- 依存: `eulerZetaFactorPhaseVelLocal`, `Finset.sum`

## HOPC 公開名（CFBRC 導線）

### `hopcPrimeLocalContribution`（定義）

- 実装: `EulerZeta.lean`
- 型: `ℕ → ℝ → ℝ → ℝ`
- 意味: `log p - phaseVel(w_p)`
- 依存: `Real.log`, `eulerZetaPhaseVelLocal`

### `hopcPrimeContributionSum`（定義）

- 実装: `EulerZeta.lean`
- 型: `Finset {p // Nat.Prime p} → ℝ → ℝ → ℝ`
- 意味: HOPC 局所寄与の有限和
- 依存: `hopcPrimeLocalContribution`, `Finset.sum`

### `eulerZetaFactorPhaseVelFinite_eq_hopcPrimeContributionSum`（補題）

- 実装: `EulerZetaLemmas.lean`
- 意味: 既存因子位相速度和と HOPC 公開和の同一化
- 依存: `phaseVel_eulerZetaFactorVerticalExp_eq_log_sub_phaseVelLocal`

### 停留判定 wrapper（補題）

- 実装: `EulerZetaLemmas.lean`
- 補題:
  - `driftFreeAt_eulerZetaFinite_onVertical_iff_hopcPrimeContributionSum_eq_zero`
  - `stationaryAt_eulerZetaFinite_onVertical_iff_hopcPrimeContributionSum_eq_zero`
  - `nondegenerateStationaryAt_eulerZetaFinite_onVertical_iff_hopcPrimeContributionSum`
- 意味: `eulerZetaFinite_onVertical` の停留/非退化停留を
  `hopcPrimeContributionSum` の零化条件で判定する API

## OP-004（曲率供給）語彙

### `BoundaryInsertPhaseCurvProvider`（定義）

- 実装: `CFBRCBridge.lean`
- 型: `BoundarySide → Finset prime → d x u σ t → Type`
- 意味: `insert p S` 観測器に対する `phaseCurv ≠ 0` 供給 record
- 依存: `phaseCurv`, `eulerZetaFinite_onVertical`, `boundaryDiffPow`

### `boundaryInsertPhaseCurvProvider_of_split`（補題）

- 実装: `CFBRCBridge.lean`
- 意味: split 形式の `hcurv_lift` から provider record を構成する最小 wrapper

### nondegenerate bridge 群（補題）

- 実装: `CFBRCBridge.lean`
- 補題:
  - `exists_nondegenerateStationaryAt_singleton_of_cfbRc_primitive_prime_boundary_bridge_of_local_and_phaseCurv`
  - `exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_local_split_and_phaseCurv`
  - `exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_provider_and_phaseCurvProvider`
- 意味:
  - `stationaryAt` bridge に曲率非零供給を合成し、
    `nondegenerateStationaryAt` の存在へ接続する。

## 注意（前提）

- 多くの停留判定補題は `∀ p ∈ S, w_p(σ,t) ≠ 0` を仮定する。
- これは `phaseVel` の 0 除算回避と微分可能性を確保するための前提。

## 関連文書

- 方針: `HOPC-RH.txt`
- ロードマップ: `HOPC-RH-Roadmap.md`
- 議論: `RH-CFBRC-Discussion.md`
- 実装履歴: `RH_Implements_History-01.md`
