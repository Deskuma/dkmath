# DkMath.RH

`DkMath.RH` は、Riemann Hypothesis 周辺の解析を
「prime-local contribution（素数ごとの局所寄与）」で観測するための Lean モジュール群です。

ここでの実装目標は、RH の即時証明主張ではなく、次を機械検証可能な API として整備することです。

- 位相ドリフト骨格（`phaseVel`, `driftFreeAt`, `phaseCurv`）
- Euler 因子の局所観測（`w_p`, factor phase velocity）
- 有限 Euler 積での停留・非退化停留判定
- CFBRC と接続可能な HOPC 観測量（寄与総和）公開

## 入口

- 実装トップ: `DkMath/RH.lean`
- 詳細解説（長文）: `DkMath/RH/docs/README.md`
- 方針文書: `DkMath/RH/docs/HOPC-RH.txt`
- ロードマップ: `DkMath/RH/docs/HOPC-RH-Roadmap.md`
- 用語集: `DkMath/RH/docs/HOPC-RH-Glossary.md`
- 未解決タスク: `DkMath/RH/docs/HOPC-RH-OpenProblems.md`
- CFBRC 連携議論: `DkMath/RH/docs/RH-CFBRC-Discussion.md`
- 実装履歴: `DkMath/RH/docs/RH_Implements_History.md`

## ファイル構成（実装）

- `Defs.lean`
  - `vertical`, `torque`, `phaseVel`, `phaseUnwrap`, `driftFreeAt`, `phaseCurv`
- `Lemmas.lean`
  - 位相速度の代数公式、積・商・逆数法則、停留同値
- `Theorems.lean`
  - `phaseUnwrap` の微分に関する基礎定理
- `EulerZeta.lean`
  - Euler 因子 / 有限積 / 局所位相寄与
  - HOPC 公開定義:
    - `hopcPrimeLocalContribution`
    - `hopcPrimeContributionSum`
- `EulerZetaLemmas.lean`
  - 単一素数因子の導関数・位相速度
  - 有限積の積→和補題
  - `driftFreeAt` / `stationaryAt` / `nondegenerateStationaryAt` と
    HOPC 寄与総和の同値
- `EulerZetaConvergence.lean`
  - `σ > 1` での magnitude 無限積収束と正値
- `CFBRCBridge.lean`
  - CFBRC の primitive-prime existence から RH 側 singleton 停留判定へ接続する bridge

## 主要 API（RH-N23 時点）

- HOPC 観測量:
  - `hopcPrimeLocalContribution p σ t`
  - `hopcPrimeContributionSum S σ t`
- 停留判定（有限 Euler 積）:
  - `driftFreeAt_eulerZetaFinite_onVertical_iff_hopcPrimeContributionSum_eq_zero`
  - `stationaryAt_eulerZetaFinite_onVertical_iff_hopcPrimeContributionSum_eq_zero`
  - `nondegenerateStationaryAt_eulerZetaFinite_onVertical_iff_hopcPrimeContributionSum`
- CFBRC 連携 bridge（singleton）:
  - `exists_stationaryAt_singleton_of_cfbRc_primitive_prime_bridge`（global 仮定版）
  - `exists_stationaryAt_singleton_of_cfbRc_primitive_prime_bridge_of_local`（local 仮定版）
- CFBRC 連携 bridge（small finite-set）:
  - `stationaryAt_insert_of_hopcPrimeContributionSum_eq_zero`
  - `exists_stationaryAt_insert_of_cfbRc_primitive_prime_bridge_of_local`
  - `exists_stationaryAt_insert_of_cfbRc_primitive_prime_bridge_of_local_split`
- CFBRC 連携 bridge（`BoundarySide` 統一）:
  - `exists_stationaryAt_singleton_of_cfbRc_primitive_prime_boundary_bridge_of_local`
  - `exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_local`
  - `exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_local_split`
  - `BoundaryInsertLocalLiftProvider`
  - `exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_provider`
  - `boundary_hS_lift_of_nonzero_on_S_and_witness`
  - `boundaryInsertLocalLiftProvider_of_nonzero_on_S_and_witness`
  - `boundary_hsum_lift_of_local_zero_on_S_and_witness`
  - `boundaryInsertLocalLiftProvider_of_nonzero_and_local_zero_on_S_and_witness`
  - `boundary_nonzero_on_S_of_boundary_dvd_and_gap`
  - `boundary_hwnz_witness_of_boundaryCore_nonzero`
  - `boundary_local_zero_on_S_of_boundary_dvd_and_gap`
  - `boundary_hlocal_witness_of_boundaryCore_local_zero`
  - `boundaryInsertLocalLiftProvider_of_boundary_dvd_and_gap`
  - `boundaryInsertLocalLiftProvider_of_boundary_dvd_and_gap_of_boundaryCore_witness`
  - `hopcPrimeLocalContribution_eq_eulerZetaFactorPhaseVelLocal_of_nonzero`
  - `hopcPrimeLocalContribution_eq_zero_of_factorPhaseVelLocal_eq_zero_of_nonzero`
  - `boundary_hlocal_core_of_boundaryCore_factorPhaseVelLocal_eq_zero`
  - `boundaryInsertLocalLiftProvider_of_boundary_dvd_gap_of_boundaryCore_factor0`
  - `boundaryInsertLocalLiftProvider_of_boundary_dvd_and_gap_and_local_zero`

## 利用例（import）

```lean
import DkMath.RH

open DkMath.RH.EulerZeta
```

必要最小だけ使う場合:

```lean
import DkMath.RH.EulerZeta
import DkMath.RH.EulerZetaLemmas
```

CFBRC 連携 bridge まで使う場合:

```lean
import DkMath.RH.CFBRCBridge

open DkMath.RH.EulerZeta
```

`BoundarySide` 高位 API（split 仮定）を使う最小テンプレート:

```lean
import DkMath.RH.CFBRCBridge

open DkMath.RH.EulerZeta

-- side : DkMath.CFBRC.BoundarySide
-- hpnd : match side with | .right => ¬ d ∣ x | .left => ¬ d ∣ u
-- hS_lift / hsum_lift は insert p S 上の仮定供給器
example (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : match side with
      | .right => ¬ d ∣ x
      | .left => ¬ d ∣ u)
    (hS_lift :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          (match side with | .right => ¬ p.1 ∣ x | .left => ¬ p.1 ∣ u) →
          ∀ r ∈ (insert p S), eulerZeta_exp_s_log_p_sub_one r.1 σ t ≠ 0)
    (hsum_lift :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          (match side with | .right => ¬ p.1 ∣ x | .left => ¬ p.1 ∣ u) →
          hopcPrimeContributionSum (S := insert p S) σ t = 0) :
    ∃ p : {q // Nat.Prime q},
      DkMath.RH.stationaryAt
        (fun v : ℝ => eulerZetaFinite_onVertical (insert p S) σ v) t := by
  exact
    exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_local_split
      (side := side) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
      hd_prime hd_ge hx hu hcop hpnd hS_lift hsum_lift
```

`BoundaryInsertLocalLiftProvider` を使う最小テンプレート:

```lean
import DkMath.RH.CFBRCBridge

open DkMath.RH.EulerZeta

example (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : match side with
      | .right => ¬ d ∣ x
      | .left => ¬ d ∣ u)
    (provider : BoundaryInsertLocalLiftProvider side S d x u σ t) :
    ∃ p : {q // Nat.Prime q},
      DkMath.RH.stationaryAt
        (fun v : ℝ => eulerZetaFinite_onVertical (insert p S) σ v) t := by
  exact
    exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_provider
      (side := side) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
      hd_prime hd_ge hx hu hcop hpnd provider
```

段階供給（RH-N12/N13）から provider を生成するテンプレート:

```lean
import DkMath.RH.CFBRCBridge

open DkMath.RH.EulerZeta

example (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hS_nonzero :
      ∀ r ∈ S, eulerZeta_exp_s_log_p_sub_one r.1 σ t ≠ 0)
    (hwnz_witness :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          (match side with | .right => ¬ p.1 ∣ x | .left => ¬ p.1 ∣ u) →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hS_local0 :
      ∀ r ∈ S, hopcPrimeLocalContribution r.1 σ t = 0)
    (hlocal_witness :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          (match side with | .right => ¬ p.1 ∣ x | .left => ¬ p.1 ∣ u) →
          hopcPrimeLocalContribution p.1 σ t = 0) :
    BoundaryInsertLocalLiftProvider side S d x u σ t := by
  exact
    boundaryInsertLocalLiftProvider_of_nonzero_and_local_zero_on_S_and_witness
      (side := side) (S := S)
      (hS_nonzero := hS_nonzero)
      (hwnz_witness := hwnz_witness)
      (hS_local0 := hS_local0)
      (hlocal_witness := hlocal_witness)
```

`boundary_dvd + gap` 供給（RH-N21 前提簡約版）から provider を生成するテンプレート:

```lean
import DkMath.RH.CFBRCBridge

open DkMath.RH.EulerZeta

example (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hS_dvd :
      ∀ r ∈ S, r.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u)
    (hS_gap :
      ∀ r ∈ S, (match side with | .right => ¬ r.1 ∣ x | .left => ¬ r.1 ∣ u))
    (hwnz_witness :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          (match side with | .right => ¬ p.1 ∣ x | .left => ¬ p.1 ∣ u) →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hlocal_witness :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          (match side with | .right => ¬ p.1 ∣ x | .left => ¬ p.1 ∣ u) →
          hopcPrimeLocalContribution p.1 σ t = 0) :
    BoundaryInsertLocalLiftProvider side S d x u σ t := by
  exact
    boundaryInsertLocalLiftProvider_of_boundary_dvd_and_gap
      (side := side) (S := S)
      (hS_dvd := hS_dvd)
      (hS_gap := hS_gap)
      (hwnz_witness := hwnz_witness)
      (hlocal_witness := hlocal_witness)
```

`boundaryCore` 側 witness 仮定（RH-N22）から provider を生成するテンプレート:

```lean
import DkMath.RH.CFBRCBridge

open DkMath.RH.EulerZeta

example (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hS_dvd :
      ∀ r ∈ S, r.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u)
    (hS_gap :
      ∀ r ∈ S, (match side with | .right => ¬ r.1 ∣ x | .left => ¬ r.1 ∣ u))
    (hwnz_core :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hlocal_core :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
          hopcPrimeLocalContribution p.1 σ t = 0) :
    BoundaryInsertLocalLiftProvider side S d x u σ t := by
  exact
    boundaryInsertLocalLiftProvider_of_boundary_dvd_and_gap_of_boundaryCore_witness
      (side := side) (S := S)
      (hS_dvd := hS_dvd)
      (hS_gap := hS_gap)
      (hwnz_core := hwnz_core)
      (hlocal_core := hlocal_core)
```

`boundaryCore` 上の factor 位相速度ゼロ仮定（RH-N23）から provider を生成するテンプレート:

```lean
import DkMath.RH.CFBRCBridge

open DkMath.RH.EulerZeta

example (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hS_dvd :
      ∀ r ∈ S, r.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u)
    (hS_gap :
      ∀ r ∈ S, (match side with | .right => ¬ r.1 ∣ x | .left => ¬ r.1 ∣ u))
    (hwnz_core :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hfactor_core0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
          eulerZetaFactorPhaseVelLocal p.1 σ t = 0) :
    BoundaryInsertLocalLiftProvider side S d x u σ t := by
  exact
    boundaryInsertLocalLiftProvider_of_boundary_dvd_gap_of_boundaryCore_factor0
      (side := side) (S := S)
      (hS_dvd := hS_dvd)
      (hS_gap := hS_gap)
      (hwnz_core := hwnz_core)
      (hfactor_core0 := hfactor_core0)
```

## 注意

- 本層は「観測器 API の整備」を主目的とし、RH の完全証明を主張しません。
- `arg` の枝問題は避け、`phaseVel` / `phaseUnwrap` 中心で整理します。
