 /-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CFBRC.Bridge
import DkMath.RH.HopcInfiniteLift
import DkMath.RH.EulerZetaLemmas

set_option linter.style.longLine false

/-!
# RH-CFBRC Bridge

CFBRC 側で得た primitive-prime existence を、RH 側の
`hopcPrimeContributionSum` 判定へ接続する最小 bridge。
-/

namespace DkMath.RH.EulerZeta

open scoped Topology

/--
CFBRC の primitive-prime existence（right boundary）から、
RH 側の singleton 観測器の停留点存在へ接続する bridge。

`hwnz` と `hhopc0` は「CFBRC で得た素数を RH 観測へ解釈する」翻訳仮定。
-/
theorem exists_stationaryAt_singleton_of_cfbRc_primitive_prime_bridge
    {d x u : ℕ} {σ t : ℝ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : ¬ d ∣ x)
    (hwnz :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ ((x + u) ^ d - u ^ d) → ¬ p.1 ∣ x →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hhopc0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ ((x + u) ^ d - u ^ d) → ¬ p.1 ∣ x →
          hopcPrimeContributionSum (S := ({p} : Finset {q // Nat.Prime q})) σ t = 0) :
    ∃ p : {q // Nat.Prime q},
      DkMath.RH.stationaryAt
        (fun v : ℝ =>
          eulerZetaFinite_onVertical ({p} : Finset {q // Nat.Prime q}) σ v) t := by
  rcases DkMath.CFBRC.exists_primitive_prime_factor_sub_pow_of_prime_exp_boundary_of_coprime
      (d := d) (x := x) (u := u) hd_prime hd_ge hx hu hcop hpnd with
    ⟨q, hqP, hq_dvd, hq_not_dvd_x, _hprim⟩
  let p : {q // Nat.Prime q} := ⟨q, hqP⟩
  have hS_ne :
      ∀ r ∈ ({p} : Finset {q // Nat.Prime q}),
        eulerZeta_exp_s_log_p_sub_one r.1 σ t ≠ 0 := by
    intro r hr
    have hrp : r = p := Finset.mem_singleton.mp hr
    subst hrp
    exact hwnz p hq_dvd hq_not_dvd_x
  have hstat :
      DkMath.RH.stationaryAt
        (fun v : ℝ =>
          eulerZetaFinite_onVertical ({p} : Finset {q // Nat.Prime q}) σ v) t := by
    exact (stationaryAt_eulerZetaFinite_onVertical_iff_hopcPrimeContributionSum_eq_zero
      (S := ({p} : Finset {q // Nat.Prime q})) (σ := σ) (t := t) hS_ne).2
        (hhopc0 p hq_dvd hq_not_dvd_x)
  exact ⟨p, hstat⟩

/--
RH-J3: local 仮定版 bridge。

`hopcPrimeContributionSum` ではなく `hopcPrimeLocalContribution` を仮定し、
singleton wrapper で停留へ落とす。
-/
theorem exists_stationaryAt_singleton_of_cfbRc_primitive_prime_bridge_of_local
    {d x u : ℕ} {σ t : ℝ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : ¬ d ∣ x)
    (hwnz :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ ((x + u) ^ d - u ^ d) → ¬ p.1 ∣ x →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hhopc_local0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ ((x + u) ^ d - u ^ d) → ¬ p.1 ∣ x →
          hopcPrimeLocalContribution p.1 σ t = 0) :
    ∃ p : {q // Nat.Prime q},
      DkMath.RH.stationaryAt
        (fun v : ℝ =>
          eulerZetaFinite_onVertical ({p} : Finset {q // Nat.Prime q}) σ v) t := by
  rcases DkMath.CFBRC.exists_primitive_prime_factor_sub_pow_of_prime_exp_boundary_of_coprime
      (d := d) (x := x) (u := u) hd_prime hd_ge hx hu hcop hpnd with
    ⟨q, hqP, hq_dvd, hq_not_dvd_x, _hprim⟩
  let p : {q // Nat.Prime q} := ⟨q, hqP⟩
  have hp_ne :
      eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0 :=
    hwnz p hq_dvd hq_not_dvd_x
  have hlocal0 :
      hopcPrimeLocalContribution p.1 σ t = 0 :=
    hhopc_local0 p hq_dvd hq_not_dvd_x
  exact ⟨p,
    stationaryAt_eulerZetaFinite_onVertical_singleton_of_hopcPrimeLocalContribution_eq_zero
      (p := p) (σ := σ) (t := t) hp_ne hlocal0⟩

/--
RH-N1: small finite-set へ持ち上げる `insert` wrapper。

`insert p S` 上で `w_r ≠ 0` と `hopcPrimeContributionSum = 0` が供給できれば、
`eulerZetaFinite_onVertical` の停留を得る。
-/
theorem stationaryAt_insert_of_hopcPrimeContributionSum_eq_zero
    (S : Finset {q // Nat.Prime q}) (p : {q // Nat.Prime q}) {σ t : ℝ}
    (hS_ne :
      ∀ r ∈ (insert p S), eulerZeta_exp_s_log_p_sub_one r.1 σ t ≠ 0)
    (hsum0 :
      hopcPrimeContributionSum (S := insert p S) σ t = 0) :
    DkMath.RH.stationaryAt
      (fun v : ℝ =>
        eulerZetaFinite_onVertical (insert p S) σ v) t := by
  exact (stationaryAt_eulerZetaFinite_onVertical_iff_hopcPrimeContributionSum_eq_zero
    (S := insert p S) (σ := σ) (t := t) hS_ne).2 hsum0

/--
OP-004: `insert p S` 観測器で、停留 + 曲率非零から
非退化停留を得る標準 wrapper。
-/
theorem nondegenerateStationaryAt_insert_of_hopcPrimeContributionSum_eq_zero_and_phaseCurv_ne_zero
    (S : Finset {q // Nat.Prime q}) (p : {q // Nat.Prime q}) {σ t : ℝ}
    (hS_ne :
      ∀ r ∈ (insert p S), eulerZeta_exp_s_log_p_sub_one r.1 σ t ≠ 0)
    (hsum0 :
      hopcPrimeContributionSum (S := insert p S) σ t = 0)
    (hcurv0 :
      DkMath.RH.phaseCurv
        (fun v : ℝ => eulerZetaFinite_onVertical (insert p S) σ v) t ≠ 0) :
    DkMath.RH.nondegenerateStationaryAt
      (fun v : ℝ => eulerZetaFinite_onVertical (insert p S) σ v) t := by
  exact
    (nondegenerateStationaryAt_eulerZetaFinite_onVertical_iff_hopcPrimeContributionSum
      (S := insert p S) (σ := σ) (t := t) hS_ne).2 ⟨hsum0, hcurv0⟩

/--
RH-N1: CFBRC existence + local 翻訳仮定を small finite-set（`insert p S`）へ持ち上げる
API スケッチ。

`hlift` によって `insert p S` 上の非零前提と寄与総和ゼロを供給できるとき、
対応する有限観測器の停留点存在を返す。
-/
theorem exists_stationaryAt_insert_of_cfbRc_primitive_prime_bridge_of_local
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : ¬ d ∣ x)
    (hlift :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ ((x + u) ^ d - u ^ d) → ¬ p.1 ∣ x →
          (∀ r ∈ (insert p S), eulerZeta_exp_s_log_p_sub_one r.1 σ t ≠ 0) ∧
          hopcPrimeContributionSum (S := insert p S) σ t = 0) :
    ∃ p : {q // Nat.Prime q},
      DkMath.RH.stationaryAt
        (fun v : ℝ => eulerZetaFinite_onVertical (insert p S) σ v) t := by
  rcases DkMath.CFBRC.exists_primitive_prime_factor_sub_pow_of_prime_exp_boundary_of_coprime
      (d := d) (x := x) (u := u) hd_prime hd_ge hx hu hcop hpnd with
    ⟨q, hqP, hq_dvd, hq_not_dvd_x, _hprim⟩
  let p : {q // Nat.Prime q} := ⟨q, hqP⟩
  have hS_ne :
      ∀ r ∈ (insert p S), eulerZeta_exp_s_log_p_sub_one r.1 σ t ≠ 0 :=
    (hlift p hq_dvd hq_not_dvd_x).1
  have hsum0 :
      hopcPrimeContributionSum (S := insert p S) σ t = 0 :=
    (hlift p hq_dvd hq_not_dvd_x).2
  exact ⟨p, stationaryAt_insert_of_hopcPrimeContributionSum_eq_zero
    (S := S) (p := p) (hS_ne := hS_ne) (hsum0 := hsum0)⟩

/--
RH-N2: `hlift` を分解した small finite-set bridge。

`insert p S` 上の非零前提供給 (`hS_lift`) と寄与総和ゼロ供給 (`hsum_lift`) を
個別に受け取り、停留点存在へ落とす。
-/
theorem exists_stationaryAt_insert_of_cfbRc_primitive_prime_bridge_of_local_split
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : ¬ d ∣ x)
    (hS_lift :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ ((x + u) ^ d - u ^ d) → ¬ p.1 ∣ x →
          ∀ r ∈ (insert p S), eulerZeta_exp_s_log_p_sub_one r.1 σ t ≠ 0)
    (hsum_lift :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ ((x + u) ^ d - u ^ d) → ¬ p.1 ∣ x →
          hopcPrimeContributionSum (S := insert p S) σ t = 0) :
    ∃ p : {q // Nat.Prime q},
      DkMath.RH.stationaryAt
        (fun v : ℝ => eulerZetaFinite_onVertical (insert p S) σ v) t := by
  rcases DkMath.CFBRC.exists_primitive_prime_factor_sub_pow_of_prime_exp_boundary_of_coprime
      (d := d) (x := x) (u := u) hd_prime hd_ge hx hu hcop hpnd with
    ⟨q, hqP, hq_dvd, hq_not_dvd_x, _hprim⟩
  let p : {q // Nat.Prime q} := ⟨q, hqP⟩
  have hS_ne :
      ∀ r ∈ (insert p S), eulerZeta_exp_s_log_p_sub_one r.1 σ t ≠ 0 :=
    hS_lift p hq_dvd hq_not_dvd_x
  have hsum0 :
      hopcPrimeContributionSum (S := insert p S) σ t = 0 :=
    hsum_lift p hq_dvd hq_not_dvd_x
  exact ⟨p, stationaryAt_insert_of_hopcPrimeContributionSum_eq_zero
    (S := S) (p := p) (hS_ne := hS_ne) (hsum0 := hsum0)⟩

/--
OP-004: small finite-set bridge（right 境界）に曲率非零供給を追加した版。

`hS_lift` / `hsum_lift` に加えて `hcurv_lift` を受け取り、
`insert p S` 観測器での非退化停留点存在へ接続する。
-/
theorem exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_bridge_of_local_split_and_phaseCurv
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : ¬ d ∣ x)
    (hS_lift :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ ((x + u) ^ d - u ^ d) → ¬ p.1 ∣ x →
          ∀ r ∈ (insert p S), eulerZeta_exp_s_log_p_sub_one r.1 σ t ≠ 0)
    (hsum_lift :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ ((x + u) ^ d - u ^ d) → ¬ p.1 ∣ x →
          hopcPrimeContributionSum (S := insert p S) σ t = 0)
    (hcurv_lift :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ ((x + u) ^ d - u ^ d) → ¬ p.1 ∣ x →
          DkMath.RH.phaseCurv
            (fun v : ℝ => eulerZetaFinite_onVertical (insert p S) σ v) t ≠ 0) :
    ∃ p : {q // Nat.Prime q},
      DkMath.RH.nondegenerateStationaryAt
        (fun v : ℝ => eulerZetaFinite_onVertical (insert p S) σ v) t := by
  rcases DkMath.CFBRC.exists_primitive_prime_factor_sub_pow_of_prime_exp_boundary_of_coprime
      (d := d) (x := x) (u := u) hd_prime hd_ge hx hu hcop hpnd with
    ⟨q, hqP, hq_dvd, hq_not_dvd_x, _hprim⟩
  let p : {q // Nat.Prime q} := ⟨q, hqP⟩
  have hS_ne :
      ∀ r ∈ (insert p S), eulerZeta_exp_s_log_p_sub_one r.1 σ t ≠ 0 :=
    hS_lift p hq_dvd hq_not_dvd_x
  have hsum0 :
      hopcPrimeContributionSum (S := insert p S) σ t = 0 :=
    hsum_lift p hq_dvd hq_not_dvd_x
  have hcurv0 :
      DkMath.RH.phaseCurv
        (fun v : ℝ => eulerZetaFinite_onVertical (insert p S) σ v) t ≠ 0 :=
    hcurv_lift p hq_dvd hq_not_dvd_x
  exact ⟨p,
    nondegenerateStationaryAt_insert_of_hopcPrimeContributionSum_eq_zero_and_phaseCurv_ne_zero
      (S := S) (p := p) (hS_ne := hS_ne) (hsum0 := hsum0) (hcurv0 := hcurv0)⟩

/--
RH-N3: `BoundarySide` 統一版の singleton local bridge。

`side` が `right/left` のどちらでも、対応する境界差分
`boundaryDiffPow side d x u` の primitive prime existence から
singleton 観測器の停留点存在へ接続する。
-/
theorem exists_stationaryAt_singleton_of_cfbRc_primitive_prime_boundary_bridge_of_local
    (side : DkMath.CFBRC.BoundarySide)
    {d x u : ℕ} {σ t : ℝ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : match side with
      | .right => ¬ d ∣ x
      | .left => ¬ d ∣ u)
    (hwnz :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          (match side with
            | .right => ¬ p.1 ∣ x
            | .left => ¬ p.1 ∣ u) →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hhopc_local0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          (match side with
            | .right => ¬ p.1 ∣ x
            | .left => ¬ p.1 ∣ u) →
          hopcPrimeLocalContribution p.1 σ t = 0) :
    ∃ p : {q // Nat.Prime q},
      DkMath.RH.stationaryAt
        (fun v : ℝ =>
          eulerZetaFinite_onVertical ({p} : Finset {q // Nat.Prime q}) σ v) t := by
  cases side with
  | right =>
      simpa [DkMath.CFBRC.boundaryDiffPow] using
        (exists_stationaryAt_singleton_of_cfbRc_primitive_prime_bridge_of_local
          (d := d) (x := x) (u := u) (σ := σ) (t := t)
          hd_prime hd_ge hx hu hcop hpnd hwnz hhopc_local0)
  | left =>
      simpa [DkMath.CFBRC.boundaryDiffPow, Nat.add_comm] using
        (exists_stationaryAt_singleton_of_cfbRc_primitive_prime_bridge_of_local
          (d := d) (x := u) (u := x) (σ := σ) (t := t)
          hd_prime hd_ge hu hx hcop.symm hpnd
          (fun p hq_dvd hq_not_dvd_u =>
            hwnz p (by simpa [DkMath.CFBRC.boundaryDiffPow, Nat.add_comm] using hq_dvd)
              hq_not_dvd_u)
          (fun p hq_dvd hq_not_dvd_u =>
            hhopc_local0 p
              (by simpa [DkMath.CFBRC.boundaryDiffPow, Nat.add_comm] using hq_dvd)
              hq_not_dvd_u))

/--
OP-004: `BoundarySide` 統一版の singleton 非退化停留 bridge（local + phaseCurv）。

`side` 境界の primitive prime existence を使い、
singleton 観測器で `stationaryAt` と `phaseCurv ≠ 0` を同時に満たす点を返す。
-/
theorem exists_nondegenerateStationaryAt_singleton_of_cfbRc_primitive_prime_boundary_bridge_of_local_and_phaseCurv
    (side : DkMath.CFBRC.BoundarySide)
    {d x u : ℕ} {σ t : ℝ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : match side with
      | .right => ¬ d ∣ x
      | .left => ¬ d ∣ u)
    (hwnz :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          (match side with
            | .right => ¬ p.1 ∣ x
            | .left => ¬ p.1 ∣ u) →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hhopc_local0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          (match side with
            | .right => ¬ p.1 ∣ x
            | .left => ¬ p.1 ∣ u) →
          hopcPrimeLocalContribution p.1 σ t = 0)
    (hcurv_local0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          (match side with
            | .right => ¬ p.1 ∣ x
            | .left => ¬ p.1 ∣ u) →
          DkMath.RH.phaseCurv
            (fun v : ℝ => eulerZetaFinite_onVertical ({p} : Finset {q // Nat.Prime q}) σ v) t ≠ 0) :
    ∃ p : {q // Nat.Prime q},
      DkMath.RH.nondegenerateStationaryAt
        (fun v : ℝ => eulerZetaFinite_onVertical ({p} : Finset {q // Nat.Prime q}) σ v) t := by
  cases side with
  | right =>
      have hS_lift :
          ∀ p : {q // Nat.Prime q},
            p.1 ∣ ((x + u) ^ d - u ^ d) → ¬ p.1 ∣ x →
            ∀ r ∈ (insert p (∅ : Finset {q // Nat.Prime q})),
              eulerZeta_exp_s_log_p_sub_one r.1 σ t ≠ 0 := by
        intro p hp_dvd hp_gap r hr
        have hpr : eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0 :=
          hwnz p (by simpa [DkMath.CFBRC.boundaryDiffPow] using hp_dvd) hp_gap
        have hrp : r = p := by simpa using (Finset.mem_singleton.mp (by simpa using hr))
        simpa [hrp] using hpr
      have hsum_lift :
          ∀ p : {q // Nat.Prime q},
            p.1 ∣ ((x + u) ^ d - u ^ d) → ¬ p.1 ∣ x →
            hopcPrimeContributionSum (S := insert p (∅ : Finset {q // Nat.Prime q})) σ t = 0 := by
        intro p hp_dvd hp_gap
        have hlocal0 : hopcPrimeLocalContribution p.1 σ t = 0 :=
          hhopc_local0 p (by simpa [DkMath.CFBRC.boundaryDiffPow] using hp_dvd) hp_gap
        simpa using hlocal0
      have hcurv_lift :
          ∀ p : {q // Nat.Prime q},
            p.1 ∣ ((x + u) ^ d - u ^ d) → ¬ p.1 ∣ x →
            DkMath.RH.phaseCurv
              (fun v : ℝ =>
                eulerZetaFinite_onVertical (insert p (∅ : Finset {q // Nat.Prime q})) σ v) t ≠ 0 := by
        intro p hp_dvd hp_gap
        have hcurv0 :
            DkMath.RH.phaseCurv
              (fun v : ℝ => eulerZetaFinite_onVertical ({p} : Finset {q // Nat.Prime q}) σ v) t ≠ 0 :=
          hcurv_local0 p (by simpa [DkMath.CFBRC.boundaryDiffPow] using hp_dvd) hp_gap
        simpa using hcurv0
      simpa using
        (exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_bridge_of_local_split_and_phaseCurv
          (S := (∅ : Finset {q // Nat.Prime q}))
          (d := d) (x := x) (u := u) (σ := σ) (t := t)
          hd_prime hd_ge hx hu hcop hpnd hS_lift hsum_lift hcurv_lift)
  | left =>
      have hS_lift :
          ∀ p : {q // Nat.Prime q},
            p.1 ∣ ((u + x) ^ d - x ^ d) → ¬ p.1 ∣ u →
            ∀ r ∈ (insert p (∅ : Finset {q // Nat.Prime q})),
              eulerZeta_exp_s_log_p_sub_one r.1 σ t ≠ 0 := by
        intro p hp_dvd hp_gap r hr
        have hpr : eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0 :=
          hwnz p (by simpa [DkMath.CFBRC.boundaryDiffPow, Nat.add_comm] using hp_dvd) hp_gap
        have hrp : r = p := by simpa using (Finset.mem_singleton.mp (by simpa using hr))
        simpa [hrp] using hpr
      have hsum_lift :
          ∀ p : {q // Nat.Prime q},
            p.1 ∣ ((u + x) ^ d - x ^ d) → ¬ p.1 ∣ u →
            hopcPrimeContributionSum (S := insert p (∅ : Finset {q // Nat.Prime q})) σ t = 0 := by
        intro p hp_dvd hp_gap
        have hlocal0 : hopcPrimeLocalContribution p.1 σ t = 0 :=
          hhopc_local0 p (by simpa [DkMath.CFBRC.boundaryDiffPow, Nat.add_comm] using hp_dvd) hp_gap
        simpa using hlocal0
      have hcurv_lift :
          ∀ p : {q // Nat.Prime q},
            p.1 ∣ ((u + x) ^ d - x ^ d) → ¬ p.1 ∣ u →
            DkMath.RH.phaseCurv
              (fun v : ℝ =>
                eulerZetaFinite_onVertical (insert p (∅ : Finset {q // Nat.Prime q})) σ v) t ≠ 0 := by
        intro p hp_dvd hp_gap
        have hcurv0 :
            DkMath.RH.phaseCurv
              (fun v : ℝ => eulerZetaFinite_onVertical ({p} : Finset {q // Nat.Prime q}) σ v) t ≠ 0 :=
          hcurv_local0 p (by simpa [DkMath.CFBRC.boundaryDiffPow, Nat.add_comm] using hp_dvd) hp_gap
        simpa using hcurv0
      simpa using
        (exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_bridge_of_local_split_and_phaseCurv
          (S := (∅ : Finset {q // Nat.Prime q}))
          (d := d) (x := u) (u := x) (σ := σ) (t := t)
          hd_prime hd_ge hu hx hcop.symm hpnd hS_lift hsum_lift hcurv_lift)

/--
RH-N3: `BoundarySide` 統一版の small finite-set bridge（split 仮定）。

`insert p S` 上の非零前提供給と寄与総和ゼロ供給を分離したまま、
左右境界を `side` 引数で共通化する。
-/
theorem exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_local_split
    (side : DkMath.CFBRC.BoundarySide)
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
          (match side with
            | .right => ¬ p.1 ∣ x
            | .left => ¬ p.1 ∣ u) →
          ∀ r ∈ (insert p S), eulerZeta_exp_s_log_p_sub_one r.1 σ t ≠ 0)
    (hsum_lift :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          (match side with
            | .right => ¬ p.1 ∣ x
            | .left => ¬ p.1 ∣ u) →
          hopcPrimeContributionSum (S := insert p S) σ t = 0) :
    ∃ p : {q // Nat.Prime q},
      DkMath.RH.stationaryAt
        (fun v : ℝ => eulerZetaFinite_onVertical (insert p S) σ v) t := by
  cases side with
  | right =>
      simpa [DkMath.CFBRC.boundaryDiffPow] using
        (exists_stationaryAt_insert_of_cfbRc_primitive_prime_bridge_of_local_split
          (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
          hd_prime hd_ge hx hu hcop hpnd hS_lift hsum_lift)
  | left =>
      simpa [DkMath.CFBRC.boundaryDiffPow, Nat.add_comm] using
        (exists_stationaryAt_insert_of_cfbRc_primitive_prime_bridge_of_local_split
          (S := S) (d := d) (x := u) (u := x) (σ := σ) (t := t)
          hd_prime hd_ge hu hx hcop.symm hpnd
          (fun p hq_dvd hq_not_dvd_u =>
            hS_lift p
              (by simpa [DkMath.CFBRC.boundaryDiffPow, Nat.add_comm] using hq_dvd)
              hq_not_dvd_u)
          (fun p hq_dvd hq_not_dvd_u =>
            hsum_lift p
              (by simpa [DkMath.CFBRC.boundaryDiffPow, Nat.add_comm] using hq_dvd)
              hq_not_dvd_u))

/--
OP-004: `BoundarySide` 統一版の small finite-set 非退化停留 bridge（split 仮定）。

`hS_lift` / `hsum_lift` に加え、`hcurv_lift`（曲率非零供給）を受け取る。
-/
theorem exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_local_split_and_phaseCurv
    (side : DkMath.CFBRC.BoundarySide)
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
          (match side with
            | .right => ¬ p.1 ∣ x
            | .left => ¬ p.1 ∣ u) →
          ∀ r ∈ (insert p S), eulerZeta_exp_s_log_p_sub_one r.1 σ t ≠ 0)
    (hsum_lift :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          (match side with
            | .right => ¬ p.1 ∣ x
            | .left => ¬ p.1 ∣ u) →
          hopcPrimeContributionSum (S := insert p S) σ t = 0)
    (hcurv_lift :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          (match side with
            | .right => ¬ p.1 ∣ x
            | .left => ¬ p.1 ∣ u) →
          DkMath.RH.phaseCurv
            (fun v : ℝ => eulerZetaFinite_onVertical (insert p S) σ v) t ≠ 0) :
    ∃ p : {q // Nat.Prime q},
      DkMath.RH.nondegenerateStationaryAt
        (fun v : ℝ => eulerZetaFinite_onVertical (insert p S) σ v) t := by
  cases side with
  | right =>
      simpa [DkMath.CFBRC.boundaryDiffPow] using
        (exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_bridge_of_local_split_and_phaseCurv
          (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
          hd_prime hd_ge hx hu hcop hpnd hS_lift hsum_lift hcurv_lift)
  | left =>
      simpa [DkMath.CFBRC.boundaryDiffPow, Nat.add_comm] using
        (exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_bridge_of_local_split_and_phaseCurv
          (S := S) (d := d) (x := u) (u := x) (σ := σ) (t := t)
          hd_prime hd_ge hu hx hcop.symm hpnd
          (fun p hq_dvd hq_not_dvd_u =>
            hS_lift p
              (by simpa [DkMath.CFBRC.boundaryDiffPow, Nat.add_comm] using hq_dvd)
              hq_not_dvd_u)
          (fun p hq_dvd hq_not_dvd_u =>
            hsum_lift p
              (by simpa [DkMath.CFBRC.boundaryDiffPow, Nat.add_comm] using hq_dvd)
              hq_not_dvd_u)
          (fun p hq_dvd hq_not_dvd_u =>
            hcurv_lift p
              (by simpa [DkMath.CFBRC.boundaryDiffPow, Nat.add_comm] using hq_dvd)
              hq_not_dvd_u))

/--
RH-N3: `BoundarySide` 統一版の small finite-set bridge（一括 `hlift` 入力）。

split 版 API への互換 wrapper。
-/
theorem exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_local
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : match side with
      | .right => ¬ d ∣ x
      | .left => ¬ d ∣ u)
    (hlift :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          (match side with
            | .right => ¬ p.1 ∣ x
            | .left => ¬ p.1 ∣ u) →
          (∀ r ∈ (insert p S), eulerZeta_exp_s_log_p_sub_one r.1 σ t ≠ 0) ∧
          hopcPrimeContributionSum (S := insert p S) σ t = 0) :
    ∃ p : {q // Nat.Prime q},
      DkMath.RH.stationaryAt
        (fun v : ℝ => eulerZetaFinite_onVertical (insert p S) σ v) t := by
  cases side with
  | right =>
      simpa [DkMath.CFBRC.boundaryDiffPow] using
        (exists_stationaryAt_insert_of_cfbRc_primitive_prime_bridge_of_local
          (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
          hd_prime hd_ge hx hu hcop hpnd hlift)
  | left =>
      simpa [DkMath.CFBRC.boundaryDiffPow, Nat.add_comm] using
        (exists_stationaryAt_insert_of_cfbRc_primitive_prime_bridge_of_local
          (S := S) (d := d) (x := u) (u := x) (σ := σ) (t := t)
          hd_prime hd_ge hu hx hcop.symm hpnd
          (fun p hq_dvd hq_not_dvd_u =>
            hlift p
              (by simpa [DkMath.CFBRC.boundaryDiffPow, Nat.add_comm] using hq_dvd)
              hq_not_dvd_u))

/--
RH-N7: `BoundarySide` + small finite-set 向けの split 供給インターフェース。

`hS_lift`（非零前提供給）と `hsum_lift`（寄与総和ゼロ供給）を
一つの record として束ね、provider 層から bridge へ渡しやすくする。
-/
structure BoundaryInsertLocalLiftProvider
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    (d x u : ℕ) (σ t : ℝ) : Type where
  hS_lift :
    ∀ p : {q // Nat.Prime q},
      p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
        (match side with
          | .right => ¬ p.1 ∣ x
          | .left => ¬ p.1 ∣ u) →
        ∀ r ∈ (insert p S), eulerZeta_exp_s_log_p_sub_one r.1 σ t ≠ 0
  hsum_lift :
    ∀ p : {q // Nat.Prime q},
      p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
        (match side with
          | .right => ¬ p.1 ∣ x
          | .left => ¬ p.1 ∣ u) →
        hopcPrimeContributionSum (S := insert p S) σ t = 0

/--
OP-004: `BoundarySide` + small finite-set 向けの曲率非零供給インターフェース。

`insert p S` 観測器に対する `phaseCurv ≠ 0` 供給を record 化する。
-/
structure BoundaryInsertPhaseCurvProvider
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    (d x u : ℕ) (σ t : ℝ) : Type where
  hcurv_lift :
    ∀ p : {q // Nat.Prime q},
      p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
        (match side with
          | .right => ¬ p.1 ∣ x
          | .left => ¬ p.1 ∣ u) →
        DkMath.RH.phaseCurv
          (fun v : ℝ => eulerZetaFinite_onVertical (insert p S) σ v) t ≠ 0

/--
RH-N11: split 仮定から provider record を構成する最小補題。

`hS_lift` と `hsum_lift` をそのまま `BoundaryInsertLocalLiftProvider`
へ束ねる供給器。
-/
def boundaryInsertLocalLiftProvider_of_split
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hS_lift :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          (match side with
            | .right => ¬ p.1 ∣ x
            | .left => ¬ p.1 ∣ u) →
          ∀ r ∈ (insert p S), eulerZeta_exp_s_log_p_sub_one r.1 σ t ≠ 0)
    (hsum_lift :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          (match side with
            | .right => ¬ p.1 ∣ x
            | .left => ¬ p.1 ∣ u) →
          hopcPrimeContributionSum (S := insert p S) σ t = 0) :
    BoundaryInsertLocalLiftProvider side S d x u σ t :=
  ⟨hS_lift, hsum_lift⟩

/--
OP-004: split 仮定から曲率供給 provider を構成する最小補題。
-/
def boundaryInsertPhaseCurvProvider_of_split
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hcurv_lift :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          (match side with
            | .right => ¬ p.1 ∣ x
            | .left => ¬ p.1 ∣ u) →
          DkMath.RH.phaseCurv
            (fun v : ℝ => eulerZetaFinite_onVertical (insert p S) σ v) t ≠ 0) :
    BoundaryInsertPhaseCurvProvider side S d x u σ t :=
  ⟨hcurv_lift⟩

/--
RH-N11: pair 形式 (`hlift`) から provider record を構成する補題。

既存の一括入力
`(hS_lift ∧ hsum_lift)` 形式から provider 版 API へ接続する。
-/
def boundaryInsertLocalLiftProvider_of_pair
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hlift :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          (match side with
            | .right => ¬ p.1 ∣ x
            | .left => ¬ p.1 ∣ u) →
          (∀ r ∈ (insert p S), eulerZeta_exp_s_log_p_sub_one r.1 σ t ≠ 0) ∧
          hopcPrimeContributionSum (S := insert p S) σ t = 0) :
    BoundaryInsertLocalLiftProvider side S d x u σ t := by
  cases side with
  | right =>
      exact boundaryInsertLocalLiftProvider_of_split
        (side := .right) (S := S)
        (hS_lift := fun p hq_dvd hq_not_dvd_x =>
          (hlift p hq_dvd hq_not_dvd_x).1)
        (hsum_lift := fun p hq_dvd hq_not_dvd_x =>
          (hlift p hq_dvd hq_not_dvd_x).2)
  | left =>
      exact boundaryInsertLocalLiftProvider_of_split
        (side := .left) (S := S)
        (hS_lift := fun p hq_dvd hq_not_dvd_u =>
          (hlift p hq_dvd hq_not_dvd_u).1)
        (hsum_lift := fun p hq_dvd hq_not_dvd_u =>
          (hlift p hq_dvd hq_not_dvd_u).2)

/--
RH-N12: `hS_lift` の段階供給補題（`S` 上非零 + witness 非零）。

`insert p S` 上の非零前提を、次の 2 段で組み立てる:
1. `S` 上の一様非零供給
2. witness prime `p` 自身の非零供給
-/
theorem boundary_hS_lift_of_nonzero_on_S_and_witness
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hS_nonzero :
      ∀ r ∈ S, eulerZeta_exp_s_log_p_sub_one r.1 σ t ≠ 0)
    (hwnz_witness :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          (match side with
            | .right => ¬ p.1 ∣ x
            | .left => ¬ p.1 ∣ u) →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0) :
    ∀ p : {q // Nat.Prime q},
      p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
        (match side with
          | .right => ¬ p.1 ∣ x
          | .left => ¬ p.1 ∣ u) →
        ∀ r ∈ (insert p S), eulerZeta_exp_s_log_p_sub_one r.1 σ t ≠ 0 := by
  cases side with
  | right =>
      intro p hq_dvd hq_not_dvd_x r hr
      rcases Finset.mem_insert.mp hr with hr_eq | hrS
      · have hp_nonzero :
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0 :=
          hwnz_witness p hq_dvd hq_not_dvd_x
        simpa [hr_eq] using hp_nonzero
      · exact hS_nonzero r hrS
  | left =>
      intro p hq_dvd hq_not_dvd_u r hr
      rcases Finset.mem_insert.mp hr with hr_eq | hrS
      · have hp_nonzero :
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0 :=
          hwnz_witness p hq_dvd hq_not_dvd_u
        simpa [hr_eq] using hp_nonzero
      · exact hS_nonzero r hrS

/--
RH-N17: CFBRC 側条件（boundary 除法 + gap 非除法）から `S` 上非零を供給。

各 `r ∈ S` について
`r ∣ boundaryDiffPow side d x u` と
`side` 対応の gap 非除法が供給されれば、
`hwnz_witness` から `eulerZeta_exp_s_log_p_sub_one r.1 σ t ≠ 0` を得る。
-/
theorem boundary_nonzero_on_S_of_boundary_dvd_and_gap
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hS_dvd :
      ∀ r ∈ S, r.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u)
    (hS_gap :
      ∀ r ∈ S, (match side with
        | .right => ¬ r.1 ∣ x
        | .left => ¬ r.1 ∣ u))
    (hwnz_witness :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          (match side with
            | .right => ¬ p.1 ∣ x
            | .left => ¬ p.1 ∣ u) →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0) :
    ∀ r ∈ S, eulerZeta_exp_s_log_p_sub_one r.1 σ t ≠ 0 := by
  cases side with
  | right =>
      intro r hr
      exact hwnz_witness r (hS_dvd r hr) (hS_gap r hr)
  | left =>
      intro r hr
      exact hwnz_witness r (hS_dvd r hr) (hS_gap r hr)

/--
RH-N22: `boundaryCyclotomicPrimeCore` 側の非零仮定から witness 非零を復元。

`hwnz_core`（core 除法だけを前提にした非零仮定）から、
`boundaryDiffPow` 除法 + gap 非除法を前提にした
`hwnz_witness` 形式へ落とす。
-/
theorem boundary_hwnz_witness_of_boundaryCore_nonzero
    (side : DkMath.CFBRC.BoundarySide)
    {d x u : ℕ} {σ t : ℝ}
    (hwnz_core :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0) :
    ∀ p : {q // Nat.Prime q},
      p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
        (match side with
          | .right => ¬ p.1 ∣ x
          | .left => ¬ p.1 ∣ u) →
        eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0 := by
  cases side with
  | right =>
      intro p hq_dvd hq_not_dvd_x
      have hq_dvd_core : p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore .right d x u := by
        have hq_dvd_core_nat : p.1 ∣ DkMath.CFBRC.cyclotomicPrimeCore d x u :=
          (DkMath.CFBRC.prime_dvd_sub_pow_iff_dvd_cyclotomicPrimeCore_nat
            (p := d) (x := x) (u := u) (q := p.1) p.2 hq_not_dvd_x).1
            (by simpa [DkMath.CFBRC.boundaryDiffPow] using hq_dvd)
        simpa [DkMath.CFBRC.boundaryCyclotomicPrimeCore] using hq_dvd_core_nat
      exact hwnz_core p hq_dvd_core
  | left =>
      intro p hq_dvd hq_not_dvd_u
      have hq_dvd_core : p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore .left d x u := by
        have hq_dvd_sub_swap : p.1 ∣ ((u + x) ^ d - x ^ d) := by
          simpa [DkMath.CFBRC.boundaryDiffPow, Nat.add_comm] using hq_dvd
        have hq_dvd_core_swap : p.1 ∣ DkMath.CFBRC.cyclotomicPrimeCore d u x :=
          (DkMath.CFBRC.prime_dvd_sub_pow_iff_dvd_cyclotomicPrimeCore_nat
            (p := d) (x := u) (u := x) (q := p.1) p.2 hq_not_dvd_u).1 hq_dvd_sub_swap
        simpa [DkMath.CFBRC.boundaryCyclotomicPrimeCore] using hq_dvd_core_swap
      exact hwnz_core p hq_dvd_core

/--
RH-N21: CFBRC 側条件（boundary 除法 + gap 非除法）から `S` 上 local-zero を供給。

各 `r ∈ S` について
`r ∣ boundaryDiffPow side d x u` と
`side` 対応の gap 非除法が供給されれば、
`hlocal_witness` から `hopcPrimeLocalContribution r.1 σ t = 0` を得る。
-/
theorem boundary_local_zero_on_S_of_boundary_dvd_and_gap
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hS_dvd :
      ∀ r ∈ S, r.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u)
    (hS_gap :
      ∀ r ∈ S, (match side with
        | .right => ¬ r.1 ∣ x
        | .left => ¬ r.1 ∣ u))
    (hlocal_witness :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          (match side with
            | .right => ¬ p.1 ∣ x
            | .left => ¬ p.1 ∣ u) →
          hopcPrimeLocalContribution p.1 σ t = 0) :
    ∀ r ∈ S, hopcPrimeLocalContribution r.1 σ t = 0 := by
  cases side with
  | right =>
      intro r hr
      exact hlocal_witness r (hS_dvd r hr) (hS_gap r hr)
  | left =>
      intro r hr
      exact hlocal_witness r (hS_dvd r hr) (hS_gap r hr)

/--
RH-N28: `S` 上の boundary 除法仮定と witness の boundary 除法を合成し、
`insert p S` 上の boundary 除法仮定を供給する補題。
-/
theorem boundary_dvd_on_insert_of_boundary_dvd_and_witness
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ}
    (p : {q // Nat.Prime q})
    (hS_dvd :
      ∀ r ∈ S, r.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u)
    (hp_dvd : p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u) :
    ∀ r ∈ insert p S, r.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u := by
  intro r hr
  rcases Finset.mem_insert.mp hr with hrp | hrS
  · simpa [hrp] using hp_dvd
  · exact hS_dvd r hrS

/--
RH-N28: `S` 上の gap 非除法仮定と witness の gap 非除法を合成し、
`insert p S` 上の gap 非除法仮定を供給する補題。
-/
theorem boundary_gap_on_insert_of_boundary_gap_and_witness
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {x u : ℕ}
    (p : {q // Nat.Prime q})
    (hS_gap :
      ∀ r ∈ S, (match side with
        | .right => ¬ r.1 ∣ x
        | .left => ¬ r.1 ∣ u))
    (hp_gap : match side with
      | .right => ¬ p.1 ∣ x
      | .left => ¬ p.1 ∣ u) :
    ∀ r ∈ insert p S, (match side with
      | .right => ¬ r.1 ∣ x
      | .left => ¬ r.1 ∣ u) := by
  cases side with
  | right =>
      intro r hr
      rcases Finset.mem_insert.mp hr with hrp | hrS
      · simpa [hrp] using hp_gap
      · exact hS_gap r hrS
  | left =>
      intro r hr
      rcases Finset.mem_insert.mp hr with hrp | hrS
      · simpa [hrp] using hp_gap
      · exact hS_gap r hrS

/--
RH-N28: CFBRC の primitive prime existence から、
`boundaryDiffPow side d x u` を割り、対応 gap を割らない素数 witness を返す。
-/
theorem exists_boundaryPrime_dvd_gap_of_cfbRc_primitive_prime_boundaryDiffPow_of_coprime
    (side : DkMath.CFBRC.BoundarySide)
    {d x u : ℕ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : match side with
      | .right => ¬ d ∣ x
      | .left => ¬ d ∣ u) :
    ∃ p : {q // Nat.Prime q},
      p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u ∧
      (match side with
        | .right => ¬ p.1 ∣ x
        | .left => ¬ p.1 ∣ u) := by
  rcases DkMath.CFBRC.exists_primitive_prime_factor_boundaryDiffPow_of_prime_exp_boundary_of_coprime
      (side := side) (d := d) (x := x) (u := u)
      hd_prime hd_ge hx hu hcop hpnd with
    ⟨q, hqP, hq_dvd, hq_gap, _hprim⟩
  exact ⟨⟨q, hqP⟩, hq_dvd, hq_gap⟩

/--
RH-N28: CFBRC primitive prime existence と `S` 上の `hS_dvd / hS_gap` を接続し、
`insert p S` 上の `hS_dvd / hS_gap` を同時供給する実補題。
-/
theorem exists_boundary_dvd_gap_on_insert_of_cfbRc_primitive_prime_boundaryDiffPow_of_coprime
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : match side with
      | .right => ¬ d ∣ x
      | .left => ¬ d ∣ u)
    (hS_dvd :
      ∀ r ∈ S, r.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u)
    (hS_gap :
      ∀ r ∈ S, (match side with
        | .right => ¬ r.1 ∣ x
        | .left => ¬ r.1 ∣ u)) :
    ∃ p : {q // Nat.Prime q},
      (∀ r ∈ insert p S, r.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u) ∧
      (∀ r ∈ insert p S, (match side with
        | .right => ¬ r.1 ∣ x
        | .left => ¬ r.1 ∣ u)) := by
  cases side with
  | right =>
      rcases exists_boundaryPrime_dvd_gap_of_cfbRc_primitive_prime_boundaryDiffPow_of_coprime
          (side := .right) (d := d) (x := x) (u := u)
          hd_prime hd_ge hx hu hcop hpnd with
        ⟨p, hp_dvd, hp_gap⟩
      exact ⟨p,
        boundary_dvd_on_insert_of_boundary_dvd_and_witness
          (side := .right) (S := S) (d := d) (x := x) (u := u) p hS_dvd hp_dvd,
        boundary_gap_on_insert_of_boundary_gap_and_witness
          (side := .right) (S := S) (x := x) (u := u) p hS_gap hp_gap⟩
  | left =>
      rcases exists_boundaryPrime_dvd_gap_of_cfbRc_primitive_prime_boundaryDiffPow_of_coprime
          (side := .left) (d := d) (x := x) (u := u)
          hd_prime hd_ge hx hu hcop hpnd with
        ⟨p, hp_dvd, hp_gap⟩
      exact ⟨p,
        boundary_dvd_on_insert_of_boundary_dvd_and_witness
          (side := .left) (S := S) (d := d) (x := x) (u := u) p hS_dvd hp_dvd,
        boundary_gap_on_insert_of_boundary_gap_and_witness
          (side := .left) (S := S) (x := x) (u := u) p hS_gap hp_gap⟩

/--
RH-N22: `boundaryCyclotomicPrimeCore` 側の local-zero 仮定から witness local-zero を復元。

`hlocal_core`（core 除法だけを前提にした local-zero 仮定）から、
`boundaryDiffPow` 除法 + gap 非除法を前提にした
`hlocal_witness` 形式へ落とす。
-/
theorem boundary_hlocal_witness_of_boundaryCore_local_zero
    (side : DkMath.CFBRC.BoundarySide)
    {d x u : ℕ} {σ t : ℝ}
    (hlocal_core :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
          hopcPrimeLocalContribution p.1 σ t = 0) :
    ∀ p : {q // Nat.Prime q},
      p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
        (match side with
          | .right => ¬ p.1 ∣ x
          | .left => ¬ p.1 ∣ u) →
        hopcPrimeLocalContribution p.1 σ t = 0 := by
  cases side with
  | right =>
      intro p hq_dvd hq_not_dvd_x
      have hq_dvd_core : p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore .right d x u := by
        have hq_dvd_core_nat : p.1 ∣ DkMath.CFBRC.cyclotomicPrimeCore d x u :=
          (DkMath.CFBRC.prime_dvd_sub_pow_iff_dvd_cyclotomicPrimeCore_nat
            (p := d) (x := x) (u := u) (q := p.1) p.2 hq_not_dvd_x).1
            (by simpa [DkMath.CFBRC.boundaryDiffPow] using hq_dvd)
        simpa [DkMath.CFBRC.boundaryCyclotomicPrimeCore] using hq_dvd_core_nat
      exact hlocal_core p hq_dvd_core
  | left =>
      intro p hq_dvd hq_not_dvd_u
      have hq_dvd_core : p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore .left d x u := by
        have hq_dvd_sub_swap : p.1 ∣ ((u + x) ^ d - x ^ d) := by
          simpa [DkMath.CFBRC.boundaryDiffPow, Nat.add_comm] using hq_dvd
        have hq_dvd_core_swap : p.1 ∣ DkMath.CFBRC.cyclotomicPrimeCore d u x :=
          (DkMath.CFBRC.prime_dvd_sub_pow_iff_dvd_cyclotomicPrimeCore_nat
            (p := d) (x := u) (u := x) (q := p.1) p.2 hq_not_dvd_u).1 hq_dvd_sub_swap
        simpa [DkMath.CFBRC.boundaryCyclotomicPrimeCore] using hq_dvd_core_swap
      exact hlocal_core p hq_dvd_core

/--
RH-N23: `w_p ≠ 0` の下で HOPC 局所寄与と factor 位相速度寄与を同一化。
-/
theorem hopcPrimeLocalContribution_eq_eulerZetaFactorPhaseVelLocal_of_nonzero
    {p : ℕ} {σ t : ℝ}
    (hp_ne : eulerZeta_exp_s_log_p_sub_one p σ t ≠ 0) :
    hopcPrimeLocalContribution p σ t = eulerZetaFactorPhaseVelLocal p σ t := by
  simpa [hopcPrimeLocalContribution_eq_log_sub_phaseVelLocal] using
    (phaseVel_eulerZetaFactorVerticalExp_eq_log_sub_phaseVelLocal
      (p := p) (σ := σ) (t := t) hp_ne).symm

/--
RH-N23: `w_p ≠ 0` と factor 位相速度寄与ゼロから HOPC 局所寄与ゼロを得る。
-/
theorem hopcPrimeLocalContribution_eq_zero_of_factorPhaseVelLocal_eq_zero_of_nonzero
    {p : ℕ} {σ t : ℝ}
    (hp_ne : eulerZeta_exp_s_log_p_sub_one p σ t ≠ 0)
    (hfactor0 : eulerZetaFactorPhaseVelLocal p σ t = 0) :
    hopcPrimeLocalContribution p σ t = 0 := by
  rw [hopcPrimeLocalContribution_eq_eulerZetaFactorPhaseVelLocal_of_nonzero
    (p := p) (σ := σ) (t := t) hp_ne]
  exact hfactor0

/--
RH-N25: `w_p ≠ 0` と HOPC 局所寄与ゼロから factor 位相速度寄与ゼロを得る。
-/
theorem eulerZetaFactorPhaseVelLocal_eq_zero_of_hopcPrimeLocalContribution_eq_zero_of_nonzero
    {p : ℕ} {σ t : ℝ}
    (hp_ne : eulerZeta_exp_s_log_p_sub_one p σ t ≠ 0)
    (hlocal0 : hopcPrimeLocalContribution p σ t = 0) :
    eulerZetaFactorPhaseVelLocal p σ t = 0 := by
  rw [← hopcPrimeLocalContribution_eq_eulerZetaFactorPhaseVelLocal_of_nonzero
    (p := p) (σ := σ) (t := t) hp_ne]
  exact hlocal0

/--
RH-N23: `boundaryCyclotomicPrimeCore` 側の factor 位相速度ゼロ仮定から `hlocal_core` を供給。
-/
theorem boundary_hlocal_core_of_boundaryCore_factorPhaseVelLocal_eq_zero
    (side : DkMath.CFBRC.BoundarySide)
    {d x u : ℕ} {σ t : ℝ}
    (hwnz_core :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hfactor_core0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
          eulerZetaFactorPhaseVelLocal p.1 σ t = 0) :
    ∀ p : {q // Nat.Prime q},
      p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
        hopcPrimeLocalContribution p.1 σ t = 0 := by
  intro p hp_core
  exact hopcPrimeLocalContribution_eq_zero_of_factorPhaseVelLocal_eq_zero_of_nonzero
    (p := p.1) (σ := σ) (t := t)
    (hwnz_core p hp_core)
    (hfactor_core0 p hp_core)

/--
RH-N25: `boundaryCyclotomicPrimeCore` 側の local-zero 仮定から `hfactor_core0` を供給。
-/
theorem boundary_hfactor_core0_of_boundaryCore_local_zero
    (side : DkMath.CFBRC.BoundarySide)
    {d x u : ℕ} {σ t : ℝ}
    (hwnz_core :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hlocal_core :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
          hopcPrimeLocalContribution p.1 σ t = 0) :
    ∀ p : {q // Nat.Prime q},
      p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
        eulerZetaFactorPhaseVelLocal p.1 σ t = 0 := by
  intro p hp_core
  exact eulerZetaFactorPhaseVelLocal_eq_zero_of_hopcPrimeLocalContribution_eq_zero_of_nonzero
    (p := p.1) (σ := σ) (t := t)
    (hwnz_core p hp_core)
    (hlocal_core p hp_core)

/--
RH-N26: `boundaryDiffPow` 側 local-zero 仮定から `hlocal_core` を供給。

`boundaryCyclotomicPrimeCore` が差冪を掛け因子として持つこと
`((x+u)^d-u^d)=x*core`, `((x+u)^d-x^d)=u*core` を使って、
core 除法を差冪除法へ持ち上げて local-zero を移送する。
-/
theorem boundary_hlocal_core_of_boundaryDiffPow_local_zero
    (side : DkMath.CFBRC.BoundarySide)
    {d x u : ℕ} {σ t : ℝ}
    (hlocal_diff0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          hopcPrimeLocalContribution p.1 σ t = 0) :
    ∀ p : {q // Nat.Prime q},
      p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
        hopcPrimeLocalContribution p.1 σ t = 0 := by
  cases side with
  | right =>
      intro p hp_core
      have hp_core' : p.1 ∣ DkMath.CFBRC.cyclotomicPrimeCore d x u := by
        simpa [DkMath.CFBRC.boundaryCyclotomicPrimeCore] using hp_core
      have hp_diff : p.1 ∣ DkMath.CFBRC.boundaryDiffPow .right d x u := by
        have hmul : p.1 ∣ x * DkMath.CFBRC.cyclotomicPrimeCore d x u :=
          dvd_mul_of_dvd_right hp_core' x
        have hsub :
            (x + u) ^ d - u ^ d = x * DkMath.CFBRC.cyclotomicPrimeCore d x u := by
          simpa using DkMath.CFBRC.sub_eq_mul_cyclotomicPrimeCore_nat d x u
        simpa [DkMath.CFBRC.boundaryDiffPow] using (hsub ▸ hmul)
      exact hlocal_diff0 p hp_diff
  | left =>
      intro p hp_core
      have hp_core' : p.1 ∣ DkMath.CFBRC.cyclotomicPrimeCore d u x := by
        simpa [DkMath.CFBRC.boundaryCyclotomicPrimeCore] using hp_core
      have hp_diff : p.1 ∣ DkMath.CFBRC.boundaryDiffPow .left d x u := by
        have hmul : p.1 ∣ u * DkMath.CFBRC.cyclotomicPrimeCore d u x :=
          dvd_mul_of_dvd_right hp_core' u
        have hsub :
            (u + x) ^ d - x ^ d = u * DkMath.CFBRC.cyclotomicPrimeCore d u x := by
          simpa using DkMath.CFBRC.sub_eq_mul_cyclotomicPrimeCore_nat d u x
        have hs : p.1 ∣ (u + x) ^ d - x ^ d := hsub ▸ hmul
        simpa [DkMath.CFBRC.boundaryDiffPow, Nat.add_comm] using hs
      exact hlocal_diff0 p hp_diff

/--
RH-N27: `boundaryDiffPow` 側の非零仮定から `hwnz_core` を供給。
-/
theorem boundary_hwnz_core_of_boundaryDiffPow_nonzero
    (side : DkMath.CFBRC.BoundarySide)
    {d x u : ℕ} {σ t : ℝ}
    (hwnz_diff :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0) :
    ∀ p : {q // Nat.Prime q},
      p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
        eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0 := by
  cases side with
  | right =>
      intro p hp_core
      have hp_core' : p.1 ∣ DkMath.CFBRC.cyclotomicPrimeCore d x u := by
        simpa [DkMath.CFBRC.boundaryCyclotomicPrimeCore] using hp_core
      have hp_diff : p.1 ∣ DkMath.CFBRC.boundaryDiffPow .right d x u := by
        have hmul : p.1 ∣ x * DkMath.CFBRC.cyclotomicPrimeCore d x u :=
          dvd_mul_of_dvd_right hp_core' x
        have hsub :
            (x + u) ^ d - u ^ d = x * DkMath.CFBRC.cyclotomicPrimeCore d x u := by
          simpa using DkMath.CFBRC.sub_eq_mul_cyclotomicPrimeCore_nat d x u
        simpa [DkMath.CFBRC.boundaryDiffPow] using (hsub ▸ hmul)
      exact hwnz_diff p hp_diff
  | left =>
      intro p hp_core
      have hp_core' : p.1 ∣ DkMath.CFBRC.cyclotomicPrimeCore d u x := by
        simpa [DkMath.CFBRC.boundaryCyclotomicPrimeCore] using hp_core
      have hp_diff : p.1 ∣ DkMath.CFBRC.boundaryDiffPow .left d x u := by
        have hmul : p.1 ∣ u * DkMath.CFBRC.cyclotomicPrimeCore d u x :=
          dvd_mul_of_dvd_right hp_core' u
        have hsub :
            (u + x) ^ d - x ^ d = u * DkMath.CFBRC.cyclotomicPrimeCore d u x := by
          simpa using DkMath.CFBRC.sub_eq_mul_cyclotomicPrimeCore_nat d u x
        have hs : p.1 ∣ (u + x) ^ d - x ^ d := hsub ▸ hmul
        simpa [DkMath.CFBRC.boundaryDiffPow, Nat.add_comm] using hs
      exact hwnz_diff p hp_diff

/--
RH-N27: `boundaryDiffPow` 側の factor 位相速度ゼロ仮定から `hlocal_diff0` を供給。
-/
theorem boundary_hlocal_diff0_of_boundaryDiffPow_factorPhaseVelLocal_eq_zero
    (side : DkMath.CFBRC.BoundarySide)
    {d x u : ℕ} {σ t : ℝ}
    (hwnz_diff :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hfactor_diff0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZetaFactorPhaseVelLocal p.1 σ t = 0) :
    ∀ p : {q // Nat.Prime q},
      p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
        hopcPrimeLocalContribution p.1 σ t = 0 := by
  intro p hp_dvd
  exact hopcPrimeLocalContribution_eq_zero_of_factorPhaseVelLocal_eq_zero_of_nonzero
    (p := p.1) (σ := σ) (t := t)
    (hwnz_diff p hp_dvd)
    (hfactor_diff0 p hp_dvd)

/--
RH-N12: `hS_lift` 段階供給を使った provider 構成補題。

`hS_nonzero` と `hwnz_witness` で `hS_lift` を組み立て、
別途供給された `hsum_lift` と合わせて provider record を返す。
-/
def boundaryInsertLocalLiftProvider_of_nonzero_on_S_and_witness
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hS_nonzero :
      ∀ r ∈ S, eulerZeta_exp_s_log_p_sub_one r.1 σ t ≠ 0)
    (hwnz_witness :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          (match side with
            | .right => ¬ p.1 ∣ x
            | .left => ¬ p.1 ∣ u) →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hsum_lift :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          (match side with
            | .right => ¬ p.1 ∣ x
            | .left => ¬ p.1 ∣ u) →
          hopcPrimeContributionSum (S := insert p S) σ t = 0) :
    BoundaryInsertLocalLiftProvider side S d x u σ t := by
  cases side with
  | right =>
      exact boundaryInsertLocalLiftProvider_of_split
        (side := .right) (S := S)
        (hS_lift := boundary_hS_lift_of_nonzero_on_S_and_witness
          (side := .right) (S := S) hS_nonzero hwnz_witness)
        (hsum_lift := hsum_lift)
  | left =>
      exact boundaryInsertLocalLiftProvider_of_split
        (side := .left) (S := S)
        (hS_lift := boundary_hS_lift_of_nonzero_on_S_and_witness
          (side := .left) (S := S) hS_nonzero hwnz_witness)
        (hsum_lift := hsum_lift)

/--
RH-N13: `hsum_lift` の段階供給補題（`S` 上 local=0 + witness local=0）。

`insert p S` 上の local contribution をゼロ化して、
`hopcPrimeContributionSum (insert p S) = 0` を組み立てる。
-/
theorem boundary_hsum_lift_of_local_zero_on_S_and_witness
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hS_local0 :
      ∀ r ∈ S, hopcPrimeLocalContribution r.1 σ t = 0)
    (hlocal_witness :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          (match side with
            | .right => ¬ p.1 ∣ x
            | .left => ¬ p.1 ∣ u) →
          hopcPrimeLocalContribution p.1 σ t = 0) :
    ∀ p : {q // Nat.Prime q},
      p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
        (match side with
          | .right => ¬ p.1 ∣ x
          | .left => ¬ p.1 ∣ u) →
        hopcPrimeContributionSum (S := insert p S) σ t = 0 := by
  cases side with
  | right =>
      intro p hq_dvd hq_not_dvd_x
      unfold hopcPrimeContributionSum
      refine Finset.sum_eq_zero ?_
      intro r hr
      rcases Finset.mem_insert.mp hr with hr_eq | hrS
      · have hp0 : hopcPrimeLocalContribution p.1 σ t = 0 :=
          hlocal_witness p hq_dvd hq_not_dvd_x
        simpa [hr_eq] using hp0
      · exact hS_local0 r hrS
  | left =>
      intro p hq_dvd hq_not_dvd_u
      unfold hopcPrimeContributionSum
      refine Finset.sum_eq_zero ?_
      intro r hr
      rcases Finset.mem_insert.mp hr with hr_eq | hrS
      · have hp0 : hopcPrimeLocalContribution p.1 σ t = 0 :=
          hlocal_witness p hq_dvd hq_not_dvd_u
        simpa [hr_eq] using hp0
      · exact hS_local0 r hrS

/--
RH-N13: nonzero/local-zero の段階供給を統合した provider 構成補題。

`hS_lift` は RH-N12 補題で、`hsum_lift` は RH-N13 補題で生成し、
`BoundaryInsertLocalLiftProvider` へ束ねる。
-/
def boundaryInsertLocalLiftProvider_of_nonzero_and_local_zero_on_S_and_witness
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hS_nonzero :
      ∀ r ∈ S, eulerZeta_exp_s_log_p_sub_one r.1 σ t ≠ 0)
    (hwnz_witness :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          (match side with
            | .right => ¬ p.1 ∣ x
            | .left => ¬ p.1 ∣ u) →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hS_local0 :
      ∀ r ∈ S, hopcPrimeLocalContribution r.1 σ t = 0)
    (hlocal_witness :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          (match side with
            | .right => ¬ p.1 ∣ x
            | .left => ¬ p.1 ∣ u) →
          hopcPrimeLocalContribution p.1 σ t = 0) :
    BoundaryInsertLocalLiftProvider side S d x u σ t := by
  cases side with
  | right =>
      exact boundaryInsertLocalLiftProvider_of_split
        (side := .right) (S := S)
        (hS_lift := boundary_hS_lift_of_nonzero_on_S_and_witness
          (side := .right) (S := S) hS_nonzero hwnz_witness)
        (hsum_lift := boundary_hsum_lift_of_local_zero_on_S_and_witness
          (side := .right) (S := S) hS_local0 hlocal_witness)
  | left =>
      exact boundaryInsertLocalLiftProvider_of_split
        (side := .left) (S := S)
        (hS_lift := boundary_hS_lift_of_nonzero_on_S_and_witness
          (side := .left) (S := S) hS_nonzero hwnz_witness)
        (hsum_lift := boundary_hsum_lift_of_local_zero_on_S_and_witness
          (side := .left) (S := S) hS_local0 hlocal_witness)

/--
RH-N17: boundary 除法情報つき `S` から provider を直接構成する wrapper。

`hS_nonzero` を `boundary_nonzero_on_S_of_boundary_dvd_and_gap` で生成し、
RH-N13 の段階供給統合 constructor へ接続する。
-/
def boundaryInsertLocalLiftProvider_of_boundary_dvd_and_gap_and_local_zero
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hS_dvd :
      ∀ r ∈ S, r.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u)
    (hS_gap :
      ∀ r ∈ S, (match side with
        | .right => ¬ r.1 ∣ x
        | .left => ¬ r.1 ∣ u))
    (hwnz_witness :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          (match side with
            | .right => ¬ p.1 ∣ x
            | .left => ¬ p.1 ∣ u) →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hS_local0 :
      ∀ r ∈ S, hopcPrimeLocalContribution r.1 σ t = 0)
    (hlocal_witness :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          (match side with
            | .right => ¬ p.1 ∣ x
            | .left => ¬ p.1 ∣ u) →
          hopcPrimeLocalContribution p.1 σ t = 0) :
    BoundaryInsertLocalLiftProvider side S d x u σ t := by
  cases side with
  | right =>
      exact boundaryInsertLocalLiftProvider_of_nonzero_and_local_zero_on_S_and_witness
        (side := .right) (S := S)
        (hS_nonzero := boundary_nonzero_on_S_of_boundary_dvd_and_gap
          (side := .right) (S := S) hS_dvd hS_gap hwnz_witness)
        (hwnz_witness := hwnz_witness)
        (hS_local0 := hS_local0)
        (hlocal_witness := hlocal_witness)
  | left =>
      exact boundaryInsertLocalLiftProvider_of_nonzero_and_local_zero_on_S_and_witness
        (side := .left) (S := S)
        (hS_nonzero := boundary_nonzero_on_S_of_boundary_dvd_and_gap
          (side := .left) (S := S) hS_dvd hS_gap hwnz_witness)
        (hwnz_witness := hwnz_witness)
        (hS_local0 := hS_local0)
        (hlocal_witness := hlocal_witness)

/--
RH-N21: `boundary_dvd + gap` から nonzero/local-zero を同時生成する簡約 wrapper。

`hS_local0` を要求せず、`hlocal_witness` から
`boundary_local_zero_on_S_of_boundary_dvd_and_gap` で自動生成して
RH-N17 wrapper へ委譲する。
-/
def boundaryInsertLocalLiftProvider_of_boundary_dvd_and_gap
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hS_dvd :
      ∀ r ∈ S, r.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u)
    (hS_gap :
      ∀ r ∈ S, (match side with
        | .right => ¬ r.1 ∣ x
        | .left => ¬ r.1 ∣ u))
    (hwnz_witness :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          (match side with
            | .right => ¬ p.1 ∣ x
            | .left => ¬ p.1 ∣ u) →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hlocal_witness :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          (match side with
            | .right => ¬ p.1 ∣ x
            | .left => ¬ p.1 ∣ u) →
          hopcPrimeLocalContribution p.1 σ t = 0) :
    BoundaryInsertLocalLiftProvider side S d x u σ t := by
  cases side with
  | right =>
      exact boundaryInsertLocalLiftProvider_of_boundary_dvd_and_gap_and_local_zero
        (side := .right) (S := S)
        (hS_dvd := hS_dvd)
        (hS_gap := hS_gap)
        (hwnz_witness := hwnz_witness)
        (hS_local0 := boundary_local_zero_on_S_of_boundary_dvd_and_gap
          (side := .right) (S := S) hS_dvd hS_gap hlocal_witness)
        (hlocal_witness := hlocal_witness)
  | left =>
      exact boundaryInsertLocalLiftProvider_of_boundary_dvd_and_gap_and_local_zero
        (side := .left) (S := S)
        (hS_dvd := hS_dvd)
        (hS_gap := hS_gap)
        (hwnz_witness := hwnz_witness)
        (hS_local0 := boundary_local_zero_on_S_of_boundary_dvd_and_gap
          (side := .left) (S := S) hS_dvd hS_gap hlocal_witness)
        (hlocal_witness := hlocal_witness)

/--
RH-N22: `boundaryCore` 側 witness 仮定から provider を構成する wrapper。

`boundaryDiffPow` 側 witness 仮定は内部で復元し、
RH-N21 の前提簡約 wrapper へ委譲する。
-/
def boundaryInsertLocalLiftProvider_of_boundary_dvd_and_gap_of_boundaryCore_witness
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hS_dvd :
      ∀ r ∈ S, r.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u)
    (hS_gap :
      ∀ r ∈ S, (match side with
        | .right => ¬ r.1 ∣ x
        | .left => ¬ r.1 ∣ u))
    (hwnz_core :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hlocal_core :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
          hopcPrimeLocalContribution p.1 σ t = 0) :
    BoundaryInsertLocalLiftProvider side S d x u σ t := by
  cases side with
  | right =>
      exact boundaryInsertLocalLiftProvider_of_boundary_dvd_and_gap
        (side := .right) (S := S)
        (hS_dvd := hS_dvd)
        (hS_gap := hS_gap)
        (hwnz_witness := boundary_hwnz_witness_of_boundaryCore_nonzero
          (side := .right) (d := d) (x := x) (u := u) (σ := σ) (t := t) hwnz_core)
        (hlocal_witness := boundary_hlocal_witness_of_boundaryCore_local_zero
          (side := .right) (d := d) (x := x) (u := u) (σ := σ) (t := t) hlocal_core)
  | left =>
      exact boundaryInsertLocalLiftProvider_of_boundary_dvd_and_gap
        (side := .left) (S := S)
        (hS_dvd := hS_dvd)
        (hS_gap := hS_gap)
        (hwnz_witness := boundary_hwnz_witness_of_boundaryCore_nonzero
          (side := .left) (d := d) (x := x) (u := u) (σ := σ) (t := t) hwnz_core)
        (hlocal_witness := boundary_hlocal_witness_of_boundaryCore_local_zero
          (side := .left) (d := d) (x := x) (u := u) (σ := σ) (t := t) hlocal_core)

/--
RH-N23: `boundaryCore` 上の factor 位相速度ゼロ仮定から provider を構成する wrapper。

`hlocal_core` は
`boundary_hlocal_core_of_boundaryCore_factorPhaseVelLocal_eq_zero`
で自動生成し、RH-N22 wrapper へ委譲する。
-/
def
    boundaryInsertLocalLiftProvider_of_boundary_dvd_gap_of_boundaryCore_factor0
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hS_dvd :
      ∀ r ∈ S, r.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u)
    (hS_gap :
      ∀ r ∈ S, (match side with
        | .right => ¬ r.1 ∣ x
        | .left => ¬ r.1 ∣ u))
    (hwnz_core :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hfactor_core0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
          eulerZetaFactorPhaseVelLocal p.1 σ t = 0) :
    BoundaryInsertLocalLiftProvider side S d x u σ t := by
  exact boundaryInsertLocalLiftProvider_of_boundary_dvd_and_gap_of_boundaryCore_witness
    (side := side) (S := S)
    (hS_dvd := hS_dvd)
    (hS_gap := hS_gap)
    (hwnz_core := hwnz_core)
    (hlocal_core := boundary_hlocal_core_of_boundaryCore_factorPhaseVelLocal_eq_zero
      (side := side) (d := d) (x := x) (u := u) (σ := σ) (t := t)
      hwnz_core hfactor_core0)

/--
RH-N26: `boundaryDiffPow` 側 local-zero 仮定から provider を構成する wrapper。

`hlocal_core` は
`boundary_hlocal_core_of_boundaryDiffPow_local_zero`
で自動生成し、RH-N25 local0 入口へ委譲する。
-/
def boundaryInsertLocalLiftProvider_of_boundary_dvd_gap_of_boundaryDiffPow_local0
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hS_dvd :
      ∀ r ∈ S, r.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u)
    (hS_gap :
      ∀ r ∈ S, (match side with
        | .right => ¬ r.1 ∣ x
        | .left => ¬ r.1 ∣ u))
    (hwnz_core :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hlocal_diff0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          hopcPrimeLocalContribution p.1 σ t = 0) :
    BoundaryInsertLocalLiftProvider side S d x u σ t := by
  exact boundaryInsertLocalLiftProvider_of_boundary_dvd_and_gap_of_boundaryCore_witness
    (side := side) (S := S)
    (hS_dvd := hS_dvd)
    (hS_gap := hS_gap)
    (hwnz_core := hwnz_core)
    (hlocal_core := boundary_hlocal_core_of_boundaryDiffPow_local_zero
      (side := side) (d := d) (x := x) (u := u) (σ := σ) (t := t) hlocal_diff0)

/--
RH-N7: provider record 版 wrapper（`BoundarySide` + small finite-set）。

`BoundaryInsertLocalLiftProvider` を受け取り、
split 版 bridge へ委譲して停留点存在を返す。
-/
theorem exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_provider
    (side : DkMath.CFBRC.BoundarySide)
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
  cases side with
  | right =>
      exact
        exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_local_split
          (side := .right) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
          hd_prime hd_ge hx hu hcop hpnd provider.hS_lift provider.hsum_lift
  | left =>
      exact
        exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_local_split
          (side := .left) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
          hd_prime hd_ge hx hu hcop hpnd provider.hS_lift provider.hsum_lift

/--
OP-004: provider record + 曲率 provider 版の非退化停留 bridge。

`BoundaryInsertLocalLiftProvider`（停留供給）と
`BoundaryInsertPhaseCurvProvider`（曲率非零供給）を分離したまま受け取り、
`insert p S` 観測器での非退化停留点存在を返す。
-/
theorem exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_provider_and_phaseCurvProvider
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : match side with
      | .right => ¬ d ∣ x
      | .left => ¬ d ∣ u)
    (provider : BoundaryInsertLocalLiftProvider side S d x u σ t)
    (curvProvider : BoundaryInsertPhaseCurvProvider side S d x u σ t) :
    ∃ p : {q // Nat.Prime q},
      DkMath.RH.nondegenerateStationaryAt
        (fun v : ℝ => eulerZetaFinite_onVertical (insert p S) σ v) t := by
  cases side with
  | right =>
      exact
        exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_local_split_and_phaseCurv
          (side := .right) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
          hd_prime hd_ge hx hu hcop hpnd
          provider.hS_lift provider.hsum_lift curvProvider.hcurv_lift
  | left =>
      exact
        exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_local_split_and_phaseCurv
          (side := .left) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
          hd_prime hd_ge hx hu hcop hpnd
          provider.hS_lift provider.hsum_lift curvProvider.hcurv_lift

/--
OP-004: `boundaryCore` の factor 位相速度ゼロ仮定 + 曲率非零仮定から、
small finite-set 非退化停留点存在へ接続する高位 wrapper。
-/
theorem
    exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryCore_factor0_and_phaseCurv
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : match side with
      | .right => ¬ d ∣ x
      | .left => ¬ d ∣ u)
    (hS_dvd :
      ∀ r ∈ S, r.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u)
    (hS_gap :
      ∀ r ∈ S, (match side with
        | .right => ¬ r.1 ∣ x
        | .left => ¬ r.1 ∣ u))
    (hwnz_core :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hfactor_core0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
          eulerZetaFactorPhaseVelLocal p.1 σ t = 0)
    (hcurv_lift :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          (match side with
            | .right => ¬ p.1 ∣ x
            | .left => ¬ p.1 ∣ u) →
          DkMath.RH.phaseCurv
            (fun v : ℝ => eulerZetaFinite_onVertical (insert p S) σ v) t ≠ 0) :
    ∃ p : {q // Nat.Prime q},
      DkMath.RH.nondegenerateStationaryAt
        (fun v : ℝ => eulerZetaFinite_onVertical (insert p S) σ v) t := by
  cases side with
  | right =>
      exact
        exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_provider_and_phaseCurvProvider
          (side := .right) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
          hd_prime hd_ge hx hu hcop hpnd
          (boundaryInsertLocalLiftProvider_of_boundary_dvd_gap_of_boundaryCore_factor0
            (side := .right) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
            hS_dvd hS_gap hwnz_core hfactor_core0)
          (boundaryInsertPhaseCurvProvider_of_split
            (side := .right) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
            hcurv_lift)
  | left =>
      exact
        exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_provider_and_phaseCurvProvider
          (side := .left) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
          hd_prime hd_ge hx hu hcop hpnd
          (boundaryInsertLocalLiftProvider_of_boundary_dvd_gap_of_boundaryCore_factor0
            (side := .left) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
            hS_dvd hS_gap hwnz_core hfactor_core0)
          (boundaryInsertPhaseCurvProvider_of_split
            (side := .left) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
            hcurv_lift)

/--
OP-004: `boundaryCore` factor0 + 曲率非零仮定から、
singleton 非退化停留点存在へ接続する wrapper。
-/
theorem
    exists_nondegenerateStationaryAt_singleton_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryCore_factor0_and_phaseCurv
    (side : DkMath.CFBRC.BoundarySide)
    {d x u : ℕ} {σ t : ℝ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : match side with
      | .right => ¬ d ∣ x
      | .left => ¬ d ∣ u)
    (hwnz_core :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hfactor_core0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
          eulerZetaFactorPhaseVelLocal p.1 σ t = 0)
    (hcurv_local0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          (match side with
            | .right => ¬ p.1 ∣ x
            | .left => ¬ p.1 ∣ u) →
          DkMath.RH.phaseCurv
            (fun v : ℝ => eulerZetaFinite_onVertical ({p} : Finset {q // Nat.Prime q}) σ v) t ≠ 0) :
    ∃ p : {q // Nat.Prime q},
      DkMath.RH.nondegenerateStationaryAt
        (fun v : ℝ =>
          eulerZetaFinite_onVertical ({p} : Finset {q // Nat.Prime q}) σ v) t := by
  cases side with
  | right =>
      have hS_dvd :
          ∀ r ∈ (∅ : Finset {q // Nat.Prime q}),
            r.1 ∣ DkMath.CFBRC.boundaryDiffPow .right d x u := by
        intro r hr
        simp at hr
      have hS_gap :
          ∀ r ∈ (∅ : Finset {q // Nat.Prime q}), ¬ r.1 ∣ x := by
        intro r hr
        simp at hr
      have hcurv_lift :
          ∀ p : {q // Nat.Prime q},
            p.1 ∣ DkMath.CFBRC.boundaryDiffPow .right d x u →
              ¬ p.1 ∣ x →
              DkMath.RH.phaseCurv
                (fun v : ℝ =>
                  eulerZetaFinite_onVertical (insert p (∅ : Finset {q // Nat.Prime q})) σ v) t ≠ 0 := by
        intro p hp_dvd hp_gap
        simpa using hcurv_local0 p hp_dvd hp_gap
      simpa using
        (exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryCore_factor0_and_phaseCurv
          (side := .right) (S := (∅ : Finset {q // Nat.Prime q}))
          (d := d) (x := x) (u := u) (σ := σ) (t := t)
          hd_prime hd_ge hx hu hcop hpnd
          hS_dvd hS_gap hwnz_core hfactor_core0 hcurv_lift)
  | left =>
      have hS_dvd :
          ∀ r ∈ (∅ : Finset {q // Nat.Prime q}),
            r.1 ∣ DkMath.CFBRC.boundaryDiffPow .left d x u := by
        intro r hr
        simp at hr
      have hS_gap :
          ∀ r ∈ (∅ : Finset {q // Nat.Prime q}), ¬ r.1 ∣ u := by
        intro r hr
        simp at hr
      have hcurv_lift :
          ∀ p : {q // Nat.Prime q},
            p.1 ∣ DkMath.CFBRC.boundaryDiffPow .left d x u →
              ¬ p.1 ∣ u →
              DkMath.RH.phaseCurv
                (fun v : ℝ =>
                  eulerZetaFinite_onVertical (insert p (∅ : Finset {q // Nat.Prime q})) σ v) t ≠ 0 := by
        intro p hp_dvd hp_gap
        simpa using hcurv_local0 p hp_dvd hp_gap
      simpa using
        (exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryCore_factor0_and_phaseCurv
          (side := .left) (S := (∅ : Finset {q // Nat.Prime q}))
          (d := d) (x := x) (u := u) (σ := σ) (t := t)
          hd_prime hd_ge hx hu hcop hpnd
          hS_dvd hS_gap hwnz_core hfactor_core0 hcurv_lift)

/--
OP-004: `boundaryCore` local-zero + 曲率非零仮定から、
small finite-set 非退化停留点存在へ接続する高位 wrapper。
-/
theorem
    exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryCore_local0_and_phaseCurv
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : match side with
      | .right => ¬ d ∣ x
      | .left => ¬ d ∣ u)
    (hS_dvd :
      ∀ r ∈ S, r.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u)
    (hS_gap :
      ∀ r ∈ S, (match side with
        | .right => ¬ r.1 ∣ x
        | .left => ¬ r.1 ∣ u))
    (hwnz_core :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hlocal_core :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
          hopcPrimeLocalContribution p.1 σ t = 0)
    (hcurv_lift :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          (match side with
            | .right => ¬ p.1 ∣ x
            | .left => ¬ p.1 ∣ u) →
          DkMath.RH.phaseCurv
            (fun v : ℝ => eulerZetaFinite_onVertical (insert p S) σ v) t ≠ 0) :
    ∃ p : {q // Nat.Prime q},
      DkMath.RH.nondegenerateStationaryAt
        (fun v : ℝ => eulerZetaFinite_onVertical (insert p S) σ v) t := by
  cases side with
  | right =>
      exact
        exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryCore_factor0_and_phaseCurv
          (side := .right) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
          hd_prime hd_ge hx hu hcop hpnd hS_dvd hS_gap hwnz_core
          (boundary_hfactor_core0_of_boundaryCore_local_zero
            (side := .right) (d := d) (x := x) (u := u) (σ := σ) (t := t)
            hwnz_core hlocal_core)
          hcurv_lift
  | left =>
      exact
        exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryCore_factor0_and_phaseCurv
          (side := .left) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
          hd_prime hd_ge hx hu hcop hpnd hS_dvd hS_gap hwnz_core
          (boundary_hfactor_core0_of_boundaryCore_local_zero
            (side := .left) (d := d) (x := x) (u := u) (σ := σ) (t := t)
            hwnz_core hlocal_core)
          hcurv_lift

/--
OP-004: `boundaryCore` local-zero + 曲率非零仮定から、
singleton 非退化停留点存在へ接続する wrapper。
-/
theorem
    exists_nondegenerateStationaryAt_singleton_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryCore_local0_and_phaseCurv
    (side : DkMath.CFBRC.BoundarySide)
    {d x u : ℕ} {σ t : ℝ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : match side with
      | .right => ¬ d ∣ x
      | .left => ¬ d ∣ u)
    (hwnz_core :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hlocal_core :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
          hopcPrimeLocalContribution p.1 σ t = 0)
    (hcurv_local0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          (match side with
            | .right => ¬ p.1 ∣ x
            | .left => ¬ p.1 ∣ u) →
          DkMath.RH.phaseCurv
            (fun v : ℝ => eulerZetaFinite_onVertical ({p} : Finset {q // Nat.Prime q}) σ v) t ≠ 0) :
    ∃ p : {q // Nat.Prime q},
      DkMath.RH.nondegenerateStationaryAt
        (fun v : ℝ =>
          eulerZetaFinite_onVertical ({p} : Finset {q // Nat.Prime q}) σ v) t := by
  cases side with
  | right =>
      exact
        exists_nondegenerateStationaryAt_singleton_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryCore_factor0_and_phaseCurv
          (side := .right) (d := d) (x := x) (u := u) (σ := σ) (t := t)
          hd_prime hd_ge hx hu hcop hpnd hwnz_core
          (boundary_hfactor_core0_of_boundaryCore_local_zero
            (side := .right) (d := d) (x := x) (u := u) (σ := σ) (t := t)
            hwnz_core hlocal_core)
          hcurv_local0
  | left =>
      exact
        exists_nondegenerateStationaryAt_singleton_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryCore_factor0_and_phaseCurv
          (side := .left) (d := d) (x := x) (u := u) (σ := σ) (t := t)
          hd_prime hd_ge hx hu hcop hpnd hwnz_core
          (boundary_hfactor_core0_of_boundaryCore_local_zero
            (side := .left) (d := d) (x := x) (u := u) (σ := σ) (t := t)
            hwnz_core hlocal_core)
          hcurv_local0

/--
OP-004: `boundaryDiffPow` local-zero + 曲率非零仮定から、
small finite-set 非退化停留点存在へ接続する高位 wrapper。
-/
theorem
    exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryDiffPow_local0_and_phaseCurv
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : match side with
      | .right => ¬ d ∣ x
      | .left => ¬ d ∣ u)
    (hS_dvd :
      ∀ r ∈ S, r.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u)
    (hS_gap :
      ∀ r ∈ S, (match side with
        | .right => ¬ r.1 ∣ x
        | .left => ¬ r.1 ∣ u))
    (hwnz_core :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hlocal_diff0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          hopcPrimeLocalContribution p.1 σ t = 0)
    (hcurv_lift :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          (match side with
            | .right => ¬ p.1 ∣ x
            | .left => ¬ p.1 ∣ u) →
          DkMath.RH.phaseCurv
            (fun v : ℝ => eulerZetaFinite_onVertical (insert p S) σ v) t ≠ 0) :
    ∃ p : {q // Nat.Prime q},
      DkMath.RH.nondegenerateStationaryAt
        (fun v : ℝ => eulerZetaFinite_onVertical (insert p S) σ v) t := by
  cases side with
  | right =>
      exact
        exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryCore_local0_and_phaseCurv
          (side := .right) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
          hd_prime hd_ge hx hu hcop hpnd hS_dvd hS_gap hwnz_core
          (boundary_hlocal_core_of_boundaryDiffPow_local_zero
            (side := .right) (d := d) (x := x) (u := u) (σ := σ) (t := t) hlocal_diff0)
          hcurv_lift
  | left =>
      exact
        exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryCore_local0_and_phaseCurv
          (side := .left) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
          hd_prime hd_ge hx hu hcop hpnd hS_dvd hS_gap hwnz_core
          (boundary_hlocal_core_of_boundaryDiffPow_local_zero
            (side := .left) (d := d) (x := x) (u := u) (σ := σ) (t := t) hlocal_diff0)
          hcurv_lift

/--
OP-004: `boundaryDiffPow` local-zero + 曲率非零仮定から、
singleton 非退化停留点存在へ接続する wrapper。
-/
theorem
    exists_nondegenerateStationaryAt_singleton_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryDiffPow_local0_and_phaseCurv
    (side : DkMath.CFBRC.BoundarySide)
    {d x u : ℕ} {σ t : ℝ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : match side with
      | .right => ¬ d ∣ x
      | .left => ¬ d ∣ u)
    (hwnz_core :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hlocal_diff0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          hopcPrimeLocalContribution p.1 σ t = 0)
    (hcurv_local0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          (match side with
            | .right => ¬ p.1 ∣ x
            | .left => ¬ p.1 ∣ u) →
          DkMath.RH.phaseCurv
            (fun v : ℝ => eulerZetaFinite_onVertical ({p} : Finset {q // Nat.Prime q}) σ v) t ≠ 0) :
    ∃ p : {q // Nat.Prime q},
      DkMath.RH.nondegenerateStationaryAt
        (fun v : ℝ =>
          eulerZetaFinite_onVertical ({p} : Finset {q // Nat.Prime q}) σ v) t := by
  cases side with
  | right =>
      exact
        exists_nondegenerateStationaryAt_singleton_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryCore_local0_and_phaseCurv
          (side := .right) (d := d) (x := x) (u := u) (σ := σ) (t := t)
          hd_prime hd_ge hx hu hcop hpnd hwnz_core
          (boundary_hlocal_core_of_boundaryDiffPow_local_zero
            (side := .right) (d := d) (x := x) (u := u) (σ := σ) (t := t) hlocal_diff0)
          hcurv_local0
  | left =>
      exact
        exists_nondegenerateStationaryAt_singleton_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryCore_local0_and_phaseCurv
          (side := .left) (d := d) (x := x) (u := u) (σ := σ) (t := t)
          hd_prime hd_ge hx hu hcop hpnd hwnz_core
          (boundary_hlocal_core_of_boundaryDiffPow_local_zero
            (side := .left) (d := d) (x := x) (u := u) (σ := σ) (t := t) hlocal_diff0)
          hcurv_local0

/--
OP-004: `boundaryDiffPow` factor0 + 曲率非零仮定から、
small finite-set 非退化停留点存在へ接続する高位 wrapper。
-/
theorem
    exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryDiffPow_factor0_and_phaseCurv
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : match side with
      | .right => ¬ d ∣ x
      | .left => ¬ d ∣ u)
    (hS_dvd :
      ∀ r ∈ S, r.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u)
    (hS_gap :
      ∀ r ∈ S, (match side with
        | .right => ¬ r.1 ∣ x
        | .left => ¬ r.1 ∣ u))
    (hwnz_diff :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hfactor_diff0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZetaFactorPhaseVelLocal p.1 σ t = 0)
    (hcurv_lift :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          (match side with
            | .right => ¬ p.1 ∣ x
            | .left => ¬ p.1 ∣ u) →
          DkMath.RH.phaseCurv
            (fun v : ℝ => eulerZetaFinite_onVertical (insert p S) σ v) t ≠ 0) :
    ∃ p : {q // Nat.Prime q},
      DkMath.RH.nondegenerateStationaryAt
        (fun v : ℝ => eulerZetaFinite_onVertical (insert p S) σ v) t := by
  cases side with
  | right =>
      exact
        exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryDiffPow_local0_and_phaseCurv
          (side := .right) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
          hd_prime hd_ge hx hu hcop hpnd hS_dvd hS_gap
          (boundary_hwnz_core_of_boundaryDiffPow_nonzero
            (side := .right) (d := d) (x := x) (u := u) (σ := σ) (t := t) hwnz_diff)
          (boundary_hlocal_diff0_of_boundaryDiffPow_factorPhaseVelLocal_eq_zero
            (side := .right) (d := d) (x := x) (u := u) (σ := σ) (t := t)
            hwnz_diff hfactor_diff0)
          hcurv_lift
  | left =>
      exact
        exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryDiffPow_local0_and_phaseCurv
          (side := .left) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
          hd_prime hd_ge hx hu hcop hpnd hS_dvd hS_gap
          (boundary_hwnz_core_of_boundaryDiffPow_nonzero
            (side := .left) (d := d) (x := x) (u := u) (σ := σ) (t := t) hwnz_diff)
          (boundary_hlocal_diff0_of_boundaryDiffPow_factorPhaseVelLocal_eq_zero
            (side := .left) (d := d) (x := x) (u := u) (σ := σ) (t := t)
            hwnz_diff hfactor_diff0)
          hcurv_lift

/--
OP-004: `boundaryDiffPow` factor0 + 曲率非零仮定から、
singleton 非退化停留点存在へ接続する wrapper。
-/
theorem
    exists_nondegenerateStationaryAt_singleton_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryDiffPow_factor0_and_phaseCurv
    (side : DkMath.CFBRC.BoundarySide)
    {d x u : ℕ} {σ t : ℝ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : match side with
      | .right => ¬ d ∣ x
      | .left => ¬ d ∣ u)
    (hwnz_diff :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hfactor_diff0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZetaFactorPhaseVelLocal p.1 σ t = 0)
    (hcurv_local0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          (match side with
            | .right => ¬ p.1 ∣ x
            | .left => ¬ p.1 ∣ u) →
          DkMath.RH.phaseCurv
            (fun v : ℝ => eulerZetaFinite_onVertical ({p} : Finset {q // Nat.Prime q}) σ v) t ≠ 0) :
    ∃ p : {q // Nat.Prime q},
      DkMath.RH.nondegenerateStationaryAt
        (fun v : ℝ =>
          eulerZetaFinite_onVertical ({p} : Finset {q // Nat.Prime q}) σ v) t := by
  cases side with
  | right =>
      exact
        exists_nondegenerateStationaryAt_singleton_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryDiffPow_local0_and_phaseCurv
          (side := .right) (d := d) (x := x) (u := u) (σ := σ) (t := t)
          hd_prime hd_ge hx hu hcop hpnd
          (boundary_hwnz_core_of_boundaryDiffPow_nonzero
            (side := .right) (d := d) (x := x) (u := u) (σ := σ) (t := t) hwnz_diff)
          (boundary_hlocal_diff0_of_boundaryDiffPow_factorPhaseVelLocal_eq_zero
            (side := .right) (d := d) (x := x) (u := u) (σ := σ) (t := t)
            hwnz_diff hfactor_diff0)
          hcurv_local0
  | left =>
      exact
        exists_nondegenerateStationaryAt_singleton_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryDiffPow_local0_and_phaseCurv
          (side := .left) (d := d) (x := x) (u := u) (σ := σ) (t := t)
          hd_prime hd_ge hx hu hcop hpnd
          (boundary_hwnz_core_of_boundaryDiffPow_nonzero
            (side := .left) (d := d) (x := x) (u := u) (σ := σ) (t := t) hwnz_diff)
          (boundary_hlocal_diff0_of_boundaryDiffPow_factorPhaseVelLocal_eq_zero
            (side := .left) (d := d) (x := x) (u := u) (σ := σ) (t := t)
            hwnz_diff hfactor_diff0)
          hcurv_local0

/--
RH-N24: `boundaryCore` の factor 位相速度ゼロ仮定から
small finite-set 停留点存在へ接続する高位 wrapper。

provider は RH-N23 の
`boundaryInsertLocalLiftProvider_of_boundary_dvd_gap_of_boundaryCore_factor0`
で自動構成する。
-/
theorem
    exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryCore_factor0
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : match side with
      | .right => ¬ d ∣ x
      | .left => ¬ d ∣ u)
    (hS_dvd :
      ∀ r ∈ S, r.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u)
    (hS_gap :
      ∀ r ∈ S, (match side with
        | .right => ¬ r.1 ∣ x
        | .left => ¬ r.1 ∣ u))
    (hwnz_core :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hfactor_core0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
          eulerZetaFactorPhaseVelLocal p.1 σ t = 0) :
    ∃ p : {q // Nat.Prime q},
      DkMath.RH.stationaryAt
        (fun v : ℝ => eulerZetaFinite_onVertical (insert p S) σ v) t := by
  cases side with
  | right =>
      exact exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_provider
        (side := .right) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
        hd_prime hd_ge hx hu hcop hpnd
        (boundaryInsertLocalLiftProvider_of_boundary_dvd_gap_of_boundaryCore_factor0
          (side := .right) (S := S)
          (hS_dvd := hS_dvd)
          (hS_gap := hS_gap)
          (hwnz_core := hwnz_core)
          (hfactor_core0 := hfactor_core0))
  | left =>
      exact exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_provider
        (side := .left) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
        hd_prime hd_ge hx hu hcop hpnd
        (boundaryInsertLocalLiftProvider_of_boundary_dvd_gap_of_boundaryCore_factor0
          (side := .left) (S := S)
          (hS_dvd := hS_dvd)
          (hS_gap := hS_gap)
          (hwnz_core := hwnz_core)
          (hfactor_core0 := hfactor_core0))

/--
RH-N24: `boundaryCore` factor0 仮定から singleton 停留点存在へ接続する wrapper。

`S = ∅` として RH-N24 insert 版を適用する。
-/
theorem
    exists_stationaryAt_singleton_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryCore_factor0
    (side : DkMath.CFBRC.BoundarySide)
    {d x u : ℕ} {σ t : ℝ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : match side with
      | .right => ¬ d ∣ x
      | .left => ¬ d ∣ u)
    (hwnz_core :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hfactor_core0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
          eulerZetaFactorPhaseVelLocal p.1 σ t = 0) :
    ∃ p : {q // Nat.Prime q},
      DkMath.RH.stationaryAt
        (fun v : ℝ =>
          eulerZetaFinite_onVertical ({p} : Finset {q // Nat.Prime q}) σ v) t := by
  cases side with
  | right =>
      have hS_dvd :
          ∀ r ∈ (∅ : Finset {q // Nat.Prime q}),
            r.1 ∣ DkMath.CFBRC.boundaryDiffPow .right d x u := by
        intro r hr
        simp at hr
      have hS_gap :
          ∀ r ∈ (∅ : Finset {q // Nat.Prime q}), ¬ r.1 ∣ x := by
        intro r hr
        simp at hr
      simpa using
        (exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryCore_factor0
          (side := .right) (S := (∅ : Finset {q // Nat.Prime q}))
          (d := d) (x := x) (u := u) (σ := σ) (t := t)
          hd_prime hd_ge hx hu hcop hpnd hS_dvd hS_gap hwnz_core hfactor_core0)
  | left =>
      have hS_dvd :
          ∀ r ∈ (∅ : Finset {q // Nat.Prime q}),
            r.1 ∣ DkMath.CFBRC.boundaryDiffPow .left d x u := by
        intro r hr
        simp at hr
      have hS_gap :
          ∀ r ∈ (∅ : Finset {q // Nat.Prime q}), ¬ r.1 ∣ u := by
        intro r hr
        simp at hr
      simpa using
        (exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryCore_factor0
          (side := .left) (S := (∅ : Finset {q // Nat.Prime q}))
          (d := d) (x := x) (u := u) (σ := σ) (t := t)
          hd_prime hd_ge hx hu hcop hpnd hS_dvd hS_gap hwnz_core hfactor_core0)

/--
RH-N25: `boundaryCore` local-zero 仮定から
small finite-set 停留点存在へ接続する高位 wrapper。

`hfactor_core0` は
`boundary_hfactor_core0_of_boundaryCore_local_zero`
で自動生成し、RH-N24 wrapper へ委譲する。
-/
theorem
    exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryCore_local0
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : match side with
      | .right => ¬ d ∣ x
      | .left => ¬ d ∣ u)
    (hS_dvd :
      ∀ r ∈ S, r.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u)
    (hS_gap :
      ∀ r ∈ S, (match side with
        | .right => ¬ r.1 ∣ x
        | .left => ¬ r.1 ∣ u))
    (hwnz_core :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hlocal_core :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
          hopcPrimeLocalContribution p.1 σ t = 0) :
    ∃ p : {q // Nat.Prime q},
      DkMath.RH.stationaryAt
        (fun v : ℝ => eulerZetaFinite_onVertical (insert p S) σ v) t := by
  cases side with
  | right =>
      exact
        exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryCore_factor0
          (side := .right) (S := S)
          (d := d) (x := x) (u := u) (σ := σ) (t := t)
          hd_prime hd_ge hx hu hcop hpnd hS_dvd hS_gap hwnz_core
          (boundary_hfactor_core0_of_boundaryCore_local_zero
            (side := .right) (d := d) (x := x) (u := u) (σ := σ) (t := t)
            hwnz_core hlocal_core)
  | left =>
      exact
        exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryCore_factor0
          (side := .left) (S := S)
          (d := d) (x := x) (u := u) (σ := σ) (t := t)
          hd_prime hd_ge hx hu hcop hpnd hS_dvd hS_gap hwnz_core
          (boundary_hfactor_core0_of_boundaryCore_local_zero
            (side := .left) (d := d) (x := x) (u := u) (σ := σ) (t := t)
            hwnz_core hlocal_core)

local notation "existsStatSingletonBoundaryCoreFactor0" =>
  exists_stationaryAt_singleton_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryCore_factor0

/--
RH-N25: `boundaryCore` local-zero 仮定から singleton 停留点存在へ接続する wrapper。
-/
theorem
    exists_stationaryAt_singleton_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryCore_local0
    (side : DkMath.CFBRC.BoundarySide)
    {d x u : ℕ} {σ t : ℝ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : match side with
      | .right => ¬ d ∣ x
      | .left => ¬ d ∣ u)
    (hwnz_core :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hlocal_core :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
          hopcPrimeLocalContribution p.1 σ t = 0) :
    ∃ p : {q // Nat.Prime q},
      DkMath.RH.stationaryAt
        (fun v : ℝ =>
          eulerZetaFinite_onVertical ({p} : Finset {q // Nat.Prime q}) σ v) t := by
  cases side with
  | right =>
      have hstat :=
        existsStatSingletonBoundaryCoreFactor0
          (side := .right) (d := d) (x := x) (u := u) (σ := σ) (t := t)
          hd_prime hd_ge hx hu hcop hpnd hwnz_core
          (boundary_hfactor_core0_of_boundaryCore_local_zero
            (side := .right) (d := d) (x := x) (u := u) (σ := σ) (t := t)
            hwnz_core hlocal_core)
      exact hstat
  | left =>
      have hstat :=
        existsStatSingletonBoundaryCoreFactor0
          (side := .left) (d := d) (x := x) (u := u) (σ := σ) (t := t)
          hd_prime hd_ge hx hu hcop hpnd hwnz_core
          (boundary_hfactor_core0_of_boundaryCore_local_zero
            (side := .left) (d := d) (x := x) (u := u) (σ := σ) (t := t)
            hwnz_core hlocal_core)
      exact hstat

/--
RH-N26: `boundaryDiffPow` local-zero 仮定から
small finite-set 停留点存在へ接続する高位 wrapper。
-/
theorem
    exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryDiffPow_local0
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : match side with
      | .right => ¬ d ∣ x
      | .left => ¬ d ∣ u)
    (hS_dvd :
      ∀ r ∈ S, r.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u)
    (hS_gap :
      ∀ r ∈ S, (match side with
        | .right => ¬ r.1 ∣ x
        | .left => ¬ r.1 ∣ u))
    (hwnz_core :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hlocal_diff0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          hopcPrimeLocalContribution p.1 σ t = 0) :
    ∃ p : {q // Nat.Prime q},
      DkMath.RH.stationaryAt
        (fun v : ℝ => eulerZetaFinite_onVertical (insert p S) σ v) t := by
  exact exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryCore_local0
    (side := side) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
    hd_prime hd_ge hx hu hcop hpnd hS_dvd hS_gap hwnz_core
    (boundary_hlocal_core_of_boundaryDiffPow_local_zero
      (side := side) (d := d) (x := x) (u := u) (σ := σ) (t := t) hlocal_diff0)

local notation "existsStatInsertBoundaryCoreLocal0" =>
  exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryCore_local0

local notation "existsStatSingletonBoundaryCoreLocal0" =>
  exists_stationaryAt_singleton_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryCore_local0

/--
RH-N26: `boundaryDiffPow` local-zero 仮定から singleton 停留点存在へ接続する wrapper。
-/
theorem
    exists_stationaryAt_singleton_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryDiffPow_local0
    (side : DkMath.CFBRC.BoundarySide)
    {d x u : ℕ} {σ t : ℝ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : match side with
      | .right => ¬ d ∣ x
      | .left => ¬ d ∣ u)
    (hwnz_core :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hlocal_diff0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          hopcPrimeLocalContribution p.1 σ t = 0) :
    ∃ p : {q // Nat.Prime q},
      DkMath.RH.stationaryAt
        (fun v : ℝ =>
          eulerZetaFinite_onVertical ({p} : Finset {q // Nat.Prime q}) σ v) t := by
  exact existsStatSingletonBoundaryCoreLocal0
    (side := side) (d := d) (x := x) (u := u) (σ := σ) (t := t)
    hd_prime hd_ge hx hu hcop hpnd hwnz_core
    (boundary_hlocal_core_of_boundaryDiffPow_local_zero
      (side := side) (d := d) (x := x) (u := u) (σ := σ) (t := t) hlocal_diff0)

/--
RH-N27: `boundaryDiffPow` factor0 仮定から provider を構成する wrapper。
-/
def boundaryInsertLocalLiftProvider_of_boundary_dvd_gap_of_boundaryDiffPow_factor0
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hS_dvd :
      ∀ r ∈ S, r.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u)
    (hS_gap :
      ∀ r ∈ S, (match side with
        | .right => ¬ r.1 ∣ x
        | .left => ¬ r.1 ∣ u))
    (hwnz_diff :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hfactor_diff0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZetaFactorPhaseVelLocal p.1 σ t = 0) :
    BoundaryInsertLocalLiftProvider side S d x u σ t := by
  exact boundaryInsertLocalLiftProvider_of_boundary_dvd_gap_of_boundaryDiffPow_local0
    (side := side) (S := S)
    (hS_dvd := hS_dvd)
    (hS_gap := hS_gap)
    (hwnz_core := boundary_hwnz_core_of_boundaryDiffPow_nonzero
      (side := side) (d := d) (x := x) (u := u) (σ := σ) (t := t) hwnz_diff)
    (hlocal_diff0 := boundary_hlocal_diff0_of_boundaryDiffPow_factorPhaseVelLocal_eq_zero
      (side := side) (d := d) (x := x) (u := u) (σ := σ) (t := t)
      hwnz_diff hfactor_diff0)

/--
RH-N29: `boundaryDiffPow` factor0 仮定で、`hS_gap` を要求しない provider 構成 wrapper。

`hS_dvd` と `hwnz_diff` から `S` 上非零を、
`hS_dvd` と `hfactor_diff0` から `S` 上 local-zero を生成して
provider を返す。
-/
def boundaryInsertLocalLiftProvider_of_boundary_dvd_of_boundaryDiffPow_factor0
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hS_dvd :
      ∀ r ∈ S, r.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u)
    (hwnz_diff :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hfactor_diff0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZetaFactorPhaseVelLocal p.1 σ t = 0) :
    BoundaryInsertLocalLiftProvider side S d x u σ t := by
  have hS_nonzero :
      ∀ r ∈ S, eulerZeta_exp_s_log_p_sub_one r.1 σ t ≠ 0 := by
    intro r hr
    exact hwnz_diff r (hS_dvd r hr)
  have hS_local0 :
      ∀ r ∈ S, hopcPrimeLocalContribution r.1 σ t = 0 := by
    intro r hr
    exact hopcPrimeLocalContribution_eq_zero_of_factorPhaseVelLocal_eq_zero_of_nonzero
      (p := r.1) (σ := σ) (t := t)
      (hwnz_diff r (hS_dvd r hr))
      (hfactor_diff0 r (hS_dvd r hr))
  have hlocal_diff0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          hopcPrimeLocalContribution p.1 σ t = 0 :=
    boundary_hlocal_diff0_of_boundaryDiffPow_factorPhaseVelLocal_eq_zero
      (side := side) (d := d) (x := x) (u := u) (σ := σ) (t := t)
      hwnz_diff hfactor_diff0
  exact boundaryInsertLocalLiftProvider_of_nonzero_and_local_zero_on_S_and_witness
    (side := side) (S := S)
    (hS_nonzero := hS_nonzero)
    (hwnz_witness := fun p hp_dvd _hgap => hwnz_diff p hp_dvd)
    (hS_local0 := hS_local0)
    (hlocal_witness := fun p hp_dvd _hgap => hlocal_diff0 p hp_dvd)

/--
RH-N29: `boundaryDiffPow` factor0 仮定で、`hS_gap` を要求しない
small finite-set 停留点存在 wrapper。
-/
theorem
    exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryDiffPow_factor0_of_dvd
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : match side with
      | .right => ¬ d ∣ x
      | .left => ¬ d ∣ u)
    (hS_dvd :
      ∀ r ∈ S, r.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u)
    (hwnz_diff :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hfactor_diff0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZetaFactorPhaseVelLocal p.1 σ t = 0) :
    ∃ p : {q // Nat.Prime q},
      DkMath.RH.stationaryAt
        (fun v : ℝ => eulerZetaFinite_onVertical (insert p S) σ v) t := by
  exact exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_provider
    (side := side) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
    hd_prime hd_ge hx hu hcop hpnd
    (boundaryInsertLocalLiftProvider_of_boundary_dvd_of_boundaryDiffPow_factor0
      (side := side) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
      hS_dvd hwnz_diff hfactor_diff0)

/--
OP-004: `boundaryDiffPow` factor0 + `hS_dvd`（`hS_gap` 不要）から、
small finite-set 非退化停留点存在へ接続する wrapper。
-/
theorem
    exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryDiffPow_factor0_of_dvd_and_phaseCurv
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : match side with
      | .right => ¬ d ∣ x
      | .left => ¬ d ∣ u)
    (hS_dvd :
      ∀ r ∈ S, r.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u)
    (hwnz_diff :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hfactor_diff0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZetaFactorPhaseVelLocal p.1 σ t = 0)
    (hcurv_lift :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          (match side with
            | .right => ¬ p.1 ∣ x
            | .left => ¬ p.1 ∣ u) →
          DkMath.RH.phaseCurv
            (fun v : ℝ => eulerZetaFinite_onVertical (insert p S) σ v) t ≠ 0) :
    ∃ p : {q // Nat.Prime q},
      DkMath.RH.nondegenerateStationaryAt
        (fun v : ℝ => eulerZetaFinite_onVertical (insert p S) σ v) t := by
  cases side with
  | right =>
      exact
        exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_provider_and_phaseCurvProvider
          (side := .right) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
          hd_prime hd_ge hx hu hcop hpnd
          (boundaryInsertLocalLiftProvider_of_boundary_dvd_of_boundaryDiffPow_factor0
            (side := .right) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
            hS_dvd hwnz_diff hfactor_diff0)
          (boundaryInsertPhaseCurvProvider_of_split
            (side := .right) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
            hcurv_lift)
  | left =>
      exact
        exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_provider_and_phaseCurvProvider
          (side := .left) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
          hd_prime hd_ge hx hu hcop hpnd
          (boundaryInsertLocalLiftProvider_of_boundary_dvd_of_boundaryDiffPow_factor0
            (side := .left) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
            hS_dvd hwnz_diff hfactor_diff0)
          (boundaryInsertPhaseCurvProvider_of_split
            (side := .left) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
            hcurv_lift)

/--
RH-N30: `S` を `boundaryDiffPow side d x u` の除法条件で正規化した有限集合。
-/
@[simp] def boundaryDiffPowDvdSet
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    (d x u : ℕ) : Finset {q // Nat.Prime q} :=
  S.filter (fun r => r.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u)

/--
RH-N30: `boundaryDiffPowDvdSet` の要素は自動的に boundary 除法を満たす。
-/
theorem boundary_dvd_on_boundaryDiffPowDvdSet
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} :
    ∀ r ∈ boundaryDiffPowDvdSet side S d x u,
      r.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u := by
  intro r hr
  exact (Finset.mem_filter.mp hr).2

/--
RH-N30: `S` の正規化を使って `hS_dvd` を要求しない provider 構成 wrapper。
-/
def boundaryInsertLocalLiftProvider_of_boundaryDiffPow_factor0_normalized
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hwnz_diff :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hfactor_diff0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZetaFactorPhaseVelLocal p.1 σ t = 0) :
    BoundaryInsertLocalLiftProvider side (boundaryDiffPowDvdSet side S d x u) d x u σ t := by
  exact boundaryInsertLocalLiftProvider_of_boundary_dvd_of_boundaryDiffPow_factor0
    (side := side) (S := boundaryDiffPowDvdSet side S d x u)
    (d := d) (x := x) (u := u) (σ := σ) (t := t)
    (hS_dvd := boundary_dvd_on_boundaryDiffPowDvdSet (side := side) (S := S))
    hwnz_diff hfactor_diff0

/--
RH-N30: `S` 正規化版の `boundaryDiffPow` factor0 から
small finite-set 停留点存在へ接続する wrapper。
-/
theorem
    exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryDiffPow_factor0_normalized
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : match side with
      | .right => ¬ d ∣ x
      | .left => ¬ d ∣ u)
    (hwnz_diff :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hfactor_diff0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZetaFactorPhaseVelLocal p.1 σ t = 0) :
    ∃ p : {q // Nat.Prime q},
      DkMath.RH.stationaryAt
        (fun v : ℝ =>
          eulerZetaFinite_onVertical (insert p (boundaryDiffPowDvdSet side S d x u)) σ v) t := by
  exact exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryDiffPow_factor0_of_dvd
    (side := side) (S := boundaryDiffPowDvdSet side S d x u)
    (d := d) (x := x) (u := u) (σ := σ) (t := t)
    hd_prime hd_ge hx hu hcop hpnd
    (hS_dvd := boundary_dvd_on_boundaryDiffPowDvdSet (side := side) (S := S))
    hwnz_diff hfactor_diff0

/--
OP-004: `S` 正規化版（`boundaryDiffPowDvdSet`）の
`boundaryDiffPow` factor0 から非退化停留点存在へ接続する wrapper。
-/
theorem
    exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryDiffPow_factor0_normalized_and_phaseCurv
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : match side with
      | .right => ¬ d ∣ x
      | .left => ¬ d ∣ u)
    (hwnz_diff :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hfactor_diff0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZetaFactorPhaseVelLocal p.1 σ t = 0)
    (hcurv_lift :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          (match side with
            | .right => ¬ p.1 ∣ x
            | .left => ¬ p.1 ∣ u) →
          DkMath.RH.phaseCurv
            (fun v : ℝ =>
              eulerZetaFinite_onVertical (insert p (boundaryDiffPowDvdSet side S d x u)) σ v) t ≠ 0) :
    ∃ p : {q // Nat.Prime q},
      DkMath.RH.nondegenerateStationaryAt
        (fun v : ℝ =>
          eulerZetaFinite_onVertical (insert p (boundaryDiffPowDvdSet side S d x u)) σ v) t := by
  cases side with
  | right =>
      exact
        exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryDiffPow_factor0_of_dvd_and_phaseCurv
          (side := .right) (S := boundaryDiffPowDvdSet .right S d x u)
          (d := d) (x := x) (u := u) (σ := σ) (t := t)
          hd_prime hd_ge hx hu hcop hpnd
          (hS_dvd := boundary_dvd_on_boundaryDiffPowDvdSet (side := .right) (S := S))
          hwnz_diff hfactor_diff0 hcurv_lift
  | left =>
      exact
        exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryDiffPow_factor0_of_dvd_and_phaseCurv
          (side := .left) (S := boundaryDiffPowDvdSet .left S d x u)
          (d := d) (x := x) (u := u) (σ := σ) (t := t)
          hd_prime hd_ge hx hu hcop hpnd
          (hS_dvd := boundary_dvd_on_boundaryDiffPowDvdSet (side := .left) (S := S))
          hwnz_diff hfactor_diff0 hcurv_lift

/--
RH-N31: 元の `S` を保持したまま、`hS_dvd` を要求しない provider 構成 wrapper。

`S` のうち `boundaryDiffPow` を割る要素は `hwnz_diff / hfactor_diff0` で処理し、
割らない要素は `hS_nonzero_offdvd / hS_local0_offdvd` で補完する。
-/
def boundaryInsertLocalLiftProvider_of_boundaryDiffPow_factor0_with_offdvd
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hwnz_diff :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hfactor_diff0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZetaFactorPhaseVelLocal p.1 σ t = 0)
    (hS_nonzero_offdvd :
      ∀ r ∈ S, ¬ r.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
        eulerZeta_exp_s_log_p_sub_one r.1 σ t ≠ 0)
    (hS_local0_offdvd :
      ∀ r ∈ S, ¬ r.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
        hopcPrimeLocalContribution r.1 σ t = 0) :
    BoundaryInsertLocalLiftProvider side S d x u σ t := by
  have hS_nonzero :
      ∀ r ∈ S, eulerZeta_exp_s_log_p_sub_one r.1 σ t ≠ 0 := by
    intro r hr
    by_cases hrdvd : r.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u
    · exact hwnz_diff r hrdvd
    · exact hS_nonzero_offdvd r hr hrdvd
  have hS_local0 :
      ∀ r ∈ S, hopcPrimeLocalContribution r.1 σ t = 0 := by
    intro r hr
    by_cases hrdvd : r.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u
    · exact hopcPrimeLocalContribution_eq_zero_of_factorPhaseVelLocal_eq_zero_of_nonzero
        (p := r.1) (σ := σ) (t := t)
        (hwnz_diff r hrdvd) (hfactor_diff0 r hrdvd)
    · exact hS_local0_offdvd r hr hrdvd
  have hlocal_diff0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          hopcPrimeLocalContribution p.1 σ t = 0 :=
    boundary_hlocal_diff0_of_boundaryDiffPow_factorPhaseVelLocal_eq_zero
      (side := side) (d := d) (x := x) (u := u) (σ := σ) (t := t)
      hwnz_diff hfactor_diff0
  exact boundaryInsertLocalLiftProvider_of_nonzero_and_local_zero_on_S_and_witness
    (side := side) (S := S)
    (hS_nonzero := hS_nonzero)
    (hwnz_witness := fun p hp_dvd _hgap => hwnz_diff p hp_dvd)
    (hS_local0 := hS_local0)
    (hlocal_witness := fun p hp_dvd _hgap => hlocal_diff0 p hp_dvd)

/--
RH-N31: 元の `S` を保持したまま、`hS_dvd` を要求しない
small finite-set 停留点存在 wrapper。
-/
theorem
    exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryDiffPow_factor0_with_offdvd
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : match side with
      | .right => ¬ d ∣ x
      | .left => ¬ d ∣ u)
    (hwnz_diff :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hfactor_diff0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZetaFactorPhaseVelLocal p.1 σ t = 0)
    (hS_nonzero_offdvd :
      ∀ r ∈ S, ¬ r.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
        eulerZeta_exp_s_log_p_sub_one r.1 σ t ≠ 0)
    (hS_local0_offdvd :
      ∀ r ∈ S, ¬ r.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
        hopcPrimeLocalContribution r.1 σ t = 0) :
    ∃ p : {q // Nat.Prime q},
      DkMath.RH.stationaryAt
        (fun v : ℝ => eulerZetaFinite_onVertical (insert p S) σ v) t := by
  exact exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_provider
    (side := side) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
    hd_prime hd_ge hx hu hcop hpnd
    (boundaryInsertLocalLiftProvider_of_boundaryDiffPow_factor0_with_offdvd
      (side := side) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
      hwnz_diff hfactor_diff0 hS_nonzero_offdvd hS_local0_offdvd)

/--
OP-004: `boundaryDiffPow` factor0 + off-dvd 補完仮定（`hS_dvd` 不要）から、
small finite-set 非退化停留点存在へ接続する wrapper。
-/
theorem
    exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryDiffPow_factor0_with_offdvd_and_phaseCurv
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : match side with
      | .right => ¬ d ∣ x
      | .left => ¬ d ∣ u)
    (hwnz_diff :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hfactor_diff0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZetaFactorPhaseVelLocal p.1 σ t = 0)
    (hS_nonzero_offdvd :
      ∀ r ∈ S, ¬ r.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
        eulerZeta_exp_s_log_p_sub_one r.1 σ t ≠ 0)
    (hS_local0_offdvd :
      ∀ r ∈ S, ¬ r.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
        hopcPrimeLocalContribution r.1 σ t = 0)
    (hcurv_lift :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          (match side with
            | .right => ¬ p.1 ∣ x
            | .left => ¬ p.1 ∣ u) →
          DkMath.RH.phaseCurv
            (fun v : ℝ => eulerZetaFinite_onVertical (insert p S) σ v) t ≠ 0) :
    ∃ p : {q // Nat.Prime q},
      DkMath.RH.nondegenerateStationaryAt
        (fun v : ℝ => eulerZetaFinite_onVertical (insert p S) σ v) t := by
  cases side with
  | right =>
      exact
        exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_provider_and_phaseCurvProvider
          (side := .right) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
          hd_prime hd_ge hx hu hcop hpnd
          (boundaryInsertLocalLiftProvider_of_boundaryDiffPow_factor0_with_offdvd
            (side := .right) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
            hwnz_diff hfactor_diff0 hS_nonzero_offdvd hS_local0_offdvd)
          (boundaryInsertPhaseCurvProvider_of_split
            (side := .right) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
            hcurv_lift)
  | left =>
      exact
        exists_nondegenerateStationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_provider_and_phaseCurvProvider
          (side := .left) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
          hd_prime hd_ge hx hu hcop hpnd
          (boundaryInsertLocalLiftProvider_of_boundaryDiffPow_factor0_with_offdvd
            (side := .left) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
            hwnz_diff hfactor_diff0 hS_nonzero_offdvd hS_local0_offdvd)
          (boundaryInsertPhaseCurvProvider_of_split
            (side := .left) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
            hcurv_lift)

local notation "existsStatInsertBoundaryDiffPowLocal0" =>
  exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryDiffPow_local0

local notation "existsStatSingletonBoundaryDiffPowLocal0" =>
  exists_stationaryAt_singleton_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryDiffPow_local0

/--
RH-N27: `boundaryDiffPow` factor0 仮定から
small finite-set 停留点存在へ接続する高位 wrapper。
-/
theorem
    exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryDiffPow_factor0
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : match side with
      | .right => ¬ d ∣ x
      | .left => ¬ d ∣ u)
    (hS_dvd :
      ∀ r ∈ S, r.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u)
    (hS_gap :
      ∀ r ∈ S, (match side with
        | .right => ¬ r.1 ∣ x
        | .left => ¬ r.1 ∣ u))
    (hwnz_diff :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hfactor_diff0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZetaFactorPhaseVelLocal p.1 σ t = 0) :
    ∃ p : {q // Nat.Prime q},
      DkMath.RH.stationaryAt
        (fun v : ℝ => eulerZetaFinite_onVertical (insert p S) σ v) t := by
  exact existsStatInsertBoundaryDiffPowLocal0
    (side := side) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
    hd_prime hd_ge hx hu hcop hpnd hS_dvd hS_gap
    (boundary_hwnz_core_of_boundaryDiffPow_nonzero
      (side := side) (d := d) (x := x) (u := u) (σ := σ) (t := t) hwnz_diff)
    (boundary_hlocal_diff0_of_boundaryDiffPow_factorPhaseVelLocal_eq_zero
      (side := side) (d := d) (x := x) (u := u) (σ := σ) (t := t)
      hwnz_diff hfactor_diff0)

/--
RH-N27: `boundaryDiffPow` factor0 仮定から singleton 停留点存在へ接続する wrapper。
-/
theorem
    exists_stationaryAt_singleton_of_cfbRc_primitive_prime_boundary_bridge_of_boundaryDiffPow_factor0
    (side : DkMath.CFBRC.BoundarySide)
    {d x u : ℕ} {σ t : ℝ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : match side with
      | .right => ¬ d ∣ x
      | .left => ¬ d ∣ u)
    (hwnz_diff :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hfactor_diff0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZetaFactorPhaseVelLocal p.1 σ t = 0) :
    ∃ p : {q // Nat.Prime q},
      DkMath.RH.stationaryAt
        (fun v : ℝ =>
          eulerZetaFinite_onVertical ({p} : Finset {q // Nat.Prime q}) σ v) t := by
  exact existsStatSingletonBoundaryDiffPowLocal0
    (side := side) (d := d) (x := x) (u := u) (σ := σ) (t := t)
    hd_prime hd_ge hx hu hcop hpnd
    (boundary_hwnz_core_of_boundaryDiffPow_nonzero
      (side := side) (d := d) (x := x) (u := u) (σ := σ) (t := t) hwnz_diff)
    (boundary_hlocal_diff0_of_boundaryDiffPow_factorPhaseVelLocal_eq_zero
      (side := side) (d := d) (x := x) (u := u) (σ := σ) (t := t)
      hwnz_diff hfactor_diff0)

/--
RH-O7: `boundaryDiffPow` に関する split 仮定（divide / off-divide）から、
`|hopcPrimeContributionFn| ≤ C / p^σ` の一括上界を構成する。
-/
theorem hopcPrimeContributionFn_abs_le_prime_rpow_of_boundaryDiffPow_split
    (side : DkMath.CFBRC.BoundarySide)
    {d x u : ℕ} {σ t C : ℝ}
    (hAbs_dvd :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          |hopcPrimeContributionFn σ t p| ≤ C / (↑p : ℝ) ^ σ)
    (hAbs_offdvd :
      ∀ p : {q // Nat.Prime q},
        ¬ p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          |hopcPrimeContributionFn σ t p| ≤ C / (↑p : ℝ) ^ σ) :
    ∀ p : {q // Nat.Prime q},
      |hopcPrimeContributionFn σ t p| ≤ C / (↑p : ℝ) ^ σ := by
  intro p
  by_cases hp_dvd : p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u
  · exact hAbs_dvd p hp_dvd
  · exact hAbs_offdvd p hp_dvd

/--
RH-O7: `boundaryDiffPow` split 上界と `σ > 1`・`eventually stationary` から
`hopcPrimeContributionTsum = 0` を得る。
-/
theorem hopcPrimeContributionTsum_eq_zero_of_boundaryDiffPow_split_prime_rpow_bound_sigma_gt_one
    (side : DkMath.CFBRC.BoundarySide)
    {d x u : ℕ} {σ t C : ℝ}
    (hσ : 1 < σ)
    (hAbs_dvd :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          |hopcPrimeContributionFn σ t p| ≤ C / (↑p : ℝ) ^ σ)
    (hAbs_offdvd :
      ∀ p : {q // Nat.Prime q},
        ¬ p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          |hopcPrimeContributionFn σ t p| ≤ C / (↑p : ℝ) ^ σ)
    (hEvStationary :
      ∀ᶠ S : Finset {q // Nat.Prime q} in Filter.atTop,
        DkMath.RH.stationaryAt
          (fun v : ℝ => eulerZetaFinite_onVertical S σ v) t) :
    hopcPrimeContributionTsum σ t = 0 := by
  have hAbs :
      ∀ p : {q // Nat.Prime q},
        |hopcPrimeContributionFn σ t p| ≤ C / (↑p : ℝ) ^ σ :=
    hopcPrimeContributionFn_abs_le_prime_rpow_of_boundaryDiffPow_split
      (side := side) (d := d) (x := x) (u := u) (σ := σ) (t := t) (C := C)
      hAbs_dvd hAbs_offdvd
  exact hopcPrimeContributionTsum_eq_zero_of_prime_rpow_bound_sigma_gt_one
    (σ := σ) (t := t) (C := C) hσ hAbs hEvStationary

/--
RH-O7: `boundaryDiffPow` split 上界と `σ > 1`・`eventually stationary` から、
有限寄与和の atTop 極限（0）を得る。
-/
theorem tendsto_hopcPrimeContributionSum_atTop_of_boundaryDiffPow_split_prime_rpow_bound_sigma_gt_one
    (side : DkMath.CFBRC.BoundarySide)
    {d x u : ℕ} {σ t C : ℝ}
    (hσ : 1 < σ)
    (hAbs_dvd :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          |hopcPrimeContributionFn σ t p| ≤ C / (↑p : ℝ) ^ σ)
    (hAbs_offdvd :
      ∀ p : {q // Nat.Prime q},
        ¬ p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          |hopcPrimeContributionFn σ t p| ≤ C / (↑p : ℝ) ^ σ)
    (hEvStationary :
      ∀ᶠ S : Finset {q // Nat.Prime q} in Filter.atTop,
        DkMath.RH.stationaryAt
          (fun v : ℝ => eulerZetaFinite_onVertical S σ v) t) :
    Filter.Tendsto
      (fun S : Finset {p // Nat.Prime p} =>
        hopcPrimeContributionSum (S := S) σ t)
      Filter.atTop (𝓝 (0 : ℝ)) := by
  have hAbs :
      ∀ p : {q // Nat.Prime q},
        |hopcPrimeContributionFn σ t p| ≤ C / (↑p : ℝ) ^ σ :=
    hopcPrimeContributionFn_abs_le_prime_rpow_of_boundaryDiffPow_split
      (side := side) (d := d) (x := x) (u := u) (σ := σ) (t := t) (C := C)
      hAbs_dvd hAbs_offdvd
  exact tendsto_hopcPrimeContributionSum_atTop_of_prime_rpow_bound_sigma_gt_one
    (σ := σ) (t := t) (C := C) hσ hAbs hEvStationary

/--
RH-O8: `hopcPrimeLocalContribution = 0` から
`|hopcPrimeContributionFn| ≤ C / p^σ` を供給する補題。
-/
theorem hopcPrimeContributionFn_abs_le_prime_rpow_of_local_zero
    {σ t C : ℝ}
    (hC : 0 ≤ C)
    (hlocal0 :
      ∀ p : {q // Nat.Prime q}, hopcPrimeLocalContribution p.1 σ t = 0) :
    ∀ p : {q // Nat.Prime q},
      |hopcPrimeContributionFn σ t p| ≤ C / (↑p : ℝ) ^ σ := by
  intro p
  have hp_pos : (0 : ℝ) < (↑p : ℝ) := by
    exact_mod_cast p.2.pos
  have hBoundNonneg : 0 ≤ C / (↑p : ℝ) ^ σ := by
    exact div_nonneg hC (le_of_lt (Real.rpow_pos_of_pos hp_pos σ))
  have h0 : hopcPrimeContributionFn σ t p = 0 := by
    simpa [hopcPrimeContributionFn] using hlocal0 p
  rw [h0]
  simpa using hBoundNonneg

/--
RH-O8: `boundaryDiffPow` を割る素数での
`w_p ≠ 0` と factor 位相速度ゼロから、`hAbs_dvd` を供給する。
-/
theorem hopcPrimeContributionFn_abs_le_prime_rpow_of_boundaryDiffPow_factor0
    (side : DkMath.CFBRC.BoundarySide)
    {d x u : ℕ} {σ t C : ℝ}
    (hC : 0 ≤ C)
    (hwnz_diff :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hfactor_diff0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZetaFactorPhaseVelLocal p.1 σ t = 0) :
    ∀ p : {q // Nat.Prime q},
      p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
        |hopcPrimeContributionFn σ t p| ≤ C / (↑p : ℝ) ^ σ := by
  intro p hp_dvd
  have hlocal0 : hopcPrimeLocalContribution p.1 σ t = 0 :=
    hopcPrimeLocalContribution_eq_zero_of_factorPhaseVelLocal_eq_zero_of_nonzero
      (p := p.1) (σ := σ) (t := t) (hwnz_diff p hp_dvd) (hfactor_diff0 p hp_dvd)
  have hp_pos : (0 : ℝ) < (↑p : ℝ) := by
    exact_mod_cast p.2.pos
  have hBoundNonneg : 0 ≤ C / (↑p : ℝ) ^ σ := by
    exact div_nonneg hC (le_of_lt (Real.rpow_pos_of_pos hp_pos σ))
  have h0 : hopcPrimeContributionFn σ t p = 0 := by
    simpa [hopcPrimeContributionFn] using hlocal0
  rw [h0]
  simpa using hBoundNonneg

/--
RH-O8: `boundaryDiffPow` を割らない素数での local-zero 仮定から、
`hAbs_offdvd` を供給する。
-/
theorem hopcPrimeContributionFn_abs_le_prime_rpow_of_boundaryDiffPow_offdvd_local0
    (side : DkMath.CFBRC.BoundarySide)
    {d x u : ℕ} {σ t C : ℝ}
    (hC : 0 ≤ C)
    (hlocal_offdvd :
      ∀ p : {q // Nat.Prime q},
        ¬ p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          hopcPrimeLocalContribution p.1 σ t = 0) :
    ∀ p : {q // Nat.Prime q},
      ¬ p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
        |hopcPrimeContributionFn σ t p| ≤ C / (↑p : ℝ) ^ σ := by
  intro p hp_offdvd
  have hlocal0 : hopcPrimeLocalContribution p.1 σ t = 0 :=
    hlocal_offdvd p hp_offdvd
  have hp_pos : (0 : ℝ) < (↑p : ℝ) := by
    exact_mod_cast p.2.pos
  have hBoundNonneg : 0 ≤ C / (↑p : ℝ) ^ σ := by
    exact div_nonneg hC (le_of_lt (Real.rpow_pos_of_pos hp_pos σ))
  have h0 : hopcPrimeContributionFn σ t p = 0 := by
    simpa [hopcPrimeContributionFn] using hlocal0
  rw [h0]
  simpa using hBoundNonneg

/--
RH-O8: `boundaryDiffPow` を割る側は factor0、割らない側は local-zero を仮定して、
global な `|hopcPrimeContributionFn| ≤ C / p^σ` を供給する。
-/
theorem hopcPrimeContributionFn_abs_le_prime_rpow_of_boundaryDiffPow_factor0_with_offdvd_local0
    (side : DkMath.CFBRC.BoundarySide)
    {d x u : ℕ} {σ t C : ℝ}
    (hC : 0 ≤ C)
    (hwnz_diff :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hfactor_diff0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZetaFactorPhaseVelLocal p.1 σ t = 0)
    (hlocal_offdvd :
      ∀ p : {q // Nat.Prime q},
        ¬ p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          hopcPrimeLocalContribution p.1 σ t = 0) :
    ∀ p : {q // Nat.Prime q},
      |hopcPrimeContributionFn σ t p| ≤ C / (↑p : ℝ) ^ σ :=
  hopcPrimeContributionFn_abs_le_prime_rpow_of_boundaryDiffPow_split
    (side := side) (d := d) (x := x) (u := u) (σ := σ) (t := t) (C := C)
    (hAbs_dvd := hopcPrimeContributionFn_abs_le_prime_rpow_of_boundaryDiffPow_factor0
      (side := side) (d := d) (x := x) (u := u) (σ := σ) (t := t) (C := C)
      hC hwnz_diff hfactor_diff0)
    (hAbs_offdvd := hopcPrimeContributionFn_abs_le_prime_rpow_of_boundaryDiffPow_offdvd_local0
      (side := side) (d := d) (x := x) (u := u) (σ := σ) (t := t) (C := C)
      hC hlocal_offdvd)

/--
RH-O8: `boundaryDiffPow` factor0 + off-dvd local-zero 仮定から、
`hopcPrimeContributionTsum = 0` を得る。
-/
theorem hopcPrimeContributionTsum_eq_zero_of_boundaryDiffPow_factor0_with_offdvd_local0_sigma_gt_one
    (side : DkMath.CFBRC.BoundarySide)
    {d x u : ℕ} {σ t C : ℝ}
    (hσ : 1 < σ) (hC : 0 ≤ C)
    (hwnz_diff :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hfactor_diff0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZetaFactorPhaseVelLocal p.1 σ t = 0)
    (hlocal_offdvd :
      ∀ p : {q // Nat.Prime q},
        ¬ p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          hopcPrimeLocalContribution p.1 σ t = 0)
    (hEvStationary :
      ∀ᶠ S : Finset {q // Nat.Prime q} in Filter.atTop,
        DkMath.RH.stationaryAt
          (fun v : ℝ => eulerZetaFinite_onVertical S σ v) t) :
    hopcPrimeContributionTsum σ t = 0 := by
  have hAbs :
      ∀ p : {q // Nat.Prime q},
        |hopcPrimeContributionFn σ t p| ≤ C / (↑p : ℝ) ^ σ :=
    hopcPrimeContributionFn_abs_le_prime_rpow_of_boundaryDiffPow_factor0_with_offdvd_local0
      (side := side) (d := d) (x := x) (u := u) (σ := σ) (t := t) (C := C)
      hC hwnz_diff hfactor_diff0 hlocal_offdvd
  exact hopcPrimeContributionTsum_eq_zero_of_prime_rpow_bound_sigma_gt_one
    (σ := σ) (t := t) (C := C) hσ hAbs hEvStationary

/--
RH-O8: `boundaryDiffPow` factor0 + off-dvd local-zero 仮定から、
有限寄与和の atTop 極限（0）を得る。
-/
theorem tendsto_hopcPrimeContributionSum_atTop_of_boundaryDiffPow_factor0_with_offdvd_local0_sigma_gt_one
    (side : DkMath.CFBRC.BoundarySide)
    {d x u : ℕ} {σ t C : ℝ}
    (hσ : 1 < σ) (hC : 0 ≤ C)
    (hwnz_diff :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hfactor_diff0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZetaFactorPhaseVelLocal p.1 σ t = 0)
    (hlocal_offdvd :
      ∀ p : {q // Nat.Prime q},
        ¬ p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          hopcPrimeLocalContribution p.1 σ t = 0)
    (hEvStationary :
      ∀ᶠ S : Finset {q // Nat.Prime q} in Filter.atTop,
        DkMath.RH.stationaryAt
          (fun v : ℝ => eulerZetaFinite_onVertical S σ v) t) :
    Filter.Tendsto
      (fun S : Finset {p // Nat.Prime p} =>
        hopcPrimeContributionSum (S := S) σ t)
      Filter.atTop (𝓝 (0 : ℝ)) := by
  have hAbs :
      ∀ p : {q // Nat.Prime q},
        |hopcPrimeContributionFn σ t p| ≤ C / (↑p : ℝ) ^ σ :=
    hopcPrimeContributionFn_abs_le_prime_rpow_of_boundaryDiffPow_factor0_with_offdvd_local0
      (side := side) (d := d) (x := x) (u := u) (σ := σ) (t := t) (C := C)
      hC hwnz_diff hfactor_diff0 hlocal_offdvd
  exact tendsto_hopcPrimeContributionSum_atTop_of_prime_rpow_bound_sigma_gt_one
    (σ := σ) (t := t) (C := C) hσ hAbs hEvStationary

/--
RH-O9: `boundaryDiffPow` を割らない素数に対する local-zero 供給器。
-/
structure BoundaryOffDvdLocalZeroProvider
    (side : DkMath.CFBRC.BoundarySide)
    (d x u : ℕ) (σ t : ℝ) : Type where
  hlocal_offdvd :
    ∀ p : {q // Nat.Prime q},
      ¬ p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          hopcPrimeLocalContribution p.1 σ t = 0

/--
RH-O14: 有限集合 `S` 上に制限した off-dvd local-zero 供給器。
-/
structure BoundaryOffDvdLocalZeroOnSetProvider
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    (d x u : ℕ) (σ t : ℝ) : Type where
  hlocal_offdvd_on_S :
    ∀ r ∈ S,
      ¬ r.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
        hopcPrimeLocalContribution r.1 σ t = 0

/--
RH-O14: global off-dvd local-zero provider から on-set provider へ制限する。
-/
def boundaryOffDvdLocalZeroOnSetProvider_of_global
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (offdvdProvider : BoundaryOffDvdLocalZeroProvider side d x u σ t) :
    BoundaryOffDvdLocalZeroOnSetProvider side S d x u σ t := by
  refine ⟨?_⟩
  intro r _hrS hr_offdvd
  exact offdvdProvider.hlocal_offdvd r hr_offdvd

/--
RH-O14: singleton `S={r}` で、insert-provider の `hsum_lift` から
off-dvd 側の局所寄与ゼロを抽出する十分条件補題。
-/
theorem boundary_hlocal_offdvd_singleton_of_insertProvider_and_witness_local0
    (side : DkMath.CFBRC.BoundarySide)
    {d x u : ℕ} {σ t : ℝ}
    (r p : {q // Nat.Prime q})
    (provider :
      BoundaryInsertLocalLiftProvider side ({r} : Finset {q // Nat.Prime q}) d x u σ t)
    (hp_dvd : p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u)
    (hp_gap : match side with
      | .right => ¬ p.1 ∣ x
      | .left => ¬ p.1 ∣ u)
    (hr_offdvd : ¬ r.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u)
    (hlocal_p : hopcPrimeLocalContribution p.1 σ t = 0) :
    hopcPrimeLocalContribution r.1 σ t = 0 := by
  cases side with
  | right =>
      have hp_ne_r : p.1 ≠ r.1 := by
        intro hp_eq
        apply hr_offdvd
        simpa [DkMath.CFBRC.boundaryDiffPow, hp_eq] using hp_dvd
      have hp_ne_r_subtype : p ≠ r := by
        intro hpr
        apply hp_ne_r
        exact congrArg Subtype.val hpr
      have hp_not_mem : p ∉ ({r} : Finset {q // Nat.Prime q}) := by
        simp [hp_ne_r_subtype]
      have hsum :
          hopcPrimeContributionSum (S := insert p ({r} : Finset {q // Nat.Prime q})) σ t = 0 :=
        provider.hsum_lift p hp_dvd hp_gap
      have hpair :
          hopcPrimeLocalContribution p.1 σ t + hopcPrimeLocalContribution r.1 σ t = 0 := by
        unfold hopcPrimeContributionSum at hsum
        rw [Finset.sum_insert hp_not_mem] at hsum
        simpa using hsum
      rw [hlocal_p, zero_add] at hpair
      exact hpair
  | left =>
      have hp_ne_r : p.1 ≠ r.1 := by
        intro hp_eq
        apply hr_offdvd
        simpa [DkMath.CFBRC.boundaryDiffPow, Nat.add_comm, hp_eq] using hp_dvd
      have hp_ne_r_subtype : p ≠ r := by
        intro hpr
        apply hp_ne_r
        exact congrArg Subtype.val hpr
      have hp_not_mem : p ∉ ({r} : Finset {q // Nat.Prime q}) := by
        simp [hp_ne_r_subtype]
      have hsum :
          hopcPrimeContributionSum (S := insert p ({r} : Finset {q // Nat.Prime q})) σ t = 0 :=
        provider.hsum_lift p hp_dvd hp_gap
      have hpair :
          hopcPrimeLocalContribution p.1 σ t + hopcPrimeLocalContribution r.1 σ t = 0 := by
        unfold hopcPrimeContributionSum at hsum
        rw [Finset.sum_insert hp_not_mem] at hsum
        simpa using hsum
      rw [hlocal_p, zero_add] at hpair
      exact hpair

/--
RH-O14: singleton `S={r}` で、`boundaryDiffPow` 側 factor0 仮定から
insert-provider を使って off-dvd 局所寄与ゼロを抽出する wrapper。
-/
theorem boundary_hlocal_offdvd_singleton_of_insertProvider_and_boundaryDiffPow_factor0
    (side : DkMath.CFBRC.BoundarySide)
    {d x u : ℕ} {σ t : ℝ}
    (r p : {q // Nat.Prime q})
    (provider :
      BoundaryInsertLocalLiftProvider side ({r} : Finset {q // Nat.Prime q}) d x u σ t)
    (hp_dvd : p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u)
    (hp_gap : match side with
      | .right => ¬ p.1 ∣ x
      | .left => ¬ p.1 ∣ u)
    (hr_offdvd : ¬ r.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u)
    (hwnz_diff :
      ∀ q : {q0 // Nat.Prime q0},
        q.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZeta_exp_s_log_p_sub_one q.1 σ t ≠ 0)
    (hfactor_diff0 :
      ∀ q : {q0 // Nat.Prime q0},
        q.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZetaFactorPhaseVelLocal q.1 σ t = 0) :
    hopcPrimeLocalContribution r.1 σ t = 0 := by
  have hlocal_p : hopcPrimeLocalContribution p.1 σ t = 0 :=
    hopcPrimeLocalContribution_eq_zero_of_factorPhaseVelLocal_eq_zero_of_nonzero
      (p := p.1) (σ := σ) (t := t)
      (hwnz_diff p hp_dvd)
      (hfactor_diff0 p hp_dvd)
  exact boundary_hlocal_offdvd_singleton_of_insertProvider_and_witness_local0
    (side := side) (d := d) (x := x) (u := u) (σ := σ) (t := t)
    (r := r) (p := p) provider hp_dvd hp_gap hr_offdvd hlocal_p

/--
RH-O14: singleton `S={r}` の off-dvd local-zero 抽出を
on-set provider として返す wrapper。
-/
def boundaryOffDvdLocalZeroOnSetProvider_singleton_of_insertProvider_and_boundaryDiffPow_factor0
    (side : DkMath.CFBRC.BoundarySide)
    {d x u : ℕ} {σ t : ℝ}
    (r p : {q // Nat.Prime q})
    (provider :
      BoundaryInsertLocalLiftProvider side ({r} : Finset {q // Nat.Prime q}) d x u σ t)
    (hp_dvd : p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u)
    (hp_gap : match side with
      | .right => ¬ p.1 ∣ x
      | .left => ¬ p.1 ∣ u)
    (hwnz_diff :
      ∀ q : {q0 // Nat.Prime q0},
        q.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZeta_exp_s_log_p_sub_one q.1 σ t ≠ 0)
    (hfactor_diff0 :
      ∀ q : {q0 // Nat.Prime q0},
        q.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZetaFactorPhaseVelLocal q.1 σ t = 0) :
    BoundaryOffDvdLocalZeroOnSetProvider
      side ({r} : Finset {q // Nat.Prime q}) d x u σ t := by
  refine ⟨?_⟩
  intro s hs hs_offdvd
  have hs_eq : s = r := Finset.mem_singleton.mp hs
  have hs_offdvd_r : ¬ r.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u := by
    simpa [hs_eq] using hs_offdvd
  have hr0 : hopcPrimeLocalContribution r.1 σ t = 0 :=
    boundary_hlocal_offdvd_singleton_of_insertProvider_and_boundaryDiffPow_factor0
      (side := side) (d := d) (x := x) (u := u) (σ := σ) (t := t)
      (r := r) (p := p) provider hp_dvd hp_gap hs_offdvd_r hwnz_diff hfactor_diff0
  simpa [hs_eq] using hr0

/--
RH-O15: 一般有限集合 `S` 版の 1 点抽出補題。

`insert p S` 上の寄与総和ゼロ（`hsum_lift`）と、
`S.erase r` 上の local-zero が与えられたとき、`r` の local-zero を導く。
RH-O17 で `p ∉ S` の明示仮定を不要化し、`p ∈ S` / `p ∉ S` を内部で分岐処理する。
-/
theorem boundary_hlocal_on_S_of_insertProvider_and_witness_local0_and_local0_on_erase
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (r p : {q // Nat.Prime q})
    (hrS : r ∈ S)
    (provider : BoundaryInsertLocalLiftProvider side S d x u σ t)
    (hp_dvd : p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u)
    (hp_gap : match side with
      | .right => ¬ p.1 ∣ x
      | .left => ¬ p.1 ∣ u)
    (hlocal_p : hopcPrimeLocalContribution p.1 σ t = 0)
    (hlocal_erase :
      ∀ q ∈ S.erase r, hopcPrimeLocalContribution q.1 σ t = 0) :
    hopcPrimeLocalContribution r.1 σ t = 0 := by
  cases side with
  | right =>
      have hsum_insert :
          hopcPrimeContributionSum (S := insert p S) σ t = 0 :=
        provider.hsum_lift p hp_dvd hp_gap
      unfold hopcPrimeContributionSum at hsum_insert
      have hsum :
          (∑ q ∈ S, hopcPrimeLocalContribution q.1 σ t) = 0 := by
        by_cases hp_mem : p ∈ S
        · simpa [Finset.insert_eq_of_mem hp_mem] using hsum_insert
        · rw [Finset.sum_insert hp_mem, hlocal_p, zero_add] at hsum_insert
          exact hsum_insert
      have hdecomp :
          hopcPrimeLocalContribution r.1 σ t +
              (∑ q ∈ S.erase r, hopcPrimeLocalContribution q.1 σ t) =
            (∑ q ∈ S, hopcPrimeLocalContribution q.1 σ t) := by
        calc
          hopcPrimeLocalContribution r.1 σ t +
              (∑ q ∈ S.erase r, hopcPrimeLocalContribution q.1 σ t)
              = (∑ q ∈ insert r (S.erase r), hopcPrimeLocalContribution q.1 σ t) := by
                rw [Finset.sum_insert (by simp)]
          _ = (∑ q ∈ S, hopcPrimeLocalContribution q.1 σ t) := by
            simp [Finset.insert_erase hrS]
      have hsum_erase_zero :
          (∑ q ∈ S.erase r, hopcPrimeLocalContribution q.1 σ t) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro q hq
        exact hlocal_erase q hq
      have hr_plus : hopcPrimeLocalContribution r.1 σ t +
          (∑ q ∈ S.erase r, hopcPrimeLocalContribution q.1 σ t) = 0 := by
        calc
          hopcPrimeLocalContribution r.1 σ t +
              (∑ q ∈ S.erase r, hopcPrimeLocalContribution q.1 σ t)
              = (∑ q ∈ S, hopcPrimeLocalContribution q.1 σ t) := hdecomp
          _ = 0 := hsum
      calc
        hopcPrimeLocalContribution r.1 σ t
            = hopcPrimeLocalContribution r.1 σ t + 0 := by simp
        _ = hopcPrimeLocalContribution r.1 σ t +
              (∑ q ∈ S.erase r, hopcPrimeLocalContribution q.1 σ t) := by
              rw [hsum_erase_zero]
        _ = 0 := hr_plus
  | left =>
      have hsum_insert :
          hopcPrimeContributionSum (S := insert p S) σ t = 0 :=
        provider.hsum_lift p hp_dvd hp_gap
      unfold hopcPrimeContributionSum at hsum_insert
      have hsum :
          (∑ q ∈ S, hopcPrimeLocalContribution q.1 σ t) = 0 := by
        by_cases hp_mem : p ∈ S
        · simpa [Finset.insert_eq_of_mem hp_mem] using hsum_insert
        · rw [Finset.sum_insert hp_mem, hlocal_p, zero_add] at hsum_insert
          exact hsum_insert
      have hdecomp :
          hopcPrimeLocalContribution r.1 σ t +
              (∑ q ∈ S.erase r, hopcPrimeLocalContribution q.1 σ t) =
            (∑ q ∈ S, hopcPrimeLocalContribution q.1 σ t) := by
        calc
          hopcPrimeLocalContribution r.1 σ t +
              (∑ q ∈ S.erase r, hopcPrimeLocalContribution q.1 σ t)
              = (∑ q ∈ insert r (S.erase r), hopcPrimeLocalContribution q.1 σ t) := by
                rw [Finset.sum_insert (by simp)]
          _ = (∑ q ∈ S, hopcPrimeLocalContribution q.1 σ t) := by
            simp [Finset.insert_erase hrS]
      have hsum_erase_zero :
          (∑ q ∈ S.erase r, hopcPrimeLocalContribution q.1 σ t) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro q hq
        exact hlocal_erase q hq
      have hr_plus : hopcPrimeLocalContribution r.1 σ t +
          (∑ q ∈ S.erase r, hopcPrimeLocalContribution q.1 σ t) = 0 := by
        calc
          hopcPrimeLocalContribution r.1 σ t +
              (∑ q ∈ S.erase r, hopcPrimeLocalContribution q.1 σ t)
              = (∑ q ∈ S, hopcPrimeLocalContribution q.1 σ t) := hdecomp
          _ = 0 := hsum
      calc
        hopcPrimeLocalContribution r.1 σ t
            = hopcPrimeLocalContribution r.1 σ t + 0 := by simp
        _ = hopcPrimeLocalContribution r.1 σ t +
              (∑ q ∈ S.erase r, hopcPrimeLocalContribution q.1 σ t) := by
              rw [hsum_erase_zero]
        _ = 0 := hr_plus

/--
RH-O15: 一般有限集合 `S` での on-set provider 構成器。

各 `r ∈ S` について witness prime `p` と `S.erase r` 上 local-zero を供給できるなら、
`BoundaryOffDvdLocalZeroOnSetProvider` を構成できる。
RH-O17 で witness 側から `p ∉ S` 条件を除去した。
-/
def boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_witness_local0_and_local0_on_erase
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (provider : BoundaryInsertLocalLiftProvider side S d x u σ t)
    (hwitness :
      ∀ r ∈ S,
        ∃ p : {q // Nat.Prime q},
          p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u ∧
          (match side with
            | .right => ¬ p.1 ∣ x
            | .left => ¬ p.1 ∣ u) ∧
          hopcPrimeLocalContribution p.1 σ t = 0)
    (hlocal_erase :
      ∀ r ∈ S, ∀ q ∈ S.erase r, hopcPrimeLocalContribution q.1 σ t = 0) :
    BoundaryOffDvdLocalZeroOnSetProvider side S d x u σ t := by
  refine ⟨?_⟩
  intro r hrS _hr_offdvd
  rcases hwitness r hrS with ⟨p, hp_dvd, hp_gap, hlocal_p⟩
  exact boundary_hlocal_on_S_of_insertProvider_and_witness_local0_and_local0_on_erase
    (side := side) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
    (r := r) (p := p) hrS provider hp_dvd
    (by
      cases side <;> simpa using hp_gap)
    hlocal_p
    (hlocal_erase r hrS)

/--
RH-O16: RH-O15 の `hlocal_erase` を、
`boundaryDiffPow` 側 factor0 + `S.erase r` 上の除法仮定から内部生成する wrapper。
-/
theorem boundary_hlocal_on_S_of_insertProvider_and_boundaryDiffPow_factor0_and_dvd_on_erase
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (r p : {q // Nat.Prime q})
    (hrS : r ∈ S)
    (provider : BoundaryInsertLocalLiftProvider side S d x u σ t)
    (hp_dvd : p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u)
    (hp_gap : match side with
      | .right => ¬ p.1 ∣ x
      | .left => ¬ p.1 ∣ u)
    (herase_dvd :
      ∀ q ∈ S.erase r, q.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u)
    (hwnz_diff :
      ∀ q : {q0 // Nat.Prime q0},
        q.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZeta_exp_s_log_p_sub_one q.1 σ t ≠ 0)
    (hfactor_diff0 :
      ∀ q : {q0 // Nat.Prime q0},
        q.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZetaFactorPhaseVelLocal q.1 σ t = 0) :
    hopcPrimeLocalContribution r.1 σ t = 0 := by
  have hlocal_p : hopcPrimeLocalContribution p.1 σ t = 0 :=
    hopcPrimeLocalContribution_eq_zero_of_factorPhaseVelLocal_eq_zero_of_nonzero
      (p := p.1) (σ := σ) (t := t)
      (hwnz_diff p hp_dvd)
      (hfactor_diff0 p hp_dvd)
  have hlocal_erase :
      ∀ q ∈ S.erase r, hopcPrimeLocalContribution q.1 σ t = 0 := by
    intro q hq
    exact hopcPrimeLocalContribution_eq_zero_of_factorPhaseVelLocal_eq_zero_of_nonzero
      (p := q.1) (σ := σ) (t := t)
      (hwnz_diff q (herase_dvd q hq))
      (hfactor_diff0 q (herase_dvd q hq))
  exact boundary_hlocal_on_S_of_insertProvider_and_witness_local0_and_local0_on_erase
    (side := side) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
    (r := r) (p := p) hrS provider hp_dvd hp_gap hlocal_p hlocal_erase

/--
RH-O16: 一般有限集合 `S` での on-set provider 構成器（erase 除法版）。

各 `r ∈ S` について witness prime（divide + gap）と
`S.erase r` 上の `boundaryDiffPow` 除法を供給できれば、
factor0 仮定から `BoundaryOffDvdLocalZeroOnSetProvider` を構成する。
RH-O17 で witness 側から `p ∉ S` 条件を除去した。
-/
def boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_boundaryDiffPow_factor0_and_dvd_on_erase
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (provider : BoundaryInsertLocalLiftProvider side S d x u σ t)
    (hwitness :
      ∀ r ∈ S,
        ∃ p : {q // Nat.Prime q},
          p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u ∧
          (match side with
            | .right => ¬ p.1 ∣ x
            | .left => ¬ p.1 ∣ u))
    (herase_dvd :
      ∀ r ∈ S, ∀ q ∈ S.erase r, q.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u)
    (hwnz_diff :
      ∀ q : {q0 // Nat.Prime q0},
        q.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZeta_exp_s_log_p_sub_one q.1 σ t ≠ 0)
    (hfactor_diff0 :
      ∀ q : {q0 // Nat.Prime q0},
        q.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZetaFactorPhaseVelLocal q.1 σ t = 0) :
    BoundaryOffDvdLocalZeroOnSetProvider side S d x u σ t := by
  refine ⟨?_⟩
  intro r hrS _hr_offdvd
  rcases hwitness r hrS with ⟨p, hp_dvd, hp_gap⟩
  exact boundary_hlocal_on_S_of_insertProvider_and_boundaryDiffPow_factor0_and_dvd_on_erase
    (side := side) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
    (r := r) (p := p) hrS provider hp_dvd
    (by
      cases side <;> simpa using hp_gap)
    (herase_dvd r hrS) hwnz_diff hfactor_diff0

/--
RH-O16: 一般有限集合 `S` での on-set provider 構成器（`S` 全体除法版）。

`∀ q ∈ S, q ∣ boundaryDiffPow` を与えるだけで erase 除法前提を自動生成する。
-/
def boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_boundaryDiffPow_factor0_and_dvd_on_S
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (provider : BoundaryInsertLocalLiftProvider side S d x u σ t)
    (hwitness :
      ∀ r ∈ S,
        ∃ p : {q // Nat.Prime q},
          p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u ∧
          (match side with
            | .right => ¬ p.1 ∣ x
            | .left => ¬ p.1 ∣ u))
    (hS_dvd :
      ∀ q ∈ S, q.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u)
    (hwnz_diff :
      ∀ q : {q0 // Nat.Prime q0},
        q.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZeta_exp_s_log_p_sub_one q.1 σ t ≠ 0)
    (hfactor_diff0 :
      ∀ q : {q0 // Nat.Prime q0},
        q.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZetaFactorPhaseVelLocal q.1 σ t = 0) :
    BoundaryOffDvdLocalZeroOnSetProvider side S d x u σ t := by
  exact boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_boundaryDiffPow_factor0_and_dvd_on_erase
    (side := side) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
    provider hwitness
    (fun r hrS q hq => hS_dvd q (Finset.mem_of_mem_erase hq))
    hwnz_diff hfactor_diff0

/--
RH-O19: `BoundaryInsertLocalLiftProvider` は
「候補 witness `p` を与えたときの持ち上げ則」だけを含み、
`p` の存在そのものは内包しない。

この不足分（global witness existence）を別 record として分離した供給器。
-/
structure BoundaryGlobalWitnessProvider
    (side : DkMath.CFBRC.BoundarySide)
    (d x u : ℕ) : Type where
  hwitness :
    ∃ p : {q // Nat.Prime q},
      p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u ∧
      (match side with
        | .right => ¬ p.1 ∣ x
        | .left => ¬ p.1 ∣ u)

/--
RH-O19: global witness existence + witness local-zero を束ねる供給器。
-/
structure BoundaryGlobalWitnessLocalZeroProvider
    (side : DkMath.CFBRC.BoundarySide)
    (d x u : ℕ) (σ t : ℝ) : Type where
  hwitness :
    ∃ p : {q // Nat.Prime q},
      p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u ∧
      (match side with
        | .right => ¬ p.1 ∣ x
        | .left => ¬ p.1 ∣ u) ∧
      hopcPrimeLocalContribution p.1 σ t = 0

/--
RH-O19: witness existence 命題を `BoundaryGlobalWitnessProvider` に束ねる。
-/
def boundaryGlobalWitnessProvider_of_exists
    (side : DkMath.CFBRC.BoundarySide)
    {d x u : ℕ}
    (hwitness :
      ∃ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u ∧
        (match side with
          | .right => ¬ p.1 ∣ x
          | .left => ¬ p.1 ∣ u)) :
    BoundaryGlobalWitnessProvider side d x u := ⟨hwitness⟩

/--
RH-O19: witness existence + witness local-zero 命題を
`BoundaryGlobalWitnessLocalZeroProvider` に束ねる。
-/
def boundaryGlobalWitnessLocalZeroProvider_of_exists
    (side : DkMath.CFBRC.BoundarySide)
    {d x u : ℕ} {σ t : ℝ}
    (hwitness :
      ∃ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u ∧
        (match side with
          | .right => ¬ p.1 ∣ x
          | .left => ¬ p.1 ∣ u) ∧
        hopcPrimeLocalContribution p.1 σ t = 0) :
    BoundaryGlobalWitnessLocalZeroProvider side d x u σ t := ⟨hwitness⟩

/--
RH-O19: CFBRC primitive-prime existence から
`BoundaryGlobalWitnessProvider` を構成する標準 wrapper。
-/
def boundaryGlobalWitnessProvider_of_cfbRc_primitive_prime_boundaryDiffPow_of_coprime
    (side : DkMath.CFBRC.BoundarySide)
    {d x u : ℕ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : match side with
      | .right => ¬ d ∣ x
      | .left => ¬ d ∣ u) :
    BoundaryGlobalWitnessProvider side d x u := by
  cases side with
  | right =>
      refine ⟨?_⟩
      simpa using
        (exists_boundaryPrime_dvd_gap_of_cfbRc_primitive_prime_boundaryDiffPow_of_coprime
          (side := .right) (d := d) (x := x) (u := u)
          hd_prime hd_ge hx hu hcop hpnd)
  | left =>
      refine ⟨?_⟩
      simpa using
        (exists_boundaryPrime_dvd_gap_of_cfbRc_primitive_prime_boundaryDiffPow_of_coprime
          (side := .left) (d := d) (x := x) (u := u)
          hd_prime hd_ge hx hu hcop hpnd)

/--
RH-O18: 一般有限集合 `S` での on-set provider 構成器（global witness + erase local-zero 版）。

`r` ごとの witness ではなく、共通 witness prime を 1 つ与えるだけで
RH-O15 の on-set provider 構成器へ接続する。
-/
def boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_global_witness_local0_and_local0_on_erase
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (provider : BoundaryInsertLocalLiftProvider side S d x u σ t)
    (hwitness :
      ∃ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u ∧
        (match side with
          | .right => ¬ p.1 ∣ x
          | .left => ¬ p.1 ∣ u) ∧
        hopcPrimeLocalContribution p.1 σ t = 0)
    (hlocal_erase :
      ∀ r ∈ S, ∀ q ∈ S.erase r, hopcPrimeLocalContribution q.1 σ t = 0) :
    BoundaryOffDvdLocalZeroOnSetProvider side S d x u σ t := by
  cases side with
  | right =>
      classical
      let p : {q // Nat.Prime q} := Classical.choose hwitness
      have hp_dvd : p.1 ∣ DkMath.CFBRC.boundaryDiffPow .right d x u := by
        simpa [p] using (Classical.choose_spec hwitness).1
      have hp_gap : ¬ p.1 ∣ x := by
        simpa [p] using (Classical.choose_spec hwitness).2.1
      have hlocal_p : hopcPrimeLocalContribution p.1 σ t = 0 := by
        simpa [p] using (Classical.choose_spec hwitness).2.2
      exact boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_witness_local0_and_local0_on_erase
        (side := .right) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
        provider
        (fun r hrS => ⟨p, hp_dvd, hp_gap, hlocal_p⟩)
        hlocal_erase
  | left =>
      classical
      let p : {q // Nat.Prime q} := Classical.choose hwitness
      have hp_dvd : p.1 ∣ DkMath.CFBRC.boundaryDiffPow .left d x u := by
        simpa [p] using (Classical.choose_spec hwitness).1
      have hp_gap : ¬ p.1 ∣ u := by
        simpa [p] using (Classical.choose_spec hwitness).2.1
      have hlocal_p : hopcPrimeLocalContribution p.1 σ t = 0 := by
        simpa [p] using (Classical.choose_spec hwitness).2.2
      exact boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_witness_local0_and_local0_on_erase
        (side := .left) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
        provider
        (fun r hrS => ⟨p, hp_dvd, hp_gap, hlocal_p⟩)
        hlocal_erase

/--
RH-O18: 一般有限集合 `S` での on-set provider 構成器
（global witness + factor0 + erase 除法版）。

`r` ごとの witness を要求せず、共通 witness prime を 1 つ与えれば
RH-O16 erase 除法版へ接続できる。
-/
def boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_boundaryDiffPow_factor0_and_dvd_on_erase_of_global_witness
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (provider : BoundaryInsertLocalLiftProvider side S d x u σ t)
    (hwitness :
      ∃ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u ∧
        (match side with
          | .right => ¬ p.1 ∣ x
          | .left => ¬ p.1 ∣ u))
    (herase_dvd :
      ∀ r ∈ S, ∀ q ∈ S.erase r, q.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u)
    (hwnz_diff :
      ∀ q : {q0 // Nat.Prime q0},
        q.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZeta_exp_s_log_p_sub_one q.1 σ t ≠ 0)
    (hfactor_diff0 :
      ∀ q : {q0 // Nat.Prime q0},
        q.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZetaFactorPhaseVelLocal q.1 σ t = 0) :
    BoundaryOffDvdLocalZeroOnSetProvider side S d x u σ t := by
  cases side with
  | right =>
      classical
      let p : {q // Nat.Prime q} := Classical.choose hwitness
      have hp_dvd : p.1 ∣ DkMath.CFBRC.boundaryDiffPow .right d x u := by
        simpa [p] using (Classical.choose_spec hwitness).1
      have hp_gap : ¬ p.1 ∣ x := by
        simpa [p] using (Classical.choose_spec hwitness).2
      exact boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_boundaryDiffPow_factor0_and_dvd_on_erase
        (side := .right) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
        provider
        (fun r hrS => ⟨p, hp_dvd, hp_gap⟩)
        herase_dvd hwnz_diff hfactor_diff0
  | left =>
      classical
      let p : {q // Nat.Prime q} := Classical.choose hwitness
      have hp_dvd : p.1 ∣ DkMath.CFBRC.boundaryDiffPow .left d x u := by
        simpa [p] using (Classical.choose_spec hwitness).1
      have hp_gap : ¬ p.1 ∣ u := by
        simpa [p] using (Classical.choose_spec hwitness).2
      exact boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_boundaryDiffPow_factor0_and_dvd_on_erase
        (side := .left) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
        provider
        (fun r hrS => ⟨p, hp_dvd, hp_gap⟩)
        herase_dvd hwnz_diff hfactor_diff0

/--
RH-O18: 一般有限集合 `S` での on-set provider 構成器
（global witness + factor0 + `S` 全体除法版）。
-/
def boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_boundaryDiffPow_factor0_and_dvd_on_S_of_global_witness
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (provider : BoundaryInsertLocalLiftProvider side S d x u σ t)
    (hwitness :
      ∃ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u ∧
        (match side with
          | .right => ¬ p.1 ∣ x
          | .left => ¬ p.1 ∣ u))
    (hS_dvd :
      ∀ q ∈ S, q.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u)
    (hwnz_diff :
      ∀ q : {q0 // Nat.Prime q0},
        q.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZeta_exp_s_log_p_sub_one q.1 σ t ≠ 0)
    (hfactor_diff0 :
      ∀ q : {q0 // Nat.Prime q0},
        q.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZetaFactorPhaseVelLocal q.1 σ t = 0) :
    BoundaryOffDvdLocalZeroOnSetProvider side S d x u σ t := by
  cases side with
  | right =>
      classical
      let p : {q // Nat.Prime q} := Classical.choose hwitness
      have hp_dvd : p.1 ∣ DkMath.CFBRC.boundaryDiffPow .right d x u := by
        simpa [p] using (Classical.choose_spec hwitness).1
      have hp_gap : ¬ p.1 ∣ x := by
        simpa [p] using (Classical.choose_spec hwitness).2
      exact boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_boundaryDiffPow_factor0_and_dvd_on_S
        (side := .right) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
        provider
        (fun r hrS => ⟨p, hp_dvd, hp_gap⟩)
        hS_dvd hwnz_diff hfactor_diff0
  | left =>
      classical
      let p : {q // Nat.Prime q} := Classical.choose hwitness
      have hp_dvd : p.1 ∣ DkMath.CFBRC.boundaryDiffPow .left d x u := by
        simpa [p] using (Classical.choose_spec hwitness).1
      have hp_gap : ¬ p.1 ∣ u := by
        simpa [p] using (Classical.choose_spec hwitness).2
      exact boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_boundaryDiffPow_factor0_and_dvd_on_S
        (side := .left) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
        provider
        (fun r hrS => ⟨p, hp_dvd, hp_gap⟩)
        hS_dvd hwnz_diff hfactor_diff0

/--
RH-O18: CFBRC primitive-prime existence を使い、
global witness を自動生成して RH-O18 の `S` 全体除法版へ接続する wrapper。
-/
def boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_boundaryDiffPow_factor0_and_dvd_on_S_of_cfbRc_primitive_prime_boundaryDiffPow_of_coprime
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : match side with
      | .right => ¬ d ∣ x
      | .left => ¬ d ∣ u)
    (provider : BoundaryInsertLocalLiftProvider side S d x u σ t)
    (hS_dvd :
      ∀ q ∈ S, q.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u)
    (hwnz_diff :
      ∀ q : {q0 // Nat.Prime q0},
        q.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZeta_exp_s_log_p_sub_one q.1 σ t ≠ 0)
    (hfactor_diff0 :
      ∀ q : {q0 // Nat.Prime q0},
        q.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZetaFactorPhaseVelLocal q.1 σ t = 0) :
    BoundaryOffDvdLocalZeroOnSetProvider side S d x u σ t := by
  cases side with
  | right =>
      have hwitness :
          ∃ p : {q // Nat.Prime q},
            p.1 ∣ DkMath.CFBRC.boundaryDiffPow .right d x u ∧
            ¬ p.1 ∣ x := by
        simpa using
          (exists_boundaryPrime_dvd_gap_of_cfbRc_primitive_prime_boundaryDiffPow_of_coprime
            (side := .right) (d := d) (x := x) (u := u)
            hd_prime hd_ge hx hu hcop hpnd)
      exact boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_boundaryDiffPow_factor0_and_dvd_on_S
        (side := .right) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
        provider
        (fun r hrS => by
          rcases hwitness with ⟨p, hp_dvd, hp_gap⟩
          exact ⟨p, hp_dvd, hp_gap⟩)
        hS_dvd hwnz_diff hfactor_diff0
  | left =>
      have hwitness :
          ∃ p : {q // Nat.Prime q},
            p.1 ∣ DkMath.CFBRC.boundaryDiffPow .left d x u ∧
            ¬ p.1 ∣ u := by
        simpa using
          (exists_boundaryPrime_dvd_gap_of_cfbRc_primitive_prime_boundaryDiffPow_of_coprime
            (side := .left) (d := d) (x := x) (u := u)
            hd_prime hd_ge hx hu hcop hpnd)
      exact boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_boundaryDiffPow_factor0_and_dvd_on_S
        (side := .left) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
        provider
        (fun r hrS => by
          rcases hwitness with ⟨p, hp_dvd, hp_gap⟩
          exact ⟨p, hp_dvd, hp_gap⟩)
        hS_dvd hwnz_diff hfactor_diff0

/--
RH-O19: witness-local-zero provider を使って、
RH-O18（global witness + erase local-zero）へ接続する wrapper。
-/
def boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_globalWitnessLocalZeroProvider_and_local0_on_erase
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (provider : BoundaryInsertLocalLiftProvider side S d x u σ t)
    (witnessProvider : BoundaryGlobalWitnessLocalZeroProvider side d x u σ t)
    (hlocal_erase :
      ∀ r ∈ S, ∀ q ∈ S.erase r, hopcPrimeLocalContribution q.1 σ t = 0) :
    BoundaryOffDvdLocalZeroOnSetProvider side S d x u σ t := by
  cases side with
  | right =>
      exact boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_witness_local0_and_local0_on_erase
        (side := .right) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
        provider
        (fun r hrS => by
          rcases witnessProvider.hwitness with ⟨p, hp_dvd, hp_gap, hlocal_p⟩
          exact ⟨p, hp_dvd, hp_gap, hlocal_p⟩)
        hlocal_erase
  | left =>
      exact boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_witness_local0_and_local0_on_erase
        (side := .left) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
        provider
        (fun r hrS => by
          rcases witnessProvider.hwitness with ⟨p, hp_dvd, hp_gap, hlocal_p⟩
          exact ⟨p, hp_dvd, hp_gap, hlocal_p⟩)
        hlocal_erase

/--
RH-O19: witness provider を使って、
RH-O18（global witness + factor0 + `S` 全体除法版）へ接続する wrapper。
-/
def boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_boundaryDiffPow_factor0_and_dvd_on_S_of_globalWitnessProvider
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (provider : BoundaryInsertLocalLiftProvider side S d x u σ t)
    (witnessProvider : BoundaryGlobalWitnessProvider side d x u)
    (hS_dvd :
      ∀ q ∈ S, q.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u)
    (hwnz_diff :
      ∀ q : {q0 // Nat.Prime q0},
        q.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZeta_exp_s_log_p_sub_one q.1 σ t ≠ 0)
    (hfactor_diff0 :
      ∀ q : {q0 // Nat.Prime q0},
        q.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZetaFactorPhaseVelLocal q.1 σ t = 0) :
    BoundaryOffDvdLocalZeroOnSetProvider side S d x u σ t := by
  cases side with
  | right =>
      exact boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_boundaryDiffPow_factor0_and_dvd_on_S
        (side := .right) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
        provider
        (fun r hrS => by
          rcases witnessProvider.hwitness with ⟨p, hp_dvd, hp_gap⟩
          exact ⟨p, hp_dvd, hp_gap⟩)
        hS_dvd hwnz_diff hfactor_diff0
  | left =>
      exact boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_boundaryDiffPow_factor0_and_dvd_on_S
        (side := .left) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
        provider
        (fun r hrS => by
          rcases witnessProvider.hwitness with ⟨p, hp_dvd, hp_gap⟩
          exact ⟨p, hp_dvd, hp_gap⟩)
        hS_dvd hwnz_diff hfactor_diff0

/--
RH-O19: CFBRC primitive-prime existence から witness provider を構成し、
RH-O19 の witness-provider 版 wrapper へ接続する。
-/
def boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_boundaryDiffPow_factor0_and_dvd_on_S_of_globalWitnessProvider_of_cfbRc_primitive_prime_boundaryDiffPow_of_coprime
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : match side with
      | .right => ¬ d ∣ x
      | .left => ¬ d ∣ u)
    (provider : BoundaryInsertLocalLiftProvider side S d x u σ t)
    (hS_dvd :
      ∀ q ∈ S, q.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u)
    (hwnz_diff :
      ∀ q : {q0 // Nat.Prime q0},
        q.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZeta_exp_s_log_p_sub_one q.1 σ t ≠ 0)
    (hfactor_diff0 :
      ∀ q : {q0 // Nat.Prime q0},
        q.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZetaFactorPhaseVelLocal q.1 σ t = 0) :
    BoundaryOffDvdLocalZeroOnSetProvider side S d x u σ t :=
  boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_boundaryDiffPow_factor0_and_dvd_on_S_of_globalWitnessProvider
    (side := side) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
    provider
    (boundaryGlobalWitnessProvider_of_cfbRc_primitive_prime_boundaryDiffPow_of_coprime
      (side := side) (d := d) (x := x) (u := u)
      hd_prime hd_ge hx hu hcop hpnd)
    hS_dvd hwnz_diff hfactor_diff0

/--
RH-O20: `boundaryDiffPow` を割る側の
`w_p ≠ 0` と factor 位相速度ゼロを束ねる供給器。
-/
structure BoundaryDiffPowFactorZeroProvider
    (side : DkMath.CFBRC.BoundarySide)
    (d x u : ℕ) (σ t : ℝ) : Type where
  hwnz_diff :
    ∀ q : {q0 // Nat.Prime q0},
      q.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
        eulerZeta_exp_s_log_p_sub_one q.1 σ t ≠ 0
  hfactor_diff0 :
    ∀ q : {q0 // Nat.Prime q0},
      q.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
        eulerZetaFactorPhaseVelLocal q.1 σ t = 0

/--
RH-O20: `hwnz_diff` / `hfactor_diff0` 関数を
`BoundaryDiffPowFactorZeroProvider` へ束ねる標準構成器。
-/
def boundaryDiffPowFactorZeroProvider_of_split
    (side : DkMath.CFBRC.BoundarySide)
    {d x u : ℕ} {σ t : ℝ}
    (hwnz_diff :
      ∀ q : {q0 // Nat.Prime q0},
        q.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZeta_exp_s_log_p_sub_one q.1 σ t ≠ 0)
    (hfactor_diff0 :
      ∀ q : {q0 // Nat.Prime q0},
        q.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZetaFactorPhaseVelLocal q.1 σ t = 0) :
    BoundaryDiffPowFactorZeroProvider side d x u σ t :=
  ⟨hwnz_diff, hfactor_diff0⟩

/--
RH-O20: 命名統一版（推奨）
`insert-provider + witnessProvider + diffFactorProvider + S 全体除法` から
on-set off-dvd local-zero provider を構成する。
-/
def boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_dvd_on_S_of_globalWitnessProvider_and_diffFactorZeroProvider
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (provider : BoundaryInsertLocalLiftProvider side S d x u σ t)
    (witnessProvider : BoundaryGlobalWitnessProvider side d x u)
    (diffProvider : BoundaryDiffPowFactorZeroProvider side d x u σ t)
    (hS_dvd :
      ∀ q ∈ S, q.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u) :
    BoundaryOffDvdLocalZeroOnSetProvider side S d x u σ t :=
  boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_boundaryDiffPow_factor0_and_dvd_on_S_of_globalWitnessProvider
    (side := side) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
    provider witnessProvider hS_dvd diffProvider.hwnz_diff diffProvider.hfactor_diff0

/--
RH-O20: 命名統一版（推奨）
CFBRC primitive-prime existence から witness provider を自動生成し、
`diffFactorProvider` と `hS_dvd` だけで on-set provider を構成する。
-/
def boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_dvd_on_S_of_cfbRc_primitive_prime_and_diffFactorZeroProvider
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : match side with
      | .right => ¬ d ∣ x
      | .left => ¬ d ∣ u)
    (provider : BoundaryInsertLocalLiftProvider side S d x u σ t)
    (diffProvider : BoundaryDiffPowFactorZeroProvider side d x u σ t)
    (hS_dvd :
      ∀ q ∈ S, q.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u) :
    BoundaryOffDvdLocalZeroOnSetProvider side S d x u σ t :=
  boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_dvd_on_S_of_globalWitnessProvider_and_diffFactorZeroProvider
    (side := side) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
    provider
    (boundaryGlobalWitnessProvider_of_cfbRc_primitive_prime_boundaryDiffPow_of_coprime
      (side := side) (d := d) (x := x) (u := u)
      hd_prime hd_ge hx hu hcop hpnd)
    diffProvider hS_dvd

/--
RH-O21: 命名統一版（推奨）
`insert-provider + witnessProvider + diffFactorProvider + erase 除法` から
on-set off-dvd local-zero provider を構成する。
-/
def boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_dvd_on_erase_of_globalWitnessProvider_and_diffFactorZeroProvider
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (provider : BoundaryInsertLocalLiftProvider side S d x u σ t)
    (witnessProvider : BoundaryGlobalWitnessProvider side d x u)
    (diffProvider : BoundaryDiffPowFactorZeroProvider side d x u σ t)
    (herase_dvd :
      ∀ r ∈ S, ∀ q ∈ S.erase r, q.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u) :
    BoundaryOffDvdLocalZeroOnSetProvider side S d x u σ t := by
  cases side with
  | right =>
      exact boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_boundaryDiffPow_factor0_and_dvd_on_erase
        (side := .right) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
        provider
        (fun r hrS => by
          rcases witnessProvider.hwitness with ⟨p, hp_dvd, hp_gap⟩
          exact ⟨p, hp_dvd, hp_gap⟩)
        herase_dvd diffProvider.hwnz_diff diffProvider.hfactor_diff0
  | left =>
      exact boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_boundaryDiffPow_factor0_and_dvd_on_erase
        (side := .left) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
        provider
        (fun r hrS => by
          rcases witnessProvider.hwitness with ⟨p, hp_dvd, hp_gap⟩
          exact ⟨p, hp_dvd, hp_gap⟩)
        herase_dvd diffProvider.hwnz_diff diffProvider.hfactor_diff0

-- RH-O21/RH-O22: 旧 `..._global_witness...` 命名は互換維持のみ。
-- 新規利用は provider ベース命名（RH-O20/O21）へ移行し、
-- 削除候補日は 2026-06-30（以降、移行完了を確認して撤去）とする。
attribute [deprecated boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_globalWitnessLocalZeroProvider_and_local0_on_erase
  (since := "2026-03-13")]
  boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_global_witness_local0_and_local0_on_erase

attribute [deprecated boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_dvd_on_erase_of_globalWitnessProvider_and_diffFactorZeroProvider
  (since := "2026-03-13")]
  boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_boundaryDiffPow_factor0_and_dvd_on_erase_of_global_witness

attribute [deprecated boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_dvd_on_S_of_globalWitnessProvider_and_diffFactorZeroProvider
  (since := "2026-03-13")]
  boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_boundaryDiffPow_factor0_and_dvd_on_S_of_global_witness

attribute [deprecated boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_dvd_on_S_of_cfbRc_primitive_prime_and_diffFactorZeroProvider
  (since := "2026-03-13")]
  boundaryOffDvdLocalZeroOnSetProvider_of_insertProvider_and_boundaryDiffPow_factor0_and_dvd_on_S_of_cfbRc_primitive_prime_boundaryDiffPow_of_coprime

/--
RH-O12: off-dvd 側の非零 (`w_p ≠ 0`) と factor 位相速度ゼロを束ねる供給器。
-/
structure BoundaryOffDvdFactorZeroProvider
    (side : DkMath.CFBRC.BoundarySide)
    (d x u : ℕ) (σ t : ℝ) : Type where
  hwnz_offdvd :
    ∀ p : {q // Nat.Prime q},
      ¬ p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
        eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0
  hfactor_offdvd0 :
    ∀ p : {q // Nat.Prime q},
      ¬ p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
        eulerZetaFactorPhaseVelLocal p.1 σ t = 0

/--
RH-O13: off-dvd 側の非零/因子位相速度ゼロ仮定を
`BoundaryOffDvdFactorZeroProvider` へ束ねる標準構成器。
-/
def boundaryOffDvdFactorZeroProvider_of_split
    (side : DkMath.CFBRC.BoundarySide)
    {d x u : ℕ} {σ t : ℝ}
    (hwnz_offdvd :
      ∀ p : {q // Nat.Prime q},
        ¬ p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hfactor_offdvd0 :
      ∀ p : {q // Nat.Prime q},
        ¬ p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZetaFactorPhaseVelLocal p.1 σ t = 0) :
    BoundaryOffDvdFactorZeroProvider side d x u σ t :=
  ⟨hwnz_offdvd, hfactor_offdvd0⟩

/--
RH-O13: off-dvd 側の非零供給と local-zero provider から
`BoundaryOffDvdFactorZeroProvider` を構成する。
-/
def boundaryOffDvdFactorZeroProvider_of_nonzero_and_localZeroProvider
    (side : DkMath.CFBRC.BoundarySide)
    {d x u : ℕ} {σ t : ℝ}
    (hwnz_offdvd :
      ∀ p : {q // Nat.Prime q},
        ¬ p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (offdvdProvider : BoundaryOffDvdLocalZeroProvider side d x u σ t) :
    BoundaryOffDvdFactorZeroProvider side d x u σ t := by
  refine ⟨hwnz_offdvd, ?_⟩
  intro p hp_offdvd
  exact eulerZetaFactorPhaseVelLocal_eq_zero_of_hopcPrimeLocalContribution_eq_zero_of_nonzero
    (p := p.1) (σ := σ) (t := t)
    (hwnz_offdvd p hp_offdvd)
    (offdvdProvider.hlocal_offdvd p hp_offdvd)

/--
RH-O13: insert-provider と off-dvd 側 local-zero provider から
`BoundaryOffDvdFactorZeroProvider` を構成する変換規則。
-/
def boundaryOffDvdFactorZeroProvider_of_boundaryInsertLocalLiftProvider_of_nonzero_and_localZeroProvider
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (_provider : BoundaryInsertLocalLiftProvider side S d x u σ t)
    (hwnz_offdvd :
      ∀ p : {q // Nat.Prime q},
        ¬ p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (offdvdProvider : BoundaryOffDvdLocalZeroProvider side d x u σ t) :
    BoundaryOffDvdFactorZeroProvider side d x u σ t :=
  boundaryOffDvdFactorZeroProvider_of_nonzero_and_localZeroProvider
    (side := side) (d := d) (x := x) (u := u) (σ := σ) (t := t)
    hwnz_offdvd offdvdProvider

/--
RH-O13: insert-provider と off-dvd 側 local-zero 仮定（関数形式）から
`BoundaryOffDvdFactorZeroProvider` を構成する標準 wrapper。
-/
def boundaryOffDvdFactorZeroProvider_of_boundaryInsertLocalLiftProvider_of_nonzero_and_local_zero
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (provider : BoundaryInsertLocalLiftProvider side S d x u σ t)
    (hwnz_offdvd :
      ∀ p : {q // Nat.Prime q},
        ¬ p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hlocal_offdvd :
      ∀ p : {q // Nat.Prime q},
        ¬ p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          hopcPrimeLocalContribution p.1 σ t = 0) :
    BoundaryOffDvdFactorZeroProvider side d x u σ t := by
  let offdvdProvider : BoundaryOffDvdLocalZeroProvider side d x u σ t :=
    ⟨hlocal_offdvd⟩
  exact
    boundaryOffDvdFactorZeroProvider_of_boundaryInsertLocalLiftProvider_of_nonzero_and_localZeroProvider
      (side := side) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
      provider hwnz_offdvd offdvdProvider

/--
RH-O12: off-dvd factor0 provider から local-zero provider を構成する。
-/
def boundaryOffDvdLocalZeroProvider_of_offdvdFactorZeroProvider
    (side : DkMath.CFBRC.BoundarySide)
    {d x u : ℕ} {σ t : ℝ}
    (offdvdFactorProvider : BoundaryOffDvdFactorZeroProvider side d x u σ t) :
    BoundaryOffDvdLocalZeroProvider side d x u σ t := by
  refine ⟨?_⟩
  intro p hp_offdvd
  exact hopcPrimeLocalContribution_eq_zero_of_factorPhaseVelLocal_eq_zero_of_nonzero
    (p := p.1) (σ := σ) (t := t)
    (offdvdFactorProvider.hwnz_offdvd p hp_offdvd)
    (offdvdFactorProvider.hfactor_offdvd0 p hp_offdvd)

/--
RH-O10: `BoundaryInsertLocalLiftProvider` から off-dvd local-zero provider へ落とす
最小変換規則（追加の off-dvd local-zero 仮定を受け取る）。
-/
def boundaryOffDvdLocalZeroProvider_of_boundaryInsertLocalLiftProvider
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (_provider : BoundaryInsertLocalLiftProvider side S d x u σ t)
    (hlocal_offdvd :
      ∀ p : {q // Nat.Prime q},
        ¬ p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          hopcPrimeLocalContribution p.1 σ t = 0) :
    BoundaryOffDvdLocalZeroProvider side d x u σ t :=
  ⟨hlocal_offdvd⟩

/--
RH-O9: off-dvd 側で `w_p ≠ 0` と factor 位相速度ゼロが供給できるとき、
`BoundaryOffDvdLocalZeroProvider` を構成する。
-/
def boundaryOffDvdLocalZeroProvider_of_factorPhaseVelLocal_eq_zero
    (side : DkMath.CFBRC.BoundarySide)
    {d x u : ℕ} {σ t : ℝ}
    (hwnz_offdvd :
      ∀ p : {q // Nat.Prime q},
        ¬ p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hfactor_offdvd0 :
      ∀ p : {q // Nat.Prime q},
        ¬ p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZetaFactorPhaseVelLocal p.1 σ t = 0) :
    BoundaryOffDvdLocalZeroProvider side d x u σ t := by
  refine ⟨?_⟩
  intro p hp_offdvd
  exact hopcPrimeLocalContribution_eq_zero_of_factorPhaseVelLocal_eq_zero_of_nonzero
    (p := p.1) (σ := σ) (t := t)
    (hwnz_offdvd p hp_offdvd) (hfactor_offdvd0 p hp_offdvd)

/--
RH-O10: `BoundaryInsertLocalLiftProvider` から、
off-dvd 側の `w_p ≠ 0` と factor 位相速度ゼロ仮定を用いて
`BoundaryOffDvdLocalZeroProvider` を構成する変換規則。
-/
def boundaryOffDvdLocalZeroProvider_of_boundaryInsertLocalLiftProvider_of_factorPhaseVelLocal_eq_zero
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (_provider : BoundaryInsertLocalLiftProvider side S d x u σ t)
    (hwnz_offdvd :
      ∀ p : {q // Nat.Prime q},
        ¬ p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hfactor_offdvd0 :
      ∀ p : {q // Nat.Prime q},
        ¬ p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZetaFactorPhaseVelLocal p.1 σ t = 0) :
    BoundaryOffDvdLocalZeroProvider side d x u σ t :=
  boundaryOffDvdLocalZeroProvider_of_factorPhaseVelLocal_eq_zero
    (side := side) (d := d) (x := x) (u := u) (σ := σ) (t := t)
    hwnz_offdvd hfactor_offdvd0

/--
RH-O12: `BoundaryInsertLocalLiftProvider` と off-dvd factor0 provider から
off-dvd local-zero provider を構成する。
-/
def boundaryOffDvdLocalZeroProvider_of_boundaryInsertLocalLiftProvider_of_offdvdFactorZeroProvider
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t : ℝ}
    (_provider : BoundaryInsertLocalLiftProvider side S d x u σ t)
    (offdvdFactorProvider : BoundaryOffDvdFactorZeroProvider side d x u σ t) :
    BoundaryOffDvdLocalZeroProvider side d x u σ t :=
  boundaryOffDvdLocalZeroProvider_of_offdvdFactorZeroProvider
    (side := side) (d := d) (x := x) (u := u) (σ := σ) (t := t)
    offdvdFactorProvider

/--
RH-O12: insert-provider + off-dvd factor0 provider から、
`|hopcPrimeContributionFn| ≤ C / p^σ` を直接得る高位 wrapper。
-/
theorem hopcPrimeContributionFn_abs_le_prime_rpow_of_boundaryDiffPow_factor0_with_insertProvider_and_offdvdFactorZeroProvider
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t C : ℝ}
    (hC : 0 ≤ C)
    (hwnz_diff :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hfactor_diff0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZetaFactorPhaseVelLocal p.1 σ t = 0)
    (provider : BoundaryInsertLocalLiftProvider side S d x u σ t)
    (offdvdFactorProvider : BoundaryOffDvdFactorZeroProvider side d x u σ t) :
    ∀ p : {q // Nat.Prime q},
      |hopcPrimeContributionFn σ t p| ≤ C / (↑p : ℝ) ^ σ := by
  let offdvdProvider : BoundaryOffDvdLocalZeroProvider side d x u σ t :=
    boundaryOffDvdLocalZeroProvider_of_boundaryInsertLocalLiftProvider_of_offdvdFactorZeroProvider
      (side := side) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
      provider offdvdFactorProvider
  exact
    hopcPrimeContributionFn_abs_le_prime_rpow_of_boundaryDiffPow_factor0_with_offdvd_local0
      (side := side) (d := d) (x := x) (u := u) (σ := σ) (t := t) (C := C)
      hC hwnz_diff hfactor_diff0 offdvdProvider.hlocal_offdvd

/--
RH-O12: insert-provider + off-dvd factor0 provider から、
`hopcPrimeContributionTsum = 0` を直接得る高位 wrapper。
-/
theorem hopcPrimeContributionTsum_eq_zero_of_boundaryDiffPow_factor0_with_insertProvider_and_offdvdFactorZeroProvider_sigma_gt_one
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t C : ℝ}
    (hσ : 1 < σ) (hC : 0 ≤ C)
    (hwnz_diff :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hfactor_diff0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZetaFactorPhaseVelLocal p.1 σ t = 0)
    (provider : BoundaryInsertLocalLiftProvider side S d x u σ t)
    (offdvdFactorProvider : BoundaryOffDvdFactorZeroProvider side d x u σ t)
    (hEvStationary :
      ∀ᶠ S : Finset {q // Nat.Prime q} in Filter.atTop,
        DkMath.RH.stationaryAt
          (fun v : ℝ => eulerZetaFinite_onVertical S σ v) t) :
    hopcPrimeContributionTsum σ t = 0 := by
  let offdvdProvider : BoundaryOffDvdLocalZeroProvider side d x u σ t :=
    boundaryOffDvdLocalZeroProvider_of_boundaryInsertLocalLiftProvider_of_offdvdFactorZeroProvider
      (side := side) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
      provider offdvdFactorProvider
  exact
    hopcPrimeContributionTsum_eq_zero_of_boundaryDiffPow_factor0_with_offdvd_local0_sigma_gt_one
      (side := side) (d := d) (x := x) (u := u) (σ := σ) (t := t) (C := C)
      hσ hC hwnz_diff hfactor_diff0 offdvdProvider.hlocal_offdvd hEvStationary

/--
RH-O12: insert-provider + off-dvd factor0 provider から、
有限寄与和の atTop 極限（0）を直接得る高位 wrapper。
-/
theorem tendsto_hopcPrimeContributionSum_atTop_of_boundaryDiffPow_factor0_with_insertProvider_and_offdvdFactorZeroProvider_sigma_gt_one
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t C : ℝ}
    (hσ : 1 < σ) (hC : 0 ≤ C)
    (hwnz_diff :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hfactor_diff0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZetaFactorPhaseVelLocal p.1 σ t = 0)
    (provider : BoundaryInsertLocalLiftProvider side S d x u σ t)
    (offdvdFactorProvider : BoundaryOffDvdFactorZeroProvider side d x u σ t)
    (hEvStationary :
      ∀ᶠ S : Finset {q // Nat.Prime q} in Filter.atTop,
        DkMath.RH.stationaryAt
          (fun v : ℝ => eulerZetaFinite_onVertical S σ v) t) :
    Filter.Tendsto
      (fun S : Finset {p // Nat.Prime p} =>
        hopcPrimeContributionSum (S := S) σ t)
      Filter.atTop (𝓝 (0 : ℝ)) := by
  let offdvdProvider : BoundaryOffDvdLocalZeroProvider side d x u σ t :=
    boundaryOffDvdLocalZeroProvider_of_boundaryInsertLocalLiftProvider_of_offdvdFactorZeroProvider
      (side := side) (S := S) (d := d) (x := x) (u := u) (σ := σ) (t := t)
      provider offdvdFactorProvider
  exact
    tendsto_hopcPrimeContributionSum_atTop_of_boundaryDiffPow_factor0_with_offdvd_local0_sigma_gt_one
      (side := side) (d := d) (x := x) (u := u) (σ := σ) (t := t) (C := C)
      hσ hC hwnz_diff hfactor_diff0 offdvdProvider.hlocal_offdvd hEvStationary

/--
RH-O11: `BoundaryInsertLocalLiftProvider` と off-dvd 側 factor0 供給から、
`|hopcPrimeContributionFn| ≤ C / p^σ` を直接得る高位 wrapper。
-/
theorem hopcPrimeContributionFn_abs_le_prime_rpow_of_boundaryDiffPow_factor0_with_insertProvider_sigma
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t C : ℝ}
    (hC : 0 ≤ C)
    (hwnz_diff :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hfactor_diff0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZetaFactorPhaseVelLocal p.1 σ t = 0)
    (provider : BoundaryInsertLocalLiftProvider side S d x u σ t)
    (hwnz_offdvd :
      ∀ p : {q // Nat.Prime q},
        ¬ p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hfactor_offdvd0 :
      ∀ p : {q // Nat.Prime q},
        ¬ p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZetaFactorPhaseVelLocal p.1 σ t = 0) :
    ∀ p : {q // Nat.Prime q},
      |hopcPrimeContributionFn σ t p| ≤ C / (↑p : ℝ) ^ σ := by
  let offdvdFactorProvider : BoundaryOffDvdFactorZeroProvider side d x u σ t :=
    boundaryOffDvdFactorZeroProvider_of_split
      (side := side) (d := d) (x := x) (u := u) (σ := σ) (t := t)
      hwnz_offdvd hfactor_offdvd0
  exact
    hopcPrimeContributionFn_abs_le_prime_rpow_of_boundaryDiffPow_factor0_with_insertProvider_and_offdvdFactorZeroProvider
      (side := side) (d := d) (x := x) (u := u) (σ := σ) (t := t) (C := C)
      (S := S) hC hwnz_diff hfactor_diff0 provider offdvdFactorProvider

/--
RH-O11: `BoundaryInsertLocalLiftProvider` と off-dvd 側 factor0 供給から、
`hopcPrimeContributionTsum = 0` を直接得る高位 wrapper。
-/
theorem hopcPrimeContributionTsum_eq_zero_of_boundaryDiffPow_factor0_with_insertProvider_sigma_gt_one
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t C : ℝ}
    (hσ : 1 < σ) (hC : 0 ≤ C)
    (hwnz_diff :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hfactor_diff0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZetaFactorPhaseVelLocal p.1 σ t = 0)
    (provider : BoundaryInsertLocalLiftProvider side S d x u σ t)
    (hwnz_offdvd :
      ∀ p : {q // Nat.Prime q},
        ¬ p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hfactor_offdvd0 :
      ∀ p : {q // Nat.Prime q},
        ¬ p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZetaFactorPhaseVelLocal p.1 σ t = 0)
    (hEvStationary :
      ∀ᶠ S : Finset {q // Nat.Prime q} in Filter.atTop,
        DkMath.RH.stationaryAt
          (fun v : ℝ => eulerZetaFinite_onVertical S σ v) t) :
    hopcPrimeContributionTsum σ t = 0 := by
  let offdvdFactorProvider : BoundaryOffDvdFactorZeroProvider side d x u σ t :=
    boundaryOffDvdFactorZeroProvider_of_split
      (side := side) (d := d) (x := x) (u := u) (σ := σ) (t := t)
      hwnz_offdvd hfactor_offdvd0
  exact
    hopcPrimeContributionTsum_eq_zero_of_boundaryDiffPow_factor0_with_insertProvider_and_offdvdFactorZeroProvider_sigma_gt_one
      (side := side) (d := d) (x := x) (u := u) (σ := σ) (t := t) (C := C)
      (S := S) hσ hC hwnz_diff hfactor_diff0 provider offdvdFactorProvider hEvStationary

/--
RH-O11: `BoundaryInsertLocalLiftProvider` と off-dvd 側 factor0 供給から、
有限寄与和の atTop 極限（0）を直接得る高位 wrapper。
-/
theorem tendsto_hopcPrimeContributionSum_atTop_of_boundaryDiffPow_factor0_with_insertProvider_sigma_gt_one
    (side : DkMath.CFBRC.BoundarySide)
    (S : Finset {q // Nat.Prime q})
    {d x u : ℕ} {σ t C : ℝ}
    (hσ : 1 < σ) (hC : 0 ≤ C)
    (hwnz_diff :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hfactor_diff0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZetaFactorPhaseVelLocal p.1 σ t = 0)
    (provider : BoundaryInsertLocalLiftProvider side S d x u σ t)
    (hwnz_offdvd :
      ∀ p : {q // Nat.Prime q},
        ¬ p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hfactor_offdvd0 :
      ∀ p : {q // Nat.Prime q},
        ¬ p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZetaFactorPhaseVelLocal p.1 σ t = 0)
    (hEvStationary :
      ∀ᶠ S : Finset {q // Nat.Prime q} in Filter.atTop,
        DkMath.RH.stationaryAt
          (fun v : ℝ => eulerZetaFinite_onVertical S σ v) t) :
    Filter.Tendsto
      (fun S : Finset {p // Nat.Prime p} =>
        hopcPrimeContributionSum (S := S) σ t)
      Filter.atTop (𝓝 (0 : ℝ)) := by
  let offdvdFactorProvider : BoundaryOffDvdFactorZeroProvider side d x u σ t :=
    boundaryOffDvdFactorZeroProvider_of_split
      (side := side) (d := d) (x := x) (u := u) (σ := σ) (t := t)
      hwnz_offdvd hfactor_offdvd0
  exact
    tendsto_hopcPrimeContributionSum_atTop_of_boundaryDiffPow_factor0_with_insertProvider_and_offdvdFactorZeroProvider_sigma_gt_one
      (side := side) (d := d) (x := x) (u := u) (σ := σ) (t := t) (C := C)
      (S := S) hσ hC hwnz_diff hfactor_diff0 provider offdvdFactorProvider hEvStationary

/--
RH-O9: off-dvd local-zero provider を使って
`|hopcPrimeContributionFn| ≤ C / p^σ` を供給する wrapper。
-/
theorem hopcPrimeContributionFn_abs_le_prime_rpow_of_boundaryDiffPow_factor0_with_offdvd_provider
    (side : DkMath.CFBRC.BoundarySide)
    {d x u : ℕ} {σ t C : ℝ}
    (hC : 0 ≤ C)
    (hwnz_diff :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hfactor_diff0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZetaFactorPhaseVelLocal p.1 σ t = 0)
    (offdvdProvider : BoundaryOffDvdLocalZeroProvider side d x u σ t) :
    ∀ p : {q // Nat.Prime q},
      |hopcPrimeContributionFn σ t p| ≤ C / (↑p : ℝ) ^ σ :=
  hopcPrimeContributionFn_abs_le_prime_rpow_of_boundaryDiffPow_factor0_with_offdvd_local0
    (side := side) (d := d) (x := x) (u := u) (σ := σ) (t := t) (C := C)
    hC hwnz_diff hfactor_diff0 offdvdProvider.hlocal_offdvd

/--
RH-O9: off-dvd local-zero provider 版の `hopcPrimeContributionTsum = 0`。
-/
theorem hopcPrimeContributionTsum_eq_zero_of_boundaryDiffPow_factor0_with_offdvd_provider_sigma_gt_one
    (side : DkMath.CFBRC.BoundarySide)
    {d x u : ℕ} {σ t C : ℝ}
    (hσ : 1 < σ) (hC : 0 ≤ C)
    (hwnz_diff :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hfactor_diff0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZetaFactorPhaseVelLocal p.1 σ t = 0)
    (offdvdProvider : BoundaryOffDvdLocalZeroProvider side d x u σ t)
    (hEvStationary :
      ∀ᶠ S : Finset {q // Nat.Prime q} in Filter.atTop,
        DkMath.RH.stationaryAt
          (fun v : ℝ => eulerZetaFinite_onVertical S σ v) t) :
    hopcPrimeContributionTsum σ t = 0 :=
  hopcPrimeContributionTsum_eq_zero_of_boundaryDiffPow_factor0_with_offdvd_local0_sigma_gt_one
    (side := side) (d := d) (x := x) (u := u) (σ := σ) (t := t) (C := C)
    hσ hC hwnz_diff hfactor_diff0 offdvdProvider.hlocal_offdvd hEvStationary

/--
RH-O9: off-dvd local-zero provider 版の atTop 極限（0）。
-/
theorem tendsto_hopcPrimeContributionSum_atTop_of_boundaryDiffPow_factor0_with_offdvd_provider_sigma_gt_one
    (side : DkMath.CFBRC.BoundarySide)
    {d x u : ℕ} {σ t C : ℝ}
    (hσ : 1 < σ) (hC : 0 ≤ C)
    (hwnz_diff :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hfactor_diff0 :
      ∀ p : {q // Nat.Prime q},
        p.1 ∣ DkMath.CFBRC.boundaryDiffPow side d x u →
          eulerZetaFactorPhaseVelLocal p.1 σ t = 0)
    (offdvdProvider : BoundaryOffDvdLocalZeroProvider side d x u σ t)
    (hEvStationary :
      ∀ᶠ S : Finset {q // Nat.Prime q} in Filter.atTop,
        DkMath.RH.stationaryAt
          (fun v : ℝ => eulerZetaFinite_onVertical S σ v) t) :
    Filter.Tendsto
      (fun S : Finset {p // Nat.Prime p} =>
        hopcPrimeContributionSum (S := S) σ t)
      Filter.atTop (𝓝 (0 : ℝ)) :=
  tendsto_hopcPrimeContributionSum_atTop_of_boundaryDiffPow_factor0_with_offdvd_local0_sigma_gt_one
    (side := side) (d := d) (x := x) (u := u) (σ := σ) (t := t) (C := C)
    hσ hC hwnz_diff hfactor_diff0 offdvdProvider.hlocal_offdvd hEvStationary

end DkMath.RH.EulerZeta
