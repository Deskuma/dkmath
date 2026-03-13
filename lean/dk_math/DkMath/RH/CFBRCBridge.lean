 /-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CFBRC.Bridge
import DkMath.RH.EulerZetaLemmas

/-!
# RH-CFBRC Bridge

CFBRC 側で得た primitive-prime existence を、RH 側の
`hopcPrimeContributionSum` 判定へ接続する最小 bridge。
-/

namespace DkMath.RH.EulerZeta

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

end DkMath.RH.EulerZeta
