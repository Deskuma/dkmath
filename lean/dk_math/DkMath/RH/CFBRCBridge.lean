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

end DkMath.RH.EulerZeta
