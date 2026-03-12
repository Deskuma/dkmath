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
  rcases hlift p hq_dvd hq_not_dvd_x with ⟨hS_ne, hsum0⟩
  exact ⟨p, stationaryAt_insert_of_hopcPrimeContributionSum_eq_zero
    (S := S) (p := p) (hS_ne := hS_ne) (hsum0 := hsum0)⟩

end DkMath.RH.EulerZeta
