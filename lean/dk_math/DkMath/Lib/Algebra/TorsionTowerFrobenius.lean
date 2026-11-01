/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: ../NumberTheory/RegularKummer/LICENSE
Upstream notices: ../NumberTheory/RegularKummer/ANTHROPIC-NOTICE
Adapted from the final group-theoretic argument in
anthropics/fermats-last-theorem/P2M/Sol/S_FreyPackage_frey_no_cofixed_large.lean.
Upstream blob: 16f282e721fd66e1593db1149266834bfd99af1a
Modified: separate Frobenius absorption, prime-to-p scalar cancellation,
and torsion cardinality; keep all tower and arithmetic hypotheses explicit.
-/

import DkMath.Lib.Algebra.TorsionMultiplication
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Abel
import Lean.Elab.Tactic.Omega

#print "file: DkMath.Lib.Algebra.TorsionTowerFrobenius"

/-!
# Frobenius と捩れ塔の最後の矛盾

本章は上流の `frey_no_cofixed_large` の最終群論を三段階に分ける。

1. `φ` が `G[n]/K` 上で自明に作用し、Frobenius の Cayley–Hamilton 関係を
   満たすなら、還元点数に対応する整数 `N` は `G[n]/K` を消す。
2. `N=p^t*u`, `p ∤ u` と分解する。`p^N` 段までの scalar absorption と
   点群の可除性から、任意の `p` 捩れ点を塔の底 `H` へ落とせる。
3. `#G[p]=p²`, `#H=p` なら単射な包含が `p²≤p` を与え、矛盾する。

局所慣性から商上の Galois 作用を自明化する定理、実際の Frobenius 関係、
適切な塔 `K` の存在は本章の仮定である。群論を完了しても、それらの算術を
構成するまでは一般 hno は完成しない。
-/

namespace DkMath.Lib.Algebra.TorsionTowerFrobenius

variable {G : Type*} [AddCommGroup G]

/-- 商上の固定性と Cayley–Hamilton 関係から、点数 scalar の吸収を得る。
`φ` が実際の Frobenius であることは利用側が供給する。 -/
theorem nsmul_mem_of_frobenius_relation
    (K : AddSubgroup G) (φ : G →+ G) (n N : ℕ) (ell : ℤ)
    (hfixed : ∀ x : G, n • x = 0 → φ x - x ∈ K)
    (hCH : ∀ x : G, n • x = 0 →
      φ (φ x) + ell • x = (ell + 1 - (N : ℤ)) • φ x)
    {y : G} (hy : n • y = 0) : N • y ∈ K := by
  have hd₁ := hfixed y hy
  have hφy : n • φ y = 0 := by rw [← map_nsmul, hy, map_zero]
  have hd₂ := hfixed (φ y) hφy
  have hch := hCH y hy
  rw [sub_smul, add_smul, one_smul] at hch
  have hφφ : φ (φ y) = ell • φ y + φ y - (N : ℤ) • φ y - ell • y :=
    eq_sub_of_add_eq hch
  have hNφ : (N : ℤ) • φ y = ell • (φ y - y) - (φ (φ y) - φ y) := by
    rw [zsmul_sub, hφφ]
    abel
  have hNφmem : (N : ℤ) • φ y ∈ K := by
    rw [hNφ]
    exact K.sub_mem (K.zsmul_mem hd₁ _) hd₂
  have heq : (N : ℤ) • y = (N : ℤ) • φ y - (N : ℤ) • (φ y - y) := by
    rw [zsmul_sub]
    abel
  rw [← natCast_zsmul y, heq]
  exact K.sub_mem hNφmem (K.zsmul_mem hd₁ _)

/-- `p` 捩れ上では `p` と素な scalar を部分群所属から約分できる。
Bézout の係数は整数で取り、任意の可換加法群に適用する。 -/
theorem mem_of_coprime_nsmul (H : AddSubgroup G) {p u : ℕ}
    (hcop : u.Coprime p) {e : G} (he : p • e = 0) (hu : u • e ∈ H) : e ∈ H := by
  have hbez := Nat.gcd_eq_gcd_ab u p
  rw [hcop.gcd_eq_one] at hbez
  have heq : e = Nat.gcdA u p • ((u : ℤ) • e) + Nat.gcdB u p • ((p : ℤ) • e) := by
    calc
      e = (1 : ℤ) • e := (one_smul ℤ e).symm
      _ = ((u : ℤ) * Nat.gcdA u p + (p : ℤ) * Nat.gcdB u p) • e := by rw [← hbez]; norm_num
      _ = _ := by rw [add_zsmul, mul_comm (u : ℤ), mul_comm (p : ℤ), mul_zsmul, mul_zsmul]
  rw [heq]
  apply H.add_mem
  · exact H.zsmul_mem (by simpa only [natCast_zsmul] using hu) _
  · rw [natCast_zsmul, he, zsmul_zero]
    exact H.zero_mem

/-- scalar absorption が十分高い段で成立すれば、全 `p` 捩れが塔の底に入る。
塔を構成したという主張はせず、必要なのは `hdown` と `habsorb` の二条件だと明示する。 -/
theorem prime_torsion_mem_of_scalar_absorbs
    {p : ℕ} (hp : p.Prime) (H K : AddSubgroup G) {N : ℕ} (hN : 0 < N)
    (hlift : ∀ t : ℕ, Function.Surjective (nsmulAddMonoidHom (p ^ t) : G →+ G))
    (hdown : ∀ x ∈ K, p • x = 0 → x ∈ H)
    (habsorb : ∀ y : G, p ^ N • y = 0 → N • y ∈ K)
    {e : G} (he : p • e = 0) : e ∈ H := by
  obtain ⟨t, u, hpu, hNu⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' p hp.ne_one
  have ht : t < N := by
    have hd : p ^ t ∣ N := ⟨u, hNu⟩
    have hle := Nat.le_of_dvd hN hd
    have hlt : p ^ t < p ^ N := lt_of_le_of_lt hle (Nat.lt_pow_self hp.one_lt)
    exact (Nat.pow_lt_pow_iff_right hp.one_lt).mp hlt
  obtain ⟨y, hy⟩ := hlift t e
  have hy' : p ^ t • y = e := hy
  have hyT : p ^ (t + 1) • y = 0 := by rw [pow_succ, mul_nsmul, hy', he]
  have hyN : p ^ N • y = 0 := by
    obtain ⟨d, hd⟩ : ∃ d : ℕ, N = (t + 1) + d := ⟨N - (t + 1), by omega⟩
    rw [hd, pow_add, mul_nsmul, hyT, nsmul_zero]
  have hNy : N • y ∈ K := habsorb y hyN
  have hNy_eq : N • y = u • e := by rw [hNu, mul_nsmul, hy']
  have hueK : u • e ∈ K := hNy_eq ▸ hNy
  have hueH : u • e ∈ H := hdown _ hueK (by rw [← mul_nsmul, mul_comm, mul_nsmul, he, nsmul_zero])
  exact mem_of_coprime_nsmul H ((hp.coprime_iff_not_dvd.mpr hpu).symm) he hueH

/-- 全 `p` 捩れの濃度が `p²`、塔の底の濃度が `p` なら scalar absorption は不可能。
無限型の `Nat.card=0` を有限濃度として扱わず、非零濃度から有限性を確保する。 -/
theorem false_of_rank_two_scalar_absorbs
    {p : ℕ} (hp : p.Prime) (H K : AddSubgroup G) {N : ℕ} (hN : 0 < N)
    (hcard : Nat.card (TorsionMultiplication.Kernel G p) = p ^ 2)
    (hHcard : Nat.card H = p)
    (hlift : ∀ t : ℕ, Function.Surjective (nsmulAddMonoidHom (p ^ t) : G →+ G))
    (hdown : ∀ x ∈ K, p • x = 0 → x ∈ H)
    (habsorb : ∀ y : G, p ^ N • y = 0 → N • y ∈ K) : False := by
  let : Finite H := Nat.finite_of_card_ne_zero (hHcard ▸ hp.ne_zero)
  let : Finite (TorsionMultiplication.Kernel G p) :=
    Nat.finite_of_card_ne_zero (hcard ▸ pow_ne_zero _ hp.ne_zero)
  let f : TorsionMultiplication.Kernel G p → H := fun x =>
    ⟨x.val, prime_torsion_mem_of_scalar_absorbs hp H K hN hlift hdown habsorb x.property⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : H => z.val) hxy
  have hle : p ^ 2 ≤ p := by
    calc
      p ^ 2 = Nat.card (TorsionMultiplication.Kernel G p) := hcard.symm
      _ ≤ Nat.card H := Nat.card_le_card_of_injective f hf
      _ = p := hHcard
  rw [pow_two] at hle
  have hple : p ≤ 1 := Nat.le_of_mul_le_mul_left (by simpa using hle) hp.pos
  have := hp.two_le
  omega

end DkMath.Lib.Algebra.TorsionTowerFrobenius
