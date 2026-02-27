/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.PrimeProvider.TriominoCosmic
import DkMath.FLT.Core
import DkMath.Basic.Nat

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# Triomino/Cosmic Prime-Ge5 Roadmap

`PrimeGe5FLTProvider` の本体実装を育てるための作業用モジュール。

方針:
- ここでは `sorry` を導入しない。
- 未完成な定理本体はまだ置かず、ターゲットの型と補題分解順だけを固定する。
- 実装が進んだら、このファイルで不足補題を順次定理化し、
  最後に `FLT_prime_ge5` を実装する。
-/

namespace DkMath.FLT

open scoped BigOperators

/--
残る本質ターゲット:
`p ≥ 5` の素数指数に対する FLT 供給。

現時点では `PrimeGe5FLTProvider` の別名として固定し、
この型を埋めることだけに集中できるようにする。
-/
abbrev FLTPrimeGe5Target : Prop :=
  PrimeGe5FLTProvider

/--
`FLTPrimeGe5Target` が埋まれば、既存の global provider 導線へ接続できる。
`PrimeGe5FLTProvider` 名だけでなく、「prime-ge5 本体ターゲット」という意味でも読める別名。
-/
theorem triominoCosmic_globalProvider_of_FLTPrimeGe5
    (hprimeGe5 : FLTPrimeGe5Target) :
    GlobalPrimeExponentFLTProvider := by
  exact triominoCosmic_globalProvider_of_primeGe5 hprimeGe5

/--
`FLTPrimeGe5Target` が埋まれば、`TriominoPrimeProvider` にも直結できる。
-/
theorem triominoPrimeProvider_of_FLTPrimeGe5
    (hprimeGe5 : FLTPrimeGe5Target) :
    TriominoPrimeProvider := by
  exact triominoPrimeProvider_of_primeGe5 hprimeGe5

/-- 「素因数分解の指数がすべて `p` の倍数」なら、`p` 乗根を素朴に構成できる。 -/
private lemma exists_eq_pow_of_factorization_dvd
    {u p : ℕ} (hu0 : u ≠ 0) (_hp0 : 0 < p)
    (hdiv : ∀ q : ℕ, p ∣ u.factorization q) :
    ∃ t : ℕ, u = t ^ p := by
  classical
  let t : ℕ := u.factorization.support.prod (fun q => q ^ (u.factorization q / p))
  refine ⟨t, ?_⟩
  have hu_prod :
      u.factorization.support.prod (fun q => q ^ u.factorization q) = u :=
    Nat.factorization_prod_pow_eq_self hu0
  have ht : t ^ p = u := by
    calc
      t ^ p
          = (u.factorization.support.prod (fun q => q ^ (u.factorization q / p))) ^ p := rfl
      _ = u.factorization.support.prod (fun q => (q ^ (u.factorization q / p)) ^ p) := by
          rw [Finset.prod_pow]
      _ = u.factorization.support.prod (fun q => q ^ (u.factorization q)) := by
          refine Finset.prod_congr rfl (fun q _ => ?_)
          have hq : p ∣ u.factorization q := hdiv q
          rw [← pow_mul, Nat.div_mul_cancel hq]
      _ = u := hu_prod
  exact ht.symm

/--
TODO-1（純算術・核）:
`u` が `p` 乗でないなら、ある素因子 `q` で「指数が `p` の倍数でない」が起きる。
-/
lemma exists_primeFactor_factorization_not_dvd_of_not_isPow
    {u p : ℕ} (hu0 : u ≠ 0) (hp0 : 0 < p)
    (hnot : ¬ ∃ t : ℕ, u = t ^ p) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ u ∧ ¬ p ∣ u.factorization q := by
  classical
  have hnotAll : ¬ (∀ q : ℕ, p ∣ u.factorization q) := by
    intro hall
    rcases exists_eq_pow_of_factorization_dvd (u := u) (p := p) hu0 hp0 hall with ⟨t, ht⟩
    exact hnot ⟨t, ht⟩
  rcases not_forall.mp hnotAll with ⟨q, hq⟩
  have hq_ne0 : u.factorization q ≠ 0 := by
    intro h0
    have : p ∣ u.factorization q := by
      simp [h0]
    exact hq this
  have hq_mem : q ∈ u.factorization.support := by
    rw [Finsupp.mem_support_iff]
    exact hq_ne0
  have hsup := (DkMath.Basic.Nat.mem_support_factorization_iff (n := u) (p := q)).1 hq_mem
  rcases hsup with ⟨_, hqPrime, hqDvd⟩
  exact ⟨q, hqPrime, hqDvd, hq⟩

/-- `Nat.Prime q` のもとで `padicValNat q u` は `u.factorization q` と一致する。 -/
lemma padicValNat_eq_factorization {q u : ℕ} (hq : Nat.Prime q) (hu0 : u ≠ 0) :
    padicValNat q u = u.factorization q := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  apply Nat.le_antisymm
  · have hdiv : q ^ padicValNat q u ∣ u := by
      simpa using (pow_padicValNat_dvd (p := q) (n := u))
    exact (hq.pow_dvd_iff_le_factorization hu0).1 hdiv
  · have hdiv : q ^ u.factorization q ∣ u :=
      (hq.pow_dvd_iff_le_factorization hu0).2 le_rfl
    exact (@padicValNat_dvd_iff_le q (Fact.mk hq) u (u.factorization q) hu0).1 hdiv

/-- factorization 版の `¬ p ∣ ...` を `padicValNat` 版へ運ぶ薄い橋。 -/
lemma not_dvd_padicValNat_of_not_dvd_factorization
    {p q u : ℕ} (hq : Nat.Prime q) (hu0 : u ≠ 0)
    (h : ¬ p ∣ u.factorization q) :
    ¬ p ∣ padicValNat q u := by
  have hEq : padicValNat q u = u.factorization q :=
    padicValNat_eq_factorization (q := q) (u := u) hq hu0
  simpa [hEq] using h

/-- TODO-1 の最終形：`padicValNat` 版。 -/
lemma exists_primeFactor_val_not_dvd_of_not_isPow
    {u p : ℕ} (hu0 : u ≠ 0) (hp0 : 0 < p)
    (hnot : ¬ ∃ t : ℕ, u = t ^ p) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ u ∧ ¬ p ∣ padicValNat q u := by
  rcases exists_primeFactor_factorization_not_dvd_of_not_isPow
      (u := u) (p := p) hu0 hp0 hnot with
    ⟨q, hqPrime, hqDvd, hNot⟩
  refine ⟨q, hqPrime, hqDvd, ?_⟩
  exact not_dvd_padicValNat_of_not_dvd_factorization
    (p := p) (q := q) (u := u) hqPrime hu0 hNot

/-!
## 実装ロードマップ（順序固定）

以下の順に補題を埋めると、`FLT_prime_ge5` の本体へ最短で到達できる。

1. TODO-1（純算術）:
   `u ≠ 0 ∧ ¬ ∃ t, u = t^p` から
   `∃ q, Nat.Prime q ∧ q ∣ u ∧ ¬ p ∣ padicValNat q u`
   を取り出す補題。

2. TODO-3（正規化）:
   反例を primitive/coprime 形へ正規化し、
   `u := z - y` に対して `Nat.Coprime u y` を得る補題。

3. TODO-2（Triomino/Cosmic 本丸）:
   反例があるなら `u = z - y` は `p` 乗になれないことを示す補題。

4. 枝葉:
   `q ≠ p`、`GN p u y ≠ 0`、`¬ q ∣ GN p u y` を接続する短い補題群。

最終形の目標定理シグネチャ（未実装）:

```lean
theorem FLT_prime_ge5 (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    FermatLastTheoremFor p
```

このターゲットが埋まれば、
`triominoCosmic_globalProvider_of_primeGe5` を通じて
`GlobalPrimeExponentFLTProvider` が得られ、
既存の provider 系 API へそのまま接続できる。
-/

end DkMath.FLT
