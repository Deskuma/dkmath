/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.PrimeProvider.TriominoCosmicPrimeGe5Core

set_option linter.style.longLine false
set_option linter.style.emptyLine false

namespace DkMath.FLT

/--
`Basic.lean` から呼ぶ Branch A（`p ∣ z - y`）専用の gap-power 供給仕様。

`GapInvariant` の本線 API とは切り離し、`Basic` が依存循環なしで参照できる
最小入口として lower layer に固定する。
-/
abbrev PrimeGe5BranchAGapPowFactorizationTarget : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    ∀ q : ℕ, p ∣ (z - y).factorization q

/--
Branch A の因数分解指数仕様が供給されれば、`gap = z - y` は pure `p` 乗に落ちる。
-/
theorem primeGe5BranchAGapPow_of_factorization
    (hFac : PrimeGe5BranchAGapPowFactorizationTarget) :
    ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
      p ∣ (z - y) →
      ∃ t : ℕ, (z - y) = t ^ p := by
  intro p x y z hpack hp_dvd_gap
  have hp0 : 0 < p := hpack.hp.pos
  have hgap_ne0 : (z - y) ≠ 0 := by
    exact Nat.ne_of_gt (Nat.sub_pos_of_lt hpack.hyz_lt)
  exact exists_eq_pow_of_factorization_dvd
    (u := z - y) (p := p)
    hgap_ne0 hp0
    (hFac hpack hp_dvd_gap)

/--
Branch A 本線 target（shape-factorization 版）。

`u := z - y` について
- `q ≠ p` 側の指数は `p` の倍数
- `q = p` 側の指数は `(p - 1) + p * m` 形
を lower layer で要求する。
-/
abbrev PrimeGe5BranchAShapeFactorizationTarget : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    (∀ q : ℕ, q ≠ p → p ∣ (z - y).factorization q) ∧
    ∃ m : ℕ, (z - y).factorization p = (p - 1) + p * m

/-- Branch A の値域 shape 出口。 -/
abbrev PrimeGe5BranchAShapeValueTarget : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    ∃ t : ℕ, (z - y) = p ^ (p - 1) * t ^ p

/--
Branch A の shape 値を refute する lower-layer 契約。

ここを clean な descent/shrink kernel で埋めれば、
`Basic.lean` 側は `primeGe5BranchARefuter_default` をそのまま呼び続けてよい。
-/
abbrev PrimeGe5BranchAShapeValueToRefuterTarget : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    (∃ t : ℕ, (z - y) = p ^ (p - 1) * t ^ p) →
    False

/--
Branch A の shape-factorization から値域 shape へ送る clean 実装。

`z - y = p^(p-1) * t^p` を直接再構成する。
-/
theorem primeGe5BranchAShapeValue_of_factorization
    (hShape : PrimeGe5BranchAShapeFactorizationTarget) :
    PrimeGe5BranchAShapeValueTarget := by
  intro p x y z hpack hp_dvd_gap
  rcases hShape hpack hp_dvd_gap with ⟨hNe, hpPart⟩
  rcases hpPart with ⟨m, hm⟩
  let u : ℕ := z - y
  let d : ℕ := p ^ (p - 1)
  have hu_pos : 0 < u := by
    simpa [u] using Nat.sub_pos_of_lt hpack.hyz_lt
  have hu0 : u ≠ 0 := Nat.ne_of_gt hu_pos
  have hle : p - 1 ≤ u.factorization p := by
    rw [hm]
    exact Nat.le_add_right (p - 1) (p * m)
  have hdvd_u : d ∣ u := by
    unfold d
    exact (hpack.hp.pow_dvd_iff_le_factorization hu0).2 hle
  have hd_pos : 0 < d := by
    unfold d
    exact Nat.pow_pos hpack.hp.pos
  let w : ℕ := u / d
  have hw_pos : 0 < w := Nat.div_pos (Nat.le_of_dvd hu_pos hdvd_u) hd_pos
  have hw0 : w ≠ 0 := Nat.ne_of_gt hw_pos
  have hfac_div : w.factorization = u.factorization - d.factorization := by
    simpa [w] using Nat.factorization_div hdvd_u
  have hall_w : ∀ q : ℕ, p ∣ w.factorization q := by
    intro q
    by_cases hq_eq : q = p
    · have hd_fac_p : d.factorization p = p - 1 := by
        unfold d
        simp [hpack.hp.factorization]
      have hm_u : u.factorization p = (p - 1) + p * m := by
        simpa [u] using hm
      have hw_fac_p : w.factorization p = p * m := by
        calc
          w.factorization p = u.factorization p - d.factorization p := by
            simpa using congrArg (fun f => f p) hfac_div
          _ = ((p - 1) + p * m) - (p - 1) := by simp [hm_u, hd_fac_p]
          _ = p * m := by omega
      exact ⟨m, by simp [hq_eq, hw_fac_p]⟩
    · by_cases hqP : Nat.Prime q
      · have hd_fac_q : d.factorization q = 0 := by
          unfold d
          rw [Nat.Prime.factorization_pow hpack.hp]
          simp [hq_eq]
        have hw_fac_q : w.factorization q = u.factorization q := by
          calc
            w.factorization q = u.factorization q - d.factorization q := by
              simpa using congrArg (fun f => f q) hfac_div
            _ = u.factorization q := by simp [hd_fac_q]
        rcases hNe q hq_eq with ⟨k, hk⟩
        exact ⟨k, by simpa [hw_fac_q, hk]⟩
      · have hw_fac0 : w.factorization q = 0 := Nat.factorization_eq_zero_of_not_prime w hqP
        exact ⟨0, by simp [hw_fac0]⟩
  rcases exists_eq_pow_of_factorization_dvd
      (u := w) (p := p) hw0 hpack.hp.pos hall_w with ⟨t, ht⟩
  have hu_mul : u = d * w := by
    have hw_mul : w * d = u := by
      simpa [w] using Nat.div_mul_cancel hdvd_u
    simpa [Nat.mul_comm] using hw_mul.symm
  refine ⟨t, ?_⟩
  calc
    z - y = u := by rfl
    _ = d * w := hu_mul
    _ = p ^ (p - 1) * t ^ p := by simp [d, ht]

/--
shape-factorization と shape-value refuter 契約が揃えば、
Branch A 専用 refuter が得られる。
-/
theorem primeGe5BranchARefuter_of_shape_pipeline
    (hShape : PrimeGe5BranchAShapeFactorizationTarget)
    (hRefuteValue : PrimeGe5BranchAShapeValueToRefuterTarget) :
    ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
      p ∣ (z - y) →
      False := by
  intro p x y z hpack hp_dvd_gap
  exact hRefuteValue hpack hp_dvd_gap
    (primeGe5BranchAShapeValue_of_factorization hShape hpack hp_dvd_gap)

/--
`FLT_of_coprime` の residual branch から呼ぶ Branch A 専用 refuter 入口。

将来は `PrimeGe5BranchAGapPowFactorizationTarget` と shape/descent kernel を
ここで合成する。現段階では残差 `sorry` を `Basic.lean` から切り離して
この lower layer に局所化する。
-/
theorem primeGe5BranchARefuter_default :
    ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
      p ∣ (z - y) →
      False := by
  intro p x y z hpack hp_dvd_gap
  /-
  TODO:
  1. `q ≠ p` / `q = p` の Branch A factorization spine を接続する。
  2. shape もしくは pure gap-pow を既存 descent/refuter kernel へ送る。
  3. `Basic.lean` 側はこの入口だけを呼び続ける。
  -/
  sorry

end DkMath.FLT
