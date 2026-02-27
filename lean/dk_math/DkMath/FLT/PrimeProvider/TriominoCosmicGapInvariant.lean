/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.PrimeProvider.TriominoCosmicPrimeGe5

set_option linter.style.longLine false
set_option linter.style.emptyLine false

namespace DkMath.FLT

open DkMath.CosmicFormulaBinom

/-!
# Triomino/Cosmic Gap Invariant

`TriominoCosmicGapInvariant` の本体証明を育てる隔離モジュール。
`TriominoCosmicPrimeGe5` は staging として維持し、このファイル側にのみ
研究中の本丸を閉じ込める。
-/

/-- `x^p = u * GN p u y` と `u = t^p` から、`GN p u y` も `p` 乗に落ちる。 -/
lemma exists_eq_pow_of_gap_eq_pow
    {p x y u t : ℕ}
    (hp : Nat.Prime p)
    (hu_pos : 0 < u)
    (hxpow : x ^ p = u * GN p u y)
    (htu : u = t ^ p) :
    ∃ s : ℕ, GN p u y = s ^ p := by
  have ht_pow_dvd : t ^ p ∣ x ^ p := by
    refine ⟨GN p u y, ?_⟩
    calc
      x ^ p = u * GN p u y := hxpow
      _ = t ^ p * GN p u y := by simp [htu]
  have ht_ne_zero : t ≠ 0 := by
    intro ht0
    have hu_zero : u = 0 := by
      calc
        u = t ^ p := htu
        _ = 0 := by simp [ht0, hp.ne_zero]
    exact (Nat.ne_of_gt hu_pos) hu_zero
  have ht_pos : 0 < t := Nat.pos_of_ne_zero ht_ne_zero
  have ht_dvd_x : t ∣ x :=
    (Nat.pow_dvd_pow_iff hp.ne_zero).1 ht_pow_dvd
  rcases ht_dvd_x with ⟨s, hsx⟩
  have hxpow' : (t * s) ^ p = u * GN p u y := by
    simpa [hsx] using hxpow
  have hmul : t ^ p * s ^ p = t ^ p * GN p u y := by
    calc
      t ^ p * s ^ p = (t * s) ^ p := by rw [Nat.mul_pow]
      _ = u * GN p u y := hxpow'
      _ = t ^ p * GN p u y := by simp [htu]
  have hs_eq : s ^ p = GN p u y :=
    Nat.eq_of_mul_eq_mul_left (Nat.pow_pos ht_pos) hmul
  exact ⟨s, hs_eq.symm⟩

/--
Triomino/Cosmic 側で最終的に供給すべき Body 不変量。
`gap` そのものではなく `GN` 側の「p 乗になれなさ」に責務を移す。
-/
abbrev TriominoCosmicBodyInvariant : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    ¬ ∃ s : ℕ, GN p (z - y) y = s ^ p

/--
`GN` が `p` 乗でないことを示すための最小入力仕様:
ある素数 `q` が `GN` を割るが、`q^2` は割らない。
-/
abbrev NoPowOnGN_fromCounterexample : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ GN p (z - y) y ∧ ¬ q ^ 2 ∣ GN p (z - y) y

/-- Branch A 用の入力仕様: `p ∣ (z - y)` のとき、`GN` に平方止まりの素因子が入る。 -/
abbrev NoSqPrimeOnGN_when_p_dvd_u : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ GN p (z - y) y ∧ ¬ q ^ 2 ∣ GN p (z - y) y

/-- Branch B 用の入力仕様: `¬ p ∣ (z - y)` のとき、`GN` に平方止まりの素因子が入る。 -/
abbrev NoSqPrimeOnGN_when_p_not_dvd_u : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    ¬ p ∣ (z - y) →
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ GN p (z - y) y ∧ ¬ q ^ 2 ∣ GN p (z - y) y

/-- Branch A / B の 2 分岐仕様が揃えば、`NoPowOnGN` は合成できる。 -/
theorem noPowOnGN_of_branches
    (hA : NoSqPrimeOnGN_when_p_dvd_u)
    (hB : NoSqPrimeOnGN_when_p_not_dvd_u) :
    NoPowOnGN_fromCounterexample := by
  intro p x y z hpack
  by_cases hp_dvd_u : p ∣ (z - y)
  · exact hA hpack hp_dvd_u
  · exact hB hpack hp_dvd_u

/-- `p ≥ 5` のもと、`q ∣ N` かつ `q^2 ∤ N` があれば、`N` は `p` 乗になれない。 -/
lemma not_isPow_of_exists_prime_dvd_not_dvd_sq
    {p N : ℕ} (hp5 : 5 ≤ p)
    (h : ∃ q : ℕ, Nat.Prime q ∧ q ∣ N ∧ ¬ q ^ 2 ∣ N) :
    ¬ ∃ s : ℕ, N = s ^ p := by
  rintro ⟨s, rfl⟩
  rcases h with ⟨q, hqP, hqDvd, hq2Not⟩
  have hq_dvd_s : q ∣ s :=
    hqP.dvd_of_dvd_pow (by simpa using hqDvd)
  have hqpow : q ^ p ∣ s ^ p :=
    pow_dvd_pow_of_dvd hq_dvd_s p
  have hp2 : 2 ≤ p := le_trans (by decide : 2 ≤ 5) hp5
  have hq2_dvd_qp : q ^ 2 ∣ q ^ p :=
    pow_dvd_pow q hp2
  have hq2 : q ^ 2 ∣ s ^ p :=
    dvd_trans hq2_dvd_qp hqpow
  exact hq2Not hq2

/-- `NoPowOnGN` 仕様があれば、Body 不変量はただちに得られる。 -/
theorem bodyInvariant_of_NoPowOnGN
    (hNoPow : NoPowOnGN_fromCounterexample) :
    TriominoCosmicBodyInvariant := by
  intro p x y z hpack
  exact not_isPow_of_exists_prime_dvd_not_dvd_sq hpack.hp5 (hNoPow hpack)

/--
Triomino/Cosmic 本丸（NoPowOnGN 版）:
primitive 反例パックから、`GN p (z - y) y` に「平方止まりの素因子」が入る。

現時点では本体未実装。`TODO-2` の未解決点をこのファイル 1 箇所へ隔離する。
-/
theorem triominoCosmicNoPowOnGN : NoPowOnGN_fromCounterexample := by
  -- TODO:
  -- 1. `NoSqPrimeOnGN_when_p_dvd_u` を自前（binom 展開）で閉じる
  -- 2. `NoSqPrimeOnGN_when_p_not_dvd_u` を Zsigmondy / NonLiftable 系から供給
  -- 3. `noPowOnGN_of_branches` で合成
  sorry

/-- Triomino/Cosmic 本丸（Body 版）は、`NoPowOnGN` 仕様から得る。 -/
theorem triominoCosmicBodyInvariant : TriominoCosmicBodyInvariant := by
  exact bodyInvariant_of_NoPowOnGN triominoCosmicNoPowOnGN

/--
Body 不変量があれば、gap 不変量は自動で得られる。
`u = t^p` なら `GN` も `p` 乗へ落ちるため、Body 側で矛盾が出る。
-/
theorem gapInvariant_of_bodyInvariant
    (hBody : TriominoCosmicBodyInvariant) :
    TriominoCosmicGapInvariant := by
  intro p x y z hpack
  let u : ℕ := hpack.gap
  have hu_pos : 0 < u := by
    simpa [u] using hpack.gap_pos
  have hxpow := by
    simpa [u, PrimeGe5CounterexamplePack.gap] using
      (pow_eq_sub_mul_GN_of_add_pow_eq p x y z hpack.hyz hpack.hEq)
  intro hgap
  rcases hgap with ⟨t, htu⟩
  rcases exists_eq_pow_of_gap_eq_pow hpack.hp hu_pos hxpow htu with ⟨s, hs⟩
  exact hBody hpack ⟨s, by simpa using hs⟩

/--
Triomino/Cosmic 本丸:
primitive 反例パックがあるなら gap は `p` 乗になれない。
-/
theorem triominoCosmicGapInvariant : TriominoCosmicGapInvariant := by
  exact gapInvariant_of_bodyInvariant triominoCosmicBodyInvariant

end DkMath.FLT
