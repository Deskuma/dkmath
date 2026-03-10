/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.PrimeProvider.TriominoCosmicPrimeGe5
import DkMath.FLT.CosmicPetalBridge
import DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN

set_option linter.style.longLine false
set_option linter.style.emptyLine false

namespace DkMath.FLT

open DkMath.CosmicFormulaBinom
open scoped BigOperators

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

/-- Branch B 用の第1段仕様: 反例から原始素因子を 1 つ取り出す。 -/
abbrev PrimitivePrime_fromCounterexample : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    ¬ p ∣ (z - y) →
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ (z ^ p - y ^ p) ∧ ¬ q ∣ (z - y)

/-- Branch B 用の第2段仕様: 原始素因子は `GN` に深刺ししない。 -/
abbrev NoSqOnGN_of_primitivePrime : Prop :=
  ∀ {p y u q : ℕ}, Nat.Prime q →
    q ∣ GN p u y →
    ¬ q ∣ u →
    ¬ q ^ 2 ∣ GN p u y

/-- `GN` に対する原始素因子条件。 -/
def PrimitiveOnGN (p u y q : ℕ) : Prop :=
  Nat.Prime q ∧ q ∣ GN p u y ∧ ¬ q ∣ u

/-- `GN` に対する 2 段目持ち上げ禁止。 -/
def NonLiftableGN (p u y q : ℕ) : Prop :=
  PrimitiveOnGN p u y q → ¬ q ^ 2 ∣ GN p u y

/-- `GN` の全原始素因子が持ち上がらない。 -/
def AllNonLiftableOnGN (p u y : ℕ) : Prop :=
  ∀ q : ℕ, NonLiftableGN p u y q

/- `TriominoNoWieferichBridge` から押し戻した最終入力仕様。 -/
abbrev TriominoCosmicNonLiftableGNBridge : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    ¬ p ∣ (z - y) ->
    AllNonLiftableOnGN p (z - y) y

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

/-- Branch A（`p ∣ gap`）は、`q := p` と `GN` の head/tail 分解で閉じる。 -/
theorem noSqPrimeOnGN_when_p_dvd_u_impl :
    NoSqPrimeOnGN_when_p_dvd_u := by
  intro p x y z hpack hp_dvd_u
  let u : ℕ := z - y
  let N : ℕ := GN p u y
  let A : ℕ := p * y ^ (p - 1)
  let B : ℕ := Finset.sum ((Finset.range p).erase 0) (fun k =>
    (Nat.choose p (k + 1) : ℕ) * u ^ k * y ^ (p - 1 - k))
  have hp_pos : 0 < p := hpack.hp.pos
  have hp_not_dvd_y : ¬ p ∣ y := by
    simpa [u, PrimeGe5CounterexamplePack.gap] using
      hpack.prime_not_dvd_right_of_prime_dvd_gap hp_dvd_u
  have hsplitBA : B + A = N := by
    let f : ℕ → ℕ := fun k =>
      (Nat.choose p (k + 1) : ℕ) * (z - y) ^ k * y ^ (p - 1 - k)
    have hsum :
        Finset.sum ((Finset.range p).erase 0) f + f 0 = Finset.sum (Finset.range p) f := by
      simpa using
        (Finset.sum_erase_add (s := Finset.range p) (f := f) (a := 0)
          (by simpa using hp_pos))
    unfold N A B u
    simpa [f, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hsum
  have hsplit : N = A + B := by
    simpa [Nat.add_comm] using hsplitBA.symm
  have hB_sq : p ^ 2 ∣ B := by
    unfold B
    refine Finset.dvd_sum ?_
    intro k hk
    have hk_mem : k ∈ Finset.range p := by
      exact Finset.mem_of_mem_erase hk
    have hk_lt : k < p := Finset.mem_range.mp hk_mem
    have hk_ne_zero : k ≠ 0 := Finset.mem_erase.mp hk |>.1
    by_cases hk_one : k = 1
    · have hchoose : p ∣ Nat.choose p (k + 1) := by
        rw [hk_one]
        apply hpack.hp.dvd_choose_self
        · decide
        · exact lt_of_lt_of_le (by decide : 2 < 5) hpack.hp5
      have hp_dvd_uk : p ∣ u ^ k := by
        simpa [hk_one] using hp_dvd_u
      have hprefix : p ^ 2 ∣ (Nat.choose p (k + 1) : ℕ) * u ^ k := by
        simpa [pow_two] using Nat.mul_dvd_mul hchoose hp_dvd_uk
      have hmul : p ^ 2 ∣ ((Nat.choose p (k + 1) : ℕ) * u ^ k) * y ^ (p - 1 - k) :=
        dvd_mul_of_dvd_left hprefix _
      simpa [Nat.mul_assoc] using hmul
    · have hk_ge_two : 2 ≤ k := by omega
      have hpp_dvd_u2 : p ^ 2 ∣ u ^ 2 := by
        simpa [pow_two] using Nat.mul_dvd_mul hp_dvd_u hp_dvd_u
      have hpp_dvd_uk : p ^ 2 ∣ u ^ k :=
        dvd_trans hpp_dvd_u2 (pow_dvd_pow u hk_ge_two)
      have hprefix : p ^ 2 ∣ (Nat.choose p (k + 1) : ℕ) * u ^ k :=
        dvd_mul_of_dvd_right hpp_dvd_uk _
      have hmul : p ^ 2 ∣ ((Nat.choose p (k + 1) : ℕ) * u ^ k) * y ^ (p - 1 - k) :=
        dvd_mul_of_dvd_left hprefix _
      simpa [Nat.mul_assoc] using hmul
  have hA_not_sq : ¬ p ^ 2 ∣ A := by
    intro hA_sq
    have hp_dvd_ypow : p ∣ y ^ (p - 1) := by
      have hmul : p * p ∣ p * y ^ (p - 1) := by
        simpa [A, pow_two] using hA_sq
      exact Nat.dvd_of_mul_dvd_mul_left hp_pos hmul
    exact hp_not_dvd_y (hpack.hp.dvd_of_dvd_pow hp_dvd_ypow)
  refine ⟨p, hpack.hp, ?_, ?_⟩
  · have hp_dvd_A : p ∣ A := by
      unfold A
      exact dvd_mul_right p (y ^ (p - 1))
    have hp_dvd_B : p ∣ B := by
      have hB_sq' : p * p ∣ B := by
        simpa [pow_two] using hB_sq
      exact dvd_trans (dvd_mul_right p p) hB_sq'
    have hp_dvd_N : p ∣ N := by
      simpa [hsplit] using (Nat.dvd_add hp_dvd_A hp_dvd_B)
    simpa [N, u] using hp_dvd_N
  · intro hN_sq
    have hA_sq : p ^ 2 ∣ A := by
      have hN_sq' : p ^ 2 ∣ N := by
        simpa [N, u] using hN_sq
      have hAB_sq : p ^ 2 ∣ A + B := by
        simpa [hsplit] using hN_sq'
      have hBA_sq : p ^ 2 ∣ B + A := by
        simpa [Nat.add_comm] using hAB_sq
      exact (Nat.dvd_add_right hB_sq).1 hBA_sq
    exact hA_not_sq hA_sq

/-- Branch B は「原始素因子の取得」と「深刺し禁止」の 2 仕様から合成できる。 -/
theorem noSqPrimeOnGN_when_p_not_dvd_u_of_specs
    (hPrim : PrimitivePrime_fromCounterexample)
    (hAll : ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
      ¬ p ∣ (z - y) ->
      AllNonLiftableOnGN p (z - y) y) :
    NoSqPrimeOnGN_when_p_not_dvd_u := by
  intro p x y z hpack hp_not_dvd_u
  rcases hPrim hpack hp_not_dvd_u with ⟨q, hqP, hq_dvd_diff, hq_not_dvd_u⟩
  have hq_dvd_GN_raw : q ∣ GN p (z - y) y := by
    exact dvd_GN_of_dvd_sub_pow
      (d := p) (z := z) (y := y) (q := q)
      hqP hq_dvd_diff hq_not_dvd_u
  have hq_dvd_GN : q ∣ GN p (z - y) y := by
    change q ∣
      (∑ x ∈ Finset.range p,
        Nat.choose p (x + 1) * (z - y) ^ x * y ^ (p - 1 - x)) at hq_dvd_GN_raw
    simpa [GN] using hq_dvd_GN_raw
  have hq2_not : ¬ q ^ 2 ∣ GN p (z - y) y := by
    exact (hAll hpack hp_not_dvd_u q) ⟨hqP, hq_dvd_GN, hq_not_dvd_u⟩
  exact ⟨q, hqP, hq_dvd_GN, hq2_not⟩

/-- Branch B の前半: prime-ge5 反例パックから Zsigmondy 原始素因子を取り出す。 -/
theorem primitivePrime_fromCounterexample_impl :
    PrimitivePrime_fromCounterexample := by
  intro p x y z hpack hp_not_dvd_u
  have hyz_coprime : Nat.Coprime z y := by
    exact (coprime_right_of_add_pow_eq_pow hpack.hp hpack.hxy hpack.hEq).symm
  exact DkMath.NumberTheory.GcdNext.exists_primitive_prime_factor_prime
    (a := z) (b := y) (d := p)
    hpack.hp
    (le_trans (by decide : 3 ≤ 5) hpack.hp5)
    hpack.hyz_lt
    hpack.y_pos
    hyz_coprime
    hp_not_dvd_u

/--
prime-ge5 反例パックから `AllNonLiftableOnGN` を供給する本丸インターフェイス。

現時点では、一般 `p ≥ 5` 用の no-`so#rry` family 供給がコードベース本体に無いため、
未解決点をこの 1 定理に隔離する。
-/
theorem allNonLiftableOnGN_fromCounterexample_impl :
    TriominoWieferichBranchBridge ->
    TriominoCosmicNonLiftableGNBridge := by
  intro hBranch
  exact triominoCosmicNonLiftableGNBridge_of_noWieferich
    (triominoNoWieferichBridge_impl hBranch)

/-- 一般 `GN` の nonlift family が供給されれば、`NoPowOnGN` は no-`so#rry` で閉じる。 -/
theorem triominoCosmicNoPowOnGN_of_nonLiftableGNBridge
    (hBridge : TriominoCosmicNonLiftableGNBridge) :
    NoPowOnGN_fromCounterexample := by
  have hA : NoSqPrimeOnGN_when_p_dvd_u :=
    noSqPrimeOnGN_when_p_dvd_u_impl
  have hB : NoSqPrimeOnGN_when_p_not_dvd_u :=
    noSqPrimeOnGN_when_p_not_dvd_u_of_specs
      primitivePrime_fromCounterexample_impl
      hBridge
  intro p x y z hpack
  exact noPowOnGN_of_branches hA hB hpack

/--
Triomino/Cosmic 本丸（NoPowOnGN 版）:
primitive 反例パックから、`GN p (z - y) y` に「平方止まりの素因子」が入る。

現時点では本体未実装。`TODO-2` の未解決点をこのファイル 1 箇所へ隔離する。
-/
theorem triominoCosmicNoPowOnGN
    (hBranch : TriominoWieferichBranchBridge) :
    NoPowOnGN_fromCounterexample := by
  exact triominoCosmicNoPowOnGN_of_nonLiftableGNBridge
    (allNonLiftableOnGN_fromCounterexample_impl hBranch)

/-- Triomino/Cosmic 本丸（Body 版）は、`NoPowOnGN` 仕様から得る。 -/
theorem triominoCosmicBodyInvariant
    (hBranch : TriominoWieferichBranchBridge) :
    TriominoCosmicBodyInvariant := by
  exact bodyInvariant_of_NoPowOnGN (triominoCosmicNoPowOnGN hBranch)

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
theorem triominoCosmicGapInvariant
    (hBranch : TriominoWieferichBranchBridge) :
    TriominoCosmicGapInvariant := by
  exact gapInvariant_of_bodyInvariant (triominoCosmicBodyInvariant hBranch)

end DkMath.FLT
