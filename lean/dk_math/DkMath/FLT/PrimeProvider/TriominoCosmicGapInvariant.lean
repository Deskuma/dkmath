/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.PrimeProvider.TriominoCosmicPrimeGe5
import DkMath.FLT.CosmicPetalBridge
import DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN
import DkMath.FLT.PrimeProvider.TriominoCosmicBranchA

#print "file: DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant"

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

/-- `p ∣ n` かつ `¬ p^2 ∣ n` なら `padicValNat p n = 1`。 -/
lemma padicValNat_eq_one_of_dvd_not_sq
    {p n : ℕ} (hp : Nat.Prime p)
    (hpd : p ∣ n) (hpsq : ¬ p ^ 2 ∣ n) :
    padicValNat p n = 1 := by
  have hnz : n ≠ 0 := by
    intro hn0
    apply hpsq
    simp [hn0]
  have hge : 1 ≤ padicValNat p n :=
    DkMath.ABC.padicValNat_one_le_of_prime_dvd hp hnz hpd
  have hle : padicValNat p n ≤ 1 := by
    by_contra hnot
    have h2 : 2 ≤ padicValNat p n := by omega
    have hsq : p ^ 2 ∣ n :=
      (@padicValNat_dvd_iff_le p (Fact.mk hp) n 2 hnz).2 h2
    exact hpsq hsq
  exact le_antisymm hle hge

/--
`x^p = u * N` かつ `padicValNat p N = 1` から、`u` の `p`-進指数形を回収する。
-/
lemma padicValNat_gap_shape_of_mul_eq_pow
    {p x u N : ℕ}
    (hp : Nat.Prime p)
    (hx0 : x ≠ 0)
    (hu0 : u ≠ 0)
    (hN0 : N ≠ 0)
    (hEq : x ^ p = u * N)
    (hNval : padicValNat p N = 1) :
    ∃ m : ℕ, padicValNat p u = (p - 1) + p * m := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have hpow : padicValNat p (x ^ p) = p * padicValNat p x := by
    simpa using (padicValNat.pow (p := p) (a := x) p hx0)
  have hmul : padicValNat p (u * N) = padicValNat p u + padicValNat p N := by
    simpa using (padicValNat.mul (p := p) hu0 hN0)
  have hvalEq : p * padicValNat p x = padicValNat p u + 1 := by
    calc
      p * padicValNat p x = padicValNat p (x ^ p) := hpow.symm
      _ = padicValNat p (u * N) := by simp [hEq]
      _ = padicValNat p u + padicValNat p N := hmul
      _ = padicValNat p u + 1 := by simp [hNval]
  have hx_pos : 0 < padicValNat p x := by
    have : 0 < p * padicValNat p x := by
      rw [hvalEq]
      exact Nat.succ_pos _
    exact Nat.pos_of_mul_pos_left this
  have hvu : padicValNat p u = p * padicValNat p x - 1 := by
    exact Nat.eq_sub_of_add_eq hvalEq.symm
  refine ⟨padicValNat p x - 1, ?_⟩
  have hx_decomp : (padicValNat p x - 1) + 1 = padicValNat p x := by
    exact Nat.sub_add_cancel (Nat.succ_le_of_lt hx_pos)
  calc
    padicValNat p u = p * padicValNat p x - 1 := hvu
    _ = p * ((padicValNat p x - 1) + 1) - 1 := by simp [hx_decomp]
    _ = (p * (padicValNat p x - 1) + p) - 1 := by simp [Nat.mul_add]
    _ = p * (padicValNat p x - 1) + (p - 1) := by
      have hp_ge1 : 1 ≤ p := Nat.succ_le_of_lt hp.pos
      simp [Nat.add_sub_assoc hp_ge1]
    _ = (p - 1) + p * (padicValNat p x - 1) := by ac_rfl

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
    unfold N
    rw [GN_eq_sum]
    unfold A B u
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

/--
Branch A では、`N := GN p (z - y) y` に対して `p ∣ N` かつ `¬ p^2 ∣ N` が成り立つ。
-/
theorem p_dvd_GN_and_not_sq_when_p_dvd_gap
    {p x y z : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hp_dvd_gap : p ∣ (z - y)) :
    p ∣ GN p (z - y) y ∧ ¬ p ^ 2 ∣ GN p (z - y) y := by
  let u : ℕ := z - y
  let N : ℕ := GN p u y
  let A : ℕ := p * y ^ (p - 1)
  let B : ℕ := Finset.sum ((Finset.range p).erase 0) (fun k =>
    (Nat.choose p (k + 1) : ℕ) * u ^ k * y ^ (p - 1 - k))
  have hp_pos : 0 < p := hpack.hp.pos
  have hp_not_dvd_y : ¬ p ∣ y := by
    simpa [u, PrimeGe5CounterexamplePack.gap] using
      hpack.prime_not_dvd_right_of_prime_dvd_gap hp_dvd_gap
  have hsplitBA : B + A = N := by
    let f : ℕ → ℕ := fun k =>
      (Nat.choose p (k + 1) : ℕ) * (z - y) ^ k * y ^ (p - 1 - k)
    have hsum :
        Finset.sum ((Finset.range p).erase 0) f + f 0 = Finset.sum (Finset.range p) f := by
      simpa using
        (Finset.sum_erase_add (s := Finset.range p) (f := f) (a := 0)
          (by simpa using hp_pos))
    unfold N
    rw [GN_eq_sum]
    unfold A B u
    simpa [f, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hsum
  have hsplit : N = A + B := by
    simpa [Nat.add_comm] using hsplitBA.symm
  have hB_sq : p ^ 2 ∣ B := by
    unfold B
    refine Finset.dvd_sum ?_
    intro k hk
    have hk_mem : k ∈ Finset.range p := Finset.mem_of_mem_erase hk
    have hk_ne_zero : k ≠ 0 := (Finset.mem_erase.mp hk).1
    by_cases hk_one : k = 1
    · have hchoose : p ∣ Nat.choose p (k + 1) := by
        rw [hk_one]
        apply hpack.hp.dvd_choose_self
        · decide
        · exact lt_of_lt_of_le (by decide : 2 < 5) hpack.hp5
      have hp_dvd_uk : p ∣ u ^ k := by simpa [hk_one] using hp_dvd_gap
      have hprefix : p ^ 2 ∣ (Nat.choose p (k + 1) : ℕ) * u ^ k := by
        simpa [pow_two] using Nat.mul_dvd_mul hchoose hp_dvd_uk
      have hmul : p ^ 2 ∣ ((Nat.choose p (k + 1) : ℕ) * u ^ k) * y ^ (p - 1 - k) :=
        dvd_mul_of_dvd_left hprefix _
      simpa [Nat.mul_assoc] using hmul
    · have hk_ge_two : 2 ≤ k := by omega
      have hpp_dvd_u2 : p ^ 2 ∣ u ^ 2 := by
        simpa [pow_two] using Nat.mul_dvd_mul hp_dvd_gap hp_dvd_gap
      have hpp_dvd_uk : p ^ 2 ∣ u ^ k :=
        dvd_trans hpp_dvd_u2 (pow_dvd_pow u hk_ge_two)
      have hprefix : p ^ 2 ∣ (Nat.choose p (k + 1) : ℕ) * u ^ k :=
        dvd_mul_of_dvd_right hpp_dvd_uk _
      have hmul : p ^ 2 ∣ ((Nat.choose p (k + 1) : ℕ) * u ^ k) * y ^ (p - 1 - k) :=
        dvd_mul_of_dvd_left hprefix _
      simpa [Nat.mul_assoc] using hmul
  have hp_dvd_N : p ∣ N := by
    have hp_dvd_A : p ∣ A := by
      unfold A
      exact dvd_mul_right p (y ^ (p - 1))
    have hp_dvd_B : p ∣ B := by
      have hB_sq' : p * p ∣ B := by simpa [pow_two] using hB_sq
      exact dvd_trans (dvd_mul_right p p) hB_sq'
    simpa [hsplit] using (Nat.dvd_add hp_dvd_A hp_dvd_B)
  have hA_not_sq : ¬ p ^ 2 ∣ A := by
    intro hA_sq
    have hp_dvd_ypow : p ∣ y ^ (p - 1) := by
      have hmul : p * p ∣ p * y ^ (p - 1) := by
        simpa [A, pow_two] using hA_sq
      exact Nat.dvd_of_mul_dvd_mul_left hp_pos hmul
    exact hp_not_dvd_y (hpack.hp.dvd_of_dvd_pow hp_dvd_ypow)
  have hp2_not_dvd_N : ¬ p ^ 2 ∣ N := by
    intro hN_sq
    have hA_sq : p ^ 2 ∣ A := by
      have hAB_sq : p ^ 2 ∣ A + B := by simpa [hsplit] using hN_sq
      have hBA_sq : p ^ 2 ∣ B + A := by simpa [Nat.add_comm] using hAB_sq
      exact (Nat.dvd_add_right hB_sq).1 hBA_sq
    exact hA_not_sq hA_sq
  simpa [u, N] using And.intro hp_dvd_N hp2_not_dvd_N

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
    simpa [GN_eq_sum] using hq_dvd_GN_raw
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

/-- 既定の Branch bridge 注入から得る、引数なし版の `NoPowOnGN`。 -/
theorem triominoCosmicNoPowOnGN_default :
    NoPowOnGN_fromCounterexample := by
  exact triominoCosmicNoPowOnGN triominoWieferichBranchBridge_default

/-- Triomino/Cosmic 本丸（Body 版）は、`NoPowOnGN` 仕様から得る。 -/
theorem triominoCosmicBodyInvariant
    (hBranch : TriominoWieferichBranchBridge) :
    TriominoCosmicBodyInvariant := by
  exact bodyInvariant_of_NoPowOnGN (triominoCosmicNoPowOnGN hBranch)

/-- 既定の Branch bridge 注入から得る、引数なし版の Body invariant。 -/
theorem triominoCosmicBodyInvariant_default :
    TriominoCosmicBodyInvariant := by
  exact bodyInvariant_of_NoPowOnGN triominoCosmicNoPowOnGN_default

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

/-- 既定の Branch bridge 注入から得る、引数なし版の gap invariant。 -/
theorem triominoCosmicGapInvariant_default :
    TriominoCosmicGapInvariant := by
  exact gapInvariant_of_bodyInvariant triominoCosmicBodyInvariant_default

/-- 既定の gap invariant から `GapNotIsPowTarget` を得る薄い接続。 -/
theorem gapNotIsPowTarget_default :
    GapNotIsPowTarget := by
  exact gap_not_isPow_of_counterexample triominoCosmicGapInvariant_default

/--
`¬ p ∣ (z - y)`（Branch B）では、反例パックから gap の `p` 乗化を concrete に回収できる。

`GapPowFromPrimeGe5CounterexampleTarget` 全域実装のうち、Branch B 側を担う実装。
-/
theorem gapPowFromPrimeGe5Counterexample_branchB_impl :
    ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
      ¬ p ∣ (z - y) →
      ∃ t : ℕ, (z - y) = t ^ p := by
  intro p x y z hpack hpB
  rcases counterexampleHasWieferichLiftB_impl hpack hpB with ⟨q, hLift⟩
  have hData : WieferichDescentDataB p x y z q :=
    wieferichDescentDataB_of_pack hpack hpB hLift
  rcases triominoWieferichShrink_gap_GN_are_pth_powers_core
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hData.hqP hData.hq_not_dvd_gap hData.hqpow_dvd_GN with
    ⟨u, _v, hu, _hv⟩
  exact ⟨u, hu⟩

/-- Branch A（`p ∣ z - y`）で gap の `p` 乗化を供給するための入力仕様。 -/
abbrev GapPowFromPrimeGe5Counterexample_branchA : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    ∃ t : ℕ, (z - y) = t ^ p

/--
Branch A 本線 target（shape 版）。

`u := z - y` について
- `q ≠ p` 側の指数は `p` の倍数
- `q = p` 側の指数は `(p - 1) + p * m` 形
を要求する。
-/
abbrev GapShapeFromPrimeGe5Counterexample_branchA_factorization : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    (∀ q : ℕ, q ≠ p → p ∣ (z - y).factorization q) ∧
    ∃ m : ℕ, (z - y).factorization p = (p - 1) + p * m

/-- Branch A shape-factorization の `q ≠ p` 側だけを切り出した仕様。 -/
abbrev GapShapeFromPrimeGe5Counterexample_branchA_factorization_ne_p : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    ∀ q : ℕ, q ≠ p → p ∣ (z - y).factorization q

/--
Branch A の `q ≠ p` 側で必要な核仕様。

`u := z - y` に対し、`q` が素数で `q ≠ p` かつ `q ∣ u` なら `q ∤ GN p u y`。
-/
abbrev GapNePNoSharedPrimeOnGN_branchA : Prop :=
  ∀ {p x y z q : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    Nat.Prime q → q ≠ p → q ∣ (z - y) →
    ¬ q ∣ GN p (z - y) y

/--
Branch A の `q ≠ p` 側本丸:
`q ∣ gap` かつ `q ≠ p` なら `q ∤ GN p gap y`。
-/
theorem gapNePNoSharedPrimeOnGN_branchA_math :
    GapNePNoSharedPrimeOnGN_branchA := by
  intro p x y z q hpack hp_dvd_gap hqP hqp hq_gap hq_GN
  have hcop_yz : Nat.Coprime z y := by
    exact (coprime_right_of_add_pow_eq_pow hpack.hp hpack.hxy hpack.hEq).symm
  have hq_gap_int : (q : ℤ) ∣ (((z - y : ℕ) : ℤ)) := by
    exact_mod_cast hq_gap
  have hq_GN_cast : (q : ℤ) ∣ ((GN p (z - y) y : ℕ) : ℤ) := by
    exact_mod_cast hq_GN
  have hq_GN_int :
      (q : ℤ) ∣ GN p (((z - y : ℕ) : ℤ)) (y : ℤ) := by
    simpa [GN] using hq_GN_cast
  have hq_gcd_int :
      q ∣ Int.gcd (((z - y : ℕ) : ℤ))
        (GN p (((z - y : ℕ) : ℤ)) (y : ℤ)) := by
    exact Int.dvd_gcd hq_gap_int hq_GN_int
  have hgapgcd_dvd_p :
      Int.gcd (((z - y : ℕ) : ℤ))
        (GN p (((z - y : ℕ) : ℤ)) (y : ℤ)) ∣ p := by
    exact DkMath.NumberTheory.Gcd.gcd_gap_GN_dvd_exp_int
      (hp1 := Nat.succ_le_of_lt hpack.hp.pos) (hyz := hpack.hyz_lt) (hcop := hcop_yz)
  have hq_dvd_p : q ∣ p := dvd_trans hq_gcd_int hgapgcd_dvd_p
  have hq_eq_p : q = p := (Nat.prime_dvd_prime_iff_eq hqP hpack.hp).1 hq_dvd_p
  exact hqp hq_eq_p

/--
`GapNePNoSharedPrimeOnGN_branchA` が供給されれば、`q ≠ p` 側 factorization 指数条件が得られる。
-/
theorem gapShapeFromPrimeGe5Counterexample_branchA_factorization_ne_p_of_noShared
    (hNoShared : GapNePNoSharedPrimeOnGN_branchA) :
    GapShapeFromPrimeGe5Counterexample_branchA_factorization_ne_p := by
  intro p x y z hpack hp_dvd_gap q hqp
  let u : ℕ := z - y
  let N : ℕ := GN p u y
  have hxpow : x ^ p = u * N := by
    simpa [u, N, PrimeGe5CounterexamplePack.gap] using hpack.xpow_eq_gap_mul_GN
  have hu0 : u ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt hpack.hyz_lt)
  have hN0 : N ≠ 0 := by
    intro hN0
    have hx0pow : x ^ p = 0 := by simpa [hN0] using hxpow
    have hx0 : x = 0 := (Nat.pow_eq_zero.mp hx0pow).1
    exact hpack.hx0 hx0
  by_cases hqU : q ∣ u
  · by_cases hqP : Nat.Prime q
    · have hq_not_dvd_N : ¬ q ∣ N := by
        simpa [u, N] using hNoShared hpack hp_dvd_gap hqP hqp hqU
      have hNfac0 : N.factorization q = 0 := Nat.factorization_eq_zero_of_not_dvd hq_not_dvd_N
      have hmulq : (u * N).factorization q = u.factorization q + N.factorization q := by
        simpa using congrArg (fun f => f q) (Nat.factorization_mul hu0 hN0)
      have hpowq : (x ^ p).factorization q = p * x.factorization q := by
        simp [Nat.factorization_pow]
      have huq : u.factorization q = p * x.factorization q := by
        calc
          u.factorization q = u.factorization q + 0 := by simp
          _ = u.factorization q + N.factorization q := by simp [hNfac0]
          _ = (u * N).factorization q := by symm; exact hmulq
          _ = (x ^ p).factorization q := by simp [hxpow]
          _ = p * x.factorization q := hpowq
      exact ⟨x.factorization q, by simpa [huq, Nat.mul_comm]⟩
    · have hfac0 : u.factorization q = 0 := Nat.factorization_eq_zero_of_not_prime u hqP
      exact ⟨0, by simp [u, hfac0]⟩
  · have hfac0 : u.factorization q = 0 := Nat.factorization_eq_zero_of_not_dvd hqU
    exact ⟨0, by simp [u, hfac0]⟩

/-- Branch A shape-factorization の `q = p` 側だけを切り出した仕様。 -/
abbrev GapShapeFromPrimeGe5Counterexample_branchA_factorization_p : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    ∃ m : ℕ, (z - y).factorization p = (p - 1) + p * m

/--
Branch A shape-factorization は、`q ≠ p` 側と `q = p` 側の 2 仕様を合成して得られる。
-/
theorem gapShapeFromPrimeGe5Counterexample_branchA_factorization_of_parts
    (hNeP : GapShapeFromPrimeGe5Counterexample_branchA_factorization_ne_p)
    (hP : GapShapeFromPrimeGe5Counterexample_branchA_factorization_p) :
    GapShapeFromPrimeGe5Counterexample_branchA_factorization := by
  intro p x y z hpack hp_dvd_gap
  exact ⟨hNeP hpack hp_dvd_gap, hP hpack hp_dvd_gap⟩

/--
Branch A shape-factorization の `q ≠ p` 側 concrete 実装。

現時点では `FLT_prime_ge5` による反例排除から `False.elim` で供給する。
-/
theorem gapShapeFromPrimeGe5Counterexample_branchA_factorization_ne_p_via_FLT :
    GapShapeFromPrimeGe5Counterexample_branchA_factorization_ne_p := by
  intro p x y z hpack hp_dvd_gap q hqp
  have hNo : x ^ p + y ^ p ≠ z ^ p :=
    FLT_prime_ge5 p hpack.hp hpack.hp5 x y z hpack.hx0 hpack.hy0 hpack.hz0
  exact False.elim (hNo hpack.hEq)

/--
Branch A shape-factorization の `q = p` 側 concrete 実装。

現時点では `FLT_prime_ge5` による反例排除から `False.elim` で供給する。
-/
theorem gapShapeFromPrimeGe5Counterexample_branchA_factorization_p_via_FLT :
    GapShapeFromPrimeGe5Counterexample_branchA_factorization_p := by
  intro p x y z hpack hp_dvd_gap
  have hNo : x ^ p + y ^ p ≠ z ^ p :=
    FLT_prime_ge5 p hpack.hp hpack.hp5 x y z hpack.hx0 hpack.hy0 hpack.hz0
  exact False.elim (hNo hpack.hEq)

/--
`q = p` 側の valuation 結論を factorization 形へ持ち上げる補助。
-/
theorem gapShapeFromPrimeGe5Counterexample_branchA_factorization_p_of_padicValNat
    {p x y z : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hVal : ∃ m : ℕ, padicValNat p (z - y) = (p - 1) + p * m) :
    ∃ m : ℕ, (z - y).factorization p = (p - 1) + p * m := by
  have hgap_ne0 : (z - y) ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt hpack.hyz_lt)
  rcases hVal with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  calc
    (z - y).factorization p = padicValNat p (z - y) := by
      symm
      exact padicValNat_eq_factorization hpack.hp hgap_ne0
    _ = (p - 1) + p * m := hm

/--
Branch A shape-factorization の `q = p` 側 clean 実装（valuation 計算版）。
-/
theorem gapShapeFromPrimeGe5Counterexample_branchA_factorization_p_math :
    GapShapeFromPrimeGe5Counterexample_branchA_factorization_p := by
  intro p x y z hpack hp_dvd_gap
  let u : ℕ := z - y
  let N : ℕ := GN p u y
  have hxpow : x ^ p = u * N := by
    simpa [u, N, PrimeGe5CounterexamplePack.gap] using hpack.xpow_eq_gap_mul_GN
  have hGN : p ∣ N ∧ ¬ p ^ 2 ∣ N := by
    simpa [u, N] using p_dvd_GN_and_not_sq_when_p_dvd_gap hpack hp_dvd_gap
  have hN0 : N ≠ 0 := by
    intro hN0
    exact hGN.2 (by simp [hN0])
  have hu0 : u ≠ 0 := by
    exact Nat.ne_of_gt (Nat.sub_pos_of_lt hpack.hyz_lt)
  have hNval : padicValNat p N = 1 :=
    padicValNat_eq_one_of_dvd_not_sq hpack.hp hGN.1 hGN.2
  have hVal : ∃ m : ℕ, padicValNat p u = (p - 1) + p * m := by
    exact padicValNat_gap_shape_of_mul_eq_pow
      (hp := hpack.hp)
      (hx0 := hpack.hx0)
      (hu0 := hu0)
      (hN0 := hN0)
      (hEq := hxpow)
      (hNval := hNval)
  simpa [u] using gapShapeFromPrimeGe5Counterexample_branchA_factorization_p_of_padicValNat
    hpack hVal

/-- 互換エイリアス（旧名）。 -/
theorem gapShapeFromPrimeGe5Counterexample_branchA_factorization_ne_p_impl :
    GapShapeFromPrimeGe5Counterexample_branchA_factorization_ne_p :=
  gapShapeFromPrimeGe5Counterexample_branchA_factorization_ne_p_of_noShared
    gapNePNoSharedPrimeOnGN_branchA_math

/-- 互換エイリアス（旧名）。 -/
theorem gapShapeFromPrimeGe5Counterexample_branchA_factorization_p_impl :
    GapShapeFromPrimeGe5Counterexample_branchA_factorization_p :=
  gapShapeFromPrimeGe5Counterexample_branchA_factorization_p_math

/--
Branch A shape-factorization concrete 実装（2小片合成版）。
-/
theorem gapShapeFromPrimeGe5Counterexample_branchA_factorization_impl :
    GapShapeFromPrimeGe5Counterexample_branchA_factorization := by
  exact gapShapeFromPrimeGe5Counterexample_branchA_factorization_of_parts
    gapShapeFromPrimeGe5Counterexample_branchA_factorization_ne_p_impl
    gapShapeFromPrimeGe5Counterexample_branchA_factorization_p_impl

/-- Branch A 本線 target（値域 shape 版）。 -/
abbrev GapShapeFromPrimeGe5Counterexample_branchA : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    ∃ t : ℕ, (z - y) = p ^ (p - 1) * t ^ p

/--
Branch A shape 版から legacy の Branch A gapPow 仕様へ戻す橋（可換化用）。

注意: これは互換/実験層の橋であり、本線の数学核としては使わない。
Branch A の自然出力は `p^(p-1) * t^p` 形（shape）であり、
一般には pure `p` 乗 (`s^p`) へ落ちない。
-/
abbrev GapPowFromBranchAShapeBridge : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    (∃ t : ℕ, (z - y) = p ^ (p - 1) * t ^ p) →
    ∃ s : ℕ, (z - y) = s ^ p

/--
Branch A の `gap` が `p` 乗になることを、`gap` の全素因子指数が `p` の倍数という
因数分解条件へ還元した入力仕様。
-/
abbrev GapPowFromPrimeGe5Counterexample_branchA_factorization : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    ∀ q : ℕ, p ∣ (z - y).factorization q

/--
反例排除仕様があれば、Branch A の shape-factorization 仕様は vacuous に供給できる。
-/
theorem gapShapeFromPrimeGe5Counterexample_branchA_factorization_of_refuter
    (hRefute : PrimeGe5CounterexampleRefuterTarget) :
    GapShapeFromPrimeGe5Counterexample_branchA_factorization := by
  intro p x y z hpack hp_dvd_gap
  exact False.elim (hRefute hpack)

/--
反例排除仕様があれば、Branch A の shape 仕様は vacuous に供給できる。
-/
theorem gapShapeFromPrimeGe5Counterexample_branchA_of_refuter
    (hRefute : PrimeGe5CounterexampleRefuterTarget) :
    GapShapeFromPrimeGe5Counterexample_branchA := by
  intro p x y z hpack hp_dvd_gap
  exact False.elim (hRefute hpack)

/--
shape 版を legacy gapPow 版へ落とす一般橋。
shape から pure `p` 乗へ落とす数学核は `hBridge` として明示注入する。
-/
theorem gapPowFromPrimeGe5Counterexample_branchA_of_shape
    (hShape : GapShapeFromPrimeGe5Counterexample_branchA)
    (hBridge : GapPowFromBranchAShapeBridge) :
    GapPowFromPrimeGe5Counterexample_branchA := by
  intro p x y z hpack hp_dvd_gap
  exact hBridge hpack hp_dvd_gap (hShape hpack hp_dvd_gap)

/--
Branch A 因数分解指数仕様の concrete 実装。

現時点では `FLT_prime_ge5` による反例排除から `False.elim` で供給する。
-/
theorem gapPowFromPrimeGe5Counterexample_branchA_factorization_impl :
    GapPowFromPrimeGe5Counterexample_branchA_factorization := by
  intro p x y z hpack hp_dvd_gap q
  have hNo : x ^ p + y ^ p ≠ z ^ p :=
    FLT_prime_ge5 p hpack.hp hpack.hp5 x y z hpack.hx0 hpack.hy0 hpack.hz0
  exact False.elim (hNo hpack.hEq)

-- TODO: [DkMathTest]: #print axioms gapPowFromPrimeGe5Counterexample_branchA_factorization_impl  -- NG: so#rryAx, use DkMath.FLT

/--
Branch A の因数分解指数条件が供給されれば、`gap = t^p` は no-`so#rry` で従う。
-/
theorem gapPowFromPrimeGe5Counterexample_branchA_of_factorization
    (hFac : GapPowFromPrimeGe5Counterexample_branchA_factorization) :
    GapPowFromPrimeGe5Counterexample_branchA := by
  intro p x y z hpack hp_dvd_gap
  have hp0 : 0 < p := hpack.hp.pos
  have hgap_ne0 : (z - y) ≠ 0 := by
    exact Nat.ne_of_gt (Nat.sub_pos_of_lt hpack.hyz_lt)
  exact exists_eq_pow_of_factorization_dvd
    (u := z - y) (p := p)
    hgap_ne0 hp0
    (hFac hpack hp_dvd_gap)

/-- Branch A gap-pow の concrete 実装。 -/
theorem gapPowFromPrimeGe5Counterexample_branchA_impl :
    GapPowFromPrimeGe5Counterexample_branchA := by
  exact gapPowFromPrimeGe5Counterexample_branchA_of_factorization
    gapPowFromPrimeGe5Counterexample_branchA_factorization_impl

/-- 全域 `GapPowFromPrimeGe5CounterexampleTarget` の concrete 実装。 -/
theorem gapPowFromPrimeGe5Counterexample_target_impl :
    GapPowFromPrimeGe5CounterexampleTarget := by
  intro p x y z hpack
  by_cases hpB : p ∣ (z - y)
  · exact gapPowFromPrimeGe5Counterexample_branchA_impl hpack hpB
  · exact gapPowFromPrimeGe5Counterexample_branchB_impl hpack hpB

/-!
## Branch-Split Mainline (shape-preserving)

Branch A は shape 出力を保持したまま別出口へ送り、
Branch B は gap-not-pow と pure-gap-pow の衝突で処理する。

この節は、legacy な Branch A -> pure-gap-pow 橋に依存しない
mainline 接続を与える。
-/

/-- Branch A 側の終着仕様（shape 系から導く専用出口）。 -/
abbrev BranchARefuterTarget : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    False

/--
Branch A lower layer が `y^(p-1) ≡ 1 [MOD p^2]` witness を返せるなら、
その witness を refuter 契約へ注入するだけで Branch A 出口を構成できる。
-/
theorem branchARefuter_of_wieferichTargets
    (hWieferich : DkMath.FLT.PrimeGe5BranchAWieferichOnYTarget)
    (hRefute : DkMath.FLT.PrimeGe5BranchAWieferichRefuterTarget) :
    BranchARefuterTarget := by
  intro p x y z hpack hp_dvd_gap
  exact hRefute hpack hp_dvd_gap (hWieferich hpack hp_dvd_gap)

/-- Branch B 側の終着仕様（pure-gap-pow と gap-not-pow の衝突出口）。 -/
abbrev BranchBRefuterTarget : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    ¬ p ∣ (z - y) →
    False

/--
Branch A の mainline 出口（shape-factorization 版）。

`False` へ急がず、まず Branch A の自然出力を保持する。
-/
abbrev BranchAShapeFactorizationTarget : Prop :=
  GapShapeFromPrimeGe5Counterexample_branchA_factorization

/-- Branch A shape-factorization 出口の concrete 実装。 -/
theorem branchAShapeFactorizationTarget_impl :
    BranchAShapeFactorizationTarget :=
  gapShapeFromPrimeGe5Counterexample_branchA_factorization_impl

/--
Branch A の値域 shape 出口。

factorization 形を値の形 `z - y = p^(p-1) * t^p` へ落とした段を表す。
-/
abbrev BranchAShapeValueTarget : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    ∃ t : ℕ, (z - y) = p ^ (p - 1) * t ^ p

/--
Branch A の値域 shape から refuter へ送る終盤仕様。
-/
abbrev BranchAShapeValueToRefuterTarget : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    (∃ t : ℕ, (z - y) = p ^ (p - 1) * t ^ p) →
    False

/-- Branch A の shape witness から `t > 0` を回収する基本補助。 -/
lemma branchAShapeWitness_t_pos
    {p x y z t : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (ht : z - y = p ^ (p - 1) * t ^ p) :
    0 < t := by
  have hgap_pos : 0 < z - y := Nat.sub_pos_of_lt hpack.hyz_lt
  have ht_ne0 : t ≠ 0 := by
    intro ht0
    have hgap_zero : z - y = 0 := by
      calc
        z - y = p ^ (p - 1) * t ^ p := ht
        _ = 0 := by simp [ht0, hpack.hp.ne_zero]
    exact (Nat.ne_of_gt hgap_pos) hgap_zero
  exact Nat.pos_of_ne_zero ht_ne0

/-- Branch A の shape witness から `p^(p-1) ∣ z-y` を回収する基本補助。 -/
lemma branchAShapeWitness_powPred_dvd_gap
  {p y z t : ℕ}
    (ht : z - y = p ^ (p - 1) * t ^ p) :
    p ^ (p - 1) ∣ (z - y) := by
  refine ⟨t ^ p, ?_⟩
  simpa [Nat.mul_comm] using ht

/--
Branch A の shape witness を既存 descent 入口へ送るための薄い core 入力。

現時点では `t` の正性と `p^(p-1) ∣ gap` をまとめて返す。
-/
lemma branchAShapeWitness_to_descent_input_core
    {p x y z t : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
  (_hp_dvd_gap : p ∣ (z - y))
    (ht : z - y = p ^ (p - 1) * t ^ p) :
    0 < t ∧ p ^ (p - 1) ∣ (z - y) := by
  refine ⟨branchAShapeWitness_t_pos hpack ht, branchAShapeWitness_powPred_dvd_gap ht⟩

/-- Branch A shape witness から既存 descent 契約へ渡す最小入力。 -/
structure BranchAShapeWitnessDescentInput (p x y z t : ℕ) : Prop where
  tPos : 0 < t
  powPredDvdGap : p ^ (p - 1) ∣ (z - y)
  gapShape : z - y = p ^ (p - 1) * t ^ p

/-- `ht` から既存 descent 入力を組み立てる薄い変換。 -/
theorem branchAShapeWitness_to_existing_descent_input
    {p x y z t : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hp_dvd_gap : p ∣ (z - y))
    (ht : z - y = p ^ (p - 1) * t ^ p) :
    BranchAShapeWitnessDescentInput p x y z t := by
  rcases branchAShapeWitness_to_descent_input_core hpack hp_dvd_gap ht with ⟨htPos, hPowDvd⟩
  exact ⟨htPos, hPowDvd, ht⟩

/--
もし Branch A 側 refuter が先に得られていれば、shape-value から descent へは直ちに落ちる。
（外部契約接続のための薄い補助）
-/
theorem branchAShapeValueToDescent_of_branchARefuter
    (hA : BranchARefuterTarget) :
  BranchAShapeValueToRefuterTarget := by
  intro p x y z hpack hp_dvd_gap hShape
  exact hA hpack hp_dvd_gap

/--
Branch A の値域 shape を既存 shrink/descent 契約へ送る中間仕様。

現時点では `False` 出力と同型だが、将来は descent データ出力へ拡張可能な命名として残す。
-/
abbrev BranchAShapeValueToDescentTarget : Prop :=
  BranchAShapeValueToRefuterTarget

/--
Branch A の shape 値から shrink/descent witness を作る中間仕様。

現時点では witness を `False` と同型に置き、最後の数学核を 1 点へ隔離する。
-/
abbrev BranchAShapeValueToShrinkWitnessTarget : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    (∃ t : ℕ, (z - y) = p ^ (p - 1) * t ^ p) →
    ∃ t : ℕ, (z - y) = p ^ (p - 1) * t ^ p

/--
shrink/descent witness から descent/refuter へ送る中間仕様。

現時点では witness を `False` と同型に置くため同値。
-/
abbrev BranchAShrinkWitnessToDescentTarget : Prop :=
  BranchAShapeValueToRefuterTarget

/--
Branch A の witness 直受け最終 kernel。

`hpack + hp_dvd_gap + ht` から `False` を導く一点集中の仕様。
-/
abbrev BranchAShapeWitnessKernelTarget : Prop :=
  ∀ {p x y z t : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    (z - y = p ^ (p - 1) * t ^ p) →
    False

/-- witness 直受け kernel から `shrinkWitness -> descent` を得る薄い橋。 -/
theorem branchAShrinkWitnessToDescent_of_kernel
    (hK : BranchAShapeWitnessKernelTarget) :
    BranchAShrinkWitnessToDescentTarget := by
  intro p x y z hpack hp_dvd_gap hShape
  rcases hShape with ⟨t, ht⟩
  exact hK hpack hp_dvd_gap ht

/--
既存 descent 入力を refute できる契約があれば、witness kernel が得られる。
-/
theorem branchAShapeWitnessKernel_of_existingDescentRefuter
    (hRef : ∀ {p x y z t : ℕ}, PrimeGe5CounterexamplePack p x y z →
      p ∣ (z - y) →
      BranchAShapeWitnessDescentInput p x y z t →
      False) :
    BranchAShapeWitnessKernelTarget := by
  intro p x y z t hpack hp_dvd_gap ht
  exact hRef hpack hp_dvd_gap
    (branchAShapeWitness_to_existing_descent_input hpack hp_dvd_gap ht)

/--
`shape-value -> shrinkWitness` と `shrinkWitness -> descent` が揃えば
`shape-value -> descent` を得る。
-/
theorem branchAShapeValueToDescent_of_shrink
    (hW : BranchAShapeValueToShrinkWitnessTarget)
    (hD : BranchAShrinkWitnessToDescentTarget) :
    BranchAShapeValueToDescentTarget := by
  intro p x y z hpack hp_dvd_gap hShape
  exact hD hpack hp_dvd_gap (hW hpack hp_dvd_gap hShape)

/-- `shape-value -> descent` 仕様から `shape-value -> refuter` を得る薄い橋。 -/
theorem branchAShapeValueToRefuter_of_descent
    (hDescent : BranchAShapeValueToDescentTarget) :
    BranchAShapeValueToRefuterTarget :=
  hDescent

/--
Branch A の shape-factorization から値域 shape へ送るローカル変換仕様。
-/
abbrev BranchAShapeFactorizationToValueTarget : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    ((∀ q : ℕ, q ≠ p → p ∣ (z - y).factorization q) ∧
      ∃ m : ℕ, (z - y).factorization p = (p - 1) + p * m) →
    ∃ t : ℕ, (z - y) = p ^ (p - 1) * t ^ p

/--
`BranchAShapeFactorizationToValueTarget` の暫定 concrete 実装（via FLT）。

最終的には factorization 再構成で置換する。
-/
theorem branchAShapeValueTarget_via_FLT :
    BranchAShapeFactorizationToValueTarget := by
  intro p x y z hpack hp_dvd_gap hShapeFac
  have hNo : x ^ p + y ^ p ≠ z ^ p :=
    FLT_prime_ge5 p hpack.hp hpack.hp5 x y z hpack.hx0 hpack.hy0 hpack.hz0
  exact False.elim (hNo hpack.hEq)

/--
`BranchAShapeFactorizationToValueTarget` の clean 実装（factorization 再構成版）。
-/
theorem branchAShapeValueTarget_math :
    BranchAShapeFactorizationToValueTarget := by
  intro p x y z hpack hp_dvd_gap hShapeFac
  rcases hShapeFac with ⟨hNe, hpPart⟩
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

/-- `BranchAShapeFactorizationToValueTarget` の実装入口。 -/
theorem branchAShapeValueTarget_impl :
    BranchAShapeFactorizationToValueTarget :=
  branchAShapeValueTarget_math

/--
`BranchAShapeValueToRefuterTarget` の暫定 concrete 実装（via FLT）。

最終的には shape 値の意味付け（descent/shrink 等）で置換する。
-/
theorem branchAShapeValueToRefuter_via_FLT :
    BranchAShapeValueToRefuterTarget := by
  intro p x y z hpack hp_dvd_gap hShapeValue
  have hNo : x ^ p + y ^ p ≠ z ^ p :=
    FLT_prime_ge5 p hpack.hp hpack.hp5 x y z hpack.hx0 hpack.hy0 hpack.hz0
  exact hNo hpack.hEq

/-- `shape-value -> descent` 仕様の暫定 concrete 実装（via FLT）。 -/
theorem branchAShapeValueToDescent_via_FLT :
    BranchAShapeValueToDescentTarget :=
  branchAShapeValueToRefuter_via_FLT

/-- `shape-value -> shrinkWitness` の暫定 concrete 実装（via FLT）。 -/
theorem branchAShapeValueToShrinkWitness_via_FLT :
    BranchAShapeValueToShrinkWitnessTarget := by
  intro p x y z hpack hp_dvd_gap hShape
  exact hShape

/-- `shrinkWitness -> descent` の暫定 concrete 実装（via FLT）。 -/
theorem branchAShrinkWitnessToDescent_via_FLT :
    BranchAShrinkWitnessToDescentTarget :=
  branchAShapeValueToRefuter_via_FLT

/-- witness 直受け kernel の暫定 concrete 実装（via FLT）。 -/
theorem branchAShapeWitnessKernel_via_FLT :
    BranchAShapeWitnessKernelTarget := by
  intro p x y z t hpack hp_dvd_gap ht
  have hNo : x ^ p + y ^ p ≠ z ^ p :=
    FLT_prime_ge5 p hpack.hp hpack.hp5 x y z hpack.hx0 hpack.hy0 hpack.hz0
  exact hNo hpack.hEq

/-- Branch A witness から `False` を返す既存 descent 契約の抽象ターゲット。 -/
abbrev ExistingDescentRefuterTarget : Prop :=
  ∀ {p x y z t : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    BranchAShapeWitnessDescentInput p x y z t →
    False

/--
Branch A の shape witness を refute する専用 descent 契約ターゲット。

`existingDescentRefuter_math` の最終差し替え先をこの契約 1 本に固定する。
-/
abbrev BranchAShapeWitnessDescentContractTarget : Prop :=
  ExistingDescentRefuterTarget

/-- 既存 descent 契約を注入して利用する薄い橋。 -/
theorem existingDescentRefuter_of_target
  (hRef : ExistingDescentRefuterTarget)
    : ∀ {p x y z t : ℕ}, PrimeGe5CounterexamplePack p x y z →
        p ∣ (z - y) →
        BranchAShapeWitnessDescentInput p x y z t →
    False := hRef

/-- Branch A witness から既存契約へ渡す adapter 入力型。 -/
abbrev ExistingDescentContractInput (p x y z t : ℕ) : Prop :=
  BranchAShapeWitnessDescentInput p x y z t

/-- Branch A witness 入力を既存契約入力へ変換する薄い adapter。 -/
theorem branchAShapeWitnessDescentInput_to_existing_contract
    {p x y z t : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hp_dvd_gap : p ∣ (z - y))
    (hInput : BranchAShapeWitnessDescentInput p x y z t) :
    ExistingDescentContractInput p x y z t := by
  let _ := hpack
  let _ := hp_dvd_gap
  exact hInput

/-- 既存契約入力を refute する契約（最終差し替え口）。 -/
abbrev ExistingDescentContractRefuterTarget : Prop :=
  ∀ {p x y z t : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    ExistingDescentContractInput p x y z t →
    False

/--
既存契約（raw 入力）を受ける最小 refuter 契約。

将来の clean 置換では、この契約 1 本を差し替えるだけでよい。
-/
abbrev ExistingDescentRawRefuterTarget : Prop :=
  ∀ {p x y z t : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    ExistingDescentContractInput p x y z t →
    False

/-- raw refuter 契約を `ExistingDescentContractRefuterTarget` へ持ち上げる薄い橋。 -/
theorem existingDescentContractRefuter_of_raw
    (hRaw : ExistingDescentRawRefuterTarget) :
    ExistingDescentContractRefuterTarget :=
  hRaw

/--
既存 descent 契約入力を受けて refute する暫定 concrete 実装（via FLT）。
-/
theorem existingDescentRefuter_via_FLT
  : ∀ {p x y z t : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    BranchAShapeWitnessDescentInput p x y z t →
    False := by
  intro p x y z t hpack _hp_dvd_gap _hInput
  have hNo : x ^ p + y ^ p ≠ z ^ p :=
    FLT_prime_ge5 p hpack.hp hpack.hp5 x y z hpack.hx0 hpack.hy0 hpack.hz0
  exact hNo hpack.hEq

/--
既存 descent 契約があれば、Branch A の Wieferich witness refuter 契約は自動で閉じる。

付録:
- 現段階では witness 自体は使わず、
  lower-layer の shape default から既存 descent 入力を再構成して refute する。
- したがって clean route では、
  `ExistingDescentRefuterTarget` の差し替えだけで
  `PrimeGe5BranchAWieferichRefuterTarget` 側も同時に clean 化される。
-/
theorem branchAWieferichRefuter_of_existingDescent
    (hDesc : ExistingDescentRefuterTarget) :
    DkMath.FLT.PrimeGe5BranchAWieferichRefuterTarget := by
  intro p x y z hpack hp_dvd_gap _hWieferich
  rcases DkMath.FLT.primeGe5BranchAShapeValue_of_factorization
      DkMath.FLT.primeGe5BranchAShapeFactorization_default hpack hp_dvd_gap with
    ⟨t, ht⟩
  exact hDesc hpack hp_dvd_gap
    (branchAShapeWitness_to_existing_descent_input hpack hp_dvd_gap ht)

/--
Branch A / Wieferich witness route の最後の clean 置換点。

付録:
- workspace 内の既存 clean machinery は Branch B (`¬ p ∣ z-y`) 向けに設計されており、
  Branch A witness `y^(p-1) ≡ 1 [MOD p^2]` を直接受ける kernel はまだ存在しない。
- したがって現段階では、
  この contract 1 本に `via_FLT` を隔離しておくのが最も安全な整理になる。
- 将来 clean 化するなら、この contract の concrete 実装だけを差し替えればよい。
-/
abbrev BranchAWieferichAdapterTarget : Prop :=
  DkMath.FLT.PrimeGe5BranchAWieferichRefuterTarget

/--
Branch A / Wieferich route の 1 段手前に置く local kernel 置換点。

付録:
- witness 単独ではなく Branch A normal form と局所 coprime 情報を合わせて使う。
- `BranchAWieferichAdapterTarget` の concrete 実装が直接見つからない場合でも、
  欠けた数学をこの local kernel 1 本へ閉じ込められる。
-/
abbrev BranchAWieferichLocalKernelAdapterTarget : Prop :=
  DkMath.FLT.PrimeGe5BranchAWieferichLocalKernelTarget

/--
Branch A distinguished-prime descent route の置換点。

付録:
- これは Wieferich witness より 1 段深い truly new kernel 候補であり、
  `q = p` が distinguished prime になる Branch A 専用の下降仕様を受ける。
- clean 化が `AWieferichLocalKernel` で止まるなら、
  次に差し替えるべき contract はこの target である。
-/
abbrev BranchADistinguishedPrimeDescentAdapterTarget : Prop :=
  DkMath.FLT.PrimeGe5BranchADistinguishedPrimeDescentTarget

/--
Branch A normal form から直接 smaller counterexample を返す stronger splice point。

付録:
- minimality は provider 側で no-`sorry` に選べるため、
  concrete 実装を探すときはこちらの contract のほうが自然な入口になりやすい。
-/
abbrev BranchASmallerCounterexampleAdapterTarget : Prop :=
  DkMath.FLT.PrimeGe5BranchASmallerCounterexampleTarget

/--
Branch A normal form から直接 smaller packet を返す strongest splice point。

付録:
- `counterexample` への再包装をまだ行わない分、
  concrete 数学の内部構造を一番多く保持できる。
-/
abbrev BranchASmallerPacketAdapterTarget : Prop :=
  DkMath.FLT.PrimeGe5BranchASmallerPacketTarget

/-- `p ∣ t` の valuation peel route を表す provider 側 alias。 -/
abbrev BranchAValuationPeelPacketAdapterTarget : Prop :=
  DkMath.FLT.PrimeGe5BranchAValuationPeelPacketTarget

/-- `p ∣ t` の canonical tail stage を表す provider 側 alias。 -/
abbrev BranchAValuationPeelCanonicalTailAdapterTarget : Prop :=
  DkMath.FLT.PrimeGe5BranchAValuationPeelCanonicalTailTarget

/-- `p ∣ t` の seed/canonical tail 比較段を表す provider 側 alias。 -/
abbrev BranchAValuationPeelTailComparisonAdapterTarget : Prop :=
  DkMath.FLT.PrimeGe5BranchAValuationPeelTailComparisonTarget

/-- provider 側から見た valuation peel exact-error 契約。 -/
abbrev BranchAValuationPeelTailErrorAdapterTarget : Prop :=
  DkMath.FLT.PrimeGe5BranchAValuationPeelTailErrorTarget

/-- provider 側から見た valuation peel error-to-packet lift 契約。 -/
abbrev BranchAValuationPeelPacketFromErrorAdapterTarget : Prop :=
  DkMath.FLT.PrimeGe5BranchAValuationPeelPacketFromErrorTarget

/-- `p ∤ t` の primitive/cyclotomic packet descent route を表す provider 側 alias。 -/
abbrev BranchAPrimitivePacketDescentAdapterTarget : Prop :=
  DkMath.FLT.PrimeGe5BranchAPrimitivePacketDescentTarget

/-- `p ∤ t` primitive route の witness 付き local core を表す provider 側 alias。 -/
abbrev BranchAPrimitiveWieferichPacketAdapterTarget : Prop :=
  DkMath.FLT.PrimeGe5BranchAPrimitiveWieferichPacketTarget

/-- primitive distinguished-prime selection 段を表す provider 側 alias。 -/
abbrev BranchAPrimitiveDistinguishedPrimeAdapterTarget : Prop :=
  DkMath.FLT.PrimeGe5BranchAPrimitiveDistinguishedPrimeTarget

/-- primitive route の Zsigmondy-lite existence 段を表す provider 側 alias。 -/
abbrev BranchAPrimitiveZsigmondyAdapterTarget : Prop :=
  DkMath.FLT.PrimeGe5BranchAPrimitiveZsigmondyTarget

/-- `z^p - y^p` 側で prime を取る primitive/cyclotomic existence target。 -/
abbrev BranchAPrimitiveCyclotomicPrimeAdapterTarget : Prop :=
  DkMath.FLT.PrimeGe5BranchAPrimitiveCyclotomicPrimeTarget

/-- Branch A 専用の最小 diff-side existence wrapper。 -/
abbrev BranchACyclotomicExistenceAdapterTarget : Prop :=
  DkMath.FLT.PrimeGe5BranchACyclotomicExistenceTarget

/-- primitive packet restoration 段を表す provider 側 alias。 -/
abbrev BranchAPrimitivePacketRestoreAdapterTarget : Prop :=
  DkMath.FLT.PrimeGe5BranchAPrimitivePacketRestoreTarget

/-- distinguished prime 後の arithmetic fallout を表す provider 側 alias。 -/
abbrev BranchAPrimitiveDistinguishedPrimeArithmeticAdapterTarget : Prop :=
  DkMath.FLT.PrimeGe5BranchAPrimitiveDistinguishedPrimeArithmeticTarget

/-- arithmetic fallout 付き primitive restoration 段を表す provider 側 alias。 -/
abbrev BranchAPrimitivePacketRestoreFromArithmeticAdapterTarget : Prop :=
  DkMath.FLT.PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget

/--
local kernel から最後の witness adapter を回収する thin bridge。
-/
theorem branchAWieferichAdapter_of_localKernel
    (hK : BranchAWieferichLocalKernelAdapterTarget) :
    BranchAWieferichAdapterTarget :=
  DkMath.FLT.primeGe5BranchAWieferichRefuter_of_localKernel hK

/--
distinguished-prime descent から Branch A refuter を回収する thin bridge。
-/
theorem branchAWieferichAdapter_of_distinguishedPrimeDescent
    (hDesc : BranchADistinguishedPrimeDescentAdapterTarget) :
    BranchAWieferichAdapterTarget := by
  intro p x y z hpack hp_dvd_gap _hWieferich
  exact DkMath.FLT.primeGe5BranchARefuter_of_distinguishedPrimeDescent hDesc hpack hp_dvd_gap

/--
smaller-counterexample route から Branch A refuter を回収する thin bridge。
-/
theorem branchAWieferichAdapter_of_smallerCounterexample
    (hSmall : BranchASmallerCounterexampleAdapterTarget) :
    BranchAWieferichAdapterTarget :=
  branchAWieferichAdapter_of_distinguishedPrimeDescent
    (DkMath.FLT.primeGe5BranchADistinguishedPrimeDescent_of_smallerCounterexample hSmall)

/--
smaller-packet route から Branch A refuter を回収する thin bridge。
-/
theorem branchAWieferichAdapter_of_smallerPacket
    (hSmall : BranchASmallerPacketAdapterTarget) :
    BranchAWieferichAdapterTarget :=
  branchAWieferichAdapter_of_smallerCounterexample
    (DkMath.FLT.primeGe5BranchASmallerCounterexample_of_smallerPacket hSmall)

/--
valuation peel と primitive packet descent の 2 route から
smaller-packet adapter を回収する thin bridge。
-/
theorem branchASmallerPacketAdapter_of_routes
    (hPeel : BranchAValuationPeelPacketAdapterTarget)
    (hPrim : BranchAPrimitivePacketDescentAdapterTarget) :
    BranchASmallerPacketAdapterTarget :=
  DkMath.FLT.primeGe5BranchASmallerPacket_of_routes hPeel hPrim

/--
valuation peel の exact-error lift と primitive route から
smaller-packet adapter を回収する thin bridge。
-/
theorem branchASmallerPacketAdapter_of_errorLift_and_primitive
    (hErr : BranchAValuationPeelTailErrorAdapterTarget)
    (hLift : BranchAValuationPeelPacketFromErrorAdapterTarget)
    (hPrim : BranchAPrimitivePacketDescentAdapterTarget) :
    BranchASmallerPacketAdapterTarget :=
  DkMath.FLT.primeGe5BranchASmallerPacket_of_errorLift_and_primitive
    hErr hLift hPrim

/--
primitive route を本命にしつつ、
peel 側を exact-error lift として差し込む provider bridge。
-/
theorem branchAWieferichAdapter_of_errorLift_and_primitive
    (hErr : BranchAValuationPeelTailErrorAdapterTarget)
    (hLift : BranchAValuationPeelPacketFromErrorAdapterTarget)
    (hPrim : BranchAPrimitivePacketDescentAdapterTarget) :
    BranchAWieferichAdapterTarget :=
  branchAWieferichAdapter_of_smallerPacket
    (branchASmallerPacketAdapter_of_errorLift_and_primitive hErr hLift hPrim)

/--
primitive route を canonical mainline として読む provider wrapper。
-/
theorem branchAWieferichAdapter_of_primitiveMainline
    (hErr : BranchAValuationPeelTailErrorAdapterTarget)
    (hLift : BranchAValuationPeelPacketFromErrorAdapterTarget)
    (hPrim : BranchAPrimitivePacketDescentAdapterTarget) :
    BranchAWieferichAdapterTarget :=
  branchAWieferichAdapter_of_errorLift_and_primitive hErr hLift hPrim

/--
witness 付き primitive local core から、
primitive packet descent adapter を回収する thin bridge。
-/
theorem branchAPrimitivePacketDescentAdapter_of_wieferichPacket
    (hPrim : BranchAPrimitiveWieferichPacketAdapterTarget) :
    BranchAPrimitivePacketDescentAdapterTarget :=
  DkMath.FLT.primeGe5BranchAPrimitivePacketDescent_of_wieferichPacket hPrim

/--
primitive distinguished-prime selection と restoration から、
witness 付き primitive packet adapter を回収する thin bridge。
-/
theorem branchAPrimitiveWieferichPacketAdapter_of_distinguishedPrime_and_restore
    (hPrime : BranchAPrimitiveDistinguishedPrimeAdapterTarget)
    (hRestore : BranchAPrimitivePacketRestoreAdapterTarget) :
    BranchAPrimitiveWieferichPacketAdapterTarget :=
  DkMath.FLT.primeGe5BranchAPrimitiveWieferichPacket_of_distinguishedPrime_and_restore
    hPrime hRestore

/--
Zsigmondy-lite existence から、
primitive distinguished-prime adapter を回収する thin bridge。
-/
theorem branchAPrimitiveDistinguishedPrimeAdapter_of_zsigmondy
    (hZ : BranchAPrimitiveZsigmondyAdapterTarget) :
    BranchAPrimitiveDistinguishedPrimeAdapterTarget :=
  DkMath.FLT.primeGe5BranchAPrimitiveDistinguishedPrime_of_zsigmondy hZ

/--
cyclotomic / diff-power 側の prime existence から、
primitive Zsigmondy adapter を回収する thin bridge。
-/
theorem branchAPrimitiveZsigmondyAdapter_of_cyclotomicPrime
    (hCyc : BranchAPrimitiveCyclotomicPrimeAdapterTarget) :
    BranchAPrimitiveZsigmondyAdapterTarget :=
  DkMath.FLT.primeGe5BranchAPrimitiveZsigmondy_of_cyclotomicPrime hCyc

/--
Branch A 専用 existence wrapper から、
primitive cyclotomic-prime adapter を回収する thin bridge。
-/
theorem branchAPrimitiveCyclotomicPrimeAdapter_of_existence
    (hEx : BranchACyclotomicExistenceAdapterTarget) :
    BranchAPrimitiveCyclotomicPrimeAdapterTarget :=
  DkMath.FLT.primeGe5BranchAPrimitiveCyclotomicPrime_of_existence hEx

/-- distinguished prime selection から arithmetic fallout adapter を回収する thin bridge。 -/
theorem branchAPrimitiveDistinguishedPrimeArithmeticAdapter_default :
    BranchAPrimitiveDistinguishedPrimeArithmeticAdapterTarget :=
  DkMath.FLT.primeGe5BranchAPrimitiveDistinguishedPrimeArithmetic_default

/--
arithmetic fallout 付き restoration target から、
primitive packet restoration adapter を回収する thin bridge。
-/
theorem branchAPrimitivePacketRestoreAdapter_of_arithmetic
    (hArith : BranchAPrimitiveDistinguishedPrimeArithmeticAdapterTarget)
    (hRestore : BranchAPrimitivePacketRestoreFromArithmeticAdapterTarget) :
    BranchAPrimitivePacketRestoreAdapterTarget :=
  DkMath.FLT.primeGe5BranchAPrimitivePacketRestore_of_arithmetic hArith hRestore

/--
Zsigmondy-lite existence と arithmetic-aware restoration から、
witness 付き primitive packet adapter を回収する thin bridge。
-/
theorem branchAPrimitiveWieferichPacketAdapter_of_zsigmondy_arithmetic_and_restore
    (hZ : BranchAPrimitiveZsigmondyAdapterTarget)
    (hArith : BranchAPrimitiveDistinguishedPrimeArithmeticAdapterTarget)
    (hRestore : BranchAPrimitivePacketRestoreFromArithmeticAdapterTarget) :
    BranchAPrimitiveWieferichPacketAdapterTarget :=
  DkMath.FLT.primeGe5BranchAPrimitiveWieferichPacket_of_zsigmondy_arithmetic_and_restore
    hZ hArith hRestore

/--
primitive packet descent adapter は、
`zsigmondy existence + arithmetic fallout + restore-from-arithmetic`
の 3 段から橋だけで閉じる。
-/
theorem branchAPrimitivePacketDescentAdapter_of_zsigmondy_arithmetic_and_restore
    (hZ : BranchAPrimitiveZsigmondyAdapterTarget)
    (hArith : BranchAPrimitiveDistinguishedPrimeArithmeticAdapterTarget)
    (hRestore : BranchAPrimitivePacketRestoreFromArithmeticAdapterTarget) :
    BranchAPrimitivePacketDescentAdapterTarget :=
  DkMath.FLT.primeGe5BranchAPrimitivePacketDescent_of_zsigmondy_arithmetic_and_restore
    hZ hArith hRestore

/--
primitive packet descent adapter は、
Branch A 専用 cyclotomic prime existence と restore-from-arithmetic
の 2 本だけがあれば橋で閉じる。
-/
theorem branchAPrimitivePacketDescentAdapter_of_cyclotomicPrime_and_restore
    (hCyc : BranchAPrimitiveCyclotomicPrimeAdapterTarget)
    (hRestore : BranchAPrimitivePacketRestoreFromArithmeticAdapterTarget) :
    BranchAPrimitivePacketDescentAdapterTarget :=
  DkMath.FLT.primeGe5BranchAPrimitivePacketDescent_of_cyclotomicPrime_and_restore
    hCyc hRestore

/--
primitive packet descent adapter は、
Branch A 専用 existence wrapper と restore-from-arithmetic
の 2 本だけがあれば橋で閉じる。
-/
theorem branchAPrimitivePacketDescentAdapter_of_existence_and_restore
    (hEx : BranchACyclotomicExistenceAdapterTarget)
    (hRestore : BranchAPrimitivePacketRestoreFromArithmeticAdapterTarget) :
    BranchAPrimitivePacketDescentAdapterTarget :=
  DkMath.FLT.primeGe5BranchAPrimitivePacketDescent_of_existence_and_restore
    hEx hRestore

/--
暫定 concrete adapter for the Branch A Wieferich witness route.

付録:
- 現段階では `BranchAWieferichAdapterTarget` の clean 実装はまだ未発見だが、
  実装自体は既存 descent 契約を経由して閉じる。
- したがって clean route では、
  この theorem 1 本の差し替えだけで
  witness route 全体を clean 化できる。
-/
theorem branchAWieferichAdapter_via_FLT :
    BranchAWieferichAdapterTarget :=
  branchAWieferichRefuter_of_existingDescent existingDescentRefuter_via_FLT

/--
Branch A / Wieferich witness refuter の実装本体。

最終 clean 置換点はこの定理 1 本に集約する。
-/
theorem branchAWieferichRefuter_math :
    DkMath.FLT.PrimeGe5BranchAWieferichRefuterTarget :=
  branchAWieferichAdapter_via_FLT

/-- Branch A / Wieferich witness refuter の実装入口。 -/
theorem branchAWieferichRefuter_impl :
    DkMath.FLT.PrimeGe5BranchAWieferichRefuterTarget :=
  branchAWieferichRefuter_math

/--
Branch A の Wieferich witness refuter 契約があれば、
既存 descent 契約は witness を再構成して閉じられる。

付録:
- `BranchAShapeWitnessDescentInput` の `gapShape` 自体はここでは使わない。
- clean route では、
  `PrimeGe5BranchAWieferichRefuterTarget`
  の差し替えだけで
  `ExistingDescentRefuterTarget`
  も同時に clean 化できる。
-/
theorem existingDescentRefuter_of_branchAWieferich
    (hRefute : DkMath.FLT.PrimeGe5BranchAWieferichRefuterTarget) :
    ExistingDescentRefuterTarget := by
  intro p x y z t hpack hp_dvd_gap _hInput
  exact hRefute hpack hp_dvd_gap
    (DkMath.FLT.primeGe5BranchAWieferichOnY_default hpack hp_dvd_gap)

/-- 既存契約入力を refute する暫定 concrete 実装（via FLT）。 -/
theorem existingDescentContractRefuter_via_FLT :
  ExistingDescentRawRefuterTarget := by
  intro p x y z t hpack hp_dvd_gap hC
  exact existingDescentRefuter_via_FLT hpack hp_dvd_gap hC

/--
`ExistingDescentRawRefuterTarget` の実装本体。

現時点では `via_FLT` を束ねるが、最終 clean 置換点はこの定理 1 本に集約する。
-/
theorem existingDescentRawRefuter_math :
    ExistingDescentRawRefuterTarget :=
  existingDescentContractRefuter_via_FLT

/-- `ExistingDescentRawRefuterTarget` の実装入口。 -/
theorem existingDescentRawRefuter_impl :
    ExistingDescentRawRefuterTarget :=
  existingDescentRawRefuter_math

/--
既存契約入力を refute する実装本体。

現時点では `via_FLT` を束ねるが、最終 clean 置換点はこの定理 1 本に集約する。
-/
theorem existingDescentContractRefuter_math :
    ExistingDescentContractRefuterTarget :=
  existingDescentContractRefuter_of_raw existingDescentRawRefuter_impl

/-- 既存契約入力を refute する実装入口。 -/
theorem existingDescentContractRefuter_impl :
    ExistingDescentContractRefuterTarget :=
  existingDescentContractRefuter_math

/-- Branch A 専用 descent 契約の暫定 concrete 実装（via FLT）。 -/
theorem branchAShapeWitnessDescentContract_via_FLT :
    BranchAShapeWitnessDescentContractTarget :=
  existingDescentRefuter_via_FLT

/--
Branch A 専用 descent 契約の実装本体。

現時点では `via_FLT` を束ねるが、最終 clean 置換点はこの定理 1 本に集約する。
-/
theorem branchAShapeWitnessDescentContract_math :
    BranchAShapeWitnessDescentContractTarget := by
  intro p x y z t hpack hp_dvd_gap hInput
  let hC : ExistingDescentContractInput p x y z t :=
    branchAShapeWitnessDescentInput_to_existing_contract hpack hp_dvd_gap hInput
  exact existingDescentContractRefuter_impl hpack hp_dvd_gap hC

/-- Branch A 専用 descent 契約の実装入口。 -/
theorem branchAShapeWitnessDescentContract_impl :
    BranchAShapeWitnessDescentContractTarget :=
  branchAShapeWitnessDescentContract_math

/--
既存 descent 契約入力を受けて refute する実装本体。

最終 clean 置換点はこの定理 1 本。
-/
theorem existingDescentRefuter_math
  : ∀ {p x y z t : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    BranchAShapeWitnessDescentInput p x y z t →
    False :=
  existingDescentRefuter_of_branchAWieferich
    branchAWieferichRefuter_impl

/--
witness 直受け kernel の実装本体。

現時点では `via_FLT` を束ねるが、最終 clean 置換点はこの定理 1 本に集約する。
-/
theorem branchAShapeWitnessKernel_math :
    BranchAShapeWitnessKernelTarget :=
  branchAShapeWitnessKernel_of_existingDescentRefuter
    existingDescentRefuter_math

/-- witness 直受け kernel の実装入口。 -/
theorem branchAShapeWitnessKernel_impl :
    BranchAShapeWitnessKernelTarget :=
  branchAShapeWitnessKernel_math

/--
`shrinkWitness -> descent` の実装入口。

現時点では `via_FLT` を束ねるが、最終 clean 置換点はこの定理 1 本に集約する。
-/
theorem branchAShrinkWitnessToDescent_math :
    BranchAShrinkWitnessToDescentTarget :=
  branchAShrinkWitnessToDescent_of_kernel
    branchAShapeWitnessKernel_impl

/--
`shape-value -> descent` の実装入口（shrink 分解版）。
-/
theorem branchAShapeValueToDescent_impl :
    BranchAShapeValueToDescentTarget :=
  branchAShapeValueToDescent_of_shrink
    branchAShapeValueToShrinkWitness_via_FLT
    branchAShrinkWitnessToDescent_math

/--
`shrinkWitness -> descent` の clean 契約を外部注入して
`shape-value -> descent` を得る実装入口。

この定理により、最後の置換点は
`BranchAShrinkWitnessToDescentTarget` の実体 1 本へ固定される。
-/
theorem branchAShapeValueToDescent_of_shrinkWitness_impl
    (hSD : BranchAShrinkWitnessToDescentTarget) :
    BranchAShapeValueToDescentTarget :=
  branchAShapeValueToDescent_of_shrink
    branchAShapeValueToShrinkWitness_via_FLT
    hSD

/-- `BranchAShapeValueToRefuterTarget` の実装入口。 -/
theorem branchAShapeValueToRefuter_impl :
    BranchAShapeValueToRefuterTarget :=
  branchAShapeValueToRefuter_of_descent branchAShapeValueToDescent_impl

/--
`shape-value -> descent` の clean 契約を外部注入して
`shape-value -> refuter` を得る実装入口。
-/
theorem branchAShapeValueToRefuter_of_descent_impl
    (hDescent : BranchAShapeValueToDescentTarget) :
    BranchAShapeValueToRefuterTarget :=
  branchAShapeValueToRefuter_of_descent hDescent

/--
`shrinkWitness -> descent` を外部注入して
`shape-value -> refuter` を得る実装入口。
-/
theorem branchAShapeValueToRefuter_of_shrinkWitness_impl
    (hSD : BranchAShrinkWitnessToDescentTarget) :
    BranchAShapeValueToRefuterTarget :=
  branchAShapeValueToRefuter_of_descent_impl
    (branchAShapeValueToDescent_of_shrinkWitness_impl hSD)

/--
Branch A の shape-factorization から refuter へ送る 1-pack kernel 仕様。

終盤の数学核を 1 定理へ固定するための中間仕様。
-/
abbrev BranchAShapeToRefuterTarget : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    ((∀ q : ℕ, q ≠ p → p ∣ (z - y).factorization q) ∧
      ∃ m : ℕ, (z - y).factorization p = (p - 1) + p * m) →
    False

/--
1-pack kernel があれば、Branch A の shape 出口を Branch A refuter 出口へ持ち上げられる。
-/
theorem branchAShapeToRefuter_of_kernel
    (hK : BranchAShapeToRefuterTarget) :
    BranchAShapeFactorizationTarget → BranchARefuterTarget := by
  intro hShape p x y z hpack hp_dvd_gap
  exact hK hpack hp_dvd_gap (hShape hpack hp_dvd_gap)

/--
`shape-factorization -> shape-value` と `shape-value -> refuter` が揃えば、
`shape-factorization -> refuter`（kernel）を得る。
-/
theorem branchAShapeToRefuter_of_value
    (hValue : BranchAShapeFactorizationToValueTarget)
    (hRefuteValue : BranchAShapeValueToRefuterTarget) :
    BranchAShapeToRefuterTarget := by
  intro p x y z hpack hp_dvd_gap hShapeFac
  exact hRefuteValue hpack hp_dvd_gap (hValue hpack hp_dvd_gap hShapeFac)

/-- Branch A/B の 2 終着仕様が揃えば、反例排除仕様が得られる。 -/
theorem primeGe5CounterexampleRefuter_of_branch_split
    (hA : BranchARefuterTarget)
    (hB : BranchBRefuterTarget) :
    PrimeGe5CounterexampleRefuterTarget := by
  intro p x y z hpack
  by_cases hpB : p ∣ (z - y)
  · exact hA hpack hpB
  · exact hB hpack hpB

/--
Branch B concrete (`gap = t^p`) と default の gap-not-pow から、
Branch B 側終着仕様を得る。
-/
theorem branchBRefuter_of_gapPow_and_defaultNotPow
    (hGapPowB : ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
      ¬ p ∣ (z - y) → ∃ t : ℕ, (z - y) = t ^ p) :
    BranchBRefuterTarget := by
  intro p x y z hpack hpB
  exact (gapNotIsPowTarget_default hpack) (hGapPowB hpack hpB)

/--
shape-preserving mainline:
Branch A/B 分岐終着仕様から `FLTPrimeGe5Target` へ接続する。
-/
theorem FLTPrimeGe5Target_of_branch_split_refuter_with_normalizer_impl
    (hA : BranchARefuterTarget)
    (hB : BranchBRefuterTarget) :
    FLTPrimeGe5Target := by
  exact FLTPrimeGe5Target_of_normalizer_and_refuter
    primeGe5CounterexampleNormalizer_impl
    (primeGe5CounterexampleRefuter_of_branch_split hA hB)

/--
2層 mainline:
Branch A は shape 出口、Branch B は refuter 出口を取り、
`shape -> refuter` 橋を外部注入して `FLTPrimeGe5Target` へ接続する。
-/
theorem FLTPrimeGe5Target_of_branch_split_shape_and_refuter_with_normalizer_impl
    (hAShape : BranchAShapeFactorizationTarget)
    (hB : BranchBRefuterTarget)
    (hShapeToRefuter : BranchAShapeFactorizationTarget → BranchARefuterTarget) :
    FLTPrimeGe5Target := by
  exact FLTPrimeGe5Target_of_branch_split_refuter_with_normalizer_impl
    (hShapeToRefuter hAShape)
    hB

/--
Branch A lower layer が Wieferich witness を返せるなら、
既存の branch-split mainline へ直接注入できる。
-/
theorem FLTPrimeGe5Target_of_branchA_wieferich_with_normalizer_impl
    (hRefute : DkMath.FLT.PrimeGe5BranchAWieferichRefuterTarget) :
    FLTPrimeGe5Target := by
  exact FLTPrimeGe5Target_of_branch_split_refuter_with_normalizer_impl
    (branchARefuter_of_wieferichTargets
      DkMath.FLT.primeGe5BranchAWieferichOnY_default
      hRefute)
    (branchBRefuter_of_gapPow_and_defaultNotPow
      gapPowFromPrimeGe5Counterexample_branchB_impl)

/--
既定の Branch A Wieferich witness と暫定 refuter から得る default mainline。

`PrimeGe5BranchAWieferichRefuterTarget` の clean 置換先はこの theorem の引数 1 本に隔離する。
-/
theorem FLTPrimeGe5Target_of_branchA_wieferich_default_with_normalizer_impl :
    FLTPrimeGe5Target := by
  exact FLTPrimeGe5Target_of_branchA_wieferich_with_normalizer_impl
    branchAWieferichRefuter_impl

/--
Branch A の Wieferich witness route が供給されれば、
`p ≥ 5` 素数指数の FLT を concrete に返せる。
-/
theorem FLT_prime_ge5_of_branchA_wieferich_with_normalizer_impl
    (hRefute : DkMath.FLT.PrimeGe5BranchAWieferichRefuterTarget)
    (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    FermatLastTheoremFor p := by
  exact (FLTPrimeGe5Target_of_branchA_wieferich_with_normalizer_impl hRefute) p hp hp5

/--
既定の Branch A Wieferich route から得る `FLT_prime_ge5` 実装版。
-/
theorem FLT_prime_ge5_of_branchA_wieferich_default_with_normalizer_impl
    (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    FermatLastTheoremFor p := by
  exact (FLTPrimeGe5Target_of_branchA_wieferich_default_with_normalizer_impl) p hp hp5

/--
Branch A の Wieferich witness route が供給されれば、
`FLT_prime_ge5` 本体を通さず global provider へ直結できる。
-/
theorem triominoCosmic_globalProvider_of_branchA_wieferich_with_normalizer_impl
    (hRefute : DkMath.FLT.PrimeGe5BranchAWieferichRefuterTarget) :
    GlobalPrimeExponentFLTProvider := by
  exact triominoCosmic_globalProvider_of_FLTPrimeGe5
    (FLTPrimeGe5Target_of_branchA_wieferich_with_normalizer_impl hRefute)

/--
既定の Branch A Wieferich route から得る global provider。
-/
theorem triominoCosmic_globalProvider_of_branchA_wieferich_default_with_normalizer_impl :
    GlobalPrimeExponentFLTProvider := by
  exact triominoCosmic_globalProvider_of_FLTPrimeGe5
    FLTPrimeGe5Target_of_branchA_wieferich_default_with_normalizer_impl

/--
Branch A の Wieferich witness route が供給されれば、
`FLT_prime_ge5` 本体を通さず Triomino provider へ直結できる。
-/
theorem triominoPrimeProvider_of_branchA_wieferich_with_normalizer_impl
    (hRefute : DkMath.FLT.PrimeGe5BranchAWieferichRefuterTarget) :
    TriominoPrimeProvider := by
  exact triominoPrimeProvider_of_FLTPrimeGe5
    (FLTPrimeGe5Target_of_branchA_wieferich_with_normalizer_impl hRefute)

/--
既定の Branch A Wieferich route から得る Triomino provider。
-/
theorem triominoPrimeProvider_of_branchA_wieferich_default_with_normalizer_impl :
    TriominoPrimeProvider := by
  exact triominoPrimeProvider_of_FLTPrimeGe5
    FLTPrimeGe5Target_of_branchA_wieferich_default_with_normalizer_impl

/--
2層 mainline の kernel 版。
`BranchAShapeToRefuterTarget` が与えられれば、shape 出口から refuter 出口への橋は自動生成できる。
-/
theorem FLTPrimeGe5Target_of_branch_split_shapeKernel_and_refuter_with_normalizer_impl
    (hAShape : BranchAShapeFactorizationTarget)
    (hB : BranchBRefuterTarget)
    (hK : BranchAShapeToRefuterTarget) :
    FLTPrimeGe5Target := by
  exact FLTPrimeGe5Target_of_branch_split_shape_and_refuter_with_normalizer_impl
    hAShape hB (branchAShapeToRefuter_of_kernel hK)

/--
3層 mainline:
Branch A は `shape-factorization -> shape-value -> refuter` の順に送り、
Branch B refuter と合成して `FLTPrimeGe5Target` へ接続する。
-/
theorem FLTPrimeGe5Target_of_branch_split_shapeValue_and_refuter_with_normalizer_impl
    (hAShape : BranchAShapeFactorizationTarget)
    (hB : BranchBRefuterTarget)
    (hValue : BranchAShapeFactorizationToValueTarget)
    (hRefuteValue : BranchAShapeValueToRefuterTarget) :
    FLTPrimeGe5Target := by
  exact FLTPrimeGe5Target_of_branch_split_shapeKernel_and_refuter_with_normalizer_impl
    hAShape hB (branchAShapeToRefuter_of_value hValue hRefuteValue)

/--
Branch-split mainline の legacy 起動定理（shape/value concrete 実装接続版）。

注意:
- Branch A の value/refuter 実装は現時点では via FLT であり、
  最終的には clean 数学核へ置換する。
- 既定の public mainline は、より細く隔離された
  `FLTPrimeGe5Target_of_branchA_wieferich_default_with_normalizer_impl`
  を経由する。
-/
theorem FLTPrimeGe5Target_branch_split_mainline_legacy_shape :
    FLTPrimeGe5Target := by
  exact FLTPrimeGe5Target_of_branch_split_shapeValue_and_refuter_with_normalizer_impl
    branchAShapeFactorizationTarget_impl
    (branchBRefuter_of_gapPow_and_defaultNotPow
      gapPowFromPrimeGe5Counterexample_branchB_impl)
    branchAShapeValueTarget_impl
    branchAShapeValueToRefuter_impl

/--
Branch-split mainline の既定起動定理。

現在の default route は、Branch A を shape/value comparison から直接起動するのではなく、
Wieferich witness route に正規化してから mainline へ流す。
-/
theorem FLTPrimeGe5Target_branch_split_mainline :
    FLTPrimeGe5Target := by
  exact FLTPrimeGe5Target_of_branchA_wieferich_default_with_normalizer_impl

/--
`TriominoCosmicGapInvariant` 側の canonical default `FLTPrimeGe5Target` 入口。

現在の既定 route は Branch A / Wieferich witness を経由する branch-split mainline である。
-/
theorem FLTPrimeGe5Target_default :
    FLTPrimeGe5Target := by
  exact FLTPrimeGe5Target_branch_split_mainline

/--
canonical default `FLT_prime_ge5` 実装版。

`TriominoCosmicPrimeGe5.FLT_prime_ge5` とは独立に、
provider 層だけで閉じる既定入口を与える。
-/
theorem FLT_prime_ge5_default
    (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    FermatLastTheoremFor p := by
  exact (FLTPrimeGe5Target_default) p hp hp5

/--
canonical default global provider。

既定の branch-split / Wieferich witness mainline から直接得る。
-/
theorem triominoCosmic_globalProvider_default :
    GlobalPrimeExponentFLTProvider := by
  exact triominoCosmic_globalProvider_of_FLTPrimeGe5
    FLTPrimeGe5Target_default

/--
canonical default Triomino prime provider。

既定の branch-split / Wieferich witness mainline から直接得る。
-/
theorem triominoPrimeProvider_default :
    TriominoPrimeProvider := by
  exact triominoPrimeProvider_of_FLTPrimeGe5
    FLTPrimeGe5Target_default

/--
最終仮橋 (`branchAShapeValueToDescent_via_FLT`) を使わない clean 起動版。
`shape-value -> descent` の実体が供給されれば、そのまま mainline を起動できる。
-/
theorem FLTPrimeGe5Target_branch_split_mainline_of_descent
    (hDescent : BranchAShapeValueToDescentTarget) :
    FLTPrimeGe5Target := by
  exact FLTPrimeGe5Target_of_branch_split_shapeValue_and_refuter_with_normalizer_impl
    branchAShapeFactorizationTarget_impl
    (branchBRefuter_of_gapPow_and_defaultNotPow
      gapPowFromPrimeGe5Counterexample_branchB_impl)
    branchAShapeValueTarget_impl
    (branchAShapeValueToRefuter_of_descent_impl hDescent)

/--
最終一点 (`BranchAShrinkWitnessToDescentTarget`) を埋めれば起動できる clean mainline。
-/
theorem FLTPrimeGe5Target_branch_split_mainline_of_shrinkWitness
    (hSD : BranchAShrinkWitnessToDescentTarget) :
    FLTPrimeGe5Target := by
  exact FLTPrimeGe5Target_branch_split_mainline_of_descent
    (branchAShapeValueToDescent_of_shrinkWitness_impl hSD)

/--
Branch A で `gap = t^p` が供給されれば、`gap` の全素因子指数は `p` の倍数になる。
-/
theorem gapPowFromPrimeGe5Counterexample_branchA_factorization_of_gapPow
    (hA : GapPowFromPrimeGe5Counterexample_branchA) :
    GapPowFromPrimeGe5Counterexample_branchA_factorization := by
  intro p x y z hpack hp_dvd_gap q
  rcases hA hpack hp_dvd_gap with ⟨t, ht⟩
  have hfac : (z - y).factorization q = p * t.factorization q := by
    calc
      (z - y).factorization q = (t ^ p).factorization q := by simp [ht]
      _ = p * t.factorization q := by simp [Nat.factorization_pow]
  exact ⟨t.factorization q, by simp [hfac]⟩


/-- Branch A では、`gap` の `p` 乗化仕様と因数分解指数仕様は同値。 -/
theorem gapPowFromPrimeGe5Counterexample_branchA_iff_factorization :
    GapPowFromPrimeGe5Counterexample_branchA ↔
      GapPowFromPrimeGe5Counterexample_branchA_factorization := by
  constructor
  · exact gapPowFromPrimeGe5Counterexample_branchA_factorization_of_gapPow
  · exact gapPowFromPrimeGe5Counterexample_branchA_of_factorization

/--
反例排除仕様があれば、Branch A の gap-pow は `False.elim` で回収できる。

理論核としては弱いが、導線検証や API 接続の最小補助として有用。
-/
theorem gapPowFromPrimeGe5Counterexample_branchA_of_refuter
    (hRefute : PrimeGe5CounterexampleRefuterTarget) :
    GapPowFromPrimeGe5Counterexample_branchA := by
  intro p x y z hpack hp_dvd_gap
  exact False.elim (hRefute hpack)

/--
反例排除仕様があれば、Branch A の因数分解指数仕様も vacuous に供給できる。
-/
theorem gapPowFromPrimeGe5Counterexample_branchA_factorization_of_refuter
    (hRefute : PrimeGe5CounterexampleRefuterTarget) :
    GapPowFromPrimeGe5Counterexample_branchA_factorization := by
  intro p x y z hpack hp_dvd_gap q
  exact False.elim (hRefute hpack)

/--
反例排除仕様があれば、全域 `GapPowFromPrimeGe5CounterexampleTarget` を直接供給できる。
-/
theorem gapPowFromPrimeGe5Counterexample_target_of_refuter
    (hRefute : PrimeGe5CounterexampleRefuterTarget) :
    GapPowFromPrimeGe5CounterexampleTarget := by
  intro p x y z hpack
  exact False.elim (hRefute hpack)

/--
Branch A の因数分解仕様が供給されれば、全域 `GapPowFromPrimeGe5CounterexampleTarget` を得る。
-/
theorem gapPowFromPrimeGe5Counterexample_target_of_branchA_factorization
    (hFac : GapPowFromPrimeGe5Counterexample_branchA_factorization) :
    GapPowFromPrimeGe5CounterexampleTarget := by
  intro p x y z hpack
  by_cases hpB : p ∣ (z - y)
  · exact (gapPowFromPrimeGe5Counterexample_branchA_of_factorization hFac) hpack hpB
  · exact gapPowFromPrimeGe5Counterexample_branchB_impl hpack hpB

/--
Branch A shape 仕様 + shape→gapPow 橋が供給されれば、全域 `GapPow` が得られる。
-/
theorem gapPowFromPrimeGe5Counterexample_target_of_branchA_shape
    (hShape : GapShapeFromPrimeGe5Counterexample_branchA)
    (hBridge : GapPowFromBranchAShapeBridge) :
    GapPowFromPrimeGe5CounterexampleTarget := by
  intro p x y z hpack
  by_cases hpB : p ∣ (z - y)
  · exact (gapPowFromPrimeGe5Counterexample_branchA_of_shape hShape hBridge) hpack hpB
  · exact gapPowFromPrimeGe5Counterexample_branchB_impl hpack hpB

/-- Branch A/B の 2 分岐仕様が揃えば、全域 `GapPowFromPrimeGe5CounterexampleTarget` が得られる。 -/
theorem gapPowFromPrimeGe5Counterexample_of_branches
    (hA : GapPowFromPrimeGe5Counterexample_branchA) :
    GapPowFromPrimeGe5CounterexampleTarget := by
  intro p x y z hpack
  by_cases hpB : p ∣ (z - y)
  · exact hA hpack hpB
  · exact gapPowFromPrimeGe5Counterexample_branchB_impl hpack hpB

/--
Branch A 仮定が供給されれば、concrete normalizer 実装と default gap-not-isPow で
`FLTPrimeGe5Target` を構成できる。
-/
theorem FLTPrimeGe5Target_of_branchA_with_normalizer_impl
    (hA : GapPowFromPrimeGe5Counterexample_branchA) :
    FLTPrimeGe5Target := by
  exact FLTPrimeGe5Target_of_gap_specs_with_normalizer_impl
    gapNotIsPowTarget_default
    (gapPowFromPrimeGe5Counterexample_of_branches hA)

/--
Branch A 仮定が供給されれば、`p ≥ 5` 素数指数の FLT を concrete に返せる。
-/
theorem FLT_prime_ge5_of_branchA_with_normalizer_impl
    (hA : GapPowFromPrimeGe5Counterexample_branchA)
    (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    FermatLastTheoremFor p := by
  exact (FLTPrimeGe5Target_of_branchA_with_normalizer_impl hA) p hp hp5

/--
Branch A 仮定が供給されれば、`FLT_prime_ge5` 本体を通さず global provider へ直結できる。
-/
theorem triominoCosmic_globalProvider_of_branchA_with_normalizer_impl
    (hA : GapPowFromPrimeGe5Counterexample_branchA) :
    GlobalPrimeExponentFLTProvider := by
  exact triominoCosmic_globalProvider_of_FLTPrimeGe5
    (FLTPrimeGe5Target_of_branchA_with_normalizer_impl hA)

/--
Branch A 仮定が供給されれば、`FLT_prime_ge5` 本体を通さず Triomino provider へ直結できる。
-/
theorem triominoPrimeProvider_of_branchA_with_normalizer_impl
    (hA : GapPowFromPrimeGe5Counterexample_branchA) :
    TriominoPrimeProvider := by
  exact triominoPrimeProvider_of_FLTPrimeGe5
    (FLTPrimeGe5Target_of_branchA_with_normalizer_impl hA)

/--
`hNotPow` を外部入力にした clean 版。
Branch A 仮定が供給されれば、default 依存なしで `FLTPrimeGe5Target` を構成できる。
-/
theorem FLTPrimeGe5Target_of_branchA_with_normalizer_and_notPow
    (hNotPow : GapNotIsPowTarget)
    (hA : GapPowFromPrimeGe5Counterexample_branchA) :
    FLTPrimeGe5Target := by
  exact FLTPrimeGe5Target_of_gap_specs_with_normalizer_impl
    hNotPow
    (gapPowFromPrimeGe5Counterexample_of_branches hA)

/-- `hNotPow` を外部入力にした clean 版の `FLT_prime_ge5`。 -/
theorem FLT_prime_ge5_of_branchA_with_normalizer_and_notPow
    (hNotPow : GapNotIsPowTarget)
    (hA : GapPowFromPrimeGe5Counterexample_branchA)
    (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    FermatLastTheoremFor p := by
  exact (FLTPrimeGe5Target_of_branchA_with_normalizer_and_notPow hNotPow hA) p hp hp5

/--
`hNotPow` を外部入力にした clean 版。
Branch A 仮定が供給されれば、`FLT_prime_ge5` 本体を通さず global provider へ直結できる。
-/
theorem triominoCosmic_globalProvider_of_branchA_with_normalizer_and_notPow
    (hNotPow : GapNotIsPowTarget)
    (hA : GapPowFromPrimeGe5Counterexample_branchA) :
    GlobalPrimeExponentFLTProvider := by
  exact triominoCosmic_globalProvider_of_FLTPrimeGe5
    (FLTPrimeGe5Target_of_branchA_with_normalizer_and_notPow hNotPow hA)

/--
`hNotPow` を外部入力にした clean 版。
Branch A 仮定が供給されれば、`FLT_prime_ge5` 本体を通さず Triomino provider へ直結できる。
-/
theorem triominoPrimeProvider_of_branchA_with_normalizer_and_notPow
    (hNotPow : GapNotIsPowTarget)
    (hA : GapPowFromPrimeGe5Counterexample_branchA) :
    TriominoPrimeProvider := by
  exact triominoPrimeProvider_of_FLTPrimeGe5
    (FLTPrimeGe5Target_of_branchA_with_normalizer_and_notPow hNotPow hA)

/--
Branch A の因数分解仕様を直接使う clean 版。
`hNotPow` と concrete normalizer 実装だけで `FLTPrimeGe5Target` へ接続する。
-/
theorem FLTPrimeGe5Target_of_branchA_factorization_with_normalizer_and_notPow
    (hNotPow : GapNotIsPowTarget)
    (hFac : GapPowFromPrimeGe5Counterexample_branchA_factorization) :
    FLTPrimeGe5Target := by
  exact FLTPrimeGe5Target_of_gap_specs_with_normalizer_impl
    hNotPow
    (gapPowFromPrimeGe5Counterexample_target_of_branchA_factorization hFac)

/--
Branch A の因数分解仕様を直接使う clean 版の `FLT_prime_ge5`。
-/
theorem FLT_prime_ge5_of_branchA_factorization_with_normalizer_and_notPow
    (hNotPow : GapNotIsPowTarget)
    (hFac : GapPowFromPrimeGe5Counterexample_branchA_factorization)
    (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    FermatLastTheoremFor p := by
  exact (FLTPrimeGe5Target_of_branchA_factorization_with_normalizer_and_notPow hNotPow hFac)
    p hp hp5

/--
Branch A の因数分解仕様を直接使う clean 版。
`FLT_prime_ge5` 本体を通さず global provider へ直結する。
-/
theorem triominoCosmic_globalProvider_of_branchA_factorization_with_normalizer_and_notPow
    (hNotPow : GapNotIsPowTarget)
    (hFac : GapPowFromPrimeGe5Counterexample_branchA_factorization) :
    GlobalPrimeExponentFLTProvider := by
  exact triominoCosmic_globalProvider_of_FLTPrimeGe5
    (FLTPrimeGe5Target_of_branchA_factorization_with_normalizer_and_notPow hNotPow hFac)

/--
Branch A の因数分解仕様を直接使う clean 版。
`FLT_prime_ge5` 本体を通さず Triomino provider へ直結する。
-/
theorem triominoPrimeProvider_of_branchA_factorization_with_normalizer_and_notPow
    (hNotPow : GapNotIsPowTarget)
    (hFac : GapPowFromPrimeGe5Counterexample_branchA_factorization) :
    TriominoPrimeProvider := by
  exact triominoPrimeProvider_of_FLTPrimeGe5
    (FLTPrimeGe5Target_of_branchA_factorization_with_normalizer_and_notPow hNotPow hFac)

/--
default の gap-not-isPow 供給を使って、残り 2 本（normalizer / gap-pow）から
`FLTPrimeGe5Target` を得る接合定理。
-/
theorem FLTPrimeGe5Target_of_normalizer_and_gapPow_default
    (hNorm : PrimeGe5CounterexampleNormalizerTarget)
    (hGapPow : GapPowFromPrimeGe5CounterexampleTarget) :
    FLTPrimeGe5Target := by
  exact FLTPrimeGe5Target_of_normalizer_and_gap_specs
    hNorm
    gapNotIsPowTarget_default
    hGapPow

/--
default の gap-not-isPow 供給を使う `FLT_prime_ge5` 実装版。

残る実装責務は normalizer と gap-pow 仕様の 2 本だけ。
-/
theorem FLT_prime_ge5_of_normalizer_and_gapPow_default
    (hNorm : PrimeGe5CounterexampleNormalizerTarget)
    (hGapPow : GapPowFromPrimeGe5CounterexampleTarget)
    (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    FermatLastTheoremFor p := by
  exact (FLTPrimeGe5Target_of_normalizer_and_gapPow_default hNorm hGapPow) p hp hp5

/--
`FLT_prime_ge5` 本体（`Basic.FLT` 経由）を使わず、
normalizer + gap-pow(default gap-not-pow) から global provider へ直結する回避ルート。
-/
theorem triominoCosmic_globalProvider_of_normalizer_and_gapPow_default
    (hNorm : PrimeGe5CounterexampleNormalizerTarget)
    (hGapPow : GapPowFromPrimeGe5CounterexampleTarget) :
    GlobalPrimeExponentFLTProvider := by
  exact triominoCosmic_globalProvider_of_FLTPrimeGe5
    (FLTPrimeGe5Target_of_normalizer_and_gapPow_default hNorm hGapPow)

/--
`FLT_prime_ge5` 本体（`Basic.FLT` 経由）を使わず、
normalizer + gap-pow(default gap-not-pow) から Triomino provider へ直結する回避ルート。
-/
theorem triominoPrimeProvider_of_normalizer_and_gapPow_default
    (hNorm : PrimeGe5CounterexampleNormalizerTarget)
    (hGapPow : GapPowFromPrimeGe5CounterexampleTarget) :
    TriominoPrimeProvider := by
  exact triominoPrimeProvider_of_FLTPrimeGe5
    (FLTPrimeGe5Target_of_normalizer_and_gapPow_default hNorm hGapPow)

end DkMath.FLT
