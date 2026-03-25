/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.PrimeProvider.TriominoCosmicPrimeGe5Core
import DkMath.NumberTheory.Gcd.GN

set_option linter.style.longLine false
set_option linter.style.emptyLine false

namespace DkMath.FLT

open DkMath.CosmicFormulaBinom

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

/-- Branch A では `GN` 自体も `p * s^p` 形になる。 -/
abbrev PrimeGe5BranchAGNShapeTarget : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    ∃ s : ℕ, GN p (z - y) y = p * s ^ p

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
Branch A の `q ≠ p` 側で必要な核仕様。

`u := z - y` に対し、`q` が素数で `q ≠ p` かつ `q ∣ u` なら `q ∤ GN p u y`。
-/
abbrev PrimeGe5BranchANoSharedPrimeOnGNTarget : Prop :=
  ∀ {p x y z q : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    Nat.Prime q → q ≠ p → q ∣ (z - y) →
    ¬ q ∣ GN p (z - y) y

/-- `p ∣ n` かつ `¬ p^2 ∣ n` なら `padicValNat p n = 1`。 -/
lemma primeGe5BranchAPadicValNat_eq_one_of_dvd_not_sq
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
lemma primeGe5BranchAPadicValNat_gap_shape_of_mul_eq_pow
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

/--
Branch A では、`N := GN p (z - y) y` に対して `p ∣ N` かつ `¬ p^2 ∣ N` が成り立つ。
-/
theorem primeGe5BranchAP_dvd_GN_and_not_sq_when_p_dvd_gap
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
    unfold N A B u
    simpa [f, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hsum
  have hsplit : N = A + B := by
    simpa [Nat.add_comm] using hsplitBA.symm
  have hB_sq : p ^ 2 ∣ B := by
    unfold B
    refine Finset.dvd_sum ?_
    intro k hk
    have hk_mem : k ∈ Finset.range p := Finset.mem_of_mem_erase hk
    have hk_lt : k < p := Finset.mem_range.mp hk_mem
    have hk_ne_zero : k ≠ 0 := Finset.mem_erase.mp hk |>.1
    by_cases hk_one : k = 1
    · have hchoose : p ∣ Nat.choose p (k + 1) := by
        rw [hk_one]
        apply hpack.hp.dvd_choose_self
        · decide
        · exact lt_of_lt_of_le (by decide : 2 < 5) hpack.hp5
      have hp_dvd_uk : p ∣ u ^ k := by
        simpa [hk_one] using hp_dvd_gap
      have hprefix : p ^ 2 ∣ (Nat.choose p (k + 1) : ℕ) * u ^ k := by
        simpa [pow_two] using Nat.mul_dvd_mul hchoose hp_dvd_uk
      have hmul : p ^ 2 ∣ ((Nat.choose p (k + 1) : ℕ) * u ^ k) * y ^ (p - 1 - k) :=
        dvd_mul_of_dvd_left hprefix _
      simpa [Nat.mul_assoc] using hmul
    · have hk_ge_two : 2 ≤ k := by omega
      have hpp_dvd_u2 : p ^ 2 ∣ u ^ 2 := by
        simpa [pow_two] using Nat.mul_dvd_mul hp_dvd_gap hp_dvd_gap
      have hpp_dvd_uk : p ^ 2 ∣ u ^ k := dvd_trans hpp_dvd_u2 (pow_dvd_pow u hk_ge_two)
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
  refine ⟨?_, ?_⟩
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
Branch A の `q ≠ p` 側本丸:
`q ∣ gap` かつ `q ≠ p` なら `q ∤ GN p gap y`。
-/
theorem primeGe5BranchANoSharedPrimeOnGN_math :
    PrimeGe5BranchANoSharedPrimeOnGNTarget := by
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
`PrimeGe5BranchANoSharedPrimeOnGNTarget` が供給されれば、`q ≠ p` 側 factorization 条件が得られる。
-/
theorem primeGe5BranchAShapeFactorization_ne_p_of_noShared
    (hNoShared : PrimeGe5BranchANoSharedPrimeOnGNTarget) :
    ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
      p ∣ (z - y) →
      ∀ q : ℕ, q ≠ p → p ∣ (z - y).factorization q := by
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
      exact ⟨x.factorization q, by simp [u, huq]⟩
    · have hfac0 : u.factorization q = 0 := Nat.factorization_eq_zero_of_not_prime u hqP
      exact ⟨0, by simp [u, hfac0]⟩
  · have hfac0 : u.factorization q = 0 := Nat.factorization_eq_zero_of_not_dvd hqU
    exact ⟨0, by simp [u, hfac0]⟩

/-- Branch A shape-factorization の `q ≠ p` 側 clean 実装。 -/
theorem primeGe5BranchAShapeFactorization_ne_p_default :
    ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
      p ∣ (z - y) →
      ∀ q : ℕ, q ≠ p → p ∣ (z - y).factorization q :=
  primeGe5BranchAShapeFactorization_ne_p_of_noShared
    primeGe5BranchANoSharedPrimeOnGN_math

/--
`q = p` 側の valuation 結論を factorization 形へ持ち上げる補助。
-/
theorem primeGe5BranchAShapeFactorization_p_of_padicValNat
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

/-- Branch A shape-factorization の `q = p` 側 clean 実装（valuation 計算版）。 -/
theorem primeGe5BranchAShapeFactorization_p_default :
    ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
      p ∣ (z - y) →
      ∃ m : ℕ, (z - y).factorization p = (p - 1) + p * m := by
  intro p x y z hpack hp_dvd_gap
  let u : ℕ := z - y
  let N : ℕ := GN p u y
  have hxpow : x ^ p = u * N := by
    simpa [u, N, PrimeGe5CounterexamplePack.gap] using hpack.xpow_eq_gap_mul_GN
  have hGN : p ∣ N ∧ ¬ p ^ 2 ∣ N := by
    simpa [u, N] using primeGe5BranchAP_dvd_GN_and_not_sq_when_p_dvd_gap hpack hp_dvd_gap
  have hN0 : N ≠ 0 := by
    intro hN0
    exact hGN.2 (by simp [hN0])
  have hu0 : u ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt hpack.hyz_lt)
  have hNval : padicValNat p N = 1 :=
    primeGe5BranchAPadicValNat_eq_one_of_dvd_not_sq hpack.hp hGN.1 hGN.2
  have hVal : ∃ m : ℕ, padicValNat p u = (p - 1) + p * m := by
    exact primeGe5BranchAPadicValNat_gap_shape_of_mul_eq_pow
      (hp := hpack.hp)
      (hx0 := hpack.hx0)
      (hu0 := hu0)
      (hN0 := hN0)
      (hEq := hxpow)
      (hNval := hNval)
  simpa [u] using primeGe5BranchAShapeFactorization_p_of_padicValNat hpack hVal

/-- Branch A の shape witness `z - y = p^(p-1) * t^p` から `t > 0` を回収する。 -/
lemma primeGe5BranchAShapeWitness_t_pos
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

/--
shape-value から `q ≠ p` 側の指数整列
`p ∣ (z - y).factorization q`
を読み戻す。
-/
theorem primeGe5BranchAShapeFactorization_ne_p_of_value
    {p x y z : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (_hp_dvd_gap : p ∣ (z - y))
    (hShapeValue : ∃ t : ℕ, (z - y) = p ^ (p - 1) * t ^ p) :
    ∀ q : ℕ, q ≠ p → p ∣ (z - y).factorization q := by
  intro q hq_ne
  rcases hShapeValue with ⟨t, ht⟩
  have ht_pos : 0 < t := primeGe5BranchAShapeWitness_t_pos hpack ht
  have hd0 : p ^ (p - 1) ≠ 0 := Nat.ne_of_gt (Nat.pow_pos hpack.hp.pos)
  have htp0 : t ^ p ≠ 0 := by
    exact pow_ne_zero p (Nat.ne_of_gt ht_pos)
  have hp_fac_q : p.factorization q = 0 := by
    by_cases hqP : Nat.Prime q
    · exact Nat.factorization_eq_zero_of_not_dvd (by
        intro hq_dvd_p
        exact hq_ne ((Nat.prime_dvd_prime_iff_eq hqP hpack.hp).1 hq_dvd_p))
    · exact Nat.factorization_eq_zero_of_not_prime p hqP
  have hd_fac_q : (p ^ (p - 1)).factorization q = 0 := by
    calc
      (p ^ (p - 1)).factorization q = (p - 1) * p.factorization q := by
        simp [Nat.factorization_pow]
      _ = 0 := by simp [hp_fac_q]
  have ht_fac_q : (t ^ p).factorization q = p * t.factorization q := by
    simp [Nat.factorization_pow]
  have hgap_fac_q : (z - y).factorization q = p * t.factorization q := by
    calc
      (z - y).factorization q = (p ^ (p - 1) * t ^ p).factorization q := by simp [ht]
      _ = (p ^ (p - 1)).factorization q + (t ^ p).factorization q := by
        simp [Nat.factorization_mul hd0 htp0]
      _ = 0 + p * t.factorization q := by
        rw [hd_fac_q, ht_fac_q]
      _ = p * t.factorization q := by simp
  exact ⟨t.factorization q, by simp [hgap_fac_q]⟩

/--
shape-value から `q = p` 側の指数形
`(z - y).factorization p = (p - 1) + p * m`
を読み戻す。
-/
theorem primeGe5BranchAShapeFactorization_p_of_value
    {p x y z : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (_hp_dvd_gap : p ∣ (z - y))
    (hShapeValue : ∃ t : ℕ, (z - y) = p ^ (p - 1) * t ^ p) :
    ∃ m : ℕ, (z - y).factorization p = (p - 1) + p * m := by
  rcases hShapeValue with ⟨t, ht⟩
  have ht_pos : 0 < t := primeGe5BranchAShapeWitness_t_pos hpack ht
  have hd0 : p ^ (p - 1) ≠ 0 := Nat.ne_of_gt (Nat.pow_pos hpack.hp.pos)
  have htp0 : t ^ p ≠ 0 := by
    exact pow_ne_zero p (Nat.ne_of_gt ht_pos)
  have hd_fac_p : (p ^ (p - 1)).factorization p = p - 1 := by
    simpa using Nat.factorization_pow_self (p := p) (n := p - 1) hpack.hp
  have ht_fac_p : (t ^ p).factorization p = p * t.factorization p := by
    simp [Nat.factorization_pow]
  refine ⟨t.factorization p, ?_⟩
  calc
    (z - y).factorization p = (p ^ (p - 1) * t ^ p).factorization p := by simp [ht]
    _ = (p ^ (p - 1)).factorization p + (t ^ p).factorization p := by
      simp [Nat.factorization_mul hd0 htp0]
    _ = (p - 1) + p * t.factorization p := by
      rw [hd_fac_p, ht_fac_p]

/--
shape-value が供給されれば、Branch A の shape-factorization target へ戻せる。
-/
theorem primeGe5BranchAShapeFactorization_of_value
    (hValue : PrimeGe5BranchAShapeValueTarget) :
    PrimeGe5BranchAShapeFactorizationTarget := by
  intro p x y z hpack hp_dvd_gap
  have hShapeValue := hValue hpack hp_dvd_gap
  refine ⟨?_, ?_⟩
  · exact primeGe5BranchAShapeFactorization_ne_p_of_value hpack hp_dvd_gap hShapeValue
  · exact primeGe5BranchAShapeFactorization_p_of_value hpack hp_dvd_gap hShapeValue

/--
Branch A shape-factorization の clean 実装。

残る未完核を shape-value refuter 側へ押し込み、factorization spine は
BranchA lower layer だけで閉じる。
-/
theorem primeGe5BranchAShapeFactorization_default :
    PrimeGe5BranchAShapeFactorizationTarget := by
  intro p x y z hpack hp_dvd_gap
  exact ⟨primeGe5BranchAShapeFactorization_ne_p_default hpack hp_dvd_gap,
    primeGe5BranchAShapeFactorization_p_default hpack hp_dvd_gap⟩

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
Branch A では `q ≠ p` 側の `GN` 指数は `p` の倍数。
-/
theorem primeGe5BranchAGN_factorization_ne_p_math
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hp_dvd_gap : p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hqp : q ≠ p) :
    p ∣ (GN p (z - y) y).factorization q := by
  let u : ℕ := z - y
  let N : ℕ := GN p u y
  have hxpow : x ^ p = u * N := by
    simpa [u, N, PrimeGe5CounterexamplePack.gap] using hpack.xpow_eq_gap_mul_GN
  have hu0 : u ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt hpack.hyz_lt)
  have hN0 : N ≠ 0 := by
    intro hN0
    have hGN : p ∣ N ∧ ¬ p ^ 2 ∣ N := by
      simpa [u, N] using primeGe5BranchAP_dvd_GN_and_not_sq_when_p_dvd_gap hpack hp_dvd_gap
    exact hGN.2 (by simp [hN0])
  by_cases hqU : q ∣ u
  · have hq_not_dvd_N : ¬ q ∣ N := by
      simpa [u, N] using primeGe5BranchANoSharedPrimeOnGN_math hpack hp_dvd_gap hqP hqp hqU
    have hNfac0 : N.factorization q = 0 := Nat.factorization_eq_zero_of_not_dvd hq_not_dvd_N
    exact ⟨0, by simpa [N, hNfac0]⟩
  · have hfac0 : u.factorization q = 0 := Nat.factorization_eq_zero_of_not_dvd hqU
    have hmulq : (u * N).factorization q = u.factorization q + N.factorization q := by
      simpa using congrArg (fun f => f q) (Nat.factorization_mul hu0 hN0)
    have hpowq : (x ^ p).factorization q = p * x.factorization q := by
      simp [Nat.factorization_pow]
    have hNq : N.factorization q = p * x.factorization q := by
      calc
        N.factorization q = 0 + N.factorization q := by simp
        _ = u.factorization q + N.factorization q := by simp [hfac0]
        _ = (u * N).factorization q := by symm; exact hmulq
        _ = (x ^ p).factorization q := by simp [hxpow]
        _ = p * x.factorization q := hpowq
    exact ⟨x.factorization q, by simpa [N, hNq]⟩

/--
Branch A では `GN` 自体が `p * s^p` 形になる。
`gapShape` はまだ使わない。
-/
theorem primeGe5BranchAGN_eq_p_mul_pow_math :
    PrimeGe5BranchAGNShapeTarget := by
  intro p x y z hpack hp_dvd_gap
  let N : ℕ := GN p (z - y) y
  have hp_dvd_N : p ∣ N := by
    simpa [N] using (primeGe5BranchAP_dvd_GN_and_not_sq_when_p_dvd_gap hpack hp_dvd_gap).1
  have hN_not_sq : ¬ p ^ 2 ∣ N := by
    simpa [N] using (primeGe5BranchAP_dvd_GN_and_not_sq_when_p_dvd_gap hpack hp_dvd_gap).2
  have hN0 : N ≠ 0 := by
    intro hN0
    exact hN_not_sq (by simp [hN0])
  have hNfac_p : N.factorization p = 1 := by
    calc
      N.factorization p = padicValNat p N := by
        symm
        exact padicValNat_eq_factorization hpack.hp hN0
      _ = 1 := primeGe5BranchAPadicValNat_eq_one_of_dvd_not_sq hpack.hp hp_dvd_N hN_not_sq
  let w : ℕ := N / p
  have hw_pos : 0 < w := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hp_dvd_N) hpack.hp.pos
  have hw0 : w ≠ 0 := Nat.ne_of_gt hw_pos
  have hfac_div : w.factorization = N.factorization - p.factorization := by
    simpa [w] using Nat.factorization_div hp_dvd_N
  have hall_w : ∀ q : ℕ, p ∣ w.factorization q := by
    intro q
    by_cases hq_eq : q = p
    · have hp_fac_p : p.factorization p = 1 := by
        simpa using congrArg (fun f => f p) hpack.hp.factorization
      have hw_fac_p : w.factorization p = 0 := by
        calc
          w.factorization p = N.factorization p - p.factorization p := by
            simpa using congrArg (fun f => f p) hfac_div
          _ = 1 - 1 := by simp [hNfac_p, hp_fac_p]
          _ = 0 := by simp
      exact ⟨0, by simp [hq_eq, hw_fac_p]⟩
    · by_cases hqP : Nat.Prime q
      · have hNq : p ∣ N.factorization q := by
          simpa [N] using primeGe5BranchAGN_factorization_ne_p_math hpack hp_dvd_gap hqP hq_eq
        have hp_fac_q : p.factorization q = 0 := by
          exact Nat.factorization_eq_zero_of_not_dvd (by
            intro hq_dvd_p
            exact hq_eq ((Nat.prime_dvd_prime_iff_eq hqP hpack.hp).1 hq_dvd_p))
        have hw_fac_q : w.factorization q = N.factorization q := by
          calc
            w.factorization q = N.factorization q - p.factorization q := by
              simpa using congrArg (fun f => f q) hfac_div
            _ = N.factorization q := by simp [hp_fac_q]
        rcases hNq with ⟨k, hk⟩
        exact ⟨k, by simp [hw_fac_q, hk]⟩
      · have hw_fac0 : w.factorization q = 0 := Nat.factorization_eq_zero_of_not_prime w hqP
        exact ⟨0, by simp [hw_fac0]⟩
  rcases exists_eq_pow_of_factorization_dvd
      (u := w) (p := p) hw0 hpack.hp.pos hall_w with ⟨s, hs⟩
  have hN_mul : N = p * w := by
    have hw_mul : w * p = N := by
      simpa [w] using Nat.div_mul_cancel hp_dvd_N
    simpa [Nat.mul_comm] using hw_mul.symm
  refine ⟨s, ?_⟩
  calc
    GN p (z - y) y = N := by rfl
    _ = p * w := hN_mul
    _ = p * s ^ p := by simp [hs]

/--
Branch A witness から `gap`, `GN`, `x` の 3 つを同時に正規形へ揃える。
-/
theorem primeGe5BranchANormalForm_of_witness
    {p x y z t : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hp_dvd_gap : p ∣ (z - y))
    (ht : z - y = p ^ (p - 1) * t ^ p) :
    ∃ s : ℕ, GN p (z - y) y = p * s ^ p ∧ x = p * (t * s) := by
  rcases primeGe5BranchAGN_eq_p_mul_pow_math hpack hp_dvd_gap with ⟨s, hs⟩
  refine ⟨s, hs, ?_⟩
  have hxpow : x ^ p = (z - y) * GN p (z - y) y := by
    simpa [PrimeGe5CounterexamplePack.gap] using hpack.xpow_eq_gap_mul_GN
  have hpred : p - 1 + 1 = p := Nat.sub_add_cancel (Nat.succ_le_of_lt hpack.hp.pos)
  have hs' : GN p (p ^ (p - 1) * t ^ p) y = p * s ^ p := by
    simpa [ht] using hs
  have hpow_eq : x ^ p = (p * (t * s)) ^ p := by
    calc
      x ^ p = (z - y) * GN p (z - y) y := hxpow
      _ = (p ^ (p - 1) * t ^ p) * GN p (p ^ (p - 1) * t ^ p) y := by rw [ht]
      _ = (p ^ (p - 1) * t ^ p) * (p * s ^ p) := by rw [hs']
      _ = (p ^ (p - 1) * p) * (t ^ p * s ^ p) := by ac_rfl
      _ = p ^ ((p - 1) + 1) * (t ^ p * s ^ p) := by rw [← pow_succ]
      _ = p ^ p * (t ^ p * s ^ p) := by rw [hpred]
      _ = p ^ p * (t * s) ^ p := by rw [Nat.mul_pow]
      _ = (p * (t * s)) ^ p := by symm; exact Nat.mul_pow p (t * s) p
  exact (Nat.pow_left_injective hpack.hp.ne_zero) hpow_eq

/--
Branch A の `gcd(gap, GN)` が `p` を割るという制御を注入する abstract target。
-/
abbrev PrimeGe5BranchAGcdGapGNDvdPTarget : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    Nat.gcd (z - y) (GN p (z - y) y) ∣ p

/--
`PrimeGe5CounterexamplePack` では、既存の gcd/GN API から
`gcd(gap, GN) ∣ p` を自然数版で直接回収できる。
-/
theorem primeGe5BranchAGcdGapGNDvdP_default :
    PrimeGe5BranchAGcdGapGNDvdPTarget := by
  intro p x y z hpack _hp_dvd_gap
  have hcop_zy : Nat.Coprime z y := by
    exact (coprime_right_of_add_pow_eq_pow hpack.hp hpack.hxy hpack.hEq).symm
  exact DkMath.NumberTheory.Gcd.gcd_gap_GN_dvd_exp
    (hp1 := Nat.succ_le_of_lt hpack.hp.pos) (hyz := hpack.hyz_lt) (hcop := hcop_zy)

/--
normal form から、`p * gcd(t,s)^p` は `gcd(gap, GN)` を割る。

gcd exactness の下半身。
-/
theorem primeGe5BranchANormalForm_p_mul_gcd_ts_pow_dvd_gcd_gap_GN
    {p x y z t s : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (_hp_dvd_gap : p ∣ (z - y))
    (hgap : z - y = p ^ (p - 1) * t ^ p)
    (hsGN : GN p (z - y) y = p * s ^ p) :
    p * Nat.gcd t s ^ p ∣ Nat.gcd (z - y) (GN p (z - y) y) := by
  let g : ℕ := Nat.gcd t s
  have hg_t : g ∣ t := by
    exact Nat.gcd_dvd_left t s
  have hg_s : g ∣ s := by
    exact Nat.gcd_dvd_right t s
  have hgpow_tpow : g ^ p ∣ t ^ p := pow_dvd_pow_of_dvd hg_t p
  have hgpow_spow : g ^ p ∣ s ^ p := pow_dvd_pow_of_dvd hg_s p
  have hp_dvd_powPred : p ∣ p ^ (p - 1) := by
    exact dvd_pow_self p (Nat.sub_ne_zero_of_lt hpack.hp.one_lt)
  have hleft : p * g ^ p ∣ z - y := by
    have hmul : p * g ^ p ∣ p ^ (p - 1) * t ^ p := by
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
        Nat.mul_dvd_mul hp_dvd_powPred hgpow_tpow
    simpa [hgap] using hmul
  have hright : p * g ^ p ∣ GN p (z - y) y := by
    have hsGN' : GN p (z - y) y = p * s ^ p := hsGN
    have hmul : p * g ^ p ∣ p * s ^ p := by
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
        Nat.mul_dvd_mul (dvd_rfl : p ∣ p) hgpow_spow
    rw [hsGN']
    exact hmul
  exact Nat.dvd_gcd hleft hright

/--
`gcd(gap, GN) ∣ p` が与えられれば、normal form から `gcd(t,s) = 1` を抽出できる。
-/
theorem primeGe5BranchANormalForm_gcd_ts_eq_one_of_gcd_gap_GN_dvd_p
    {p x y z t s : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hp_dvd_gap : p ∣ (z - y))
    (hgap : z - y = p ^ (p - 1) * t ^ p)
    (hsGN : GN p (z - y) y = p * s ^ p)
    (hgcd_dvd_p : Nat.gcd (z - y) (GN p (z - y) y) ∣ p) :
    Nat.gcd t s = 1 := by
  let g : ℕ := Nat.gcd t s
  have hdiv : p * g ^ p ∣ p := by
    exact dvd_trans
      (primeGe5BranchANormalForm_p_mul_gcd_ts_pow_dvd_gcd_gap_GN hpack hp_dvd_gap hgap hsGN)
      hgcd_dvd_p
  rcases hdiv with ⟨k, hk⟩
  have hk' : p * 1 = p * (g ^ p * k) := by
    calc
      p * 1 = p := by simp
      _ = (p * g ^ p) * k := hk
      _ = p * (g ^ p * k) := by ac_rfl
  have h1 : 1 = g ^ p * k := Nat.eq_of_mul_eq_mul_left hpack.hp.pos hk'
  have hgpow_dvd_one : g ^ p ∣ 1 := ⟨k, h1⟩
  have hgpow_eq_one : g ^ p = 1 := Nat.eq_one_of_dvd_one hgpow_dvd_one
  have hg_eq : g ^ p = 1 ^ p := by simpa using hgpow_eq_one
  exact (Nat.pow_left_injective hpack.hp.ne_zero) hg_eq

/--
Branch A の既存 gcd 制御を使えば、normal form から `gcd(t,s) = 1` を default で抽出できる。
-/
theorem primeGe5BranchANormalForm_gcd_ts_eq_one_default
    {p x y z t s : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hp_dvd_gap : p ∣ (z - y))
    (hgap : z - y = p ^ (p - 1) * t ^ p)
    (hsGN : GN p (z - y) y = p * s ^ p) :
    Nat.gcd t s = 1 := by
  exact primeGe5BranchANormalForm_gcd_ts_eq_one_of_gcd_gap_GN_dvd_p
    hpack hp_dvd_gap hgap hsGN
    (primeGe5BranchAGcdGapGNDvdP_default hpack hp_dvd_gap)

/--
normal form の `x = p * (t * s)` と反例 pack の `x ⟂ y` から、
`t * s` も `y` と互いに素である。
-/
theorem primeGe5BranchANormalForm_coprime_ts_right
    {p x y z t s : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hsx : x = p * (t * s)) :
    Nat.Coprime (t * s) y := by
  have hcop_y_pts : Nat.Coprime y (p * (t * s)) := by
    simpa [Nat.coprime_comm, hsx]
      using hpack.hxy
  have hparts : Nat.Coprime y p ∧ Nat.Coprime y (t * s) :=
    (Nat.coprime_mul_iff_right).1 hcop_y_pts
  simpa [Nat.coprime_comm] using hparts.2

/--
`t * s ⟂ y` なら、個別にも `t ⟂ y` と `s ⟂ y` が従う。
-/
theorem primeGe5BranchANormalForm_coprime_t_right
    {p x y z t s : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hsx : x = p * (t * s)) :
    Nat.Coprime t y := by
  have hcop_y_ts : Nat.Coprime y (t * s) := by
    simpa [Nat.coprime_comm, mul_comm] using
      (primeGe5BranchANormalForm_coprime_ts_right hpack hsx)
  have hparts : Nat.Coprime y t ∧ Nat.Coprime y s :=
    (Nat.coprime_mul_iff_right).1 hcop_y_ts
  simpa [Nat.coprime_comm] using hparts.1

/--
`t * s ⟂ y` なら、個別にも `s ⟂ y` が従う。
-/
theorem primeGe5BranchANormalForm_coprime_s_right
    {p x y z t s : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hsx : x = p * (t * s)) :
    Nat.Coprime s y := by
  have hcop_y_ts : Nat.Coprime y (t * s) := by
    simpa [Nat.coprime_comm, mul_comm] using
      (primeGe5BranchANormalForm_coprime_ts_right hpack hsx)
  have hparts : Nat.Coprime y t ∧ Nat.Coprime y s :=
    (Nat.coprime_mul_iff_right).1 hcop_y_ts
  simpa [Nat.coprime_comm] using hparts.2

/--
Branch A normal form では `t` と `s` 自体も互いに素になる。
-/
theorem primeGe5BranchANormalForm_coprime_ts_default
    {p x y z t s : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hp_dvd_gap : p ∣ (z - y))
    (hgap : z - y = p ^ (p - 1) * t ^ p)
    (hsGN : GN p (z - y) y = p * s ^ p) :
    Nat.Coprime t s := by
  exact (Nat.coprime_iff_gcd_eq_one).2
    (primeGe5BranchANormalForm_gcd_ts_eq_one_default hpack hp_dvd_gap hgap hsGN)

/--
Branch A normal form では、既存の `gcd(gap, GN) ∣ p` と
`p ∣ gap`, `p ∣ GN` を合わせて `gcd(gap, GN) = p` まで exact に戻せる。
-/
theorem primeGe5BranchANormalForm_gcd_gap_GN_eq_p_default
    {p x y z t s : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hp_dvd_gap : p ∣ (z - y))
    (_hgap : z - y = p ^ (p - 1) * t ^ p)
    (hsGN : GN p (z - y) y = p * s ^ p) :
    Nat.gcd (z - y) (GN p (z - y) y) = p := by
  have hgcd_dvd_p :
      Nat.gcd (z - y) (GN p (z - y) y) ∣ p :=
    primeGe5BranchAGcdGapGNDvdP_default hpack hp_dvd_gap
  have hp_dvd_gcd :
      p ∣ Nat.gcd (z - y) (GN p (z - y) y) := by
    refine Nat.dvd_gcd hp_dvd_gap ?_
    rw [hsGN]
    exact dvd_mul_right p (s ^ p)
  rcases (Nat.dvd_prime hpack.hp).mp hgcd_dvd_p with hgcd_eq_one | hgcd_eq_p
  · have hp_dvd_one : p ∣ 1 := by
      rw [← hgcd_eq_one]
      exact hp_dvd_gcd
    have hp_eq_one : p = 1 := Nat.eq_one_of_dvd_one hp_dvd_one
    exact False.elim (hpack.hp.ne_one hp_eq_one)
  · exact hgcd_eq_p

/--
`GN = p * s^p` と `p^2 ∤ GN` から、normal form の `s` は `p` で割れない。
-/
theorem primeGe5BranchANormalForm_prime_not_dvd_s_default
    {p x y z t s : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hp_dvd_gap : p ∣ (z - y))
    (_hgap : z - y = p ^ (p - 1) * t ^ p)
    (hsGN : GN p (z - y) y = p * s ^ p) :
    ¬ p ∣ s := by
  have hGN_not_sq : ¬ p ^ 2 ∣ GN p (z - y) y := by
    simpa using (primeGe5BranchAP_dvd_GN_and_not_sq_when_p_dvd_gap hpack hp_dvd_gap).2
  intro hp_dvd_s
  have hp_dvd_spow : p ∣ s ^ p := dvd_pow hp_dvd_s hpack.hp.ne_zero
  have hp2_dvd_GN : p ^ 2 ∣ GN p (z - y) y := by
    rw [hsGN]
    have hmul : p * p ∣ p * s ^ p :=
      Nat.mul_dvd_mul_left p hp_dvd_spow
    simpa [pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
  exact hGN_not_sq hp2_dvd_GN

/--
`p ∤ s` が取れれば、素数性から `p ⟂ s` へ直ちに上げられる。
-/
theorem primeGe5BranchANormalForm_coprime_p_s_default
    {p x y z t s : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hp_dvd_gap : p ∣ (z - y))
    (hgap : z - y = p ^ (p - 1) * t ^ p)
    (hsGN : GN p (z - y) y = p * s ^ p) :
    Nat.Coprime p s := by
  exact (Nat.Prime.coprime_iff_not_dvd hpack.hp).2
    (primeGe5BranchANormalForm_prime_not_dvd_s_default hpack hp_dvd_gap hgap hsGN)

/--
Branch A では `p ∣ gap` と `gap ⟂ y` から `p ∤ y` が従う。
-/
theorem primeGe5BranchANormalForm_prime_not_dvd_y_default
    {p x y z : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hp_dvd_gap : p ∣ (z - y)) :
    ¬ p ∣ y := by
  simpa [PrimeGe5CounterexamplePack.gap] using
    hpack.prime_not_dvd_right_of_prime_dvd_gap hp_dvd_gap

/--
`p ∤ y` も、素数性から `p ⟂ y` の形へ上げておける。
-/
theorem primeGe5BranchANormalForm_coprime_p_y_default
    {p x y z : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hp_dvd_gap : p ∣ (z - y)) :
    Nat.Coprime p y := by
  exact (Nat.Prime.coprime_iff_not_dvd hpack.hp).2
    (primeGe5BranchANormalForm_prime_not_dvd_y_default hpack hp_dvd_gap)

/--
反例 pack の基本恒等式 `x^p = gap * GN` と `x ⟂ y` から、
`GN p (z - y) y` 自体も `y` と互いに素である。
-/
theorem primeGe5BranchANormalForm_coprime_GN_right_default
    {p x y z : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z) :
    Nat.Coprime (GN p (z - y) y) y := by
  have hcop_xpow_y : Nat.Coprime (x ^ p) y :=
    Nat.Coprime.pow_left p hpack.hxy
  have hcop_prod_y : Nat.Coprime ((z - y) * GN p (z - y) y) y := by
    simpa [PrimeGe5CounterexamplePack.gap] using
      (hpack.xpow_eq_gap_mul_GN ▸ hcop_xpow_y)
  have hcop_y_prod : Nat.Coprime y ((z - y) * GN p (z - y) y) := hcop_prod_y.symm
  have hparts :
      Nat.Coprime y (z - y) ∧ Nat.Coprime y (GN p (z - y) y) :=
    (Nat.coprime_mul_iff_right).1 hcop_y_prod
  simpa [Nat.coprime_comm] using hparts.2

/--
`GN ⟂ y` と `GN = p * s^p` を合わせると、
`p * s^p` そのものも `y` と互いに素である。
-/
theorem primeGe5BranchANormalForm_coprime_pspow_y_default
    {p x y z s : ℕ}
    (_hpack : PrimeGe5CounterexamplePack p x y z)
    (hsGN : GN p (z - y) y = p * s ^ p)
    (hcop_GNy : Nat.Coprime (GN p (z - y) y) y) :
    Nat.Coprime (p * s ^ p) y := by
  rw [← hsGN]
  exact hcop_GNy

/--
`p * s^p ⟂ y` から `s^p ⟂ y` を抜き出す。
-/
theorem primeGe5BranchANormalForm_coprime_spow_y_default
    {p x y z s : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hsGN : GN p (z - y) y = p * s ^ p)
    (hcop_GNy : Nat.Coprime (GN p (z - y) y) y) :
    Nat.Coprime (s ^ p) y := by
  have hcop_pspow_y : Nat.Coprime (p * s ^ p) y :=
    primeGe5BranchANormalForm_coprime_pspow_y_default hpack hsGN hcop_GNy
  exact (Nat.coprime_mul_iff_left).1 hcop_pspow_y |>.2

/--
`p ⟂ s` なら冪に上げても `p ⟂ s^p` は保たれる。
-/
theorem primeGe5BranchANormalForm_coprime_p_spow_default
    {p x y z t s : ℕ}
    (_hpack : PrimeGe5CounterexamplePack p x y z)
    (_hp_dvd_gap : p ∣ (z - y))
    (_hgap : z - y = p ^ (p - 1) * t ^ p)
    (_hsGN : GN p (z - y) y = p * s ^ p)
    (hcop_ps : Nat.Coprime p s) :
    Nat.Coprime p (s ^ p) := by
  exact Nat.Coprime.pow_right p hcop_ps

/--
`p ⟂ y` と `s ⟂ y` から、線形因子 `p * s` も `y` と互いに素である。
-/
theorem primeGe5BranchANormalForm_coprime_ps_y_default
    {p x y z t s : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hp_dvd_gap : p ∣ (z - y))
    (_hgap : z - y = p ^ (p - 1) * t ^ p)
    (_hsGN : GN p (z - y) y = p * s ^ p)
    (_hsx : x = p * (t * s))
    (hcop_sy : Nat.Coprime s y) :
    Nat.Coprime (p * s) y := by
  have hcop_py : Nat.Coprime p y :=
    primeGe5BranchANormalForm_coprime_p_y_default hpack hp_dvd_gap
  exact Nat.Coprime.mul_left hcop_py hcop_sy

/--
normal form の `x = p * (t * s)` は、線形因子 `(t, p * s)` の積に並べ替えられる。
-/
theorem primeGe5BranchANormalForm_x_eq_t_mul_ps
    {p x y z t s : ℕ}
    (_hpack : PrimeGe5CounterexamplePack p x y z)
    (_hp_dvd_gap : p ∣ (z - y))
    (_hgap : z - y = p ^ (p - 1) * t ^ p)
    (_hsGN : GN p (z - y) y = p * s ^ p)
    (hsx : x = p * (t * s)) :
    x = t * (p * s) := by
  calc
    x = p * (t * s) := hsx
    _ = t * (p * s) := by ac_rfl

/--
`t ⟂ y` と `(p * s) ⟂ y` が揃えば、線形分解 `t * (p * s)` も `y` と互いに素。
-/
theorem primeGe5BranchANormalForm_coprime_t_ps_default
    {p x y z t s : ℕ}
    (_hpack : PrimeGe5CounterexamplePack p x y z)
    (_hp_dvd_gap : p ∣ (z - y))
    (_hgap : z - y = p ^ (p - 1) * t ^ p)
    (_hsGN : GN p (z - y) y = p * s ^ p)
    (_hsx : x = p * (t * s))
    (hcop_ty : Nat.Coprime t y)
    (hcop_psy : Nat.Coprime (p * s) y) :
    Nat.Coprime (t * (p * s)) y := by
  exact Nat.Coprime.mul_left hcop_ty hcop_psy

/--
`x = t * (p * s)` を基準形にすると、`x^p` はそのまま `(t * (p * s))^p` に一致する。
-/
theorem primeGe5BranchANormalForm_xpow_eq_tps_pow
    {p x y z t s : ℕ}
    (_hpack : PrimeGe5CounterexamplePack p x y z)
    (_hp_dvd_gap : p ∣ (z - y))
    (_hgap : z - y = p ^ (p - 1) * t ^ p)
    (_hsGN : GN p (z - y) y = p * s ^ p)
    (hx_tps : x = t * (p * s)) :
    x ^ p = (t * (p * s)) ^ p := by
  simp [hx_tps]

/--
`x = t * (p * s)` の基準形では、`x^p` の factorization も
`p * ((t * (p * s)).factorization q)` に exact に戻る。
-/
theorem primeGe5BranchANormalForm_xpow_factorization_exact
    {p x y z t s q : ℕ}
    (_hpack : PrimeGe5CounterexamplePack p x y z)
    (_hp_dvd_gap : p ∣ (z - y))
    (_hgap : z - y = p ^ (p - 1) * t ^ p)
    (_hsGN : GN p (z - y) y = p * s ^ p)
    (hx_tps : x = t * (p * s)) :
    (x ^ p).factorization q = p * (t * (p * s)).factorization q := by
  calc
    (x ^ p).factorization q = p * x.factorization q := by
      simp [Nat.factorization_pow]
    _ = p * (t * (p * s)).factorization q := by
      simp [hx_tps]

/--
`gap = p^(p-1) * t^p` と `GN = p * s^p` を掛け合わせると、
右辺全体は `(t * (p * s))^p` に再構成できる。
-/
theorem primeGe5BranchANormalForm_gapGN_eq_tps_pow
    {p x y z t s : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (_hp_dvd_gap : p ∣ (z - y))
    (hgap : z - y = p ^ (p - 1) * t ^ p)
    (hsGN : GN p (z - y) y = p * s ^ p) :
    (z - y) * GN p (z - y) y = (t * (p * s)) ^ p := by
  have hp_eq : p = (p - 1) + 1 := by
    simpa [Nat.pred_eq_sub_one] using (Nat.succ_pred_eq_of_pos hpack.hp.pos).symm
  calc
    (z - y) * GN p (z - y) y
        = (z - y) * (p * s ^ p) := by
            rw [hsGN]
    _ = (p ^ (p - 1) * t ^ p) * (p * s ^ p) := by
          rw [hgap]
    _ = p ^ p * (t ^ p * s ^ p) := by
          rw [show p ^ p = p ^ (p - 1) * p by
                rw [hp_eq, Nat.pow_succ']
                simp [Nat.mul_comm]]
          ac_rfl
    _ = p ^ p * (t * s) ^ p := by
          rw [Nat.mul_pow]
    _ = (p * (t * s)) ^ p := by
          symm
          rw [Nat.mul_pow]
    _ = (t * (p * s)) ^ p := by
          symm
          congr 1
          ac_rfl

/--
`gap * GN` 側も、normal form では `p * ((t * (p * s)).factorization q)` に
exact に戻る。
-/
theorem primeGe5BranchANormalForm_gapGN_factorization_exact
    {p x y z t s q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hp_dvd_gap : p ∣ (z - y))
    (hgap : z - y = p ^ (p - 1) * t ^ p)
    (hsGN : GN p (z - y) y = p * s ^ p) :
    ((z - y) * GN p (z - y) y).factorization q =
      p * (t * (p * s)).factorization q := by
  calc
    ((z - y) * GN p (z - y) y).factorization q
        = ((t * (p * s)) ^ p).factorization q := by
            rw [primeGe5BranchANormalForm_gapGN_eq_tps_pow hpack hp_dvd_gap hgap hsGN]
    _ = p * (t * (p * s)).factorization q := by
          simp [Nat.factorization_pow]

/-- Branch A の shape witness から `p^(p-1) ∣ z-y` を回収する。 -/
lemma primeGe5BranchAShapeWitness_powPred_dvd_gap
    {p y z t : ℕ}
    (ht : z - y = p ^ (p - 1) * t ^ p) :
    p ^ (p - 1) ∣ (z - y) := by
  refine ⟨t ^ p, ?_⟩
  simpa [Nat.mul_comm] using ht

/-- Branch A shape witness から既存 descent 契約へ渡す最小入力。 -/
structure PrimeGe5BranchAShapeWitnessDescentInput (p x y z t : ℕ) : Prop where
  tPos : 0 < t
  powPredDvdGap : p ^ (p - 1) ∣ (z - y)
  gapShape : z - y = p ^ (p - 1) * t ^ p

/-- `ht` から Branch A witness の最小 descent 入力を組み立てる。 -/
theorem primeGe5BranchAShapeWitness_to_descent_input
    {p x y z t : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (_hp_dvd_gap : p ∣ (z - y))
    (ht : z - y = p ^ (p - 1) * t ^ p) :
    PrimeGe5BranchAShapeWitnessDescentInput p x y z t := by
  exact ⟨primeGe5BranchAShapeWitness_t_pos hpack ht,
    primeGe5BranchAShapeWitness_powPred_dvd_gap ht, ht⟩

/--
Branch A の witness 直受け最終 kernel。

`hpack + hp_dvd_gap + ht` から `False` を導く一点集中の差し替え口として固定する。
-/
abbrev PrimeGe5BranchAShapeWitnessKernelTarget : Prop :=
  ∀ {p x y z t : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    PrimeGe5BranchAShapeWitnessDescentInput p x y z t →
    False

/--
Branch A の局所数学核。

normal form をどう矛盾へ送るかだけを担う最終差し替え口。
-/
abbrev PrimeGe5BranchANormalFormRefuterTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    False

/--
normal form refuter の残核。

ここでは既に抽出済みの
`gcd(gap, GN) = p`,
`t ⟂ s`,
`t ⟂ y`,
`s ⟂ y`,
`p ∤ s`
だけを入力として、最後の局所矛盾へ集中する。
-/
abbrev PrimeGe5BranchANormalFormArithmeticKernelTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    Nat.gcd (z - y) (GN p (z - y) y) = p →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    False

/--
arithmetic kernel のさらに下の局所差し替え口。

`p ⟂ s` と `p ∤ y` まで明示入力にして、
最後の衝突だけへ責務をさらに寄せる。
-/
abbrev PrimeGe5BranchANormalFormLocalCoprimeKernelTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    Nat.gcd (z - y) (GN p (z - y) y) = p →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    Nat.Coprime p s →
    ¬ p ∣ y →
    False

/--
local coprime kernel のさらに下で、`GN ⟂ y` を explicit に受ける差し替え口。

`GN` 側の局所情報へ戻して衝突させる場合、この契約 1 本を詰めればよい。
-/
abbrev PrimeGe5BranchANormalFormGNRightKernelTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    Nat.gcd (z - y) (GN p (z - y) y) = p →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    Nat.Coprime p s →
    ¬ p ∣ y →
    Nat.Coprime (GN p (z - y) y) y →
    False

/--
GN-side kernel のさらに下で、`GN = p * s^p` の factor-level coprime 情報
まで explicit に並べる差し替え口。
-/
abbrev PrimeGe5BranchANormalFormGNFactorKernelTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    Nat.gcd (z - y) (GN p (z - y) y) = p →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    Nat.Coprime p s →
    ¬ p ∣ y →
    Nat.Coprime (GN p (z - y) y) y →
    Nat.Coprime (p * s ^ p) y →
    Nat.Coprime (s ^ p) y →
    False

/--
GN factor kernel のさらに下で、`p ⟂ s^p` と `p * s ⟂ y` まで
explicit に並べる差し替え口。
-/
abbrev PrimeGe5BranchANormalFormGNLinearFactorKernelTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    Nat.gcd (z - y) (GN p (z - y) y) = p →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    Nat.Coprime p s →
    ¬ p ∣ y →
    Nat.Coprime (GN p (z - y) y) y →
    Nat.Coprime (p * s ^ p) y →
    Nat.Coprime (s ^ p) y →
    Nat.Coprime p (s ^ p) →
    Nat.Coprime (p * s) y →
    False

/--
GN linear-factor kernel のさらに下で、`x = t * (p * s)` と
`Nat.Coprime (t * (p * s)) y` まで explicit に並べる差し替え口。
-/
abbrev PrimeGe5BranchANormalFormXFactorKernelTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    x = t * (p * s) →
    Nat.gcd (z - y) (GN p (z - y) y) = p →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    Nat.Coprime p s →
    ¬ p ∣ y →
    Nat.Coprime (GN p (z - y) y) y →
    Nat.Coprime (p * s ^ p) y →
    Nat.Coprime (s ^ p) y →
    Nat.Coprime p (s ^ p) →
    Nat.Coprime (p * s) y →
    Nat.Coprime (t * (p * s)) y →
    False

/--
`x` 側の最後の差し替え口。

ここでは `x = t * (p * s)` に加え、`x^p` の exactness を
等式と factorization の両方で explicit に受ける。
-/
abbrev PrimeGe5BranchANormalFormXPowExactKernelTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    x = t * (p * s) →
    Nat.gcd (z - y) (GN p (z - y) y) = p →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    Nat.Coprime p s →
    ¬ p ∣ y →
    Nat.Coprime (GN p (z - y) y) y →
    Nat.Coprime (p * s ^ p) y →
    Nat.Coprime (s ^ p) y →
    Nat.Coprime p (s ^ p) →
    Nat.Coprime (p * s) y →
    Nat.Coprime (t * (p * s)) y →
    x ^ p = (t * (p * s)) ^ p →
    (∀ q : ℕ, (x ^ p).factorization q = p * (t * (p * s)).factorization q) →
    False

/--
`x^p` 側 / `gap * GN` 側の exactness 比較だけを残す最終差し替え口。
-/
abbrev PrimeGe5BranchANormalFormPowComparisonKernelTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    x = t * (p * s) →
    Nat.gcd (z - y) (GN p (z - y) y) = p →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    Nat.Coprime p s →
    ¬ p ∣ y →
    Nat.Coprime (GN p (z - y) y) y →
    Nat.Coprime (p * s ^ p) y →
    Nat.Coprime (s ^ p) y →
    Nat.Coprime p (s ^ p) →
    Nat.Coprime (p * s) y →
    Nat.Coprime (t * (p * s)) y →
    x ^ p = (t * (p * s)) ^ p →
    (∀ q : ℕ, (x ^ p).factorization q = p * (t * (p * s)).factorization q) →
    (z - y) * GN p (z - y) y = (t * (p * s)) ^ p →
    (∀ q : ℕ, ((z - y) * GN p (z - y) y).factorization q =
      p * (t * (p * s)).factorization q) →
    False

/--
comparison kernel の equality-part。

shared normal form から `x^p = gap * GN` へ戻すだけの薄い橋を明示分離する。
-/
abbrev PrimeGe5BranchANormalFormPowEqualityPartTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    x = t * (p * s) →
    Nat.gcd (z - y) (GN p (z - y) y) = p →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    Nat.Coprime p s →
    ¬ p ∣ y →
    Nat.Coprime (GN p (z - y) y) y →
    Nat.Coprime (p * s ^ p) y →
    Nat.Coprime (s ^ p) y →
    Nat.Coprime p (s ^ p) →
    Nat.Coprime (p * s) y →
    Nat.Coprime (t * (p * s)) y →
    x ^ p = (t * (p * s)) ^ p →
    (z - y) * GN p (z - y) y = (t * (p * s)) ^ p →
    x ^ p = (z - y) * GN p (z - y) y

/--
comparison kernel の factorization-part。

equality-part で `x^p = gap * GN` を回収した後、指数比較だけに集中する。
-/
abbrev PrimeGe5BranchANormalFormPowFactorizationPartTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    x = t * (p * s) →
    Nat.gcd (z - y) (GN p (z - y) y) = p →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    Nat.Coprime p s →
    ¬ p ∣ y →
    Nat.Coprime (GN p (z - y) y) y →
    Nat.Coprime (p * s ^ p) y →
    Nat.Coprime (s ^ p) y →
    Nat.Coprime p (s ^ p) →
    Nat.Coprime (p * s) y →
    Nat.Coprime (t * (p * s)) y →
    x ^ p = (t * (p * s)) ^ p →
    (∀ q : ℕ, (x ^ p).factorization q = p * (t * (p * s)).factorization q) →
    (z - y) * GN p (z - y) y = (t * (p * s)) ^ p →
    (∀ q : ℕ, ((z - y) * GN p (z - y) y).factorization q =
      p * (t * (p * s)).factorization q) →
    x ^ p = (z - y) * GN p (z - y) y →
    False

/--
factorization-part の `q = p` 側。

`p`-進指数の比較だけを isolated に受ける差し替え口。
-/
abbrev PrimeGe5BranchANormalFormPowFactorizationAtPTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    x = t * (p * s) →
    Nat.gcd (z - y) (GN p (z - y) y) = p →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    Nat.Coprime p s →
    ¬ p ∣ y →
    Nat.Coprime (GN p (z - y) y) y →
    Nat.Coprime (p * s ^ p) y →
    Nat.Coprime (s ^ p) y →
    Nat.Coprime p (s ^ p) →
    Nat.Coprime (p * s) y →
    Nat.Coprime (t * (p * s)) y →
    x ^ p = (t * (p * s)) ^ p →
    (x ^ p).factorization p = p * (t * (p * s)).factorization p →
    (z - y) * GN p (z - y) y = (t * (p * s)) ^ p →
    ((z - y) * GN p (z - y) y).factorization p =
      p * (t * (p * s)).factorization p →
    x ^ p = (z - y) * GN p (z - y) y →
    False

/--
factorization-part の `q ≠ p` 側。

`q ≠ p` に対する指数比較だけを isolated に受ける差し替え口。
-/
abbrev PrimeGe5BranchANormalFormPowFactorizationNePTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    x = t * (p * s) →
    Nat.gcd (z - y) (GN p (z - y) y) = p →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    Nat.Coprime p s →
    ¬ p ∣ y →
    Nat.Coprime (GN p (z - y) y) y →
    Nat.Coprime (p * s ^ p) y →
    Nat.Coprime (s ^ p) y →
    Nat.Coprime p (s ^ p) →
    Nat.Coprime (p * s) y →
    Nat.Coprime (t * (p * s)) y →
    x ^ p = (t * (p * s)) ^ p →
    (∀ q : ℕ, q ≠ p → (x ^ p).factorization q = p * (t * (p * s)).factorization q) →
    (z - y) * GN p (z - y) y = (t * (p * s)) ^ p →
    (∀ q : ℕ, q ≠ p → ((z - y) * GN p (z - y) y).factorization q =
      p * (t * (p * s)).factorization q) →
    x ^ p = (z - y) * GN p (z - y) y →
    False

/--
`q = p` 側の valuation 文脈だけを explicit に受ける差し替え口。
-/
abbrev PrimeGe5BranchANormalFormPowFactorizationAtPValuationTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    x = t * (p * s) →
    Nat.gcd (z - y) (GN p (z - y) y) = p →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    Nat.Coprime p s →
    ¬ p ∣ y →
    Nat.Coprime (GN p (z - y) y) y →
    Nat.Coprime (p * s ^ p) y →
    Nat.Coprime (s ^ p) y →
    Nat.Coprime p (s ^ p) →
    Nat.Coprime (p * s) y →
    Nat.Coprime (t * (p * s)) y →
    x ^ p = (t * (p * s)) ^ p →
    (x ^ p).factorization p = p * (t * (p * s)).factorization p →
    (z - y) * GN p (z - y) y = (t * (p * s)) ^ p →
    ((z - y) * GN p (z - y) y).factorization p =
      p * (t * (p * s)).factorization p →
    x ^ p = (z - y) * GN p (z - y) y →
    (∃ m : ℕ, padicValNat p (z - y) = (p - 1) + p * m) →
    padicValNat p (GN p (z - y) y) = 1 →
    False

/--
`q ≠ p` 側の factorization spine だけを explicit に受ける差し替え口。
-/
abbrev PrimeGe5BranchANormalFormPowFactorizationNePSpineTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    x = t * (p * s) →
    Nat.gcd (z - y) (GN p (z - y) y) = p →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    Nat.Coprime p s →
    ¬ p ∣ y →
    Nat.Coprime (GN p (z - y) y) y →
    Nat.Coprime (p * s ^ p) y →
    Nat.Coprime (s ^ p) y →
    Nat.Coprime p (s ^ p) →
    Nat.Coprime (p * s) y →
    Nat.Coprime (t * (p * s)) y →
    x ^ p = (t * (p * s)) ^ p →
    (∀ q : ℕ, q ≠ p → (x ^ p).factorization q = p * (t * (p * s)).factorization q) →
    (z - y) * GN p (z - y) y = (t * (p * s)) ^ p →
    (∀ q : ℕ, q ≠ p → ((z - y) * GN p (z - y) y).factorization q =
      p * (t * (p * s)).factorization q) →
    x ^ p = (z - y) * GN p (z - y) y →
    (∀ q : ℕ, Nat.Prime q → q ≠ p → p ∣ (z - y).factorization q) →
    (∀ q : ℕ, Nat.Prime q → q ≠ p → p ∣ (GN p (z - y) y).factorization q) →
    False

/--
shape-value refuter は、最終的には witness-kernel 1 本の注入へ還元する。
-/
theorem primeGe5BranchAShapeValueToRefuter_of_witness_kernel
    (hKernel : PrimeGe5BranchAShapeWitnessKernelTarget) :
    PrimeGe5BranchAShapeValueToRefuterTarget := by
  intro p x y z hpack hp_dvd_gap hShape
  rcases hShape with ⟨t, ht⟩
  exact hKernel hpack hp_dvd_gap
    (primeGe5BranchAShapeWitness_to_descent_input hpack hp_dvd_gap ht)

/--
normal-form refuter があれば、witness kernel は薄い橋で閉じる。
-/
theorem primeGe5BranchAShapeWitnessKernel_of_normalFormRefuter
    (hRef : PrimeGe5BranchANormalFormRefuterTarget) :
    PrimeGe5BranchAShapeWitnessKernelTarget := by
  intro p x y z t hpack hp_dvd_gap hInput
  rcases primeGe5BranchANormalForm_of_witness hpack hp_dvd_gap hInput.gapShape with
    ⟨s, hsGN, hsx⟩
  exact hRef hpack hp_dvd_gap hInput.gapShape hsGN hsx

/--
normal form refuter は、最後の arithmetic kernel 1 本へ further reduce できる。
-/
theorem primeGe5BranchANormalFormRefuter_of_arithmetic_kernel
    (hKernel : PrimeGe5BranchANormalFormArithmeticKernelTarget) :
    PrimeGe5BranchANormalFormRefuterTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx
  exact hKernel hpack hp_dvd_gap hgap hsGN hsx
    (primeGe5BranchANormalForm_gcd_gap_GN_eq_p_default hpack hp_dvd_gap hgap hsGN)
    (primeGe5BranchANormalForm_coprime_ts_default hpack hp_dvd_gap hgap hsGN)
    (primeGe5BranchANormalForm_coprime_t_right hpack hsx)
    (primeGe5BranchANormalForm_coprime_s_right hpack hsx)
    (primeGe5BranchANormalForm_prime_not_dvd_s_default hpack hp_dvd_gap hgap hsGN)

/--
arithmetic kernel は、`p ⟂ s` と `p ∤ y` を明示入力にした
さらに小さい local kernel へ reduce できる。
-/
theorem primeGe5BranchANormalFormArithmeticKernel_of_localCoprimeKernel
    (hKernel : PrimeGe5BranchANormalFormLocalCoprimeKernelTarget) :
    PrimeGe5BranchANormalFormArithmeticKernelTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx hgcd_eq hp_cop_ts hp_cop_ty hp_cop_sy hp_not_dvd_s
  exact hKernel hpack hp_dvd_gap hgap hsGN hsx hgcd_eq hp_cop_ts hp_cop_ty hp_cop_sy hp_not_dvd_s
    (primeGe5BranchANormalForm_coprime_p_s_default hpack hp_dvd_gap hgap hsGN)
    (primeGe5BranchANormalForm_prime_not_dvd_y_default hpack hp_dvd_gap)

/--
local coprime kernel は、`GN ⟂ y` を explicit に受ける
さらに小さい GN-side kernel へ reduce できる。
-/
theorem primeGe5BranchANormalFormLocalCoprimeKernel_of_GNRightKernel
    (hKernel : PrimeGe5BranchANormalFormGNRightKernelTarget) :
    PrimeGe5BranchANormalFormLocalCoprimeKernelTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx hgcd_eq hp_cop_ts hp_cop_ty hp_cop_sy hp_not_dvd_s hp_cop_ps hp_not_dvd_y
  exact hKernel hpack hp_dvd_gap hgap hsGN hsx hgcd_eq hp_cop_ts hp_cop_ty hp_cop_sy hp_not_dvd_s hp_cop_ps hp_not_dvd_y
    (primeGe5BranchANormalForm_coprime_GN_right_default hpack)

/--
GN-side kernel は、`p * s^p ⟂ y` と `s^p ⟂ y` を explicit に受ける
さらに小さい factor kernel へ reduce できる。
-/
theorem primeGe5BranchANormalFormGNRightKernel_of_factorKernel
    (hKernel : PrimeGe5BranchANormalFormGNFactorKernelTarget) :
    PrimeGe5BranchANormalFormGNRightKernelTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx hgcd_eq hp_cop_ts hp_cop_ty hp_cop_sy hp_not_dvd_s hp_cop_ps hp_not_dvd_y hp_cop_GNy
  exact hKernel hpack hp_dvd_gap hgap hsGN hsx hgcd_eq hp_cop_ts hp_cop_ty hp_cop_sy hp_not_dvd_s hp_cop_ps hp_not_dvd_y hp_cop_GNy
    (primeGe5BranchANormalForm_coprime_pspow_y_default hpack hsGN hp_cop_GNy)
    (primeGe5BranchANormalForm_coprime_spow_y_default hpack hsGN hp_cop_GNy)

/--
GN factor kernel は、`p ⟂ s^p` と `p * s ⟂ y` を explicit に受ける
さらに小さい linear-factor kernel へ reduce できる。
-/
theorem primeGe5BranchANormalFormGNFactorKernel_of_linearFactorKernel
    (hKernel : PrimeGe5BranchANormalFormGNLinearFactorKernelTarget) :
    PrimeGe5BranchANormalFormGNFactorKernelTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx hgcd_eq hp_cop_ts hp_cop_ty hp_cop_sy hp_not_dvd_s hp_cop_ps hp_not_dvd_y hp_cop_GNy hp_cop_pspow_y hp_cop_spow_y
  exact hKernel hpack hp_dvd_gap hgap hsGN hsx hgcd_eq hp_cop_ts hp_cop_ty hp_cop_sy hp_not_dvd_s hp_cop_ps hp_not_dvd_y hp_cop_GNy hp_cop_pspow_y hp_cop_spow_y
    (primeGe5BranchANormalForm_coprime_p_spow_default hpack hp_dvd_gap hgap hsGN hp_cop_ps)
    (primeGe5BranchANormalForm_coprime_ps_y_default hpack hp_dvd_gap hgap hsGN hsx hp_cop_sy)

/--
GN linear-factor kernel は、`x = t * (p * s)` と
`Nat.Coprime (t * (p * s)) y` を explicit に受ける
さらに小さい x-factor kernel へ reduce できる。
-/
theorem primeGe5BranchANormalFormGNLinearFactorKernel_of_xFactorKernel
    (hKernel : PrimeGe5BranchANormalFormXFactorKernelTarget) :
    PrimeGe5BranchANormalFormGNLinearFactorKernelTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx hgcd_eq hp_cop_ts hp_cop_ty hp_cop_sy hp_not_dvd_s hp_cop_ps hp_not_dvd_y hp_cop_GNy hp_cop_pspow_y hp_cop_spow_y hp_cop_pspow hp_cop_ps_y
  exact hKernel hpack hp_dvd_gap hgap hsGN hsx
    (primeGe5BranchANormalForm_x_eq_t_mul_ps hpack hp_dvd_gap hgap hsGN hsx)
    hgcd_eq hp_cop_ts hp_cop_ty hp_cop_sy hp_not_dvd_s hp_cop_ps hp_not_dvd_y hp_cop_GNy hp_cop_pspow_y hp_cop_spow_y hp_cop_pspow hp_cop_ps_y
    (primeGe5BranchANormalForm_coprime_t_ps_default hpack hp_dvd_gap hgap hsGN hsx hp_cop_ty hp_cop_ps_y)

/--
X-factor kernel は、`x^p` の基準形 exactness を explicit に受ける
さらに小さい xpow-exact kernel へ reduce できる。
-/
theorem primeGe5BranchANormalFormXFactorKernel_of_xpowExactKernel
    (hKernel : PrimeGe5BranchANormalFormXPowExactKernelTarget) :
    PrimeGe5BranchANormalFormXFactorKernelTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx hx_tps hgcd_eq hp_cop_ts hp_cop_ty hp_cop_sy hp_not_dvd_s hp_cop_ps hp_not_dvd_y hp_cop_GNy hp_cop_pspow_y hp_cop_spow_y hp_cop_pspow hp_cop_ps_y hp_cop_tps_y
  exact hKernel hpack hp_dvd_gap hgap hsGN hsx hx_tps hgcd_eq hp_cop_ts hp_cop_ty hp_cop_sy hp_not_dvd_s hp_cop_ps hp_not_dvd_y hp_cop_GNy hp_cop_pspow_y hp_cop_spow_y hp_cop_pspow hp_cop_ps_y hp_cop_tps_y
    (primeGe5BranchANormalForm_xpow_eq_tps_pow hpack hp_dvd_gap hgap hsGN hx_tps)
    (fun q => primeGe5BranchANormalForm_xpow_factorization_exact hpack hp_dvd_gap hgap hsGN hx_tps)

/--
X-pow exact kernel は、`gap * GN` 側の exactness も explicit に受ける
comparison kernel へ further reduce できる。
-/
theorem primeGe5BranchANormalFormXPowExactKernel_of_powComparisonKernel
    (hKernel : PrimeGe5BranchANormalFormPowComparisonKernelTarget) :
    PrimeGe5BranchANormalFormXPowExactKernelTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx hx_tps hgcd_eq hp_cop_ts hp_cop_ty hp_cop_sy hp_not_dvd_s hp_cop_ps hp_not_dvd_y hp_cop_GNy hp_cop_pspow_y hp_cop_spow_y hp_cop_pspow hp_cop_ps_y hp_cop_tps_y hxpow_tps hfac_xpow
  exact hKernel hpack hp_dvd_gap hgap hsGN hsx hx_tps hgcd_eq hp_cop_ts hp_cop_ty hp_cop_sy hp_not_dvd_s hp_cop_ps hp_not_dvd_y hp_cop_GNy hp_cop_pspow_y hp_cop_spow_y hp_cop_pspow hp_cop_ps_y hp_cop_tps_y hxpow_tps hfac_xpow
    (primeGe5BranchANormalForm_gapGN_eq_tps_pow hpack hp_dvd_gap hgap hsGN)
    (fun q => primeGe5BranchANormalForm_gapGN_factorization_exact hpack hp_dvd_gap hgap hsGN)

/--
equality-part と factorization-part が揃えば、comparison kernel は橋だけで閉じる。
-/
theorem primeGe5BranchANormalFormPowComparisonKernel_of_parts
    (hEqPart : PrimeGe5BranchANormalFormPowEqualityPartTarget)
    (hFacPart : PrimeGe5BranchANormalFormPowFactorizationPartTarget) :
    PrimeGe5BranchANormalFormPowComparisonKernelTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx hx_tps hgcd_eq hp_cop_ts hp_cop_ty hp_cop_sy hp_not_dvd_s hp_cop_ps hp_not_dvd_y hp_cop_GNy hp_cop_pspow_y hp_cop_spow_y hp_cop_pspow hp_cop_ps_y hp_cop_tps_y hxpow_tps hfac_xpow hgapGN_tps hfac_gapGN
  have hEq :
      x ^ p = (z - y) * GN p (z - y) y :=
    hEqPart hpack hp_dvd_gap hgap hsGN hsx hx_tps hgcd_eq hp_cop_ts hp_cop_ty hp_cop_sy hp_not_dvd_s hp_cop_ps hp_not_dvd_y hp_cop_GNy hp_cop_pspow_y hp_cop_spow_y hp_cop_pspow hp_cop_ps_y hp_cop_tps_y hxpow_tps hgapGN_tps
  exact hFacPart hpack hp_dvd_gap hgap hsGN hsx hx_tps hgcd_eq hp_cop_ts hp_cop_ty hp_cop_sy hp_not_dvd_s hp_cop_ps hp_not_dvd_y hp_cop_GNy hp_cop_pspow_y hp_cop_spow_y hp_cop_pspow hp_cop_ps_y hp_cop_tps_y hxpow_tps hfac_xpow hgapGN_tps hfac_gapGN hEq

/--
comparison kernel の equality-part 実装入口。

ここは obstruction ではなく、pack 由来の `x^p = gap * GN` を
explicit に戻すだけの薄い橋である。
-/
theorem primeGe5BranchANormalFormPowEqualityPart_default :
    PrimeGe5BranchANormalFormPowEqualityPartTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx hx_tps hgcd_eq hp_cop_ts hp_cop_ty hp_cop_sy hp_not_dvd_s hp_cop_ps hp_not_dvd_y hp_cop_GNy hp_cop_pspow_y hp_cop_spow_y hp_cop_pspow hp_cop_ps_y hp_cop_tps_y hxpow_tps hgapGN_tps
  let _ := t
  let _ := s
  let _ := hp_dvd_gap
  let _ := hgap
  let _ := hsGN
  let _ := hsx
  let _ := hx_tps
  let _ := hgcd_eq
  let _ := hp_cop_ts
  let _ := hp_cop_ty
  let _ := hp_cop_sy
  let _ := hp_not_dvd_s
  let _ := hp_cop_ps
  let _ := hp_not_dvd_y
  let _ := hp_cop_GNy
  let _ := hp_cop_pspow_y
  let _ := hp_cop_spow_y
  let _ := hp_cop_pspow
  let _ := hp_cop_ps_y
  let _ := hp_cop_tps_y
  let _ := hxpow_tps
  let _ := hgapGN_tps
  simpa [PrimeGe5CounterexamplePack.gap] using hpack.xpow_eq_gap_mul_GN

/--
`q = p` / `q ≠ p` の 2 部品が揃えば、factorization-part は橋だけで閉じる。
-/
theorem primeGe5BranchANormalFormPowFactorizationPart_of_cases
    (hAtP : PrimeGe5BranchANormalFormPowFactorizationAtPTarget)
    (_hNeP : PrimeGe5BranchANormalFormPowFactorizationNePTarget) :
    PrimeGe5BranchANormalFormPowFactorizationPartTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx hx_tps hgcd_eq hp_cop_ts hp_cop_ty hp_cop_sy hp_not_dvd_s hp_cop_ps hp_not_dvd_y hp_cop_GNy hp_cop_pspow_y hp_cop_spow_y hp_cop_pspow hp_cop_ps_y hp_cop_tps_y hxpow_tps hfac_xpow hgapGN_tps hfac_gapGN hEq
  have hAtPFalse : False := by
    exact hAtP hpack hp_dvd_gap hgap hsGN hsx hx_tps hgcd_eq hp_cop_ts hp_cop_ty hp_cop_sy hp_not_dvd_s hp_cop_ps hp_not_dvd_y hp_cop_GNy hp_cop_pspow_y hp_cop_spow_y hp_cop_pspow hp_cop_ps_y hp_cop_tps_y hxpow_tps
      (hfac_xpow p) hgapGN_tps (hfac_gapGN p) hEq
  exact hAtPFalse

/--
`q ≠ p` 側だけで十分なら、factorization-part はそのまま thin bridge で閉じられる。

現状の mainline では、true obstruction はこちらに寄ると見てよい。
-/
theorem primeGe5BranchANormalFormPowFactorizationPart_of_neP
    (hNeP : PrimeGe5BranchANormalFormPowFactorizationNePTarget) :
    PrimeGe5BranchANormalFormPowFactorizationPartTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx hx_tps hgcd_eq hp_cop_ts hp_cop_ty hp_cop_sy hp_not_dvd_s hp_cop_ps hp_not_dvd_y hp_cop_GNy hp_cop_pspow_y hp_cop_spow_y hp_cop_pspow hp_cop_ps_y hp_cop_tps_y hxpow_tps hfac_xpow hgapGN_tps hfac_gapGN hEq
  exact hNeP hpack hp_dvd_gap hgap hsGN hsx hx_tps hgcd_eq hp_cop_ts hp_cop_ty hp_cop_sy hp_not_dvd_s hp_cop_ps hp_not_dvd_y hp_cop_GNy hp_cop_pspow_y hp_cop_spow_y hp_cop_pspow hp_cop_ps_y hp_cop_tps_y hxpow_tps
    (fun q hqp => hfac_xpow q)
    hgapGN_tps
    (fun q hqp => hfac_gapGN q)
    hEq

/--
valuation kernel があれば、`q = p` 側 factorization target は薄い橋で閉じる。
-/
theorem primeGe5BranchANormalFormPowFactorizationAtP_of_valuationKernel
    (hVal : PrimeGe5BranchANormalFormPowFactorizationAtPValuationTarget) :
    PrimeGe5BranchANormalFormPowFactorizationAtPTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx hx_tps hgcd_eq hp_cop_ts hp_cop_ty hp_cop_sy hp_not_dvd_s hp_cop_ps hp_not_dvd_y hp_cop_GNy hp_cop_pspow_y hp_cop_spow_y hp_cop_pspow hp_cop_ps_y hp_cop_tps_y hxpow_tps hfac_xpow_p hgapGN_tps hfac_gapGN_p hEq
  have hgapVal : ∃ m : ℕ, padicValNat p (z - y) = (p - 1) + p * m := by
    rcases primeGe5BranchAShapeFactorization_p_of_value hpack hp_dvd_gap ⟨t, hgap⟩ with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have hgap_ne0 : (z - y) ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt hpack.hyz_lt)
    calc
      padicValNat p (z - y) = (z - y).factorization p := by
        exact padicValNat_eq_factorization hpack.hp hgap_ne0
      _ = (p - 1) + p * m := hm
  have hGNVal : padicValNat p (GN p (z - y) y) = 1 := by
    exact primeGe5BranchAPadicValNat_eq_one_of_dvd_not_sq hpack.hp
      (by
        simpa using (primeGe5BranchAP_dvd_GN_and_not_sq_when_p_dvd_gap hpack hp_dvd_gap).1)
      (by
        simpa using (primeGe5BranchAP_dvd_GN_and_not_sq_when_p_dvd_gap hpack hp_dvd_gap).2)
  exact hVal hpack hp_dvd_gap hgap hsGN hsx hx_tps hgcd_eq hp_cop_ts hp_cop_ty hp_cop_sy hp_not_dvd_s hp_cop_ps hp_not_dvd_y hp_cop_GNy hp_cop_pspow_y hp_cop_spow_y hp_cop_pspow hp_cop_ps_y hp_cop_tps_y hxpow_tps hfac_xpow_p hgapGN_tps hfac_gapGN_p hEq hgapVal hGNVal

/--
spine kernel があれば、`q ≠ p` 側 factorization target は薄い橋で閉じる。
-/
theorem primeGe5BranchANormalFormPowFactorizationNeP_of_spineKernel
    (hSpine : PrimeGe5BranchANormalFormPowFactorizationNePSpineTarget) :
    PrimeGe5BranchANormalFormPowFactorizationNePTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx hx_tps hgcd_eq hp_cop_ts hp_cop_ty hp_cop_sy hp_not_dvd_s hp_cop_ps hp_not_dvd_y hp_cop_GNy hp_cop_pspow_y hp_cop_spow_y hp_cop_pspow hp_cop_ps_y hp_cop_tps_y hxpow_tps hfac_xpow_ne hgapGN_tps hfac_gapGN_ne hEq
  exact hSpine hpack hp_dvd_gap hgap hsGN hsx hx_tps hgcd_eq hp_cop_ts hp_cop_ty hp_cop_sy hp_not_dvd_s hp_cop_ps hp_not_dvd_y hp_cop_GNy hp_cop_pspow_y hp_cop_spow_y hp_cop_pspow hp_cop_ps_y hp_cop_tps_y hxpow_tps hfac_xpow_ne hgapGN_tps hfac_gapGN_ne hEq
    (fun q _hqP hqp =>
      primeGe5BranchAShapeFactorization_ne_p_of_value hpack hp_dvd_gap ⟨t, hgap⟩ q hqp)
    (fun q hqP hqp =>
      primeGe5BranchAGN_factorization_ne_p_math hpack hp_dvd_gap hqP hqp)

/--
`q ≠ p` 側の spine kernel 実装入口。
-/
theorem primeGe5BranchANormalFormPowFactorizationNePSpine_default :
    PrimeGe5BranchANormalFormPowFactorizationNePSpineTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx hx_tps hgcd_eq hp_cop_ts hp_cop_ty hp_cop_sy hp_not_dvd_s hp_cop_ps hp_not_dvd_y hp_cop_GNy hp_cop_pspow_y hp_cop_spow_y hp_cop_pspow hp_cop_ps_y hp_cop_tps_y hxpow_tps hfac_xpow_ne hgapGN_tps hfac_gapGN_ne hEq hgapFac_ne hGNFac_ne
  let _ := p
  let _ := x
  let _ := y
  let _ := z
  let _ := t
  let _ := s
  let _ := hpack
  let _ := hp_dvd_gap
  let _ := hgap
  let _ := hsGN
  let _ := hsx
  let _ := hx_tps
  let _ := hgcd_eq
  let _ := hp_cop_ts
  let _ := hp_cop_ty
  let _ := hp_cop_sy
  let _ := hp_not_dvd_s
  let _ := hp_cop_ps
  let _ := hp_not_dvd_y
  let _ := hp_cop_GNy
  let _ := hp_cop_pspow_y
  let _ := hp_cop_spow_y
  let _ := hp_cop_pspow
  let _ := hp_cop_ps_y
  let _ := hp_cop_tps_y
  let _ := hxpow_tps
  let _ := hfac_xpow_ne
  let _ := hgapGN_tps
  let _ := hfac_gapGN_ne
  let _ := hEq
  let _ := hgapFac_ne
  let _ := hGNFac_ne
  /-
  TODO:
  1. `q ≠ p` の指数比較を、
     gap/GN の no-shared / factorization spine へ戻して読む。
  2. 必要なら `Nat.Coprime t s` を `q ≠ p` kernel 専用 helper に下ろす。
  -/
  sorry

/--
factorization-part の `q ≠ p` 側実装入口。

ここでは `q ≠ p` の指数比較だけを isolated に受ける。
-/
theorem primeGe5BranchANormalFormPowFactorizationNeP_default :
    PrimeGe5BranchANormalFormPowFactorizationNePTarget := by
  exact primeGe5BranchANormalFormPowFactorizationNeP_of_spineKernel
    primeGe5BranchANormalFormPowFactorizationNePSpine_default

/--
comparison kernel の factorization-part 実装入口。

ここでは prime ごとの指数比較だけを残し、
comparison の本当の算術 obstruction を 1 点へ集約する。
-/
theorem primeGe5BranchANormalFormPowFactorizationPart_default :
    PrimeGe5BranchANormalFormPowFactorizationPartTarget := by
  exact primeGe5BranchANormalFormPowFactorizationPart_of_neP
    primeGe5BranchANormalFormPowFactorizationNeP_default

/--
X-pow exact kernel の実装入口。

ここでは `x^p = (t * (p * s))^p` と factorization exactness まで explicit に受け、
最後の `x^p` 側衝突だけを残す。
-/
theorem primeGe5BranchANormalFormPowComparisonKernel_default :
    PrimeGe5BranchANormalFormPowComparisonKernelTarget := by
  exact primeGe5BranchANormalFormPowComparisonKernel_of_parts
    primeGe5BranchANormalFormPowEqualityPart_default
    primeGe5BranchANormalFormPowFactorizationPart_default

/--
X-pow exact kernel の実装入口。

ここでは `x^p` 側 exactness に加え、`gap * GN` 側 exactness も explicit に受け、
最後の比較核だけを残す。
-/
theorem primeGe5BranchANormalFormXPowExactKernel_default :
    PrimeGe5BranchANormalFormXPowExactKernelTarget := by
  exact primeGe5BranchANormalFormXPowExactKernel_of_powComparisonKernel
    primeGe5BranchANormalFormPowComparisonKernel_default

/--
x-factor kernel の実装入口。

ここでは `x = t * (p * s)` と `Nat.Coprime (t * (p * s)) y`
まで explicit に受け、最後の `x` 側 exactness との衝突だけを残す。
-/
theorem primeGe5BranchANormalFormXFactorKernel_default :
    PrimeGe5BranchANormalFormXFactorKernelTarget := by
  exact primeGe5BranchANormalFormXFactorKernel_of_xpowExactKernel
    primeGe5BranchANormalFormXPowExactKernel_default

/--
GN linear-factor kernel の実装入口。

ここでは `Nat.Coprime p (s ^ p)` と `Nat.Coprime (p * s) y`
まで explicit に受け、最後の線形/冪因子の局所衝突だけを残す。
-/
theorem primeGe5BranchANormalFormGNLinearFactorKernel_default :
    PrimeGe5BranchANormalFormGNLinearFactorKernelTarget := by
  exact primeGe5BranchANormalFormGNLinearFactorKernel_of_xFactorKernel
    primeGe5BranchANormalFormXFactorKernel_default

/--
GN factor kernel の実装入口。

ここでは `p * s^p ⟂ y` と `s^p ⟂ y` まで explicit に受け、
最後の factor-level 局所衝突だけを残す。
-/
theorem primeGe5BranchANormalFormGNFactorKernel_default :
    PrimeGe5BranchANormalFormGNFactorKernelTarget := by
  exact primeGe5BranchANormalFormGNFactorKernel_of_linearFactorKernel
    primeGe5BranchANormalFormGNLinearFactorKernel_default

/--
GN-side local kernel の実装入口。

ここでは `GN ⟂ y` まで explicit に受け取り、
最後の `GN` 側局所衝突だけを残す。
-/
theorem primeGe5BranchANormalFormGNRightKernel_default :
    PrimeGe5BranchANormalFormGNRightKernelTarget := by
  exact primeGe5BranchANormalFormGNRightKernel_of_factorKernel
    primeGe5BranchANormalFormGNFactorKernel_default

/--
local coprime kernel の実装入口。

ここでは `p ⟂ s` と `p ∤ y` まで explicit に並べた上で、
最後の局所 gcd / valuation 衝突だけを扱う。
-/
theorem primeGe5BranchANormalFormLocalCoprimeKernel_default :
    PrimeGe5BranchANormalFormLocalCoprimeKernelTarget := by
  exact primeGe5BranchANormalFormLocalCoprimeKernel_of_GNRightKernel
    primeGe5BranchANormalFormGNRightKernel_default

/--
Branch A arithmetic kernel の実装入口。

未完核を normal form そのものから切り離し、
抽出済みの算術拘束だけへ局所化する。
-/
theorem primeGe5BranchANormalFormArithmeticKernel_default :
    PrimeGe5BranchANormalFormArithmeticKernelTarget := by
  exact primeGe5BranchANormalFormArithmeticKernel_of_localCoprimeKernel
    primeGe5BranchANormalFormLocalCoprimeKernel_default

/--
Branch A の normal-form refuter 実装入口。

ここが clean な局所 gcd / valuation 衝突数学へ置換される最終穴。
-/
theorem primeGe5BranchANormalFormRefuter_default :
    PrimeGe5BranchANormalFormRefuterTarget := by
  exact primeGe5BranchANormalFormRefuter_of_arithmetic_kernel
    primeGe5BranchANormalFormArithmeticKernel_default

/--
Branch A の shape-witness kernel 実装入口。

ここが clean descent / shrink 数学へ最終的に置換される本当の残穴。
-/
theorem primeGe5BranchAShapeWitnessKernel_default :
    PrimeGe5BranchAShapeWitnessKernelTarget := by
  exact primeGe5BranchAShapeWitnessKernel_of_normalFormRefuter
    primeGe5BranchANormalFormRefuter_default

/-- Branch A の shape-value refuter 実装入口。 -/
theorem primeGe5BranchAShapeValueToRefuter_default :
    PrimeGe5BranchAShapeValueToRefuterTarget :=
  primeGe5BranchAShapeValueToRefuter_of_witness_kernel
    primeGe5BranchAShapeWitnessKernel_default

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
  exact primeGe5BranchARefuter_of_shape_pipeline
    primeGe5BranchAShapeFactorization_default
    primeGe5BranchAShapeValueToRefuter_default

end DkMath.FLT
