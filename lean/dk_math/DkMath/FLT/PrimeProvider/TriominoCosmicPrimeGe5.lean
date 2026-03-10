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
- ここでは `so#rry` を導入しない。
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

/--
TODO-3 の最薄部:
`y ≤ z` かつ `Nat.Coprime y z` なら、差 `z - y` と `y` も互いに素。
-/
lemma coprime_sub_of_coprime
    {y z : ℕ} (hyz : y ≤ z) (hcop : Nat.Coprime y z) :
    Nat.Coprime (z - y) y := by
  have hy_sub : Nat.Coprime y (z - y) :=
    (Nat.coprime_sub_self_right hyz).2 hcop
  simpa [Nat.coprime_comm] using hy_sub

/--
TODO-3 の残り:
`x^p + y^p = z^p` と `Nat.Coprime x y` から `Nat.Coprime y z` を回収する。
-/
lemma coprime_right_of_add_pow_eq_pow
    {p x y z : ℕ}
    (hp : Nat.Prime p)
    (hxy : Nat.Coprime x y)
    (hEq : x ^ p + y ^ p = z ^ p) :
    Nat.Coprime y z := by
  refine (Nat.coprime_iff_gcd_eq_one).2 ?_
  by_contra hg1
  have hg_ne1 : Nat.gcd y z ≠ 1 := by
    simpa using hg1
  rcases Nat.exists_prime_and_dvd (n := Nat.gcd y z) hg_ne1 with ⟨q, hqPrime, hq_dvd_g⟩
  have hq_dvd_y : q ∣ y := dvd_trans hq_dvd_g (Nat.gcd_dvd_left y z)
  have hq_dvd_z : q ∣ z := dvd_trans hq_dvd_g (Nat.gcd_dvd_right y z)
  have hq_dvd_yp : q ∣ y ^ p :=
    dvd_trans hq_dvd_y (dvd_pow_self y hp.ne_zero)
  have hq_dvd_zp : q ∣ z ^ p :=
    dvd_trans hq_dvd_z (dvd_pow_self z hp.ne_zero)
  have hq_dvd_sum : q ∣ x ^ p + y ^ p := by
    rw [hEq]
    exact hq_dvd_zp
  have hq_dvd_xp : q ∣ x ^ p := by
    exact (Nat.dvd_add_left hq_dvd_yp).1 hq_dvd_sum
  have hq_dvd_x : q ∣ x := hqPrime.dvd_of_dvd_pow hq_dvd_xp
  have hnot : ¬ Nat.Coprime x y :=
    Nat.not_coprime_of_dvd_of_dvd (Nat.Prime.one_lt hqPrime) hq_dvd_x hq_dvd_y
  exact hnot hxy

/--
`FLT_prime_ge5` で扱う primitive 反例の標準入力束。
`TODO-2` / `TODO-3` の仮定を 1 箇所へ固定する。
-/
structure PrimeCounterexamplePack (p x y z : ℕ) : Prop where
  hp : Nat.Prime p
  hxy : Nat.Coprime x y
  hyz : y ≤ z
  hyz_lt : y < z
  hEq : x ^ p + y ^ p = z ^ p

namespace PrimeCounterexamplePack

/-- 差（gap）`u := z - y`。 -/
def gap {p x y z : ℕ} (_h : PrimeCounterexamplePack p x y z) : ℕ :=
  z - y

/-- `gap` は正。 -/
lemma gap_pos {p x y z : ℕ} (h : PrimeCounterexamplePack p x y z) :
    0 < h.gap := by
  exact Nat.sub_pos_of_lt h.hyz_lt

/-- `gap` と `y` は互いに素。`TODO-3` の完成版。 -/
lemma gap_coprime_right {p x y z : ℕ} (h : PrimeCounterexamplePack p x y z) :
    Nat.Coprime h.gap y := by
  have hyz_coprime : Nat.Coprime y z :=
    coprime_right_of_add_pow_eq_pow h.hp h.hxy h.hEq
  simpa [PrimeCounterexamplePack.gap] using
    (coprime_sub_of_coprime h.hyz hyz_coprime)

end PrimeCounterexamplePack

/--
`TODO-2` 以降で使う、prime-ge5 専用の primitive 反例入力束。
`p = 2, 3` を排除し、Body/Gap 不変量が真になりうる領域へ制限する。
さらに、Zsigmondy 系の入口に必要な非零条件もここで固定する。
-/
structure PrimeGe5CounterexamplePack (p x y z : ℕ) : Prop
    extends PrimeCounterexamplePack p x y z where
  hp5 : 5 ≤ p
  hx0 : x ≠ 0
  hy0 : y ≠ 0
  hz0 : z ≠ 0

namespace PrimeGe5CounterexamplePack

/-- 差（gap）`u := z - y`。 -/
def gap {p x y z : ℕ} (h : PrimeGe5CounterexamplePack p x y z) : ℕ :=
  h.toPrimeCounterexamplePack.gap

/-- `gap` は正。 -/
lemma gap_pos {p x y z : ℕ} (h : PrimeGe5CounterexamplePack p x y z) :
    0 < h.gap := by
  simpa [PrimeGe5CounterexamplePack.gap] using
    h.toPrimeCounterexamplePack.gap_pos

/-- `gap` と `y` は互いに素。 -/
lemma gap_coprime_right {p x y z : ℕ} (h : PrimeGe5CounterexamplePack p x y z) :
    Nat.Coprime h.gap y := by
  simpa [PrimeGe5CounterexamplePack.gap] using
    h.toPrimeCounterexamplePack.gap_coprime_right

/-- FLT 反例形から `x^p = gap * GN p gap y` を回収する。 -/
lemma xpow_eq_gap_mul_GN {p x y z : ℕ} (h : PrimeGe5CounterexamplePack p x y z) :
    x ^ p = h.gap * DkMath.CosmicFormulaBinom.GN p h.gap y := by
  simpa [PrimeGe5CounterexamplePack.gap] using
    (pow_eq_sub_mul_GN_of_add_pow_eq p x y z h.hyz h.hEq)

/-- `p ∣ gap` なら、`gap ⟂ y` より `p ∤ y`。 -/
lemma prime_not_dvd_right_of_prime_dvd_gap
    {p x y z : ℕ} (h : PrimeGe5CounterexamplePack p x y z)
    (hp_dvd_gap : p ∣ h.gap) :
    ¬ p ∣ y := by
  intro hp_dvd_y
  have hnot : ¬ Nat.Coprime h.gap y :=
    Nat.not_coprime_of_dvd_of_dvd (Nat.Prime.one_lt h.hp) hp_dvd_gap hp_dvd_y
  exact hnot h.gap_coprime_right

/-- `x ≠ 0` から `0 < x` を回収する。 -/
lemma x_pos {p x y z : ℕ} (h : PrimeGe5CounterexamplePack p x y z) :
    0 < x :=
  Nat.pos_of_ne_zero h.hx0

/-- `y ≠ 0` から `0 < y` を回収する。 -/
lemma y_pos {p x y z : ℕ} (h : PrimeGe5CounterexamplePack p x y z) :
    0 < y :=
  Nat.pos_of_ne_zero h.hy0

/-- `z ≠ 0` から `0 < z` を回収する。 -/
lemma z_pos {p x y z : ℕ} (h : PrimeGe5CounterexamplePack p x y z) :
    0 < z :=
  Nat.pos_of_ne_zero h.hz0

end PrimeGe5CounterexamplePack

/--
TODO-2 の目標型:
prime-ge5 反例パックから、差 `z - y` が `p` 乗になれないことを供給する。
-/
abbrev GapNotIsPowTarget : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z → ¬ ∃ t : ℕ, (z - y) = t ^ p

/--
Triomino/Cosmic 側で最終的に供給すべき本丸インターフェイス。
意味付けを固定し、`TODO-2` の実装本体を別モジュールへ隔離しやすくする。
-/
abbrev TriominoCosmicGapInvariant : Prop :=
  GapNotIsPowTarget

/--
Triomino/Cosmic の gap 不変量があれば、`TODO-2` ターゲットは即座に埋まる。
ここでは薄い接続だけを固定し、本丸の証明は別ファイルで育てる。
-/
theorem gap_not_isPow_of_counterexample
    (hTri : TriominoCosmicGapInvariant) :
    GapNotIsPowTarget := by
  intro p x y z hpack
  exact hTri hpack

/--
`FermatLastTheoremFor p` へ接続するための正規化仕様。

非自明解 `a^p + b^p = c^p` から、Triomino/Cosmic 側が扱う
`PrimeGe5CounterexamplePack` を 1 つ構成できることを要求する。
-/
abbrev PrimeGe5CounterexampleNormalizerTarget : Prop :=
  ∀ {p a b c : ℕ},
    Nat.Prime p → 5 ≤ p →
    a ≠ 0 → b ≠ 0 → c ≠ 0 →
    a ^ p + b ^ p = c ^ p →
    ∃ x y z : ℕ, PrimeGe5CounterexamplePack p x y z

/--
`PrimeGe5CounterexamplePack` を直接排除できることを要求する最小仕様。

`TODO-2` 系の最終到達点を `FermatLastTheoremFor p` へ接続する際の
最後の穴を 1 つの命題として固定する。
-/
abbrev PrimeGe5CounterexampleRefuterTarget : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z → False

/--
正規化仕様と反例排除仕様が揃えば、`p ≥ 5` 素数指数の FLT 供給は得られる。

この定理により、`FLT_prime_ge5` 本体は
「正規化の実装」と「反例排除の実装」を埋めるだけへ還元される。
-/
theorem FLTPrimeGe5Target_of_normalizer_and_refuter
    (hNorm : PrimeGe5CounterexampleNormalizerTarget)
    (hRefute : PrimeGe5CounterexampleRefuterTarget) :
    FLTPrimeGe5Target := by
  intro p hp hp5 a b c ha hb hc hEq
  rcases hNorm hp hp5 ha hb hc hEq with ⟨x, y, z, hpack⟩
  exact hRefute hpack

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
