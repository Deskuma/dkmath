/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Data.ZMod.Basic
import DkMath.Lib.Cosmic.CoreNested
import DkMath.CosmicFormula.Defs
import DkMath.Lib.Cosmic.GTailFactor
import DkMath.Lib.Cosmic.GTailCongruence

#print "file: DkMath.Lib.Cosmic.GNPrime37"

/-!
# 37次の二方向 GN と、全ての素数に共通する Pascal 行

二項展開・GN 分解・内部係数の p 可除性は正則性を使わない。
37も11・13と同じ定理の特殊化である。相違は円分イデアル類から元を抽出する後段にある。
37を36個の掛算へ展開せず、2乗・2乗・3乗・3乗と最後の掛算で表す。
-/

namespace DkMath.Lib.Cosmic

open DkMath.CosmicFormula

/-- 二進法の例：x^7=x^4*x^2*x。可換性さえ不要。 -/
theorem pow_seven_small {R : Type*} [Monoid R] (x : R) : x ^ 7 = x ^ 4 * x ^ 2 * x := by
  calc
    x ^ 7 = x ^ 6 * x := pow_succ x 6
    _ = x ^ 4 * x ^ 2 * x := congrArg (fun y => y * x) (pow_add x 4 2)

/-- 2*2*3*3+1=37 をそのまま冪の合成へ移す。巨大な多項式展開はしない。 -/
theorem pow_thirtySeven_small {R : Type*} [Monoid R] (x : R) :
    x ^ 37 = (((x ^ 2) ^ 2) ^ 3) ^ 3 * x := by
  norm_num [← pow_mul, ← pow_succ]

/-- x を抜く側の37次 GN。x=0 を含む恒等式で、割算は用いない。 -/
theorem thirtySeven_difference_left {R : Type*} [CommRing R] (x u : R) :
    (x + u) ^ 37 - u ^ 37 = x * GN 37 x u := by
  simpa only [powerCore, add_comm u x] using powerCore_eq_gtail_one 37 u x

/-- u を抜く側の37次 GN。二つの式は x,u の交換で対応する。 -/
theorem thirtySeven_difference_right {R : Type*} [CommRing R] (x u : R) :
    (x + u) ^ 37 - x ^ 37 = u * GN 37 u x :=
  powerCore_eq_gtail_one 37 x u

/-- 非正則性に関係なく、任意の素数 p の内部二項係数は p をちょうど1回含む。
`k*C(p,k)=p*C(p-1,k-1)` と、pより小さい行の係数の p 互いに素性を使う。 -/
theorem prime_choose_exact_layer {p k : ℕ} (hp : p.Prime) (hk : 0 < k) (hkp : k < p) :
    p ∣ p.choose k ∧ ¬ p ^ 2 ∣ p.choose k := by
  refine ⟨hp.dvd_choose_self hk.ne' hkp, ?_⟩
  intro hsq
  have hid : p * (p - 1).choose (k - 1) = p.choose k * k := by
    simpa only [Nat.sub_add_cancel hp.pos, Nat.sub_add_cancel hk] using
      Nat.add_one_mul_choose_eq (p - 1) (k - 1)
  have hd : p ^ 2 ∣ p * (p - 1).choose (k - 1) := by
    rw [hid]
    exact dvd_mul_of_dvd_left hsq k
  have hd' : p ∣ (p - 1).choose (k - 1) :=
    Nat.dvd_of_mul_dvd_mul_left hp.pos (by simpa only [pow_two] using hd)
  have hc := hp.coprime_choose_of_lt (by omega : p - 1 < p)
    (by omega : k - 1 ≤ p - 1)
  exact Nat.not_coprime_of_dvd_of_dvd hp.one_lt (dvd_refl p) hd' hc

/-- Pascal 行の内部係数の内容は p。37でも同じであり、非正則性はここには現れない。 -/
theorem prime_interior_content {p : ℕ} (hp : p.Prime) :
    coeffGCD p (Finset.Ico 1 p) = p := coeffGCD_prime_interior p hp

/-- 37次の全内部係数について一様な正確な37可除性。 -/
theorem thirtySeven_choose_exact_layer {k : ℕ} (hk : 0 < k) (hkp : k < 37) :
    37 ∣ Nat.choose 37 k ∧ ¬ 37 ^ 2 ∣ Nat.choose 37 k :=
  prime_choose_exact_layer (by decide) hk hkp

/-- 11・13・37の内部係数内容を同じ一般定理で比較する。 -/
theorem interior_contents_eleven_thirteen_thirtySeven :
    coeffGCD 11 (Finset.Ico 1 11) = 11 ∧ coeffGCD 13 (Finset.Ico 1 13) = 13 ∧
      coeffGCD 37 (Finset.Ico 1 37) = 37 :=
  ⟨prime_interior_content (by decide), prime_interior_content (by decide),
    prime_interior_content (by decide)⟩

/-- 具体的な小さい係数。37, 37*18, 37*210 となる。 -/
theorem thirtySeven_initial_coefficients :
    Nat.choose 37 1 = 37 ∧ Nat.choose 37 2 = 666 ∧ Nat.choose 37 3 = 7770 := by
  norm_num [Nat.choose]

/-- 素数次 GN を F_p へ送ると、末尾の x^(p-1) だけが残る。
この有限体への射影も正則性・非正則性を見分けない。 -/
theorem prime_GN_zmod {p : ℕ} [hp : Fact p.Prime] (x u : ZMod p) :
    GN p x u = x ^ (p - 1) := by
  change GTail p 1 x u = _
  rw [GTail_one_eq_sum]
  let f : ℕ → ZMod p := fun k => (Nat.choose p (k + 1) : ZMod p) * x ^ k * u ^ (p - 1 - k)
  change (∑ k ∈ Finset.range p, f k) = _
  have hz : ∑ k ∈ Finset.range (p - 1), f k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hd := hp.out.dvd_choose_self (by omega : k + 1 ≠ 0)
      (by have := Finset.mem_range.mp hk; omega : k + 1 < p)
    have hc : (Nat.choose p (k + 1) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hd
    simp only [f, hc, zero_mul]
  calc
    (∑ k ∈ Finset.range p, f k) = (∑ k ∈ Finset.range (p - 1), f k) + f (p - 1) := by
      simpa only [Nat.sub_add_cancel hp.out.pos] using Finset.sum_range_succ f (p - 1)
    _ = x ^ (p - 1) := by
      rw [hz]
      simp [f, Nat.sub_add_cancel hp.out.pos]

/-- 37の局所的な正確可除性。37∣x、37∤u ならGNの37付値は1。
大域的な類群障害や、FLT37 の反例排除は結論しない。 -/
theorem thirtySeven_GN_exact_layer {x u : ℕ} (hx : 37 ∣ x) (hu : ¬ 37 ∣ u) :
    37 ∣ GN 37 x u ∧ ¬ 37 ^ 2 ∣ GN 37 x u := by
  have hp : Nat.Prime 37 := by decide
  refine ⟨(prime_dvd_GN_iff_dvd_gap hp).mpr hx, ?_⟩
  intro hsq
  have hmod := GN_modEq_head_mod_sq_of_odd_prime_dvd_x x u hp (by decide) hx
  have hhead : 37 ^ 2 ∣ 37 * u ^ (37 - 1) :=
    Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hsq))
  have hpow : 37 ∣ u ^ (37 - 1) :=
    Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 37) (by simpa only [pow_two] using hhead)
  exact hu (hp.dvd_of_dvd_pow hpow)

end DkMath.Lib.Cosmic
