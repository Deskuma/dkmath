/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.CosmicRamifiedValuation
import DkMath.NumberTheory.AKSBridge

/-!
# 分岐側 GN の整数根の剰余類

整数上の先頭合同式と AKSBridge の GN 版 Fermat を接続する。
`GN=p*t^p` が与えられた後の算術なので、円分体・類群・正則性は不要。
正則性が必要なのは、この等式を元の FLT 方程式から構成する前段である。
-/

open DkMath.CosmicFormula DkMath.Lib.NumberTheory

namespace DkMath.NumberTheory

/-- `p*t^p ≡ p*u^(p-1) mod p²` の共通因子 p を消去する。
両辺だけでなく法も p² から p へ縮小する。p∤u はこの段階では不要。 -/
theorem ramified_integral_root_pow_modEq_parameter
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) {x u t : ℤ}
    (hx : (p : ℤ) ∣ x) (ht : GTail p 1 x u = (p : ℤ) * t ^ p) :
    t ^ p ≡ u ^ (p - 1) [ZMOD (p : ℤ)] := by
  have h := integral_GN_modEq_head_mod_prime_sq hp hp3 hx (u := u)
  rw [ht, pow_two] at h
  exact Int.ModEq.mul_left_cancel' (by exact_mod_cast hp.ne_zero) h

/-- **分岐側の整数根は 1 mod p**。

GN の mod p² 先頭項と `GN=p*t^p` から p を一つ消去する。
GN 版 Fermat の小定理を u,t に適用し、p∤u により
`u^(p-1)=1` を得る。従って t≡1。
`p∤t` を別途仮定せず、すべての整数根 t に成り立つ。
円分整数環の単元の合同条件を結論する定理ではない。 -/
theorem ramified_integral_root_modEq_one
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) {x u t : ℤ}
    (hx : (p : ℤ) ∣ x) (hu : ¬ (p : ℤ) ∣ u)
    (ht : GTail p 1 x u = (p : ℤ) * t ^ p) :
    t ≡ 1 [ZMOD (p : ℤ)] := by
  let : Fact p.Prime := ⟨hp⟩
  have hpow := (ZMod.intCast_eq_intCast_iff _ _ p).mpr
    (ramified_integral_root_pow_modEq_parameter hp hp3 hx ht)
  have hu0 : (u : ZMod p) ≠ 0 := fun h =>
    hu ((ZMod.intCast_zmod_eq_zero_iff_dvd u p).mp h)
  have hu1 : (u : ZMod p) ^ (p - 1) = 1 := by
    apply mul_right_cancel₀ hu0
    rw [one_mul, ← pow_succ, Nat.sub_add_cancel hp.one_le]
    exact prime_zmod_gap_compress_via_GN hp _
  apply (ZMod.intCast_eq_intCast_iff t 1 p).mp
  simpa only [Int.cast_pow, prime_zmod_gap_compress_via_GN hp, hu1, Int.cast_one] using hpow

end DkMath.NumberTheory
