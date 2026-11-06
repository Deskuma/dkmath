/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Topology.Algebra.Group.Neighborhood
import Mathlib.Topology.Algebra.Group.Units

#print "file: DkMath.Lib.Algebra.PadicCharacterLimit"

/-!
# 両立する有限単元値指標の実際の p 進極限

第 n 段の法は p^(n+1)。法1の第0成分を補って整数代表の Cauchy 列を作る。
極限の各剰余が元の指標であることから乗法性・一意性を証明する。
有限段の開核から極限の連続性を導く。無限段の核が開とは主張しない。
-/

namespace DkMath.Lib.Algebra.PadicCharacterLimit

noncomputable section
variable {p : ℕ} [Fact p.Prime] {Γ : Type*} [Group Γ]
    (c : ∀ n : ℕ, Γ →* (ZMod (p ^ (n + 1)))ˣ)
    (hc : ∀ n g, Units.map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ (n + 1)))
      (ZMod (p ^ (n + 1)))).toMonoidHom (c (n + 1) g) = c n g)

/-- 法1の成分を0とした、同じ有限指標の非負整数代表。 -/
def representatives (g : Γ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => (c n g : ZMod (p ^ (n + 1))).val

include hc in
/-- 隣接両立性が、整数代表の差の p 冪可除性を与える。 -/
theorem representatives_dvd (g : Γ) (i : ℕ) :
    (p : ℤ) ^ i ∣ representatives c g (i + 1) - representatives c g i := by
  cases i with
  | zero => simp
  | succ i =>
    rw [← Int.natCast_pow, ← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub]
    have h := congrArg Units.val (hc i g)
    change ZMod.castHom _ _ (c (i + 1) g : ZMod (p ^ (i + 1 + 1))) = _ at h
    rw [ZMod.castHom_apply, ZMod.cast_eq_val] at h
    simpa only [representatives, Int.cast_natCast, ZMod.natCast_zmod_val, sub_eq_zero] using h

/-- 実際の整数 Cauchy 列の p 進極限。 -/
def value (g : Γ) : ℤ_[p] :=
  PadicInt.ofIntSeq (representatives c g)
    (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub _ p (representatives_dvd c hc g))

/-- 各有限剰余は、元の同じ指標そのものである。 -/
theorem value_mod (n : ℕ) (g : Γ) :
    PadicInt.toZModPow (n + 1) (value c hc g) = (c n g : ZMod (p ^ (n + 1))) := by
  have h := PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub _ p (representatives_dvd c hc g) (n + 1)
  simpa only [value, representatives, Int.cast_natCast, ZMod.natCast_zmod_val] using h

/-- 全ての正冪剰余が同じなら p 進整数は同じ。法1の成分は自明。 -/
theorem ext_positive {x y : ℤ_[p]}
    (h : ∀ n, PadicInt.toZModPow (n + 1) x = PadicInt.toZModPow (n + 1) y) : x = y := by
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  cases n with
  | zero =>
    have : Subsingleton (ZMod (p ^ 0)) := by rw [pow_zero]; infer_instance
    exact Subsingleton.elim _ _
  | succ n => exact h n

/-- 剰余ごとの乗法性から作った実際の p 進準同型。 -/
def valueHom : Γ →* ℤ_[p] where
  toFun := value c hc
  map_one' := by
    apply ext_positive
    intro n
    rw [value_mod, map_one, map_one, Units.val_one]
  map_mul' g h := by
    apply ext_positive
    intro n
    rw [value_mod, map_mul, map_mul, value_mod, value_mod, Units.val_mul]

/-- 群の逆元を使って単元へ持ち上げた実際の極限指標。 -/
def character : Γ →* ℤ_[p]ˣ := (valueHom c hc).toHomUnits

/-- 極限指標の有限段への単元値剰余公式。 -/
theorem character_mod (n : ℕ) (g : Γ) :
    Units.map (PadicInt.toZModPow (n + 1)).toMonoidHom (character c hc g) = c n g := by
  apply Units.ext
  exact value_mod c hc n g

/-- 同じ有限指標を持つ p 進単元値指標は一意。 -/
theorem character_unique (d : Γ →* ℤ_[p]ˣ)
    (hd : ∀ n g, Units.map (PadicInt.toZModPow (n + 1)).toMonoidHom (d g) = c n g) :
    character c hc = d := by
  apply MonoidHom.ext
  intro g
  apply Units.ext
  apply ext_positive
  intro n
  exact (value_mod c hc n g).trans (congrArg Units.val (hd n g)).symm

/-- 極限指標値1は、すべての有限段の指標値1と同値。 -/
theorem character_eq_one_iff (g : Γ) : character c hc g = 1 ↔ ∀ n, c n g = 1 := by
  constructor
  · intro h n
    rw [← character_mod c hc n g, h, map_one]
  · intro h
    apply Units.ext
    apply ext_positive
    intro n
    change PadicInt.toZModPow (n + 1) (value c hc g) = PadicInt.toZModPow (n + 1) 1
    rw [value_mod, h n, map_one, Units.val_one]

/-- 各有限段の開核から極限指標の連続性を証明する。無限段の開核は結論しない。 -/
theorem character_continuous [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (hopen : ∀ n, IsOpen ((c n).ker : Set Γ)) : Continuous (character c hc) := by
  apply Continuous.of_coeHom_comp
  apply continuous_of_continuousAt_one
  rw [Metric.continuousAt_iff']
  intro ε hε
  obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt p hε
  have hsmall : (p : ℝ) ^ (-((k + 1 : ℕ) : ℤ)) < ε := by
    refine lt_of_le_of_lt ?_ hk
    gcongr
    · exact_mod_cast (Fact.out : p.Prime).one_le
    · omega
  filter_upwards [(hopen k).mem_nhds ((c k).ker.one_mem)] with g hg
  apply lt_of_le_of_lt _ hsmall
  rw [dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow,
    RingHom.mem_ker, map_sub, sub_eq_zero]
  change PadicInt.toZModPow (k + 1) (value c hc g) =
    PadicInt.toZModPow (k + 1) (value c hc 1)
  rw [value_mod, value_mod, map_one, Units.val_one]
  exact congrArg Units.val hg

end
end DkMath.Lib.Algebra.PadicCharacterLimit
