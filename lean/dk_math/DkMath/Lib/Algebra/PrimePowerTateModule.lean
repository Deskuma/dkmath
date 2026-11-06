/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Algebra.PrimePowerTateSequence
import DkMath.Lib.Algebra.PadicCharacterLimit
import Mathlib.Algebra.Module.MinimalAxioms

#print "file: DkMath.Lib.Algebra.PrimePowerTateModule"

/-!
# 同じ Tate 点列への標準 p 進 scalar と互換剰余の復元

(a • x)ₙ=(a mod p^(n+1)).val • xₙ と定義する。
元の点の零化条件から代表の選択に依存しないことを証明し、遷移条件と加群公理を導く。
位数や階数を仮定して加群構造を運び込む定義ではない。
-/

namespace DkMath.Lib.Algebra.PrimePowerTateSequence
noncomputable section
variable {G : Type*} [AddCommGroup G]

/-- N で消える点への自然数倍は、法 N の同じ剰余だけで決まる。 -/
theorem nsmul_eq_of_residue {N a b : ℕ} (x : G) (hx : N • x = 0)
    (h : (a : ZMod N) = b) : a • x = b • x := by
  have hm (c : ℕ) : (c % N) • x = c • x := by
    have hc := congrArg (fun k : ℕ => k • x) (Nat.mod_add_div c N)
    simpa only [add_nsmul, mul_nsmul, hx, nsmul_zero, add_zero] using hc
  have hab : a % N = b % N := by simpa only [ZMod.val_natCast] using congrArg ZMod.val h
  rw [← hm a, ← hm b, hab]

variable {p : ℕ} [Fact p.Prime]

/-- 実際の各成分への、標準剰余を用いた p 進 scalar。 -/
def padicSMul (a : ℤ_[p]) (x : Tate p G) : Tate p G :=
  ⟨fun n => (PadicInt.toZModPow (n + 1) a).val • evaluation n x,
    ⟨fun n => by rw [smul_comm, killed, nsmul_zero], fun n => by
      rw [smul_comm, compatible]
      apply nsmul_eq_of_residue _ (killed x n)
      rw [ZMod.natCast_zmod_val]
      have h := PadicInt.cast_toZModPow (n + 1) (n + 1 + 1) (Nat.le_succ _) a
      rw [ZMod.cast_eq_val] at h
      exact h⟩⟩

instance padicSMulInstance : SMul ℤ_[p] (Tate p G) := ⟨padicSMul⟩

/-- スカラー倍の評価公式。元の同じ点の自然数倍である。 -/
theorem evaluation_smul (a : ℤ_[p]) (x : Tate p G) (n : ℕ) :
    evaluation n (a • x) = (PadicInt.toZModPow (n + 1) a).val • evaluation n x := rfl

instance padicModule : Module ℤ_[p] (Tate p G) := Module.ofMinimalAxioms
  (fun a x y => by
    apply ext; intro n
    change (PadicInt.toZModPow (n + 1) a).val • (evaluation n x + evaluation n y) =
      (PadicInt.toZModPow (n + 1) a).val • evaluation n x +
        (PadicInt.toZModPow (n + 1) a).val • evaluation n y
    exact nsmul_add _ _ _)
  (fun a b x => by
    apply ext; intro n
    rw [evaluation_smul, map_add, map_add (evaluation n), evaluation_smul, evaluation_smul, ← add_nsmul]
    apply nsmul_eq_of_residue _ (killed x n)
    simp only [Nat.cast_add, ZMod.natCast_zmod_val])
  (fun a b x => by
    apply ext; intro n
    rw [evaluation_smul, map_mul, evaluation_smul, evaluation_smul, ← mul_nsmul']
    apply nsmul_eq_of_residue _ (killed x n)
    simp only [Nat.cast_mul, ZMod.natCast_zmod_val])
  (fun x => by
    apply ext; intro n
    rw [evaluation_smul, map_one]
    have h := nsmul_eq_of_residue (evaluation n x) (killed x n)
      (show (((1 : ZMod (p ^ (n + 1)))).val : ZMod (p ^ (n + 1))) = (1 : ℕ) by
        simp only [ZMod.natCast_zmod_val, Nat.cast_one])
    exact h.trans (one_nsmul _))

variable {H : Type*} [AddCommGroup H]

/-- 元の加法準同型は、標準 scalar に関して自動的に p 進線形。 -/
def mapLinear (f : G →+ H) : Tate p G →ₗ[ℤ_[p]] Tate p H where
  __ := map f
  map_smul' a x := by
    apply ext; intro n
    change f ((PadicInt.toZModPow (n + 1) a).val • evaluation n x) =
      (PadicInt.toZModPow (n + 1) a).val • f (evaluation n x)
    exact map_nsmul f _ _

variable {Γ : Type*} [Group Γ]

/-- 同じ成分ごとの作用を標準 p 進線形作用として公開する。 -/
def actionLinear (ρ : Γ →* AddMonoid.End G) : Γ →* Module.End ℤ_[p] (Tate p G) where
  toFun g := mapLinear (ρ g)
  map_one' := by
    apply LinearMap.ext; intro x
    exact congrArg (fun f : AddMonoid.End (Tate p G) => f x) (action ρ).map_one
  map_mul' g h := by
    apply LinearMap.ext; intro x
    exact congrArg (fun f : AddMonoid.End (Tate p G) => f x) ((action ρ).map_mul g h)

/-- 互換な法 p^(n+1) の値を、実際の p 進整数へ復元するための整数列。 -/
def residueRepresentatives (c : ∀ n : ℕ, ZMod (p ^ (n + 1))) : ℕ → ℤ
  | 0 => 0
  | n + 1 => (c n).val

variable (c : ∀ n : ℕ, ZMod (p ^ (n + 1)))
    (hc : ∀ n, ZMod.castHom (pow_dvd_pow p (Nat.le_succ (n + 1)))
      (ZMod (p ^ (n + 1))) (c (n + 1)) = c n)

include hc in
/-- 隣接剰余両立性から Cauchy 性に必要な可除性を取り出す。 -/
theorem residueRepresentatives_dvd (i : ℕ) :
    (p : ℤ) ^ i ∣ residueRepresentatives c (i + 1) - residueRepresentatives c i := by
  cases i with
  | zero => simp
  | succ i =>
    rw [← Int.natCast_pow, ← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub]
    have h := hc i
    rw [ZMod.castHom_apply, ZMod.cast_eq_val] at h
    simpa only [residueRepresentatives, Int.cast_natCast, ZMod.natCast_zmod_val, sub_eq_zero] using h

/-- 互換剰余列の実際の Cauchy 極限。元が単元であることは要求しない。 -/
def liftResidues : ℤ_[p] :=
  PadicInt.ofIntSeq (residueRepresentatives c)
    (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub _ p (residueRepresentatives_dvd c hc))

/-- 構成した整数は元の全ての剰余を正確に持つ。 -/
theorem liftResidues_mod (n : ℕ) : PadicInt.toZModPow (n + 1) (liftResidues c hc) = c n := by
  have h := PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub _ p (residueRepresentatives_dvd c hc) (n + 1)
  simpa only [liftResidues, residueRepresentatives, Int.cast_natCast, ZMod.natCast_zmod_val] using h

end
end DkMath.Lib.Algebra.PrimePowerTateSequence
