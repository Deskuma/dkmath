/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.GaloisPhaseObstructionTransport

#print "file: DkMath.Lib.NumberTheory.GaloisPhaseOrbitNorm"

/-!
# IRR-007: 非零位相軌道の類群的ノルム

位相0は固定点、残る p−1 個は単元群の正則軌道である。全位相積をこの二つに
分解し、既存の同変性を代入すると ω₀ N(ω₁)=1 を得る。これは各障害の消滅を
意味しない。ノルムの核と指標成分の分類は、別途証明すべき算術である。
-/

namespace DkMath.Lib.NumberTheory
namespace RamifiedPhasePacket
variable {p : ℕ} [Fact p.Prime]

/-- 非零位相を単元で一度ずつ数える同値。代表元の重複を許す列挙ではない。 -/
def nonzeroPhaseEquiv : (ZMod p)ˣ ≃ {i : Fin p // i ≠ 0} where
  toFun a := ⟨⟨a.val.val, ZMod.val_lt _⟩, by
    intro h
    have hz : a.val.val = 0 := congrArg Fin.val h
    exact a.ne_zero (by simpa [hz] using (ZMod.natCast_zmod_val a.val).symm)⟩
  invFun i := Units.mk0 (i.val.val : ZMod p) (by
    intro h
    apply i.property
    apply Fin.ext
    have hv := congrArg ZMod.val h
    simpa [Nat.mod_eq_of_lt i.val.isLt] using hv)
  left_inv a := by
    apply Units.ext
    exact ZMod.natCast_zmod_val _
  right_inv i := by
    apply Subtype.ext
    apply Fin.ext
    change (i.val.val : ZMod p).val = i.val.val
    rw [ZMod.val_natCast]
    exact Nat.mod_eq_of_lt i.val.isLt

/-- 上の同値は位相1に対する乗法作用そのものである。 -/
theorem nonzeroPhaseEquiv_apply (a : (ZMod p)ˣ) :
    (nonzeroPhaseEquiv a).val = phaseMul a 1 := by
  apply Fin.ext
  simp [nonzeroPhaseEquiv, phaseMul,
    Nat.mod_eq_of_lt (ZMod.val_lt a.val)]

/-- 非零位相は一つの軌道。係数の固定性は、この添字の事実とは別の前提である。 -/
theorem exists_phaseMul_one (i : Fin p) (hi : i ≠ 0) :
    ∃! a : (ZMod p)ˣ, phaseMul a 1 = i := by
  refine ⟨nonzeroPhaseEquiv.symm ⟨i, hi⟩, ?_, ?_⟩
  · change phaseMul (nonzeroPhaseEquiv.symm ⟨i, hi⟩) 1 = i
    rw [← nonzeroPhaseEquiv_apply]
    exact congrArg Subtype.val (nonzeroPhaseEquiv.apply_symm_apply ⟨i, hi⟩)
  · intro a ha
    apply nonzeroPhaseEquiv.injective
    apply Subtype.ext
    simpa only [nonzeroPhaseEquiv_apply, Equiv.apply_symm_apply] using ha

/-- 全位相積を固定位相と非零軌道へ分解する。一般の可換モノイドで成立する。 -/
theorem prod_eq_zero_mul_orbit {M : Type*} [CommMonoid M] (f : Fin p → M) :
    ∏ i, f i = f 0 * ∏ a : (ZMod p)ˣ, f (phaseMul a 1) := by
  classical
  rw [Fintype.prod_eq_mul_prod_subtype_ne f 0]
  congr 1
  simpa only [nonzeroPhaseEquiv_apply] using
    (nonzeroPhaseEquiv.prod_comp (fun i : {i : Fin p // i ≠ 0} => f i.val)).symm

/-- 同変な障害族の全積則から軌道ノルム則を得る。
作用の由来は呼出側が供給し、ここで人工的な類群作用を導入しない。 -/
theorem zero_mul_orbit_norm {M : Type*} [CommMonoid M]
    (f : Fin p → M) (σ : (ZMod p)ˣ → M → M)
    (heq : ∀ a i, σ a (f i) = f (phaseMul a i)) (hprod : ∏ i, f i = 1) :
    f 0 * ∏ a : (ZMod p)ˣ, σ a (f 1) = 1 := by
  simp_rw [heq]
  rw [← prod_eq_zero_mul_orbit, hprod]

end RamifiedPhasePacket

namespace CyclotomicPhaseGalois
open scoped NumberField
variable {K : Type*} [Field K] [NumberField K]
  {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]

/-- 真の円分体ガロア群による類群の軌道積。体の元のノルムとは対象が異なる。 -/
noncomputable def orbitNorm (w : ClassGroup (𝓞 K)) : ClassGroup (𝓞 K) :=
  ∏ a : (ZMod p)ˣ, ClassGroup.mulEquiv (sigma a) w

/-- 軌道積は類群の乗法を保存する。各位相を独立に消す操作ではない。 -/
theorem orbitNorm_mul (v w : ClassGroup (𝓞 K)) :
    orbitNorm (p := p) (v * w) = orbitNorm (p := p) v * orbitNorm (p := p) w := by
  simp only [orbitNorm, map_mul, Finset.prod_mul_distrib]

/-- 軌道積は全ガロア作用で固定される。単元群の左移動で積を再索引する。 -/
theorem orbitNorm_fixed (a : (ZMod p)ˣ) (w : ClassGroup (𝓞 K)) :
    ClassGroup.mulEquiv (sigma a) (orbitNorm (p := p) w) = orbitNorm (p := p) w := by
  simp only [orbitNorm, map_prod]
  simp_rw [← classGroup_map_trans, ← sigma_mul]
  exact Equiv.prod_comp (Equiv.mulLeft a) (fun b => ClassGroup.mulEquiv (sigma b) w)

/-- p で消える類の軌道積も p で消える。非自明な p-torsion の存在は仮定しない。 -/
theorem orbitNorm_torsion (w : ClassGroup (𝓞 K)) (hw : w ^ p = 1) :
    orbitNorm (p := p) w ^ p = 1 := by
  simp only [orbitNorm, ← Finset.prod_pow, ← map_pow, hw, map_one, Finset.prod_const_one]

/-- 整数係数の位相族では ω₀ N(ω₁)=1。
元の λ の単元補正は `obstruction_int` のイデアル輸送証明で処理される。 -/
theorem zero_mul_orbitNorm
    (hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) p) (hodd : Odd p)
    (C : PhaseClassPacket (𝓞 K) p (Fin p)) (q : 𝓞 K) (A B : ℤ)
    (hq : (A : 𝓞 K) + B = (cyclotomicRamifiedPhase hζ hodd).lambda * q)
    (hf : ∀ i, C.factor i = (cyclotomicRamifiedPhase hζ hodd).quotient q B i)
    (hprod : ∏ i, C.obstruction i = 1) :
    C.obstruction 0 * orbitNorm (p := p) (C.obstruction 1) = 1 :=
  RamifiedPhasePacket.zero_mul_orbit_norm C.obstruction
    (fun a => ClassGroup.mulEquiv (sigma a))
    (obstruction_int hζ hodd C q A B hq hf) hprod

end CyclotomicPhaseGalois
end DkMath.Lib.NumberTheory
