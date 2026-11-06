/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Algebra.PrimePowerTatePairSpan
import DkMath.Lib.NumberTheory.EllipticTateReduction

#print "file: DkMath.Lib.NumberTheory.EllipticTatePairBasis"

/-!
# 互換な二点から全 Tate 加群の実際の線形同型を構成する

第0段の生成性から各有限段への全射を構成し、実際の捩れ濃度と比較して全単射にする。
その同じ有限座標の互換性と Cauchy 復元から、全 Tate 加群の二成分表示を得る。
-/
namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open DkMath.Lib.Algebra DkMath.Lib.Algebra.PrimePowerTateSequence
noncomputable section
variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
    {p : ℕ} [Fact p.Prime] (v w : Tate p (Points E))

omit [CharZero K] [E.IsElliptic] in
/-- 既存の捩れ scalar を元の同じ点の自然数倍として読む。 -/
theorem torsion_smul_val {N : ℕ} [NeZero N] (c : ZMod N) (x : Torsion E N) :
    (c • x).val = c.val • x.val := by
  have h := Nat.cast_smul_eq_nsmul (ZMod N) c.val x
  rw [ZMod.natCast_zmod_val] at h
  have he := congrArg (torsionGroup E N).subtype h
  rw [map_nsmul] at he
  exact he

/-- 各有限段の二つの同じ点による標準線形写像。 -/
def tatePairLevel (n : ℕ) :
    ZMod (p ^ (n + 1)) × ZMod (p ^ (n + 1)) →ₗ[ZMod (p ^ (n + 1))] Torsion E (p ^ (n + 1)) where
  toFun a := a.1 • ⟨evaluation n v, killed v n⟩ + a.2 • ⟨evaluation n w, killed w n⟩
  map_add' a b := by simp only [Prod.fst_add, Prod.snd_add, add_smul]; abel
  map_smul' c a := by simp only [Prod.smul_fst, Prod.smul_snd, smul_add, smul_smul, RingHom.id_apply, smul_eq_mul]

omit [CharZero K] [E.IsElliptic] in
/-- 有限座標の実際の点への値。 -/
theorem tatePairLevel_val (n : ℕ) (a : ZMod (p ^ (n + 1)) × ZMod (p ^ (n + 1))) :
    (tatePairLevel E v w n a).val = a.1.val • evaluation n v + a.2.val • evaluation n w := by
  change (torsionGroup E _).subtype (_ + _) = _
  rw [map_add]
  change (a.1 • (⟨evaluation n v, killed v n⟩ : Torsion E _)).val +
    (a.2 • (⟨evaluation n w, killed w n⟩ : Torsion E _)).val = _
  rw [torsion_smul_val, torsion_smul_val]

variable (hbase : ∀ x : Points E, p • x = 0 → ∃ a b : ℕ,
    x = a • evaluation 0 v + b • evaluation 0 w)

include hbase in
omit [CharZero K] [E.IsElliptic] in
/-- 実際の有限段への全射は、第0段の生成性からの帰納法で得る。 -/
theorem tatePairLevel_surjective (n : ℕ) : Function.Surjective (tatePairLevel E v w n) := by
  intro x
  obtain ⟨a, b, hab⟩ := pair_span v w hbase n x.val x.property
  refine ⟨(a, b), ?_⟩
  apply Subtype.ext
  rw [tatePairLevel_val]
  apply Eq.trans _ hab.symm
  exact congrArg₂ (fun a b : Points E => a + b)
    (nsmul_eq_of_residue _ (killed v n) (ZMod.natCast_zmod_val (a : ZMod (p ^ (n + 1)))))
    (nsmul_eq_of_residue _ (killed w n) (ZMod.natCast_zmod_val (b : ZMod (p ^ (n + 1)))))

/-- 有限段の濃度は実際に同じ。全射と合わせて単射も得る。 -/
def tatePairLevelEquiv (n : ℕ) :
    (ZMod (p ^ (n + 1)) × ZMod (p ^ (n + 1))) ≃ₗ[ZMod (p ^ (n + 1))] Torsion E (p ^ (n + 1)) :=
  LinearEquiv.ofBijective (tatePairLevel E v w n) <|
    (Nat.bijective_iff_surjective_and_card _).mpr ⟨tatePairLevel_surjective E v w hbase n, by
      rw [Nat.card_prod, Nat.card_zmod, card_torsion_sq E _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero), pow_two]⟩

local notation "lev" => tatePairLevelEquiv E v w hbase

/-- 同じ点列の第 n 成分の二つの係数。 -/
def tatePairCoefficients (x : Tate p (Points E)) (n : ℕ) :
    ZMod (p ^ (n + 1)) × ZMod (p ^ (n + 1)) := (lev n).symm ⟨evaluation n x, killed x n⟩

local notation "coeff" => tatePairCoefficients E v w hbase

/-- 点列・二つの生成点列が互換なので、両係数も標準剰余で互換となる。 -/
theorem tatePairCoefficients_compatible (x : Tate p (Points E)) (n : ℕ) :
    let f := ZMod.castHom (pow_dvd_pow p (Nat.le_succ (n + 1))) (ZMod (p ^ (n + 1)))
    (f (coeff x (n + 1)).1, f (coeff x (n + 1)).2) = coeff x n := by
  dsimp only
  apply (lev n).injective
  apply Subtype.ext
  change (tatePairLevel E v w n _).val = _
  rw [tatePairLevel_val]
  have he := congrArg (fun z : Torsion E (p ^ (n + 1 + 1)) => z.val)
    ((lev (n + 1)).apply_symm_apply ⟨evaluation (n + 1) x, killed x (n + 1)⟩)
  change (tatePairLevel E v w (n + 1) (coeff x (n + 1))).val = evaluation (n + 1) x at he
  rw [tatePairLevel_val] at he
  have hp := congrArg (fun z : Points E => p • z) he
  rw [nsmul_add, smul_comm p, smul_comm p, compatible, compatible, compatible] at hp
  have hcast (c : ZMod (p ^ (n + 1 + 1))) (z : Points E) (hz : p ^ (n + 1) • z = 0) :
      (ZMod.castHom (pow_dvd_pow p (Nat.le_succ (n + 1))) (ZMod (p ^ (n + 1))) c).val • z = c.val • z := by
    apply nsmul_eq_of_residue z hz
    rw [ZMod.natCast_zmod_val, ZMod.castHom_apply, ZMod.cast_eq_val]
  rw [hcast _ _ (killed v n), hcast _ _ (killed w n)]
  change _ = ((lev n) ((lev n).symm ⟨evaluation n x, killed x n⟩)).val
  rw [LinearEquiv.apply_symm_apply]
  exact hp

/-- 同じ二点列の標準 p 進線形結合。 -/
def tatePairParametrization : ℤ_[p] × ℤ_[p] →ₗ[ℤ_[p]] Tate p (Points E) where
  toFun a := a.1 • v + a.2 • w
  map_add' a b := by simp only [Prod.fst_add, Prod.snd_add, add_smul]; abel
  map_smul' c a := by simp only [Prod.smul_fst, Prod.smul_snd, smul_add, smul_smul, RingHom.id_apply, smul_eq_mul]

omit [CharZero K] [E.IsElliptic] in
/-- 無限座標から有限座標への評価公式。 -/
theorem tatePairParametrization_level (a : ℤ_[p] × ℤ_[p]) (n : ℕ) :
    evaluation n (tatePairParametrization E v w a) =
      (tatePairLevel E v w n (PadicInt.toZModPow (n + 1) a.1, PadicInt.toZModPow (n + 1) a.2)).val := by
  rw [tatePairLevel_val]
  exact congrArg₂ (fun a b : Points E => a + b) (evaluation_smul a.1 v n) (evaluation_smul a.2 w n)

include hbase in
/-- 有限同型の単射性と p 進剰余外延性から、無限座標も単射。 -/
theorem tatePairParametrization_injective : Function.Injective (tatePairParametrization E v w) := by
  intro a b h
  have hh (n : ℕ) :
      (PadicInt.toZModPow (n + 1) a.1, PadicInt.toZModPow (n + 1) a.2) =
      (PadicInt.toZModPow (n + 1) b.1, PadicInt.toZModPow (n + 1) b.2) := by
    apply (lev n).injective
    apply Subtype.ext
    have he := congrArg (evaluation n) h
    rw [tatePairParametrization_level, tatePairParametrization_level] at he
    exact he
  apply Prod.ext
  · exact PadicCharacterLimit.ext_positive (fun n => congrArg Prod.fst (hh n))
  · exact PadicCharacterLimit.ext_positive (fun n => congrArg Prod.snd (hh n))

include hbase in
/-- 両係数の実際の Cauchy 復元から、全 Tate 点列を表せる。 -/
theorem tatePairParametrization_surjective : Function.Surjective (tatePairParametrization E v w) := by
  intro x
  have hfst n := congrArg Prod.fst (tatePairCoefficients_compatible E v w hbase x n)
  have hsnd n := congrArg Prod.snd (tatePairCoefficients_compatible E v w hbase x n)
  let a := liftResidues (fun n => (coeff x n).1) hfst
  let b := liftResidues (fun n => (coeff x n).2) hsnd
  refine ⟨(a, b), ?_⟩
  apply PrimePowerTateSequence.ext; intro n
  rw [tatePairParametrization_level, liftResidues_mod, liftResidues_mod]
  exact congrArg (fun z : Torsion E (p ^ (n + 1)) => z.val)
    ((lev n).apply_symm_apply ⟨evaluation n x, killed x n⟩)

/-- 全 Tate 加群への実際の二成分線形同型。 -/
def tatePairEquiv : (ℤ_[p] × ℤ_[p]) ≃ₗ[ℤ_[p]] Tate p (Points E) :=
  LinearEquiv.ofBijective (tatePairParametrization E v w)
    ⟨tatePairParametrization_injective E v w hbase, tatePairParametrization_surjective E v w hbase⟩

end
end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
