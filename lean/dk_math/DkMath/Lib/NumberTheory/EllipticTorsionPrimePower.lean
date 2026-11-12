/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Algebra.TorsionPowerLifting
import DkMath.Lib.NumberTheory.EllipticTorsionAllCard
import DkMath.Lib.NumberTheory.EllipticTorsionGL2

#print "file: DkMath.Lib.NumberTheory.EllipticTorsionPrimePower"

/-!
# 素数冪ねじれ点群の自由加群構造

実際のE[p]の二つの基底ベクトルをpᵏ倍写像で持ち上げる。
最高段の基底から生成性を運ぶ一般群の帰納法により、二つの持ち上げはE[p^{k+1}]を生成する。
ZMod(p^{k+1})²からの生成写像は、既存の正確な位数公式によって全単射になる。
これを線形同型と基底として公開する。基底選択は非計算的・非標準的であり、
段をまたぐ基底の互換性や自明なガロア作用を主張しない。
-/
namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open Module DkMath.Lib.Algebra.TorsionPowerLifting
variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
  (p : ℕ) [Fact p.Prime]

/-- E[p]の基底は、p倍で零になる実際の点を自然数係数で生成する。 -/
theorem prime_basis_generates_points (x : Points E) (hx : p • x = 0) :
    ∃ a b : ℕ, x = a • (torsionBasis E p 0).val + b • (torsionBasis E p 1).val := by
  let q : Torsion E p := ⟨x, hx⟩
  have h := (torsionBasis E p).sum_repr q
  rw [Fin.sum_univ_two] at h
  have hs (c : ZMod p) (P : Torsion E p) : c • P = c.val • P := by
    conv_lhs => rw [← ZMod.natCast_zmod_val c]
    exact Nat.cast_smul_eq_nsmul _ _ _
  rw [hs, hs] at h
  exact ⟨((torsionBasis E p).repr q 0).val, ((torsionBasis E p).repr q 1).val,
    congrArg (fun P : Torsion E p => P.val) h.symm⟩

/-- 同じ実際の点群の全射性で、二つの基底ベクトルを同時に持ち上げられる。 -/
theorem exists_prime_power_lifts (k : ℕ) :
    ∃ P : Fin 2 → Torsion E (p ^ (k + 1)),
      ∀ i, p ^ k • (P i).val = (torsionBasis E p i).val := by
  choose f hf using fun i : Fin 2 => multiplication_surjective E (p ^ k)
    (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) (torsionBasis E p i).val
  refine ⟨fun i => ⟨f i, ?_⟩, hf⟩
  change p ^ (k + 1) • f i = 0
  rw [pow_succ', mul_smul, show p ^ k • f i = (torsionBasis E p i).val from hf i]
  exact (torsionBasis E p i).property

/-- 任意の二点から定まる二変数の線形生成写像。 -/
noncomputable def primePowerPresentation (k : ℕ) (P : Fin 2 → Torsion E (p ^ (k + 1))) :
    (Fin 2 → ZMod (p ^ (k + 1))) →ₗ[ZMod (p ^ (k + 1))] Torsion E (p ^ (k + 1)) where
  toFun a := a 0 • P 0 + a 1 • P 1
  map_add' a b := by simp only [Pi.add_apply, add_smul]; abel
  map_smul' a b := by simp only [Pi.smul_apply, smul_eq_mul, smul_add, mul_smul, RingHom.id_apply]

/-- 最高段で基底になる持ち上げは、冪の核全体を生成する。 -/
theorem primePowerPresentation_surjective (k : ℕ) (P : Fin 2 → Torsion E (p ^ (k + 1)))
    (hP : ∀ i, p ^ k • (P i).val = (torsionBasis E p i).val) :
    Function.Surjective (primePowerPresentation E p k P) := by
  intro x
  obtain ⟨a, b, hab⟩ := lifted_pair_generates p (torsionBasis E p 0).val (torsionBasis E p 1).val
    (prime_basis_generates_points E p) k (P 0).val (P 1).val (hP 0) (hP 1) x.val x.property
  refine ⟨![(a : ZMod (p ^ (k + 1))), (b : ZMod (p ^ (k + 1)))], ?_⟩
  apply Subtype.ext
  change (((a : ZMod (p ^ (k + 1))) • P 0 + (b : ZMod (p ^ (k + 1))) • P 1).val) = x.val
  rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  exact hab.symm

/-- 正確な位数が一致するため、全射な二生成写像は単射にもなる。 -/
theorem primePowerPresentation_bijective (k : ℕ) (P : Fin 2 → Torsion E (p ^ (k + 1)))
    (hP : ∀ i, p ^ k • (P i).val = (torsionBasis E p i).val) :
    Function.Bijective (primePowerPresentation E p k P) := by
  apply (primePowerPresentation_surjective E p k P hP).bijective_of_nat_card_le
  rw [Nat.card_fun, Nat.card_fin, Nat.card_zmod,
    card_torsion_sq E _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)]

/-- 非標準的に選んだ同じ実際の基底の持ち上げ。 -/
noncomputable def primePowerLifts (k : ℕ) : Fin 2 → Torsion E (p ^ (k + 1)) :=
  (exists_prime_power_lifts E p k).choose

/-- 選択された持ち上げは、指定の最高段の基底へ写る。 -/
theorem primePowerLifts_spec (k : ℕ) (i : Fin 2) :
    p ^ k • (primePowerLifts E p k i).val = (torsionBasis E p i).val :=
  (exists_prime_power_lifts E p k).choose_spec i

/-- 正指数の素数冪ねじれ点の線形座標同型。可逆性を位数の一致で証明する。 -/
noncomputable def primePowerSuccEquiv (k : ℕ) :
    Torsion E (p ^ (k + 1)) ≃ₗ[ZMod (p ^ (k + 1))] (Fin 2 → ZMod (p ^ (k + 1))) :=
  (LinearEquiv.ofBijective (primePowerPresentation E p k (primePowerLifts E p k))
    (primePowerPresentation_bijective E p k _ (primePowerLifts_spec E p k))).symm

/-- 全てのk≥0に対する構造同型。k=0は零加群同士の同型であり、自由階数の一意性は主張しない。 -/
noncomputable def primePowerEquiv (k : ℕ) :
    Torsion E (p ^ k) ≃ₗ[ZMod (p ^ k)] (Fin 2 → ZMod (p ^ k)) := by
  cases k with
  | zero =>
    have : Subsingleton (ZMod (p ^ 0)) := by rw [pow_zero]; infer_instance
    have : Subsingleton (Torsion E (p ^ 0)) := ⟨fun x y =>
      (torsion_one_eq_zero E x).trans (torsion_one_eq_zero E y).symm⟩
    exact LinearEquiv.ofBijective 0 ⟨fun _ _ _ => Subsingleton.elim _ _,
      fun x => ⟨0, Subsingleton.elim _ x⟩⟩
  | succ k => exact primePowerSuccEquiv E p k

/-- 各段の非標準的な二元基底。ガロア作用の同変な自明化や互換的な塔の基底ではない。 -/
noncomputable def primePowerBasis (k : ℕ) : Basis (Fin 2) (ZMod (p ^ k)) (Torsion E (p ^ k)) :=
  Basis.ofEquivFun (primePowerEquiv E p k)

/-- 正指数では係数環が非自明であり、自由加群の有限階数は2となる。 -/
theorem primePower_finrank (k : ℕ) : finrank (ZMod (p ^ (k + 1))) (Torsion E (p ^ (k + 1))) = 2 := by
  have : Fact (1 < p ^ (k + 1)) := ⟨one_lt_pow' (Fact.out : p.Prime).one_lt (Nat.succ_ne_zero k)⟩
  exact Module.finrank_eq_card_basis (primePowerBasis E p (k + 1))

/-- 座標同型の逆は、選ばれた二点を係数で足す具体的な生成写像である。 -/
theorem primePowerSuccEquiv_symm_apply (k : ℕ) (a : Fin 2 → ZMod (p ^ (k + 1))) :
    (primePowerSuccEquiv E p k).symm a = a 0 • primePowerLifts E p k 0 + a 1 • primePowerLifts E p k 1 := rfl

/-- 基底を持つので、各段はZMod(pᵏ)上の自由加群である。 -/
theorem primePower_free (k : ℕ) : Module.Free (ZMod (p ^ k)) (Torsion E (p ^ k)) :=
  Module.Free.of_basis (primePowerBasis E p k)

/-- 同じ実際の点をp倍する塔の遷移写像。基底選択からは独立である。 -/
noncomputable def primePowerTransition (k : ℕ) : Torsion E (p ^ (k + 1)) →+ Torsion E (p ^ k) where
  toFun P := ⟨p • P.val, by
    change p ^ k • (p • P.val) = 0
    rw [← mul_smul, ← pow_succ]
    exact P.property⟩
  map_zero' := Subtype.ext (nsmul_zero _)
  map_add' P Q := Subtype.ext (map_add (nsmulAddMonoidHom p) P.val Q.val)

/-- 塔の各遷移は全射である。選ばれた各段の基底の互換性は仮定しない。 -/
theorem primePowerTransition_surjective (k : ℕ) : Function.Surjective (primePowerTransition E p k) := by
  intro Q
  obtain ⟨P, hP⟩ := multiplication_surjective E p (Fact.out : p.Prime).ne_zero Q.val
  have hP' : p • P = Q.val := hP
  refine ⟨⟨P, ?_⟩, Subtype.ext hP'⟩
  change p ^ (k + 1) • P = 0
  rw [pow_succ, mul_smul, hP']
  exact Q.property

omit [CharZero K] [E.IsElliptic] [Fact p.Prime] in
/-- 遷移写像は元のガロア作用と可換する。 -/
theorem primePowerTransition_equivariant (k : ℕ) (σ : Field.absoluteGaloisGroup K)
    (P : Torsion E (p ^ (k + 1))) :
    primePowerTransition E p k (representation E (p ^ (k + 1)) σ P) =
      representation E (p ^ k) σ (primePowerTransition E p k P) := by
  apply Subtype.ext
  change p • pointAction E σ P.val = pointAction E σ (p • P.val)
  exact (map_nsmul (pointAction E σ) p P.val).symm

/-- 各段の座標空間上に、同じガロア作用を線形同型に沿って運ぶ。自明な作用とは限らない。 -/
noncomputable def primePowerCoordinateRepresentation (k : ℕ) :
    Representation (ZMod (p ^ k)) (Field.absoluteGaloisGroup K) (Fin 2 → ZMod (p ^ k)) :=
  (primePowerEquiv E p k).conjRingEquiv.toMonoidHom.comp (representation E (p ^ k))

/-- 各段の座標同型は、移した作用に関して同変である。 -/
theorem primePowerCoordinate_equivariant (k : ℕ) (σ : Field.absoluteGaloisGroup K)
    (P : Torsion E (p ^ k)) :
    primePowerEquiv E p k (representation E (p ^ k) σ P) =
      primePowerCoordinateRepresentation E p k σ (primePowerEquiv E p k P) := by
  change primePowerEquiv E p k (representation E (p ^ k) σ P) =
    primePowerEquiv E p k (representation E (p ^ k) σ ((primePowerEquiv E p k).symm (primePowerEquiv E p k P)))
  rw [(primePowerEquiv E p k).symm_apply_apply]

end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
