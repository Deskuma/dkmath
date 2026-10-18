/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.PhaseObstructionTransport

#print "file: DkMath.Lib.NumberTheory.IdealGaloisTransport"

/-!
# IRR-006: 環同型による実際のイデアル根の輸送

`Ideal.map` を使って根そのものを運び、Mathlib の `ClassGroup.mulEquiv` と接続する。
正の指数の冪写像は Dedekind 環のイデアル上で単射である。類群上の冪写像の
単射性（正則性）は使わない。この区別により非自明な p-torsion も保存される。
-/

namespace DkMath.Lib.NumberTheory
open scoped nonZeroDivisors

variable {R S : Type*} [CommRing R] [IsDedekindDomain R]
  [CommRing S] [IsDedekindDomain S]

/-- 非零イデアルを実際に写す。環同型の単射性により非零性が保たれる。 -/
def mapNonzeroIdeal (e : R ≃+* S) (I : (Ideal R)⁰) : (Ideal S)⁰ :=
  ⟨Ideal.map e I, mem_nonZeroDivisors_iff_ne_zero.mpr (by
    intro h
    exact (mem_nonZeroDivisors_iff_ne_zero.mp I.property)
      ((Ideal.map_eq_bot_iff_of_injective e.injective).mp h))⟩

private theorem fractional_map_ideal (e : R ≃+* S) (I : Ideal R) :
    FractionalIdeal.ringEquivOfRingEquiv (FractionRing R) (FractionRing S) e
      (I : FractionalIdeal R⁰ (FractionRing R)) =
      (Ideal.map e I : FractionalIdeal S⁰ (FractionRing S)) := by
  ext x
  simp only [FractionalIdeal.ringEquivOfRingEquiv_apply,
    FractionalIdeal.mem_coeIdeal]
  constructor
  · rintro ⟨y, ⟨r, hr, rfl⟩, rfl⟩
    exact ⟨e r, Ideal.mem_map_of_mem e hr, by
      change algebraMap S (FractionRing S) (e r) =
        IsFractionRing.ringEquivOfRingEquiv (K := FractionRing R) (L := FractionRing S) e
          (algebraMap R (FractionRing R) r)
      exact (IsFractionRing.ringEquivOfRingEquiv_algebraMap e r).symm⟩
  · rintro ⟨s, hs, rfl⟩
    refine ⟨algebraMap R (FractionRing R) (e.symm s), ⟨e.symm s, ?_, rfl⟩, ?_⟩
    · obtain ⟨r, hr, he⟩ := (Ideal.mem_map_of_equiv e s).mp hs
      simpa [← he] using hr
    · change IsFractionRing.ringEquivOfRingEquiv
        (K := FractionRing R) (L := FractionRing S) e
        (algebraMap R (FractionRing R) (e.symm s)) = algebraMap S (FractionRing S) s
      rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap, e.apply_symm_apply]

/-- Mathlib の類群同型は、非零イデアルの実際の像の類を与える。 -/
theorem classGroup_map_mk0 (e : R ≃+* S) (I : (Ideal R)⁰) :
    ClassGroup.mulEquiv e (ClassGroup.mk0 I) = ClassGroup.mk0 (mapNonzeroIdeal e I) := by
  apply (ClassGroup.equiv (FractionRing S)).injective
  simp only [ClassGroup.mulEquiv, MulEquiv.trans_apply, ClassGroup.equiv_mk0,
    MulEquiv.apply_symm_apply]
  change QuotientGroup.mk' _
      (Units.mapEquiv (FractionalIdeal.ringEquivOfRingEquiv
        (FractionRing R) (FractionRing S) e).toMulEquiv
        (FractionalIdeal.mk0 (FractionRing R) I)) = _
  congr 1
  apply Units.ext
  exact fractional_map_ideal e I

/-- 恒等環同型は類群の全ての類を固定する。 -/
theorem classGroup_map_refl (w : ClassGroup R) :
    ClassGroup.mulEquiv (RingEquiv.refl R) w = w := by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective w
  rw [classGroup_map_mk0]
  congr 1
  apply Subtype.ext
  exact Ideal.map_id _

/-- 環同型の合成と類群作用の合成は一致する。 -/
theorem classGroup_map_trans {T : Type*} [CommRing T] [IsDedekindDomain T]
    (e : R ≃+* S) (f : S ≃+* T) (w : ClassGroup R) :
    ClassGroup.mulEquiv (e.trans f) w = ClassGroup.mulEquiv f (ClassGroup.mulEquiv e w) := by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective w
  rw [classGroup_map_mk0, classGroup_map_mk0, classGroup_map_mk0]
  congr 1
  apply Subtype.ext
  exact (Ideal.map_map (I := (I : Ideal R)) (e : R →+* S) (f : S →+* T)).symm

namespace IdealPowerObstruction
variable {p : ℕ} {Q : R}

/-- 元・イデアル根・冪等式を同時に輸送する。根の主イデアル化は要求しない。 -/
def transport (E : IdealPowerObstruction R p Q) (e : R ≃+* S) :
    IdealPowerObstruction S p (e Q) where
  root := mapNonzeroIdeal e E.root
  equation := by
    change Ideal.span ({e Q} : Set S) = (Ideal.map e (E.root : Ideal R)) ^ p
    rw [← Ideal.map_pow, ← E.equation, Ideal.map_span]
    simp

/-- 障害の輸送は実際の類群同型である。 -/
theorem obstruction_transport (E : IdealPowerObstruction R p Q) (e : R ≃+* S) :
    (E.transport e).obstruction = ClassGroup.mulEquiv e E.obstruction :=
  (classGroup_map_mk0 e E.root).symm

/-- 像の元が単元倍で一致すれば、任意に選んだ対象側の根も像の根と一致する。
ここで打ち消すのはイデアルの p 乗であって、類群の p 乗ではない。 -/
theorem root_transport_of_unit (E : IdealPowerObstruction R p Q)
    {T : S} (F : IdealPowerObstruction S p T) (e : R ≃+* S)
    (hp : p ≠ 0) (u : Sˣ) (h : e Q = u * T) :
    mapNonzeroIdeal e E.root = F.root := by
  apply Subtype.ext
  apply pow_left_injective hp
  change ((E.transport e).root : Ideal S) ^ p = (F.root : Ideal S) ^ p
  rw [← (E.transport e).equation, h, Ideal.span_singleton_mul_left_unit u.isUnit,
    F.equation]

/-- 単元補正はイデアル類から消える。元の単元冪障害が消えるとは主張しない。 -/
theorem obstruction_transport_of_unit (E : IdealPowerObstruction R p Q)
    {T : S} (F : IdealPowerObstruction S p T) (e : R ≃+* S)
    (hp : p ≠ 0) (u : Sˣ) (h : e Q = u * T) :
    ClassGroup.mulEquiv e E.obstruction = F.obstruction := by
  rw [← E.obstruction_transport e]
  exact congrArg ClassGroup.mk0 (E.root_transport_of_unit F e hp u h)

end IdealPowerObstruction

namespace PhaseClassPacket
variable {p : ℕ} {ι : Type*}

/-- 係数が固定されない場合にも、因子族全体とその実際のイデアル根を運べる。
これはラベルだけを変更する `reindex` とは異なる操作である。 -/
def transport (C : PhaseClassPacket R p ι) (e : R ≃+* S) : PhaseClassPacket S p ι where
  factor i := e (C.factor i)
  power i := (C.power i).transport e

/-- 族全体の輸送は各位相の類群作用と一致する。座標の固定性は不要。 -/
theorem obstruction_transport (C : PhaseClassPacket R p ι) (e : R ≃+* S) (i : ι) :
    (C.transport e).obstruction i = ClassGroup.mulEquiv e (C.obstruction i) :=
  (C.power i).obstruction_transport e

end PhaseClassPacket
end DkMath.Lib.NumberTheory
