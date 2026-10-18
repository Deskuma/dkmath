/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.PrincipalIdealPower

#print "file: DkMath.Lib.NumberTheory.IdealPowerObstruction"

/-!
# IRR-001: 元の冪を抽出する前に、イデアル類の障害を保持する

`(Q)=I^p` はイデアルの等式であり `Q=εβ^p` とは異なる。
非零な I 自身を保存し、その実際の類 `ω=[I]` を観測する。
常に ω^p=1 だが、ω=1 は別の数学的事実である。
正則性は ω=1 を一律に供給する十分条件であり、定義には入れない。
-/

namespace DkMath.Lib.NumberTheory

open scoped nonZeroDivisors

/-- 選んだ非零イデアル根と、その同じ根の p 乗であるという等式。
観測する類を任意に付け足さず、必ずこの root から計算する。 -/
structure IdealPowerObstruction (R : Type*) [CommRing R] [IsDedekindDomain R]
    (p : ℕ) (Q : R) where
  root : (Ideal R)⁰
  equation : Ideal.span ({Q} : Set R) = (root : Ideal R) ^ p

namespace IdealPowerObstruction

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {p : ℕ} {Q : R}

/-- IRR-001 の観測値。非零性は root の型に保持される。 -/
noncomputable def obstruction (E : IdealPowerObstruction R p Q) : ClassGroup R :=
  ClassGroup.mk0 E.root

/-- 主イデアルの p 乗根の類は p-torsion に入る。正則性は不要。 -/
theorem torsion (E : IdealPowerObstruction R p Q) : E.obstruction ^ p = 1 := by
  rw [obstruction, ← map_pow]
  apply (ClassGroup.mk0_eq_one_iff (E.root ^ p).property).mpr
  change ((E.root : Ideal R) ^ p).IsPrincipal
  rw [← E.equation]
  exact ⟨Q, rfl⟩

/-- 障害の消滅は、記録した同じイデアル根の主性と同値。 -/
theorem trivial_iff_principal (E : IdealPowerObstruction R p Q) :
    E.obstruction = 1 ↔ (E.root : Ideal R).IsPrincipal :=
  ClassGroup.mk0_eq_one_iff E.root.property

/-- 正則な場合は全障害が消える。非正則な場合にこの引数を自動生成しない。 -/
theorem trivial_of_torsionFree (E : IdealPowerObstruction R p Q)
    (hfree : classGroupPTorsionFreeAt R p) : E.obstruction = 1 := hfree _ E.torsion

/-- 個々の障害が消えた場合だけ、同じ根 I の生成元と単元を復元する。
単元を捨てず、次の IRR-004 へ運ぶ。 -/
theorem exists_unit_generator (E : IdealPowerObstruction R p Q) (h : E.obstruction = 1) :
    ∃ (u : Rˣ) (b : R), Ideal.span ({b} : Set R) = (E.root : Ideal R) ∧ Q = u * b ^ p := by
  obtain ⟨u, b, hu, hb, he⟩ := exists_unit_mul_pow_of_span_eq_pow_of_isPrincipal
    (E.trivial_iff_principal.mp h) E.equation
  exact ⟨hu.unit, b, hb, by simpa only [IsUnit.unit_spec] using he⟩

/-- 同じイデアル根の生成元を保つ冪表示が得られることの必要十分条件。 -/
theorem trivial_iff_generator (E : IdealPowerObstruction R p Q) :
    E.obstruction = 1 ↔ ∃ (u : Rˣ) (b : R),
      Ideal.span ({b} : Set R) = (E.root : Ideal R) ∧ Q = u * b ^ p := by
  refine ⟨E.exists_unit_generator, ?_⟩
  rintro ⟨u, b, hb, _⟩
  apply E.trivial_iff_principal.mpr
  rw [← hb]
  exact ⟨b, rfl⟩

/-- 非自明障害なら、記録した根を主イデアルとして取り出すことはできない。 -/
theorem not_principal_of_nontrivial (E : IdealPowerObstruction R p Q) (h : E.obstruction ≠ 1) :
    ¬ (E.root : Ideal R).IsPrincipal := fun hI => h (E.trivial_iff_principal.mpr hI)

/-- 非零イデアルの冪は非零なので、対象 Q も非零である。 -/
theorem nonzero (E : IdealPowerObstruction R p Q) : Q ≠ 0 := by
  intro hQ
  have hroot : (E.root : Ideal R) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp E.root.property
  apply pow_ne_zero p hroot
  rw [← E.equation, hQ, Ideal.span_singleton_eq_bot.mpr rfl]
  rfl

/-- イデアルの正冪写像は単射。これは類群の冪写像の単射性とは異なる。
したがって選んだイデアル根の類も、Q と p を固定すれば一意である。 -/
theorem obstruction_independent (E F : IdealPowerObstruction R p Q) (hp : p ≠ 0) :
    E.obstruction = F.obstruction := by
  have hroot : E.root = F.root := Subtype.ext
    (pow_left_injective hp (E.equation.symm.trans F.equation))
  exact congrArg ClassGroup.mk0 hroot

/-- どの元 b による単元倍 p 乗表示でも、理想根の一意性により障害は消える。 -/
theorem trivial_of_unit_power (E : IdealPowerObstruction R p Q) (hp : p ≠ 0)
    (u : Rˣ) (b : R) (he : Q = u * b ^ p) : E.obstruction = 1 := by
  have heq : (E.root : Ideal R) ^ p = Ideal.span ({b} : Set R) ^ p := by
    rw [← E.equation, he, Ideal.span_singleton_mul_left_unit u.isUnit, Ideal.span_singleton_pow]
  have hr := pow_left_injective hp heq
  apply E.trivial_iff_principal.mpr
  rw [hr]
  exact ⟨b, rfl⟩

/-- 個別の類障害の消滅は、元の単元倍 p 乗表示と同値。単元吸収はまだ別問題。 -/
theorem trivial_iff_unit_power (E : IdealPowerObstruction R p Q) (hp : p ≠ 0) :
    E.obstruction = 1 ↔ ∃ (u : Rˣ) (b : R), Q = u * b ^ p := by
  constructor
  · intro h
    obtain ⟨u, b, _, he⟩ := E.exists_unit_generator h
    exact ⟨u, b, he⟩
  · rintro ⟨u, b, he⟩
    exact E.trivial_of_unit_power hp u b he

end IdealPowerObstruction

/-- 非自明な p-torsion の存在。これは特定の GN 位相にその類が現れるという主張ではない。 -/
def HasClassGroupPTorsion (R : Type*) [CommRing R] [IsDomain R] (p : ℕ) : Prop :=
  ∃ w : ClassGroup R, w ^ p = 1 ∧ w ≠ 1

/-- 正則性の失敗と非自明 p-torsion は同値。有限性や類数の計算は不要。 -/
theorem hasClassGroupPTorsion_iff_not_torsionFree
    {R : Type*} [CommRing R] [IsDomain R] {p : ℕ} :
    HasClassGroupPTorsion R p ↔ ¬ classGroupPTorsionFreeAt R p := by
  classical
  constructor
  · rintro ⟨w, hw, hn⟩ hfree
    exact hn (hfree w hw)
  · intro hn
    by_contra hnone
    apply hn
    intro w hw
    by_contra hnon
    exact hnone ⟨w, hw, hnon⟩

end DkMath.Lib.NumberTheory
