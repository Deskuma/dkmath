/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.NumberFieldInertiaGeneration
import DkMath.Lib.RepresentationTheory.LocalFixedCofixed

#print "file: DkMath.Lib.NumberTheory.NumberFieldInertiaRepresentation"

/-!
# NOTE-031-001A: 有限ガロア拡大で慣性自明性を大域Fixed/Cofixedへ移す

K/ℚの全有限素点の慣性群が全群を生成する算術を、実際の表現へ適用する。
生成性・不分岐拡大不存在をproviderとして仮定しない。係数加群の有限性も不要である。
同じ表現ρと同じ部分加群Nの作用を、全ての素点で同じ側に保って輸送する。

ここでの群は有限ガロア群Gal(K/ℚ)である。絶対ガロア群から有限段階への
慣性の持ち上げ・制限との対応は031-001Bへ残す。
Frey Sourceの031-002〜005の局所算術やhcasesそのものを証明したとはしない。
-/
namespace DkMath.Lib.NumberTheory.NumberFieldInertiaRepresentation
open scoped NumberField
open DkMath.Lib.RepresentationTheory LocalFixedCofixed
variable {K R V : Type*} [Field K] [NumberField K] [IsGalois ℚ K]
  [CommRing R] [AddCommGroup V] [Module R V]

/-- 全有限素点の慣性群でNが点ごとに固定されれば、Gal(K/ℚ)全体でFixedとなる。 -/
theorem isFixedOn_of_inertia (ρ : Representation R (K ≃ₐ[ℚ] K) V) (N : Submodule R V)
    (hlocal : ∀ P : Ideal (𝓞 K), P.IsMaximal → FixedOn ρ N (P.inertia (K ≃ₐ[ℚ] K))) :
    IsFixedOn ρ N :=
  isFixedOn_of_iSup_eq_top (fun P : {P : Ideal (𝓞 K) // P.IsMaximal} => P.val.inertia (K ≃ₐ[ℚ] K))
    NumberFieldInertiaGeneration.iSup_inertia_eq_top ρ N (fun P => hlocal P.val P.property)

/-- 全有限素点の慣性群で商の変化量がNへ入れば、大域でもCofixedとなる。
生成性は有限拡大のMinkowskiの議論から供給し、商を別の表現へすり替えない。 -/
theorem isCofixedOn_of_inertia (ρ : Representation R (K ≃ₐ[ℚ] K) V) (N : Submodule R V)
    (hlocal : ∀ P : Ideal (𝓞 K), P.IsMaximal → CofixedOn ρ N (P.inertia (K ≃ₐ[ℚ] K))) :
    IsCofixedOn ρ N :=
  isCofixedOn_of_iSup_eq_top (fun P : {P : Ideal (𝓞 K) // P.IsMaximal} => P.val.inertia (K ≃ₐ[ℚ] K))
    NumberFieldInertiaGeneration.iSup_inertia_eq_top ρ N (fun P => hlocal P.val P.property)

/-- 全慣性群で共通の側を選んだ二択を、大域のFixed/Cofixed二択へ移す。
各素点で独立に二択を選ぶ前提とは異なることを型に保持する。 -/
theorem fixed_or_cofixed_of_inertia_common_side (ρ : Representation R (K ≃ₐ[ℚ] K) V)
    (N : Submodule R V)
    (hside : (∀ P : Ideal (𝓞 K), P.IsMaximal → FixedOn ρ N (P.inertia (K ≃ₐ[ℚ] K))) ∨
      (∀ P : Ideal (𝓞 K), P.IsMaximal → CofixedOn ρ N (P.inertia (K ≃ₐ[ℚ] K)))) :
    IsFixedOn ρ N ∨ IsCofixedOn ρ N :=
  hside.elim (fun h => Or.inl (isFixedOn_of_inertia ρ N h))
    (fun h => Or.inr (isCofixedOn_of_inertia ρ N h))

end DkMath.Lib.NumberTheory.NumberFieldInertiaRepresentation
