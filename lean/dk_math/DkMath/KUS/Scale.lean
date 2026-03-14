/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.KUS.Monoid

namespace DkMath.KUS

universe u v u' v'

variable {U : Type u}
variable {Blueprint : BlueprintFamily U}
variable {V : Type u'}
variable {Blueprint' : BlueprintFamily V}

/--
`ScaleSpec` は、unit 変更と blueprint transport を束ねた最小仕様。

`mapBlueprint` は依存型として
`Blueprint u -> Blueprint' (mapUnit u)`
を与える。
-/
structure ScaleSpec
    (U : Type u) (Blueprint : BlueprintFamily U)
    (V : Type u') (Blueprint' : BlueprintFamily V) where
  mapUnit : U → V
  mapBlueprint : ∀ {u : U}, Blueprint u → Blueprint' (mapUnit u)

namespace ScaleSpec

variable (σ : ScaleSpec U Blueprint V Blueprint')

/-- `US` の scale。 -/
@[simp] def scaleUS (x : US U Blueprint) : US V Blueprint' where
  unit := σ.mapUnit x.unit
  blueprint := σ.mapBlueprint x.blueprint

/-- `KUS` の scale（可視係数は保存）。 -/
@[simp] def scaleKUS (x : KUS U Blueprint) : KUS V Blueprint' where
  coeff := x.coeff
  unit := (scaleUS σ (toUS x)).unit
  blueprint := (scaleUS σ (toUS x)).blueprint

@[simp] theorem toUS_scaleKUS (x : KUS U Blueprint) :
    toUS (scaleKUS σ x) = scaleUS σ (toUS x) := by
  cases x
  rfl

@[simp] theorem extract_scaleKUS (x : KUS U Blueprint) :
    extract (scaleKUS σ x) = scaleUS σ (extract x) := by
  simp [extract]

@[simp] theorem toNat_scaleKUS (x : KUS U Blueprint) :
    toNat (scaleKUS σ x) = toNat x :=
  rfl

@[simp] theorem scaleKUS_zeroState (support : US U Blueprint) :
    scaleKUS σ (zeroState support) = zeroState (scaleUS σ support) := by
  rfl

/-- 恒等 scale。 -/
@[simp] def idScale : ScaleSpec U Blueprint U Blueprint where
  mapUnit := fun x => x
  mapBlueprint := fun {_u} b => b

@[simp] theorem scaleUS_id (x : US U Blueprint) :
    scaleUS (idScale (U := U) (Blueprint := Blueprint)) x = x := by
  cases x
  rfl

@[simp] theorem scaleKUS_id (x : KUS U Blueprint) :
    scaleKUS (idScale (U := U) (Blueprint := Blueprint)) x = x := by
  cases x
  rfl

/-- scale 仕様の合成。 -/
@[simp] def comp
    {W : Type _} {Blueprint'' : BlueprintFamily W}
    (τ : ScaleSpec V Blueprint' W Blueprint'')
    (σ : ScaleSpec U Blueprint V Blueprint') :
    ScaleSpec U Blueprint W Blueprint'' where
  mapUnit := fun u => τ.mapUnit (σ.mapUnit u)
  mapBlueprint := fun {_} b => τ.mapBlueprint (σ.mapBlueprint b)

@[simp] theorem scaleUS_comp
    {W : Type _} {Blueprint'' : BlueprintFamily W}
    (τ : ScaleSpec V Blueprint' W Blueprint'')
    (σ : ScaleSpec U Blueprint V Blueprint')
    (x : US U Blueprint) :
    scaleUS (comp τ σ) x = scaleUS τ (scaleUS σ x) := by
  cases x
  rfl

@[simp] theorem scaleKUS_comp
    {W : Type _} {Blueprint'' : BlueprintFamily W}
    (τ : ScaleSpec V Blueprint' W Blueprint'')
    (σ : ScaleSpec U Blueprint V Blueprint')
    (x : KUS U Blueprint) :
    scaleKUS (comp τ σ) x = scaleKUS τ (scaleKUS σ x) := by
  cases x
  rfl

@[simp] theorem scaleKUS_toKUS
    (support : US U Blueprint)
    (n : Fiber support) :
    scaleKUS σ (Fiber.toKUS support n)
      = Fiber.toKUS (scaleUS σ support) n := by
  cases support
  rfl

@[simp] theorem extract_scaleKUS_toKUS
    (support : US U Blueprint)
    (n : Fiber support) :
    extract (scaleKUS σ (Fiber.toKUS support n)) = scaleUS σ support := by
  rw [scaleKUS_toKUS (σ := σ) support n]
  simp

@[simp] theorem toNat_scaleKUS_toKUS_add
    (support : US U Blueprint)
    (n m : Fiber support) :
    toNat (scaleKUS σ (Fiber.toKUS support (n + m)))
      = toNat (scaleKUS σ (Fiber.toKUS support n))
        + toNat (scaleKUS σ (Fiber.toKUS support m)) := by
  simp

end ScaleSpec

/-! ## phase-08: non-breaking API aliases -/

/-- `ScaleSpec.scaleKUS_toKUS` の短い別名（非破壊 alias）。 -/
theorem scale_toKUS
    {σ : ScaleSpec U Blueprint V Blueprint'}
    (support : US U Blueprint)
    (n : Fiber support) :
    ScaleSpec.scaleKUS σ (Fiber.toKUS support n)
      = Fiber.toKUS (ScaleSpec.scaleUS σ support) n :=
  ScaleSpec.scaleKUS_toKUS (σ := σ) support n

/-- `ScaleSpec.extract_scaleKUS_toKUS` の短い別名（非破壊 alias）。 -/
theorem extract_scale_toKUS
    {σ : ScaleSpec U Blueprint V Blueprint'}
    (support : US U Blueprint)
    (n : Fiber support) :
  extract (ScaleSpec.scaleKUS σ (Fiber.toKUS support n)) = ScaleSpec.scaleUS σ support :=
  ScaleSpec.extract_scaleKUS_toKUS (σ := σ) support n

/-- `ScaleSpec.toNat_scaleKUS_toKUS_add` の短い別名（非破壊 alias）。 -/
theorem toNat_scale_toKUS_add
    {σ : ScaleSpec U Blueprint V Blueprint'}
    (support : US U Blueprint)
    (n m : Fiber support) :
    toNat (ScaleSpec.scaleKUS σ (Fiber.toKUS support (n + m)))
      = toNat (ScaleSpec.scaleKUS σ (Fiber.toKUS support n))
        + toNat (ScaleSpec.scaleKUS σ (Fiber.toKUS support m)) :=
  ScaleSpec.toNat_scaleKUS_toKUS_add (σ := σ) support n m

end DkMath.KUS
