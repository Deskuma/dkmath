/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.KUS.Blueprint

#print "file: DkMath.KUS.Core"

namespace DkMath.KUS

universe u v

set_option linter.dupNamespace false

/--
`KUS` の最小核。

`coeff` は観測される可視係数であり、`unit` と `blueprint` は係数が 0 でも保持される。
-/
@[ext] structure KUS (U : Type u) (Blueprint : BlueprintFamily U) where
  coeff : Nat
  unit : U
  blueprint : Blueprint unit

variable {U : Type u}
variable {Blueprint : BlueprintFamily U}

/-- KUS から構造保持側 `US` だけを取り出す。 -/
@[simp] def toUS (x : KUS U Blueprint) : US U Blueprint where
  unit := x.unit
  blueprint := x.blueprint

/-- 固定された `US` 上で係数だけを差し替えて KUS を作る。 -/
@[simp] def mkWith (coeff : Nat) (support : US U Blueprint) : KUS U Blueprint where
  coeff := coeff
  unit := support.unit
  blueprint := support.blueprint

/-- 可視係数だけが零化した構造保持零。 -/
@[simp] def zeroState (support : US U Blueprint) : KUS U Blueprint :=
  mkWith 0 support

@[simp] theorem coeff_mkWith (coeff : Nat) (support : US U Blueprint) :
    (mkWith coeff support).coeff = coeff := rfl

@[simp] theorem toUS_mkWith (coeff : Nat) (support : US U Blueprint) :
  toUS (mkWith coeff support) = support := by
  cases support
  rfl

@[simp] theorem coeff_zeroState (support : US U Blueprint) :
    (zeroState support).coeff = 0 := rfl

@[simp] theorem toUS_zeroState (support : US U Blueprint) :
    toUS (zeroState support) = support := by
  simp [zeroState]

end DkMath.KUS
