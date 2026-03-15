/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.KUS.Transport
import DkMath.DHNT.DHNT_Base

#print "file: DkMath.KUS.Bridge"

/-!
## DkMath.KUS.Bridge

`DHNT.Qty`（連続スケール世界）と `GKUS`（依存型 support 世界）の
最小接続層。

接続の方向: **DHNT → KUS**（埋め込み・一方向）

```
DHNT.Qty  ──embedQty──▶  GKUS ℝ ℕ DHNTBlueprint
                                  │
                         HarmonizeSpec (addViaSpec)
                                  │
                         harmonizeAdd / harmonizeMul
```

詳細設計: `DkMath/KUS/docs/KUS-bridge-design-spec.md`
-/

namespace DkMath.KUS.Bridge

open DkMath.KUS
open DkMath.DHNT

/-! ## trivial blueprint for DHNT -/

/-- DHNT 接続用 trivial blueprint family。unit 値によらず blueprint は `Fin 1` 。 -/
abbrev DHNTBlueprint : BlueprintFamily ℕ := fun _ => Fin 1

/-- trivial blueprint の唯一の値。 -/
@[simp] def trivialBlueprint (n : ℕ) : DHNTBlueprint n := ⟨0, by omega⟩

/-! ## phiUnit — 離散化写像 -/

/-- `DHNT.Unit`（`ℝ > 0`）を `ℕ` へ離散化する。`⌊u.val⌋₊` を採用。 -/
noncomputable def phiUnit (u : DHNT.Unit) : ℕ :=
  ⌊u.val⌋₊

@[simp] theorem phiUnit_pos (u : DHNT.Unit) : 0 < phiUnit u ↔ 1 ≤ u.val := by
  simp [phiUnit, Nat.floor_pos]

@[simp] theorem phiUnit_one : phiUnit ⟨1, one_pos⟩ = 1 := by
  simp [phiUnit]

/-! ## embedQty — Qty → GKUS の埋め込み -/

/-- `Qty` を `GKUS ℝ ℕ DHNTBlueprint` へ埋め込む。
blueprint は trivial（`Fin 1`）固定。 -/
noncomputable def embedQty (q : Qty) : GKUS ℝ ℕ DHNTBlueprint :=
  mkGWith q.x ⟨phiUnit q.u, trivialBlueprint (phiUnit q.u)⟩

@[simp] theorem toCoeff_embedQty (q : Qty) :
    toCoeff (embedQty q) = q.x := rfl

@[simp] theorem extract_g_embedQty (q : Qty) :
    (extract_g (embedQty q)).unit = phiUnit q.u := rfl

/-! ## encConst — 定数 unit への ScaleSpec -/

/-- unit を定数 `n : ℕ` に写す trivial `ScaleSpec`。
-/
@[simp] def encConst (n : ℕ) : ScaleSpec ℕ DHNTBlueprint ℕ DHNTBlueprint where
  mapUnit    := fun _ => n
  mapBlueprint := fun {_} _ => trivialBlueprint n

@[simp] theorem scaleUS_encConst (n : ℕ) (s : US ℕ DHNTBlueprint) :
    ScaleSpec.scaleUS (encConst n) s = ⟨n, trivialBlueprint n⟩ := by
  simp [ScaleSpec.scaleUS, encConst, trivialBlueprint]

/-! ## addViaSpec — addVia に対応する HarmonizeSpec -/

/-- 共通単位 `w` への encode を表す `HarmonizeSpec`。
`Qty.addVia w` の KUS 対応物。 -/
noncomputable def addViaSpec (w : DHNT.Unit) :
    HarmonizeSpec ℝ ℕ DHNTBlueprint ℕ DHNTBlueprint ℕ DHNTBlueprint :=
  HarmonizeSpec.mkHarmonizeFixed
    (encConst (phiUnit w))
    (encConst (phiUnit w))
    ⟨phiUnit w, trivialBlueprint (phiUnit w)⟩
    (fun x => by simp [ScaleSpec.scaleUS])
    (fun y => by simp [ScaleSpec.scaleUS])

/-! ## 基本補題 -/

/-- `addViaSpec` で加算した係数は元の係数の和に等しい。 -/
@[simp] theorem addVia_toCoeff (w : DHNT.Unit) (a b : Qty) :
    toCoeff (HarmonizeSpec.harmonizeAdd (addViaSpec w) (embedQty a) (embedQty b))
      = a.x + b.x := by
  simpa using HarmonizeSpec.toCoeff_harmonizeAdd
    (hs := addViaSpec w) (x := embedQty a) (y := embedQty b)

/-- `harmonizeAdd (addViaSpec w)` の結果 unit は `phiUnit w` に等しい。 -/
@[simp] theorem addVia_unit (w : DHNT.Unit) (a b : Qty) :
    (extract_g (HarmonizeSpec.harmonizeAdd (addViaSpec w) (embedQty a) (embedQty b))).unit
      = phiUnit w := by
  simp [HarmonizeSpec.harmonizeAdd, HarmonizeSpec.encodeLeft,
    ScaleSpec.scaleGKUS, ScaleSpec.scaleUS, gOp, addViaSpec,
    HarmonizeSpec.mkHarmonizeFixed, HarmonizeSpec.mkHarmonize,
    encConst, embedQty, mkGWith, extract_g]

/-! ## addVia_natural の KUS 対応 -/

/--
`Qty.addVia_natural` の KUS 対応補題。

DHNT では `convert (addVia w₁ a b) w₂ = addVia w₂ a b`。
KUS では decode 先を `w₂` に換えることが `harmonizeAddTo_decode_comp` に対応する。

本補題は「`w₁` で合流した結果を `w₂` へ re-encode することが、
最初から `w₂` で合流したのと係数上で一致する」ことを示す。
-/
theorem addVia_natural_toCoeff
    (w₁ w₂ : DHNT.Unit) (a b : Qty) :
    toCoeff (ScaleSpec.scaleGKUS (encConst (phiUnit w₂))
        (HarmonizeSpec.harmonizeAdd (addViaSpec w₁) (embedQty a) (embedQty b)))
      = toCoeff (HarmonizeSpec.harmonizeAdd (addViaSpec w₂) (embedQty a) (embedQty b)) := by
  simp only [ScaleSpec.toCoeff_scaleGKUS, addVia_toCoeff]

/--
`addVia_natural_toCoeff` の `harmonizeAddTo` 版。
decode 仕様の合成可換性 `harmonizeAddTo_decode_comp` との対応を明示。
-/
theorem addVia_natural_harmonizeAddTo
    (w₁ w₂ : DHNT.Unit) (a b : Qty) :
    toCoeff (HarmonizeSpec.harmonizeAddTo (addViaSpec w₁)
        ⟨ScaleSpec.comp (encConst (phiUnit w₂)) (encConst (phiUnit w₁))⟩
        (embedQty a) (embedQty b))
      = a.x + b.x := by
  simp only [HarmonizeSpec.toCoeff_harmonizeAddTo, toCoeff_embedQty]

/-! ## mulViaSpec — 乗法 bridge -/

/--
乗法用 `HarmonizeSpec`。`Qty` の乗法では単位が `u * v`（積）になる。
KUS 側では encode 先を `phiUnit w` に固定した `addViaSpec` と同じ形。
-/
noncomputable def mulViaSpec (w : DHNT.Unit) :
    HarmonizeSpec ℝ ℕ DHNTBlueprint ℕ DHNTBlueprint ℕ DHNTBlueprint :=
  addViaSpec w   -- spec は加算と共通（支持先は同じ `phiUnit w`）

/--
`mulViaSpec` で乗算した係数は元の係数の積に等しい。
-/
@[simp] theorem mulVia_toCoeff (w : DHNT.Unit) (a b : Qty) :
    toCoeff (HarmonizeSpec.harmonizeMul (mulViaSpec w) (embedQty a) (embedQty b))
      = a.x * b.x := by
  simpa using HarmonizeSpec.toCoeff_harmonizeMul
    (hs := mulViaSpec w) (x := embedQty a) (y := embedQty b)

/-- `harmonizeMul (mulViaSpec w)` の結果 unit は `phiUnit w` に等しい。 -/
@[simp] theorem mulVia_unit (w : DHNT.Unit) (a b : Qty) :
    (extract_g (HarmonizeSpec.harmonizeMul (mulViaSpec w) (embedQty a) (embedQty b))).unit
      = phiUnit w := by
  simp [HarmonizeSpec.harmonizeMul, HarmonizeSpec.encodeLeft,
    ScaleSpec.scaleGKUS, ScaleSpec.scaleUS, gOp, mulViaSpec, addViaSpec,
    HarmonizeSpec.mkHarmonizeFixed, HarmonizeSpec.mkHarmonize,
    encConst, embedQty, mkGWith, extract_g]

end DkMath.KUS.Bridge
