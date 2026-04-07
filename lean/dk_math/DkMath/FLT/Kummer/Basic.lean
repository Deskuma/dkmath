/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.PrimeProvider.TriominoCosmicBranchADescentChain

#print "file: DkMath.FLT.Kummer.Basic"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

open DkMath.CosmicFormulaBinom

/-!
# Kummer Branch — Abstract Targets for Stage 2 (Global)

## 背景

primitive 側の `2m-global` を解析した結果、内部は 2 段に分かれる:
- **Stage 1 (LOCAL)**: z' mod q^p の Hensel lift → `2m-local` が concrete に担当済み ✅
- **Stage 2 (GLOBAL)**: z' mod q^p → z' ∈ ℤ → Kummer 理論 / ℤ[ζ_p] ideal class group に帰着

さらに `2m-global` と `2m-pure` の formal gap を解析した結果:
- `q ∤ (z-y)` のとき（actual DescentChain path）: witness R の Φ_p(R) = 0 は自動充足 ✅
- `q | (z-y)` かつ `q ≠ p` のとき: `2m-global` は vacuously true → **genuine gap**

このモジュールは、後者の gap-divisible branch を isolate し、
Kummer 語彙の abstract target を DkMath 幹線に接続する。

## 設計

新設する target:
1. `GapDivisibleBranchTarget` — `q | (z-y)` branch の isolate
2. `CyclotomicPrincipalizationTarget` — Kummer principalization 仮定
3. `CyclotomicClassGroupPTorsionFreeTarget` — class group 仮定の器

依存の向き:
```
ClassGroupPTorsionFree → CyclotomicPrincipalization → GapDivisibleBranch → 2m-pure → FLT
```
-/

namespace DkMath.FLT

/-!
## §1. Descent existence の存在版同値

`descentExistence_iff_gnReduction` の ∃ 量化版。
GN 語彙と z' 語彙を自由に行き来するための基盤。
-/

/--
存在版: `(∃ g', g' · GN(p, g', y) = xq^p) ↔ (∃ z', z'^p = xq^p + y^p)`。

`descentExistence_iff_gnReduction` の存在量化持ち上げ。
Kummer 側では z' 語彙、Cosmic 側では g' 語彙を使えるようにする。
-/
theorem descentExistence_exists_iff_gnReduction_exists (p y xq : ℕ) :
    (∃ g' : ℕ, g' * GN p g' y = xq ^ p) ↔
    (∃ z' : ℕ, z' ^ p = xq ^ p + y ^ p) := by
  constructor
  · rintro ⟨g', hg'⟩
    exact ⟨g' + y, (descentExistence_iff_gnReduction p g' y xq).mp hg'⟩
  · rintro ⟨z', hz'⟩
    by_cases h : y ≤ z'
    · exact ⟨z' - y, (descentExistence_iff_gnReduction p (z' - y) y xq).mpr
        (by rw [Nat.sub_add_cancel h]; exact hz')⟩
    · -- z' < y のとき z'^p = xq^p + y^p ≥ y^p > z'^p で矛盾
      push_neg at h
      exfalso
      by_cases hp : p = 0
      · subst hp; simp at hz'
      · have : y ^ p ≤ z' ^ p := by omega
        exact not_le.mpr (Nat.pow_lt_pow_left (by omega) (by omega)) this

end DkMath.FLT
