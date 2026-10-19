/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.IrregularCharacter37
import DkMath.Lib.NumberTheory.Cyclotomic37CharacterTransport

#print "file: DkMath.FLT.Kummer.IrregularCharacterTransport37"

/-!
# IRR-010: 整数座標のStateの指標別位相輸送

37個の位相の添字iと、36個の指標のラベルmuを区別する。
位相のガロア再索引i↦aiは記録済みの障害を運び、各指標では単元χmu(a)倍となる。
従って非零位相の間では、元ごとの指標支持全体が一致する。
これは既存の同変性を精密化する定理であり、新しい障害消滅条件ではない。
x,yが整数に由来する前提を全ての位相輸送で保持する。
-/
namespace DkMath.FLT.Kummer.IrregularPrime37
open DkMath.Lib.NumberTheory Cyclotomic37CharacterDecomposition
open scoped NumberField
attribute [local instance] prime37 cyclotomic37

/-- 同じ観測障害のベクトル化は、実際のガロア作用と可換である。 -/
theorem observeVector_galois {m : ℕ} (E : RegularDescent.State phase37 (m + 1))
    (A B : ℤ) (hx : E.x = (A : 𝓞 Cyclotomic37)) (hy : E.y = (B : 𝓞 Cyclotomic37))
    (a : (ZMod 37)ˣ) (i : Fin 37) :
    observeVector E (RamifiedPhasePacket.phaseMul a i) = action a (observeVector E i) := by
  apply underlying_injective
  exact (observe_galois E A B hx hy a i).2.symm

/-- 指標ごとの位相輸送。指標値は非零スカラーなので情報を失わない。 -/
theorem observe_projector_galois {m : ℕ} (E : RegularDescent.State phase37 (m + 1))
    (A B : ℤ) (hx : E.x = (A : 𝓞 Cyclotomic37)) (hy : E.y = (B : 𝓞 Cyclotomic37))
    (mu a : (ZMod 37)ˣ) (i : Fin 37) :
    projector mu (observeVector E (RamifiedPhasePacket.phaseMul a i)) =
      ((character mu a : (ZMod 37)ˣ) : ZMod 37) • projector mu (observeVector E i) := by
  rw [observeVector_galois E A B hx hy, projector_action]

/-- 全指標の支持は位相ガロア輸送で保存される。 -/
theorem observe_characterSupport_galois {m : ℕ} (E : RegularDescent.State phase37 (m + 1))
    (A B : ℤ) (hx : E.x = (A : 𝓞 Cyclotomic37)) (hy : E.y = (B : 𝓞 Cyclotomic37))
    (a : (ZMod 37)ˣ) (i : Fin 37) :
    characterSupport (observeVector E (RamifiedPhasePacket.phaseMul a i)) =
      characterSupport (observeVector E i) := by
  rw [observeVector_galois E A B hx hy, characterSupport_action]

/-- 非零36位相は、どの指標に非零射影を持つかまで一致する。 -/
theorem observe_nonzero_characterSupport_eq {m : ℕ} (E : RegularDescent.State phase37 (m + 1))
    (A B : ℤ) (hx : E.x = (A : 𝓞 Cyclotomic37)) (hy : E.y = (B : 𝓞 Cyclotomic37))
    (i : Fin 37) (hi : i ≠ 0) :
    characterSupport (observeVector E i) = characterSupport (observeVector E 1) := by
  obtain ⟨a, ha, _⟩ := RamifiedPhasePacket.exists_phaseMul_one i hi
  simpa only [ha] using observe_characterSupport_galois E A B hx hy a 1

/-- 一つの指標に注目しても、非零位相の非零性は位相1と同値である。 -/
theorem observe_nonzero_projector_iff {m : ℕ} (E : RegularDescent.State phase37 (m + 1))
    (A B : ℤ) (hx : E.x = (A : 𝓞 Cyclotomic37)) (hy : E.y = (B : 𝓞 Cyclotomic37))
    (mu : (ZMod 37)ˣ) (i : Fin 37) (hi : i ≠ 0) :
    projector mu (observeVector E i) ≠ 0 ↔ projector mu (observeVector E 1) ≠ 0 := by
  rw [← mem_characterSupport, ← mem_characterSupport,
    observe_nonzero_characterSupport_eq E A B hx hy i hi]

/-- 位相0のベクトルは全指標で零。非零位相の支持との同値にはi≠0が必要である。 -/
theorem observe_zero_projector {m : ℕ} (E : RegularDescent.State phase37 (m + 1))
    (A B : ℤ) (hx : E.x = (A : 𝓞 Cyclotomic37)) (hy : E.y = (B : 𝓞 Cyclotomic37))
    (mu : (ZMod 37)ˣ) : projector mu (observeVector E 0) = 0 := by
  have hv : observeVector E 0 = 0 :=
    underlying_injective (observe_zero_obstruction_eq_one E A B hx hy)
  rw [hv, map_zero]

/-- Bernoulli32の対象指標では輸送係数はa⁵。この成分の非零性は仮定していない。 -/
theorem observe_bernoulli32_projector_galois {m : ℕ}
    (E : RegularDescent.State phase37 (m + 1)) (A B : ℤ)
    (hx : E.x = (A : 𝓞 Cyclotomic37)) (hy : E.y = (B : 𝓞 Cyclotomic37))
    (a : (ZMod 37)ˣ) (i : Fin 37) :
    projector bernoulli32Label (observeVector E (RamifiedPhasePacket.phaseMul a i)) =
      (a : ZMod 37) ^ 5 • projector bernoulli32Label (observeVector E i) := by
  rw [observe_projector_galois E A B hx hy, bernoulli32_character]
  rfl

end DkMath.FLT.Kummer.IrregularPrime37
