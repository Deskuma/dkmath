/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition
import DkMath.Lib.NumberTheory.BernoulliPrime37

#print "file: DkMath.Lib.NumberTheory.Cyclotomic37CharacterTransport"

/-!
# IRR-010 / IRR-011入口: 指標射影の同変性と標準の冪指標

指標射影の値は固有空間に属する。そこでは全てのガロア元aがχ(a)倍として働く。
射影と作用が可換であることを合わせ、Pμ(σₐx)=χμ(a)Pμ(x)を得る。
χμ(a)は単元なので、零／非零の支持は作用で変わらない。

生成元依存のラベルg^rが、生成元に依存しない冪指標a↦a^rと一致することも証明する。
B₃₂の有限証明書はr=37−32=5というラベルと併記するだけであり、
その指標成分の非零性やHerbrand–Ribetの定理を供給するものではない。
-/
namespace DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition
open scoped NumberField
open Module Polynomial CyclotomicPhaseGalois
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]

/-- 生成元上で一致する二つの指標は、全群上で一致する。 -/
theorem character_ext {χ ψ : (ZMod 37)ˣ →* (ZMod 37)ˣ} (h : χ generator = ψ generator) :
    χ = ψ := by
  ext a
  obtain ⟨t, ht⟩ := exists_generator_pow a
  rw [← ht, map_pow, map_pow, h]

/-- 任意の冪指標を、既存の固有値ラベルで正確に読み替える。 -/
theorem character_generator_pow (r : ℕ) : character (generator ^ r) = powMonoidHom r := by
  apply character_ext
  exact character_generator _

/-- 固有空間の上では、全てのガロア作用が指標値によるスカラー倍になる。 -/
theorem action_apply_component (mu a : (ZMod 37)ˣ) {x : Space K}
    (hx : x ∈ component mu) : action a x = ((character mu a : (ZMod 37)ˣ) : ZMod 37) • x := by
  apply underlying_injective
  rw [underlying_smul]
  exact ((mem_component_iff mu x).mp hx).2 a

/-- 補間射影と真のガロア作用は可換。生成元の冪と多項式の可換性を使う。 -/
theorem projector_action_commute (mu a : (ZMod 37)ˣ) :
    Commute (projector (K := K) mu) (action a) := by
  obtain ⟨t, ht⟩ := exists_generator_pow a
  rw [← ht, map_pow]
  change Commute (aeval operator (Lagrange.basis Finset.univ Units.val mu)) (operator ^ t)
  have h := (Commute.all (Lagrange.basis Finset.univ (Units.val : (ZMod 37)ˣ → ZMod 37) mu)
    (X ^ t)).map (aeval (operator (K := K)))
  simpa only [map_pow, aeval_X] using h

/-- 各指標に射影した後のガロア輸送は、対応する単元スカラーを掛けるだけである。 -/
theorem projector_action (mu a : (ZMod 37)ˣ) (x : Space K) :
    projector mu (action a x) = ((character mu a : (ZMod 37)ˣ) : ZMod 37) • projector mu x := by
  have he := DkMath.Lib.LinearAlgebra.FiniteSpectrumProjectors.projector_eigen
    Units.val (operator (K := K)) aeval_nodal mu x
  have hm : projector mu x ∈ component mu := Module.End.mem_eigenspace_iff.mpr he
  calc
    projector mu (action a x) = action a (projector mu x) :=
      LinearMap.congr_fun (projector_action_commute mu a).eq x
    _ = _ := action_apply_component mu a hm

/-- 指標値は単元なので、射影の零性はガロア輸送で変わらない。 -/
theorem projector_action_eq_zero_iff (mu a : (ZMod 37)ˣ) (x : Space K) :
    projector mu (action a x) = 0 ↔ projector mu x = 0 := by
  rw [projector_action, smul_eq_zero_iff_right (Units.ne_zero (character mu a))]

/-- 非零射影の指標を有限集合として記録する。成分の非零次元とは別の、元ごとの支持。 -/
noncomputable def characterSupport (x : Space K) : Finset (ZMod 37)ˣ := by
  classical
  exact Finset.univ.filter (fun mu => projector mu x ≠ 0)

/-- 支持の所属は、その元の射影が非零であることを意味する。 -/
theorem mem_characterSupport (mu : (ZMod 37)ˣ) (x : Space K) :
    mu ∈ characterSupport x ↔ projector mu x ≠ 0 := by
  classical
  simp [characterSupport]

/-- 元ごとの指標支持はガロア軌道上で一定となる。 -/
theorem characterSupport_action (a : (ZMod 37)ˣ) (x : Space K) :
    characterSupport (action a x) = characterSupport x := by
  ext mu
  simp only [mem_characterSupport, ne_eq, projector_action_eq_zero_iff]

/-- B₃₂に対応する冪指標の固有値ラベル。生成元を選び直しても冪指標自体は同じ。 -/
noncomputable def bernoulli32Label : (ZMod 37)ˣ := generator ^ 5

/-- 37−32=5という添字の変換を明示し、指標をa↦a⁵と同定する。 -/
theorem bernoulli32_character : character bernoulli32Label = powMonoidHom 5 :=
  character_generator_pow 5

/-- 指標5は自明ではない。具体的な単元2での値から確認する。 -/
theorem bernoulli32_character_ne_one : character bernoulli32Label ≠ 1 := by
  rw [bernoulli32_character]
  intro h
  have he := congrArg (fun χ : (ZMod 37)ˣ →* (ZMod 37)ˣ => χ (Units.mk0 2 (by decide))) h
  have hv := congrArg (fun a : (ZMod 37)ˣ => (a : ZMod 37)) he
  exact (by decide : (32 : ZMod 37) ≠ 1) hv

/-- 対象ラベルは自明指標のラベル1とは異なる。 -/
theorem bernoulli32Label_ne_one : bernoulli32Label ≠ 1 := by
  intro h
  exact bernoulli32_character_ne_one (h ▸ character_one)

/-- 古典的な添字1−32を位数36で読むと5となる。負の添字の規約も明示する。 -/
theorem bernoulli32_residual_exponent : (1 - (32 : ZMod 36)) = 5 := by decide

/-- Bernoulli証明書と指標同定を同じ契約で読む。非零類群の存在は結論に含めない。 -/
theorem bernoulli32_target_certificate :
    BernoulliPrime37.BernoulliIrregularPair 37 32 ∧
      37 - 32 = (5 : ℕ) ∧ character bernoulli32Label = powMonoidHom 5 :=
  ⟨(BernoulliPrime37.irregular_pair_thirtySeven_iff 32).mpr rfl, rfl, bernoulli32_character⟩

end DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition
