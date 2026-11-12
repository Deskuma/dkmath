/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.CyclotomicClassNorm
import DkMath.Lib.LinearAlgebra.FiniteSpectrumProjectors
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Finite.Basic

#print "file: DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition"

/-!
# IRR-009: 真の37-torsion 類群の指標射影と直和分解

類群の37乗写像の核を加法的に読み、F₃₇ 線形空間にする。円分体の真のガロア作用は
この空間の線形作用となる。F₃₇ˣ の生成元 g を選ぶと T=σ_g は T³⁶=1 を満たす。
X³⁶−1 の相異なる36根での Lagrange 補間から、射影と直和分解を構成する。
各固有成分を既存の `characterComponent` と同定するため、単なる代替空間ではない。
自明成分は算術的な全共役ノルムで消える。非零類の存在・非零成分の次元・
Bernoulli 非正則対との対応、37²以上の torsion の分解は別途必要である。
-/
namespace DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition
open scoped NumberField DirectSum
open Module Polynomial
open CyclotomicPhaseGalois
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

variable {K : Type*} [Field K] [NumberField K]

/-- 実際の類群の37乗写像の核。元を新しい形式記号へ置き換えない。 -/
noncomputable def torsionGroup (K : Type*) [Field K] [NumberField K] : Subgroup (ClassGroup (𝓞 K)) :=
  (powMonoidHom 37).ker

/-- 同じ37-torsion群を、線形代数用の加法記法で読む。 -/
abbrev Space (K : Type*) [Field K] [NumberField K] := Additive (torsionGroup K)

/-- 加法記法から元の実際のイデアル類へ戻す。 -/
def underlying (x : Space K) : ClassGroup (𝓞 K) := x.toMul.val

/-- 記法の変更は単射であり、元の類を区別できる。 -/
theorem underlying_injective : Function.Injective (underlying (K := K)) := by
  intro x y h
  apply Additive.toMul.injective
  exact Subtype.ext h

/-- 零ベクトルは主イデアル類である。 -/
theorem underlying_zero : underlying (0 : Space K) = 1 := rfl

/-- 記録した元は37で消える。 -/
theorem underlying_torsion (x : Space K) : underlying x ^ 37 = 1 := x.toMul.property

/-- 指数37の群に対する標準の F₃₇-module 構造。剰余スカラーは反復加法で作用する。 -/
noncomputable instance spaceModule : Module (ZMod 37) (Space K) :=
  AddCommGroup.zmodModule (n := 37) (by
    intro x
    apply underlying_injective
    exact underlying_torsion x)

/-- スカラー作用を元の類群へ戻すと、標準代表による冪になる。 -/
theorem underlying_smul (c : ZMod 37) (x : Space K) :
    underlying (c • x) = underlying x ^ c.val := rfl

variable [IsCyclotomicExtension {37} ℚ K]

/-- 真のガロア作用を37-torsion部分群へ制限する。 -/
noncomputable def actionMul (a : (ZMod 37)ˣ) : torsionGroup K →* torsionGroup K where
  toFun x := ⟨ClassGroup.mulEquiv (sigma (K := K) a) (x : ClassGroup (𝓞 K)), by
    change ClassGroup.mulEquiv (sigma (K := K) a) (x : ClassGroup (𝓞 K)) ^ 37 = 1
    rw [← map_pow]
    exact congrArg (ClassGroup.mulEquiv (sigma a)) x.property |>.trans (map_one _)⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul (ClassGroup.mulEquiv (sigma (K := K) a)) (x : ClassGroup (𝓞 K)) (y : ClassGroup (𝓞 K)))

/-- 指数37の加法群の準同型は F₃₇ 線形となる。 -/
noncomputable def linearAction (a : (ZMod 37)ˣ) : End (ZMod 37) (Space K) :=
  ((actionMul (K := K) a).toAdditive).toZModLinearMap 37

/-- 線形作用を類群へ戻すと、既存の実際のガロア作用と一致する。 -/
theorem underlying_action (a : (ZMod 37)ˣ) (x : Space K) :
    underlying (linearAction a x) = ClassGroup.mulEquiv (sigma a) (underlying x) := rfl

/-- 作用の合成則も既存の `sigma_mul` と類群同型の合成から従う。 -/
noncomputable def action : (ZMod 37)ˣ →* End (ZMod 37) (Space K) where
  toFun := linearAction
  map_one' := by
    apply LinearMap.ext
    intro x
    apply underlying_injective
    change ClassGroup.mulEquiv (sigma (1 : (ZMod 37)ˣ)) (underlying x) = underlying x
    rw [sigma_one, classGroup_map_refl]
  map_mul' a b := by
    apply LinearMap.ext
    intro x
    apply underlying_injective
    change ClassGroup.mulEquiv (sigma (a * b)) (underlying x) =
      ClassGroup.mulEquiv (sigma a) (ClassGroup.mulEquiv (sigma b) (underlying x))
    rw [sigma_mul, classGroup_map_trans]

/-- 有限体の単元群の生成元。非計算的な選択を公開し、特定の数2を仮定しない。 -/
noncomputable def generator : (ZMod 37)ˣ := IsCyclic.exists_monoid_generator.choose

/-- 全てのガロア位相は同じ生成元の自然数冪で表せる。 -/
theorem exists_generator_pow (a : (ZMod 37)ˣ) : ∃ n : ℕ, generator ^ n = a :=
  (Submonoid.mem_powers_iff a generator).mp (IsCyclic.exists_monoid_generator.choose_spec a)

/-- 固有値muの離散指数。存在する有限指数を選ぶだけで、類群の次元計算は行わない。 -/
noncomputable def exponent (mu : (ZMod 37)ˣ) : ℕ := (exists_generator_pow mu).choose

/-- 各固有値をラベルとする真の乗法指標。 -/
noncomputable def character (mu : (ZMod 37)ˣ) : (ZMod 37)ˣ →* (ZMod 37)ˣ :=
  powMonoidHom (exponent mu)

/-- 指標は選んだ生成元で指定された固有値を取る。 -/
theorem character_generator (mu : (ZMod 37)ˣ) : character mu generator = mu :=
  (exists_generator_pow mu).choose_spec

/-- 異なる固有値は異なる指標を表す。 -/
theorem character_injective : Function.Injective character := by
  intro mu μ h
  have he := congrArg (fun χ : (ZMod 37)ˣ →* (ZMod 37)ˣ => χ generator) h
  simpa only [character_generator] using he

/-- 生成元による一つの線形作用素。 -/
noncomputable def operator : End (ZMod 37) (Space K) := action generator

/-- ガロア単元群の位数36による消失式。 -/
theorem operator_pow : (operator (K := K)) ^ 36 = 1 := by
  have hg : generator ^ 36 = 1 := by
    simpa only [ZMod.card_units_eq_totient, Nat.totient_prime (by decide : Nat.Prime 37)] using
      (pow_card_eq_one : generator ^ Fintype.card (ZMod 37)ˣ = 1)
  rw [operator, ← map_pow, hg, map_one]

/-- 単元群の36個の相異なる根の消失多項式は X³⁶−1。 -/
theorem nodal_eq : Lagrange.nodal Finset.univ ((↑) : (ZMod 37)ˣ → ZMod 37) = X ^ 36 - 1 := by
  classical
  let : Fintype (⊤ : Subgroup (ZMod 37)ˣ) := Fintype.ofFinite _
  have hc : Fintype.card (⊤ : Subgroup (ZMod 37)ˣ) = 36 := by
    rw [Fintype.card_congr (Subgroup.topEquiv.toEquiv)]
    norm_num [ZMod.card_units_eq_totient, Nat.totient_prime (by decide : Nat.Prime 37)]
  simpa only [Subgroup.coe_top, Set.toFinset_univ, hc] using Lagrange.nodal_subgroup_eq_X_pow_card_sub_one (⊤ : Subgroup (ZMod 37)ˣ)

/-- 補間射影の一般定理に渡す、作用素の消失多項式。 -/
theorem aeval_nodal : aeval (operator (K := K))
    (Lagrange.nodal Finset.univ ((↑) : (ZMod 37)ˣ → ZMod 37)) = 0 := by
  rw [nodal_eq, map_sub, map_pow, aeval_X, map_one, operator_pow, sub_self]

/-- 指標ラベルmuに対応する実際の固有空間。 -/
noncomputable def component (mu : (ZMod 37)ˣ) : Submodule (ZMod 37) (Space K) :=
  (operator (K := K)).eigenspace (mu : ZMod 37)

/-- 実際の37-torsion類に対する有限指標射影。 -/
noncomputable def projector (mu : (ZMod 37)ˣ) : End (ZMod 37) (Space K) :=
  DkMath.Lib.LinearAlgebra.FiniteSpectrumProjectors.projector Units.val operator mu

/-- 実際の類群上でも各指標射影は冪等である。 -/
theorem projector_idempotent (a : (ZMod 37)ˣ) :
    projector (K := K) a * projector a = projector a :=
  DkMath.Lib.LinearAlgebra.FiniteSpectrumProjectors.projector_idempotent Units.val operator
    Units.val_injective aeval_nodal a

/-- 異なる指標成分の射影は互いを消す。 -/
theorem projector_orthogonal {a b : (ZMod 37)ˣ} (hab : a ≠ b) :
    projector (K := K) a * projector b = 0 :=
  DkMath.Lib.LinearAlgebra.FiniteSpectrumProjectors.projector_orthogonal Units.val operator
    Units.val_injective aeval_nodal hab

/-- 成分の線形代数的定義と、既存の類群上の指標条件は同値である。 -/
theorem mem_component_iff (mu : (ZMod 37)ˣ) (x : Space K) :
    x ∈ component mu ↔ underlying x ∈ characterComponent (character mu) := by
  constructor
  · intro hx
    have he : operator x = (mu : ZMod 37) • x := Module.End.mem_eigenspace_iff.mp hx
    refine ⟨underlying_torsion x, ?_⟩
    intro a
    obtain ⟨t, ht⟩ := exists_generator_pow a
    have hpow : (operator (K := K) ^ t) x = (mu : ZMod 37) ^ t • x := by
      simpa only [map_pow, aeval_X, eval_pow, eval_X] using
        Module.End.aeval_apply_of_mem_apply_eq_smul (p := X ^ t) he
    have hχ : character mu a = mu ^ t := by rw [← ht, map_pow, character_generator]
    calc
      ClassGroup.mulEquiv (sigma a) (underlying x) = underlying (action a x) := rfl
      _ = underlying ((operator ^ t) x) := by rw [← ht, map_pow]; rfl
      _ = underlying ((mu : ZMod 37) ^ t • x) := congrArg underlying hpow
      _ = underlying x ^ (character mu a).val.val := by rw [underlying_smul, hχ]; simp
  · intro hx
    apply Module.End.mem_eigenspace_iff.mpr
    apply underlying_injective
    change underlying (linearAction generator x) = underlying ((mu : ZMod 37) • x)
    rw [underlying_action, underlying_smul, hx.2 generator, character_generator]

/-- 有限36成分の直和と実際の37-torsion類群の線形同型。 -/
noncomputable def decomposition : Space K ≃ₗ[ZMod 37] ⨁ mu : (ZMod 37)ˣ, component (K := K) mu :=
  DkMath.Lib.LinearAlgebra.FiniteSpectrumProjectors.directSumEquiv Units.val operator
    Units.val_injective aeval_nodal

/-- 射影の和による復元。存在する類の情報を捨てずに往復する。 -/
theorem sum_projector (x : Space K) : ∑ mu : (ZMod 37)ˣ, projector mu x = x :=
  DkMath.Lib.LinearAlgebra.FiniteSpectrumProjectors.sum_projector_apply Units.val operator
    Units.val_injective x

/-- 自明指標のラベルはmu=1。生成元だけでなく、全ての群の元で1となる。 -/
theorem character_one : character 1 = 1 := by
  ext a
  obtain ⟨t, ht⟩ := exists_generator_pow a
  rw [← ht, map_pow, character_generator]
  simp

/-- 算術的ノルム消滅を使い、自明指標成分を除去する。 -/
theorem component_one : component (K := K) 1 = ⊥ := by
  ext x
  rw [mem_component_iff, character_one, trivial_characterComponent, Subgroup.mem_bot, Submodule.mem_bot]
  exact ⟨fun h => underlying_injective (h.trans underlying_zero.symm), fun h => h ▸ underlying_zero⟩

/-- 自明指標への射影は零作用素。 -/
theorem projector_one : projector (K := K) 1 = 0 := by
  apply LinearMap.ext
  intro x
  have he := DkMath.Lib.LinearAlgebra.FiniteSpectrumProjectors.projector_eigen
    Units.val (operator (K := K)) aeval_nodal (1 : (ZMod 37)ˣ) x
  have hm : projector 1 x ∈ component (K := K) 1 := Module.End.mem_eigenspace_iff.mpr he
  rwa [component_one, Submodule.mem_bot] at hm

/-- 非零類があれば、少なくとも一つの非自明指標で射影が非零になる。
その入力となる非零類の存在や、どのラベルで非零かを外部から捏造しない。 -/
theorem exists_nontrivial_component {x : Space K} (hx : x ≠ 0) :
    ∃ mu : (ZMod 37)ˣ, mu ≠ 1 ∧ projector mu x ≠ 0 := by
  obtain ⟨mu, hmu⟩ := DkMath.Lib.LinearAlgebra.FiniteSpectrumProjectors.exists_nonzero_projector
    Units.val operator Units.val_injective hx
  refine ⟨mu, ?_, hmu⟩
  intro he
  subst mu
  exact hmu (LinearMap.congr_fun projector_one x)

end DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition
