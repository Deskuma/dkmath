/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.CyclotomicRootModule
import DkMath.Lib.RepresentationTheory.AlternatingDeterminant

#print "file: DkMath.Lib.NumberTheory.RootPairingDeterminant"

/-!
# 乗法的な交代対から円分行列式へ

双加法性から対の値はn乗根になる。これをAdditive μₙへの双線形写像へ翻訳する。
素数pでは係数環が体となり、非退化性による基底対の非零性を使って行列式を決定できる。
根の作用は既に定義した円分指標のスカラー倍なので、対のガロア同変性を入力すれば
行列式指標との一致が従う。対の存在を仮定に隠して無条件の円分行列式とは呼ばない。
-/
namespace DkMath.Lib.NumberTheory
open Module CyclotomicRootModule DkMath.Lib.RepresentationTheory

/-- 乗法値の非退化交代対の法則。存在定理ではなく、構成されるべき数学的データである。 -/
structure RootPairing (L : Type*) [Field L] (n : ℕ) (V : Type*) [AddCommGroup V]
    [Module (ZMod n) V] where
  value : V → V → Lˣ
  add_left : ∀ x x' y, value (x + x') y = value x y * value x' y
  add_right : ∀ x y y', value x (y + y') = value x y * value x y'
  alternating : ∀ x, value x x = 1
  nondegenerate : ∀ x, (∀ y, value x y = 1) → x = 0

namespace RootPairing
variable {L V : Type*} [Field L] {n : ℕ} [AddCommGroup V] [Module (ZMod n) V]
  (e : RootPairing L n V)

/-- 双加法性は零点での値が1となることを強制する。 -/
theorem zero_left (y : V) : e.value 0 y = 1 := by
  have h := e.add_left 0 0 y
  rw [add_zero] at h
  exact mul_eq_left.mp h.symm

/-- 第二変数が零のときの値も1である。 -/
theorem zero_right (x : V) : e.value x 0 = 1 := by
  have h := e.add_right x 0 0
  rw [add_zero] at h
  exact mul_eq_left.mp h.symm

/-- 整数倍への双加法性を帰納的に証明する。 -/
theorem nsmul_left (a : ℕ) (x y : V) : e.value (a • x) y = e.value x y ^ a := by
  induction a with
  | zero => rw [zero_nsmul, e.zero_left, pow_zero]
  | succ a ih => rw [succ_nsmul, e.add_left, ih, pow_succ]

/-- ZMod n上の点群であることから、全ての対の値はn乗根になる。 -/
theorem value_pow (x y : V) : e.value x y ^ n = 1 := by
  rw [← e.nsmul_left, ← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self,
    zero_smul, e.zero_left]

/-- 対の値を、乗法を加法とする根の加群へ入れる。 -/
def rootValue (x y : V) : RootSpace L n :=
  Additive.ofMul ⟨e.value x y, (mem_rootsOfUnity n _).mpr (e.value_pow x y)⟩

/-- 根の加法的零と、元の乗法的な値1との対応。 -/
theorem rootValue_eq_zero (x y : V) : e.rootValue x y = 0 ↔ e.value x y = 1 := by
  change (⟨e.value x y, _⟩ : rootsOfUnity n L) = 1 ↔ e.value x y = 1
  exact Subtype.ext_iff

/-- 第二変数に関する加法準同型。 -/
def rootAddHom (x : V) : V →+ RootSpace L n where
  toFun := e.rootValue x
  map_zero' := (e.rootValue_eq_zero x 0).mpr (e.zero_right x)
  map_add' y y' := by
    apply Additive.ext
    apply Subtype.ext
    exact e.add_right x y y'

/-- 双加法性をZMod n双線形性へ運ぶ。冪の剰余計算を各証明で繰り返さずに済む。 -/
noncomputable def rootForm : V →ₗ[ZMod n] V →ₗ[ZMod n] RootSpace L n :=
  (show V →+ (V →ₗ[ZMod n] RootSpace L n) from
    { toFun := fun x => (e.rootAddHom x).toZModLinearMap n
      map_zero' := by
        apply LinearMap.ext
        intro y
        exact (e.rootValue_eq_zero 0 y).mpr (e.zero_left y)
      map_add' := by
        intro x x'
        apply LinearMap.ext
        intro y
        apply Additive.ext
        apply Subtype.ext
        exact e.add_left x x' y }).toZModLinearMap n

/-- 翻訳した双線形対は交代的である。標数2でもこの法則を保持する。 -/
theorem rootForm_alternating (x : V) : e.rootForm x x = 0 :=
  (e.rootValue_eq_zero x x).mpr (e.alternating x)

/-- 翻訳によって非退化性も失われない。 -/
theorem rootForm_nondegenerate (x : V) (hx : ∀ y, e.rootForm x y = 0) : x = 0 :=
  e.nondegenerate x (fun y => (e.rootValue_eq_zero x y).mp (hx y))

variable {K : Type*} [Field K] [CharZero K] {p : ℕ} [Fact p.Prime]
  [Module (ZMod p) V]

/-- 同じ二次元表現に乗法的な非退化交代対を与え、そのガロア同変性を証明した場合の終点。
対の幾何学的構成は明示的な入力であり、この定理自体はその存在を供給しない。 -/
theorem determinant_eq_cyclotomic_of_pairing
    (ρ : Representation (ZMod p) (Field.absoluteGaloisGroup K) V)
    (b : Basis (Fin 2) (ZMod p) V) (w : RootPairing (AlgebraicClosure K) p V)
    (heq : ∀ σ x y, (w.value (ρ σ x) (ρ σ y) : AlgebraicClosure K) =
      σ.toAlgHom (w.value x y : AlgebraicClosure K)) :
    determinantCharacterWithBasis ρ b = cyclotomicCharacter p := by
  apply determinantCharacter_eq_of_equivariant_pairing ρ (cyclotomicCharacter p) b w.rootForm
    w.rootForm_alternating w.rootForm_nondegenerate
  intro σ x y
  change w.rootValue (ρ σ x) (ρ σ y) = (cyclotomicCharacter p σ : ZMod p) • w.rootValue x y
  apply Additive.ext
  rw [smul_toMul]
  apply Subtype.ext
  apply Units.ext
  exact (heq σ x y).trans (cyclotomicCharacter_spec p σ
    ⟨w.value x y, (mem_rootsOfUnity p _).mpr (w.value_pow x y)⟩)

end RootPairing
end DkMath.Lib.NumberTheory
