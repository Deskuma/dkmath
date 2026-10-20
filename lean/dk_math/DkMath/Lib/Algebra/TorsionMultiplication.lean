/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Algebra.Exact.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Coset.Card

#print "file: DkMath.Lib.Algebra.TorsionMultiplication"

/-!
# 倍写像の核を結ぶ短完全列

可換加法群Gのn倍写像の核をG[n]と書く。包含G[n]→G[mn]と、n倍写像
G[mn]→G[m]を実際の元を保持して構成する。後者の核はG[n]そのものである。
G上のn倍写像が全射なら制限も全射となるので、短完全列が得られる。
商と核の位数公式により |G[mn]|=|G[m]|·|G[n]| が従う。
写像・核の同定には有限性も互いに素性も不要である。Nat.cardは無限型では0となるため、
有限群の位数として利用する側では有限性を別途確認する。
-/
namespace DkMath.Lib.Algebra.TorsionMultiplication
variable (G : Type*) [AddCommGroup G] (m n : ℕ)

/-- n倍で零になる実際の元の部分群。 -/
def Kernel : AddSubgroup G := (nsmulAddMonoidHom n : G →+ G).ker

/-- G[n]からG[mn]への自然な包含。点の値は変更しない。 -/
def inclusion : Kernel G n →+ Kernel G (m * n) where
  toFun x := ⟨x.val, by
    change (m * n) • x.val = 0
    rw [mul_smul, (show n • x.val = 0 from x.property), smul_zero]⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- G[mn]からG[m]へのn倍写像。添字の順序をこの定義で固定する。 -/
def multiply : Kernel G (m * n) →+ Kernel G m where
  toFun x := ⟨n • x.val, by
    change m • (n • x.val) = 0
    rw [← mul_smul]
    exact x.property⟩
  map_zero' := Subtype.ext (nsmul_zero _)
  map_add' x y := Subtype.ext (map_add (nsmulAddMonoidHom n) x.val y.val)

/-- 包含は元を保持するため単射である。 -/
theorem inclusion_injective : Function.Injective (inclusion G m n) := by
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : Kernel G (m * n) => z.val) h

/-- 制限したn倍写像の核をG[n]と同定する加法同型。 -/
def kernelEquiv : Kernel G n ≃+ (multiply G m n).ker where
  toFun x := ⟨inclusion G m n x, by
    apply Subtype.ext
    change n • x.val = 0
    exact x.property⟩
  invFun x := ⟨x.val.val, by
    change n • x.val.val = 0
    exact congrArg (fun z : Kernel G m => z.val) x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- 像と核の一致をFunction.Exactとして公開する。右側の全射性とは独立の事実である。 -/
theorem exact_pair : Function.Exact (inclusion G m n) (multiply G m n) := by
  intro y
  constructor
  · intro h
    exact ⟨(kernelEquiv G m n).symm ⟨y, h⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    exact (kernelEquiv G m n x).property

/-- G上のn倍写像が全射なら、G[mn]→G[m]も全射となる。
原像Pは[mn]P=[m]Q=0を満たすので、同じ点を大きい核に入れられる。 -/
theorem multiply_surjective (hn : Function.Surjective (nsmulAddMonoidHom n : G →+ G)) :
    Function.Surjective (multiply G m n) := by
  intro y
  obtain ⟨x, hx⟩ := hn y.val
  have hx' : n • x = y.val := hx
  refine ⟨⟨x, ?_⟩, ?_⟩
  · change (m * n) • x = 0
    rw [mul_smul, hx']
    exact y.property
  · apply Subtype.ext
    exact hx'

/-- 単射・完全性・全射性の三条件を同じ写像のまままとめる短完全列。 -/
theorem short_exact (hn : Function.Surjective (nsmulAddMonoidHom n : G →+ G)) :
    Function.Injective (inclusion G m n) ∧
      Function.Exact (inclusion G m n) (multiply G m n) ∧
      Function.Surjective (multiply G m n) :=
  ⟨inclusion_injective G m n, exact_pair G m n, multiply_surjective G m n hn⟩

/-- 全射な制限写像の商はG[m]と同型になる。 -/
noncomputable def quotientEquiv (hn : Function.Surjective (nsmulAddMonoidHom n : G →+ G)) :
    Kernel G (m * n) ⧸ (multiply G m n).ker ≃+ Kernel G m :=
  QuotientAddGroup.quotientKerEquivOfSurjective (multiply G m n) (multiply_surjective G m n hn)

/-- 短完全列の濃度公式。互いに素性は不要で、Nat.cardの一般の商・核公式を使う。 -/
theorem card_mul (hn : Function.Surjective (nsmulAddMonoidHom n : G →+ G)) :
    Nat.card (Kernel G (m * n)) = Nat.card (Kernel G m) * Nat.card (Kernel G n) := by
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (multiply G m n).ker,
    Nat.card_congr (quotientEquiv G m n hn).toEquiv,
    ← Nat.card_congr (kernelEquiv G m n).toEquiv]

end DkMath.Lib.Algebra.TorsionMultiplication
