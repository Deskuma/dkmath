/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Algebra.TorsionMultiplication
import Mathlib.Algebra.Module.ZMod
import Mathlib.RepresentationTheory.Basic

#print "file: DkMath.Lib.Algebra.TorsionPreimageQuotient"

/-!
# 捩れ塔の一段を作る実際の商 `n⁻¹K / K`

`P = {y ∈ G | n • y ∈ K}` を実際の点の部分群として構成する。
包含 `K ⊆ P` と倍写像 `P → K` は異なる写像である。前者で商 `V=P/K` を作り、
後者の核を `G[n]` と同定する。`n` 倍写像が全射なら

`#P = #K * #G[n]`,  `#V = #G[n]`

となる。後の等式には `K` の有限性が必要であり、無限群の `Nat.card=0` を
約分しない。`V` は `n` 倍で消えるので、標準の `ZMod n` 加群になる。

さらに `K` を保存する実際の作用を `P`、`V` へ降ろす。
これは捩れ塔の存在を仮定する provider ではなく、与えられた同じ `K` からの
具体的な群・商・写像・表現の構成である。
-/

namespace DkMath.Lib.Algebra.TorsionPreimageQuotient

variable {G : Type*} [AddCommGroup G] (n : ℕ) (K : AddSubgroup G)

/-- 同じ群の倍写像による逆像。 -/
def preimage : AddSubgroup G := K.comap (nsmulAddMonoidHom n)

/-- 倍写像の逆像への所属。 -/
theorem mem_preimage_iff {y : G} : y ∈ preimage n K ↔ n • y ∈ K := Iff.rfl

/-- `K` の包含は、部分群の自然数倍での閉性から従う。 -/
theorem le_preimage : K ≤ preimage n K := fun _ hx => K.nsmul_mem hx n

/-- 逆像上の倍写像は、同じ `K` に値を取る。 -/
def multiply : preimage n K →+ K where
  toFun y := ⟨n • y.val, y.property⟩
  map_zero' := Subtype.ext (nsmul_zero n)
  map_add' x y := Subtype.ext (map_add (nsmulAddMonoidHom n : G →+ G) x.val y.val)

/-- 逆像上の倍写像の核は、周囲の群の実際の `n` 捩れである。 -/
def multiplyKernelEquiv : TorsionMultiplication.Kernel G n ≃+ (multiply n K).ker where
  toFun x := ⟨⟨x.val, by
    change n • x.val ∈ K
    have hx : n • x.val = 0 := x.property
    rw [hx]
    exact K.zero_mem⟩,
    Subtype.ext x.property⟩
  invFun x := ⟨x.val.val, congrArg (fun z : K => z.val) x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- 周囲の `n` 倍写像の全射性は、同じ `P → K` の全射性を供給する。 -/
theorem multiply_surjective
    (hlift : Function.Surjective (nsmulAddMonoidHom n : G →+ G)) :
    Function.Surjective (multiply n K) := by
  intro x
  obtain ⟨y, hy⟩ := hlift x.val
  exact ⟨⟨y, by change n • y ∈ K; rw [show n • y = x.val from hy]; exact x.property⟩,
    Subtype.ext hy⟩

/-- 倍写像の短完全列からの濃度公式。この段階では有限性を仮定しない。 -/
theorem card_preimage
    (hlift : Function.Surjective (nsmulAddMonoidHom n : G →+ G)) :
    Nat.card (preimage n K) = Nat.card K * Nat.card (TorsionMultiplication.Kernel G n) := by
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (multiply n K).ker,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective (multiply n K)
      (multiply_surjective n K hlift)).toEquiv,
    ← Nat.card_congr (multiplyKernelEquiv n K).toEquiv]

/-- 包含された同じ `K` で割った商。 -/
abbrev Quotient := preimage n K ⧸ K.addSubgroupOf (preimage n K)

/-- 商への標準射影。 -/
def quotientMap : preimage n K →+ Quotient n K :=
  QuotientAddGroup.mk' (K.addSubgroupOf (preimage n K))

/-- 商で零になるのは、元の点が `K` に入る場合に限る。 -/
theorem quotientMap_eq_zero_iff (y : preimage n K) :
    quotientMap n K y = 0 ↔ y.val ∈ K := by
  rw [quotientMap, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  rfl

/-- `V` の各類は `n` 倍で零となる。 -/
theorem nsmul_quotient_eq_zero (v : Quotient n K) : n • v = 0 := by
  induction v using QuotientAddGroup.induction_on with
  | H y =>
    change quotientMap n K (n • y) = 0
    apply (quotientMap_eq_zero_iff n K _).mpr
    exact y.property

/-- `n` 倍で消える商の標準 `ZMod n` 加群構造。 -/
instance quotientModule : Module (ZMod n) (Quotient n K) :=
  AddCommGroup.zmodModule (nsmul_quotient_eq_zero n K)

/-- 有限の `K` の濃度だけを約分し、商の濃度を得る。
`G` 全体や `G[n]` の有限性をこの公式に追加要求しない。 -/
theorem card_quotient [Finite K]
    (hlift : Function.Surjective (nsmulAddMonoidHom n : G →+ G)) :
    Nat.card (Quotient n K) = Nat.card (TorsionMultiplication.Kernel G n) := by
  have h := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
    (K.addSubgroupOf (preimage n K))
  rw [card_preimage n K hlift,
    Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe (le_preimage n K)).toEquiv] at h
  exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos : 0 < Nat.card K)
    (h.symm.trans (Nat.mul_comm _ _))

/-- 周囲の `n` 捩れを、同じ逆像群へ含める。 -/
def torsionInclusion : TorsionMultiplication.Kernel G n →+ preimage n K where
  toFun e := ⟨e.val, by
    change n • e.val ∈ K
    have he : n • e.val = 0 := e.property
    rw [he]
    exact K.zero_mem⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- `G[n]` の同じ商への像写像。 -/
def torsionMap : TorsionMultiplication.Kernel G n →+ Quotient n K :=
  (quotientMap n K).comp (torsionInclusion n K)

/-- 次の extension の固定側となる、実際の `G[n]` の像部分加群。 -/
def torsionImage : Submodule (ZMod n) (Quotient n K) :=
  AddSubgroup.toZModSubmodule n (torsionMap n K).range

/-- 固定側への所属は、元の捩れ点による代表の存在である。 -/
theorem mem_torsionImage_iff (v : Quotient n K) :
    v ∈ torsionImage n K ↔ ∃ e : TorsionMultiplication.Kernel G n, torsionMap n K e = v :=
  Iff.rfl

/-- 捩れ点の像が零となる条件。 -/
theorem torsionMap_eq_zero_iff (e : TorsionMultiplication.Kernel G n) :
    torsionMap n K e = 0 ↔ e.val ∈ K := quotientMap_eq_zero_iff n K _

/-- 像写像の核は `K` 自身の `n` 捩れと同型である。 -/
def torsionMapKernelEquiv : (torsionMap n K).ker ≃+ TorsionMultiplication.Kernel K n where
  toFun x := ⟨⟨x.val.val, (torsionMap_eq_zero_iff n K x.val).mp x.property⟩,
    Subtype.ext x.val.property⟩
  invFun x := ⟨⟨x.val.val, congrArg (fun z : K => z.val) x.property⟩,
    (torsionMap_eq_zero_iff n K _).mpr x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- 捩れ像の濃度公式。後で `K` の巡回性から核の濃度を具体化できる。 -/
theorem card_torsionImage_mul_card_kernel :
    Nat.card (torsionImage n K) * Nat.card (TorsionMultiplication.Kernel K n) =
      Nat.card (TorsionMultiplication.Kernel G n) := by
  have h := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (torsionMap n K).ker
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange (torsionMap n K)).toEquiv,
    Nat.card_congr (torsionMapKernelEquiv n K).toEquiv] at h
  exact h.symm

/-- `K` 自身が `n` 倍で消える場合、倍写像は商 `V` から同じ `K` へ降りる。
これは捩れ塔の最初の一段で用いる。 -/
def quotientMultiply (hKkill : ∀ x ∈ K, n • x = 0) : Quotient n K →+ K :=
  QuotientAddGroup.lift _ (multiply n K) (fun _ hx => Subtype.ext (hKkill _ hx))

/-- 商上の倍写像は同じ代表点の `n` 倍を返す。 -/
theorem quotientMultiply_quotientMap (hKkill : ∀ x ∈ K, n • x = 0)
    (y : preimage n K) : quotientMultiply n K hKkill (quotientMap n K y) = multiply n K y := rfl

/-- 倍写像の核は、構成済みの同じ捩れ像 `C` に等しい。 -/
theorem mem_torsionImage_iff_quotientMultiply_eq_zero
    (hKkill : ∀ x ∈ K, n • x = 0) (v : Quotient n K) :
    v ∈ torsionImage n K ↔ quotientMultiply n K hKkill v = 0 := by
  induction v using QuotientAddGroup.induction_on with
  | H y =>
    rw [mem_torsionImage_iff]
    constructor
    · rintro ⟨e, he⟩
      rw [← he]
      apply Subtype.ext
      exact e.property
    · intro hz
      have he : n • y.val = 0 := congrArg (fun z : K => z.val) hz
      exact ⟨⟨y.val, he⟩, rfl⟩

/-- 周囲の倍写像が全射なら、`V → K` も全射となる。 -/
theorem quotientMultiply_surjective (hKkill : ∀ x ∈ K, n • x = 0)
    (hlift : Function.Surjective (nsmulAddMonoidHom n : G →+ G)) :
    Function.Surjective (quotientMultiply n K hKkill) := by
  intro x
  obtain ⟨y, hy⟩ := multiply_surjective n K hlift x
  exact ⟨quotientMap n K y, hy⟩

/-- 同じ部分群を保存する準同型は倍写像の逆像も保存する。 -/
def mapPreimage (f : G →+ G) (hf : ∀ x ∈ K, f x ∈ K) : preimage n K →+ preimage n K where
  toFun y := ⟨f y.val, by change n • f y.val ∈ K; rw [← map_nsmul]; exact hf _ y.property⟩
  map_zero' := Subtype.ext (map_zero f)
  map_add' x y := Subtype.ext (map_add f x.val y.val)

/-- 作用の商への降下。 -/
def mapQuotient (f : G →+ G) (hf : ∀ x ∈ K, f x ∈ K) : Quotient n K →+ Quotient n K :=
  QuotientAddGroup.map _ _ (mapPreimage n K f hf) (fun _ hx => hf _ hx)

/-- 商作用は同じ代表点への写像を使う。 -/
theorem mapQuotient_quotientMap (f : G →+ G) (hf : ∀ x ∈ K, f x ∈ K)
    (y : preimage n K) :
    mapQuotient n K f hf (quotientMap n K y) =
      quotientMap n K (mapPreimage n K f hf y) := rfl

/-- 任意の実際の加法的作用から、捩れ商の基底によらない表現を構成する。 -/
def representation {Γ : Type*} [Monoid Γ] (ρ : Γ →* AddMonoid.End G)
    (hstable : ∀ g : Γ, ∀ x ∈ K, ρ g x ∈ K) :
    Representation (ZMod n) Γ (Quotient n K) where
  toFun g := (mapQuotient n K (ρ g) (hstable g)).toZModLinearMap n
  map_one' := by
    apply LinearMap.ext
    intro v
    induction v using QuotientAddGroup.induction_on with
    | H y =>
      change quotientMap n K (mapPreimage n K (ρ 1) (hstable 1) y) = quotientMap n K y
      apply congrArg (quotientMap n K)
      apply Subtype.ext
      exact congrArg (fun f : AddMonoid.End G => f y.val) ρ.map_one
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    induction v using QuotientAddGroup.induction_on with
    | H y =>
      change quotientMap n K (mapPreimage n K (ρ (g * h)) (hstable (g * h)) y) =
        quotientMap n K (mapPreimage n K (ρ g) (hstable g)
          (mapPreimage n K (ρ h) (hstable h) y))
      apply congrArg (quotientMap n K)
      apply Subtype.ext
      exact congrArg (fun f : AddMonoid.End G => f y.val) (ρ.map_mul g h)

/-- 表現は実際の代表点に作用してから同じ商を取る。 -/
theorem representation_quotientMap {Γ : Type*} [Monoid Γ] (ρ : Γ →* AddMonoid.End G)
    (hstable : ∀ g : Γ, ∀ x ∈ K, ρ g x ∈ K) (g : Γ) (y : preimage n K) :
    representation n K ρ hstable g (quotientMap n K y) =
      quotientMap n K (mapPreimage n K (ρ g) (hstable g) y) := rfl

/-- 元の `n` 捩れの作用差が `K` に吸収されれば、商の捩れ像は点ごとに固定される。
固定側の存在を仮定せず、構成済みの同じ像部分加群について証明する。 -/
theorem representation_fixed_on_torsionImage {Γ : Type*} [Monoid Γ]
    (ρ : Γ →* AddMonoid.End G) (hstable : ∀ g : Γ, ∀ x ∈ K, ρ g x ∈ K)
    (hcofixed : ∀ g : Γ, ∀ e : G, n • e = 0 → ρ g e - e ∈ K)
    (g : Γ) (v : Quotient n K) (hv : v ∈ torsionImage n K) :
    representation n K ρ hstable g v = v := by
  obtain ⟨e, rfl⟩ := (mem_torsionImage_iff n K v).mp hv
  change quotientMap n K (mapPreimage n K (ρ g) (hstable g) (torsionInclusion n K e)) =
    quotientMap n K (torsionInclusion n K e)
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact (quotientMap_eq_zero_iff n K _).mpr (hcofixed g e.val e.property)

/-- `nK=0` のとき、`K` 上の scalar 作用は商 `V/C` 上の同じ scalar 作用を与える。
商上の指標を仮定せず、倍写像の核の同定から導く。 -/
theorem representation_sub_nsmul_mem_torsionImage {Γ : Type*} [Monoid Γ]
    (ρ : Γ →* AddMonoid.End G) (hstable : ∀ g : Γ, ∀ x ∈ K, ρ g x ∈ K)
    (hKkill : ∀ x ∈ K, n • x = 0) (χ : Γ → ℕ)
    (hχ : ∀ g : Γ, ∀ x ∈ K, ρ g x = χ g • x)
    (g : Γ) (v : Quotient n K) :
    representation n K ρ hstable g v - χ g • v ∈ torsionImage n K := by
  apply (mem_torsionImage_iff_quotientMultiply_eq_zero n K hKkill _).mpr
  induction v using QuotientAddGroup.induction_on with
  | H y =>
    change quotientMultiply n K hKkill
      (quotientMap n K (mapPreimage n K (ρ g) (hstable g) y) -
        χ g • quotientMap n K y) = 0
    rw [map_sub, map_nsmul]
    apply Subtype.ext
    change n • ρ g y.val - χ g • (n • y.val) = 0
    rw [← map_nsmul, hχ g (n • y.val) y.property, sub_self]

/-- 商の部分加群の逆像を、元の同じ群の部分群へ戻す。 -/
def liftSubmodule (C' : Submodule (ZMod n) (Quotient n K)) : AddSubgroup G :=
  (C'.toAddSubgroup.comap (quotientMap n K)).map (preimage n K).subtype

/-- 持ち上げた部分群への所属を、同じ点の商の所属で判定する。 -/
theorem mem_liftSubmodule_iff (C' : Submodule (ZMod n) (Quotient n K)) (y : G) :
    y ∈ liftSubmodule n K C' ↔ ∃ hy : n • y ∈ K, quotientMap n K ⟨y, hy⟩ ∈ C' := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.property, hx⟩
  · rintro ⟨hy, hx⟩
    exact ⟨⟨y, hy⟩, hx, rfl⟩

/-- 元の `K` は、どの部分加群の持ち上げにも含まれる。 -/
theorem le_liftSubmodule (C' : Submodule (ZMod n) (Quotient n K)) : K ≤ liftSubmodule n K C' := by
  intro y hy
  apply (mem_liftSubmodule_iff n K C' y).mpr
  refine ⟨K.nsmul_mem hy n, ?_⟩
  rw [(quotientMap_eq_zero_iff n K _).mpr hy]
  exact C'.zero_mem

/-- 持ち上げた群を商の部分加群へ送る全射。 -/
def liftProjection (C' : Submodule (ZMod n) (Quotient n K)) :
    C'.toAddSubgroup.comap (quotientMap n K) →+ C' where
  toFun x := ⟨quotientMap n K x.val, x.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x.val y.val)

/-- 標準商射影の全射性から、制限した射影も全射になる。 -/
theorem liftProjection_surjective (C' : Submodule (ZMod n) (Quotient n K)) :
    Function.Surjective (liftProjection n K C') := by
  intro v
  obtain ⟨y, hy⟩ := QuotientAddGroup.mk'_surjective (K.addSubgroupOf (preimage n K)) v.val
  exact ⟨⟨y, by change quotientMap n K y ∈ C'; rw [show quotientMap n K y = v.val from hy]; exact v.property⟩,
    Subtype.ext hy⟩

/-- 持ち上げの射影の核は、元の同じ `K` である。 -/
def liftProjectionKernelEquiv (C' : Submodule (ZMod n) (Quotient n K)) :
    K ≃+ (liftProjection n K C').ker where
  toFun x := ⟨⟨⟨x.val, K.nsmul_mem x.property n⟩, by
      change quotientMap n K ⟨x.val, _⟩ ∈ C'
      rw [(quotientMap_eq_zero_iff n K _).mpr x.property]
      exact C'.zero_mem⟩,
    Subtype.ext ((quotientMap_eq_zero_iff n K _).mpr x.property)⟩
  invFun x := ⟨x.val.val.val, (quotientMap_eq_zero_iff n K _).mp
    (congrArg (fun z : C' => z.val) x.property)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- 同じ持ち上げた部分群の濃度公式。有限性を仮定せず一般の `Nat.card` で成立する。 -/
theorem card_liftSubmodule (C' : Submodule (ZMod n) (Quotient n K)) :
    Nat.card (liftSubmodule n K C') = Nat.card C' * Nat.card K := by
  unfold liftSubmodule
  rw [← Nat.card_congr ((C'.toAddSubgroup.comap (quotientMap n K)).equivMapOfInjective
    (preimage n K).subtype Subtype.val_injective).toEquiv]
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (liftProjection n K C').ker,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective (liftProjection n K C')
      (liftProjection_surjective n K C')).toEquiv,
    ← Nat.card_congr (liftProjectionKernelEquiv n K C').toEquiv]

/-- 元の捩れ像と交わらない部分加群の持ち上げでは、`n` 捩れが必ず `K` へ戻る。 -/
theorem torsion_mem_of_lift_disjoint (C' : Submodule (ZMod n) (Quotient n K))
    (hdisj : Disjoint (torsionImage n K) C') {y : G}
    (hy : y ∈ liftSubmodule n K C') (hkill : n • y = 0) : y ∈ K := by
  obtain ⟨hyp, hC'⟩ := (mem_liftSubmodule_iff n K C' y).mp hy
  have hC : quotientMap n K ⟨y, hyp⟩ ∈ torsionImage n K :=
    (mem_torsionImage_iff n K _).mpr ⟨⟨y, hkill⟩, rfl⟩
  have hz : quotientMap n K ⟨y, hyp⟩ = 0 := (Submodule.disjoint_def.mp hdisj) _ hC hC'
  exact (quotientMap_eq_zero_iff n K _).mp hz

/-- 安定な商部分加群の持ち上げは、元の同じ作用でも安定である。 -/
theorem liftSubmodule_stable {Γ : Type*} [Monoid Γ]
    (ρ : Γ →* AddMonoid.End G) (hstable : ∀ g : Γ, ∀ x ∈ K, ρ g x ∈ K)
    (C' : Submodule (ZMod n) (Quotient n K))
    (hC' : ∀ g : Γ, ∀ v ∈ C', representation n K ρ hstable g v ∈ C')
    (g : Γ) {y : G} (hy : y ∈ liftSubmodule n K C') : ρ g y ∈ liftSubmodule n K C' := by
  obtain ⟨hyp, hv⟩ := (mem_liftSubmodule_iff n K C' y).mp hy
  have h := hC' g _ hv
  apply (mem_liftSubmodule_iff n K C' _).mpr
  exact ⟨(mapPreimage n K (ρ g) (hstable g) ⟨y, hyp⟩).property, h⟩

end DkMath.Lib.Algebra.TorsionPreimageQuotient
