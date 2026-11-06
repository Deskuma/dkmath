# NOTE-032 教科書：合併の全 p 冪捩れと標準 Tate 加群の同定

日付：2026-11-06。前段：`TEXTBOOK-N032-FREY-TATE-LINE-261106.md`。

今回の2ステップは、①同じ合併 U の全 p^(n+1) 捩れを同じ有限段 Kₙ と同定すること、
②標準 Tate p U と既存の同じ階数1直線の自然な線形同型である。
元の非零生成元点列が全 Tate 加群の p 倍に入らないことも証明する。

以下の2つの Lean ブロックは production ファイルの全文である。
順にモジュールへ配置し、import 直後の正確な `#print "file: …"` を保持する。

## ステップ1：大きい巡回段の低位捩れを小さい段へ戻す

G を加法可換群、B≤K をその部分群とする。
K は有限巡回群で、|K|=pᵇ、|B|=pᵃ、a≤b、B は pᵃ で消えると仮定する。

pᵃ 倍写像の核の濃度は、有限巡回群では

    |ker(pᵃ:K→K)| = gcd(|K|,pᵃ) = pᵃ

となる。B の点は包含と零化条件によりこの核へ入る。
この写像は元の同じ点を保つ単射で、両者の実際の濃度が一致するので全射でもある。
したがって、

    x∈B ↔ x∈K ∧ pᵃ•x=0

を得る。この群論自体は p の素数性を必要としない。
巡回性・正確な濃度・包含・零化の条件は省略しない。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Coset.Card

#print "file: DkMath.Lib.Algebra.CyclicPrimePowerTorsion"

/-!
# 巡回冪位数群内の全ての低位捩れを同じ部分群へ戻す

位数 p^b の巡回群 K に、位数 p^a の B が含まれ、a≤b なら、
B の p^a 零化から K[p^a]=B を濃度で証明する。素数性はこの群論には不要。
集合的な安定性や高位捩れ全体への包含を仮定する補題ではない。
-/

namespace DkMath.Lib.Algebra.CyclicPrimePowerTorsion
variable {G : Type*} [AddCommGroup G]

/-- 低位の部分群は、大きい巡回群の同じ冪捩れ全体である。 -/
theorem mem_iff_killed {p a b : ℕ} (hab : a ≤ b)
    (K B : AddSubgroup G) [Finite K] [IsAddCyclic K]
    (hK : Nat.card K = p ^ b) (hBK : B ≤ K) (hB : Nat.card B = p ^ a)
    (hkill : ∀ x ∈ B, p ^ a • x = 0) {x : G} :
    x ∈ B ↔ x ∈ K ∧ p ^ a • x = 0 := by
  let f : B → (nsmulAddMonoidHom (p ^ a) : K →+ K).ker := fun y =>
    ⟨⟨y.val, hBK y.property⟩, Subtype.ext (hkill y.val y.property)⟩
  have hf : Function.Injective f := by
    intro u v h
    exact Subtype.ext (congrArg (fun z : (nsmulAddMonoidHom (p ^ a) : K →+ K).ker => z.val.val) h)
  have hker : Nat.card (nsmulAddMonoidHom (p ^ a) : K →+ K).ker = p ^ a := by
    rw [IsAddCyclic.card_nsmulAddMonoidHom_ker, hK, Nat.gcd_eq_right (pow_dvd_pow p hab)]
  have hsurj : Function.Surjective f :=
    ((Nat.bijective_iff_injective_and_card f).mpr ⟨hf, hB.trans hker.symm⟩).2
  constructor
  · intro hx
    exact ⟨hBK hx, hkill x hx⟩
  · rintro ⟨hx, hpx⟩
    obtain ⟨y, hy⟩ := hsurj ⟨⟨x, hx⟩, Subtype.ext hpx⟩
    have he : y.val = x := congrArg
      (fun z : (nsmulAddMonoidHom (p ^ a) : K →+ K).ker => z.val.val) hy
    exact he ▸ y.property

end DkMath.Lib.Algebra.CyclicPrimePowerTorsion
```

## ステップ2：同じ合併の標準 Tate 加群へ戻す

同じ Source、残余直線 L、rootField、hclass、全段 hbad を保持する。
以前の同じ塔 K₀⊆K₁⊆… と合併 U を使う。

### 合併の捩れと各段の一致

まず既存の二つの同じ段 Kₙ≤Kₘ、n≤m に、ステップ1を適用する。

    x∈Kₙ ↔ x∈Kₘ ∧ p^(n+1)•x=0.

この有限段の結論は、既存の段の濃度・巡回性・零化から得られ、hclass/hbad を追加要求しない。

次に x∈U が p^(n+1) で消えるとする。
x は実際のある Kₘ に属する。n≤m なら上の有限巡回群の結果で Kₙ へ戻る。
m≤n なら以前の同じ塔の単調性で Kₙ に入る。
逆向きは Kₙ の合併への包含と零化から従う。

    x∈U ∧ p^(n+1)•x=0 ↔ x∈Kₙ.

**これは U の中の捩れの主張である。**
全幾何学的点群 E(ℚ̄) の p^(n+1) 捩れ全体が Kₙ になるとは主張しない。

### 標準 Tate p U の自然な線形同型

前回の汎用定義 `Tate p G` に、実際の加法群 U をそのまま代入する。
標準 scalar は以前の `PrimePowerTateModule` のものを使う。
U→E(ℚ̄) の部分群包含から、成分ごとの線形写像

    Tate p U →ₗ[ℤₚ] Tate p E(ℚ̄)

を得る。元の包含が単射なので、この写像も単射である。

Tate p U の第 n 成分は U 内の点であり、p^(n+1) で消える。
今回の捩れ同定により、その同じ点は Kₙ に入る。
従って像は以前の同じ `residualCyclicTateLine` に入る。

逆向きは、同じ直線の第 n 成分を Kₙ⊆U によって U の点とみなすだけである。
零化と p 倍互換性は元の同じ点の等式であり、両向きで保たれる。
これにより、

    residualUnionTateLineEquiv : Tate p U ≃ₗ[ℤₚ] residualCyclicTateLine

を構成する。以前の ℤₚ との同型を合成し、

    residualUnionTateEquiv : ℤₚ ≃ₗ[ℤₚ] Tate p U

も得る。階数1という表現はこの実際の線形同型に基づく。
自然な同定の前後で、全点群の Tate 加群内の各成分は変わらない。

### 同じ Galois 作用の保存

以前の U の Galois 安定性から、元の点作用を U 自体へ制限する。
その成分ごとの標準線形作用を Tate p U に入れる。
自然な包含がこの同じ作用と可換することを証明する。

全点群への包含の単射性と、前回の同じ Tate 直線の scalar 作用公式から、
標準 Tate p U の全ての点列 x に対して

    σ(x)=χ∞(σ)•x

を得る。異なる作用や異なる指標をこの同定のために選ぶことはしない。

### 元の点列は全 Tate 加群の p 倍に入らない

任意の全 Tate 点列 w に対して、p•w の第0成分は0である。
標準 scalar の定義と第0点の p 零化を使うと、

    (p•w)₀=p•w₀=0

となる。一方、前回の元の生成元点列 v の第0成分は e₀≠0 である。
従って p•w=v は不可能であり、

    ∀ w∈Tate p E(ℚ̄), (p:ℤₚ)•w≠v

を証明する。全 Tate 加群が自由階数2であるという仮定は使わない。
ここでの原始性の主張は、正確にこの「p 倍に属さない」という結論である。
基底への拡張や階数2の表示まで得たとは主張しない。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclicTateLine
import DkMath.Lib.Algebra.CyclicPrimePowerTorsion

#print "file: DkMath.FLT.FreyCyclicTateUnion"

/-!
# 同じ合併の全 p 冪捩れと標準 Tate 加群の同定

U[p^(n+1)]=Kₙ を同じ巡回段の濃度から証明する。
標準の Tate p U から同じ既存直線への自然な線形同型を作り、
同じ全点群への包含と Galois 作用を保つ。hclass・全段 hbad は保持する。
全 Tate 加群の階数2や Frobenius 特性多項式、一般 hno はまだ証明しない。
-/

namespace DkMath.FLT.Frey.Source
open DkMath.Lib.Algebra DkMath.Lib.NumberTheory
open EllipticTorsionRepresentation DkMath.Lib.RepresentationTheory PrimePowerTateSequence
noncomputable section

section Stages
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n m : ℕ}

/-- 同じ大きい巡回段の低位捩れは、含まれる同じ小さい段全体。
既存段の群論であり、hclass/hbad を新たに要求しない。 -/
theorem ResidualCyclicStage.mem_iff_killed_in_later
    (T : S.ResidualCyclicStage L n) (V : S.ResidualCyclicStage L m)
    (hnm : n ≤ m) (hTV : T.carrier ≤ V.carrier) (x : Points S.rationalCurve) :
    x ∈ T.carrier ↔ x ∈ V.carrier ∧ p ^ (n + 1) • x = 0 := by
  let := V.finite
  let := V.cyclic
  exact CyclicPrimePowerTorsion.mem_iff_killed (Nat.add_le_add_right hnm 1)
    V.carrier T.carrier V.card hTV T.card T.killed
end Stages

open CyclotomicKernelField CyclotomicKummerWeight
variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic
variable (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p) (hp5 : 5 ≤ p)
local instance : NumberField (rootField ζ) := rootField_numberField ζ
variable
    (hclass : ∀ a : CyclotomicClassVanishing.ClassModP (rootField ζ) p,
      (∀ γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ),
        CyclotomicClassVanishing.classModPAction p γ a =
          (baseCharacter hζ γ : ZMod p) ^ 2 • a) → a = 0)
    (hbad : ∀ (n : ℕ) (T : S.ResidualCyclicStage L n), S.ResonantAbsorptionAt T.carrier)
local notation "tower" => S.residualCyclicTower L hline hcofixed hζ hp5 hclass hbad
local notation "union" => S.residualCyclicTowerUnion L hline hcofixed hζ hp5 hclass hbad
local notation "line" => S.residualCyclicTateLine L hline hcofixed hζ hp5 hclass hbad
local notation "vec" => S.residualCyclicTateVector L hline hcofixed hζ hp5 hclass hbad
local notation "padicChar" => S.residualPadicTowerCharacter L hline hcofixed hζ hp5 hclass hbad

/-- 同じ合併の全ての p^(n+1) 捩れは、正確に同じ第 n 段である。 -/
theorem residualCyclicTowerUnion_torsion (n : ℕ) (x : Points S.rationalCurve) :
    (x ∈ union ∧ p ^ (n + 1) • x = 0) ↔ x ∈ (tower n).carrier := by
  constructor
  · rintro ⟨hx, hk⟩
    obtain ⟨m, hm⟩ := (S.mem_residualCyclicTowerUnion L hline hcofixed hζ hp5 hclass hbad x).mp hx
    by_cases hnm : n ≤ m
    · exact ((tower n).mem_iff_killed_in_later (tower m) hnm
        (S.residualCyclicTower_monotone L hline hcofixed hζ hp5 hclass hbad hnm) x).mpr ⟨hm, hk⟩
    · exact S.residualCyclicTower_monotone L hline hcofixed hζ hp5 hclass hbad (by omega : m ≤ n) hm
  · intro hx
    exact ⟨(S.mem_residualCyclicTowerUnion L hline hcofixed hζ hp5 hclass hbad x).mpr ⟨n, hx⟩,
      (tower n).killed x hx⟩

/-- 標準 Tate p U の全点群への包含。成分は元の同じ点である。 -/
def residualUnionTate_inclusion : Tate p (union) →ₗ[ℤ_[p]] Tate p (Points S.rationalCurve) :=
  mapLinear (union).subtype

theorem residualUnionTate_inclusion_injective :
    Function.Injective (S.residualUnionTate_inclusion L hline hcofixed hζ hp5 hclass hbad) :=
  map_injective (union).subtype Subtype.val_injective

/-- 標準 Tate p U の零化条件を使って、各成分を同じ段へ戻す線形写像。 -/
def residualUnionTateToLine : Tate p (union) →ₗ[ℤ_[p]] line where
  toFun x := ⟨S.residualUnionTate_inclusion L hline hcofixed hζ hp5 hclass hbad x, fun n => by
    apply (S.residualCyclicTowerUnion_torsion L hline hcofixed hζ hp5 hclass hbad n (evaluation n x).val).mp
    refine ⟨(evaluation n x).property, ?_⟩
    have h := congrArg (union).subtype (killed x n)
    rw [map_nsmul, map_zero] at h
    exact h⟩
  map_add' x y := Subtype.ext (map_add _ x y)
  map_smul' a x := Subtype.ext (map_smul _ a x)

local notation "toLine" => S.residualUnionTateToLine L hline hcofixed hζ hp5 hclass hbad

/-- 標準 Tate p U と以前の同じ Tate 直線の自然な線形同型。
逆向きは各有限段の点を同じ合併内の点とみなすだけである。 -/
def residualUnionTateLineEquiv : Tate p (union) ≃ₗ[ℤ_[p]] line :=
  LinearEquiv.ofBijective toLine ⟨by
    intro x y h
    apply S.residualUnionTate_inclusion_injective L hline hcofixed hζ hp5 hclass hbad
    exact congrArg Subtype.val h, by
    intro x
    let y : Tate p (union) := ⟨fun n => ⟨evaluation n x.val,
      (S.mem_residualCyclicTowerUnion L hline hcofixed hζ hp5 hclass hbad _).mpr ⟨n, x.property n⟩⟩,
      ⟨fun n => Subtype.ext (killed x.val n), fun n => Subtype.ext (compatible x.val n)⟩⟩
    refine ⟨y, ?_⟩
    apply Subtype.ext
    apply PrimePowerTateSequence.ext
    intro n
    rfl⟩

/-- 標準 Tate p U 自体が自由階数1であることを与える同じ線形同型。 -/
def residualUnionTateEquiv : ℤ_[p] ≃ₗ[ℤ_[p]] Tate p (union) :=
  (S.residualCyclicTateLineEquiv L hline hcofixed hζ hp5 hclass hbad).trans
    (S.residualUnionTateLineEquiv L hline hcofixed hζ hp5 hclass hbad).symm

/-- 自然な同定の前後で全点群の Tate 加群内の点列は変わらない。 -/
theorem residualUnionTateLineEquiv_inclusion (x : Tate p (union)) :
    S.residualCyclicTateLine_inclusion L hline hcofixed hζ hp5 hclass hbad
      (S.residualUnionTateLineEquiv L hline hcofixed hζ hp5 hclass hbad x) =
    S.residualUnionTate_inclusion L hline hcofixed hζ hp5 hclass hbad x := rfl

/-- 同じ合併への元の実際の点作用の制限。 -/
def residualTowerUnionAction : Field.absoluteGaloisGroup ℚ →* AddMonoid.End (union) where
  toFun σ :=
    { toFun := fun x => ⟨pointAction S.rationalCurve σ x.val,
        S.residualCyclicTowerUnion_stable L hline hcofixed hζ hp5 hclass hbad σ x.val x.property⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' x y := Subtype.ext (map_add _ x.val y.val) }
  map_one' := by
    apply AddMonoidHom.ext; intro x
    exact Subtype.ext (pointAction_one S.rationalCurve x.val)
  map_mul' σ τ := by
    apply AddMonoidHom.ext; intro x
    exact Subtype.ext (pointAction_mul S.rationalCurve σ τ x.val)

local notation "uAction" => S.residualTowerUnionAction L hline hcofixed hζ hp5 hclass hbad

/-- 標準 Tate p U への包含は同じ実際の線形 Galois 作用と可換。 -/
theorem residualUnionTate_inclusion_equivariant (σ : Field.absoluteGaloisGroup ℚ) (x : Tate p (union)) :
    S.residualUnionTate_inclusion L hline hcofixed hζ hp5 hclass hbad (actionLinear uAction σ x) =
    actionLinear S.residualPointActionHom σ
      (S.residualUnionTate_inclusion L hline hcofixed hζ hp5 hclass hbad x) := rfl

/-- 同じ標準 Tate p U の全ての点列への作用は、元の同じ指標の scalar 倍。 -/
theorem residualUnionTate_action_scalar (σ : Field.absoluteGaloisGroup ℚ) (x : Tate p (union)) :
    actionLinear uAction σ x = (padicChar σ : ℤ_[p]) • x := by
  apply S.residualUnionTate_inclusion_injective L hline hcofixed hζ hp5 hclass hbad
  rw [S.residualUnionTate_inclusion_equivariant L hline hcofixed hζ hp5 hclass hbad, map_smul]
  exact S.residualCyclicTateLine_action_scalar L hline hcofixed hζ hp5 hclass hbad σ (toLine x)

/-- 元の非零生成元点列は、全 Tate 加群の p 倍には入らない。
第0成分の非零性で検出する。全 Tate 加群の階数2は仮定しない。 -/
theorem residualCyclicTateVector_not_p_multiple (w : Tate p (Points S.rationalCurve)) :
    (p : ℤ_[p]) • w ≠ (vec).val := by
  intro h
  have hz : evaluation 0 ((p : ℤ_[p]) • w) = 0 := by
    rw [evaluation_smul, map_natCast]
    have he := nsmul_eq_of_residue (evaluation 0 w) (killed w 0)
      (ZMod.natCast_zmod_val (p : ZMod (p ^ (0 + 1))))
    exact he.trans (by simpa only [Nat.zero_add, pow_one] using killed w 0)
  have he := congrArg (evaluation 0) h
  rw [hz] at he
  apply S.residualTateSeed_ne_zero L hline hcofixed hζ hp5 hclass hbad
  exact Subtype.ext he.symm

end
end DkMath.FLT.Frey.Source
```

## 回帰例と監査

`DkMathTest.FLT.FreyCyclicTateUnion` は、実際の ZMod 125 とその25捩れ部分群を使う。
有限巡回群の核の濃度から補題の条件を確認し、5が入り1が入らないことを検査する。
ZMod 5×ZMod 5 では、第二座標が非零の点(0,1)も5で消えるが第一座標軸には入らない。
巡回性を落として小さい部分群が全ての低位捩れだと結論しないための具体例である。

同じ抽象 Frey Source と条件付き塔では、第4段に属する p² 捩れが同じ第1段へ戻ることを確認する。
Tate p U と同じ直線の往復で任意の元を回収し、第3成分が同じ元の点のままであることも確認する。
任意の全 Tate 点列の p 倍と、元の非零点列 v が一致しないことも検査する。

主要13宣言の公理報告、型・構成子・不透明証明本体の再帰依存監査、10件の公開入力監査を追加する。
汎用巡回群の核の濃度、実際の合併所属、同じ有限段の単調性・零化、
標準線形写像と同じ作用、元の種の非零性が実際に使われることを確認する。
hclass と全段 hbad は保持し、htorsion/hequiv/hrank/hfree/hscalar/hprimitive を新たな provider にしない。

Lib/FLT/root 公開、通常テスト入口、root smoke、教科書全文一致・個別コンパイルも確認する。
記録：`evidence/validation-note032-frey-tate-union.txt`。

## 残る境界

- 同じ円分類群商の特定 ω² 成分の消滅 hclass。
- 全段の共鳴素点条件 hbad または反復に十分な保存性。
- 全 Tate 加群の階数2・原始元の基底への拡張・Weil pairing。
- 良還元 Frobenius の特性多項式と、最終矛盾に必要な局所・大域算術。

今回、U の全低位捩れと同じ有限段の一致、標準 Tate p U の階数1同型、
同じ Galois scalar 作用、元の v が全 Tate 加群の p 倍に属さないことまで完成した。
点列群の位相や作用の連続性を新たに構成したとは主張しない。
**一般 hno は引き続き未完成である。**
使用するのは既存の同じ塔・生成元・指標・標準 scalar と Mathlib の有限巡回核の濃度である。
外部の消滅定理・イソジェニー分類は追加していない。
