# NOTE-032 教科書：同じ巡回塔の有限指標と剰余両立性

日付：2026-11-06。前段：`TEXTBOOK-N032-FREY-CONDITIONAL-TOWER-261106.md`。
今回の2ステップは、①巡回群への実際の作用を単元値指標に変換する汎用構成、
②同じ Frey 巡回段への適用と、隣接段・mod p の両立性の証明である。
既存の良還元論証の固定性条件を照合し、指標値1からの点数上界も明示条件付きで接続する。

以下の2つの Lean ブロックは production ファイルの全文である。
モジュールとして順に配置して利用する。個別のコピー後コンパイルも検証する。
ファイル同定に必須の import 直後の `#print "file: …"` は省略しない。

## 既存の最終矛盾の入力を確認する

`EllipticFrobeniusFixedReduction.card_fixed_torsion_le_finite_points` は、
Frobenius に **点ごとに固定された** 実際の捩れ点を有限体へ単射に還元する。
`torsion_index_le_finite_point_count_of_absorbing` は、それとは別に、
高位捩れ全体で σ(P)−P が対象の K に入るという **商上の作用差吸収** を要求する。
前回の塔で得た K の集合的な安定性だけから、どちらも自動的には従わない。

今回はその差を隠さず、各段の実際の作用を数値として読み出せるようにする。
新しい指標は作用を表現するための構成であり、値が1であるという仮定を加えて定義しない。

## ステップ1：巡回作用から実際の単元値指標へ

Γ が加法群 G に ρ:Γ→*AddMonoid.End G として作用し、
巡回座標 e:ZMod N≃+G があるとする。

    c(g)=e⁻¹(ρ(g)(e(1)))

と定義する。ZMod N の加法自己準同型は1の像を掛ける写像なので、

    e⁻¹(ρ(g)x)=c(g)e⁻¹(x)

が成立する。合成則から c(gh)=c(g)c(h)、c(1)=1 を証明する。
Γ は群なので c(g⁻¹) が c(g) の逆元となり、

    character : Γ →* (ZMod N)ˣ

を実際に構成できる。
可逆性や文字通りの character を新しい provider として要求しない。

N≠0 では、元の同じ群の点について

    ρ(g)x=character(g).val • x

が成立する。指標値1と全点の固定性は正確に同値である。
さらに、同じ G に別の巡回座標 e′ を取っても指標は変わらない。
自然数 scalar 作用から係数を一意に復元できることを使って証明する。
従って、次段と前段で同じ生成元を機械的に選ぶ必要はない。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Group.Units.Hom

#print "file: DkMath.Lib.Algebra.CyclicActionCharacter"

/-!
# 巡回加法群への実際の作用を単元値指標へ変換する

座標 e:ZMod N≃+G のもとで、作用の係数は e⁻¹(ρ(g)(e(1)))。
群作用の合成則から乗法性と可逆性を証明する。恒等作用は係数1と同値。
-/

namespace DkMath.Lib.Algebra.CyclicActionCharacter

noncomputable section
variable {Γ G : Type*} [Group Γ] [AddCommGroup G] {N : ℕ}
    (e : ZMod N ≃+ G) (ρ : Γ →* AddMonoid.End G)

/-- 実際の作用の座標上の係数。 -/
def coefficient (g : Γ) : ZMod N := e.symm (ρ g (e 1))

/-- ZMod の加法自己準同型は、1の像を掛ける写像そのもの。 -/
theorem coordinate_action (g : Γ) (x : G) :
    e.symm (ρ g x) = coefficient e ρ g * e.symm x := by
  let f : ZMod N →+ ZMod N := e.symm.toAddMonoidHom.comp ((ρ g).comp e.toAddMonoidHom)
  have h := (f.toZModLinearMap N).map_smul (e.symm x) (1 : ZMod N)
  change f (e.symm x * 1) = e.symm x * f 1 at h
  rw [mul_one] at h
  change e.symm (ρ g (e (e.symm x))) = e.symm x * coefficient e ρ g at h
  rw [e.apply_symm_apply] at h
  exact h.trans (mul_comm _ _)

/-- 合成される実際の作用の係数は乗法的。 -/
def coefficientHom : Γ →* ZMod N where
  toFun := coefficient e ρ
  map_one' := by simp [coefficient]
  map_mul' g h := by
    change e.symm (ρ (g * h) (e 1)) = _
    rw [map_mul]
    change e.symm (ρ g (ρ h (e 1))) = _
    exact coordinate_action e ρ g (ρ h (e 1))

/-- 群の逆元を写して可逆性を内部証明した、実際の単元値指標。 -/
def character : Γ →* (ZMod N)ˣ := (coefficientHom e ρ).toHomUnits

/-- 指標の値は同じ作用の係数である。 -/
theorem character_coe (g : Γ) : (character e ρ g : ZMod N) = coefficient e ρ g := rfl

/-- 指標が記述する、同じ群のすべての元への実際の作用。 -/
theorem action_eq_nsmul [NeZero N] (g : Γ) (x : G) :
    ρ g x = (character e ρ g : ZMod N).val • x := by
  apply e.symm.injective
  rw [coordinate_action, map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val, character_coe]

/-- 任意の自然数の scalar 作用から、同じ指標の値を一意に復元する。 -/
theorem character_eq_natCast_of_action (g : Γ) (a : ℕ)
    (h : ∀ x : G, ρ g x = a • x) : (character e ρ g : ZMod N) = a := by
  rw [character_coe]
  change e.symm (ρ g (e 1)) = _
  have he := congrArg e.symm (h (e 1))
  simpa only [map_nsmul, AddEquiv.symm_apply_apply, nsmul_eq_mul, mul_one] using he

/-- 指標の値1は、すべての点の固定性と正確に同値。群の安定性とは異なる。 -/
theorem character_eq_one_iff (g : Γ) : character e ρ g = 1 ↔ ∀ x : G, ρ g x = x := by
  constructor
  · intro h x
    apply e.symm.injective
    rw [coordinate_action]
    have hc : coefficient e ρ g = 1 := congrArg Units.val h
    rw [hc, one_mul]
  · intro h
    apply Units.ext
    change coefficient e ρ g = 1
    simp only [coefficient, h, AddEquiv.symm_apply_apply]

/-- 座標の選び直しで指標は変わらない。実際の作用を記述する同じ scalar である。 -/
theorem character_independent [NeZero N] (e' : ZMod N ≃+ G) : character e ρ = character e' ρ := by
  apply MonoidHom.ext
  intro g
  apply Units.ext
  have h := character_eq_natCast_of_action e ρ g (character e' ρ g : ZMod N).val
    (action_eq_nsmul e' ρ g)
  simpa only [ZMod.natCast_zmod_val] using h

end
end DkMath.Lib.Algebra.CyclicActionCharacter
```

## ステップ2：同じ Frey 巡回段に指標を載せる

同じ Source S・同じ残余直線 L・段 T:ResidualCyclicStage S L n を固定する。
その位数は p^(n+1) である。有限巡回群の座標を取り、
T.stable を使って **元の同じ pointAction** を T.carrier へ制限する。
これを前段の汎用構成に渡し、

    χT : Gℚ →* (ZMod (p^(n+1)))ˣ

を得る。同じ点 x∈T.carrier への作用は χT(σ).val 倍そのものである。
また、χT の核は、実際の全 E[p^(n+1)] 表現の開核を含むため開いている。
新しい連続性・開核の provider を要求しない。

### 包含と剰余写像

T⊆U、n≤m なら、同じ Galois 元 σ の上段係数 χU(σ) は、
すべての下段の点にもその自然数代表元の scalar として作用する。
下段係数の一意性から、

    χU(σ) mod p^(n+1)=χT(σ)

を得る。両側を Units.map と **実際の ZMod.castHom** で記述する。
座標を別々に選んでも両立し、互換な生成元の存在を追加仮定しない。

`residualCyclicTowerCharacter` は以前構成した同じ選択済みの塔の指標族である。
その隣接段の両立性は、前回の同じ塔の包含から内部供給する。
塔の構成と同じ hclass と全段 hbad は引き続き明示入力であり、今回証明していない。
Zp 単元値の極限指標や Tate 加群自体はまだ構成していない。

### mod p は同じ元の円分指標

同じ底 B の座標を ZMod p で取り、元の Cofixed 直線に対する既存の

    σ(x)=χp(σ).val • x  (x∈B)

を使う。任意の段は同じ B を含むため、係数の一意性により

    χT(σ) mod p = χp(σ)

を証明できる。この定理は hline・hcofixed を保持するが、
対象の段 T が与えられていれば hclass/hbad を必要としない。

### 良還元点数への、明示条件付きの接続

良還元素点 ell≠p、同じ局所住所 A、実際の Frobenius σ を固定する。
**hchar:χT(σ)=1 が供給された場合**、同じ T の全点が固定される。
T を実際の E[p^(n+1)] の Frobenius 固定核へ単射に写し、既存の還元単射を適用すると

    p^(n+1) ≤ #E(𝔽ell)

を得る。これが `card_le_good_points_of_character_one` である。
指標値1を導いた定理ではなく、その値を明示入力として残す。

この条件付き上界は、前述の「高位捩れ全体の作用差吸収」を用いる論証とは別の十分条件である。
両者を同一視せず、今後の一般 hno の経路で χT(Frob)=1 が必ず得られるとも主張しない。
集合的な安定性から Frobenius 固定性を導く飛躍を避け、実際に必要な作用の情報を露出させる。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclotomicConditionalTower
import DkMath.Lib.Algebra.CyclicActionCharacter
import DkMath.FLT.FreyGoodReductionTowerObstruction

#print "file: DkMath.FLT.FreyCyclicTowerCharacter"

/-!
# 同じ巡回捩れ段の実際の単元値指標と両立性

段の安定性から点ごとの恒等性を仮定せず、実際の Galois 作用の scalar を構成する。
包含された段の指標は剰余写像で両立する。固定性は指標値1と同値である。
良還元点数による上界には、その具体的な Frobenius 指標値1を明示入力に残す。
-/

namespace DkMath.FLT.Frey.Source

open DkMath.Lib.Algebra DkMath.Lib.NumberTheory
open EllipticTorsionRepresentation EllipticFrobeniusFixedReduction
open DkMath.Lib.RepresentationTheory
noncomputable section

variable {p : ℕ} [Fact p.Prime] {S : Source p}
local instance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic
variable {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ}

/-- 同じ有限巡回段の座標。値域は位数 p^(n+1) の環である。 -/
def ResidualCyclicStage.coordinates (T : S.ResidualCyclicStage L n) :
    ZMod (p ^ (n + 1)) ≃+ T.carrier :=
  zmodAddEquivOfGenerator T.cyclic.exists_generator.choose_spec T.card

/-- 同じ段への、元の絶対 Galois 点作用の制限。 -/
def ResidualCyclicStage.action (T : S.ResidualCyclicStage L n) :
    Field.absoluteGaloisGroup ℚ →* AddMonoid.End T.carrier where
  toFun σ :=
    { toFun := fun x => ⟨pointAction S.rationalCurve σ x, T.stable σ x x.property⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' x y := Subtype.ext (map_add _ x.val y.val) }
  map_one' := by
    apply AddMonoidHom.ext
    intro x
    apply Subtype.ext
    exact pointAction_one S.rationalCurve x.val
  map_mul' σ τ := by
    apply AddMonoidHom.ext
    intro x
    apply Subtype.ext
    exact pointAction_mul S.rationalCurve σ τ x.val

/-- 同じ巡回段への実際の作用を記述する単元値指標。恒等性は仮定しない。 -/
def ResidualCyclicStage.character (T : S.ResidualCyclicStage L n) :
    Field.absoluteGaloisGroup ℚ →* (ZMod (p ^ (n + 1)))ˣ :=
  CyclicActionCharacter.character T.coordinates T.action

/-- 点ごとの scalar 公式。単なる群の集合的安定性より強い内容を構成から証明する。 -/
theorem ResidualCyclicStage.character_spec (T : S.ResidualCyclicStage L n)
    (σ : Field.absoluteGaloisGroup ℚ) (x : Points S.rationalCurve) (hx : x ∈ T.carrier) :
    pointAction S.rationalCurve σ x = (T.character σ : ZMod (p ^ (n + 1))).val • x := by
  let : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have h := CyclicActionCharacter.action_eq_nsmul T.coordinates T.action σ (⟨x, hx⟩ : T.carrier)
  have he := congrArg T.carrier.subtype h
  rw [map_nsmul] at he
  exact he

/-- 指標値1と同じ段の全点固定は同値。安定性だけから値1を結論しない。 -/
theorem ResidualCyclicStage.character_eq_one_iff (T : S.ResidualCyclicStage L n)
    (σ : Field.absoluteGaloisGroup ℚ) :
    T.character σ = 1 ↔ ∀ x ∈ T.carrier, pointAction S.rationalCurve σ x = x := by
  rw [character, CyclicActionCharacter.character_eq_one_iff]
  constructor
  · intro h x hx
    exact congrArg T.carrier.subtype (h ⟨x, hx⟩)
  · intro h x
    exact Subtype.ext (h x.val x.property)

/-- 既存の実際の全捩れ表現の開核を含むので、この同じ指標も開核を持つ。 -/
theorem ResidualCyclicStage.character_kernel_isOpen (T : S.ResidualCyclicStage L n) :
    IsOpen (T.character.ker : Set (Field.absoluteGaloisGroup ℚ)) := by
  apply Subgroup.isOpen_mono (H₁ := representationKernel S.rationalCurve (p ^ (n + 1))) _
    (representationKernel_isOpen_of_ne_zero S.rationalCurve _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero))
  intro σ hσ
  change T.character σ = 1
  apply (T.character_eq_one_iff σ).mpr
  intro x hx
  change representation S.rationalCurve (p ^ (n + 1)) σ = 1 at hσ
  have he : representation S.rationalCurve (p ^ (n + 1)) σ ⟨x, T.killed x hx⟩ = ⟨x, T.killed x hx⟩ := by
    rw [hσ]
    rfl
  exact congrArg (fun z : Torsion S.rationalCurve (p ^ (n + 1)) => z.val) he

/-- 包含された同じ巡回段の作用指標は、標準の剰余写像で両立する。 -/
theorem ResidualCyclicStage.character_compatible (T : S.ResidualCyclicStage L n)
    {m : ℕ} (U : S.ResidualCyclicStage L m) (hnm : n ≤ m) (hTU : T.carrier ≤ U.carrier)
    (σ : Field.absoluteGaloisGroup ℚ) :
    Units.map (ZMod.castHom (pow_dvd_pow p (Nat.add_le_add_right hnm 1))
      (ZMod (p ^ (n + 1)))).toMonoidHom (U.character σ) = T.character σ := by
  let : NeZero (p ^ (m + 1)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have he : (T.character σ : ZMod (p ^ (n + 1))) = (U.character σ : ZMod (p ^ (m + 1))).val := by
    apply CyclicActionCharacter.character_eq_natCast_of_action T.coordinates T.action
    intro x
    apply Subtype.ext
    change T.carrier.subtype (T.action σ x) = T.carrier.subtype ((U.character σ : ZMod (p ^ (m + 1))).val • x)
    rw [map_nsmul]
    exact U.character_spec σ x.val (hTU x.property)
  apply Units.ext
  change ZMod.castHom _ _ (U.character σ : ZMod (p ^ (m + 1))) = _
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]
  exact he.symm

/-- 同じ段の指標の mod p 還元は、元の同じ Cofixed 直線の円分指標。 -/
theorem ResidualCyclicStage.character_mod_prime (T : S.ResidualCyclicStage L n)
    (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L) (σ : Field.absoluteGaloisGroup ℚ) :
    Units.map (ZMod.castHom (dvd_pow_self p (by omega : n + 1 ≠ 0)) (ZMod p)).toMonoidHom
      (T.character σ) = CyclotomicRootModule.cyclotomicCharacter p σ := by
  let : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  let B := pointSubgroup S.rationalCurve p L
  let e : ZMod p ≃+ B := zmodAddEquivOfGenerator
    (isAddCyclic_pointSubgroup S.rationalCurve p L hline).exists_generator.choose_spec
    (card_pointSubgroup S.rationalCurve p L hline)
  let a : Field.absoluteGaloisGroup ℚ →* AddMonoid.End B :=
    (S.residualCyclicStageZero L hline hcofixed).action
  have hT : (CyclicActionCharacter.character e a σ : ZMod p) =
      (T.character σ : ZMod (p ^ (n + 1))).val := by
    apply CyclicActionCharacter.character_eq_natCast_of_action e a
    intro x
    apply Subtype.ext
    change B.subtype (a σ x) = B.subtype ((T.character σ : ZMod (p ^ (n + 1))).val • x)
    rw [map_nsmul]
    exact T.character_spec σ x.val (T.base x.property)
  have hc : (CyclicActionCharacter.character e a σ : ZMod p) =
      (CyclotomicRootModule.cyclotomicCharacter p σ : ZMod p) := by
    rw [← ZMod.natCast_zmod_val (CyclotomicRootModule.cyclotomicCharacter p σ : ZMod p)]
    apply CyclicActionCharacter.character_eq_natCast_of_action e a
    intro x
    apply Subtype.ext
    change B.subtype (a σ x) = B.subtype ((CyclotomicRootModule.cyclotomicCharacter p σ : ZMod p).val • x)
    rw [map_nsmul]
    exact S.residual_cofixed_pointSubgroup_action_eq_cyclotomic_nsmul L hline hcofixed σ x.property
  apply Units.ext
  change ZMod.castHom _ _ (T.character σ : ZMod (p ^ (n + 1))) = _
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]
  exact hT.symm.trans hc

/-- 良還元上界の一つの十分条件を、同じ Frobenius の具体的な指標値1として露出する。
この値1自体を証明した定理ではなく、商上の作用差吸収とも別の条件である。 -/
theorem ResidualCyclicStage.card_le_good_points_of_character_one (T : S.ResidualCyclicStage L n)
    {ell : ℕ} (hell : ell.Prime) (hellp : ell ≠ p) (hgood : ¬ (ell : ℤ) ∣ S.curve.Δ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : ValuationInertia.LiesOverPrime A ell)
    (σ : Field.absoluteGaloisGroup ℚ) (hσ : ValuationFrobenius.IsFrobeniusAt A σ ell)
    (hchar : T.character σ = 1) : p ^ (n + 1) ≤ S.goodReductionPointCount ell := by
  let M := p ^ (n + 1)
  let : Finite (Torsion S.rationalCurve M) :=
    finite_torsion_of_ne_zero S.rationalCurve M (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  let V := LinearMap.ker (representation S.rationalCurve M σ - 1)
  let f : T.carrier → V := fun x =>
    ⟨⟨x.val, T.killed x.val x.property⟩, by
      change representation S.rationalCurve M σ ⟨x.val, T.killed x.val x.property⟩ -
        ⟨x.val, T.killed x.val x.property⟩ = 0
      apply sub_eq_zero.mpr
      apply Subtype.ext
      exact (T.character_eq_one_iff σ).mp hchar x.val x.property⟩
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun z : V => z.val.val) h
  have hqn : ¬ ell ∣ M := fun h =>
    hellp ((Nat.prime_dvd_prime_iff_eq hell (Fact.out : p.Prime)).mp (hell.dvd_of_dvd_pow h))
  calc
    p ^ (n + 1) = Nat.card T.carrier := T.card.symm
    _ ≤ Nat.card V := Nat.card_le_card_of_injective f hf
    _ ≤ S.goodReductionPointCount ell :=
      card_fixed_torsion_le_finite_points S.rationalCurve S.curve S.curve_map hell hgood hqn A hA σ hσ

end

section Tower

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

/-- 構成済みの同じ塔の各段を表す、実際の有限単元値指標族。 -/
noncomputable def residualCyclicTowerCharacter (n : ℕ) : Field.absoluteGaloisGroup ℚ →* (ZMod (p ^ (n + 1)))ˣ :=
  (tower n).character

/-- 指標族の隣接段の両立性。各段の座標を独立に選んでも成り立つ。 -/
theorem residualCyclicTowerCharacter_compatible (n : ℕ) (σ : Field.absoluteGaloisGroup ℚ) :
    Units.map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ (n + 1)))
      (ZMod (p ^ (n + 1)))).toMonoidHom
        (S.residualCyclicTowerCharacter L hline hcofixed hζ hp5 hclass hbad (n + 1) σ) =
      S.residualCyclicTowerCharacter L hline hcofixed hζ hp5 hclass hbad n σ :=
  (tower n).character_compatible (tower (n + 1)) (Nat.le_succ n)
    (S.residualCyclicTower_step L hline hcofixed hζ hp5 hclass hbad n).1 σ

end Tower
end DkMath.FLT.Frey.Source
```

## 回帰例と検証の意味

`DkMathTest.FLT.FreyCyclicTowerCharacter` は具体的な ZMod 5 の乗法単元作用を使う。
全加法群は安定だが、−1 は1を動かし、指標値も−1≠1となる。
したがって「安定な有限巡回群なら点ごとに固定」という誤った推論を除外できる。
座標を x↦−x に取り替えても、同じ指標が得られることも確認する。

同じ抽象 Source と段について、hclass/hbad なしの開核・mod p 円分一致を確認する。
以前の算術条件付き塔については、隣接段だけでなく **二段飛ばした包含** に対しても
同じ剰余写像で指標が一致することを確認する。
固定性判定を使う回帰例でも、σ や Frobenius の指標値1を勝手に追加して結論しない。

主要11宣言の公理報告・再帰的な型／構成子／不透明証明本体の依存監査を行う。
公開入力監査は、作用指標の構成や両立性に hchar/hfixed/hcompat provider がないこと、
良還元上界には本当の hchar が残ること、塔の指標族には元の hclass/全段 hbad が残ることを確認する。
新規 Lib と FLT/root、通常の DkMathTest 入口の到達性、正確なモジュール表示、
教科書2ブロックの全文一致と個別コンパイルも検証する。
記録：`evidence/validation-note032-frey-tower-character.txt`。

## 残る数学

- 同じ円分類群商の特定 ω² 成分消滅 hclass。
- 各段の共鳴素点条件 hbad、またはその保存性・必要十分な弱い局所条件。
- 最終矛盾に使う実際の Galois 作用の追加算術。安定性は固定性ではない。
- Zp 単元値指標への極限や、Tate 加群の階数1部分加群の構成は今後の目標。

今回の2ステップは、実際の有限単元値指標とその同じ塔での両立性として完成した。
**一般 hno は引き続き未完成である。**
実装は Mathlib の巡回座標・ZMod 線形性・Units の群準同型持ち上げと、
既存の DkMath の同じ点作用・円分作用・全捩れ開核・還元単射に基づく。
外部消滅定理や未証明の Tate/Frobenius 作用を import していない。
