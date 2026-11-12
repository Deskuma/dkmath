# NOTE-032 教科書：同じ巡回塔の互換生成元と非零 Tate 点列

日付：2026-11-06。前段：`TEXTBOOK-N032-FREY-PADIC-CHARACTER-261106.md`。

今回の2ステップは、①実際の群の互換な捩れ点列とその加法的な作用、
②同じ Frey 巡回塔の互換生成元・非零点列・自然な単射・固定性判定である。
以下の2つの Lean ブロックは production ファイルの全文である。
モジュールへ順に配置し、import 直後の正確な `#print "file: …"` を保持する。

## ステップ1：全点群の中の具体的な Tate 点列

G を加法可換群、p を自然数とし、

    T(p,G) = { x : ℕ → G |
      ∀ n, p^(n+1) • x(n) = 0,
      ∀ n, p • x(n+1) = x(n) }

を G^ℕ の実際の加法部分群として定義する。
通常の Tate 点列の第0成分（法1で消える零成分）を除き、最初を p 捩れに合わせた添字である。
定義・加法群・準同型の自然性には素数性は不要である。

各成分への評価は加法準同型となる。零化・隣接遷移・成分ごとの外延性を公開する。
元の加法準同型 f:G→H を全成分に適用すると、互換性と零化が保たれる。
f が単射なら点列上の写像も単射である。

さらに実際の群作用 ρ:Γ→*AddMonoid.End G を各成分へ適用し、
Γ→*AddMonoid.End T(p,G) を構成する。
これは元の点を動かす同じ作用であり、新たに作用 provider を仮定するものではない。

**このファイルでは加法群を構成する。**
ℤₚ scalar、ℤₚ 線形性、自由性・階数、点列群上の位相や作用の連続性はまだ追加しない。
前回の ℤₚˣ 値指標の連続性と、新しい点列群の位相を混同しない。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Hom.End
import Mathlib.Algebra.Module.ZMod

#print "file: DkMath.Lib.Algebra.PrimePowerTateSequence"

/-!
# p 冪で消える互換な点列の加法群

第 n 成分の位数は p^(n+1) の約数、遷移は p 倍。
これは通常の Tate 点列の、法1の自明成分を除いた具体的なモデルである。
ここでは加法群・自然な単射・実際の作用を構成し、ℤₚ 加群構造や階数は主張しない。
-/

namespace DkMath.Lib.Algebra.PrimePowerTateSequence

variable (p : ℕ) (G : Type*) [AddCommGroup G]

/-- 実際の同じ群の点からなる、零化条件と遷移条件を満たす列。 -/
def sequences : AddSubgroup (ℕ → G) where
  carrier := {x | (∀ n, p ^ (n + 1) • x n = 0) ∧ (∀ n, p • x (n + 1) = x n)}
  zero_mem' := by simp
  add_mem' := by
    rintro x y ⟨hx, hxc⟩ ⟨hy, hyc⟩
    exact ⟨fun n => by simp only [Pi.add_apply, nsmul_add, hx n, hy n, add_zero],
      fun n => by simp only [Pi.add_apply, nsmul_add, hxc n, hyc n]⟩
  neg_mem' := by
    rintro x ⟨hx, hxc⟩
    exact ⟨fun n => by simp only [Pi.neg_apply, smul_neg, hx n, neg_zero],
      fun n => by simp only [Pi.neg_apply, smul_neg, hxc n]⟩

/-- 具体的な逆極限の加法群。素数性はこの定義自体には不要。 -/
abbrev Tate := sequences p G

variable {G} {p}

/-- 第 n 成分への評価は加法準同型。 -/
def evaluation (n : ℕ) : Tate p G →+ G where
  toFun x := x.val n
  map_zero' := rfl
  map_add' _ _ := rfl

/-- 同じ点列の実際の零化条件。 -/
theorem killed (x : Tate p G) (n : ℕ) : p ^ (n + 1) • evaluation n x = 0 := x.property.1 n

/-- 同じ点列の隣接遷移。 -/
theorem compatible (x : Tate p G) (n : ℕ) : p • evaluation (n + 1) x = evaluation n x :=
  x.property.2 n

/-- 点列の評価ごとの外延性。 -/
@[ext] theorem ext {x y : Tate p G} (h : ∀ n, evaluation n x = evaluation n y) : x = y :=
  Subtype.ext (funext h)

variable {H : Type*} [AddCommGroup H]

/-- 元の群の準同型を各成分へ適用する自然な写像。 -/
def map (f : G →+ H) : Tate p G →+ Tate p H where
  toFun x := ⟨fun n => f (evaluation n x),
    ⟨fun n => by rw [← map_nsmul, killed, map_zero],
      fun n => by rw [← map_nsmul, compatible]⟩⟩
  map_zero' := by apply ext; intro n; exact f.map_zero
  map_add' x y := by apply ext; intro n; exact f.map_add _ _

/-- 元の群の単射は、実際の互換点列上でも単射。 -/
theorem map_injective (f : G →+ H) (hf : Function.Injective f) : Function.Injective (map (p := p) f) := by
  intro x y h
  apply ext
  intro n
  exact hf (congrArg (evaluation n) h)

variable {Γ : Type*} [Group Γ]

/-- 元の群作用から、各成分に作用する同じ Tate 点列作用を構成する。 -/
def action (ρ : Γ →* AddMonoid.End G) : Γ →* AddMonoid.End (Tate p G) where
  toFun g := map (ρ g)
  map_one' := by
    apply AddMonoidHom.ext
    intro x
    apply ext
    intro n
    change ρ 1 (evaluation n x) = evaluation n x
    rw [map_one]
    rfl
  map_mul' g h := by
    apply AddMonoidHom.ext
    intro x
    apply ext
    intro n
    change ρ (g * h) (evaluation n x) = ρ g (ρ h (evaluation n x))
    rw [map_mul]
    rfl

/-- 作用の評価公式。各成分は元の同じ作用で動く。 -/
theorem evaluation_action (ρ : Γ →* AddMonoid.End G) (g : Γ) (x : Tate p G) (n : ℕ) :
    evaluation n (action ρ g x) = ρ g (evaluation n x) := rfl

end DkMath.Lib.Algebra.PrimePowerTateSequence
```

## ステップ2：同じ Frey 塔の中で互換生成元を選ぶ

前回までの同じ Source、同じ残余直線 L、同じ rootField、hclass、全段 hbad を固定する。
同じ塔の段 Kₙ は位数 p^(n+1) の巡回部分群で、Kₙ⊆Kₙ₊₁ であった。
既存の `residualCyclicTower_lift` は、Kₙ の各点 x に対して、
**同じ次段 Kₙ₊₁** 内の y と p•y=x を実際に返す。

### 依存再帰と各成分の生成性

第0段の巡回座標で1の像を e₀ とする。p は素数なので法 p の1は非零であり、e₀≠0 が従う。
直前に選んだ eₙ の p 倍逆像を同じ Kₙ₊₁ 内で選び、依存再帰で eₙ₊₁ とする。
各 n で無関係な生成元を選ぶ構成ではない。

    p•eₙ₊₁=eₙ,
    pⁿ•eₙ=e₀≠0,
    p^(n+1)•eₙ=0.

最後の式は同じ段の実際の零化条件から得る。
Mathlib の `addOrderOf_eq_prime_pow` により、eₙ の位数は正確に p^(n+1) となる。
生成部分群 ℤeₙ は Kₙ に含まれ、その濃度は eₙ の位数である。
同じ実際の Kₙ の濃度 p^(n+1) と一致するので、ℤeₙ=Kₙ を証明する。

### 実際の部分群と自然な単射

全幾何学的点群 G=Points E の上で、

    C = { x∈T(p,G) | ∀ n, x(n)∈Kₙ }

を加法部分群として定義する。
その自然な包含 C→T(p,G) は加法単射である。
元の `pointAction` を各成分へ適用すると、同じ Kₙ の安定性から C は保たれる。
この作用を C へ制限し、自然な包含の同変性を証明する。

互換生成元 e=(eₙ) は C の実際の元である。
第0成分 e₀≠0 なので、e≠0 も証明できる。
これにより、条件付き塔から実際の全点群の Tate 点列群の非零元を構成したことになる。

ここでの C は **同じ有限段の中に成分が入る点列** として定義している。
合併 U の全 p 冪捩れと各 Kₙ の一致を使った Tₚ(U) との同定、
C≃ₗ[ℤₚ]ℤₚ、Tₚ(E) の階数2や直和分解まで証明したとは主張しない。

### 一つの点列による指標の検出

前回の χ∞(σ)=1 は、同じ塔の合併 U の全点固定と同値であった。
各 eₙ が Kₙ を生成するため、一つの点列 e の固定性だけで各段の全点固定を検出できる。

    σ(e)=e ↔ χ∞(σ)=1.

これは scalar 公式 σ(e)=χ∞(σ)•e を ℤₚ 加群の中で証明したものではない。
現時点では加法点列の固定性と、以前の同じ指標の値1との正確な判定である。

同じ良還元素点・付値・Frobenius の条件を保つと、前回の χ∞(Frob)≠1 から
Frob(e)≠e も従う。非固定性は矛盾ではなく、同じ指標の非自明性の点列上の実現である。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyPadicTowerCharacter
import DkMath.Lib.Algebra.PrimePowerTateSequence

#print "file: DkMath.FLT.FreyCyclicTateVector"

/-!
# 同じ Frey 巡回塔の互換生成元と非零 Tate 点列

既存の同じ次段内 p 倍逆像から互換生成元を依存再帰で構成する。
実際の点群の Tate 点列内に同じ塔の加法部分群を構成し、自然に単射で含める。
各成分の位数 p^(n+1) と生成性を証明する。ここでは ℤₚ 加群構造・階数1同型や
Tate 加群全体の階数2、Weil pairing、Frobenius 特性多項式はまだ構成しない。
-/

namespace DkMath.FLT.Frey.Source

open DkMath.Lib.Algebra DkMath.Lib.NumberTheory
open EllipticTorsionRepresentation DkMath.Lib.RepresentationTheory
open PrimePowerTateSequence
noncomputable section

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
local notation "padicChar" => S.residualPadicTowerCharacter L hline hcofixed hζ hp5 hclass hbad

/-- 第0段の実際の非零生成元。 -/
def residualTateSeed : (tower 0).carrier := (tower 0).coordinates 1

/-- 底の生成元は実際に非零。 -/
theorem residualTateSeed_ne_zero : S.residualTateSeed L hline hcofixed hζ hp5 hclass hbad ≠ 0 := by
  let : Fact (1 < p ^ (0 + 1)) := ⟨by simpa using (Fact.out : p.Prime).one_lt⟩
  intro h
  apply (one_ne_zero : (1 : ZMod (p ^ (0 + 1))) ≠ 0)
  exact (tower 0).coordinates.injective (h.trans (map_zero (tower 0).coordinates).symm)

/-- 同じ直前の点の p 倍逆像を同じ次段内で選ぶ依存再帰。 -/
def residualTateGenerators : (n : ℕ) → (tower n).carrier :=
  Nat.rec (S.residualTateSeed L hline hcofixed hζ hp5 hclass hbad)
    (fun n x => ⟨(S.residualCyclicTower_lift L hline hcofixed hζ hp5 hclass hbad n x.val x.property).choose,
      (S.residualCyclicTower_lift L hline hcofixed hζ hp5 hclass hbad n x.val x.property).choose_spec.1⟩)

local notation "gen" => S.residualTateGenerators L hline hcofixed hζ hp5 hclass hbad

/-- 再帰で選んだ実際の隣接点の互換性。 -/
theorem residualTateGenerators_step (n : ℕ) : p • (gen (n + 1)).val = (gen n).val :=
  (S.residualCyclicTower_lift L hline hcofixed hζ hp5 hclass hbad n (gen n).val (gen n).property).choose_spec.2

/-- 第 n 点の p^n 倍は、同じ元の非零生成元。 -/
theorem residualTateGenerators_to_seed (n : ℕ) : p ^ n • (gen n).val = (gen 0).val := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_nsmul', S.residualTateGenerators_step L hline hcofixed hζ hp5 hclass hbad, ih]

/-- 選んだ点は各段で正確に最大位数を持つ。独立な生成元 provider は不要。 -/
theorem residualTateGenerators_order (n : ℕ) : addOrderOf (gen n).val = p ^ (n + 1) := by
  apply addOrderOf_eq_prime_pow
  · rw [S.residualTateGenerators_to_seed L hline hcofixed hζ hp5 hclass hbad]
    intro h
    apply S.residualTateSeed_ne_zero L hline hcofixed hζ hp5 hclass hbad
    exact Subtype.ext h
  · exact (tower n).killed _ (gen n).property

/-- 同じ点が同じ段全体を生成する。最大位数と実際の濃度の一致から証明する。 -/
theorem residualTateGenerators_generate (n : ℕ) :
    AddSubgroup.zmultiples (gen n).val = (tower n).carrier := by
  let := (tower n).finite
  apply AddSubgroup.eq_of_le_of_card_ge (AddSubgroup.zmultiples_le.mpr (gen n).property)
  rw [Nat.card_zmultiples, S.residualTateGenerators_order L hline hcofixed hζ hp5 hclass hbad, (tower n).card]

/-- 全幾何学的点への実際の作用を、元の同じ点作用から組み立てる。 -/
def residualPointActionHom : Field.absoluteGaloisGroup ℚ →* AddMonoid.End (Points S.rationalCurve) where
  toFun := pointAction S.rationalCurve
  map_one' := by
    apply AddMonoidHom.ext
    exact pointAction_one S.rationalCurve
  map_mul' σ τ := by
    apply AddMonoidHom.ext
    exact pointAction_mul S.rationalCurve σ τ

/-- 同じ塔の各段に属する互換点列からなる、実際の加法部分群。 -/
def residualCyclicTate : AddSubgroup (Tate p (Points S.rationalCurve)) where
  carrier := {x | ∀ n, evaluation n x ∈ (tower n).carrier}
  zero_mem' := fun n => (tower n).carrier.zero_mem
  add_mem' := fun hx hy n => (tower n).carrier.add_mem (hx n) (hy n)
  neg_mem' := fun hx n => (tower n).carrier.neg_mem (hx n)

local notation "line" => S.residualCyclicTate L hline hcofixed hζ hp5 hclass hbad

/-- 全幾何学的点の同じ Tate 点列群への自然な加法単射。 -/
def residualCyclicTate_inclusion : line →+ Tate p (Points S.rationalCurve) := (line).subtype

theorem residualCyclicTate_inclusion_injective :
    Function.Injective (S.residualCyclicTate_inclusion L hline hcofixed hζ hp5 hclass hbad) :=
  Subtype.val_injective

/-- 同じ点群の成分ごとの作用が、同じ塔の Tate 点列部分群を保つ。 -/
theorem residualCyclicTate_stable (σ : Field.absoluteGaloisGroup ℚ)
    (x : Tate p (Points S.rationalCurve)) (hx : x ∈ line) :
    action S.residualPointActionHom σ x ∈ line :=
  fun n => (tower n).stable σ (evaluation n x) (hx n)

/-- 同じ加法部分群への実際の Galois 作用の制限。 -/
def residualCyclicTateAction : Field.absoluteGaloisGroup ℚ →* AddMonoid.End line where
  toFun σ :=
    { toFun := fun x => ⟨action S.residualPointActionHom σ x.val,
        S.residualCyclicTate_stable L hline hcofixed hζ hp5 hclass hbad σ x.val x.property⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' x y := Subtype.ext (map_add _ x.val y.val) }
  map_one' := by
    apply AddMonoidHom.ext
    intro x
    apply Subtype.ext
    change action S.residualPointActionHom 1 x.val = x.val
    rw [map_one]
    rfl
  map_mul' σ τ := by
    apply AddMonoidHom.ext
    intro x
    apply Subtype.ext
    change action S.residualPointActionHom (σ * τ) x.val =
      action S.residualPointActionHom σ (action S.residualPointActionHom τ x.val)
    rw [map_mul]
    rfl

/-- 自然な包含は同じ Galois 作用と可換。 -/
theorem residualCyclicTate_inclusion_equivariant (σ : Field.absoluteGaloisGroup ℚ) (x : line) :
    S.residualCyclicTate_inclusion L hline hcofixed hζ hp5 hclass hbad
      (S.residualCyclicTateAction L hline hcofixed hζ hp5 hclass hbad σ x) =
    action S.residualPointActionHom σ
      (S.residualCyclicTate_inclusion L hline hcofixed hζ hp5 hclass hbad x) := rfl

/-- 同じ互換生成元からなる実際の Tate 点列。 -/
def residualCyclicTateVector : line :=
  ⟨⟨fun n => (gen n).val, ⟨fun n => (tower n).killed _ (gen n).property,
    S.residualTateGenerators_step L hline hcofixed hζ hp5 hclass hbad⟩⟩,
    fun n => (gen n).property⟩

/-- 構成した点列は非零。第0成分で実際に検出する。 -/
theorem residualCyclicTateVector_ne_zero :
    S.residualCyclicTateVector L hline hcofixed hζ hp5 hclass hbad ≠ 0 := by
  intro h
  apply S.residualTateSeed_ne_zero L hline hcofixed hζ hp5 hclass hbad
  apply Subtype.ext
  exact congrArg (fun x : line => evaluation 0 x.val) h

/-- 一つの互換生成元点列の固定性が、元の p 進指標値1を正確に検出する。 -/
theorem residualCyclicTateVector_fixed_iff (σ : Field.absoluteGaloisGroup ℚ) :
    action S.residualPointActionHom σ
      (S.residualCyclicTateVector L hline hcofixed hζ hp5 hclass hbad).val =
      (S.residualCyclicTateVector L hline hcofixed hζ hp5 hclass hbad).val ↔ padicChar σ = 1 := by
  rw [S.residualPadicTowerCharacter_eq_one_iff L hline hcofixed hζ hp5 hclass hbad]
  constructor
  · intro h x hx
    obtain ⟨n, hn⟩ := (S.mem_residualCyclicTowerUnion L hline hcofixed hζ hp5 hclass hbad x).mp hx
    rw [← S.residualTateGenerators_generate L hline hcofixed hζ hp5 hclass hbad n] at hn
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hn
    have he : pointAction S.rationalCurve σ (gen n).val = (gen n).val :=
      congrArg (evaluation n) h
    rw [map_zsmul, he]
  · intro h
    apply PrimePowerTateSequence.ext
    intro n
    exact h (gen n).val
      ((S.mem_residualCyclicTowerUnion L hline hcofixed hζ hp5 hclass hbad _).mpr ⟨n, (gen n).property⟩)

/-- 同じ良還元 Frobenius は、構成した一つの Tate 生成元点列を実際に動かす。
この非固定性は矛盾ではなく、以前の非自明な指標の点列上の実現である。 -/
theorem residualCyclicTateVector_frobenius_moved
    {ell : ℕ} (hell : ell.Prime) (hellp : ell ≠ p) (hgood : ¬ (ell : ℤ) ∣ S.curve.Δ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : ValuationInertia.LiesOverPrime A ell)
    (σ : Field.absoluteGaloisGroup ℚ) (hσ : ValuationFrobenius.IsFrobeniusAt A σ ell) :
    action S.residualPointActionHom σ
      (S.residualCyclicTateVector L hline hcofixed hζ hp5 hclass hbad).val ≠
      (S.residualCyclicTateVector L hline hcofixed hζ hp5 hclass hbad).val := by
  intro h
  exact S.residualPadicTowerCharacter_frobenius_ne_one L hline hcofixed hζ hp5 hclass hbad
    hell hellp hgood A hA σ hσ
    ((S.residualCyclicTateVector_fixed_iff L hline hcofixed hζ hp5 hclass hbad σ).mp h)

end
end DkMath.FLT.Frey.Source
```

## 回帰例と監査

`DkMathTest.FLT.FreyCyclicTateVector` は、有限加法群 ZMod 25 の5進 Tate 点列が零になることを確認する。
互換性を二度使うと xₙ=25•xₙ₊₂ となり、右辺は0である。
有限段の非零点を、そのまま非零の互換無限点列と取り違えない検査である。

同じ抽象 Source と同じ算術条件付き塔では、次を確認する。

- 第2点は同じ第0生成元の p² 倍逆像で、実際の位数が p³。
- 点列の第2成分は依存再帰で選んだ同じ第2生成元。
- 同じ塔の包含で全点群の Tate 点列へ移しても非零。

元の群の単射が点列上でも単射になることも確認する。
不可能な数値の Fermat Source を作って回帰例とすることはしない。

主要12宣言の公理報告と、型・構成子・不透明証明本体を含む再帰依存監査を追加する。
10件の公開入力監査では、同じ hclass と全段 hbad を保持し、
hgen/hnext/hvector/hnonzero/hfixed/hchar/hmoved を新たな provider として要求しないことを確認する。

教科書2ブロックの全文一致・個別コンパイル、Lib/FLT/root の公開、通常テスト入口、
root smoke とソース検査も行う。
記録：`evidence/validation-note032-frey-tate-vector.txt`。

## 残る数学

- 同じ円分類群商の特定 ω² 成分の消滅 hclass。
- 全段の共鳴素点条件 hbad または反復に十分な保存性。
- 点列群上の標準 ℤₚ 加群構造、互換生成元による階数1線形同型と scalar 作用公式。
- 合併 U の捩れから定義する Tₚ(U) との明示的な同定。
- Tₚ(E) の階数2・Weil pairing・実際の Frobenius 特性多項式と最終矛盾の算術。

**今回の2ステップは、加法的な実際の Tate 点列と同じ互換生成元の構成として完成。**
**一般 hno は引き続き未完成である。**
既存の DkMath の同じ次段内 p 倍逆像・零化・Galois 作用・p 進指標と、
Mathlib の元の位数・生成部分群の濃度を使う。外部の深い分類定理は追加していない。
