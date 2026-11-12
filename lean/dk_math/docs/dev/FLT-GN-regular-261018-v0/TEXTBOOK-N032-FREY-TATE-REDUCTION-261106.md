# NOTE-032 教科書：Tate 加群 mod p の完全性と同じ残余直線

日付：2026-11-06。前段：`TEXTBOOK-N032-FREY-TATE-UNION-261106.md`。

今回の3ステップは、①第0評価の核と p 倍像、②実際の楕円曲線の mod p Tate 商、
③同じ Frey Tate 直線の飽和性と元の残余直線への還元である。
以下の3つの Lean ブロックは production ファイルの全文である。
順に配置し、import 直後の正確な `#print "file: …"` を保持する。

## ステップ1：第0成分への写像と p 倍像の完全性

前回の Tate p G は、p^(n+1)•xₙ=0 と p•xₙ₊₁=xₙ を満たす同じ群 G の点列である。
第0成分を評価すると、元の同じ G[p]=ker(p:G→G) の点になる。

    reduction : Tate p G →+ G[p].

互換性を繰り返して pⁿ•xₙ=x₀ を証明する。
x₀=0 なら、点列を一段ずらした wₙ=xₙ₊₁ も適切な p 冪で消える。
従って w は Tate 点列であり、p•w=x となる。
逆に p 倍点列の第0成分は、元の第0点の p 零化により0である。

    range(p:Tate p G→Tate p G)=ker(reduction).

また p•x=p•y なら、第 n+1 成分を比較して xₙ=yₙ が得られるので、p 倍写像は単射である。
第0評価そのものが単射であるとは主張しない。

### 第0評価の全射性には実際の p 倍全射性が必要

G の p 倍写像が全射なら、a∈G[p] を始点に、同じ直前の点の p 倍逆像を順に選ぶ。
依存再帰で得た点列は互換で、第 n 点は p^(n+1) で消える。
これが a の第0評価による実際の逆像になる。

核の等式と全射性から、

    Tate p G / p(Tate p G) ≃+ G[p]

を第一同型定理で構成する。
この汎用加法群論は p の素数性を必要としない。
p 倍全射性 hdiv は、全射性と商同型では正確に保持する。
前段までの標準 ℤₚ scalar がある素数 p の場合、自然数 p 倍と scalar p 倍は同じ作用である。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Algebra.PrimePowerTateModule
import Mathlib.GroupTheory.QuotientGroup.Basic

#print "file: DkMath.Lib.Algebra.PrimePowerTateReduction"

/-!
# 標準 Tate 加群の第0成分と p 倍像

第0成分が零なら一段ずらした点列が p 倍逆像になる。
元の群の p 倍全射性があれば、実際の互換逆像列から第0評価の全射性も得る。
-/
namespace DkMath.Lib.Algebra.PrimePowerTateSequence
noncomputable section
variable {p : ℕ} {G : Type*} [AddCommGroup G]

/-- 第 n 成分の p^n 倍は、元の同じ第0成分。 -/
theorem evaluation_to_zero (x : Tate p G) (n : ℕ) :
    p ^ n • evaluation n x = evaluation 0 x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_nsmul', compatible, ih]

/-- 同じ点群の p 捩れへの第0評価。 -/
def reduction : Tate p G →+ (nsmulAddMonoidHom p : G →+ G).ker where
  toFun x := ⟨evaluation 0 x, by
    change p • evaluation 0 x = 0
    simpa only [Nat.zero_add, pow_one] using killed x 0⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- 第0成分が零なら、同じ点列を一段ずらすことができる。 -/
def shiftOfZero (x : Tate p G) (hx : reduction x = 0) : Tate p G :=
  ⟨fun n => evaluation (n + 1) x,
    ⟨fun n => (evaluation_to_zero x (n + 1)).trans (congrArg Subtype.val hx),
      fun n => compatible x (n + 1)⟩⟩

/-- 一段ずらした点列の実際の p 倍は元の点列。 -/
theorem nsmul_shiftOfZero (x : Tate p G) (hx : reduction x = 0) :
    p • shiftOfZero x hx = x := by
  apply ext; intro n
  change p • evaluation (n + 1) x = evaluation n x
  exact compatible x n

/-- 全 Tate 点列の p 倍写像は単射。第0成分だけの単射性ではない。 -/
theorem nsmul_injective : Function.Injective (nsmulAddMonoidHom p : Tate p G →+ Tate p G) := by
  intro x y h
  apply ext; intro n
  have he := congrArg (evaluation (n + 1)) h
  change p • evaluation (n + 1) x = p • evaluation (n + 1) y at he
  simpa only [compatible] using he

/-- 第0評価の核は同じ Tate 加群内の p 倍像。 -/
theorem range_nsmul_eq_reduction_ker :
    (nsmulAddMonoidHom p : Tate p G →+ Tate p G).range = (reduction (p := p) (G := G)).ker := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    apply Subtype.ext
    change p • evaluation 0 x = 0
    simpa only [Nat.zero_add, pow_one] using killed x 0
  · intro x hx
    exact ⟨shiftOfZero x hx, nsmul_shiftOfZero x hx⟩

variable (hdiv : Function.Surjective (nsmulAddMonoidHom p : G →+ G))

/-- 同じ群内の p 倍逆像を直前の点から順に選ぶ。 -/
def divisionSequence (a : (nsmulAddMonoidHom p : G →+ G).ker) : ℕ → G :=
  Nat.rec a.val (fun _ x => (hdiv x).choose)

theorem divisionSequence_step (a : (nsmulAddMonoidHom p : G →+ G).ker) (n : ℕ) :
    p • divisionSequence hdiv a (n + 1) = divisionSequence hdiv a n :=
  (hdiv (divisionSequence hdiv a n)).choose_spec

/-- 選んだ互換逆像は正確な段の p 冪で消える。 -/
theorem divisionSequence_killed (a : (nsmulAddMonoidHom p : G →+ G).ker) (n : ℕ) :
    p ^ (n + 1) • divisionSequence hdiv a n = 0 := by
  induction n with
  | zero =>
    change p ^ (0 + 1) • a.val = 0
    rw [Nat.zero_add, pow_one]
    exact a.property
  | succ n ih => rw [pow_succ, mul_nsmul', divisionSequence_step, ih]

include hdiv in
/-- p 倍全射性から、第0評価の全射性を実際の点列で証明する。 -/
theorem reduction_surjective : Function.Surjective (reduction (p := p) (G := G)) := by
  intro a
  exact ⟨⟨divisionSequence hdiv a, ⟨divisionSequence_killed hdiv a, divisionSequence_step hdiv a⟩⟩, rfl⟩

/-- 標準 Tate 加群の p 倍による商は、元の群の p 捩れと自然に加法同型。 -/
def quotientEquiv :
    Tate p G ⧸ (nsmulAddMonoidHom p : Tate p G →+ Tate p G).range ≃+
      (nsmulAddMonoidHom p : G →+ G).ker := by
  rw [range_nsmul_eq_reduction_ker]
  exact QuotientAddGroup.quotientKerEquivOfSurjective _ (reduction_surjective hdiv)

end
end DkMath.Lib.Algebra.PrimePowerTateSequence
```

## ステップ2：同じ楕円曲線の実際の E[p] へ接続する

標数0の体 K 上の同じ楕円曲線 E を取り、G=E(algClosure K) とする。
既存の `multiplication_surjective` は、この実際の点群で p 倍写像が全射であることを証明している。
素数 p の非零性を供給してステップ1へ渡すことで、

    tateReduction_surjective

を追加の hdiv/hlift provider なしで得る。
第0評価は既存の `Torsion E p`、すなわち同じ p 倍核への写像であり、元の点を変えない。
元の実際の Galois 点作用との可換性も証明する。

### 商の標準 ZMod p 線形構造

p 倍像による商は p で消える。その標準 ZMod p 加群構造を定義する。
商と同じ E[p] の加法同型は、自然数・整数倍を保つので標準 ZMod p 作用に関して線形となる。

    tateModPLinearEquiv : TateModP E p ≃ₗ[ZMod p] Torsion E p.

既存の実際の E[p] の濃度 p² と次元2を、この線形同型で商へ戻す。

    Nat.card (TateModP E p)=p²,
    finrank (ZMod p) (TateModP E p)=2.

**これは実際の商 Tate p E / p(Tate p E) の次元2である。**
全 Tate 加群の自由階数2や基底の存在を仮定・証明したものではない。
有限段の点群と無限点列の商を、評価写像の核と全射性で接続した結果である。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Algebra.PrimePowerTateReduction
import DkMath.Lib.NumberTheory.EllipticTorsionAllCard

#print "file: DkMath.Lib.NumberTheory.EllipticTateReduction"

/-!
# 同じ楕円曲線の標準 Tate 加群 mod p と実際の E[p]

幾何学的な倍写像全射性から第0評価の全射性を内部供給する。
核は p 倍像であり、商は実際の E[p] と ZMod p 線形同型になる。
この mod p の次元2は全 Tate 加群の自由階数2とは区別する。
-/
namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open DkMath.Lib.Algebra.PrimePowerTateSequence
noncomputable section
variable {K : Type*} [Field K] (E : WeierstrassCurve K) (p : ℕ)

/-- 同じ全幾何学的 Tate 点列の第0評価。 -/
def tateReduction : Tate p (Points E) →+ Torsion E p := reduction

/-- p 倍による実際の商。p 進 scalar p 倍と自然数 p 倍は同じ。 -/
abbrev TateModP := Tate p (Points E) ⧸ (nsmulAddMonoidHom p : Tate p (Points E) →+ Tate p (Points E)).range

instance tateModPModule : Module (ZMod p) (TateModP E p) :=
  QuotientAddGroup.zmodModule (fun x => ⟨x, rfl⟩)

/-- 第0評価は元の同じ Galois 点作用と可換する。 -/
theorem tateReduction_equivariant [Fact p.Prime] (σ : Field.absoluteGaloisGroup K)
    (x : Tate p (Points E)) :
    tateReduction E p (mapLinear (pointAction E σ) x) = representation E p σ (tateReduction E p x) := rfl

variable [CharZero K] [E.IsElliptic] [Fact p.Prime]

/-- 実際の点の p 倍全射性から、互換点列を作って評価の全射性を得る。 -/
theorem tateReduction_surjective : Function.Surjective (tateReduction E p) :=
  reduction_surjective (multiplication_surjective E p (Fact.out : p.Prime).ne_zero)

/-- 商は同じ点を評価して得た実際の E[p] と加法同型。 -/
def tateModPEquiv : TateModP E p ≃+ Torsion E p :=
  quotientEquiv (multiplication_surjective E p (Fact.out : p.Prime).ne_zero)

/-- p で消える商の標準 ZMod p 作用のもとで、同じ加法同型は線形となる。 -/
def tateModPLinearEquiv : TateModP E p ≃ₗ[ZMod p] Torsion E p :=
  (tateModPEquiv E p).toLinearEquiv (fun c x => ZMod.map_smul (tateModPEquiv E p) c x)

/-- 実際の mod p 商の濃度は p²。全 Tate 加群の濃度ではない。 -/
theorem tateModP_card : Nat.card (TateModP E p) = p ^ 2 :=
  (Nat.card_congr (tateModPEquiv E p).toEquiv).trans (card_torsion_prime_sq E p)

/-- 実際の mod p 商は二次元。全 Tate 加群の自由性を仮定しない。 -/
theorem tateModP_finrank : Module.finrank (ZMod p) (TateModP E p) = 2 :=
  (tateModPLinearEquiv E p).finrank_eq.trans (finrank_torsion_prime E p)

end
end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
```

## ステップ3：同じ Frey 直線の飽和性と元の L

同じ Source、残余直線 L、rootField、hclass、全段 hbad を保持する。
既存の同じ Tate 直線を C と書く。
全 Tate 加群の mod p 商の次元2は、同じ曲線の楕円曲線性から内部供給する。
この全加群の結論には hclass/hbad は必要ない。

### p に関する飽和性

p•x が C に属するとする。
第 n+1 成分から p•xₙ₊₁∈Kₙ₊₁ を得るが、互換性によりこれは xₙ∈Kₙ₊₁ である。
xₙ は p^(n+1) で消えるので、前回の同じ二段の低位捩れ判定から xₙ∈Kₙ となる。
全ての n で成立するので x∈C である。
逆向きは部分群の自然数倍への閉性から従う。

    p•x∈C ↔ x∈C.

これは全 Tate 加群の自由性を仮定しない、同じ有限段と遷移による p 飽和性である。

### 直線の還元は元の同じ残余直線へ戻る

C の第0成分は同じ K₀=pointSubgroup(E,p,L) に属する。
点群への torsion 包含の単射性により、E[p] のその同じ点は L に属する。
従って第0評価を

    residualTateLineReduction : C →+ L

へ制限できる。全 Tate 加群の第0評価との包含図式は、元の同じ点を返す。

元の L の任意の点 q を持ち上げるため、同じ合併 U の既存の p 可除性を使う。
U の実際の群型で p 倍全射性を得て、ステップ1の互換逆像列を同じ U 内で構成する。
前回の Tate p U と C の自然な同型で戻せば、第0成分が q の同じ C の点列を得る。
新たな持ち上げ・全射性 provider は要求しない。

還元が零の x∈C に対し、全 Tate 加群内のシフト逆像 w を取ると p•w=x である。
今回の p 飽和性から w∈C が従う。従って C 自身でも

    range(p:C→C)=ker(C→L)

が成立する。
標準の ZMod p 加群構造を持つ商について第一同型定理を適用し、

    residualTateLineModPLinearEquiv : C/pC ≃ₗ[ZMod p] L

を構成する。以前の hline により、この実際の直線の mod p 商の次元は1となる。

今回で、全加群の mod p 商は同じ E[p] に、同じ直線の mod p 商は元の同じ L に戻る。
新しい残余直線を別に選んでいるのではない。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclicTateUnion
import DkMath.Lib.NumberTheory.EllipticTateReduction

#print "file: DkMath.FLT.FreyCyclicTateReduction"

/-!
# 同じ Tate 直線の p 飽和性と元の残余直線

全 Tate 加群 mod p は実際の E[p]、直線 mod p は元の同じ L に戻る。
全 Tate 加群の自由階数2・基底拡張・最終 hno はまだ証明しない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.Algebra DkMath.Lib.NumberTheory
open EllipticTorsionRepresentation DkMath.Lib.RepresentationTheory PrimePowerTateSequence
noncomputable section

section Ambient
variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic

/-- 同じ Frey 全 Tate 加群の mod p 商の実際の次元は2。 -/
theorem residualTateModP_finrank : Module.finrank (ZMod p) (TateModP S.rationalCurve p) = 2 :=
  tateModP_finrank S.rationalCurve p
end Ambient

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

/-- 同じ直線は全 Tate 加群内で p に関して飽和している。 -/
theorem residualCyclicTateLine_p_saturated (x : Tate p (Points S.rationalCurve)) :
    p • x ∈ line ↔ x ∈ line := by
  constructor
  · intro hx n
    have hh := hx (n + 1)
    change p • evaluation (n + 1) x ∈ (tower (n + 1)).carrier at hh
    rw [compatible] at hh
    exact ((tower n).mem_iff_killed_in_later (tower (n + 1)) (Nat.le_succ n)
      (S.residualCyclicTower_step L hline hcofixed hζ hp5 hclass hbad n).1 _).mpr ⟨hh, killed x n⟩
  · intro hx n
    change p • evaluation n x ∈ (tower n).carrier
    exact (tower n).carrier.nsmul_mem (hx n) p

/-- 第0評価を元の同じ残余直線 L へ戻す自然な加法写像。 -/
def residualTateLineReduction : line →+ L where
  toFun x := ⟨tateReduction S.rationalCurve p x.val, by
    have hx : evaluation 0 x.val ∈ pointSubgroup S.rationalCurve p L := x.property 0
    obtain ⟨q, hq, he⟩ := hx
    have heq : q = tateReduction S.rationalCurve p x.val := Subtype.ext he
    exact heq ▸ hq⟩
  map_zero' := rfl
  map_add' _ _ := rfl

local notation "red" => S.residualTateLineReduction L hline hcofixed hζ hp5 hclass hbad

/-- 同じ U の実際の可除性を、その部分群型の p 倍全射性として公開する。 -/
theorem residualTowerUnion_nsmul_surjective :
    Function.Surjective (nsmulAddMonoidHom p : (union) →+ (union)) := by
  intro x
  obtain ⟨y, hy, he⟩ := S.residualCyclicTowerUnion_divisible L hline hcofixed hζ hp5 hclass hbad x.val x.property
  exact ⟨⟨y, hy⟩, Subtype.ext he⟩

/-- 元の L の点は同じ U 内の互換逆像列で持ち上がり、第0評価は L 上に全射。 -/
theorem residualTateLineReduction_surjective : Function.Surjective red := by
  intro q
  have hq : q.val.val ∈ union :=
    (S.mem_residualCyclicTowerUnion L hline hcofixed hζ hp5 hclass hbad _).mpr
      ⟨0, ⟨q.val, q.property, rfl⟩⟩
  let a : (nsmulAddMonoidHom p : (union) →+ (union)).ker :=
    ⟨⟨q.val.val, hq⟩, Subtype.ext q.val.property⟩
  obtain ⟨t, ht⟩ := reduction_surjective
    (S.residualTowerUnion_nsmul_surjective L hline hcofixed hζ hp5 hclass hbad) a
  refine ⟨S.residualUnionTateLineEquiv L hline hcofixed hζ hp5 hclass hbad t, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : (nsmulAddMonoidHom p : (union) →+ (union)).ker => z.val.val) ht

/-- 直線内の第0評価の核も、その直線自身の p 倍像である。
全加群の逆像が同じ直線へ戻ることを飽和性で保証する。 -/
theorem residualTateLineReduction_ker :
    (nsmulAddMonoidHom p : (line) →+ (line)).range = (red).ker := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    apply Subtype.ext
    apply Subtype.ext
    change p • evaluation 0 x.val = 0
    simpa only [Nat.zero_add, pow_one] using killed x.val 0
  · intro x hx
    have hx0 : reduction x.val = 0 := Subtype.ext (congrArg (fun z : L => z.val.val) hx)
    let w := shiftOfZero x.val hx0
    have hw : w ∈ line := (S.residualCyclicTateLine_p_saturated L hline hcofixed hζ hp5 hclass hbad w).mp
      (by rw [nsmul_shiftOfZero]; exact x.property)
    exact ⟨⟨w, hw⟩, Subtype.ext (nsmul_shiftOfZero x.val hx0)⟩

/-- 直線自身の実際の p 倍による商。 -/
abbrev ResidualTateLineModP := (line) ⧸ (nsmulAddMonoidHom p : (line) →+ (line)).range

local notation "lineModP" => S.ResidualTateLineModP L hline hcofixed hζ hp5 hclass hbad

instance residualTateLineModPModule : Module (ZMod p) lineModP :=
  QuotientAddGroup.zmodModule (fun x => ⟨x, rfl⟩)

/-- 同じ第0評価が与える、実際の直線 mod p と元の L の加法同型。 -/
def residualTateLineModPEquiv : lineModP ≃+ L := by
  change ((line) ⧸ (nsmulAddMonoidHom p : (line) →+ (line)).range) ≃+ L
  rw [S.residualTateLineReduction_ker L hline hcofixed hζ hp5 hclass hbad]
  exact QuotientAddGroup.quotientKerEquivOfSurjective red
    (S.residualTateLineReduction_surjective L hline hcofixed hζ hp5 hclass hbad)

/-- p で消える商の標準 scalar のもとで、この自然な同定は ZMod p 線形。 -/
def residualTateLineModPLinearEquiv : lineModP ≃ₗ[ZMod p] L :=
  (S.residualTateLineModPEquiv L hline hcofixed hζ hp5 hclass hbad).toLinearEquiv
    (fun c x => ZMod.map_smul (S.residualTateLineModPEquiv L hline hcofixed hζ hp5 hclass hbad) c x)

/-- 同じ直線の mod p 商の実際の次元は1。 -/
theorem residualTateLineModP_finrank : Module.finrank (ZMod p) lineModP = 1 :=
  (S.residualTateLineModPLinearEquiv L hline hcofixed hζ hp5 hclass hbad).finrank_eq.trans hline

/-- 直線の還元と全 Tate 加群の還元は同じ E[p] の点を返す。 -/
theorem residualTateLineReduction_inclusion (x : line) :
    (red x).val = tateReduction S.rationalCurve p x.val := rfl

end
end DkMath.FLT.Frey.Source
```

## 回帰例と監査

`DkMathTest.FLT.FreyCyclicTateReduction` は、有限群 ZMod 25 の5進 Tate 点列が零となることを確認する。
一方、実際の5捩れ点5は非零であり、その第0評価への逆像は存在しない。
これにより第0評価の全射性から hdiv を落とす誤用を防ぐ。
任意の第0成分が零の点列について、実際の一段シフトが5倍逆像となることも確認する。

同じ Frey 曲線の任意の残余点を全 Tate 加群へ持ち上げる回帰例は、hclass/hbad を追加要求しない。
同じ条件付き直線では、任意の L の点を商同型で往復して回収し、
p²•x∈C から飽和性を二度使って同じ x∈C を導く。
直線と全加群の還元が同じ幾何学的 p 捩れ点を返すことも確認する。

主要15宣言の公理報告・型／構成子／不透明証明本体を含む再帰依存監査、12件の公開入力監査を追加する。
汎用全射性では hdiv を保持し、楕円曲線で実際に供給し、Frey 直線では同じ U の既存可除性から供給する。
hfree/hrank/hker/hsurj/hlift/hsat/hequiv を新たな provider として追加しない。
同じ直線の hclass と全段 hbad は従来どおり保持する。

3 production の Lib/FLT/root 公開、通常テスト入口、root smoke、教科書3ブロックの全文一致・個別コンパイルも確認する。
記録：`evidence/validation-note032-frey-tate-reduction.txt`。

## 残る境界

- 同じ円分類群商の特定 ω² 成分の消滅 hclass。
- 全段の共鳴素点条件 hbad または反復に十分な保存性。
- 全 Tate 加群の自由階数2、原始元の基底への拡張、二次元基底での上三角表示。
- 高位 Weil pairing、Frobenius 特性多項式、最終矛盾の局所・大域算術。

今回の次元2は全 Tate 加群の **mod p 商** の定理である。
p 倍の単射性・評価の完全性・実際の同じ還元を証明したが、Nakayama や完備性から自由性を導く議論は追加していない。
点列群の位相も今回新たに構成していない。
**今回の3ステップは完成。一般 hno は引き続き未完成である。**
外部の消滅定理・イソジェニー分類を追加せず、既存の実際の倍写像全射性・有限捩れ次元・
同じ塔の可除性と低位捩れ判定、Mathlib の商群の第一同型定理を使う。
