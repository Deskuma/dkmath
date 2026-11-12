# NOTE-032 教科書：算術条件付き分裂から同じ巡回捩れ塔へ

日付：2026-11-06。前段：`TEXTBOOK-N032-CYCLOTOMIC-UNIT-CLOSURE-261106.md`。
今回の2ステップは、①証明済みの単元算術を使う条件付き大域分裂から実際の巡回次段を構成、
②その次段を同じ底のもとで反復し、同じ点群内の塔と合併を構成することである。
**hclass と各段の hbad は明示入力に残る。一般 hno の完成ではない。**

以下の2つの Lean ブロックは production ファイルの全文である。
順にモジュールとして配置し、個別にコピーしてコンパイルできる。
ファイルの同定に必須の import 直後の `#print "file: …"` は省略しない。

## 今回の対象選択

最新レビューでは、類群 hclass、共鳴素点 hbad、塔の反復を分離することが提案された。
外部 source の特定 ω² 類群消滅は、Thaine 関係と非分裂次数1素イデアルの生成性を使う。
それを一般のプラス部分全体の消滅へ広げたり、別の消滅定理を仮定して済ませたりしない。
今回は、算術条件を明示して残したまま、完成した単元算術を本当の次段・塔へ接続する。
外部類群経路の source 照合範囲は evidence の JSON に記録する。

## ステップ1：同じ点群内の実際の巡回段

S と元の残余直線 L を固定し、B=pointSubgroup S.rationalCurve p L とする。
段 `ResidualCyclicStage S L n` は **同じ** Points S.rationalCurve 内の部分群 Kₙ を持ち、
次の不変量を保持する。

- #Kₙ=p^(n+1)。第0段は位数 p の元の B。
- Kₙ は巡回群。
- Kₙ は同じ絶対 Galois 作用で安定。
- 同じ B が Kₙ に含まれる。

S 自体や三つ組・正規化・gcd データを取り替えず、すべて同じ Source に添字を付ける。
有限性は位数が非零であることから、指数 p^(n+1) による零化は Lagrange の定理から導く。
同じ B への p-socle の降下も、既存の有限巡回群の濃度から証明する。
それらを追加 provider として入力しない。

### 次段の構成

ある段 T の carrier=K に対して、以前と同じ hbad と同じ hclass を与える。
証明済みの単元消滅を内部供給する Frey 分裂定理を呼び、
同じ商 (p⁻¹K)/K の同じ torsionImage に対する大域安定な補空間 D を得る。
その具体的な商部分空間の逆像から、元の点群の中に次段 K′ を作る。

既存の `exists_tower_step_of_stable_complement` が、位数 p^(n+2)、巡回性、
Galois 安定性、K⊆K′、K′[p]⊆K を実際に証明する。
同じ B⊆K と K⊆K′ を合成して、次段でも同じ B を保持する。

`residual_cyclic_stage_successor` は安定補空間・指標消滅・次段の存在を入力しない。
公開入力は元の L の一次元性・Cofixed 性、同じ原始根、p≥5、段 T、hbad、hclass である。

### hbad の正確な強さ

`ResonantAbsorptionAt K` は、以前の hbad と同じ

    p • y∈K ⇒ τ(y)−y∈K

という共鳴する悪い素点の慣性条件である。
これを「任意の高位捩れ y が吸収される」という条件へ変更していない。
名前を付けても算術的な証明を与えたことにはならず、その真偽は依然として入力である。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclotomicUnitSplit

#print "file: DkMath.FLT.FreyCyclotomicTowerStep"

/-!
# 算術条件付き分裂から、同じ点群の実際の巡回次段へ

段の不変量は位数 p^(n+1)、巡回性、全 Galois 安定性、同じ底の包含である。
有限性と捩れ指数と socle の底への降下はこれらから導く。
分裂や次段の存在を入力せず、既存の実際の hbad/hclass 付き分裂を呼び出す。
-/

namespace DkMath.FLT.Frey.Source

open DkMath.Lib.Algebra DkMath.Lib.NumberTheory
open EllipticTorsionRepresentation CyclotomicRootModule CyclotomicKernelField
open CyclotomicKummerWeight
open DkMath.Lib.RepresentationTheory
noncomputable section

variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic

/-- 同じ Source と同じ残余直線を保つ、位数 p^(n+1) の実際の巡回段。 -/
structure ResidualCyclicStage (L : Submodule (ZMod p) S.ResidualSpace) (n : ℕ) where
  carrier : AddSubgroup (Points S.rationalCurve)
  card : Nat.card carrier = p ^ (n + 1)
  cyclic : IsAddCyclic carrier
  stable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ carrier, pointAction S.rationalCurve σ x ∈ carrier
  base : pointSubgroup S.rationalCurve p L ≤ carrier

variable {S} {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ}

/-- 位数から有限性を導き、有限性 provider を段データへ追加しない。 -/
theorem ResidualCyclicStage.finite (T : S.ResidualCyclicStage L n) : Finite T.carrier :=
  Nat.finite_of_card_ne_zero (T.card ▸ pow_ne_zero _ (Fact.out : p.Prime).ne_zero)

/-- 同じ位数の段は、その同じ p^(n+1) 倍で消える。 -/
theorem ResidualCyclicStage.killed (T : S.ResidualCyclicStage L n)
    (x : Points S.rationalCurve) (hx : x ∈ T.carrier) : p ^ (n + 1) • x = 0 := by
  let := T.finite
  exact congrArg (fun z : T.carrier => z.val)
    (T.card ▸ card_nsmul_eq_zero' (x := (⟨x, hx⟩ : T.carrier)))

/-- 元の一次元の底が、どの段の p 捩れも受け取る。 -/
theorem ResidualCyclicStage.socle_mem_base (T : S.ResidualCyclicStage L n)
    (hline : Module.finrank (ZMod p) L = 1)
    {x : Points S.rationalCurve} (hx : x ∈ T.carrier) (hpx : p • x = 0) :
    x ∈ pointSubgroup S.rationalCurve p L := by
  let := T.finite
  let := T.cyclic
  exact S.residual_cyclic_tower_socle_mem_base L hline T.carrier (by omega) T.card T.base hx hpx

variable (S)

/-- 同じ底を第0段として内部構成する。非零点や段の存在を入力しない。 -/
def residualCyclicStageZero (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L) : S.ResidualCyclicStage L 0 where
  carrier := pointSubgroup S.rationalCurve p L
  card := by simpa only [zero_add, pow_one] using card_pointSubgroup S.rationalCurve p L hline
  cyclic := isAddCyclic_pointSubgroup S.rationalCurve p L hline
  stable := pointSubgroup_stable S.rationalCurve p L hcofixed.isStable
  base := le_rfl

/-- 既存の hbad と同じ慣性条件。p•y∈K を全 p 冪捩れ条件へ勝手に拡張しない。 -/
def ResonantAbsorptionAt (K : AddSubgroup (Points S.rationalCurve)) : Prop :=
  ∀ q : ℕ, q.Prime → q ≠ p → 5 ≤ q → (q : ℤ) ∣ S.a * S.b * S.c →
    ((q : ZMod p) = 1 ∨ (q : ZMod p) = -1) →
    ∀ A : ValuationSubring (AlgebraicClosure ℚ), ValuationInertia.LiesOverPrime A q →
      ∀ τ ∈ ValuationInertia.inertiaSubgroupIn A ℚ, ∀ y : Points S.rationalCurve,
        p • y ∈ K → pointAction S.rationalCurve τ y - y ∈ K

variable (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)
local instance : NumberField (rootField ζ) := rootField_numberField ζ

include hline hcofixed in
/-- 同じ段の算術条件から、同じ点群内の実際の巡回次段を構成する。
次段の有限性・巡回性・位数・安定性・底の包含は出力であり、入力しない。 -/
theorem residual_cyclic_stage_successor (hp5 : 5 ≤ p) (T : S.ResidualCyclicStage L n)
    (hbad : S.ResonantAbsorptionAt T.carrier)
    (hclass : ∀ a : CyclotomicClassVanishing.ClassModP (rootField ζ) p,
      (∀ γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ),
        CyclotomicClassVanishing.classModPAction p γ a =
          (baseCharacter hζ γ : ZMod p) ^ 2 • a) → a = 0) :
    ∃ T' : S.ResidualCyclicStage L (n + 1), T.carrier ≤ T'.carrier ∧
      (∀ x ∈ T'.carrier, p • x = 0 → x ∈ T.carrier) := by
  let := T.finite
  let := T.cyclic
  obtain ⟨D, hcompl, hstable⟩ :=
    S.residual_cyclic_extension_has_stable_complement_of_class_vanishing
      L hline hcofixed T.carrier T.stable (by omega) T.card T.base hζ hp5 hbad hclass
  obtain ⟨J, hinc, hcard, hcyclic, _, hstableJ, hdown⟩ :=
    exists_tower_step_of_stable_complement S.rationalCurve T.carrier T.stable
      (by omega) T.card T.killed D hcompl hstable
  refine ⟨⟨J, hcard, hcyclic, hstableJ, T.base.trans hinc⟩, hinc, hdown⟩

end
end DkMath.FLT.Frey.Source
```

## ステップ2：依存再帰による同じ塔と合併

反復には、同じ原始根の同じ ClassModP の固有成分消滅 hclass を全段で使う。
hbad は `∀ n (T : ResidualCyclicStage S L n), ResonantAbsorptionAt S T.carrier` と明示する。
これは **一つの K に対する hbad より強い、各段で利用できる算術入力**である。
一段の仮定が帰納的に保存されると証明したわけではない。
次段の存在や分裂を仮定する provider ではなく、元の同じ慣性条件の段ごとの供給である。

`residualCyclicNext` は前章の次段定理から選択する。
`residualCyclicTower` は Nat.rec により

    T₀=元の B,    Tₙ₊₁=選択した Tₙ の次段

を依存再帰で定義する。各 n で無関係な部分群を選んだ列ではない。
`residualCyclicTower_step` が隣接段の包含と socle 降下を保持し、
`residualCyclicTower_monotone` が全体の単調性を証明する。
各段の正確な位数、巡回性、同じ作用の安定性、同じ底への包含、指数、socle は構成から従う。

### 互換な p 倍の逆像

Kₙ₊₁ は位数 p^(n+2) の有限巡回群なので、p 倍像は p^(n+1) 倍の核と一致する。
Kₙ の同じ点 x はこの核に入るため、同じ次段の y に対して p•y=x と書ける。
`residualCyclicTower_lift` はこの実際の点 y を返す。
単に別の可除群の存在を仮定したり、ポイントを同型で取り替えたりしていない。

### 同じ点群内の合併

U=⨆ₙKₙ と置く。塔が単調なので、x∈U は ∃n,x∈Kₙ と同値である。
これを使って次を証明する。

1. 各 x∈U は有限の p 冪で消える（p-primary）。
2. 各 x∈U は同じ U 内に p 倍の逆像を持つ（p-divisible）。
3. U は同じ絶対 Galois 作用で安定。
4. x∈U かつ p•x=0 は、x∈元の B と正確に同値。
5. U は無限。有限と仮定すると、増大する有限段の濃度が U の濃度を超えて矛盾する。

最後の議論では無限型の Nat.card=0 を有限濃度として扱わない。
有限段は非零濃度から Finite を供給し、合併は Infinite として結論する。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclotomicTowerStep

#print "file: DkMath.FLT.FreyCyclotomicConditionalTower"

/-!
# 同じ底を保つ実際の巡回捩れ塔の条件付き反復

既存の類群商消滅と、各段での同じ共鳴素点条件を明示入力に残す。
次段の存在は前章の算術分裂から内部供給し、選択した段を依存再帰でつなぐ。
同じ点群内の単調な塔・その合併の p-primary 性と socle を証明する。
高位捩れ全体の慣性吸収や一般 hno の証明とは区別する。
-/

namespace DkMath.FLT.Frey.Source

open DkMath.Lib.Algebra
open DkMath.Lib.NumberTheory EllipticTorsionRepresentation CyclotomicKernelField CyclotomicKummerWeight
open DkMath.Lib.RepresentationTheory
noncomputable section

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

/-- 次段を実際の算術分裂から選ぶ。分裂・次段の存在を別 provider として要求しない。 -/
def residualCyclicNext {n : ℕ} (T : S.ResidualCyclicStage L n) : S.ResidualCyclicStage L (n + 1) :=
  (S.residual_cyclic_stage_successor L hline hcofixed hζ hp5 T (hbad n T) hclass).choose

theorem residualCyclicNext_spec {n : ℕ} (T : S.ResidualCyclicStage L n) :
    T.carrier ≤ (S.residualCyclicNext L hline hcofixed hζ hp5 hclass hbad T).carrier ∧
      (∀ x ∈ (S.residualCyclicNext L hline hcofixed hζ hp5 hclass hbad T).carrier,
        p • x = 0 → x ∈ T.carrier) :=
  (S.residual_cyclic_stage_successor L hline hcofixed hζ hp5 T (hbad n T) hclass).choose_spec

/-- 同じ元の残余直線を底に、選んだ次段を実際に反復する依存再帰。 -/
def residualCyclicTower : (n : ℕ) → S.ResidualCyclicStage L n :=
  Nat.rec (S.residualCyclicStageZero L hline hcofixed)
    (fun _ T => S.residualCyclicNext L hline hcofixed hζ hp5 hclass hbad T)

local notation "tower" => S.residualCyclicTower L hline hcofixed hζ hp5 hclass hbad

/-- 第0段は元の同じ pointSubgroup。別の同型な底へ取り替えない。 -/
theorem residualCyclicTower_zero : (tower 0).carrier = pointSubgroup S.rationalCurve p L := rfl

/-- 同じ選択を使った隣接段の包含と p 捩れの降下。 -/
theorem residualCyclicTower_step (n : ℕ) :
    (tower n).carrier ≤ (tower (n + 1)).carrier ∧
      (∀ x ∈ (tower (n + 1)).carrier, p • x = 0 → x ∈ (tower n).carrier) :=
  S.residualCyclicNext_spec L hline hcofixed hζ hp5 hclass hbad (tower n)

/-- 各段で別々の存在を選んだだけではなく、単調な同じ塔である。 -/
theorem residualCyclicTower_monotone : Monotone (fun n => (tower n).carrier) :=
  monotone_nat_of_le_succ (fun n => (S.residualCyclicTower_step L hline hcofixed hζ hp5 hclass hbad n).1)

/-- 各段の濃度と巡回性・安定性・指数・底の包含はすべて構成から従う。 -/
theorem residualCyclicTower_profile (n : ℕ) :
    Nat.card (tower n).carrier = p ^ (n + 1) ∧ IsAddCyclic (tower n).carrier ∧
      (∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ (tower n).carrier,
        pointAction S.rationalCurve σ x ∈ (tower n).carrier) ∧
      pointSubgroup S.rationalCurve p L ≤ (tower n).carrier ∧
      (∀ x ∈ (tower n).carrier, p ^ (n + 1) • x = 0) ∧
      (∀ x ∈ (tower n).carrier, p • x = 0 → x ∈ pointSubgroup S.rationalCurve p L) :=
  ⟨(tower n).card, (tower n).cyclic, (tower n).stable, (tower n).base,
    (tower n).killed, fun _ hx hpx => (tower n).socle_mem_base hline hx hpx⟩

/-- 互いに無関係な段ではなく、同じ次段内に実際の p 乗根（加法では p 倍の逆像）がある。 -/
theorem residualCyclicTower_lift (n : ℕ) (x : Points S.rationalCurve) (hx : x ∈ (tower n).carrier) :
    ∃ y ∈ (tower (n + 1)).carrier, p • y = x := by
  let J := (tower (n + 1)).carrier
  let := (tower (n + 1)).finite
  let := (tower (n + 1)).cyclic
  have hxJ : x ∈ J := (S.residualCyclicTower_step L hline hcofixed hζ hp5 hclass hbad n).1 hx
  let z : J := ⟨x, hxJ⟩
  have hz : z ∈ (nsmulAddMonoidHom p : J →+ J).range := by
    rw [CyclicPrimePowerScalar.range_nsmul_eq_ker (Fact.out : p.Prime)
      (m := n + 1 + 1) (by omega) (tower (n + 1)).card]
    change p ^ (n + 1 + 1 - 1) • z = 0
    apply Subtype.ext
    change J.subtype (p ^ (n + 1 + 1 - 1) • z) = J.subtype 0
    rw [map_nsmul, map_zero]
    change p ^ (n + 1 + 1 - 1) • x = 0
    simpa only [show n + 1 + 1 - 1 = n + 1 from by omega] using (tower n).killed x hx
  obtain ⟨y, hy⟩ := hz
  exact ⟨y.val, y.property, congrArg (fun w : J => w.val) hy⟩

/-- 同じ幾何学的点群内の、構成した単調な塔の合併。 -/
def residualCyclicTowerUnion : AddSubgroup (Points S.rationalCurve) := ⨆ n, (tower n).carrier

local notation "towerUnion" => S.residualCyclicTowerUnion L hline hcofixed hζ hp5 hclass hbad

/-- 合併の元は実際にどこか一つの有限段に入る。 -/
theorem mem_residualCyclicTowerUnion (x : Points S.rationalCurve) :
    x ∈ towerUnion ↔ ∃ n, x ∈ (tower n).carrier := by
  apply AddSubgroup.mem_iSup_of_directed
  exact (S.residualCyclicTower_monotone L hline hcofixed hζ hp5 hclass hbad).directed_le

/-- 合併の各元は有限の p 冪で消える。高位捩れ全体を合併へ含める主張ではない。 -/
theorem residualCyclicTowerUnion_primary (x : Points S.rationalCurve) (hx : x ∈ towerUnion) :
    ∃ n, p ^ (n + 1) • x = 0 := by
  obtain ⟨n, hn⟩ := (S.mem_residualCyclicTowerUnion L hline hcofixed hζ hp5 hclass hbad x).mp hx
  exact ⟨n, (tower n).killed x hn⟩

/-- 構成した同じ合併は p 倍写像で可除。別の可除群を導入しない。 -/
theorem residualCyclicTowerUnion_divisible (x : Points S.rationalCurve) (hx : x ∈ towerUnion) :
    ∃ y ∈ towerUnion, p • y = x := by
  obtain ⟨n, hn⟩ := (S.mem_residualCyclicTowerUnion L hline hcofixed hζ hp5 hclass hbad x).mp hx
  obtain ⟨y, hy, he⟩ := S.residualCyclicTower_lift L hline hcofixed hζ hp5 hclass hbad n x hn
  exact ⟨y, (S.mem_residualCyclicTowerUnion L hline hcofixed hζ hp5 hclass hbad y).mpr ⟨n + 1, hy⟩, he⟩

/-- 同じ Galois 作用で合併全体も安定である。 -/
theorem residualCyclicTowerUnion_stable (σ : Field.absoluteGaloisGroup ℚ)
    (x : Points S.rationalCurve) (hx : x ∈ towerUnion) : pointAction S.rationalCurve σ x ∈ towerUnion := by
  obtain ⟨n, hn⟩ := (S.mem_residualCyclicTowerUnion L hline hcofixed hζ hp5 hclass hbad x).mp hx
  exact (S.mem_residualCyclicTowerUnion L hline hcofixed hζ hp5 hclass hbad _).mpr
    ⟨n, (tower n).stable σ x hn⟩

/-- 合併の p 捩れは、元の同じ底と正確に一致する。 -/
theorem residualCyclicTowerUnion_socle (x : Points S.rationalCurve) :
    (x ∈ towerUnion ∧ p • x = 0) ↔ x ∈ pointSubgroup S.rationalCurve p L := by
  constructor
  · rintro ⟨hx, hpx⟩
    obtain ⟨n, hn⟩ := (S.mem_residualCyclicTowerUnion L hline hcofixed hζ hp5 hclass hbad x).mp hx
    exact (tower n).socle_mem_base hline hn hpx
  · intro hx
    exact ⟨(S.mem_residualCyclicTowerUnion L hline hcofixed hζ hp5 hclass hbad x).mpr
      ⟨0, hx⟩, pointSubgroup_killed S.rationalCurve p L x hx⟩

/-- 濃度が無限に増大するので合併は無限。有限段ごとの Nat.card を混同しない。 -/
theorem residualCyclicTowerUnion_infinite : Infinite towerUnion := by
  by_contra h
  have : Finite towerUnion := not_infinite_iff_finite.mp h
  let N := Nat.card towerUnion
  let f : (tower N).carrier → towerUnion := fun x =>
    ⟨x.val, (S.mem_residualCyclicTowerUnion L hline hcofixed hζ hp5 hclass hbad x.val).mpr ⟨N, x.property⟩⟩
  have hf : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    exact congrArg (fun z : towerUnion => z.val) he
  have hle := Nat.card_le_card_of_injective f hf
  rw [(tower N).card] at hle
  have hlt : N < p ^ (N + 1) := lt_trans (Nat.lt_succ_self N) (Nat.lt_pow_self (Fact.out : p.Prime).one_lt)
  exact (not_le_of_gt hlt) hle

end
end DkMath.FLT.Frey.Source
```

## 回帰と検証範囲

`DkMathTest.FLT.FreyCyclotomicConditionalTower` は同じ Source・L を固定する。
第0段の構成に hbad/hclass が不要であること、同じ反復で最初の3段の位数が p,p²,p³ となることを確認する。
二つの実際の隣接段リフトを合成して、元の B の点に対する p² 倍の逆像が第2段にあることを確認する。
第4段の p 捩れも前段だけでなく元の B へ戻ることを確認する。
同じ合併の p-divisibility と socle の一致、Infinite と Nat.card=0 の同時成立も確認する。

Source は Frey–FLT の仮定を含むため、ここでは偽の具体的数値 Source を作らない。
回帰例も同じ hclass と各段の hbad を明示的に保持する。
主要15宣言の公理報告と再帰的な型・構成子・不透明証明本体の監査、公開入力監査を行う。
既存の実際の算術分裂・単元消滅・巡回判定・p 倍像の核公式へ依存することを確認する。
根拠のない「次段存在」や「指標消滅」の入力へ置き換えていない。

新規2 production を FLT/root、2 test を通常の DkMathTest 入口へ公開する。
教科書2ブロックの全文一致・個別コンパイル、正確なモジュール表示も別に検証する。
記録：`evidence/validation-note032-frey-conditional-tower.txt`。

## 閉じていないもの

- 実際の ClassModP の特定 ω² 成分消滅 hclass。
- 各段での共鳴素点の慣性吸収 hbad。
- 高位捩れ全体の慣性吸収を、今回の各段の p-preimage 条件から導くこと。
- 良還元点数による最終矛盾や一般 hno への残る大域接続。

合併 U が安定であることは、商上の Galois 作用が自明であることを意味しない。
U が p-primary であることは、全 E[p^n] が U に入るという主張ではない。
従ってこの構成だけで前段の Frobenius／良還元点数の最終矛盾の算術入力は消えない。
**今回の2ステップは条件付きの実際の塔構成として完成し、一般 hno は引き続き未完成である。**

## 類群経路の照合

ローカルの `anthropics/fermats-last-theorem` の
`S_ExtCitation_Cyclotomic_clGalAction_omegaEigenspace_two_eq_bot.lean` は、
Thaine 関係、非分裂次数1素イデアルによる類群生成性、円分単元の非零射影を経由する。
今回その数学を移植したり、外部の定理を import したりしていない。
そのため hclass を「プラス部分全体が零」のような強い目標へ取り替えず、
元の特定 ω² 商成分の命題のまま保持した。
外部 checkout のビルドや公理監査を実施したという主張はしない。
