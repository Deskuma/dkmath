# NOTE-032 教科書：互換有限基底から全 Frey Tate 基底へ

日付：2026-11-06。前段：`TEXTBOOK-N032-FREY-TATE-REDUCTION-261106.md`。

今回の3ステップは、①第0成分の生成性を各有限段へ持ち上げる群論、
②有限段の実際の同型と互換係数の復元による全 Tate 加群の二成分同型、
③元の同じ Frey 生成元を含む基底と、その基底での実際の Galois 作用行列である。

以下の3つの Lean ブロックは production ファイルの全文である。
順に配置し、import 直後の正確な `#print "file: …"` を保持する。

## ステップ1：第0段の生成性から有限全段の生成性へ

G を加法可換群、v,w を同じ Tate p G の互換点列とする。
第0成分が G[p] を自然数倍で生成する、すなわち

    p•x=0 → ∃ a b:ℕ, x=a•v₀+b•w₀

と仮定する。この入力 hbase は汎用補題の条件であり、後半の実際の Frey 適用で内部供給する。

任意の p^(n+1) 捩れ点 x が vₙ,wₙ で生成されることを n の帰納法で証明する。
初段は hbase そのものである。
次段では p^(n+1)•x は p で消えるため、第0点で展開できる。
Tate 互換性から p^(n+1)•vₙ₊₁=v₀、同様に w の等式があるので、

    y=x−a•vₙ₊₁−b•wₙ₊₁

は p^(n+1) で消える。帰納法で y=c•vₙ+d•wₙ と書く。
vₙ=p•vₙ₊₁、wₙ=p•wₙ₊₁ を使えば、

    x=(a+p*c)•vₙ₊₁+(b+p*d)•wₙ₊₁

となる。これは元の同じ群の点の構成である。
有限生成性・自由性・階数・Nakayama を仮定していない。p の素数性もこの群論には不要である。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Algebra.PrimePowerTateReduction
import Mathlib.Tactic.Abel

#print "file: DkMath.Lib.Algebra.PrimePowerTatePairSpan"

/-!
# 互換な二点の第0成分の生成性を全有限段へ持ち上げる

第 n 成分の p^n 倍を第0段で展開し、その差を一つ低い捩れ段へ戻す帰納法。
自由性・有限生成性・Nakayama を仮定しない実際の点の構成である。
-/
namespace DkMath.Lib.Algebra.PrimePowerTateSequence
variable {p : ℕ} {G : Type*} [AddCommGroup G] (v w : Tate p G)
    (hbase : ∀ x : G, p • x = 0 → ∃ a b : ℕ,
      x = a • evaluation 0 v + b • evaluation 0 w)

include hbase in
/-- 同じ二つの互換点列の成分が、各 p 冪捩れ段全体を生成する。 -/
theorem pair_span (n : ℕ) (x : G) (hx : p ^ (n + 1) • x = 0) :
    ∃ a b : ℕ, x = a • evaluation n v + b • evaluation n w := by
  induction n generalizing x with
  | zero =>
    apply hbase x
    simpa only [Nat.zero_add, pow_one] using hx
  | succ n ih =>
    have hk : p • (p ^ (n + 1) • x) = 0 := by
      rw [← mul_nsmul, ← pow_succ]
      exact hx
    obtain ⟨a, b, hab⟩ := hbase _ hk
    let y := x - a • evaluation (n + 1) v - b • evaluation (n + 1) w
    have hy : p ^ (n + 1) • y = 0 := by
      dsimp [y]
      rw [nsmul_sub, nsmul_sub, smul_comm (p ^ (n + 1)) a,
        smul_comm (p ^ (n + 1)) b, evaluation_to_zero, evaluation_to_zero, hab]
      abel
    obtain ⟨c, d, hcd⟩ := ih y hy
    refine ⟨a + p * c, b + p * d, ?_⟩
    calc
      x = y + a • evaluation (n + 1) v + b • evaluation (n + 1) w := by dsimp [y]; abel
      _ = (a + p * c) • evaluation (n + 1) v + (b + p * d) • evaluation (n + 1) w := by
        rw [hcd, add_nsmul, add_nsmul, mul_nsmul, mul_nsmul, compatible, compatible]
        abel

end DkMath.Lib.Algebra.PrimePowerTateSequence
```

## ステップ2：実際の楕円曲線の全 Tate 加群へ

同じ標数0楕円曲線 E と、同じ二つの Tate 点列 v,w を取る。
各 n で N=p^(n+1) とし、既存の標準 ZMod N 作用により

    fₙ:(ZMod N)×(ZMod N) →ₗ[ZMod N] E[N],
    fₙ(a,b)=a•vₙ+b•wₙ

を定義する。これは実際の捩れ点を返す写像である。
標準 scalar を元の点群の自然数倍として読む補題で評価公式を公開する。

### 有限段の全射と同型

ステップ1から、実際の任意の E[N] の点は vₙ,wₙ の自然数倍で表せる。
自然数係数を法 N へ落とすと、この標準線形写像の全射性を得る。

定義域の濃度は N² であり、既存の `card_torsion_sq` は同じ実際の E[N] の濃度も N² と証明している。
有限群の全射と同じ濃度から単射を導き、fₙ を実際の線形同型にする。
全射性や単射性を provider として仮定しない。

### 同じ有限座標の両立性と p 進復元

任意の全 Tate 点列 x の第 n 成分を fₙ⁻¹ で読み、二つの係数を得る。
x,v,w の p 倍互換性を比較し、fₙ の単射性を使って、
上段の両係数を標準剰余で落とすと下段の両係数になることを証明する。
生成元の座標を無関係に選んで互換性を仮定する構成ではない。

標準 ℤₚ scalar のもとで

    Φ:ℤₚ×ℤₚ→ₗ[ℤₚ]Tate p E,
    Φ(a,b)=a•v+b•w

を定義する。Φ(a,b)=Φ(c,d) なら各有限同型の単射性から全正冪剰余が一致し、
p 進整数の剰余外延性で a=c、b=d を得る。

逆に任意の点列 x の二つの互換係数列を、既存の実際の Cauchy 復元 `liftResidues` で a,b にする。
有限同型を各成分で比較すると Φ(a,b)=x となる。
以上から、

    tatePairEquiv : (ℤₚ×ℤₚ) ≃ₗ[ℤₚ] Tate p E

を構成する。汎用入口には第0段の生成性 hbase を明示的に残す。
次段の Frey 適用で、その hbase を同じ実際の E[p] の基底から証明する。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Algebra.PrimePowerTatePairSpan
import DkMath.Lib.NumberTheory.EllipticTateReduction

#print "file: DkMath.Lib.NumberTheory.EllipticTatePairBasis"

/-!
# 互換な二点から全 Tate 加群の実際の線形同型を構成する

第0段の生成性から各有限段への全射を構成し、実際の捩れ濃度と比較して全単射にする。
その同じ有限座標の互換性と Cauchy 復元から、全 Tate 加群の二成分表示を得る。
-/
namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open DkMath.Lib.Algebra DkMath.Lib.Algebra.PrimePowerTateSequence
noncomputable section
variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
    {p : ℕ} [Fact p.Prime] (v w : Tate p (Points E))

omit [CharZero K] [E.IsElliptic] in
/-- 既存の捩れ scalar を元の同じ点の自然数倍として読む。 -/
theorem torsion_smul_val {N : ℕ} [NeZero N] (c : ZMod N) (x : Torsion E N) :
    (c • x).val = c.val • x.val := by
  have h := Nat.cast_smul_eq_nsmul (ZMod N) c.val x
  rw [ZMod.natCast_zmod_val] at h
  have he := congrArg (torsionGroup E N).subtype h
  rw [map_nsmul] at he
  exact he

/-- 各有限段の二つの同じ点による標準線形写像。 -/
def tatePairLevel (n : ℕ) :
    ZMod (p ^ (n + 1)) × ZMod (p ^ (n + 1)) →ₗ[ZMod (p ^ (n + 1))] Torsion E (p ^ (n + 1)) where
  toFun a := a.1 • ⟨evaluation n v, killed v n⟩ + a.2 • ⟨evaluation n w, killed w n⟩
  map_add' a b := by simp only [Prod.fst_add, Prod.snd_add, add_smul]; abel
  map_smul' c a := by simp only [Prod.smul_fst, Prod.smul_snd, smul_add, smul_smul, RingHom.id_apply, smul_eq_mul]

omit [CharZero K] [E.IsElliptic] in
/-- 有限座標の実際の点への値。 -/
theorem tatePairLevel_val (n : ℕ) (a : ZMod (p ^ (n + 1)) × ZMod (p ^ (n + 1))) :
    (tatePairLevel E v w n a).val = a.1.val • evaluation n v + a.2.val • evaluation n w := by
  change (torsionGroup E _).subtype (_ + _) = _
  rw [map_add]
  change (a.1 • (⟨evaluation n v, killed v n⟩ : Torsion E _)).val +
    (a.2 • (⟨evaluation n w, killed w n⟩ : Torsion E _)).val = _
  rw [torsion_smul_val, torsion_smul_val]

variable (hbase : ∀ x : Points E, p • x = 0 → ∃ a b : ℕ,
    x = a • evaluation 0 v + b • evaluation 0 w)

include hbase in
omit [CharZero K] [E.IsElliptic] in
/-- 実際の有限段への全射は、第0段の生成性からの帰納法で得る。 -/
theorem tatePairLevel_surjective (n : ℕ) : Function.Surjective (tatePairLevel E v w n) := by
  intro x
  obtain ⟨a, b, hab⟩ := pair_span v w hbase n x.val x.property
  refine ⟨(a, b), ?_⟩
  apply Subtype.ext
  rw [tatePairLevel_val]
  apply Eq.trans _ hab.symm
  exact congrArg₂ (fun a b : Points E => a + b)
    (nsmul_eq_of_residue _ (killed v n) (ZMod.natCast_zmod_val (a : ZMod (p ^ (n + 1)))))
    (nsmul_eq_of_residue _ (killed w n) (ZMod.natCast_zmod_val (b : ZMod (p ^ (n + 1)))))

/-- 有限段の濃度は実際に同じ。全射と合わせて単射も得る。 -/
def tatePairLevelEquiv (n : ℕ) :
    (ZMod (p ^ (n + 1)) × ZMod (p ^ (n + 1))) ≃ₗ[ZMod (p ^ (n + 1))] Torsion E (p ^ (n + 1)) :=
  LinearEquiv.ofBijective (tatePairLevel E v w n) <|
    (Nat.bijective_iff_surjective_and_card _).mpr ⟨tatePairLevel_surjective E v w hbase n, by
      rw [Nat.card_prod, Nat.card_zmod, card_torsion_sq E _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero), pow_two]⟩

local notation "lev" => tatePairLevelEquiv E v w hbase

/-- 同じ点列の第 n 成分の二つの係数。 -/
def tatePairCoefficients (x : Tate p (Points E)) (n : ℕ) :
    ZMod (p ^ (n + 1)) × ZMod (p ^ (n + 1)) := (lev n).symm ⟨evaluation n x, killed x n⟩

local notation "coeff" => tatePairCoefficients E v w hbase

/-- 点列・二つの生成点列が互換なので、両係数も標準剰余で互換となる。 -/
theorem tatePairCoefficients_compatible (x : Tate p (Points E)) (n : ℕ) :
    let f := ZMod.castHom (pow_dvd_pow p (Nat.le_succ (n + 1))) (ZMod (p ^ (n + 1)))
    (f (coeff x (n + 1)).1, f (coeff x (n + 1)).2) = coeff x n := by
  dsimp only
  apply (lev n).injective
  apply Subtype.ext
  change (tatePairLevel E v w n _).val = _
  rw [tatePairLevel_val]
  have he := congrArg (fun z : Torsion E (p ^ (n + 1 + 1)) => z.val)
    ((lev (n + 1)).apply_symm_apply ⟨evaluation (n + 1) x, killed x (n + 1)⟩)
  change (tatePairLevel E v w (n + 1) (coeff x (n + 1))).val = evaluation (n + 1) x at he
  rw [tatePairLevel_val] at he
  have hp := congrArg (fun z : Points E => p • z) he
  rw [nsmul_add, smul_comm p, smul_comm p, compatible, compatible, compatible] at hp
  have hcast (c : ZMod (p ^ (n + 1 + 1))) (z : Points E) (hz : p ^ (n + 1) • z = 0) :
      (ZMod.castHom (pow_dvd_pow p (Nat.le_succ (n + 1))) (ZMod (p ^ (n + 1))) c).val • z = c.val • z := by
    apply nsmul_eq_of_residue z hz
    rw [ZMod.natCast_zmod_val, ZMod.castHom_apply, ZMod.cast_eq_val]
  rw [hcast _ _ (killed v n), hcast _ _ (killed w n)]
  change _ = ((lev n) ((lev n).symm ⟨evaluation n x, killed x n⟩)).val
  rw [LinearEquiv.apply_symm_apply]
  exact hp

/-- 同じ二点列の標準 p 進線形結合。 -/
def tatePairParametrization : ℤ_[p] × ℤ_[p] →ₗ[ℤ_[p]] Tate p (Points E) where
  toFun a := a.1 • v + a.2 • w
  map_add' a b := by simp only [Prod.fst_add, Prod.snd_add, add_smul]; abel
  map_smul' c a := by simp only [Prod.smul_fst, Prod.smul_snd, smul_add, smul_smul, RingHom.id_apply, smul_eq_mul]

omit [CharZero K] [E.IsElliptic] in
/-- 無限座標から有限座標への評価公式。 -/
theorem tatePairParametrization_level (a : ℤ_[p] × ℤ_[p]) (n : ℕ) :
    evaluation n (tatePairParametrization E v w a) =
      (tatePairLevel E v w n (PadicInt.toZModPow (n + 1) a.1, PadicInt.toZModPow (n + 1) a.2)).val := by
  rw [tatePairLevel_val]
  exact congrArg₂ (fun a b : Points E => a + b) (evaluation_smul a.1 v n) (evaluation_smul a.2 w n)

include hbase in
/-- 有限同型の単射性と p 進剰余外延性から、無限座標も単射。 -/
theorem tatePairParametrization_injective : Function.Injective (tatePairParametrization E v w) := by
  intro a b h
  have hh (n : ℕ) :
      (PadicInt.toZModPow (n + 1) a.1, PadicInt.toZModPow (n + 1) a.2) =
      (PadicInt.toZModPow (n + 1) b.1, PadicInt.toZModPow (n + 1) b.2) := by
    apply (lev n).injective
    apply Subtype.ext
    have he := congrArg (evaluation n) h
    rw [tatePairParametrization_level, tatePairParametrization_level] at he
    exact he
  apply Prod.ext
  · exact PadicCharacterLimit.ext_positive (fun n => congrArg Prod.fst (hh n))
  · exact PadicCharacterLimit.ext_positive (fun n => congrArg Prod.snd (hh n))

include hbase in
/-- 両係数の実際の Cauchy 復元から、全 Tate 点列を表せる。 -/
theorem tatePairParametrization_surjective : Function.Surjective (tatePairParametrization E v w) := by
  intro x
  have hfst n := congrArg Prod.fst (tatePairCoefficients_compatible E v w hbase x n)
  have hsnd n := congrArg Prod.snd (tatePairCoefficients_compatible E v w hbase x n)
  let a := liftResidues (fun n => (coeff x n).1) hfst
  let b := liftResidues (fun n => (coeff x n).2) hsnd
  refine ⟨(a, b), ?_⟩
  apply PrimePowerTateSequence.ext; intro n
  rw [tatePairParametrization_level, liftResidues_mod, liftResidues_mod]
  exact congrArg (fun z : Torsion E (p ^ (n + 1)) => z.val)
    ((lev n).apply_symm_apply ⟨evaluation n x, killed x n⟩)

/-- 全 Tate 加群への実際の二成分線形同型。 -/
def tatePairEquiv : (ℤ_[p] × ℤ_[p]) ≃ₗ[ℤ_[p]] Tate p (Points E) :=
  LinearEquiv.ofBijective (tatePairParametrization E v w)
    ⟨tatePairParametrization_injective E v w hbase, tatePairParametrization_surjective E v w hbase⟩

end
end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
```

## ステップ3：元の Frey 直線を第一座標に保つ基底

同じ Source、残余直線 L、rootField、hclass、全段 hbad を保持する。
元の同じ非零互換生成元点列を v とする。その第0成分 P は同じ非零 seed である。

同じ実際の残余空間 E[p] の次元2から、P と線形独立な第二点 Q を選ぶ。
既存の実際の `tateReduction_surjective` で Q を同じ全 Tate 加群の点列 w へ持ち上げる。
有限次元や持ち上げの存在を新しい入力にしない。

線形独立な二点と実際の次元2から E[p] の基底を作る。
その基底で任意の p 捩れ点を展開し、標準 ZMod p scalar を自然数代表に戻して、
ステップ2の hbase を内部証明する。

これにより同じ Frey 曲線上に実際の線形同型

    residualTateEquiv : (ℤₚ×ℤₚ) ≃ₗ[ℤₚ] Tate p E

が得られる。第一・第二単位ベクトルの像は、元の同じ v と実際に持ち上げた w である。
標準の積基底をこの同型で写し、Fin 2 を添字とする全 Tate 基底 `residualTateBasis` を構成する。
これは全 Tate 加群の自由階数2を与える実際の基底である。
前回の mod p 商の次元2から直接飛躍せず、有限全段の同型と互換係数復元を経由した。

### 元の同じ直線と基底座標

以前の同じ直線は a•v の全体だった。
今回の二成分同型の単射性と以前の直線の全射表示から、

    residualTateEquiv(a,b)∈同じ直線 ↔ b=0

を証明する。したがって同じ直線が正確に第一座標となり、第二点列 w はその外にある。
新しい別の安定直線へ取り替えていない。

### 実際の Galois 作用行列

元の同じ全点群の `actionLinear` を、この実際の基底で行列化する。
以前の同じ指標による作用公式 σ(v)=χ∞(σ)•v と第一基底ベクトルの一致から、

    M(σ)₀₀=χ∞(σ), M(σ)₁₀=0

を証明する。2×2 行列の下左成分が零となり、第一列は同じ指標を表す。
これは実際の線形作用を `LinearMap.toMatrix` で表した結果であり、三角性を仮定していない。
第二対角成分・上右成分の算術的同定、行列式と円分指標の高位での一致、
Frobenius の特性多項式はまだこの定理には含めない。

今回の **元の直線に適合する Frey 全 Tate 基底** は、従来の hclass と全段 hbad を保持する。
一般の楕円曲線すべてに対する無条件な基底選択入口を新設したという主張ではない。
汎用二成分同型は hbase を要求し、Frey の最終入口ではその生成性を内部供給する。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclicTateReduction
import DkMath.FLT.FreyResidualRankTwo
import DkMath.Lib.NumberTheory.EllipticTatePairBasis
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.Matrix.ToLin

#print "file: DkMath.FLT.FreyTateBasis"

/-!
# 元の Frey 互換生成元を第一ベクトルに持つ全 Tate 加群の基底

同じ E[p] の次元2から第二残余点を選び、実際の第0評価で持ち上げる。
有限捩れ濃度と互換係数復元によって全 Tate 加群の自由階数2を構成する。
同じ第一ベクトルへの既存の指標作用は、実際の作用行列の第一列になる。
hclass と全段 hbad は保持し、行列式や Frobenius の最終算術はまだ証明しない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.Algebra DkMath.Lib.NumberTheory
open EllipticTorsionRepresentation DkMath.Lib.RepresentationTheory PrimePowerTateSequence
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
local notation "vec" => S.residualCyclicTateVector L hline hcofixed hζ hp5 hclass hbad
local notation "v" => Subtype.val (S.residualCyclicTateVector L hline hcofixed hζ hp5 hclass hbad)
local notation "P" => tateReduction S.rationalCurve p v
local notation "padicChar" => S.residualPadicTowerCharacter L hline hcofixed hζ hp5 hclass hbad

/-- 元の第一点列の残余点は同じ非零 seed。 -/
theorem residualTateFirstReduction_ne_zero : P ≠ 0 := by
  intro h
  apply S.residualTateSeed_ne_zero L hline hcofixed hζ hp5 hclass hbad
  have he : evaluation 0 v = 0 := congrArg (fun z : S.ResidualSpace => z.val) h
  exact Subtype.ext he

/-- 同じ残余空間の実際の次元2から、第一点と独立な第二点が存在する。 -/
theorem residualTateSecondResidual_exists : ∃ q : S.ResidualSpace, LinearIndependent (ZMod p) ![P, q] :=
  exists_linearIndependent_pair_of_one_lt_finrank (by rw [S.residual_finrank_eq_two]; decide)
    (S.residualTateFirstReduction_ne_zero L hline hcofixed hζ hp5 hclass hbad)

def residualTateSecondResidual : S.ResidualSpace :=
  (S.residualTateSecondResidual_exists L hline hcofixed hζ hp5 hclass hbad).choose

local notation "Q" => S.residualTateSecondResidual L hline hcofixed hζ hp5 hclass hbad

theorem residualTateResidualPair_independent : LinearIndependent (ZMod p) ![P, Q] :=
  (S.residualTateSecondResidual_exists L hline hcofixed hζ hp5 hclass hbad).choose_spec

/-- 第二残余点を、同じ曲線の実際の Tate 点列へ持ち上げる。 -/
def residualTateSecond : Tate p (Points S.rationalCurve) :=
  (tateReduction_surjective S.rationalCurve p Q).choose

local notation "w" => S.residualTateSecond L hline hcofixed hζ hp5 hclass hbad

theorem residualTateSecond_reduction : tateReduction S.rationalCurve p w = Q :=
  (tateReduction_surjective S.rationalCurve p Q).choose_spec

/-- 同じ第一残余点を含む実際の二次元基底。 -/
def residualTateResidualBasis : Module.Basis (Fin 2) (ZMod p) S.ResidualSpace :=
  Module.Basis.mk (S.residualTateResidualPair_independent L hline hcofixed hζ hp5 hclass hbad)
    ((S.residualTateResidualPair_independent L hline hcofixed hζ hp5 hclass hbad).span_eq_top_of_card_eq_finrank
      (by simp only [Fintype.card_fin, S.residual_finrank_eq_two])).ge

/-- 同じ二つの点列の第0成分は、実際の E[p] 全体を生成する。 -/
theorem residualTatePair_base_span (x : Points S.rationalCurve) (hx : p • x = 0) :
    ∃ a b : ℕ, x = a • evaluation 0 v + b • evaluation 0 w := by
  let b := S.residualTateResidualBasis L hline hcofixed hζ hp5 hclass hbad
  let t : S.ResidualSpace := ⟨x, hx⟩
  have hb0 : b 0 = P := by simp only [b, residualTateResidualBasis, Module.Basis.coe_mk, Matrix.cons_val_zero]
  have hb1 : b 1 = Q := by simp only [b, residualTateResidualBasis, Module.Basis.coe_mk, Matrix.cons_val_one, Matrix.cons_val_zero]
  have he := congrArg (torsionGroup S.rationalCurve p).subtype (b.sum_repr t)
  rw [Fin.sum_univ_two, map_add] at he
  change ((b.repr t 0) • b 0).val + ((b.repr t 1) • b 1).val = x at he
  rw [torsion_smul_val, torsion_smul_val, hb0, hb1] at he
  have hw := congrArg Subtype.val (S.residualTateSecond_reduction L hline hcofixed hζ hp5 hclass hbad)
  change evaluation 0 w = (Q).val at hw
  change (b.repr t 0).val • evaluation 0 v + (b.repr t 1).val • (Q).val = x at he
  rw [← hw] at he
  exact ⟨(b.repr t 0).val, (b.repr t 1).val, he.symm⟩

/-- 全 Tate 加群の実際の二成分表示。第一ベクトルは元の同じ v。 -/
def residualTateEquiv : (ℤ_[p] × ℤ_[p]) ≃ₗ[ℤ_[p]] Tate p (Points S.rationalCurve) :=
  tatePairEquiv S.rationalCurve v w (S.residualTatePair_base_span L hline hcofixed hζ hp5 hclass hbad)

local notation "eqv" => S.residualTateEquiv L hline hcofixed hζ hp5 hclass hbad

theorem residualTateEquiv_first : eqv (1, 0) = v := by
  change (1 : ℤ_[p]) • v + (0 : ℤ_[p]) • w = v
  simp

theorem residualTateEquiv_second : eqv (0, 1) = w := by
  change (0 : ℤ_[p]) • v + (1 : ℤ_[p]) • w = w
  simp

/-- 既存の同じ Tate 直線は、新しい座標の正確な第一成分である。 -/
theorem residualTateEquiv_mem_line_iff (a b : ℤ_[p]) :
    eqv (a, b) ∈ S.residualCyclicTateLine L hline hcofixed hζ hp5 hclass hbad ↔ b = 0 := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := S.residualCyclicTateParametrization_surjective L hline hcofixed hζ hp5 hclass hbad ⟨eqv (a, b), h⟩
    have he : eqv (c, 0) = eqv (a, b) := by
      change c • v + (0 : ℤ_[p]) • w = _
      rw [zero_smul, add_zero]
      have he := congrArg (fun x : S.residualCyclicTateLine L hline hcofixed hζ hp5 hclass hbad => x.val) hc
      change c • v = eqv (a, b) at he
      exact he
    exact (congrArg Prod.snd ((eqv).injective he)).symm
  · intro h
    subst b
    change a • v + (0 : ℤ_[p]) • w ∈ _
    rw [zero_smul, add_zero]
    exact (S.residualCyclicTateLine L hline hcofixed hζ hp5 hclass hbad).smul_mem a (vec).property

/-- 実際の全 Tate 加群の Fin 2 基底。 -/
def residualTateBasis : Module.Basis (Fin 2) ℤ_[p] (Tate p (Points S.rationalCurve)) :=
  (Module.Basis.finTwoProd ℤ_[p]).map eqv

local notation "basis" => S.residualTateBasis L hline hcofixed hζ hp5 hclass hbad

theorem residualTateBasis_first : basis 0 = v := by
  rw [residualTateBasis, Module.Basis.map_apply, Module.Basis.finTwoProd_zero]
  exact S.residualTateEquiv_first L hline hcofixed hζ hp5 hclass hbad

/-- 同じ実際の全 Galois 線形作用の、この基底での行列。 -/
def residualTateActionMatrix (σ : Field.absoluteGaloisGroup ℚ) : Matrix (Fin 2) (Fin 2) ℤ_[p] :=
  LinearMap.toMatrix basis basis (actionLinear S.residualPointActionHom σ)

/-- 第一列は元の指標と0。基底と同じ作用から導き、三角性を仮定しない。 -/
theorem residualTateActionMatrix_first_column (σ : Field.absoluteGaloisGroup ℚ) :
    (S.residualTateActionMatrix L hline hcofixed hζ hp5 hclass hbad σ) 0 0 = (padicChar σ : ℤ_[p]) ∧
    (S.residualTateActionMatrix L hline hcofixed hζ hp5 hclass hbad σ) 1 0 = 0 := by
  have hv : actionLinear S.residualPointActionHom σ v = (padicChar σ : ℤ_[p]) • v :=
    S.residualCyclicTateLine_action_scalar L hline hcofixed hζ hp5 hclass hbad σ
      ⟨v, (vec).property⟩
  have hcol (i : Fin 2) : (S.residualTateActionMatrix L hline hcofixed hζ hp5 hclass hbad σ) i 0 =
      (padicChar σ : ℤ_[p]) * (if i = 0 then 1 else 0) := by
    rw [residualTateActionMatrix, LinearMap.toMatrix_apply,
      S.residualTateBasis_first L hline hcofixed hζ hp5 hclass hbad, hv,
      ← S.residualTateBasis_first L hline hcofixed hζ hp5 hclass hbad, map_smul]
    by_cases hi : i = 0
    · subst i; simp
    · simp [hi]
  exact ⟨by simpa using hcol 0, by simpa using hcol 1⟩

end
end DkMath.FLT.Frey.Source
```

## 回帰例と監査

`DkMathTest.FLT.FreyTateBasis` は、同じ条件付き Source・同じ基底で次を検証する。

- 任意の全 Tate 点列が二成分同型の逆写像との往復で同じ点列へ戻る。
- 元の v と第二点列 w の座標が正確に (1,0)、(0,1) となる。
- 第二点列が以前の同じ Tate 直線の外にある。
- 任意の実際の p³ 捩れ点が同じ二点列の第2成分で表示され、有限段同型でも往復できる。
- 恒等 Galois 元の実際の作用行列が単位行列になる。

有限捩れ点と無限 Tate 点列の往復を別々に検証する。
不可能な数値の Fermat Source を製造して検証したとは主張しない。

主要15宣言の公理報告と型・構成子・不透明証明本体の再帰依存監査、12件の公開入力監査を追加する。
実際の有限捩れ濃度、Cauchy 復元、元の非零 seed、実際の残余次元2と持ち上げ、
同じ直線・指標作用が依存経路に含まれることを確認する。
汎用 hbase は正確に保持し、最終 Frey 入口では hbase/hbasis/hrank/hfree/hbij/htriangle を追加要求しない。
hclass と全段 hbad は保持する。

3 production の Lib/FLT/root 公開、通常テスト入口、root smoke、教科書3ブロックの全文一致・個別コンパイルを確認する。
記録：`evidence/validation-note032-frey-tate-basis.txt`。

## 残る境界

- 同じ円分類群商の特定 ω² 成分の消滅 hclass。
- 全段の共鳴素点条件 hbad または反復に十分な保存性。
- 第二対角指標の算術、高位 Weil pairing と円分行列式。
- 良還元 Frobenius の特性多項式と最終矛盾の局所・大域算術。

今回の条件下で、全 Tate 加群の実際の基底・元の直線への適合・実際の作用行列の第一列は完成した。
位相的な基底同型・新しい作用の連続性は今回証明していない。
上三角な作用行列だけで最終矛盾を得たとは主張しない。
**今回の3ステップは完成。一般 hno は引き続き未完成である。**
外部の分類定理を追加せず、既存の同じ曲線の全有限捩れ濃度・第0評価全射性・残余次元、
同じ塔の生成元と指標、標準 p 進 scalar・互換係数復元を使う。
