# NOTE-032 教科書：標準 p 進 Tate 加群と同じ Frey 階数1直線

日付：2026-11-06。前段：`TEXTBOOK-N032-FREY-TATE-VECTOR-261106.md`。

今回の2ステップは、①実際の全 Tate 点列への標準 ℤₚ 加群構造、
②同じ Frey 互換生成元による階数1線形同型と、同じ指標による実際の作用の記述である。
以下の2つの Lean ブロックは production ファイルの全文である。
順にモジュールへ配置し、import 直後の正確な `#print "file: …"` を保持する。

## ステップ1：点列の標準 scalar を零化条件から構成する

前回の Tate p G は、同じ加法可換群 G の点列で

    p^(n+1)•xₙ=0,  p•xₙ₊₁=xₙ

を満たす実際の加法群であった。
素数 p に対し、a∈ℤₚ の作用を

    (a•x)ₙ=(PadicInt.toZModPow (n+1) a).val • xₙ

と定義する。右辺は元の同じ群の自然数倍である。

### 自然数代表への依存を取り除く

N•y=0 の点 y について、自然数 b,c が法 N で等しいなら b•y=c•y と証明する。
実際に (b mod N)•y=b•y を除法の等式と N•y=0 から導き、
ZMod の値の等式から b mod N=c mod N を得る。

この補題により、加法・乗法を行った剰余の代表と、代表同士の和・積は同じ作用を持つ。
また、隣接する法の標準剰余両立性と元の点列の p 倍互換性から、
新しい scalar 倍の点列も p 倍互換性を満たす。
零化条件も自然数倍の交換から保たれる。

こうして元の同じ点列型上に SMul と Module の公理を証明する。
後半の線形同型から加群構造を運び込んだ定義ではない。

元の加法準同型 f:G→H は自然数倍を保つので、点列上の写像は ℤₚ 線形となる。
前回の成分ごとの群作用も同じ写像のまま ℤₚ 線形作用になる。

### 一般の互換係数列の復元

全射性には単元でない係数も必要になる。
cₙ∈ZMod(p^(n+1)) が隣接剰余で両立するなら、
0,c₀.val,c₁.val,… という整数列を取り、隣接差の p 冪可除性を証明する。
Mathlib の実際の Cauchy 極限 `PadicInt.ofIntSeq` で `liftResidues` を構成し、
その各有限剰余が元の cₙ であることを証明する。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Algebra.PrimePowerTateSequence
import DkMath.Lib.Algebra.PadicCharacterLimit
import Mathlib.Algebra.Module.MinimalAxioms

#print "file: DkMath.Lib.Algebra.PrimePowerTateModule"

/-!
# 同じ Tate 点列への標準 p 進 scalar と互換剰余の復元

(a • x)ₙ=(a mod p^(n+1)).val • xₙ と定義する。
元の点の零化条件から代表の選択に依存しないことを証明し、遷移条件と加群公理を導く。
位数や階数を仮定して加群構造を運び込む定義ではない。
-/

namespace DkMath.Lib.Algebra.PrimePowerTateSequence
noncomputable section
variable {G : Type*} [AddCommGroup G]

/-- N で消える点への自然数倍は、法 N の同じ剰余だけで決まる。 -/
theorem nsmul_eq_of_residue {N a b : ℕ} (x : G) (hx : N • x = 0)
    (h : (a : ZMod N) = b) : a • x = b • x := by
  have hm (c : ℕ) : (c % N) • x = c • x := by
    have hc := congrArg (fun k : ℕ => k • x) (Nat.mod_add_div c N)
    simpa only [add_nsmul, mul_nsmul, hx, nsmul_zero, add_zero] using hc
  have hab : a % N = b % N := by simpa only [ZMod.val_natCast] using congrArg ZMod.val h
  rw [← hm a, ← hm b, hab]

variable {p : ℕ} [Fact p.Prime]

/-- 実際の各成分への、標準剰余を用いた p 進 scalar。 -/
def padicSMul (a : ℤ_[p]) (x : Tate p G) : Tate p G :=
  ⟨fun n => (PadicInt.toZModPow (n + 1) a).val • evaluation n x,
    ⟨fun n => by rw [smul_comm, killed, nsmul_zero], fun n => by
      rw [smul_comm, compatible]
      apply nsmul_eq_of_residue _ (killed x n)
      rw [ZMod.natCast_zmod_val]
      have h := PadicInt.cast_toZModPow (n + 1) (n + 1 + 1) (Nat.le_succ _) a
      rw [ZMod.cast_eq_val] at h
      exact h⟩⟩

instance padicSMulInstance : SMul ℤ_[p] (Tate p G) := ⟨padicSMul⟩

/-- スカラー倍の評価公式。元の同じ点の自然数倍である。 -/
theorem evaluation_smul (a : ℤ_[p]) (x : Tate p G) (n : ℕ) :
    evaluation n (a • x) = (PadicInt.toZModPow (n + 1) a).val • evaluation n x := rfl

instance padicModule : Module ℤ_[p] (Tate p G) := Module.ofMinimalAxioms
  (fun a x y => by
    apply ext; intro n
    change (PadicInt.toZModPow (n + 1) a).val • (evaluation n x + evaluation n y) =
      (PadicInt.toZModPow (n + 1) a).val • evaluation n x +
        (PadicInt.toZModPow (n + 1) a).val • evaluation n y
    exact nsmul_add _ _ _)
  (fun a b x => by
    apply ext; intro n
    rw [evaluation_smul, map_add, map_add (evaluation n), evaluation_smul, evaluation_smul, ← add_nsmul]
    apply nsmul_eq_of_residue _ (killed x n)
    simp only [Nat.cast_add, ZMod.natCast_zmod_val])
  (fun a b x => by
    apply ext; intro n
    rw [evaluation_smul, map_mul, evaluation_smul, evaluation_smul, ← mul_nsmul']
    apply nsmul_eq_of_residue _ (killed x n)
    simp only [Nat.cast_mul, ZMod.natCast_zmod_val])
  (fun x => by
    apply ext; intro n
    rw [evaluation_smul, map_one]
    have h := nsmul_eq_of_residue (evaluation n x) (killed x n)
      (show (((1 : ZMod (p ^ (n + 1)))).val : ZMod (p ^ (n + 1))) = (1 : ℕ) by
        simp only [ZMod.natCast_zmod_val, Nat.cast_one])
    exact h.trans (one_nsmul _))

variable {H : Type*} [AddCommGroup H]

/-- 元の加法準同型は、標準 scalar に関して自動的に p 進線形。 -/
def mapLinear (f : G →+ H) : Tate p G →ₗ[ℤ_[p]] Tate p H where
  __ := map f
  map_smul' a x := by
    apply ext; intro n
    change f ((PadicInt.toZModPow (n + 1) a).val • evaluation n x) =
      (PadicInt.toZModPow (n + 1) a).val • f (evaluation n x)
    exact map_nsmul f _ _

variable {Γ : Type*} [Group Γ]

/-- 同じ成分ごとの作用を標準 p 進線形作用として公開する。 -/
def actionLinear (ρ : Γ →* AddMonoid.End G) : Γ →* Module.End ℤ_[p] (Tate p G) where
  toFun g := mapLinear (ρ g)
  map_one' := by
    apply LinearMap.ext; intro x
    exact congrArg (fun f : AddMonoid.End (Tate p G) => f x) (action ρ).map_one
  map_mul' g h := by
    apply LinearMap.ext; intro x
    exact congrArg (fun f : AddMonoid.End (Tate p G) => f x) ((action ρ).map_mul g h)

/-- 互換な法 p^(n+1) の値を、実際の p 進整数へ復元するための整数列。 -/
def residueRepresentatives (c : ∀ n : ℕ, ZMod (p ^ (n + 1))) : ℕ → ℤ
  | 0 => 0
  | n + 1 => (c n).val

variable (c : ∀ n : ℕ, ZMod (p ^ (n + 1)))
    (hc : ∀ n, ZMod.castHom (pow_dvd_pow p (Nat.le_succ (n + 1)))
      (ZMod (p ^ (n + 1))) (c (n + 1)) = c n)

include hc in
/-- 隣接剰余両立性から Cauchy 性に必要な可除性を取り出す。 -/
theorem residueRepresentatives_dvd (i : ℕ) :
    (p : ℤ) ^ i ∣ residueRepresentatives c (i + 1) - residueRepresentatives c i := by
  cases i with
  | zero => simp
  | succ i =>
    rw [← Int.natCast_pow, ← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub]
    have h := hc i
    rw [ZMod.castHom_apply, ZMod.cast_eq_val] at h
    simpa only [residueRepresentatives, Int.cast_natCast, ZMod.natCast_zmod_val, sub_eq_zero] using h

/-- 互換剰余列の実際の Cauchy 極限。元が単元であることは要求しない。 -/
def liftResidues : ℤ_[p] :=
  PadicInt.ofIntSeq (residueRepresentatives c)
    (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub _ p (residueRepresentatives_dvd c hc))

/-- 構成した整数は元の全ての剰余を正確に持つ。 -/
theorem liftResidues_mod (n : ℕ) : PadicInt.toZModPow (n + 1) (liftResidues c hc) = c n := by
  have h := PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub _ p (residueRepresentatives_dvd c hc) (n + 1)
  simpa only [liftResidues, residueRepresentatives, Int.cast_natCast, ZMod.natCast_zmod_val] using h

end
end DkMath.Lib.Algebra.PrimePowerTateSequence
```

## ステップ2：同じ Frey Tate 直線を線形化する

同じ Source、同じ残余直線 L、同じ rootField、hclass、全段 hbad を保持する。
前回の実際の点列部分群は、各第 n 成分が同じ有限段 Kₙ に入るという条件で定義されていた。
自然数倍で Kₙ は閉じているので、今回の標準 ℤₚ scalar でも閉じる。

`residualCyclicTateLine` は、この同じ集合・加法群を全 Tate 加群の部分加群として公開する。
自然な包含は標準 ℤₚ scalar のもとで線形かつ単射となる。
古い加法群の包含に別の写像を対応させたものではない。

### 互換生成元を使った係数の読み取り

前回の同じ生成元 eₙ は各段 Kₙ を生成し、

    p•eₙ₊₁=eₙ,  ord(eₙ)=p^(n+1)

であった。この生成元を1の像とする巡回座標

    qₙ:ZMod(p^(n+1)) ≃+ Kₙ

を構成する。自然数 k に対して qₙ(k)=k•eₙ を証明する。
任意の同じ点列 x に対して cₙ=qₙ⁻¹(xₙ) と定義し、

    xₙ=cₙ.val•eₙ

を得る。点列 x と生成元 e の両方の p 倍互換性から、
上段の係数を下段へ落とす標準剰余が cₙ になることを、qₙ の単射性で証明する。
係数の互換性を新しい provider として要求しない。

### a↦a•v の単射性・全射性

前回の同じ非零生成元点列 v=(eₙ) を使い、

    Φ:ℤₚ→ₗ[ℤₚ]residualCyclicTateLine,  Φ(a)=a•v

を定義する。これは既に構成した標準 scalar に関する実際の線形写像である。

Φ(a)=Φ(b) なら、各成分の巡回座標の単射性から a,b の全正冪剰余が一致する。
p 進整数の剰余外延性により a=b となり、Φ は単射である。

任意の x の実際の係数列 cₙ は両立するので、ステップ1の `liftResidues` で a を取る。
a の各有限剰余は cₙ であり、従って Φ(a) の各成分は xₙ に等しい。
点列の外延性で Φ(a)=x が従う。これが全射性である。

以上から、実際の線形同型

    residualCyclicTateLineEquiv : ℤₚ ≃ₗ[ℤₚ] residualCyclicTateLine

を得る。特にこの線形同型の逆が、同じ Tate 直線を ℤₚ と同一視する。
階数1という表現はこの明示的な同型に基づく。標準 scalar の構成をこの同型へ依存させていない。
選んだ基底 v は生成元選択に依存するが、指標そのものは以前の座標非依存な同じ指標を使う。

### 実際の Galois 作用を同じ指標の scalar として記述する

以前の同じ連続指標 χ∞ は、法 p^(n+1) で同じ有限段の指標 χₙ を回収する。
各段の実際の点作用は χₙ(σ).val 倍である。
標準 scalar の評価公式と比較し、全ての x について

    σ(x)=χ∞(σ)•x

を証明する。
従って σ(a•v)=χ∞(σ)•(a•v) も従う。
自然な線形包含後でも、全点群の同じ線形作用とこの scalar 表示が一致する。
以前の「指標値1 iff 固定」という判定を、全ての指標値を表す作用公式へ進めた結果である。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclicTateVector
import DkMath.Lib.Algebra.PrimePowerTateModule

#print "file: DkMath.FLT.FreyCyclicTateLine"

/-!
# 同じ Frey Tate 点列の標準 p 進直線

元の点列への標準 scalar を制限する。互換生成元から各成分の係数を読み、
係数の隣接両立性と実際の Cauchy 極限から、a↦a•v の全単射を証明する。
これにより実際の ℤₚ 線形同型と線形包含を得る。hclass と全段 hbad は保持する。
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
local notation "tower" => S.residualCyclicTower L hline hcofixed hζ hp5 hclass hbad
local notation "gen" => S.residualTateGenerators L hline hcofixed hζ hp5 hclass hbad
local notation "vec" => S.residualCyclicTateVector L hline hcofixed hζ hp5 hclass hbad
local notation "padicChar" => S.residualPadicTowerCharacter L hline hcofixed hζ hp5 hclass hbad

/-- 以前の同じ部分群を、全点列の標準 scalar に閉じた部分加群として公開する。 -/
def residualCyclicTateLine : Submodule ℤ_[p] (Tate p (Points S.rationalCurve)) where
  __ := S.residualCyclicTate L hline hcofixed hζ hp5 hclass hbad
  smul_mem' a x hx n := by
    rw [evaluation_smul]
    exact (tower n).carrier.nsmul_mem (hx n) _

local notation "line" => S.residualCyclicTateLine L hline hcofixed hζ hp5 hclass hbad

/-- 同じ全幾何学的点群の Tate 加群への自然な p 進線形包含。 -/
def residualCyclicTateLine_inclusion : line →ₗ[ℤ_[p]] Tate p (Points S.rationalCurve) := (line).subtype

theorem residualCyclicTateLine_inclusion_injective :
    Function.Injective (S.residualCyclicTateLine_inclusion L hline hcofixed hζ hp5 hclass hbad) :=
  Subtype.val_injective

/-- 同じ互換生成元を1の像に持つ各段の巡回座標。 -/
def residualTateGeneratorCoordinates (n : ℕ) : ZMod (p ^ (n + 1)) ≃+ (tower n).carrier := by
  let := (tower n).finite
  have ho : addOrderOf (gen n) = p ^ (n + 1) :=
    (addOrderOf_injective (tower n).carrier.subtype Subtype.val_injective (gen n)).symm.trans
      (S.residualTateGenerators_order L hline hcofixed hζ hp5 hclass hbad n)
  have ht : AddSubgroup.zmultiples (gen n) = ⊤ :=
    AddSubgroup.eq_top_of_card_eq _ (by rw [Nat.card_zmultiples, ho, (tower n).card])
  exact zmodAddEquivOfGenerator (fun x => ht ▸ AddSubgroup.mem_top x) (tower n).card

local notation "coords" => S.residualTateGeneratorCoordinates L hline hcofixed hζ hp5 hclass hbad

/-- 座標の自然数上の値は、元の同じ生成元の自然数倍。 -/
theorem residualTateGeneratorCoordinates_nat (n k : ℕ) :
    (coords n (k : ZMod (p ^ (n + 1)))).val = k • (gen n).val := by
  have h1 : coords n 1 = gen n := zmodAddEquivOfGenerator_apply_one _ (tower n).card
  have h := congrArg (tower n).carrier.subtype (map_nsmul (coords n) k (1 : ZMod (p ^ (n + 1))))
  simp only [nsmul_eq_mul, mul_one, h1, map_nsmul] at h
  change (coords n (k : ZMod (p ^ (n + 1)))).val = k • (gen n).val at h
  exact h

/-- 任意の同じ点列の第 n 成分を生成元座標で読む。 -/
def residualTateCoefficient (x : line) (n : ℕ) : ZMod (p ^ (n + 1)) :=
  (coords n).symm ⟨evaluation n x.val, x.property n⟩

local notation "coeff" => S.residualTateCoefficient L hline hcofixed hζ hp5 hclass hbad

/-- 第 n 成分は、実際に読み取った同じ係数と同じ生成元の積。 -/
theorem residualTateCoefficient_spec (x : line) (n : ℕ) :
    evaluation n x.val = (coeff x n).val • (gen n).val := by
  have h := S.residualTateGeneratorCoordinates_nat L hline hcofixed hζ hp5 hclass hbad n (coeff x n).val
  rw [ZMod.natCast_zmod_val] at h
  simpa only [residualTateCoefficient, AddEquiv.apply_symm_apply] using h

/-- 点列と生成元の両方の p 倍互換性から、係数の標準剰余両立性を導く。 -/
theorem residualTateCoefficient_compatible (x : line) (n : ℕ) :
    ZMod.castHom (pow_dvd_pow p (Nat.le_succ (n + 1))) (ZMod (p ^ (n + 1)))
      (coeff x (n + 1)) = coeff x n := by
  apply (coords n).injective
  apply Subtype.ext
  rw [ZMod.castHom_apply, ZMod.cast_eq_val,
    S.residualTateGeneratorCoordinates_nat L hline hcofixed hζ hp5 hclass hbad]
  change (coeff x (n + 1)).val • (gen n).val =
    ((coords n) ((coords n).symm ⟨evaluation n x.val, x.property n⟩)).val
  rw [AddEquiv.apply_symm_apply]
  rw [← S.residualTateGenerators_step L hline hcofixed hζ hp5 hclass hbad n,
    smul_comm, ← S.residualTateCoefficient_spec L hline hcofixed hζ hp5 hclass hbad]
  exact compatible x.val n

/-- 同じ生成元点列による実際の p 進線形写像 a↦a•v。 -/
def residualCyclicTateParametrization : ℤ_[p] →ₗ[ℤ_[p]] line where
  toFun a := a • (⟨(vec).val, (vec).property⟩ : line)
  map_add' a b := add_smul a b _
  map_smul' a b := mul_smul a b _

local notation "param" => S.residualCyclicTateParametrization L hline hcofixed hζ hp5 hclass hbad

/-- 各生成元の巡回座標と全 p 冪剰余の外延性から単射。 -/
theorem residualCyclicTateParametrization_injective : Function.Injective param := by
  intro a b h
  apply PadicCharacterLimit.ext_positive
  intro n
  apply (coords n).injective
  apply Subtype.ext
  have he := congrArg (fun x : line => evaluation n x.val) h
  rw [← ZMod.natCast_zmod_val (PadicInt.toZModPow (n + 1) a),
    ← ZMod.natCast_zmod_val (PadicInt.toZModPow (n + 1) b)]
  rw [S.residualTateGeneratorCoordinates_nat L hline hcofixed hζ hp5 hclass hbad,
    S.residualTateGeneratorCoordinates_nat L hline hcofixed hζ hp5 hclass hbad]
  exact he

/-- 実際の互換係数列の Cauchy 極限から全射。極限や全射性の provider は不要。 -/
theorem residualCyclicTateParametrization_surjective : Function.Surjective param := by
  intro x
  let a := liftResidues (coeff x) (S.residualTateCoefficient_compatible L hline hcofixed hζ hp5 hclass hbad x)
  refine ⟨a, ?_⟩
  apply Subtype.ext
  apply PrimePowerTateSequence.ext
  intro n
  change (PadicInt.toZModPow (n + 1) a).val • (gen n).val = evaluation n x.val
  rw [liftResidues_mod]
  exact (S.residualTateCoefficient_spec L hline hcofixed hζ hp5 hclass hbad x n).symm

/-- 同じ Tate 直線の実際の階数1線形同型。標準 scalar の上で全単射を証明した結果。 -/
def residualCyclicTateLineEquiv : ℤ_[p] ≃ₗ[ℤ_[p]] line :=
  LinearEquiv.ofBijective param
    ⟨S.residualCyclicTateParametrization_injective L hline hcofixed hζ hp5 hclass hbad,
      S.residualCyclicTateParametrization_surjective L hline hcofixed hζ hp5 hclass hbad⟩

/-- 同じ実際の Galois 点作用は、全点列上の標準 p 進 scalar 倍に等しい。 -/
theorem residualCyclicTateLine_action_scalar (σ : Field.absoluteGaloisGroup ℚ) (x : line) :
    action S.residualPointActionHom σ x.val = (padicChar σ : ℤ_[p]) • x.val := by
  apply PrimePowerTateSequence.ext
  intro n
  rw [evaluation_action, evaluation_smul]
  have hm := congrArg Units.val (S.residualPadicTowerCharacter_mod L hline hcofixed hζ hp5 hclass hbad n σ)
  change PadicInt.toZModPow (n + 1) (padicChar σ : ℤ_[p]) = _ at hm
  rw [hm]
  exact (tower n).character_spec σ (evaluation n x.val) (x.property n)

/-- 線形包含も、元の同じ Galois 作用に関して同変である。 -/
theorem residualCyclicTateLine_inclusion_scalar (σ : Field.absoluteGaloisGroup ℚ) (x : line) :
    actionLinear S.residualPointActionHom σ
      (S.residualCyclicTateLine_inclusion L hline hcofixed hζ hp5 hclass hbad x) =
    S.residualCyclicTateLine_inclusion L hline hcofixed hζ hp5 hclass hbad ((padicChar σ : ℤ_[p]) • x) :=
  S.residualCyclicTateLine_action_scalar L hline hcofixed hζ hp5 hclass hbad σ x

end
end DkMath.FLT.Frey.Source
```

## 回帰例と検証

`DkMathTest.FLT.FreyCyclicTateLine` は標準有限剰余から任意の5進整数を復元する。
特に非単元5も回収でき、最初の法5の剰余が0であっても極限が非零であることを確認する。
単元値指標の極限だけを一般の係数復元へ誤用しない。

標準 scalar と元の加法準同型による点列の移送が、各成分で可換することも確認する。
同じ抽象 Frey Source と同じ条件付き塔では、任意の点列 x について同型の逆写像で x を回収する。
さらに p•v は第0成分が0でも点列全体として非零であることを、実際の単射性から確認する。
第0成分だけで点列の零性を判定することを避ける検査である。
同じ包含の線形性も確認する。

主要13宣言の公理報告・型／構成子／不透明証明本体の再帰依存監査、
10件の公開入力監査を追加する。標準加群公理の根、実際の互換係数列の Cauchy 復元、
単射性・全射性、有限段の作用公式と同じ指標の剰余公式を監査する。
hclass と全段 hbad は保持し、hmodule/hrank/hfree/hsurj/hequiv/hscalar を新しい provider にしない。

Lib/FLT/root 公開、通常テスト入口、root smoke、教科書全文一致・個別コンパイルを確認する。
記録：`evidence/validation-note032-frey-tate-line.txt`。

## 残る境界

- 同じ円分類群商の特定 ω² 成分の消滅 hclass。
- 全段の共鳴素点条件 hbad または反復に十分な保存性。
- 合併 U の全 p 冪捩れと各 Kₙ の一致、Tₚ(U) との明示的な同定。
- Tₚ(E) 全体の階数2・Weil pairing・Frobenius 特性多項式と最終矛盾の算術。

今回、標準 ℤₚ scalar・同じ部分加群の階数1同型・包含の線形性・全点列の scalar 作用公式は完成した。
点列群の位相や新しい作用の連続性を追加したとは主張しない。以前の同じ指標の連続性は証明済みである。
**一般 hno は引き続き未完成である。**
外部の類群消滅定理やイソジェニー分類を追加せず、既存の同じ生成元・有限作用・指標と
Mathlib の巡回座標・p 進 Cauchy 極限・剰余外延性・線形同型 API を使う。
