# NOTE-032 教科書: 同じ Kummer 根の完備体への降下と局所 p 乗性

日付: 2026-11-03。同じ `S,L,K,m,v,ψ,P,F,M,α,b` と同じ素点の包含を保つ。

今回、**同じ定数 b の p 上の局所 p 乗性まで接続した**。
一般 hno の完成を主張するものではない。

\[
D_w=1\Longrightarrow e=f=1
\Longrightarrow F_v\xrightarrow[\text{元の包含を延長}]{\sim}M_w
\Longrightarrow\exists t\in F_v^\times,\quad t^p=b.
\]

前章までの `e=f=1` を入力とする一般的な完備化比較を Lib に実装した。
局所次数1・完備化写像の全射性・局所根を新たな provider として仮定していない。
Frey の局所根の入口には `hbad`、`hvanish`、`hsurj` は不要である。
指定された同じ表示 P の存在、Source・cofixed 直線・巡回段・hp5 の条件は保持する。

## 1. 今回証明した完備化比較の正確な範囲

一般数体 F,M と F→M、同じ整数環の素点 v,w、その lying-over を固定する。
この素点 v は Lean では `vF` と書き、巡回段の商元の変数 `v` と区別する。
実装: [NumberFieldCompletionComparison.lean](../../../DkMath/Lib/NumberTheory/NumberFieldCompletionComparison.lean)。

一般の局所次数公式 `[M_w:F_v]=ef` の全場合を形式化したわけではない。
必要な **e=f=1 の場合** を、桁近似と完備性から直接証明した。
この比較には M/F の Galois 性も要求しない。

### 剰余次数1から最初の桁へ

Mathlib の実際の剰余次数の定義と
`Ideal.inertiaDeg_eq_of_isMaximal` により、

\[
f=1\Longrightarrow [\mathcal O_M/w:\mathcal O_F/v]=1
\Longrightarrow\mathcal O_F/v\longrightarrow\mathcal O_M/w\text{ は全射}.
\]

w において局所整数となる x∈M、すなわち |x|_w≤1 を取る。
x=n/d、n,d∈O_M、d∉w と書ける。剰余体では d が非零なので、
[n]/[d] の原像を O_F/v に取り、さらに整数 a∈O_F に持ち上げる。

\[
n-\iota(a)d\in w\Longrightarrow |x-\iota(a)|_w<1.
\]

x 自身が大域整数である必要はない。次の桁で割り算した後も、この局所整数の補題を使える。

### 同じ一様化元で精度を一段ずつ上げる

v の一様化元 π∈F を、付値 |π|_v=exp(-1) として選ぶ。
既存の同じ素点の `valuation_liesOver` と e=1 から、

\[
|\iota(\pi)|_w=|\pi|_v=\exp(-1).
\]

整数値付値なので、誤差が1未満なら exp(-1) 以下である。
最初の桁 a を引き、同じ π で割った

\[
y=\frac{x-\iota(a)}{\iota(\pi)}
\]

は再び局所整数になる。これを帰納的に繰り返し、任意の n について

\[
\exists a_n\in F,\qquad |x-\iota(a_n)|_w\le\exp(-n)
\]

を得る。一般の x∈M は底体の π の冪で局所整数にしてから近似し、同じ冪で割り戻す。
従って任意の非零半径 γ について誤差を γ 未満にでき、底体 F の像は w 付値の M に稠密である。

### 自然な完備化写像と閉じた像

Mathlib の `uniformContinuous_algebraMap_liesOver` で元の包含を一様連続写像とし、
`Completion.mapRingHom` により完備化へ延長する。これが `completionMap v w` である。
特に次の等式を独立の定理として証明している。

\[
\operatorname{completionMap}_{v,w}(\operatorname{algebraMap}_{F,F_v}(a))
=\operatorname{algebraMap}_{M,M_w}(\iota(a)).
\]

e=1 なら元の包含が付値をそのまま保存するため、一様構造を誘導する写像となる。
完備化後もその性質を保ち、完備な底体 F_v の像は完備であり、M_w の中で閉じている。
一方、上の桁近似からその像は稠密である。よって自然な写像は全射であり、
体の環準同型の単射性と合わせて **実際の全単射** を得る。

同じ写像の `toAlgebra` を拡大構造として使い、その構造で

\[
\operatorname{finrank}_{F_v}M_w=1
\]

も導いた。別の局所体に対する次数1を流用していない。

## 2. 同じ根の降下と、同じ単元への移送

同じ表示 P の方程式 α^p=ι(b) を取る。全射性で α の M_w への像の原像 t を選ぶ。
上記の可換性により、

\[
\iota_{v,w}(t)=\alpha_w,\qquad
\iota_{v,w}(t^p)=\alpha_w^p=\iota_{v,w}(b_v).
\]

単射性から t^p=b_v である。α≠0 なので t≠0 であり、t∈F_v^× として返す。
ここで F_v^× は完備体の非零元の群である。局所整数環の単元という型と混同しない。
元の b を整数化したり、P や根を選び直したりしていない。

さらに、同じ分解 b=εc^p と同じ局所根 t があれば、

\[
\left(t/\iota_v(c)\right)^p=\iota_v(\varepsilon).
\]

この移送の代数的補題は、ε の整数性や類群消滅を要求しない。
Frey の単元還元との合流では、元の **同じ整数環単元 u** に適用する。

以下は [KummerLocalPower.lean](../../../DkMath/Lib/NumberTheory/KummerLocalPower.lean) の import 以降そのものである。
`#print "file: …"` も含めて単独コピーでコンパイルできる。

```lean
import DkMath.Lib.NumberTheory.NumberFieldCompletionComparison
import DkMath.Lib.NumberTheory.CyclicKummer

#print "file: DkMath.Lib.NumberTheory.KummerLocalPower"

/-!
# 同じ Kummer 根の完備体への降下と同じ定数の局所冪

同じ素点で e=f=1 を満たす場合、自然な完備化写像の全射性で同じ根の像を降ろす。
得られる根の冪が同じ定数の像となることを、可換な埋め込みと単射性で証明する。
別の根や別の定数へ取り替えない。単元還元 b=εc^p への移送も同じ ε を保つ。
-/

namespace DkMath.Lib.NumberTheory.KummerLocalPower

open IsDedekindDomain CyclicKummer NumberFieldCompletionComparison
open scoped NumberField
set_option backward.isDefEq.respectTransparency false
noncomputable section

variable {F M : Type*} [Field F] [NumberField F] [Field M] [NumberField M] [Algebra F M]
    {p : ℕ} (P : Presentation p F M)
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 M))
    [w.asIdeal.LiesOver v.asIdeal]

/-- 同じ根の像を底の完備体の単元へ降ろす。冪等式と上の根との一致をともに返す。 -/
theorem exists_unit_pow_constant_of_ef_eq_one (hp : 1 < p)
    (he : v.asIdeal.ramificationIdx' w.asIdeal = 1)
    (hf : w.asIdeal.inertiaDeg (𝓞 F) = 1) :
    ∃ t : (v.adicCompletion F)ˣ,
      completionMap v w (t : v.adicCompletion F) = algebraMap M (w.adicCompletion M) P.radical ∧
      (t : v.adicCompletion F) ^ p = algebraMap F (v.adicCompletion F) P.constant := by
  obtain ⟨t, ht⟩ := (completionMap_bijective_of_ef_eq_one v w he hf).surjective
    (algebraMap M (w.adicCompletion M) P.radical)
  have ht0 : t ≠ 0 := by
    intro h0
    apply P.radical_ne_zero hp
    apply (algebraMap M (w.adicCompletion M)).injective
    rw [← ht, h0, map_zero, map_zero]
  refine ⟨Units.mk0 t ht0, ht, ?_⟩
  apply (completionMap v w).injective
  change completionMap v w (t ^ p) = completionMap v w (algebraMap F (v.adicCompletion F) P.constant)
  rw [map_pow, ht, ← map_pow, P.radical_pow, completionMap_algebraMap]

omit [NumberField F] in
/-- b=εc^p と同じ局所根 t^p=b から、同じ ε の局所根 t/c を得る。
この代数的移送そのものは整数性・Selmer 所属・類群消滅を要求しない。 -/
theorem unit_pow_of_constant_pow {E : Type*} [Field E] (φ : F →+* E)
    {b ε : F} (c : Fˣ) (t : Eˣ)
    (hdecomp : b = ε * (c : F) ^ p) (hpow : (t : E) ^ p = φ b) :
    ((t / Units.map φ.toMonoidHom c : Eˣ) : E) ^ p = φ ε := by
  rw [Units.val_div_eq_div_val]
  change ((t : E) / φ (c : F)) ^ p = φ ε
  rw [div_pow, hpow, hdecomp, map_mul, map_pow]
  exact mul_div_cancel_right₀ _ (pow_ne_zero _ ((map_ne_zero φ).mpr c.ne_zero))

end
end DkMath.Lib.NumberTheory.KummerLocalPower
```

## 3. Frey の公開入口と同じ ω² 単元類

実装: [FreyCyclotomicKummerLocalPower.lean](../../../DkMath/FLT/FreyCyclotomicKummerLocalPower.lean)。

| 公開定理 | 返すもの | 残す算術入力 |
| --- | --- | --- |
| `residual_kummer_local_radical_at_p` | 同じ w に上げると同じ α の像となる t と t^p=b | 指定された P、従来の Source 等、hp5、lying-over と v ∣ p |
| `residual_kummer_constant_is_local_power_at_p` | 底体の各 v ∣ p での同じ b の局所 p 乗根 | 指定された P、従来の条件、hp5、v ∣ p |
| `residual_kummer_unit_is_local_power_at_p` | 同じ b=uc^p の同じ u の局所 p 乗根 | 上記に加えて同じ u,c と分解の等式 |
| `residual_kummer_unit_weight_square_and_local_power` | 同じ非零 ω² 単元類と全 v ∣ p の局所 p 乗条件 | hp5、hbad、hsurj、類群商の hvanish |

底体の素点だけを入力にする入口では、上の素点を整数環の lying-over で実際に選択する。
その同じ w に既存の有限分解群からの e=f=1 を適用する。
局所次数・完備化写像・根の存在を Frey 固有の仮定へ戻していない。

最後の定理は、前章までの条件付き単元還元が返した同じ u,c を受け取る。
同じ Kummer ベクトルとの一致、同じ非零単元類、同じ ω² 固有条件を保ったまま、
同じ u に対する全ての p 上の局所条件を付ける。
hbad と hvanish を証明済みとしたり、単元類の消滅を結論したりしていない。
hval と hzero は従来通り内部導出し、新たに入力へ追加しない。

次も、実際のソースの import 以降をそのまま掲載している。

```lean
import DkMath.FLT.FreyCyclotomicKummerDecomposition
import DkMath.FLT.FreyCyclotomicKummerSelmer
import DkMath.Lib.NumberTheory.KummerLocalPower
import DkMath.Lib.NumberTheory.CyclotomicKummerDecomposition

#print "file: DkMath.FLT.FreyCyclotomicKummerLocalPower"

/-!
# 同じ Frey Kummer 定数と単元の p 上の局所 p 乗性

同じ有限拡大の e=f=1 を、自然な完備化写像の全射性へ接続する。
同じ α の像を降ろし、同じ b の局所根を得る。底体の各 p 上の素点で述べる入口では
上の素点を lying-over で内部選択する。局所根そのものには hbad、hvanish、hsurj は不要。
最後の単元・重みとの合流では、既存の単元還元の入力をそのまま保持する。
-/

namespace DkMath.FLT.Frey.Source

open DkMath.Lib.Algebra DkMath.Lib.NumberTheory
open EllipticTorsionRepresentation CyclotomicRootModule CyclotomicKernelField
open CyclotomicCharacterField CyclicKummer CyclotomicKummerWeight
open KummerLocalPower NumberFieldCompletionComparison KummerSelmer KummerSelmerExact
open DkMath.Lib.RepresentationTheory
open scoped NumberField Pointwise

noncomputable section

variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance instIsEllipticCyclotomicKummerLocalPower : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic
variable (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (K : AddSubgroup (Points S.rationalCurve)) [Finite K] [IsAddCyclic K]
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ K, pointAction S.rationalCurve σ x ∈ K)
    {m : ℕ} (hm : 1 ≤ m) (hcard : Nat.card K = p ^ m)
    (hbase : pointSubgroup S.rationalCurve p L ≤ K)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)

local instance instRootFieldNumberFieldKummerLocalPower : NumberField (rootField ζ) := rootField_numberField ζ

variable (v : TorsionPreimageQuotient.Quotient p K)
    (P : (letI := extensionAlgebra (S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v) hζ;
      Presentation p (rootField ζ) (S.residualCharacterField L hline hcofixed K hstable hm hcard hbase v)))

include hline hcofixed hstable hm hcard hbase P

/-- 同じ根の像を同じ底の完備体へ降ろす。選択した上の素点との可換性も保持する。 -/
theorem residual_kummer_local_radical_at_p (hp5 : 5 ≤ p) :
    let ψ := S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v
    letI : NumberField (characterField ψ) := characterField_numberField ψ
      (S.residual_cyclic_extension_character_kernel_isOpen L hline hcofixed K hstable hm hcard hbase v)
    letI := extensionAlgebra ψ hζ
    ∀ (vF : IsDedekindDomain.HeightOneSpectrum (𝓞 (rootField ζ)))
      (w : IsDedekindDomain.HeightOneSpectrum (𝓞 (characterField ψ))),
      ∀ hvw : w.asIdeal.LiesOver vF.asIdeal,
      letI := hvw
      (p : 𝓞 (rootField ζ)) ∈ vF.asIdeal →
      ∃ t : (vF.adicCompletion (rootField ζ))ˣ,
        completionMap vF w (t : vF.adicCompletion (rootField ζ)) =
          algebraMap (characterField ψ) (w.adicCompletion (characterField ψ)) P.radical ∧
        (t : vF.adicCompletion (rootField ζ)) ^ p =
          algebraMap (rootField ζ) (vF.adicCompletion (rootField ζ)) P.constant := by
  dsimp only
  let ψ := S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v
  let : NumberField (characterField ψ) := characterField_numberField ψ
    (S.residual_cyclic_extension_character_kernel_isOpen L hline hcofixed K hstable hm hcard hbase v)
  let := extensionAlgebra ψ hζ
  intro vF w hvw
  have := hvw
  intro hpv
  have hef := S.residual_kummer_ramification_and_inertiaDeg_eq_one_at_p
    L hline hcofixed K hstable hm hcard hbase hζ v P hp5 vF w hvw hpv
  exact exists_unit_pow_constant_of_ef_eq_one P vF w (Fact.out : p.Prime).one_lt hef.1 hef.2

/-- p 上の底体の各素点で、元の同じ定数 b は実際の局所体の p 乗となる。
上の素点の存在と e=f=1 は内部供給し、局所次数や局所根を仮定しない。 -/
theorem residual_kummer_constant_is_local_power_at_p (hp5 : 5 ≤ p)
    (vF : IsDedekindDomain.HeightOneSpectrum (𝓞 (rootField ζ)))
    (hpv : (p : 𝓞 (rootField ζ)) ∈ vF.asIdeal) :
    letI := extensionAlgebra
      (S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v) hζ
    ∃ t : (vF.adicCompletion (rootField ζ))ˣ,
      (t : vF.adicCompletion (rootField ζ)) ^ p =
        algebraMap (rootField ζ) (vF.adicCompletion (rootField ζ)) P.constant := by
  let ψ := S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v
  let : NumberField (characterField ψ) := characterField_numberField ψ
    (S.residual_cyclic_extension_character_kernel_isOpen L hline hcofixed K hstable hm hcard hbase v)
  let := extensionAlgebra ψ hζ
  obtain ⟨W, hWmax, hWv⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral vF.asIdeal
    (by rw [(RingHom.injective_iff_ker_eq_bot _).mp
      (FaithfulSMul.algebraMap_injective (𝓞 (rootField ζ)) (𝓞 (characterField ψ)))]; exact bot_le)
  have : W.IsMaximal := hWmax
  have : W.LiesOver vF.asIdeal := ⟨hWv.symm⟩
  let w : IsDedekindDomain.HeightOneSpectrum (𝓞 (characterField ψ)) :=
    ⟨W, inferInstance, Ideal.ne_bot_of_liesOver_of_ne_bot vF.ne_bot W⟩
  obtain ⟨t, _, ht⟩ := S.residual_kummer_local_radical_at_p
    L hline hcofixed K hstable hm hcard hbase hζ v P hp5 vF w inferInstance hpv
  exact ⟨t, ht⟩

/-- 同じ分解 b=εc^p の同じ整数環単元 ε へ、局所根 t/c を移す。 -/
theorem residual_kummer_unit_is_local_power_at_p (hp5 : 5 ≤ p)
    (u : (𝓞 (rootField ζ))ˣ) (c : (rootField ζ)ˣ)
    (hdecomp : letI := extensionAlgebra (S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v) hζ;
      P.constant = algebraMap (𝓞 (rootField ζ)) (rootField ζ) u * (c : rootField ζ) ^ p)
    (vF : IsDedekindDomain.HeightOneSpectrum (𝓞 (rootField ζ)))
    (hpv : (p : 𝓞 (rootField ζ)) ∈ vF.asIdeal) :
    ∃ t : (vF.adicCompletion (rootField ζ))ˣ,
      (t : vF.adicCompletion (rootField ζ)) ^ p =
        algebraMap (rootField ζ) (vF.adicCompletion (rootField ζ))
          (algebraMap (𝓞 (rootField ζ)) (rootField ζ) u) := by
  obtain ⟨t, ht⟩ := S.residual_kummer_constant_is_local_power_at_p
    L hline hcofixed K hstable hm hcard hbase hζ v P hp5 vF hpv
  exact ⟨t / Units.map (algebraMap (rootField ζ) (vF.adicCompletion (rootField ζ))).toMonoidHom c,
    unit_pow_of_constant_pow _ c t hdecomp ht⟩

/-- 元の同じ非零 ω² 単元類に、全 p 上の局所 p 乗条件を同時に付ける。
hbad・hsurj・類群商の hvanish は単元還元のために保持し、hval と hzero は追加しない。 -/
theorem residual_kummer_unit_weight_square_and_local_power
    (hp5 : 5 ≤ p)
    (hbad : ∀ q : ℕ, q.Prime → q ≠ p → 5 ≤ q → (q : ℤ) ∣ S.a * S.b * S.c →
      ((q : ZMod p) = 1 ∨ (q : ZMod p) = -1) →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), ValuationInertia.LiesOverPrime A q →
        ∀ τ ∈ ValuationInertia.inertiaSubgroupIn A ℚ, ∀ y : Points S.rationalCurve,
          p • y ∈ K → pointAction S.rationalCurve τ y - y ∈ K)
    (hsurj : Function.Surjective
      (S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v))
    (hvanish : ∀ a : CyclotomicClassVanishing.ClassModP (rootField ζ) p,
      (∀ γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ),
        CyclotomicClassVanishing.classModPAction p γ a =
          (baseCharacter hζ γ : ZMod p) ^ 2 • a) → a = 0) :
    let ψ := S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v
    letI := extensionAlgebra ψ hζ
    ∃ (u : (NumberField.RingOfIntegers (rootField ζ))ˣ) (c : (rootField ζ)ˣ),
      P.constant = algebraMap (NumberField.RingOfIntegers (rootField ζ)) (rootField ζ) u * (c : rootField ζ) ^ p ∧
      constantVector ψ hζ P = Additive.ofMul
        ((Units.map (algebraMap (NumberField.RingOfIntegers (rootField ζ)) (rootField ζ)).toMonoidHom u :
          (rootField ζ)ˣ) : KummerClass (rootField ζ) p) ∧
      (u : UnitClass (NumberField.RingOfIntegers (rootField ζ)) p) ≠ 1 ∧
      (∀ γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ),
        KummerSelmerUnitEquivariance.unitClassLinearMap p (CyclotomicKummerEquivariance.integerAut γ)
            (Additive.ofMul (u : UnitClass (NumberField.RingOfIntegers (rootField ζ)) p)) =
          (baseCharacter hζ γ : ZMod p) ^ 2 •
            Additive.ofMul (u : UnitClass (NumberField.RingOfIntegers (rootField ζ)) p)) ∧
      ∀ (vF : IsDedekindDomain.HeightOneSpectrum (𝓞 (rootField ζ))),
        (p : 𝓞 (rootField ζ)) ∈ vF.asIdeal →
        ∃ t : (vF.adicCompletion (rootField ζ))ˣ,
          (t : vF.adicCompletion (rootField ζ)) ^ p =
            algebraMap (rootField ζ) (vF.adicCompletion (rootField ζ))
              (algebraMap (𝓞 (rootField ζ)) (rootField ζ) u) := by
  obtain ⟨u, c, hdecomp, hvec, hnz, hw⟩ :=
    S.residual_kummer_unit_weight_square_of_resonant_absorption
      L hline hcofixed K hstable hm hcard hbase hζ v P hp5 hbad hsurj hvanish
  refine ⟨u, c, hdecomp, hvec, hnz, hw, ?_⟩
  intro vF hpv
  exact S.residual_kummer_unit_is_local_power_at_p
    L hline hcofixed K hstable hm hcard hbase hζ v P hp5 u c hdecomp vF hpv

end
end DkMath.FLT.Frey.Source
```

## 4. 回帰検証と依存監査

回帰検証では、ℚ の実際の整数環に (2) を移して素点 v を作る。
恒等拡大に対して e=f=1 を供給し、自然な完備化写像が **完備体全体で恒等写像** と一致すること、
その写像による局所次数が1であることを確認する。
局所整数である分数 1/3 に対しては、大域整数による最初の桁の近似を検証する。

さらに、実際の2進完備体では 2 の平方根が存在しないことを証明する。
同じ主イデアルの指数1と完備化が付値を保存することから、平方根があれば
`2 * log |t| = -1` となり、整数値性に反する。
局所根を無条件に構成する実装になっていないことを検査する負の回帰例である。

分数を使う移送の回帰例は、同じ b=1/4、ε=9、c=1/6、局所根 t=1/2 を追う。
得た t/c が実際に3の像と等しく、その平方が同じ ε の像となることを確認する。
この ε=9 は一般の体の因子としての例であり、ℚ の整数環の単元と呼んでいない。

15宣言の公理報告、15入口の型・コンストラクタ・不透明な証明本体の再帰依存監査、
15入口の公開入力監査を用意した。Frey の局所根では hbad・hvanish・hsurj・he・hf を入力に残さず、
最後の単元との合流では元の hbad・hsurj・hvanish を明示する。

正確な検証結果:
[evidence/validation-note032-cyclotomic-kummer-local-power.txt](evidence/validation-note032-cyclotomic-kummer-local-power.txt)。
全新規6 Lean ファイルと上の2ブロックは import 直後の正確なモジュール表示を保持する。

## 5. 次に残る数学

今回で、同じ b と、単元還元が選ぶ同じ u の p 上の局所 p 乗性を接続した。
残る主要な仕事は次の通りである。

- 共鳴住所の幾何学的吸収 hbad。
- 実際の類群商の算術的 ω² 消滅 hvanish。
- 今回得た局所条件を備える、実際の非零 ω² 単元類の消滅。
- 巡回塔での反復と一般 hno への最終接続。

**一般 hno は未完成である。局所冪の存在と、単元類の算術的消滅は別の段階である。**
