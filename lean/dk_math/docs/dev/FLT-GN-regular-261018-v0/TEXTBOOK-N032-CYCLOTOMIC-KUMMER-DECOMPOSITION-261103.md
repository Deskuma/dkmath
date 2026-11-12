# NOTE-032 教科書: 同じ Frey Kummer 根の有限分解群と e=f=1

日付: 2026-11-03。対象は同じ `S,L,K,m,v,ψ,P,F,M,α,b` である。

今回の到達点は、既存の **p 上の絶対分解群固定性** から、元の有限拡大の
**実際の有限分解群の自明性と e=f=1** への接続である。
`hbad`、類群消滅 `hvanish`、指標全射性 `hsurj` は新しい Frey 公開定理の入力にない。
指定された表示 `P` の存在は入力のままである。非分裂からその表示を構成する既存経路を省略していない。

**局所完備体で同じ b の p 乗根 t を構成したとは主張しない。一般 hno も未完成である。**

## 1. なぜ慣性の持ち上げだけでは足りないか

前章の Selmer 所属は有限相対慣性の自明性を使った。次の局所 p 乗性へ向かうには、
剰余体にも非自明に作用し得る **分解群全体** を扱う必要がある。

有限数体の整数環の素点を w、相対拡大を M/F とすると、

\[
I_w\subseteq D_w,\qquad |D_w|=|I_w|f(w/v),\qquad |I_w|=e(w/v).
\]

I_w=1 だけでは f=1 は導けない。既存の p 上の固定性は絶対分解群について成立しているので、
その強い入力を慣性に弱めず、有限分解群へ接続する。

## 2. 同じ有限体への制限を保つ絶対分解群持ち上げ

実装: [AbsoluteDecompositionLift.lean](../../../DkMath/Lib/NumberTheory/AbsoluteDecompositionLift.lean)。

M/ℚ が有限 Galois、w が M の整数環の極大イデアル、p∈w とする。
有限自己同型 τ が w を安定化するとき、次の実際の存在定理を証明した。

\[
\exists\sigma,A,\qquad
\sigma|_M=\tau,\quad A\text{ は }p\text{ 上},\quad
\sigma\in D_A(\overline{\mathbb Q}/\mathbb Q).
\]

1. 整数閉包 ℤ̄ に w の上の極大イデアル W を取る。
2. τ の任意の絶対延長 σ₀ を取る。τ が w を安定化するので、σ₀W と W の M への収縮は等しい。
3. Gal(ℚ̄/M) の素点上の推移性で σ₀ を補正する。この補正は M を固定するので、制限は同じ τ のままである。
4. W を中心とする付値環 A を取る。a∈A は x/s（x,s∈ℤ̄、s∉W）と書ける。
   σW=W により σs∉W、従って σs は A の単元で、σa∈A となる。
   σ⁻¹ にも同じ議論を適用して σA=A を得る。

慣性持ち上げにある剰余体作用の打ち消しは行わない。
返す A は同じ有理素数 p 上にあり、元の有限元への制限は明示的な等式として保持する。
既存の整数閉包持ち上げの前半と同じ profinite 不変式論の証明を使い、既存ファイルは変更していない。
著作権・上流出典は新規ソースにも保存した。

## 3. 絶対元から同じ相対元と同じ根へ戻す

実装: [CyclotomicKummerDecomposition.lean](../../../DkMath/Lib/NumberTheory/CyclotomicKummerDecomposition.lean)。

F=ℚ(ζₚ)、M=characterField ψ とし、τ∈D_w(M/F) を取る。
上の持ち上げは、相対元をまず ℚ 自己同型として見た τ に適用する。

\[
\sigma|_M=\tau
\Longrightarrow\sigma(\zeta_p)=\zeta_p
\Longrightarrow\sigma\in\ker\chi_p.
\]

実際の `kernelEquiv_mem_decomposition_iff` で、同じ A の F 上の分解群所属へ移す。
そこで既存の根の固定性を使い、制限の等式を **同じ P.radical** へ適用することで τα=α を得る。
別の根、別の表示、別の数体を選んでいない。定数 b を整数化して取り替える操作もない。

## 4. 生成性から D_w=1 と e=f=1

F(α)=M なので、α を固定する F 自己同型は恒等である。
`Presentation.algHom_ext` はこの生成性を使う。
分解群の自明性から慣性も自明となり、上記の実際の位数公式で e=f=1 を得る。

次のブロックは [KummerDecomposition.lean](../../../DkMath/Lib/NumberTheory/KummerDecomposition.lean)
の import 以降をそのまま掲載した。単独コピーでコンパイルできる。
`#print` は出典を同定する必須情報として保持する。

```lean
import DkMath.Lib.NumberTheory.KummerLocalValuation

#print "file: DkMath.Lib.NumberTheory.KummerDecomposition"

/-!
# 同じ生成根の分解群固定性から実際の e=f=1 へ

分解群が根を固定するなら、単純生成性により分解群そのものが自明となる。
有限数体では慣性群の位数と剰余次数の積の公式から、同じ素点の e=f=1 を得る。
これは完備化の次数との比較をまだ含まない。
-/

namespace DkMath.Lib.NumberTheory.KummerDecomposition
open CyclicKummer IsDedekindDomain
open scoped NumberField Pointwise
set_option backward.isDefEq.respectTransparency false
noncomputable section

variable {F M : Type*} [Field F] [Field M] [Algebra F M]
    {p : ℕ} (P : Presentation p F M)

/-- 生成根を固定する部分群は自明。分解群・慣性群の両方に使える代数的核心。 -/
theorem subgroup_eq_bot_of_fixes_radical (H : Subgroup (M ≃ₐ[F] M))
    (hfix : ∀ σ ∈ H, σ P.radical = P.radical) : H = ⊥ := by
  apply bot_unique
  intro σ hσ
  have he : σ = 1 := by
    apply DFunLike.ext
    intro a
    exact DFunLike.congr_fun
      (P.algHom_ext (f := σ.toAlgHom) (g := AlgHom.id F M) (hfix σ hσ)) a
  rw [he]
  exact Subgroup.one_mem ⊥

variable [NumberField F] [NumberField M] [IsGalois F M]
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 M))
    [w.asIdeal.LiesOver v.asIdeal]

/-- 同じ有限分解群の固定性から、同じ素点の実際の分岐指数と剰余次数が1となる。
局所完備化の次数を仮定せず、Mathlib の整数環の位数公式で計算する。 -/
theorem ramification_and_inertiaDeg_eq_one_of_decomposition_fixes_radical
    (hfix : ∀ σ : M ≃ₐ[F] M,
      σ ∈ MulAction.stabilizer (M ≃ₐ[F] M) w.asIdeal → σ P.radical = P.radical) :
    v.asIdeal.ramificationIdx' w.asIdeal = 1 ∧ w.asIdeal.inertiaDeg (𝓞 F) = 1 := by
  let : FiniteDimensional F M := Module.Finite.of_restrictScalars_finite ℚ F M
  let : IsGaloisGroup (M ≃ₐ[F] M) (𝓞 F) (𝓞 M) :=
    IsGaloisGroup.of_isFractionRing (M ≃ₐ[F] M) (𝓞 F) (𝓞 M) F M
  let : Finite (𝓞 F ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  have hi : ∀ σ : M ≃ₐ[F] M, σ ∈ w.asIdeal.inertia (M ≃ₐ[F] M) →
      σ P.radical = P.radical := fun σ hσ => hfix σ (Ideal.inertia_le_stabilizer w.asIdeal hσ)
  have hd := subgroup_eq_bot_of_fixes_radical P
    (MulAction.stabilizer (M ≃ₐ[F] M) w.asIdeal) hfix
  have ht := subgroup_eq_bot_of_fixes_radical P (w.asIdeal.inertia (M ≃ₐ[F] M)) hi
  refine ⟨KummerLocalValuation.ramification_eq_one_of_inertia_fixes_radical P v w hi, ?_⟩
  have hc := Ideal.card_stabilizer_eq_card_inertia_mul_finrank
    (G := M ≃ₐ[F] M) v.asIdeal w.asIdeal
  simpa only [hd, ht, Nat.card_unique, one_mul] using hc.symm

end
end DkMath.Lib.NumberTheory.KummerDecomposition
```

## 5. Frey の公開入口

次は [FreyCyclotomicKummerDecomposition.lean](../../../DkMath/FLT/FreyCyclotomicKummerDecomposition.lean)
の import 以降そのものである。
数体構造は同じ指標の開核定理から内部供給する。
`P` は結論の分解群等式に文字として現れなくても、根の生成性に必要なので公開入力として明示的に保つ。
素点 w に p が属すること、v と w が同じ lying-over にあることも保持する。

```lean
import DkMath.FLT.FreyCyclotomicKummer
import DkMath.Lib.NumberTheory.CyclotomicKummerDecomposition

#print "file: DkMath.FLT.FreyCyclotomicKummerDecomposition"

/-!
# 同じ Frey Kummer 拡大の p 上の有限分解群は自明

同じ S,L,K,m,v,P を保ち、p 上の絶対分解群固定性を有限整数環の素点へ移す。
共鳴住所の吸収 hbad、類群消滅 hvanish、指標の全射性 hsurj は要求しない。
同じ有限拡大に対する D_w=1 と e=f=1 を結論する。
完備化への降下と局所 p 乗性は次の比較の課題である。
-/

namespace DkMath.FLT.Frey.Source

open DkMath.Lib.Algebra DkMath.Lib.NumberTheory
open EllipticTorsionRepresentation CyclotomicRootModule CyclotomicKernelField
open CyclotomicCharacterField CyclicKummer CyclotomicKummerWeight
open KummerDecomposition DkMath.Lib.RepresentationTheory
open scoped NumberField Pointwise

set_option backward.isDefEq.respectTransparency false
noncomputable section

variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance instIsEllipticCyclotomicKummerDecomposition : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic
variable (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (K : AddSubgroup (Points S.rationalCurve)) [Finite K] [IsAddCyclic K]
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ K, pointAction S.rationalCurve σ x ∈ K)
    {m : ℕ} (hm : 1 ≤ m) (hcard : Nat.card K = p ^ m)
    (hbase : pointSubgroup S.rationalCurve p L ≤ K)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)

local instance instRootFieldNumberFieldKummerDecomposition : NumberField (rootField ζ) := rootField_numberField ζ

variable (v : TorsionPreimageQuotient.Quotient p K)
    (P : (letI := extensionAlgebra (S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v) hζ;
      Presentation p (rootField ζ) (S.residualCharacterField L hline hcofixed K hstable hm hcard hbase v)))

include hline hcofixed hstable hm hcard hbase P

/-- 同じ p 上の有限分解群は同じ生成根を固定する。
数体構造も既存の開核定理から内部で供給する。 -/
theorem residual_kummer_finite_decomposition_fixes_radical_at_p (hp5 : 5 ≤ p) :
    let ψ := S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v
    let : NumberField (characterField ψ) := characterField_numberField ψ
      (S.residual_cyclic_extension_character_kernel_isOpen L hline hcofixed K hstable hm hcard hbase v)
    let := extensionAlgebra ψ hζ
    ∀ (w : IsDedekindDomain.HeightOneSpectrum (𝓞 (characterField ψ))),
      (p : 𝓞 (characterField ψ)) ∈ w.asIdeal →
      ∀ τ : (characterField ψ) ≃ₐ[rootField ζ] (characterField ψ),
        τ ∈ MulAction.stabilizer ((characterField ψ) ≃ₐ[rootField ζ] (characterField ψ)) w.asIdeal →
          τ P.radical = P.radical := by
  dsimp only
  let ψ := S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v
  let : NumberField (characterField ψ) := characterField_numberField ψ
    (S.residual_cyclic_extension_character_kernel_isOpen L hline hcofixed K hstable hm hcard hbase v)
  let := extensionAlgebra ψ hζ
  intro w hpw
  apply CyclotomicKummerDecomposition.finite_decomposition_fixes_radical_at_p ψ hζ
    (S.residual_cyclic_extension_character_kernel_isOpen L hline hcofixed K hstable hm hcard hbase v)
    (S.residual_cyclic_extension_character_conjugate L hline hcofixed K hstable hm hcard hbase v) P ?_ w hpw
  exact S.residual_kummer_radical_decomposition_fixed_at_p
    L hline hcofixed K hstable hm hcard hbase hζ v P hp5

/-- p 上の実際の有限分解群が自明であることを、同じ根の生成性で証明する。 -/
theorem residual_kummer_decomposition_eq_bot_at_p (hp5 : 5 ≤ p) :
    let ψ := S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v
    let : NumberField (characterField ψ) := characterField_numberField ψ
      (S.residual_cyclic_extension_character_kernel_isOpen L hline hcofixed K hstable hm hcard hbase v)
    let := extensionAlgebra ψ hζ
    ∀ (w : IsDedekindDomain.HeightOneSpectrum (𝓞 (characterField ψ))),
      (p : 𝓞 (characterField ψ)) ∈ w.asIdeal →
      MulAction.stabilizer ((characterField ψ) ≃ₐ[rootField ζ] (characterField ψ)) w.asIdeal = ⊥ := by
  dsimp only
  let ψ := S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v
  let : NumberField (characterField ψ) := characterField_numberField ψ
    (S.residual_cyclic_extension_character_kernel_isOpen L hline hcofixed K hstable hm hcard hbase v)
  let := extensionAlgebra ψ hζ
  intro w hpw
  exact subgroup_eq_bot_of_fixes_radical P _
    (S.residual_kummer_finite_decomposition_fixes_radical_at_p
      L hline hcofixed K hstable hm hcard hbase hζ v P hp5 w hpw)

/-- p 上の同じ v,w について分岐指数と剰余次数がともに1。
hbad や Selmer 所属を経由せず、分解群固定性から直接導く。 -/
theorem residual_kummer_ramification_and_inertiaDeg_eq_one_at_p (hp5 : 5 ≤ p) :
    let ψ := S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v
    let : NumberField (characterField ψ) := characterField_numberField ψ
      (S.residual_cyclic_extension_character_kernel_isOpen L hline hcofixed K hstable hm hcard hbase v)
    let := extensionAlgebra ψ hζ
    ∀ (vF : IsDedekindDomain.HeightOneSpectrum (𝓞 (rootField ζ)))
      (w : IsDedekindDomain.HeightOneSpectrum (𝓞 (characterField ψ))),
      w.asIdeal.LiesOver vF.asIdeal → (p : 𝓞 (rootField ζ)) ∈ vF.asIdeal →
      vF.asIdeal.ramificationIdx' w.asIdeal = 1 ∧ w.asIdeal.inertiaDeg (𝓞 (rootField ζ)) = 1 := by
  dsimp only
  let ψ := S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v
  let : NumberField (characterField ψ) := characterField_numberField ψ
    (S.residual_cyclic_extension_character_kernel_isOpen L hline hcofixed K hstable hm hcard hbase v)
  let := extensionAlgebra ψ hζ
  intro vF w hvw hpv
  apply CyclotomicKummerDecomposition.ramification_and_inertiaDeg_eq_one_at_p ψ hζ
    (S.residual_cyclic_extension_character_kernel_isOpen L hline hcofixed K hstable hm hcard hbase v)
    (S.residual_cyclic_extension_character_conjugate L hline hcofixed K hstable hm hcard hbase v) P ?_ vF w hvw hpv
  exact S.residual_kummer_radical_decomposition_fixed_at_p
    L hline hcofixed K hstable hm hcard hbase hζ v P hp5

end
end DkMath.FLT.Frey.Source
```

## 6. 検証と数学的境界

回帰例は、実際の ℚ(√2) の整数環に (2) 上の素点を lying-over で選ぶ。
ℚ の整数環は ℤ と定義上同一ではないので、`Rat.ringOfIntegersEquiv` で同じ (2) を明示的に移す。
同じ平方定数 2 の主イデアル指数が1であることから、その素点では e≠1、従って D≠1 と証明する。
**Kummer 方程式の存在だけで分解群の自明性は結論できない** ことを検査している。
恒等拡大の同じ (2) では e=f=1 の双方を確認する。

11公開宣言の `#print axioms`、型・コンストラクタ・不透明な証明本体を含む再帰監査、
公開入力監査を通常のテスト入口に含める。正確な実行結果は
[evidence/validation-note032-cyclotomic-kummer-decomposition.txt](evidence/validation-note032-cyclotomic-kummer-decomposition.txt)
に記録する。

残る完備化の接続は、同じ w/v に対して

\[
[M_w:F_v]=|D_w|=1
\quad\Longrightarrow\quad
\alpha\text{ の像が }F_v\text{ から来る}
\quad\Longrightarrow\quad
\exists t\in F_v^\times,\ t^p=b
\]

を **実際の埋め込みと完備化** で形式化することである。
今回の e=f=1 を、その未実装の比較定理や t の代用品にしてはいけない。
さらに同じ b=εc^p に対して ε=(t/c)^p を移し、同じ単元類の局所条件を得る作業も残る。
共鳴住所の hbad、類群商の算術的 ω² 消滅、局所条件付き単元消滅、巡回塔反復も未解決である。
