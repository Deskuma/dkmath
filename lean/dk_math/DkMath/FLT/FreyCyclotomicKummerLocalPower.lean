/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

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
