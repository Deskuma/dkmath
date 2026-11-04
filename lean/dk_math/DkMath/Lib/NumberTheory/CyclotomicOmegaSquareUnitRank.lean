/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.NumberFieldUnitPowerDimension
import DkMath.Lib.NumberTheory.CyclotomicPrimaryLogNonzero
import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings
import Mathlib.LinearAlgebra.Trace

#print "file: DkMath.Lib.NumberTheory.CyclotomicOmegaSquareUnitRank"

/-!
# 単元冪商の実際の次元と、同じ ω² 射影子のトレースによる次元判定

Dirichlet の基底と円分体の無限素点数から dim U=(p−1)/2 を無条件に証明する。
有限次元性を確立してから同じ非零固有元を利用し、1≤dim W<p を得る。
同じ射影子の trace=1 と dim W=1 の同値は証明するが、trace=1 自体は残る算術。
-/

namespace DkMath.Lib.NumberTheory.CyclotomicOmegaSquareUnitRank

open NumberFieldUnitPowerDimension CyclotomicKernelField CyclotomicKummerWeight
open CyclotomicPrimaryUnitSpace CyclotomicOmegaSquareProjector CyclotomicPrimaryLogNonzero
open KummerSelmerExact
open scoped NumberField
noncomputable section

variable {p : ℕ} [Fact p.Prime]

/-- 指定した数体・指定した原始根の単元商の、自然数としての正確な次元。 -/
theorem finrank_unitClass_cyclotomic {F : Type*} [Field F] [NumberField F]
    [IsCyclotomicExtension {p} ℚ F] {ζ : F} (hζ : IsPrimitiveRoot ζ p) (hp5 : 5 ≤ p) :
    Module.finrank (ZMod p) (Additive (UnitClass (𝓞 F) p)) = (p - 1) / 2 := by
  have hdiv : p ∣ NumberField.Units.torsionOrder F :=
    NumberField.Units.dvd_torsionOrder_of_isPrimitiveRoot hζ
  rw [finrank_unitClass F hdiv, NumberField.Units.rank,
    NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero F (by omega : 2 < p),
    IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two p,
    Nat.totient_prime (Fact.out : p.Prime)]
  omega

variable {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)
local instance : NumberField (rootField ζ) := rootField_numberField ζ

/-- 同じ rootField の実際の単元冪商は有限次元。trace や rank provider は不要。 -/
theorem unitClass_finite : Module.Finite (ZMod p) (Additive (UnitClass (𝓞 (rootField ζ)) p)) :=
  inferInstance

/-- 既存の同じ固有空間も実際に有限次元である。 -/
theorem weightSquareSpace_finite : Module.Finite (ZMod p) (weightSquareSpace hζ) :=
  inferInstance

include hζ in
/-- 同じ原始根で生成した体における、実際の単元商の次元公式。 -/
theorem root_unitClass_finrank (hp5 : 5 ≤ p) :
    Module.finrank (ZMod p) (Additive (UnitClass (𝓞 (rootField ζ)) p)) = (p - 1) / 2 := by
  let := rootField_isCyclotomic hζ
  exact finrank_unitClass_cyclotomic (baseRoot_primitive hζ) hp5

/-- 有限次元性を確立した後、前段の同じ非零固有元から正の次元を得る。 -/
theorem weightSquareSpace_finrank_pos (hp5 : 5 ≤ p) :
    0 < Module.finrank (ZMod p) (weightSquareSpace hζ) := by
  exact Module.finrank_pos_iff_exists_ne_zero.mpr
    ⟨projectedCyclotomicUnit hζ hp5, projectedCyclotomicUnit_ne_zero hζ hp5⟩

/-- 固有空間の自然数次元の上界。位数 p の法での比較と混同しない。 -/
theorem weightSquareSpace_finrank_le (hp5 : 5 ≤ p) :
    Module.finrank (ZMod p) (weightSquareSpace hζ) ≤ (p - 1) / 2 := by
  rw [← root_unitClass_finrank hζ hp5]
  exact Submodule.finrank_le _

/-- 標数 p の trace から自然数次元を復元するための厳密な上界。 -/
theorem weightSquareSpace_finrank_lt_prime (hp5 : 5 ≤ p) :
    Module.finrank (ZMod p) (weightSquareSpace hζ) < p := by
  have := weightSquareSpace_finrank_le hζ hp5
  omega

/-- 同じ冪等射影子の trace は、同じ既存の固有空間の次元の mod p 像。 -/
theorem trace_omegaSquareProjector_eq_finrank :
    LinearMap.trace (ZMod p) _ (omegaSquareProjector hζ) =
      (Module.finrank (ZMod p) (weightSquareSpace hζ) : ZMod p) := by
  have hid : IsIdempotentElem (omegaSquareProjector hζ) := omegaSquareProjector_idempotent hζ
  have h := (LinearMap.IsIdempotentElem.isProj_range _ hid).trace
  rwa [omegaSquareProjector_range] at h

/-- trace=1 の算術的証明が得られれば、mod p の一致から自然数の次元1を復元する。 -/
theorem weightSquareSpace_finrank_eq_one_of_trace (hp5 : 5 ≤ p)
    (htrace : LinearMap.trace (ZMod p) _ (omegaSquareProjector hζ) = 1) :
    Module.finrank (ZMod p) (weightSquareSpace hζ) = 1 := by
  rw [trace_omegaSquareProjector_eq_finrank] at htrace
  have h := congrArg ZMod.val htrace
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (weightSquareSpace_finrank_lt_prime hζ hp5),
    ZMod.val_one] at h
  exact h

/-- 未解決の trace 値の計算と、従来の hrank の正確な同値。 -/
theorem trace_eq_one_iff_finrank_eq_one (hp5 : 5 ≤ p) :
    LinearMap.trace (ZMod p) _ (omegaSquareProjector hζ) = 1 ↔
      Module.finrank (ZMod p) (weightSquareSpace hζ) = 1 := by
  constructor
  · exact weightSquareSpace_finrank_eq_one_of_trace hζ hp5
  · intro hrank
    rw [trace_omegaSquareProjector_eq_finrank, hrank, Nat.cast_one]

/-- 同じ実際の射影子の trace を明示入力として、証明済みの非零検出と合成する。 -/
theorem primaryWeightSquareSpace_eq_bot_of_trace (hp5 : 5 ≤ p)
    (htrace : LinearMap.trace (ZMod p) _ (omegaSquareProjector hζ) = 1) :
    primaryWeightSquareSpace hζ = ⊥ :=
  primaryWeightSquareSpace_eq_bot_of_rank_one hζ hp5
    (weightSquareSpace_finrank_eq_one_of_trace hζ hp5 htrace)

end
end DkMath.Lib.NumberTheory.CyclotomicOmegaSquareUnitRank
