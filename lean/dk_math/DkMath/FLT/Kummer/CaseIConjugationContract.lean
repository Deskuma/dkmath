/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.Data.Int.ModEq

#print "file: DkMath.FLT.Kummer.CaseIConjugationContract"

/-!
# Case I の固定する位相契約

`Packet` は二位相・隣接条件・整数 p による可除性だけを保持する。
共役・CM 単元・正則性の証明方法は型に含めない。古典的供給は
`CaseIConjugationPacket`、GN の因子抽出との合成は `GNCaseIContract` に置く。

`FactorPacketProvider` は同じ因子の単元倍 p 乗表示を入力する交換点、
`SolutionPacketProvider` は原始的 Case I 方程式を入力する交換点である。
いずれも証明を渡すための命題であり、instance や新たな公理ではない。
GN 由来の代替証明が得られた場合も、Packet の型や終端を変更する必要はない。
-/

@[expose] public section

namespace DkMath.FLT.Kummer.CaseIConjugation

open scoped NumberField

/-- 共役から得られる4項関係の固定型。既存の名前・引数・4フィールドを維持する。
出所の証明方法を含めず、位相の衝突と隣接条件を失わずに運ぶ。 -/
structure Packet {p : ℕ} {K : Type*} [Field K] (ζ : 𝓞 K) (a b : ℤ) where
  k₁ : Fin p
  k₂ : Fin p
  adjacent : Int.ModEq p (k₂ : ℤ) ((k₁ : ℤ) - 1)
  divisible : (p : 𝓞 K) ∣ (a : 𝓞 K) + b * ζ - a * ζ ^ (k₁ : ℕ) - b * ζ ^ (k₂ : ℕ)

/-- 因子表示から Packet を供給する契約。同じ u・α・a・b・ζ を入力する。
現在は古典的共役によって証明するが、契約自体は共役を要求しない。 -/
def FactorPacketProvider {p : ℕ} {K : Type*} [Field K] (ζ : 𝓞 K) : Prop :=
  ∀ {a b : ℤ} {u : (𝓞 K)ˣ} {α : 𝓞 K},
    (u : 𝓞 K) * α ^ p = a + ζ * b → Nonempty (Packet (p := p) ζ a b)

/-- 原始的 Case I 方程式から Packet を供給する契約。
類群条件の証明方法を型に固定せず、供給側が必要な算術入力を閉じる。
反例排除や State 降下そのものを仮定する契約ではない。 -/
def SolutionPacketProvider {p : ℕ} {K : Type*} [Field K] (ζ : 𝓞 K) : Prop :=
  ∀ {a b c : ℤ}, a ^ p + b ^ p = c ^ p → IsCoprime a b →
    ¬ (p : ℤ) ∣ a * b * c → Nonempty (Packet (p := p) ζ a b)


end DkMath.FLT.Kummer.CaseIConjugation
