/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.ThreeEisensteinBridge
import DkMath.FLT.Three.PositiveCubicNormalization

/-!
# GN・Kummer 経由の FLT3 再形式化実験

既存 FLT3 の mod 9 による向きの選択・整数での冪配分を再利用する。
その **同じ** 剥離商の三乗根を、円分イデアルと Kummer 単元合同の経路で
作り直す。以後は既存の座標因子分配・符号選択・積測度の減少を再利用する。
最後の強帰納法はこの新しい降下を呼ぶ。完成済み FLT3 定理を呼ばない。
-/

open scoped NumberField

namespace DkMath.FLT.Kummer

open DkMath.FLT.Three DkMath.NumberTheory.TraceOneQuadratic

/-- 指定された剥離商と三乗根を、既存の exact-cube 型へ組み込む。
従来のセクター排除を呼ばず、セクターを初めから `one` として構成する。
第二座標から積恒等式、ノルムから三乗根のノルムを導く。 -/
def eisensteinExactCubePacket_of_stripped_cube {a b c : ℕ}
    (q : EisensteinRamifierStrippedPacket a b c) (θ : EisensteinInt)
    (hθ : q.beta = θ ^ 3) : EisensteinExactCubePacket a b c := by
  let cp := eisensteinConjugateCoprimePacket_of_stripped q
  let up : EisensteinCubeUpToUnitPacket a b c :=
    ⟨cp, 1, θ, by
      change q.beta = (1 : EisensteinInt) * θ ^ 3
      simpa only [one_mul] using hθ⟩
  let sp : EisensteinCubeSectorPacket a b c :=
    ⟨up, .one, θ, by
      change q.beta = (1 : EisensteinInt) * θ ^ 3
      simpa only [one_mul] using hθ⟩
  refine {
    sectorPacket := sp
    sector_one := rfl
    beta_eq_cube := hθ
    coordinate_product := ?_
    coordinate_norm := EisensteinCubeSectorPacket.gamma_norm_eq_B sp }
  have hs : (θ ^ 3).snd = 3 * (q.powerSplit.A : ℤ) ^ 3 := by
    rw [← hθ]
    exact q.beta_snd
  have hc := eisenstein_cube_snd θ.fst θ.snd
  change (θ ^ 3).snd = _ at hc
  rw [hc] at hs
  change θ.fst * θ.snd * (θ.fst + θ.snd) = (q.powerSplit.A : ℤ) ^ 3
  linarith

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {3} ℚ K] {ζ : K}

/-- 元の原始解から **実際に** GN・Kummer の三乗根を供給して降下因子源を作る。
`splitWithPacket.2` が元の向きの来歴を保証する。A、B、β は選び直さない。 -/
noncomputable def gnEisensteinDescentFactorSource (hζ : IsPrimitiveRoot ζ 3)
    {a b c : ℕ} (source : PrimitiveCubicPack a b c) :
    EisensteinDescentFactorSource a b c := by
  let origin := signedThreeAdicOriginPacket_of_primitive_solution
    source.hx source.hy source.hz source.coprime_xy source.equation
  let splitWithPacket := signedThreeAdicPowerSplit_with_packet origin.packet
  let split := splitWithPacket.1
  let stripped := eisensteinRamifierStrippedPacket_of_powerSplit split
  let hroot := exists_cube_eq_stripped_beta hζ stripped
  let θ := Classical.choose hroot
  let exactCube := eisensteinExactCubePacket_of_stripped_cube stripped θ (Classical.choose_spec hroot)
  refine {
    origin := origin
    exactCube := exactCube
    A := split.A
    B := split.B
    r := θ.fst
    s := θ.snd
    A_pos := split.A_pos
    B_pos := split.B_pos
    coprime_A_B := split.coprime_A_B
    three_not_dvd_B := split.three_not_dvd_B
    distinguished_eq := ?_
    product_eq := exactCube.coordinate_product
    norm_eq := ?_ }
  · rw [← splitWithPacket.2]
    exact split.distinguished_eq
  · have hn := exactCube.coordinate_norm
    change DkMath.NumberTheory.TraceOneQuadratic.norm θ = (split.B : ℤ) at hn
    simpa only [DkMath.NumberTheory.TraceOneQuadratic.norm, neg_mul, one_mul, sub_neg_eq_add] using hn

/-- GN・Kummer で得た因子を、既存の三因子への冪配分と符号選択へ渡す。
新しい正の原始解と `x*y*z < a*b*c` が共に構成される。 -/
noncomputable def gnPrimitiveCubicStrictDescent (hζ : IsPrimitiveRoot ζ 3)
    {a b c : ℕ} (source : PrimitiveCubicPack a b c) :
    PrimitiveCubicStrictDescent a b c :=
  primitiveCubicStrictDescent_of_factors source
    (eisensteinSignedCubeFactors_of_source (gnEisensteinDescentFactorSource hζ source))

/-- 元の解から、GN・Kummer の三乗抽出を経由する厳密に小さい原始解。 -/
theorem exists_smaller_primitiveCubicPack_via_GN (hζ : IsPrimitiveRoot ζ 3)
    {a b c : ℕ} (source : PrimitiveCubicPack a b c) :
    ∃ x y z : ℕ, PrimitiveCubicPack x y z ∧ x * y * z < a * b * c := by
  let d := gnPrimitiveCubicStrictDescent hζ source
  exact ⟨d.x, d.y, d.z, d.next, d.measure_lt⟩

/-- 新しい GN 降下を積測度に関する強帰納法で閉じる。
既存の `primitiveCubicPack_false` を使用しない。 -/
theorem primitiveCubicPack_false_via_GN (hζ : IsPrimitiveRoot ζ 3)
    {a b c : ℕ} (source : PrimitiveCubicPack a b c) : False := by
  have noAt : ∀ n : ℕ, ∀ {a b c : ℕ},
      PrimitiveCubicPack a b c → a * b * c = n → False := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a b c p hp
      obtain ⟨x, y, z, next, hlt⟩ := exists_smaller_primitiveCubicPack_via_GN hζ p
      exact ih (x * y * z) (by simpa [hp] using hlt) next rfl
  exact noAt (a * b * c) source rfl

/-- 正の自然数に対する FLT3 の再形式化。
gcd 正規化のみ既存入口を使い、不可能性は GN・Kummer 経由の新しい降下で証明する。
円分体を選ぶ引数は数学的な追加仮定ではなく、直後の定理で具体的に供給する。 -/
theorem fermatThree_no_positive_solution_via_GN_in (hζ : IsPrimitiveRoot ζ 3)
    (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  intro heq
  obtain ⟨a', b', c', source⟩ :=
    exists_primitiveCubicPack_of_positive_solution ha hb hc heq
  exact primitiveCubicPack_false_via_GN hζ source

set_option backward.isDefEq.respectTransparency false in
/-- 具体的な三次円分体を選択した、追加仮定のない GN 版 FLT3。
これは三次での再形式化実験の終点であり、一般の正則素数の FLT は主張しない。 -/
theorem fermatThree_no_positive_solution_via_GN
    (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  let : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) :=
    CyclotomicField.isCyclotomicExtension 3 ℚ
  exact fermatThree_no_positive_solution_via_GN_in
    (IsCyclotomicExtension.zeta_spec 3 ℚ (CyclotomicField 3 ℚ)) a b c ha hb hc

end DkMath.FLT.Kummer
