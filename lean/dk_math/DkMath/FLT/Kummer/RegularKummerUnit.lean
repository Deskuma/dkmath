/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.RegularKummer.KummersLemma.KummersLemma
import DkMath.FLT.Kummer.GNKummerUnitAdapter

#print "file: DkMath.FLT.Kummer.RegularKummerUnit"

/-!
# 正則性から一般 Kummer 単元 criterion を供給する

整数合同を満たす単元の p 乗根は、GN の代数恒等式からは得られない。
下層の補助拡大・不分岐性・Hilbert 94 の証明に、類数と p の互いに素性を渡す。
このファイルはその結論を、既存 State 降下が要求する命題型へ接続する。
指数固有の単元群分類や、完成済み FLT の不存在定理は入力しない。
-/

namespace DkMath.FLT.Kummer

open scoped NumberField

/-- 環同型は整数合同と単元群内の冪根を同時に輸送する。
ノルムや類だけを一致させるのではなく、元の単元を逆写像で送り、その同じ元の根を
順写像で戻す。従って整数環のモデルや原始根の選択を変更しても criterion を再利用できる。 -/
theorem kummer_unit_power_criterion_of_ringEquiv
    {R S : Type*} [CommRing R] [CommRing S] {p : ℕ}
    (e : R ≃+* S) (h : KummerUnitPowerCriterion R p) : KummerUnitPowerCriterion S p := by
  intro u hu
  let v := Units.map e.symm.toMonoidHom u
  have hv : ∃ n : ℤ, (p : R) ∣ (v : R) - (n : R) := by
    obtain ⟨n, hn⟩ := hu
    refine ⟨n, ?_⟩
    change (p : R) ∣ e.symm (u : S) - (n : R)
    have hm := map_dvd e.symm.toRingHom hn
    change e.symm (p : S) ∣ e.symm ((u : S) - (n : S)) at hm
    simpa only [map_natCast, map_sub, map_intCast] using hm
  obtain ⟨w, hw⟩ := h v hv
  have he : Units.map e.toMonoidHom v = u := by
    apply Units.ext
    change e (e.symm (u : S)) = (u : S)
    exact e.apply_symm_apply _
  refine ⟨Units.map e.toMonoidHom w, ?_⟩
  calc
    u = Units.map e.toMonoidHom v := he.symm
    _ = Units.map e.toMonoidHom (w ^ p) := congrArg (Units.map e.toMonoidHom) hw
    _ = _ := map_pow _ _ _

/-- 奇素数 p が類数を割らなければ、整数と mod p で合同な単元は単元群内の p 乗である。

証明核は Kummer 拡大を使う。p 乗根がなければ `X^p-u` は既約で、
次数 p の巡回拡大を作る。整数合同を高い分岐合同へ強めると、この拡大は不分岐になる。
Hilbert 94 はその次数が類数を割ると結論するため、正則性と矛盾する。
得た体内の根は整性から整数環へ戻り、冪が単元なので根も単元となる。

ここで類数との互いに素性は明示的な仮定であり、すべての素数に対する criterion を
無条件に宣言しているわけではない。 -/
theorem regular_kummer_unit_power_criterion
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    (hp : p ≠ 2) (hreg : Nat.Coprime p (Fintype.card (ClassGroup (𝓞 K)))) :
    KummerUnitPowerCriterion (𝓞 K) p := by
  intro u hu
  let L := CyclotomicField p ℚ
  let : IsCyclotomicExtension {p} ℚ L := CyclotomicField.isCyclotomicExtension p ℚ
  let e : 𝓞 L ≃+* 𝓞 K := NumberField.RingOfIntegers.mapRingEquiv
    (IsCyclotomicExtension.algEquiv {p} ℚ L K).toRingEquiv
  have hcard : Fintype.card (ClassGroup (𝓞 L)) = Fintype.card (ClassGroup (𝓞 K)) :=
    Fintype.card_congr (ClassGroup.mulEquiv e).toEquiv
  have hregL : Nat.Coprime p (Fintype.card (ClassGroup (𝓞 L))) := by
    rw [hcard]
    exact hreg
  exact kummer_unit_power_criterion_of_ringEquiv e
    (DkMath.Lib.NumberTheory.RegularKummer.eq_pow_prime_of_unit_of_congruent hp hregL) u hu

end DkMath.FLT.Kummer
