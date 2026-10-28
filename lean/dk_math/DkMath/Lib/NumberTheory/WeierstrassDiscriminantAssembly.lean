/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from the delta_identity argument in
S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.lean,
blob 0c42a9282f1033d6d64cc213bb1f7c7c52b17d1e.
-/
import DkMath.Lib.NumberTheory.WeierstrassDiscriminantRoots
import DkMath.Lib.NumberTheory.WeierstrassTwoTorsionTranslate
import Mathlib.RingTheory.Valuation.ValuationSubring

#print "file: DkMath.Lib.NumberTheory.WeierstrassDiscriminantAssembly"

/-!
# 三組の根の差から判別式積公式を組み立てる

[DkMath.Lib] 源と標的の三根、それぞれの半核距離積 H₁,H₂,H₃、三組の根の差の
関係式から判別式の積恒等式を導く。これは純粋な体の計算であり、三組の関係式を
実際の Vélu 写像から供給する幾何学的な証明は別途必要である。
-/
namespace DkMath.Lib.NumberTheory.WeierstrassDiscriminantAssembly
open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassTwoTorsionTranslate
open scoped Function
variable {k : Type*} [Field k]

/-- [DkMath.Lib] 一本の2捩れ根 `e` と半核の移動根 `ξ q` から作る
モニックなファイバー因子。`ξ` の重複度は反転対に対応して2である。 -/
noncomputable def fiberFactor {ι : Type*} [DecidableEq ι] (s : Finset ι) (e : k)
    (ξ : ι → k) : k[X] :=
  (X - C e) * ∏ q ∈ s, (X - C (ξ q)) ^ 2

/-- [DkMath.Lib] ファイバー因子を任意の点で評価すると、根との差と
移動根への距離積の平方になる。判別式積公式の `hF` の右辺に対応する。 -/
theorem fiberFactor_eval {ι : Type*} [DecidableEq ι] (s : Finset ι) (e e' : k)
    (ξ : ι → k) :
    (fiberFactor s e ξ).eval e' = (e' - e) * (∏ q ∈ s, (e' - ξ q)) ^ 2 := by
  simp only [fiberFactor, eval_mul, eval_sub, eval_X, eval_C, eval_prod, eval_pow]
  rw [← Finset.prod_pow]

/-- [DkMath.Lib] ファイバー因子はモニックである。
この性質は根の個数を次数へ移す際に使う。 -/
theorem fiberFactor_monic {ι : Type*} [DecidableEq ι] (s : Finset ι) (e : k)
    (ξ : ι → k) : (fiberFactor s e ξ).Monic := by
  unfold fiberFactor
  apply Monic.mul (monic_X_sub_C e)
  apply monic_prod_of_monic
  intro q hq
  exact (monic_X_sub_C (ξ q)).pow 2

/-- [DkMath.Lib] ファイバー因子は零多項式ではない。
モニック性から直ちに得られるが、`natDegree_mul` や根の API に渡す
非零条件を毎回書き直さないための教科書用補題である。 -/
theorem fiberFactor_ne_zero {ι : Type*} [DecidableEq ι] (s : Finset ι) (e : k)
    (ξ : ι → k) : fiberFactor s e ξ ≠ 0 :=
  (fiberFactor_monic s e ξ).ne_zero

/-- [DkMath.Lib] ファイバー因子の次数は、一本の単純根と
各移動根の二重根から `2 |s| + 1` になる。 -/
theorem fiberFactor_natDegree {ι : Type*} [DecidableEq ι] (s : Finset ι) (e : k)
    (ξ : ι → k) : (fiberFactor s e ξ).natDegree = 2 * s.card + 1 := by
  unfold fiberFactor
  have hp : (∏ q ∈ s, (X - C (ξ q)) ^ 2).Monic := by
    apply monic_prod_of_monic
    intro q hq
    exact (monic_X_sub_C (ξ q)).pow 2
  rw [natDegree_mul (monic_X_sub_C e).ne_zero hp.ne_zero]
  rw [natDegree_X_sub_C, natDegree_prod_of_monic]
  · simp
    omega
  · exact fun q hq => (monic_X_sub_C (ξ q)).pow 2

/-- [DkMath.Lib] `fiberFactor` がある点で消えることの評価形。
根の集合を使う代わりに、一本の単純根 `e` または移動根 `ξ q` の
いずれかであることを直接取り出せる。 -/
theorem fiberFactor_eval_eq_zero_iff {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (e z : k) (ξ : ι → k) :
    (fiberFactor s e ξ).eval z = 0 ↔ z = e ∨ ∃ q ∈ s, z = ξ q := by
  rw [fiberFactor_eval]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · right
      have hprod : (∏ q ∈ s, (z - ξ q)) = 0 := sq_eq_zero_iff.mp h
      obtain ⟨q, hq, hqz⟩ := Finset.prod_eq_zero_iff.mp hprod
      exact ⟨q, hq, sub_eq_zero.mp hqz⟩
  · rintro (rfl | ⟨q, hq, rfl⟩)
    · simp
    · have hzero : (∏ a ∈ s, (ξ q - ξ a)) = 0 :=
        Finset.prod_eq_zero_iff.mpr ⟨q, hq, by simp⟩
      simp [hzero]

/-- [DkMath.Lib] ファイバー因子の根の多重集合は、一本の根 `e` と
各移動根 `ξ q` を二重に並べたものになる。重複を消去せず保持する。 -/
theorem fiberFactor_roots {ι : Type*} [DecidableEq ι] (s : Finset ι) (e : k)
    (ξ : ι → k) :
    (fiberFactor s e ξ).roots = {e} + s.1.bind (fun q => 2 • ({ξ q} : Multiset k)) := by
  classical
  unfold fiberFactor
  have hp : (∏ q ∈ s, (X - C (ξ q)) ^ 2) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun q hq =>
      (monic_X_sub_C (ξ q)).pow 2 |>.ne_zero
  have hroots := roots_prod (fun q => (X - C (ξ q)) ^ 2) s hp
  rw [roots_mul (mul_ne_zero (monic_X_sub_C e).ne_zero hp)]
  rw [hroots]
  simp only [roots_X_sub_C, roots_pow]

/-- [DkMath.Lib] 根が次数を尽くすモニック多項式は、`fiberFactor` の根が
一致すればその因子そのものに一致する。

これは「有理式のファイバーがこの因子を持つ」から「有理式の分子が
この因子である」へ進むための標準的な一意性層である。`hcard` は
標数や代数閉性を隠れて仮定せず、根の多重集合が次数を尽くすことを
明示的に要求する。 -/
theorem eq_fiberFactor_of_monic_of_roots
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (e : k) (ξ : ι → k)
    (p : k[X]) (hp : p.Monic)
    (hroots : p.roots = (fiberFactor s e ξ).roots)
    (hcard : p.roots.card = p.natDegree) :
    p = fiberFactor s e ξ := by
  have hcard_f : (fiberFactor s e ξ).roots.card =
      (fiberFactor s e ξ).natDegree := by
    rw [fiberFactor_roots, fiberFactor_natDegree]
    simp [Nat.mul_comm]
  have hp_repr := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hp hcard
  have hf_repr := prod_multiset_X_sub_C_of_monic_of_roots_card_eq
    (fiberFactor_monic s e ξ) hcard_f
  calc
    p = (p.roots.map fun a => X - C a).prod := hp_repr.symm
    _ = ((fiberFactor s e ξ).roots.map fun a => X - C a).prod := by rw [hroots]
    _ = fiberFactor s e ξ := hf_repr

/-- [DkMath.Lib] `fiberFactor` の根が別の非零多項式の根に多重度込みで
含まれるなら、`fiberFactor` はその多項式を割る。

実際の有限ファイバーでは、まず各平行移動点から根の包含を作り、
この補題で分子多項式への可除性へ移す。等号には別途、モニック性と
次数比較を要求するため、ここでは過剰な幾何学仮定を導入しない。 -/
theorem fiberFactor_dvd_of_roots_le
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (e : k) (ξ : ι → k)
    (p : k[X]) (hp : p ≠ 0)
    (hroots : (fiberFactor s e ξ).roots ≤ p.roots) :
    fiberFactor s e ξ ∣ p := by
  have hcard_f : (fiberFactor s e ξ).roots.card =
      (fiberFactor s e ξ).natDegree := by
    rw [fiberFactor_roots, fiberFactor_natDegree]
    simp [Nat.mul_comm]
  have hf_repr := prod_multiset_X_sub_C_of_monic_of_roots_card_eq
    (fiberFactor_monic s e ξ) hcard_f
  rw [← hf_repr]
  exact (Multiset.prod_X_sub_C_dvd_iff_le_roots hp _).mpr hroots

/-!
The preceding theorem is phrased in terms of the root multiset because that is
the canonical interface for polynomial divisibility.  In applications one
usually knows the same fact as a collection of local multiplicity bounds:
the distinguished root occurs once and every translated root occurs twice.
The next lemma is the finite, pairwise-coprime bookkeeping which converts
those local bounds into the global factor.  It deliberately asks for
injectivity and separation of the displayed roots; the geometric proof of
those hypotheses belongs to the orbit layer, not to this algebraic lemma.
-/

/-- [DkMath.Lib] Local root-multiplicity bounds imply divisibility by a
`fiberFactor`.

The index type is enlarged to `Option ι`: `none` represents the simple root
`e`, while `some q` represents the square factor at `ξ q`.  Injectivity of
this enlarged root map makes all displayed linear factors pairwise coprime;
`Finset.prod_dvd_of_coprime` then assembles the local divisibilities.  This
is the textbook bridge from geometric multiplicity statements to the
polynomial numerator used by a finite fibre.
-/
theorem fiberFactor_dvd_of_rootMultiplicity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : k) (ξ : ι → k) (p : k[X]) (hp : p ≠ 0)
    (hinj : Function.Injective ξ) (hsep : ∀ q, e ≠ ξ q)
    (he : 1 ≤ p.rootMultiplicity e)
    (hξ : ∀ q, 2 ≤ p.rootMultiplicity (ξ q)) :
    fiberFactor (Finset.univ : Finset ι) e ξ ∣ p := by
  let g : Option ι → k := fun o => match o with
    | none => e
    | some q => ξ q
  have hg : Function.Injective g := by
    intro a b hab
    cases a with
    | none =>
        cases b with
        | none => rfl
        | some q =>
            exact (hsep q hab).elim
    | some q =>
        cases b with
        | none =>
            exact (hsep q hab.symm).elim
        | some r =>
            exact congrArg some (hinj hab)
  let f : Option ι → k[X] := fun o => match o with
    | none => X - C e
    | some q => (X - C (ξ q)) ^ 2
  have hf_pair : Pairwise (IsCoprime on f) := by
    intro a b hab
    cases a with
    | none =>
        cases b with
        | none => exact (hab rfl).elim
        | some q =>
            simpa [f, g] using
              (Polynomial.pairwise_coprime_X_sub_C hg hab).pow_right
    | some q =>
        cases b with
        | none =>
            simpa [f, g] using
              ((Polynomial.pairwise_coprime_X_sub_C hg hab).pow_left)
        | some r =>
            simpa [f, g] using
              ((Polynomial.pairwise_coprime_X_sub_C hg hab).pow)
  have hf_dvd : ∀ o, f o ∣ p := by
    intro o
    cases o with
    | none =>
        simpa [f] using (le_rootMultiplicity_iff hp).mp he
    | some q =>
        simpa [f] using (le_rootMultiplicity_iff hp).mp (hξ q)
  have hprod : (∏ o : Option ι, f o) ∣ p :=
    Fintype.prod_dvd_of_coprime hf_pair hf_dvd
  change (X - C e) * ∏ q : ι, (X - C (ξ q)) ^ 2 ∣ p
  simpa [f, fiberFactor, Fintype.prod_option] using hprod

/-- [DkMath.Lib] `fiberFactor` の根を多重度込みで含み、かつ次数が
`fiberFactor` 以下であるモニック多項式は、`fiberFactor` と等しい。

根の包含、一般の多項式に対する根数上界、そして `fiberFactor` の既知の
次数を一列の不等式に並べ、根の多重集合の等号を回収する。実際の
Vélu 分子を因子同定する際の最短の入口である。 -/
theorem eq_fiberFactor_of_monic_of_roots_le
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (e : k) (ξ : ι → k)
    (p : k[X]) (hp : p.Monic)
    (hroots : (fiberFactor s e ξ).roots ≤ p.roots)
    (hdeg : p.natDegree ≤ (fiberFactor s e ξ).natDegree) :
    p = fiberFactor s e ξ := by
  have hcard_f : (fiberFactor s e ξ).roots.card =
      (fiberFactor s e ξ).natDegree := by
    rw [fiberFactor_roots, fiberFactor_natDegree]
    simp [Nat.mul_comm]
  have hcard_le : (fiberFactor s e ξ).roots.card ≤ p.roots.card :=
    Multiset.card_le_card hroots
  have hcard_roots : p.roots.card ≤ p.natDegree := Polynomial.card_roots' p
  have hcard_eq : p.roots.card = p.natDegree := by
    omega
  have hroots_eq : p.roots = (fiberFactor s e ξ).roots :=
    (Multiset.eq_of_le_of_card_le hroots (by omega)).symm
  exact eq_fiberFactor_of_monic_of_roots s e ξ p hp hroots_eq hcard_eq

/-- [DkMath.Lib] 点ごとの根差関係を有限積へ持ち上げる。
右辺の符号を `eₖ-eⱼ` に直してから積を取り、半核の濃度を指数へ変換する。
この補題が、平行移動された2捩れ点から判別式消去へ進む橋である。 -/
theorem product_root_difference_relation {ι : Type*} (s : Finset ι)
    (x ξ : ι → k) (eⱼ eₖ eₗ : k)
    (hL : ∀ q ∈ s, (eₖ - ξ q) * (x q - eⱼ) =
      -((eⱼ - eₖ) * (x q - eₗ))) :
    (∏ q ∈ s, (eₖ - ξ q)) * (∏ q ∈ s, (x q - eⱼ)) =
      (eₖ - eⱼ) ^ s.card * ∏ q ∈ s, (x q - eₗ) := by
  rw [← Finset.prod_mul_distrib]
  calc
    (∏ q ∈ s, (eₖ - ξ q) * (x q - eⱼ)) =
        ∏ q ∈ s, ((eₖ - eⱼ) * (x q - eₗ)) := by
      apply Finset.prod_congr rfl
      intro q hq
      rw [hL q hq]
      ring
    _ = (eₖ - eⱼ) ^ s.card * ∏ q ∈ s, (x q - eₗ) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card]

/-- [DkMath.Lib] 2捩れ点による affine 平行移動公式を、半核添字の有限積へ
直接持ち上げる。

各 `q` で `translated_root_difference` を呼び出すだけで、判別式積公式の
入力形式 `(e₂-ξ q)(x q-e₁)=-(e₁-e₂)(x q-e₃)` を供給する。ここでの
`hEq` と `hxe` は、加法公式の分母と曲線方程式を明示するための幾何学的
境界であり、商写像の全射性や標的の楕円性は仮定していない。 -/
theorem translated_root_product_relation {ι : Type*} [DecidableEq k]
    (W : WeierstrassCurve k)
    (s : Finset ι) (x y : ι → k)
    (e₁ e₂ e₃ : k)
    (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (hσ₁ : e₁ + e₂ + e₃ = -W.a₂)
    (hσ₂ : e₁ * e₂ + e₁ * e₃ + e₂ * e₃ = W.a₄)
    (hσ₃ : e₁ * e₂ * e₃ = -W.a₆)
    (hEq : ∀ q ∈ s, W.toAffine.Equation (x q) (y q))
    (hxe : ∀ q ∈ s, x q ≠ e₁) :
    (∏ q ∈ s, (e₂ - W.toAffine.addX e₁ (x q)
      (W.toAffine.slope e₁ (x q) 0 (y q)))) *
        (∏ q ∈ s, (x q - e₁)) =
      (e₂ - e₁) ^ s.card * ∏ q ∈ s, (x q - e₃) := by
  apply product_root_difference_relation s x
    (fun q => W.toAffine.addX e₁ (x q) (W.toAffine.slope e₁ (x q) 0 (y q)))
    e₁ e₂ e₃
  intro q hq
  exact translated_root_difference W ha₁ ha₃ hσ₁ hσ₂ hσ₃
    (hEq q hq) (hxe q hq)

/-- [DkMath.Lib] 有理式による座標評価と移動された点の積の関係から、
三組の差に共通する一つの関係式を作る。分母で割る代わりに両辺へ因子を掛ける。 -/
theorem pair_relation (n : ℕ) (G Hj Hk Hl Xj Xk ej ek A : k)
    (hA : A = Hk ^ 2 * Xk)
    (hF : A - Xj * Hk ^ 2 = (ek - ej) * G ^ 2)
    (hG : G * Hj = (ek - ej) ^ n * Hl) :
    (Xj - Xk) ^ 2 * Hj ^ 4 * Hk ^ 4 =
      (ek - ej) ^ (2 * (2 * n + 1)) * Hl ^ 4 := by
  have h : (Xk - Xj) * Hk ^ 2 * Hj ^ 2 = (ek - ej) * (G * Hj) ^ 2 := by
    linear_combination Hj ^ 2 * (hF - hA)
  rw [hG] at h
  calc
    _ = ((Xk - Xj) * Hk ^ 2 * Hj ^ 2) ^ 2 := by ring
    _ = ((ek - ej) * ((ek - ej) ^ n * Hl) ^ 2) ^ 2 := by rw [h]
    _ = _ := by ring

/-- [DkMath.Lib] 三組の根の差の関係を掛け合わせ、共通の非零因子を消去する。
`n` は半核の大きさ、`Hᵢ` は源の第 i 根への距離積、`U` は接線分母積を表す。
`P₁₂` などの仮定は実際の商写像から別に証明する必要がある。 -/
theorem discriminant_product_of_pair_relations
    (n : ℕ) (e₁ e₂ e₃ X₁ X₂ X₃ Δ Δ' H₁ H₂ H₃ U : k)
    (hH : H₁ * H₂ * H₃ ≠ 0)
    (hU : U = 4 ^ n * (H₁ * H₂ * H₃))
    (hΔ : Δ = 16 * ((e₂ - e₁) * (e₃ - e₁) * (e₃ - e₂)) ^ 2)
    (hΔ' : Δ' = 16 * ((X₁ - X₂) * (X₁ - X₃) * (X₂ - X₃)) ^ 2)
    (P₁₂ : (X₁ - X₂) ^ 2 * H₁ ^ 4 * H₂ ^ 4 =
      (e₂ - e₁) ^ (2 * (2 * n + 1)) * H₃ ^ 4)
    (P₁₃ : (X₁ - X₃) ^ 2 * H₁ ^ 4 * H₃ ^ 4 =
      (e₃ - e₁) ^ (2 * (2 * n + 1)) * H₂ ^ 4)
    (P₂₃ : (X₂ - X₃) ^ 2 * H₂ ^ 4 * H₃ ^ 4 =
      (e₃ - e₂) ^ (2 * (2 * n + 1)) * H₁ ^ 4) :
    Δ' * U ^ 4 = Δ ^ (2 * n + 1) := by
  have h16 : (16 : k) ^ (2 * n + 1) = 16 * ((4 : k) ^ n) ^ 4 := by
    rw [pow_succ, pow_mul, ← pow_mul (4 : k) n 4, mul_comm n 4, pow_mul,
      show ((16 : k)) ^ 2 = 4 ^ 4 by norm_num]
    ring
  generalize e₂ - e₁ = a at P₁₂ hΔ
  generalize e₃ - e₁ = b at P₁₃ hΔ
  generalize e₃ - e₂ = c at P₂₃ hΔ
  have hP0 : (H₁ * H₂ * H₃) ^ 4 ≠ 0 := pow_ne_zero 4 hH
  have key : ((X₁ - X₂) * (X₁ - X₃) * (X₂ - X₃)) ^ 2 *
      (H₁ * H₂ * H₃) ^ 4 * (H₁ * H₂ * H₃) ^ 4 =
      a ^ (2 * (2 * n + 1)) * b ^ (2 * (2 * n + 1)) *
        c ^ (2 * (2 * n + 1)) * (H₁ * H₂ * H₃) ^ 4 := by
    have eqprod : ((X₁ - X₂) * (X₁ - X₃) * (X₂ - X₃)) ^ 2 *
        (H₁ * H₂ * H₃) ^ 4 * (H₁ * H₂ * H₃) ^ 4 =
        ((X₁ - X₂) ^ 2 * H₁ ^ 4 * H₂ ^ 4) *
        ((X₁ - X₃) ^ 2 * H₁ ^ 4 * H₃ ^ 4) *
        ((X₂ - X₃) ^ 2 * H₂ ^ 4 * H₃ ^ 4) := by ring
    rw [eqprod, P₁₂, P₁₃, P₂₃]
    ring
  have key2 : ((X₁ - X₂) * (X₁ - X₃) * (X₂ - X₃)) ^ 2 *
      (H₁ * H₂ * H₃) ^ 4 =
      a ^ (2 * (2 * n + 1)) * b ^ (2 * (2 * n + 1)) *
        c ^ (2 * (2 * n + 1)) := mul_right_cancel₀ hP0 key
  calc
    Δ' * U ^ 4 = 16 * (4 ^ n) ^ 4 *
        (((X₁ - X₂) * (X₁ - X₃) * (X₂ - X₃)) ^ 2 * (H₁ * H₂ * H₃) ^ 4) := by
      rw [hΔ', hU]; ring
    _ = 16 * (4 ^ n) ^ 4 * (a ^ (2 * (2 * n + 1)) *
        b ^ (2 * (2 * n + 1)) * c ^ (2 * (2 * n + 1))) := by rw [key2]
    _ = Δ ^ (2 * n + 1) := by rw [hΔ, mul_pow, h16]; ring

/-! ### 付値への輸送

判別式積恒等式を得た後の局所計算は、ここで一度だけ `Valuation` に写す。
この層は積公式の幾何学的供給元を仮定せず、既に得られた体の等式を
`map_mul` と `map_pow` で輸送するだけである。 -/

/-- [DkMath.Lib] 判別式積恒等式を任意の付値へ写した形。

付値の値域には離散性を要求しない。従って、良還元・特異還元のどちらでも、
上流で積公式が供給されれば同じ教科書補題を再利用できる。 -/
theorem discriminant_product_value
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation k Γ₀)
    (n : ℕ) (Δ Δ' U : k)
    (hprod : Δ' * U ^ 4 = Δ ^ (2 * n + 1)) :
    v Δ' * (v U) ^ 4 = (v Δ) ^ (2 * n + 1) := by
  have h := congrArg v hprod
  simpa only [map_mul, map_pow] using h

/-- [DkMath.Lib] 接線因子が付値1なら、商判別式の値は源判別式の
`2*n+1` 乗になる。

`v U = 1` の単元条件を明示的に残し、判別式の非零性や付値の離散性を
隠れて仮定しない。 -/
theorem discriminant_value_of_unit_factor
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation k Γ₀)
    (n : ℕ) (Δ Δ' U : k)
    (hprod : Δ' * U ^ 4 = Δ ^ (2 * n + 1))
    (hU : v U = 1) :
    v Δ' = (v Δ) ^ (2 * n + 1) := by
  have hv := discriminant_product_value v n Δ Δ' U hprod
  rw [hU, one_pow, mul_one] at hv
  exact hv

end DkMath.Lib.NumberTheory.WeierstrassDiscriminantAssembly
