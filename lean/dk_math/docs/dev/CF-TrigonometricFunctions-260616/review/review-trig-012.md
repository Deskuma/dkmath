# Git diff / Report / Review

## Add: docs: docstring

gch: f02af1a6e0fedb633886e0ea91587156566b5271

## Report

CF2D import 配下の theorem docstring 整備を入れました。

対象は以下の 5 ファイルです。

- [Basic.lean](/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Basic.lean)
- [Trig.lean](/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Trig.lean)
- [CFSinCos.lean](/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/CFSinCos.lean)
- [Failure.lean](/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Failure.lean)
- [Real.lean](/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Real.lean)

`Vec.star`、共役、`UnitKernel`、作用、`KernelFamily`、`cfcos/cfsin`、失敗符号、Real bridge の theorem に、コード単体で数学的な意味が追える程度の軽い説明を追加しました。証明本体と API は変更していません。

確認済みです。

```text
lake build DkMath.CosmicFormula.Rotation
git diff --check
```

加えて、対象 5 ファイル内の `theorem` について docstring 欠落が残っていないことも簡易チェック済みです。

## Review

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Basic.lean b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Basic.lean
index 2df0bd0c..244786b8 100644
--- a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Basic.lean
+++ b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Basic.lean
@@ -57,19 +57,24 @@ def star [Ring R] (r z : Vec R) : Vec R :=
   ⟨r.core * z.core - r.beam * z.beam,
     r.core * z.beam + r.beam * z.core⟩

+/-- The square mass of an explicit pair is the displayed quadratic form. -/
 @[simp]
 theorem q2_mk [Semiring R] (x y : R) : q2 (Vec.mk x y) = x ^ 2 + y ^ 2 := rfl

+/-- The core coordinate of the neutral kernel is `1`. -/
 @[simp]
 theorem one_core [Zero R] [One R] : (one R).core = 1 := rfl

+/-- The beam coordinate of the neutral kernel is `0`. -/
 @[simp]
 theorem one_beam [Zero R] [One R] : (one R).beam = 0 := rfl

+/-- Core coordinate formula for the unit-kernel product. -/
 @[simp]
 theorem star_core [Ring R] (r z : Vec R) :
     (star r z).core = r.core * z.core - r.beam * z.beam := rfl

+/-- Beam coordinate formula for the unit-kernel product. -/
 @[simp]
 theorem star_beam [Ring R] (r z : Vec R) :
     (star r z).beam = r.core * z.beam + r.beam * z.core := rfl
@@ -105,18 +110,26 @@ theorem q2_star [CommRing R] (r z : Vec R) :
           simp [q2, star]
           ring

+/-- Multiplication by the neutral kernel on the right does not change a vector. -/
 @[simp]
 theorem star_one [CommRing R] (z : Vec R) : star z (one R) = z := by
   cases z with
   | mk x y =>
       simp [star, one]

+/-- Multiplication by the neutral kernel on the left does not change a vector. -/
 @[simp]
 theorem one_star [CommRing R] (z : Vec R) : star (one R) z = z := by
   cases z with
   | mk x y =>
       simp [star, one]

+/--
+Associativity of the two-component product.
+
+This is the algebraic reason that kernel multiplication can later be read as
+composition of actions.
+-/
 theorem star_assoc [CommRing R] (p q z : Vec R) :
     star (star p q) z = star p (star q z) := by
   cases p with
@@ -128,6 +141,12 @@ theorem star_assoc [CommRing R] (p q z : Vec R) :
               simp [star]
               constructor <;> ring

+/--
+Commutativity of the two-component product over a commutative ring.
+
+For the rotation interpretation this says that the 2D unit kernels form an
+abelian multiplication law.
+-/
 theorem star_comm [CommRing R] (r z : Vec R) : star r z = star z r := by
   cases r with
   | mk a b =>
@@ -140,23 +159,32 @@ theorem star_comm [CommRing R] (r z : Vec R) : star r z = star z r := by
 def conj [Neg R] (z : Vec R) : Vec R :=
   ⟨z.core, -z.beam⟩

+/-- The core coordinate is unchanged by conjugation. -/
 @[simp]
 theorem conj_core [Neg R] (z : Vec R) : (conj z).core = z.core := rfl

+/-- The beam coordinate changes sign under conjugation. -/
 @[simp]
 theorem conj_beam [Neg R] (z : Vec R) : (conj z).beam = -z.beam := rfl

+/-- Conjugation preserves the square mass. -/
 theorem q2_conj [CommRing R] (z : Vec R) : q2 (conj z) = q2 z := by
   cases z with
   | mk x y =>
       simp [q2, conj]

+/-- Conjugating twice returns the original two-component state. -/
 @[simp]
 theorem conj_conj [Ring R] (z : Vec R) : conj (conj z) = z := by
   cases z with
   | mk x y =>
       simp [conj]

+/--
+Conjugation distributes over the two-component product.
+
+This is the CF2D analogue of complex conjugation preserving multiplication.
+-/
 theorem conj_star [CommRing R] (r z : Vec R) :
     conj (star r z) = star (conj r) (conj z) := by
   cases r with
@@ -166,6 +194,10 @@ theorem conj_star [CommRing R] (r z : Vec R) :
           simp [conj, star]
           ring

+/--
+Multiplying a vector by its conjugate removes the beam coordinate and leaves
+the square mass in the core coordinate.
+-/
 theorem star_conj_self [CommRing R] (z : Vec R) :
     star z (conj z) = Vec.mk (q2 z) 0 := by
   cases z with
@@ -173,6 +205,12 @@ theorem star_conj_self [CommRing R] (z : Vec R) :
       simp [star, conj, q2]
       constructor <;> ring

+/--
+The same inverse-like identity with the conjugate placed on the left.
+
+The result agrees with `star_conj_self` because the product is commutative in
+this commutative-ring layer.
+-/
 theorem conj_star_self [CommRing R] (z : Vec R) :
     star (conj z) z = Vec.mk (q2 z) 0 := by
   cases z with
@@ -202,10 +240,12 @@ variable {R : Type u}
 instance [Semiring R] : Coe (UnitKernel R) (Vec R) :=
   ⟨UnitKernel.val⟩

+/-- Coercing a unit kernel to `Vec` exposes its defining square-mass-one law. -/
 @[simp]
 theorem coe_q2 [Semiring R] (r : UnitKernel R) : Vec.q2 (r : Vec R) = 1 :=
   r.q2_eq_one

+/-- Unit kernels are equal when their underlying two-component vectors are equal. -/
 @[ext]
 theorem ext [Semiring R] {r s : UnitKernel R} (h : (r : Vec R) = (s : Vec R)) : r = s := by
   cases r with
@@ -224,6 +264,7 @@ def conj [CommRing R] (r : UnitKernel R) : UnitKernel R :=
   ⟨Vec.conj (r : Vec R), by
     rw [Vec.q2_conj, coe_q2]⟩

+/-- The underlying vector of a conjugated unit kernel is vector conjugation. -/
 @[simp]
 theorem conj_val [CommRing R] (r : UnitKernel R) :
     (conj r : Vec R) = Vec.conj (r : Vec R) := rfl
@@ -233,26 +274,31 @@ def star [CommRing R] (r s : UnitKernel R) : UnitKernel R :=
   ⟨Vec.star (r : Vec R) (s : Vec R), by
     rw [Vec.q2_star, coe_q2, coe_q2, one_mul]⟩

+/-- The underlying vector of a product of unit kernels is the vector product. -/
 @[simp]
 theorem star_val [CommRing R] (r s : UnitKernel R) :
     (star r s : Vec R) = Vec.star (r : Vec R) (s : Vec R) := rfl

+/-- Product of unit kernels again has square mass `1`. -/
 @[simp]
 theorem star_q2 [CommRing R] (r s : UnitKernel R) : Vec.q2 (star r s : Vec R) = 1 :=
   coe_q2 (star r s)

+/-- The neutral unit kernel is a right identity for kernel multiplication. -/
 @[simp]
 theorem star_one [CommRing R] (r : UnitKernel R) : star r (one R) = r := by
   cases r with
   | mk val q2_eq_one =>
       simp [star, one]

+/-- The neutral unit kernel is a left identity for kernel multiplication. -/
 @[simp]
 theorem one_star [CommRing R] (r : UnitKernel R) : star (one R) r = r := by
   cases r with
   | mk val q2_eq_one =>
       simp [star, one]

+/-- Associativity of multiplication for unit kernels. -/
 theorem star_assoc [CommRing R] (p q r : UnitKernel R) :
     star (star p q) r = star p (star q r) := by
   cases p with
@@ -263,6 +309,7 @@ theorem star_assoc [CommRing R] (p q r : UnitKernel R) :
           | mk rv hr =>
               simp [star, Vec.star_assoc]

+/-- Commutativity of multiplication for unit kernels. -/
 theorem star_comm [CommRing R] (r s : UnitKernel R) : star r s = star s r := by
   cases r with
   | mk rv hr =>
@@ -270,12 +317,14 @@ theorem star_comm [CommRing R] (r s : UnitKernel R) : star r s = star s r := by
       | mk sv hs =>
           simp [star, Vec.star_comm]

+/-- A unit kernel multiplied by its conjugate is the neutral kernel. -/
 @[simp]
 theorem star_conj [CommRing R] (r : UnitKernel R) : star r (conj r) = one R := by
   apply UnitKernel.ext
   rw [star_val, conj_val, Vec.star_conj_self]
   simp [one, Vec.one]

+/-- The conjugate multiplied on the left is also inverse-like. -/
 @[simp]
 theorem conj_star [CommRing R] (r : UnitKernel R) : star (conj r) r = one R := by
   apply UnitKernel.ext
@@ -286,10 +335,16 @@ theorem conj_star [CommRing R] (r : UnitKernel R) : star (conj r) r = one R := b
 def act [CommRing R] (r : UnitKernel R) (z : Vec R) : Vec R :=
   Vec.star (r : Vec R) z

+/-- The neutral unit kernel acts as the identity map. -/
 @[simp]
 theorem act_one [CommRing R] (z : Vec R) : act (one R) z = z := by
   simp [act, one]

+/--
+Action by a product of kernels is composition of the two actions.
+
+This is the formal bridge from kernel multiplication to rotation composition.
+-/
 theorem act_star [CommRing R] (r s : UnitKernel R) (z : Vec R) :
     act (star r s) z = act r (act s z) := by
   change Vec.star ((star r s : UnitKernel R) : Vec R) z
@@ -297,10 +352,12 @@ theorem act_star [CommRing R] (r s : UnitKernel R) (z : Vec R) :
   rw [star_val]
   exact Vec.star_assoc (r : Vec R) (s : Vec R) z

+/-- Core coordinate formula for the action of a unit kernel. -/
 @[simp]
 theorem act_core [CommRing R] (r : UnitKernel R) (z : Vec R) :
     (act r z).core = (r : Vec R).core * z.core - (r : Vec R).beam * z.beam := rfl

+/-- Beam coordinate formula for the action of a unit kernel. -/
 @[simp]
 theorem act_beam [CommRing R] (r : UnitKernel R) (z : Vec R) :
     (act r z).beam = (r : Vec R).core * z.beam + (r : Vec R).beam * z.core := rfl
@@ -310,6 +367,7 @@ theorem q2_act [CommRing R] (r : UnitKernel R) (z : Vec R) :
     Vec.q2 (act r z) = Vec.q2 z := by
   rw [act, Vec.q2_star, coe_q2, one_mul]

+/-- The action of a unit kernel is a square-mass-preserving map. -/
 theorem preservesQ2_act [CommRing R] (r : UnitKernel R) : PreservesQ2 (act r) :=
   q2_act r

@@ -333,6 +391,7 @@ def act (r : UnitKernel R) (z : LevelSet R rho2) : LevelSet R rho2 :=
     have h := UnitKernel.q2_act r z.1
     simpa [z.2] using h⟩

+/-- The underlying value of a level-set action is the ordinary unit-kernel action. -/
 @[simp]
 theorem act_val (r : UnitKernel R) (z : LevelSet R rho2) :
     (act r z).1 = UnitKernel.act r z.1 := rfl
diff --git a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/CFSinCos.lean b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/CFSinCos.lean
index 57d7c787..d2501344 100644
--- a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/CFSinCos.lean
+++ b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/CFSinCos.lean
@@ -35,40 +35,61 @@ def cfcos (F : KernelFamily T R) (t : T) : R :=
 def cfsin (F : KernelFamily T R) (t : T) : R :=
   F.S t

+/-- `cfcos` is definitionally the core coordinate `C`. -/
 @[simp]
 theorem cfcos_eq_C (F : KernelFamily T R) (t : T) :
     F.cfcos t = F.C t := rfl

+/-- `cfsin` is definitionally the beam coordinate `S`. -/
 @[simp]
 theorem cfsin_eq_S (F : KernelFamily T R) (t : T) :
     F.cfsin t = F.S t := rfl

+/-- Cosmic-formula cosine takes value `1` at the zero parameter. -/
 @[simp]
 theorem cfcos_zero (F : KernelFamily T R) : F.cfcos 0 = 1 := by
   simp [cfcos]

+/-- Cosmic-formula sine takes value `0` at the zero parameter. -/
 @[simp]
 theorem cfsin_zero (F : KernelFamily T R) : F.cfsin 0 = 0 := by
   simp [cfsin]

+/--
+Pythagorean identity for the cosmic-formula coordinate functions.
+
+It is a projection of the unit-kernel condition `q2 = 1`.
+-/
 theorem cfcos_sq_add_cfsin_sq (F : KernelFamily T R) (t : T) :
     F.cfcos t ^ 2 + F.cfsin t ^ 2 = 1 := by
   simpa [cfcos, cfsin] using F.C_sq_add_S_sq t

+/--
+Addition formula for cosmic-formula cosine.
+
+This is the core coordinate of the kernel multiplication law.
+-/
 theorem cfcos_add (F : KernelFamily T R) (t s : T) :
     F.cfcos (t + s)
       = F.cfcos t * F.cfcos s - F.cfsin t * F.cfsin s := by
   simpa [cfcos, cfsin] using F.C_add t s

+/--
+Addition formula for cosmic-formula sine.
+
+This is the beam coordinate of the kernel multiplication law.
+-/
 theorem cfsin_add (F : KernelFamily T R) (t s : T) :
     F.cfsin (t + s)
       = F.cfcos t * F.cfsin s + F.cfsin t * F.cfcos s := by
   simpa [cfcos, cfsin] using F.S_add t s

+/-- Double-angle formula for cosmic-formula cosine. -/
 theorem cfcos_add_self (F : KernelFamily T R) (t : T) :
     F.cfcos (t + t) = F.cfcos t ^ 2 - F.cfsin t ^ 2 := by
   simpa [cfcos, cfsin] using F.C_add_self t

+/-- Double-angle formula for cosmic-formula sine. -/
 theorem cfsin_add_self (F : KernelFamily T R) (t : T) :
     F.cfsin (t + t) = 2 * F.cfcos t * F.cfsin t := by
   simpa [cfcos, cfsin] using F.S_add_self t
@@ -124,19 +145,23 @@ section AddGroup

 variable {T : Type u} {R : Type v} [AddGroup T] [CommRing R]

+/-- Cosmic-formula cosine is even with respect to parameter negation. -/
 theorem cfcos_neg (F : KernelFamily T R) (t : T) :
     F.cfcos (-t) = F.cfcos t := by
   simpa [cfcos] using F.C_neg t

+/-- Cosmic-formula sine is odd with respect to parameter negation. -/
 theorem cfsin_neg (F : KernelFamily T R) (t : T) :
     F.cfsin (-t) = -F.cfsin t := by
   simpa [cfsin] using F.S_neg t

+/-- Difference formula for cosmic-formula cosine. -/
 theorem cfcos_sub (F : KernelFamily T R) (t s : T) :
     F.cfcos (t - s)
       = F.cfcos t * F.cfcos s + F.cfsin t * F.cfsin s := by
   simpa [cfcos, cfsin] using F.C_sub t s

+/-- Difference formula for cosmic-formula sine. -/
 theorem cfsin_sub (F : KernelFamily T R) (t s : T) :
     F.cfsin (t - s)
       = F.cfsin t * F.cfcos s - F.cfcos t * F.cfsin s := by
diff --git a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Failure.lean b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Failure.lean
index b9f301e7..5576b733 100644
--- a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Failure.lean
+++ b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Failure.lean
@@ -35,10 +35,12 @@ def badStarPlus [Ring R] (r z : Vec R) : Vec R :=
   ⟨r.core * z.core + r.beam * z.beam,
     r.core * z.beam + r.beam * z.core⟩

+/-- Core coordinate formula for the plus-plus wrong product. -/
 @[simp]
 theorem badStarPlus_core [Ring R] (r z : Vec R) :
     (badStarPlus r z).core = r.core * z.core + r.beam * z.beam := rfl

+/-- Beam coordinate formula for the plus-plus wrong product. -/
 @[simp]
 theorem badStarPlus_beam [Ring R] (r z : Vec R) :
     (badStarPlus r z).beam = r.core * z.beam + r.beam * z.core := rfl
@@ -54,6 +56,12 @@ theorem q2_badStarPlus [CommRing R] (a b x y : R) :
   simp [q2, badStarPlus]
   ring

+/--
+Vector form of the plus-plus failure formula.
+
+The extra `4abxy` term measures exactly the failure of square-mass
+multiplicativity for this sign pattern.
+-/
 theorem q2_badStarPlus_eq_q2_mul_add_residual [CommRing R] (r z : Vec R) :
     q2 (badStarPlus r z) = q2 r * q2 z + 4 * r.core * r.beam * z.core * z.beam := by
   cases r with
@@ -72,20 +80,32 @@ def badStarMinus [Ring R] (r z : Vec R) : Vec R :=
   ⟨r.core * z.core - r.beam * z.beam,
     r.core * z.beam - r.beam * z.core⟩

+/-- Core coordinate formula for the minus-minus wrong product. -/
 @[simp]
 theorem badStarMinus_core [Ring R] (r z : Vec R) :
     (badStarMinus r z).core = r.core * z.core - r.beam * z.beam := rfl

+/-- Beam coordinate formula for the minus-minus wrong product. -/
 @[simp]
 theorem badStarMinus_beam [Ring R] (r z : Vec R) :
     (badStarMinus r z).beam = r.core * z.beam - r.beam * z.core := rfl

+/--
+The minus-minus sign pattern leaves the opposite residual from `badStarPlus`.
+
+This identifies the failed cancellation as a sign-sensitive phenomenon.
+-/
 theorem q2_badStarMinus [CommRing R] (a b x y : R) :
     q2 (badStarMinus (Vec.mk a b) (Vec.mk x y))
       = (a ^ 2 + b ^ 2) * (x ^ 2 + y ^ 2) - 4 * a * b * x * y := by
   simp [q2, badStarMinus]
   ring

+/--
+Vector form of the minus-minus failure formula.
+
+The residual is `-4 * r.core * r.beam * z.core * z.beam`.
+-/
 theorem q2_badStarMinus_eq_q2_mul_sub_residual [CommRing R] (r z : Vec R) :
     q2 (badStarMinus r z) = q2 r * q2 z - 4 * r.core * r.beam * z.core * z.beam := by
   cases r with
@@ -105,14 +125,22 @@ def starPlusMinus [Ring R] (r z : Vec R) : Vec R :=
   ⟨r.core * z.core + r.beam * z.beam,
     r.core * z.beam - r.beam * z.core⟩

+/-- Core coordinate formula for the plus-minus preserving product. -/
 @[simp]
 theorem starPlusMinus_core [Ring R] (r z : Vec R) :
     (starPlusMinus r z).core = r.core * z.core + r.beam * z.beam := rfl

+/-- Beam coordinate formula for the plus-minus preserving product. -/
 @[simp]
 theorem starPlusMinus_beam [Ring R] (r z : Vec R) :
     (starPlusMinus r z).beam = r.core * z.beam - r.beam * z.core := rfl

+/--
+The plus-minus sign pattern also preserves square mass.
+
+It is not the selected convention, but it is algebraically explained by
+conjugating the left kernel.
+-/
 theorem q2_starPlusMinus [CommRing R] (r z : Vec R) :
     q2 (starPlusMinus r z) = q2 r * q2 z := by
   cases r with
@@ -122,6 +150,10 @@ theorem q2_starPlusMinus [CommRing R] (r z : Vec R) :
           simp [q2, starPlusMinus]
           ring

+/--
+The plus-minus preserving product is ordinary `star` after conjugating the
+left input.
+-/
 theorem starPlusMinus_eq_star_conj_left [CommRing R] (r z : Vec R) :
     starPlusMinus r z = star (conj r) z := by
   cases r with
diff --git a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Real.lean b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Real.lean
index 80a0e51b..2f5a722f 100644
--- a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Real.lean
+++ b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Real.lean
@@ -36,37 +36,50 @@ noncomputable def realTrigKernelFamily : KernelFamily ℝ ℝ where
     simp [Vec.star, Real.cos_add, Real.sin_add]
     ring

+/-- In the real model, the abstract core coordinate is the usual `Real.cos`. -/
 @[simp]
 theorem realTrigKernelFamily_C (t : ℝ) :
     realTrigKernelFamily.C t = Real.cos t := rfl

+/-- In the real model, the abstract beam coordinate is the usual `Real.sin`. -/
 @[simp]
 theorem realTrigKernelFamily_S (t : ℝ) :
     realTrigKernelFamily.S t = Real.sin t := rfl

+/-- The cosmic-formula cosine specializes to the usual real cosine. -/
 @[simp]
 theorem realTrigKernelFamily_cfcos (t : ℝ) :
     realTrigKernelFamily.cfcos t = Real.cos t := rfl

+/-- The cosmic-formula sine specializes to the usual real sine. -/
 @[simp]
 theorem realTrigKernelFamily_cfsin (t : ℝ) :
     realTrigKernelFamily.cfsin t = Real.sin t := rfl

+/-- The real kernel at `t` is the pair `(cos t, sin t)`. -/
 @[simp]
 theorem realTrigKernelFamily_kernel_val (t : ℝ) :
     ((realTrigKernelFamily.kernel t : UnitKernel ℝ) : Vec ℝ)
       = ⟨Real.cos t, Real.sin t⟩ := rfl

+/-- Core coordinate of the usual real rotation action. -/
 theorem realTrigKernelFamily_act_core (t : ℝ) (z : Vec ℝ) :
     (UnitKernel.act (realTrigKernelFamily.kernel t) z).core
       = Real.cos t * z.core - Real.sin t * z.beam := by
   simp

+/-- Beam coordinate of the usual real rotation action. -/
 theorem realTrigKernelFamily_act_beam (t : ℝ) (z : Vec ℝ) :
     (UnitKernel.act (realTrigKernelFamily.kernel t) z).beam
       = Real.cos t * z.beam + Real.sin t * z.core := by
   simp

+/--
+Full real rotation action formula.
+
+This is the standard coordinate formula obtained as a specialization of the
+abstract cosmic-formula action theorem.
+-/
 theorem realTrigKernelFamily_act_eq (t : ℝ) (z : Vec ℝ) :
     UnitKernel.act (realTrigKernelFamily.kernel t) z
       = Vec.mk
diff --git a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Trig.lean b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Trig.lean
index fa21b75b..98d3dda5 100644
--- a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Trig.lean
+++ b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Trig.lean
@@ -50,46 +50,56 @@ def C (F : KernelFamily T R) (t : T) : R :=
 def S (F : KernelFamily T R) (t : T) : R :=
   ((F.kernel t : UnitKernel R) : Vec R).beam

+/-- Every kernel in a kernel family has square mass `1`. -/
 @[simp]
 theorem kernel_q2 (F : KernelFamily T R) (t : T) :
     Vec.q2 (((F.kernel t : UnitKernel R) : Vec R)) = 1 :=
   UnitKernel.coe_q2 (F.kernel t)

+/-- The kernel at additive zero is the neutral two-component kernel. -/
 theorem kernel_zero (F : KernelFamily T R) :
     ((F.kernel 0 : UnitKernel R) : Vec R) = Vec.one R :=
   F.map_zero

+/-- The kernel at additive zero is the neutral unit kernel. -/
 theorem kernel_zero_one (F : KernelFamily T R) :
     F.kernel 0 = UnitKernel.one R := by
   apply UnitKernel.ext
   exact F.kernel_zero

+/-- The core coordinate at zero is `1`. -/
 @[simp]
 theorem C_zero (F : KernelFamily T R) : F.C 0 = 1 := by
   have h := congrArg Vec.core F.kernel_zero
   simpa [C, Vec.one] using h

+/-- The beam coordinate at zero is `0`. -/
 @[simp]
 theorem S_zero (F : KernelFamily T R) : F.S 0 = 0 := by
   have h := congrArg Vec.beam F.kernel_zero
   simpa [S, Vec.one] using h

+/-- Adding zero on the right does not change the core coordinate. -/
 @[simp]
 theorem C_add_zero (F : KernelFamily T R) (t : T) : F.C (t + 0) = F.C t := by
   simp

+/-- Adding zero on the right does not change the beam coordinate. -/
 @[simp]
 theorem S_add_zero (F : KernelFamily T R) (t : T) : F.S (t + 0) = F.S t := by
   simp

+/-- Adding zero on the left does not change the core coordinate. -/
 @[simp]
 theorem C_zero_add (F : KernelFamily T R) (t : T) : F.C (0 + t) = F.C t := by
   simp

+/-- Adding zero on the left does not change the beam coordinate. -/
 @[simp]
 theorem S_zero_add (F : KernelFamily T R) (t : T) : F.S (0 + t) = F.S t := by
   simp

+/-- The zero-parameter kernel acts as the identity on vectors. -/
 @[simp]
 theorem act_zero (F : KernelFamily T R) (z : Vec R) :
     UnitKernel.act (F.kernel 0) z = z := by
@@ -112,6 +122,12 @@ theorem kernel_add (F : KernelFamily T R) (t s : T) :
           (((F.kernel s : UnitKernel R) : Vec R)) :=
   F.map_add t s

+/--
+The parameter addition law as an equality of unit kernels.
+
+This packages the coordinate-level `map_add` axiom in the `UnitKernel.star`
+operation.
+-/
 theorem kernel_add_star (F : KernelFamily T R) (t s : T) :
     F.kernel (t + s) = UnitKernel.star (F.kernel t) (F.kernel s) := by
   apply UnitKernel.ext
@@ -135,7 +151,12 @@ theorem S_add (F : KernelFamily T R) (t s : T) :
   have h := congrArg Vec.beam (F.kernel_add t s)
   simpa [C, S, Vec.star] using h

-/-- Unit-kernel family action composes according to parameter addition. -/
+/--
+Kernel-family actions compose according to parameter addition.
+
+This is the abstract rotation-composition law before choosing real sine and
+cosine.
+-/
 theorem act_add (F : KernelFamily T R) (t s : T) (z : Vec R) :
     UnitKernel.act (F.kernel (t + s)) z
       = UnitKernel.act (F.kernel t) (UnitKernel.act (F.kernel s) z) := by
@@ -153,11 +174,13 @@ def actLevel (F : KernelFamily T R) (t : T) {rho2 : R}
     (z : LevelSet R rho2) : LevelSet R rho2 :=
   LevelSet.act (F.kernel t) z

+/-- The underlying value of the induced level-set action. -/
 @[simp]
 theorem actLevel_val (F : KernelFamily T R) (t : T) {rho2 : R}
     (z : LevelSet R rho2) :
     (F.actLevel t z).1 = UnitKernel.act (F.kernel t) z.1 := rfl

+/-- The zero-parameter action is the identity on every square-mass level set. -/
 @[simp]
 theorem actLevel_zero (F : KernelFamily T R) {rho2 : R}
     (z : LevelSet R rho2) :
@@ -165,6 +188,7 @@ theorem actLevel_zero (F : KernelFamily T R) {rho2 : R}
   apply Subtype.ext
   simp [actLevel, F.act_zero]

+/-- Parameter addition composes the induced actions on every level set. -/
 theorem actLevel_add (F : KernelFamily T R) (t s : T) {rho2 : R}
     (z : LevelSet R rho2) :
     F.actLevel (t + s) z = F.actLevel t (F.actLevel s z) := by
@@ -187,6 +211,12 @@ section AddGroup

 variable {T : Type u} {R : Type v} [AddGroup T] [CommRing R]

+/--
+The kernel at `-t` is inverse-like to the kernel at `t`.
+
+This is derived from the additive law and the zero-kernel axiom, not from any
+analytic fact about angles.
+-/
 theorem kernel_add_neg (F : KernelFamily T R) (t : T) :
     Vec.star (((F.kernel t : UnitKernel R) : Vec R))
       (((F.kernel (-t) : UnitKernel R) : Vec R)) = Vec.one R := by
@@ -198,6 +228,7 @@ theorem kernel_add_neg (F : KernelFamily T R) (t : T) :
     simpa using h.symm
   exact h'.trans F.kernel_zero

+/-- Evenness of the core coordinate in an additive group parameter. -/
 theorem C_neg (F : KernelFamily T R) (t : T) :
     F.C (-t) = F.C t := by
   have hq : F.C t ^ 2 + F.S t ^ 2 = 1 := F.C_sq_add_S_sq t
@@ -209,6 +240,7 @@ theorem C_neg (F : KernelFamily T R) (t : T) :
     linear_combination -F.C (-t) * hq + F.C t * hc + F.S t * hs
   exact sub_eq_zero.mp h

+/-- Oddness of the beam coordinate in an additive group parameter. -/
 theorem S_neg (F : KernelFamily T R) (t : T) :
     F.S (-t) = -F.S t := by
   have hq : F.C t ^ 2 + F.S t ^ 2 = 1 := F.C_sq_add_S_sq t
@@ -220,11 +252,13 @@ theorem S_neg (F : KernelFamily T R) (t : T) :
     linear_combination -F.S (-t) * hq - F.S t * hc + F.C t * hs
   exact eq_neg_of_add_eq_zero_left h

+/-- Difference formula for the core coordinate. -/
 theorem C_sub (F : KernelFamily T R) (t s : T) :
     F.C (t - s) = F.C t * F.C s + F.S t * F.S s := by
   rw [sub_eq_add_neg, F.C_add, F.C_neg, F.S_neg]
   ring

+/-- Difference formula for the beam coordinate. -/
 theorem S_sub (F : KernelFamily T R) (t s : T) :
     F.S (t - s) = F.S t * F.C s - F.C t * F.S s := by
   rw [sub_eq_add_neg, F.S_add, F.C_neg, F.S_neg]
````
`````
