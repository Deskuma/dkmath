# Jacobian Counterexample Lean 実装設計

作成日: 2026-07-21

## 1. 設計目的

公開された三次元多項式写像について、反例成立に必要な有限証明書だけを Lean へ固定する。

中心契約は次である。

$$
\det J_F=-2\ne0
$$

$$
p_0\ne p_1
$$

$$
F(p_0)=F(p_1)
$$

したがって、

$$
\neg\operatorname{Injective}(F)
$$

であり、左逆および多項式逆写像は存在しない。

## 2. 対象写像

$$
P(x,y,z)=(1+xy)^3z+y^2(1+xy)(4+3xy)
$$

$$
Q(x,y,z)=y+3x(1+xy)^2z+3xy^2(4+3xy)
$$

$$
R(x,y,z)=2x-3x^2y-x^3z
$$

$$
F=(P,Q,R)
$$

## 3. 層構造

```text
Layer A: Polynomial syntax
  MvPolynomial (Fin 3) ℚ

Layer B: Evaluation
  (Fin 3 → ℚ) → (Fin 3 → ℚ)

Layer C: Formal Jacobian
  pderiv から生成した 3×3 matrix

Layer D: Finite certificates
  determinant = -2
  explicit point collision

Layer E: Logical consequence
  not injective
  no left inverse

Layer F: Scalar extension
  ℚ certificate → ℂ certificate

Layer G: Book of Magic bridge
  uniqueness release / Gap crystal
```

依存方向は上から下への一方向とする。Book of Magic API から反例証明へ逆依存してはならない。

## 4. ファイル設計

### `Basic.lean`

役割:

- 型エイリアス
- 座標変数
- namespace
- 最小 import

```lean
namespace DkMath.Hackathon.JacobianCounterexample3

abbrev Var3 := Fin 3
abbrev Poly3Q := MvPolynomial Var3 ℚ
abbrev Point3Q := Var3 → ℚ

end DkMath.Hackathon.JacobianCounterexample3
```

### `PolynomialMap.lean`

役割:

- `x`, `y`, `z`
- `counterexampleP`
- `counterexampleQ`
- `counterexampleR`
- `counterexamplePoly`
- `evalCounterexampleQ`

```lean
def x : Poly3Q := MvPolynomial.X 0

def y : Poly3Q := MvPolynomial.X 1

def z : Poly3Q := MvPolynomial.X 2
```

```lean
def counterexamplePoly : Fin 3 → Poly3Q
  | 0 => counterexampleP
  | 1 => counterexampleQ
  | 2 => counterexampleR
```

```lean
def evalCounterexampleQ (p : Point3Q) : Point3Q :=
  fun i => MvPolynomial.eval p (counterexamplePoly i)
```

### `Collision.lean`

役割:

- 三点と共通像
- 三点の評価
- pairwise distinct
- 三点衝突 certificate

```lean
def p0Q : Point3Q := ![0, 0, -(1 / 4)]

def p1Q : Point3Q := ![1, -(3 / 2), 13 / 2]

def p2Q : Point3Q := ![-1, 3 / 2, 13 / 2]

def targetQ : Point3Q := ![-(1 / 4), 0, 0]
```

候補定理:

```lean
theorem eval_p0Q : evalCounterexampleQ p0Q = targetQ

theorem eval_p1Q : evalCounterexampleQ p1Q = targetQ

theorem eval_p2Q : evalCounterexampleQ p2Q = targetQ

theorem p0Q_ne_p1Q : p0Q ≠ p1Q

theorem p0Q_ne_p2Q : p0Q ≠ p2Q

theorem p1Q_ne_p2Q : p1Q ≠ p2Q
```

展示用まとめ:

```lean
theorem three_point_collision_Q :
    Pairwise (fun a b => a ≠ b) [p0Q, p1Q, p2Q] ∧
    evalCounterexampleQ p0Q = targetQ ∧
    evalCounterexampleQ p1Q = targetQ ∧
    evalCounterexampleQ p2Q = targetQ
```

`List.Pairwise` が不自然なら、三本の不等式と三本の像等式を conjunction で保持する。

### `Jacobian.lean`

役割:

- `pderiv` から Jacobian 行列を生成
- 明示 Jacobian との一致
- determinant 計算

```lean
def jacobianMatrixQ : Matrix (Fin 3) (Fin 3) Poly3Q :=
  fun i j => MvPolynomial.pderiv j (counterexamplePoly i)
```

```lean
def explicitJacobianQ : Matrix (Fin 3) (Fin 3) Poly3Q :=
  !![
    ...;
    ...;
    ...
  ]
```

候補定理:

```lean
theorem jacobianMatrixQ_eq_explicit :
    jacobianMatrixQ = explicitJacobianQ
```

```lean
theorem jacobianMatrixQ_det_eq_neg_two :
    jacobianMatrixQ.det = MvPolynomial.C (-2 : ℚ)
```

```lean
theorem jacobianMatrixQ_det_ne_zero :
    jacobianMatrixQ.det ≠ 0
```

証明戦略:

```text
ext i j
fin_cases i
fin_cases j
simp [jacobianMatrixQ, explicitJacobianQ, counterexamplePoly,
      counterexampleP, counterexampleQ, counterexampleR]
ring
```

行列式:

```text
rw [jacobianMatrixQ_eq_explicit]
rw [Matrix.det_fin_three]
ring
```

`Matrix.det_fin_three` の適用形が合わない場合は、`simp [Matrix.det_fin_three]` または `native_decide` ではなく、通常の `ring_nf` へ寄せる。

### `Counterexample.lean`

役割:

- determinant certificate と collision certificate の合流
- 非単射
- 左逆不存在

```lean
theorem evalCounterexampleQ_notInjective :
    ¬ Function.Injective evalCounterexampleQ := by
  intro h
  apply p0Q_ne_p1Q
  apply h
  rw [eval_p0Q, eval_p1Q]
```

```lean
theorem evalCounterexampleQ_noLeftInverse :
    ¬ ∃ G, Function.LeftInverse G evalCounterexampleQ := by
  rintro ⟨G, hG⟩
  exact evalCounterexampleQ_notInjective hG.injective
```

最終まとめ:

```lean
theorem jacobianCounterexampleCertificateQ :
    jacobianMatrixQ.det = MvPolynomial.C (-2 : ℚ) ∧
    (-2 : ℚ) ≠ 0 ∧
    ¬ Function.Injective evalCounterexampleQ
```

### `ComplexLift.lean`

役割:

- 古典的標数零世界である `ℂ` へ接続
- 同じ係数式を `ℂ` 上で評価
- 有理衝突点を cast

実装選択肢:

1. `MvPolynomial.map` と評価可換性を利用して輸送する。
2. `ℂ` 版を別定義し、同じ有限計算を再証明する。

期限優先では 2 を許可する。一般輸送 API の整備に時間を使わない。

候補定理:

```lean
theorem jacobianCounterexampleCertificateC

theorem evalCounterexampleC_notInjective

theorem evalCounterexampleC_noLeftInverse
```

### `Normalized.lean`

第一成分を `-1/2` 倍した写像を定義する。

$$
\widetilde F=\left(-\frac12P,Q,R\right)
$$

これにより、

$$
\det J_{\widetilde F}=1
$$

となる。

候補定理:

```lean
theorem normalizedJacobian_det_eq_one

theorem normalizedCounterexample_notInjective
```

この層は MVP 後に行う。

### `Demo.lean`

役割:

- 展示用 import surface
- `#check`
- `#print axioms`
- 動画で示す短い theorem chain

```lean
#check jacobianMatrixQ_det_eq_neg_two
#check eval_p0Q
#check eval_p1Q
#check evalCounterexampleQ_notInjective
#check jacobianCounterexampleCertificateC

#print axioms jacobianCounterexampleCertificateC
```

## 5. import 方針

初期候補:

```lean
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic
```

実際の Mathlib import graph を調査し、不要 import は削る。

## 6. 計算戦略

### 多項式恒等式

優先順位:

```text
simp
ring
ring_nf
```

### 有理点評価

優先順位:

```text
ext i
fin_cases i
norm_num
```

必要に応じて `simp [MvPolynomial.eval, ...]` を足す。

### 相異性

座標射影で閉じる。

```lean
intro h
have h0 := congrFun h 0
norm_num [p0Q, p1Q] at h0
```

### determinant

3×3 専用展開を優先し、一般 determinant 展開へ深く入らない。

## 7. 証明書 structure の判断

最初から巨大な一般 structure を作らない。

MVP は theorem conjunction で閉じる。

MVP 後に必要なら次を導入する。

```lean
structure ConstantJacobianCollisionCertificate
    (R : Type _) [CommRing R] where
  map : Fin 3 → MvPolynomial (Fin 3) R
  detValue : R
  det_ne_zero : detValue ≠ 0
  jacobian_det : ...
  source₁ source₂ : Fin 3 → R
  source_ne : source₁ ≠ source₂
  collision : ...
```

ただし、この一般化は今回の反例証明を依存させない。

## 8. Book of Magic bridge

反例完成後、次を独立モジュールとして実装する。

### Unique Gap Contract

```lean
def UniqueGap
    {Body Gap : Type _}
    (RestoreRel : Body → Gap → Prop)
    (body : Body) : Prop :=
  ∃! gap, RestoreRel body gap
```

```lean
theorem not_uniqueGap_of_two
    (h₁ : RestoreRel body gap₁)
    (h₂ : RestoreRel body gap₂)
    (hne : gap₁ ≠ gap₂) :
    ¬ UniqueGap RestoreRel body
```

### Gap Crystal

```lean
def GapFiber
    (Gap : Body → Type _)
    (RestoreRel : (b : Body) → Gap b → Prop)
    (body : Body) :=
  {gap : Gap body // RestoreRel body gap}
```

```lean
abbrev CrystalWorld :=
  Σ body : Body, GapFiber Gap RestoreRel body
```

```lean
def forgetGap : CrystalWorld Gap RestoreRel → Body :=
  Sigma.fst
```

同じ body fiber に異なる二要素があれば、`forgetGap` は非単射となる。

この一般 theorem が、反例の「根住所を忘れた多対一写像」を魔法学 API へ持ち上げる。

## 9. 停止規則

1. 係数環一般化で詰まったら `ℚ` 専用へ戻る。
2. `ℂ` への輸送が重ければ、`ℂ` 版を再定義する。
3. 三点 certificate が重ければ、論理本体は `p0Q`, `p1Q` の二点で閉じる。
4. `GNFiniteDifference` は反例 certificate 完成後に回す。
5. Laurent 主部補完は別 project とする。
6. CAS 証明書を公理として導入しない。
7. `native_decide` に依存しない。

## 10. 完成判定

MVP 完成:

```text
jacobianMatrixQ_det_eq_neg_two
+
evalCounterexampleQ_notInjective
+
evalCounterexampleQ_noLeftInverse
```

公開完成:

```text
jacobianCounterexampleCertificateC
+
#print axioms で追加公理なし
```

展示完成:

```text
normalized Jacobian determinant = 1
+
three explicit points share one image
```
