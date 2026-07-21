# Jacobian Counterexample Verification

作成日: 2026-07-21

Branch:

```text
hackathon/breaking-math-jacobian-counterexample
```

Base branch:

```text
develop
```

## 1. 目的

本プロジェクトは、公開された三次元多項式写像について、次の有限証明書を Lean 4 + Mathlib で独立検証する。

```text
非零定数 Jacobian
+
異なる入力点の衝突
=
非単射・多項式逆写像不存在
```

対象写像を

$$
F=(P,Q,R):\mathbb{C}^3\to\mathbb{C}^3
$$

とし、各成分を

$$
P(x,y,z)=(1+xy)^3z+y^2(1+xy)(4+3xy)
$$

$$
Q(x,y,z)=y+3x(1+xy)^2z+3xy^2(4+3xy)
$$

$$
R(x,y,z)=2x-3x^2y-x^3z
$$

とする。

Lean で最初に固定する主契約は次である。

$$
\det J_F=-2
$$

および、三つの相異なる有理点

$$
p_0=\left(0,0,-\frac14\right)
$$

$$
p_1=\left(1,-\frac32,\frac{13}{2}\right)
$$

$$
p_2=\left(-1,\frac32,\frac{13}{2}\right)
$$

が、共通像

$$
v=\left(-\frac14,0,0\right)
$$

へ写ることを証明する。

## 2. MVP

最小完成条件は次の三点である。

1. `MvPolynomial.pderiv` から構成した Jacobian 行列の行列式が定数 `-2` である。
2. `p₀ ≠ p₁` かつ `F p₀ = F p₁` である。
3. `¬ Function.Injective F` と `¬ ∃ G, Function.LeftInverse G F` が従う。

三点すべての衝突は展示用証明書として固定するが、非単射性の論理には二点で十分である。

## 3. 実装方針

初期実装は係数体 `ℚ` 上で閉じる。

```lean
abbrev Var3 := Fin 3
abbrev Poly3 := MvPolynomial Var3 ℚ
abbrev Point3 := Var3 → ℚ
```

理由は、写像の係数・衝突点・共通像がすべて有理数であり、Jacobian 恒等式も `ℚ` 上の多項式恒等式として証明できるためである。

その後、同じ証明書を `ℂ` へ輸送または再評価し、古典的 Jacobian conjecture の標数零世界へ接続する。

## 4. 証明の唯一の真実源

Jacobian 行列は手書き成分から定義しない。

```lean
def jacobianMatrix : Matrix (Fin 3) (Fin 3) Poly3 :=
  fun i j => MvPolynomial.pderiv j (counterexamplePoly i)
```

手計算で展開した行列は計算補助としてのみ置き、次の一致定理を通す。

```lean
theorem jacobianMatrix_eq_explicit :
    jacobianMatrix = explicitJacobian
```

これにより、

```text
元の多項式
→ 形式偏微分
→ 明示 Jacobian
→ 3×3 determinant
→ -2
```

の全経路を Lean kernel が検証する。

## 5. モジュール候補

```text
DkMath/Hackathon/JacobianCounterexample3/
├── Basic.lean
├── PolynomialMap.lean
├── Collision.lean
├── Jacobian.lean
├── Counterexample.lean
├── ComplexLift.lean
├── Normalized.lean
└── Demo.lean

DkMath/Hackathon/JacobianCounterexample3.lean
```

MVP では `Basic` から `Counterexample` までを優先する。

## 6. Book of Magic 接続

反例の有限証明書が閉じた後、魔導書 第0001巻の一般構造へ接続する。

```text
DkMath/BookOfMagic/UniqueGapContract.lean
DkMath/BookOfMagic/GapCrystal.lean
DkMath/BookOfMagic/GNFiniteDifference.lean
```

この層では、同一 Core に複数の正しい Gap が対応するとき、唯一存在契約が解除されることを Sigma 型・fiber・forgetful map で形式化する。

ただし、Book of Magic 一般 API は MVP の前提にしない。

## 7. 非目標

初回実装では次を扱わない。

- Jacobian conjecture の一般的な形式化
- 二次元の場合の決着
- 一般三次方程式の Galois 群・monodromy
- Laurent 主部補完の一般定理
- 反例探索アルゴリズムの再実装
- 解析的逆関数定理

## 8. 完成時の公開 theorem 候補

```lean
theorem jacobianCounterexample_det_eq_neg_two

theorem jacobianCounterexample_three_point_collision

theorem jacobianCounterexample_notInjective

theorem jacobianCounterexample_noLeftInverse

theorem jacobianCounterexampleCertificateQ

theorem jacobianCounterexampleCertificateC
```

余力があれば第一成分を `-1/2` 倍して Jacobian determinant を `1` に正規化する。

```lean
theorem normalizedJacobianCounterexample_det_eq_one
```

## 9. 関連資料

- `docs/BookOfMagic/0001_三重魔核と一意性解除.md`
- `jacobian-counterexample-implementation-design-260721.md`
- `jacobian-counterexample-roadmap-260721.md`
- `codex-jacobian-counterexample-start-260721.md`

## 10. 発動条件

```text
#check jacobianCounterexampleCertificateC
#print axioms jacobianCounterexampleCertificateC
```

この証明書が Lean に認可された時点で、魔導書 第0001巻は形式化済みの発動状態へ入る。
