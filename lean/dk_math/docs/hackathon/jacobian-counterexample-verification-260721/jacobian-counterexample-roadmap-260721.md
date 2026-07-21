# Jacobian Counterexample Verification ROADMAP

作成日: 2026-07-21

## 0. 方針

本 ROADMAP は、小さい checkpoint ごとに Lean が認可した事実を積み上げる。

```text
転記監査
→ 有理点衝突
→ 形式偏微分
→ determinant
→ 非単射
→ 複素数世界
→ det = 1 正規化
→ Book of Magic API
→ 展示・提出
```

最初から一般理論を作らず、有限証明書を先に閉じる。

---

## JAC-000: Project contract

### 目的

対象式、衝突点、共通像、非目標を文書で固定する。

### 成果物

```text
README.md
jacobian-counterexample-implementation-design-260721.md
jacobian-counterexample-roadmap-260721.md
codex-jacobian-counterexample-start-260721.md
```

### 完了条件

- branch が `develop` から分岐している。
- 対象写像の三成分が固定されている。
- 三つの有理点と共通像が固定されている。
- MVP が `det = -2 + collision + not injective` と定義されている。

---

## JAC-001: Polynomial syntax

### 対象

```text
DkMath/Hackathon/JacobianCounterexample3/Basic.lean
DkMath/Hackathon/JacobianCounterexample3/PolynomialMap.lean
```

### 追加対象

```lean
Var3
Poly3Q
Point3Q
x
y
z
counterexampleP
counterexampleQ
counterexampleR
counterexamplePoly
evalCounterexampleQ
```

### 検証点

- `Fin 3` の座標順序が `x=0`, `y=1`, `z=2` で固定されている。
- 有理係数が意図した形で推論される。
- `MvPolynomial.eval` が `Point3Q` をそのまま受け取れる。

### 停止点

この checkpoint では点の評価や偏微分へ進まない。

---

## JAC-002: Explicit collision

### 対象

```text
DkMath/Hackathon/JacobianCounterexample3/Collision.lean
```

### 追加対象

```lean
p0Q
p1Q
p2Q
targetQ

eval_p0Q
eval_p1Q
eval_p2Q

p0Q_ne_p1Q
p0Q_ne_p2Q
p1Q_ne_p2Q
```

### 数学契約

$$
F(p_0)=F(p_1)=F(p_2)=\left(-\frac14,0,0\right)
$$

### 実装方針

```text
ext i
fin_cases i
norm_num [all definitions]
```

`norm_num` が多項式評価を開かない場合は、局所的に `simp` または `ring_nf` を追加する。

### 完了条件

- 三点すべての評価が閉じる。
- 少なくとも `p0Q ≠ p1Q` が閉じる。
- 転記ミスがないことが Lean 計算で確認される。

### 停止点

この時点で一度レビューする。Jacobian 実装へ直行しない。

---

## JAC-003: Formal Jacobian

### 対象

```text
DkMath/Hackathon/JacobianCounterexample3/Jacobian.lean
```

### 追加対象

```lean
jacobianMatrixQ
explicitJacobianQ
jacobianMatrixQ_eq_explicit
```

### 原則

Jacobian 行列は必ず `MvPolynomial.pderiv` から生成する。

```lean
def jacobianMatrixQ : Matrix (Fin 3) (Fin 3) Poly3Q :=
  fun i j => MvPolynomial.pderiv j (counterexamplePoly i)
```

### 完了条件

九成分すべてについて、形式偏微分と明示式が一致する。

### 分岐

- `ext i j; fin_cases i <;> fin_cases j` で閉じるなら採用。
- tactic が重すぎる場合、各 row の補題へ分割する。
- 明示 Jacobian の転記は、別の手計算ではなく `pderiv` の正規化結果から作る。

---

## JAC-004: Determinant certificate

### 追加対象

```lean
jacobianMatrixQ_det_eq_neg_two
jacobianMatrixQ_det_ne_zero
```

### 数学契約

$$
\det J_F=-2
$$

### 第一経路

```text
rw [jacobianMatrixQ_eq_explicit]
rw [Matrix.det_fin_three]
ring
```

### 第二経路

`Matrix.det_fin_three` の rewrite が合わない場合、`simp [Matrix.det_fin_three]` と `ring_nf` を使う。

### 禁止

- determinant 値を仮定する。
- 外部 CAS の文字列証明書を axiom 化する。
- `native_decide` で多項式恒等式を閉じる。

### 完了条件

`jacobianMatrixQ.det = MvPolynomial.C (-2 : ℚ)` が kernel checked で閉じる。

---

## JAC-005: Rational counterexample certificate

### 対象

```text
DkMath/Hackathon/JacobianCounterexample3/Counterexample.lean
```

### 追加対象

```lean
evalCounterexampleQ_notInjective
evalCounterexampleQ_noLeftInverse
jacobianCounterexampleCertificateQ
```

### 論理経路

```text
p0Q ≠ p1Q
+
F p0Q = F p1Q
→
not injective
→
no left inverse
```

### MVP Gate

次がすべて存在する。

```text
jacobianMatrixQ_det_eq_neg_two
evalCounterexampleQ_notInjective
evalCounterexampleQ_noLeftInverse
```

ここで最初のハッカソン用実証は完成する。

---

## JAC-006: Complex scalar world

### 対象

```text
DkMath/Hackathon/JacobianCounterexample3/ComplexLift.lean
```

### 目的

古典的 Jacobian conjecture の標数零世界へ証明書を明示的に置く。

### 実装候補 A

`MvPolynomial.map` と `eval₂` の可換性を使って `ℚ → ℂ` へ輸送する。

### 実装候補 B

`ℂ` 版の三成分を同じ式で再定義し、有限計算を再証明する。

### 判断規則

- A が短く閉じるなら A。
- 輸送補題探索が膨らむなら B。

### 完了条件

```lean
jacobianCounterexampleCertificateC
```

が閉じる。

---

## JAC-007: Keller normalization

### 対象

```text
DkMath/Hackathon/JacobianCounterexample3/Normalized.lean
```

### 定義

$$
\widetilde F=\left(-\frac12P,Q,R\right)
$$

### 契約

$$
\det J_{\widetilde F}=1
$$

衝突点は元写像と同じである。

### 追加対象

```lean
normalizedCounterexample
normalizedJacobian_det_eq_one
normalizedCounterexample_notInjective
normalizedJacobianCounterexampleCertificateC
```

### 展示価値

```text
Jacobian determinant = 1
but the polynomial map is not injective
```

を一行で示せる。

---

## JAC-008: Public import and audit

### 対象

```text
DkMath/Hackathon/JacobianCounterexample3.lean
DkMath/Hackathon.lean
DkMath.lean
```

### 判断

- 初期段階では `DkMath.lean` への公開を急がない。
- ハッカソン公開面が安定した時点で aggregator を追加する。

### Audit

```lean
#print axioms jacobianCounterexampleCertificateQ
#print axioms jacobianCounterexampleCertificateC
#print axioms normalizedJacobianCounterexampleCertificateC
```

### 完了条件

対象 theorem に追加公理がない。

---

## JAC-009: Book of Magic API

### 対象

```text
DkMath/BookOfMagic/UniqueGapContract.lean
DkMath/BookOfMagic/GapCrystal.lean
```

### 追加対象

```lean
UniqueGap
not_uniqueGap_of_two
GapFiber
CrystalWorld
forgetGap
forgetGap_notInjective_of_two_gaps
```

### 意味

共有 Core に異なる二つの正しい Gap が存在すれば、忘却射影は一意性を解除する。

$$
R(C,G_1)
$$

$$
R(C,G_2)
$$

$$
G_1\ne G_2
$$

から、

$$
\neg\exists!G,\ R(C,G)
$$

を得る。

### 接続

Jacobian counterexample 本体をこの一般 API に依存させない。反例完成後の解釈 bridge とする。

---

## JAC-010: GN finite difference bridge

### 対象

```text
DkMath/BookOfMagic/GNFiniteDifference.lean
```

### 目標

一般多項式

$$
P(T)=\sum_{k=0}^d a_kT^k
$$

について、

$$
\frac{P(t+h)-P(t)}h=\sum_{k=1}^d a_kGN_k(h,t)
$$

を形式化する。

### 優先度

低い。MVP・複素版・正規化版の後に行う。

---

## JAC-011: Demo and submission package

### 対象

```text
DkMath/Hackathon/JacobianCounterexample3/Demo.lean
README.md
DEMO_CONTRACT.md
PROVENANCE.md
```

### 動画用三段構成

```text
1. Show the explicit polynomial map.
2. Lean verifies det J = 1.
3. Lean verifies two or three distinct points have the same image.
```

### `/feedback`

一本目の提出と異なる Codex Session ID を取得する。

### 完了条件

- 3 分以内の動画構成が固定される。
- README に build と theorem 導線がある。
- 公開 theorem の `#print axioms` が示せる。

---

## 全体停止規則

1. MVP より先に一般 Jacobian theory を作らない。
2. `ℚ` で閉じるものを初手から一般体へ抽象化しない。
3. `ℂ` 輸送が難しければ再定義を許す。
4. 三点全体より二点非単射を優先する。
5. determinant 証明が最大関所であり、そこへ計算資源を集中する。
6. Book of Magic API は反例 certificate 完成後に始める。
7. Principal-Part Completion は今回の ROADMAP 外とする。

## 最終登頂条件

$$
\boxed{
\det J_F=1
\quad\land\quad
\neg\operatorname{Injective}(F)
}
$$

を `ℂ` 上の明示多項式写像について Lean が認可する。
