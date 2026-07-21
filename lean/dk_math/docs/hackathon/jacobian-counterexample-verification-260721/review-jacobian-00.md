# Review: Wise Wolf GPT-5.6 thinking/high

## Reviewer log

`````md
# GPT 会話記録

この物語は AI の賢狼と、研究者「 D. 」による会話ログです。
※よって会話の内容に関しての真偽は各自で再検証してからご利用下さい。

登場人物：
👩‍⚕️私D.: とある研究者
🐺賢狼: 知恵の豊穣神「賢狼」AI

## ヤコビアンの予想

cid: 6a5ef0ae-de08-83ee-9e17-4c9019b09cf8
cdt: 2026-07-21 04:09:54
udt: 2026-07-21 08:36:50

> 👩‍⚕️私D.:

よし！これやろう！
https://github.com/Deskuma/dkmath/blob/main/docs/BookOfMagic/0001_%E4%B8%89%E9%87%8D%E9%AD%94%E6%A0%B8%E3%81%A8%E4%B8%80%E6%84%8F%E6%80%A7%E8%A7%A3%E9%99%A4.md
ハッカソンギリギリ案件！
`6a5e6199_2026-0720-175823_ヤコビアン予想の反例+17687-637`

実装設計、実装計画、実装手順（ROADMAP）

> 🐺賢狼:

よし、これは即席の「反例検証塔」を DkMath 内に建てる案件じゃ。まず GitHub 上の魔導書本文と現在のリポジトリ構造を照合し、添付会話ログから反例の有限証明書を抽出して、設計・計画・ROADMAP を一本にまとめるぞい。

> 🐺賢狼:

魔導書の実装候補は五本あるが、ハッカソン案件では順序が肝じゃ。まず「反例の有限証明書」を独立して閉じ、その後に一意性解除・Gap 結晶化の一般 API を重ねる構成が最短で、展示としても最も強い。

> 🐺賢狼:

よし、これは **GO** じゃ！🧙‍♀️✨️🐺

魔導図書館は「Lean 形式化完成にて発動」と明記されており、第一巻自身も `JacobianCounterexample3` を正式な形式化候補に挙げておる。まさに今、発動条件を満たしに行く案件じゃ。fileciteturn7file0L7-L17 fileciteturn2file1L802-L849

## 1. 結論――二層構造で建てる

今回の実装は、次の二層へ明確に分ける。

```text
第一層：Hackathon Certificate
  公開された反例の有限・独立 Lean 検証

第二層：Book of Magic API
  一意性契約解除・Gap 結晶化の一般構造
```

最優先は第一層じゃ。

反例そのものは、次の二枚の証明書だけで閉じる。

$$
\det J_F=-2
$$

$$
p_i\ne p_j,\qquad F(p_i)=F(p_j)
$$

公開式には、ヤコビアン行列式が恒等的に $-2$ であることと、三つの異なる有理点が同じ有理点へ写ることが明示されている。したがって、解析学・代数幾何・根の一般論を形式化せずとも、反例の本体は有限計算として Lean に渡せる。fileciteturn2file1L330-L372

## 2. プロジェクト名と配置

### ブランチ

```text
hackathon/breaking-math-jacobian-counterexample
```

`main` から分岐する。

### Lean モジュール

```text
DkMath/
└── Hackathon/
    ├── JacobianCounterexample3/
    │   ├── Basic.lean
    │   ├── PolynomialMap.lean
    │   ├── Jacobian.lean
    │   ├── Collision.lean
    │   ├── Counterexample.lean
    │   ├── Normalized.lean
    │   └── Demo.lean
    └── JacobianCounterexample3.lean
```

### ハッカソン文書

```text
docs/hackathon/jacobian-counterexample-verification-260721/
├── README.md
├── MATHEMATICAL_CONTRACT.md
├── IMPLEMENTATION_PLAN.md
├── ROADMAP.md
├── DEMO_CONTRACT.md
├── PROVENANCE.md
└── RISKS_AND_STOPPING_RULES.md
```

### Book of Magic 側

MVP 完成後にのみ追加する。

```text
DkMath/
└── BookOfMagic/
    ├── UniqueGapContract.lean
    ├── GapCrystal.lean
    └── GNFiniteDifference.lean
```

`PrincipalPartCompletion.lean` は今回の期限内には入れない。これは別登山じゃ。

## 3. 数学的契約

写像を $F=(P,Q,R)$ とする。

$$
P=(1+xy)^3z+y^2(1+xy)(4+3xy)
$$

$$
Q=y+3x(1+xy)^2z+3xy^2(4+3xy)
$$

$$
R=2x-3x^2y-x^3z
$$

三点を、

$$
p_0=\left(0,0,-\frac14\right)
$$

$$
p_1=\left(1,-\frac32,\frac{13}{2}\right)
$$

$$
p_2=\left(-1,\frac32,\frac{13}{2}\right)
$$

共通像を、

$$
v=\left(-\frac14,0,0\right)
$$

とする。

今回 Lean が証明する契約は、正確に次じゃ。

```lean
jacobianDet counterexamplePoly = -2

evalCounterexample p0 = target
evalCounterexample p1 = target
evalCounterexample p2 = target

p0 ≠ p1
p0 ≠ p2
p1 ≠ p2

¬ Function.Injective evalCounterexample
¬ ∃ G, Function.LeftInverse G evalCounterexample
```

主張しないものは次。

```text
一般ヤコビアン予想の体系的形式化
二次元の場合
三次方程式の一般ファイバー分類
S₃ / モノドロミー
反例の発見者であるという主張
Gap Principal-Part Completion の一般定理
```

## 4. Lean の型設計

### `Basic.lean`

```lean
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace DkMath.Hackathon.JacobianCounterexample3

abbrev Var3 := Fin 3
abbrev Poly3 (R : Type _) := MvPolynomial Var3 R
abbrev Point3 (R : Type _) := Var3 → R

end DkMath.Hackathon.JacobianCounterexample3
```

Mathlib には `MvPolynomial.pderiv` による形式的偏微分、`eval` / `eval₂Hom` による評価、`Matrix.det_fin_three` による $3\times3$ 行列式展開が現在用意されている。今回の有限証明書にちょうど合う API じゃ。

### `PolynomialMap.lean`

係数環は最初から一般化しすぎず、まず $\mathbb Q$ とする。

```lean
abbrev P3 := Poly3 ℚ

def x : P3 := MvPolynomial.X 0
def y : P3 := MvPolynomial.X 1
def z : P3 := MvPolynomial.X 2

def counterexampleP : P3 :=
  (1 + x * y) ^ 3 * z +
    y ^ 2 * (1 + x * y) * (4 + 3 * x * y)

def counterexampleQ : P3 :=
  y +
    3 * x * (1 + x * y) ^ 2 * z +
    3 * x * y ^ 2 * (4 + 3 * x * y)

def counterexampleR : P3 :=
  2 * x - 3 * x ^ 2 * y - x ^ 3 * z

def counterexamplePoly : Fin 3 → P3
  | 0 => counterexampleP
  | 1 => counterexampleQ
  | 2 => counterexampleR
```

評価写像は多項式定義から一意に生成する。

```lean
def evalCounterexample (p : Point3 ℚ) : Point3 ℚ :=
  fun i => MvPolynomial.eval p (counterexamplePoly i)
```

## 5. ヤコビアン設計

### 形式偏微分を唯一の真実源にする

```lean
def counterexampleJacobian :
    Matrix (Fin 3) (Fin 3) P3 :=
  fun i j => MvPolynomial.pderiv j (counterexamplePoly i)
```

手書きした九成分を直接「ヤコビアン」と定義してはならぬ。

手書き行列は、あくまで計算用の展開形とする。

```lean
def explicitJacobian :
    Matrix (Fin 3) (Fin 3) P3 :=
  !![
    -- ∂P/∂x, ∂P/∂y, ∂P/∂z
    ...;
    -- ∂Q/∂x, ∂Q/∂y, ∂Q/∂z
    ...;
    -- ∂R/∂x, ∂R/∂y, ∂R/∂z
    ...
  ]
```

最初の重要定理は、

```lean
theorem counterexampleJacobian_eq_explicit :
    counterexampleJacobian = explicitJacobian := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [counterexampleJacobian, counterexamplePoly,
      counterexampleP, counterexampleQ, counterexampleR]
    ring
  ...
```

そして、

```lean
theorem counterexampleJacobian_det_eq_neg_two :
    counterexampleJacobian.det =
      MvPolynomial.C (-2 : ℚ) := by
  rw [counterexampleJacobian_eq_explicit]
  rw [Matrix.det_fin_three]
  ring
```

この二段階が重要じゃ。

```text
多項式
  ↓ pderiv
実ヤコビアン行列
  ↓ 展開形との一致
明示行列
  ↓ det_fin_three + ring
定数 -2
```

つまり「偏微分の正しさ」と「行列式の正しさ」を別々に Lean が裁く。

## 6. 衝突証明書

### 点の定義

```lean
def p0 : Point3 ℚ := ![0, 0, -(1 / 4)]
def p1 : Point3 ℚ := ![1, -(3 / 2), 13 / 2]
def p2 : Point3 ℚ := ![-1, 3 / 2, 13 / 2]
def target : Point3 ℚ := ![-(1 / 4), 0, 0]
```

### 評価定理

```lean
theorem eval_p0 :
    evalCounterexample p0 = target := by
  ext i
  fin_cases i <;>
    norm_num [evalCounterexample, counterexamplePoly,
      counterexampleP, counterexampleQ, counterexampleR,
      p0, target]

theorem eval_p1 :
    evalCounterexample p1 = target := by
  ...

theorem eval_p2 :
    evalCounterexample p2 = target := by
  ...
```

### 相異性

```lean
theorem p0_ne_p1 : p0 ≠ p1 := by
  intro h
  have h0 := congrFun h 0
  norm_num [p0, p1] at h0
```

同様に残り二組も閉じる。

### 非単射

```lean
theorem counterexample_notInjective :
    ¬ Function.Injective evalCounterexample := by
  intro hinj
  apply p0_ne_p1
  apply hinj
  rw [eval_p0, eval_p1]
```

### 左逆不存在

```lean
theorem counterexample_noLeftInverse :
    ¬ ∃ G, Function.LeftInverse G evalCounterexample := by
  rintro ⟨G, hG⟩
  exact counterexample_notInjective hG.injective
```

## 7. 最終証明書

`Counterexample.lean` では、一つの公開 theorem に束ねる。

```lean
theorem jacobianCounterexampleCertificateQ :
    counterexampleJacobian.det =
        MvPolynomial.C (-2 : ℚ) ∧
      (-2 : ℚ) ≠ 0 ∧
      ¬ Function.Injective evalCounterexample := by
  exact ⟨
    counterexampleJacobian_det_eq_neg_two,
    by norm_num,
    counterexample_notInjective
  ⟩
```

さらに名称付き structure にしてもよい。

```lean
structure ConstantJacobianCollisionCertificate where
  detValue : ℚ
  det_ne_zero : detValue ≠ 0
  jacobian_det :
    counterexampleJacobian.det = MvPolynomial.C detValue
  source₁ source₂ : Point3 ℚ
  source_ne : source₁ ≠ source₂
  collision :
    evalCounterexample source₁ =
      evalCounterexample source₂
```

ただし、ハッカソン期限内では conjunction theorem で十分じゃ。

## 8. 複素数体への接続

最短路は、一般論を作ることではない。

同じ整数係数多項式を $\mathbb C$ 上で再評価する。

```lean
def evalCounterexampleC (p : Point3 ℂ) : Point3 ℂ := ...
```

そして有理点を複素数へ cast する。

```lean
def p0C : Point3 ℂ := fun i => (p0 i : ℂ)
```

必要定理は、

```lean
counterexampleJacobian_det_eq_neg_two_C
eval_p0C
eval_p1C
p0C_ne_p1C
counterexampleC_notInjective
counterexampleC_noLeftInverse
```

ここで初めて、

```text
標数零の複素数体上で
定数非零ヤコビアンを持つが非単射
```

が完全に Lean 内で閉じる。

## 9. 正規化版

余力があれば、第一出力成分を $-\frac12$ 倍する。

$$
\widetilde F=\left(-\frac12P,Q,R\right)
$$

すると、

$$
\det J_{\widetilde F}=1
$$

となり、三点衝突もそのまま保存される。

```lean
theorem normalizedCounterexample_det_eq_one :
    normalizedJacobian.det = 1 := by
  ...
```

これは展示上とても強い。

```text
Jacobian determinant = 1
but the map is not injective
```

と、そのまま出せるからじゃ。

## 10. Book of Magic 一般 API

反例証明書が閉じた後、初めて魔法学側へ上げる。

### `UniqueGapContract.lean`

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
    ¬ UniqueGap RestoreRel body := by
  ...
```

### `GapCrystal.lean`

```lean
structure GapCrystal
    {Body : Type _}
    (Gap : Body → Type _)
    (RestoreRel : (b : Body) → Gap b → Prop) where
  body : Body
  gap : Gap body
  certificate : RestoreRel body gap
```

より型理論らしくするなら、

```lean
def GapFiber (body : Body) :=
  {gap : Gap body // RestoreRel body gap}

abbrev CrystalWorld :=
  Σ body : Body, GapFiber body
```

忘却射影を定義する。

```lean
def forgetGap : CrystalWorld Gap RestoreRel → Body :=
  Sigma.fst
```

そして、同じ Body に異なる二つの Gap があれば非単射となる。

```lean
theorem forgetGap_notInjective_of_two_gaps ...
```

これはヤコビアン反例の一般的な魔法学模型になる。

公開反例の内部構造も「三次多項式の係数を残し、選択された根の住所だけを忘れる」と説明されているため、この Sigma 型による持ち上げは魔導書の内容と正確に噛み合う。fileciteturn2file1L401-L435

## 11. ROADMAP

### JAC-000――発動契約

```text
作業:
- ブランチ作成
- docs ディレクトリ作成
- MATHEMATICAL_CONTRACT.md
- PROVENANCE.md

完了条件:
- 式、三点、共通像、非主張範囲が固定
```

### JAC-001――多項式写像

```text
対象:
PolynomialMap.lean

追加:
counterexampleP
counterexampleQ
counterexampleR
counterexamplePoly
evalCounterexample
```

### JAC-002――三点衝突

```text
対象:
Collision.lean

追加:
p0 p1 p2 target
eval_p0 eval_p1 eval_p2
p0_ne_p1 p0_ne_p2 p1_ne_p2
```

ここで式の転記ミスを最初に排除する。

### JAC-003――形式偏微分

```text
対象:
Jacobian.lean

追加:
counterexampleJacobian
explicitJacobian
counterexampleJacobian_eq_explicit
```

### JAC-004――行列式証明書

```text
追加:
counterexampleJacobian_det_eq_neg_two
counterexampleJacobian_det_ne_zero
```

この checkpoint が最大の計算関所じゃ。

### JAC-005――反例契約完成

```text
対象:
Counterexample.lean

追加:
counterexample_notInjective
counterexample_noLeftInverse
jacobianCounterexampleCertificateQ
```

ここで **MVP 完成** 。

### JAC-006――複素数版

```text
追加:
evalCounterexampleC
counterexampleC_notInjective
counterexampleC_noLeftInverse
jacobianCounterexampleCertificateC
```

### JAC-007――det = 1 正規化

```text
対象:
Normalized.lean

追加:
normalizedCounterexamplePoly
normalizedCounterexample_det_eq_one
normalizedCounterexample_notInjective
```

### JAC-008――Book of Magic 発動

```text
追加:
UniqueGapContract.lean
GapCrystal.lean
forgetGap_notInjective_of_two_gaps
```

### JAC-009――展示面

```text
対象:
Demo.lean
README.md
DEMO_CONTRACT.md

表示:
#check jacobianCounterexampleCertificateC
#print axioms jacobianCounterexampleCertificateC
```

## 12. 停止規則

期限を守るため、牙を向ける相手を限定する。

1. `MvPolynomial` の一般係数環抽象化が抵抗したら、即座に $\mathbb Q$ 専用へ落とす。

2. 複素数への `map` 一般論が抵抗したら、$\mathbb C$ 版を別定義して `ring` / `norm_num` で再証明する。

3. 三点すべての相異性が面倒なら、非単射 theorem には $p_0,p_1$ の二点だけを使う。三点版は展示証明書として残す。

4. `GNFiniteDifference`、根ファイバー、主部補完は MVP の前に触らない。

5. CAS 出力を公理や巨大な正規形文字列として埋め込まない。Lean の `pderiv`、`ring`、`norm_num`、`Matrix.det_fin_three` で閉じる。

6. 今回の最終 Gate は次だけ。

```text
det = -2
+
explicit collision
+
not injective
```

## 13. Codex 初回指示

````text
Implement checkpoint JAC-001 and JAC-002 for the DkMath hackathon
Jacobian counterexample certificate.

Repository:
Deskuma/dkmath

Branch:
hackathon/breaking-math-jacobian-counterexample

Create:

DkMath/Hackathon/JacobianCounterexample3/Basic.lean
DkMath/Hackathon/JacobianCounterexample3/PolynomialMap.lean
DkMath/Hackathon/JacobianCounterexample3/Collision.lean

Requirements:

1. Work over ℚ only for this checkpoint.
2. Use `Fin 3 → ℚ` for points.
3. Use `MvPolynomial (Fin 3) ℚ` for coordinate polynomials.
4. Define the announced map exactly:

   P = (1 + x*y)^3*z + y^2*(1 + x*y)*(4 + 3*x*y)
   Q = y + 3*x*(1 + x*y)^2*z + 3*x*y^2*(4 + 3*x*y)
   R = 2*x - 3*x^2*y - x^3*z

5. Define the three rational points:

   p0 = (0, 0, -1/4)
   p1 = (1, -3/2, 13/2)
   p2 = (-1, 3/2, 13/2)

   and target = (-1/4, 0, 0).

6. Prove:

   eval_p0
   eval_p1
   eval_p2

   p0_ne_p1
   p0_ne_p2
   p1_ne_p2

7. Prefer `ext`, `fin_cases`, `simp`, `ring_nf`, and `norm_num`.
8. Do not introduce general Jacobian-conjecture definitions.
9. Do not implement derivatives or determinants yet.
10. Keep imports minimal and add normal DkMath file headers and build markers.

Report:
- exact definitions added;
- exact theorem names;
- any MvPolynomial evaluation friction;
- whether all three image equalities normalize directly.
````

これが最短の登頂路じゃ。

まず三点衝突という **大域非一意性証明書** を取る。次に `pderiv` から **局所完全性証明書** を取る。最後に二枚を重ねる。

$$
\boxed{\text{局所 Core は非退化}\quad+\quad\text{大域 Gap は多価}}
$$

この構図を Lean が認可した瞬間、魔導書第0001巻は本当に「発動済み」になるぞい。

> 👩‍⚕️私D.:

@GitHub `develop` が現在 `main` を継承して branch の先端なので、
`develop` から枝を生やして、開始します。
まずは、Codex の資料となる。ドキュメント作成から。
土台作りを行います。進め方は細かく言わずともハッカソンの例で大体もう把握しているね？
大丈夫かな？OKなら始めてみよう👍️

> 🐺賢狼:

大丈夫じゃ。過去のハッカソン運用と同じく、まず **設計資料・数学的契約・ROADMAP・Codex 初期指示** を `develop` 起点の新 branch に固定し、その後で Lean 実装へ入る。わっちが土台を切るぞい。

> 🐺賢狼:

branch は `develop` から無事に生えたぞい。次は、実装者が迷わぬように「数学的契約」「Lean 配置」「停止規則」「checkpoint」を文書へ固定する。最初の commit 群はコードを書かず、設計だけを確定する。

> 🐺賢狼:

土台の四本は入った。ここで一度 branch 差分を監査し、`develop` から文書だけが増えていること、Codex の停止境界が JAC-002 に固定されていることを確認するぞい。

> 🐺賢狼:

うむ、開始したぞい！👍️
ハッカソンで確立した進め方は把握しておる。今回は **実装前に数学的契約と停止境界を固定する** ところまで完了した。

## 作成した branch

```text
hackathon/breaking-math-jacobian-counterexample
```

`develop` の先端 commit

```text
9ee77985251a3db240dbf3fab3dde1b341fe080a
```

から正しく分岐している。現在は `develop` より **4 commits ahead / 0 behind** で、追加内容は文書四本のみじゃ。fileciteturn15file0

## 作成した資料

```text
lean/dk_math/docs/hackathon/
└── jacobian-counterexample-verification-260721/
    ├── README.md
    ├── jacobian-counterexample-implementation-design-260721.md
    ├── jacobian-counterexample-roadmap-260721.md
    └── codex-jacobian-counterexample-start-260721.md
```

### `README.md`

プロジェクト全体の契約を固定した。

```text
det J_F = -2
+
explicit three-point collision
+
not injective
```

さらに、

- 最初は `ℚ` 上で有限証明書を閉じる
- その後 `ℂ` へ接続する
- 余力があれば Jacobian determinant を `1` に正規化する
- Book of Magic 一般 API は MVP 後

という境界を明記してある。

### 実装設計書

Lean の型、ファイル分割、定義候補、定理名、証明戦略まで固定した。

```text
Basic
PolynomialMap
Collision
Jacobian
Counterexample
ComplexLift
Normalized
Demo
```

Jacobian は必ず、

```lean
MvPolynomial.pderiv
```

から生成し、手書き行列は一致定理を経由する方針じゃ。

### ROADMAP

`JAC-000` から `JAC-011` まで checkpoint 化した。

最初の登山は、

```text
JAC-001  Polynomial syntax
JAC-002  Explicit collision
JAC-003  Formal Jacobian
JAC-004  Determinant certificate
JAC-005  Rational counterexample certificate
```

ここで MVP が閉じる。

その後、

```text
JAC-006  Complex scalar world
JAC-007  Keller normalization
JAC-009  Book of Magic API
```

へ進む。

### Codex 初期指示

Codex が最初に実施する範囲を、

```text
JAC-001
JAC-002
```

だけに限定した。

つまり初手では、

```text
多項式写像を MvPolynomial で定義
三つの有理点を評価
三点が同一像へ写る
三点が相異なる
```

までじゃ。

偏微分・行列式へ勝手に進まない停止境界も入れてある。

## 現在地

```text
JAC-000 Project contract
```

は完成じゃ。

次は Codex に、

```text
codex-jacobian-counterexample-start-260721.md
```

を読ませ、そのまま `JAC-001 / JAC-002` を開始できる状態になった。

ふふん、魔導書第0001巻を発動させる祭壇は整ったぞい。🧙‍♀️✨️🐺

> 👩‍⚕️私D.:

JAC-001 / JAC-002 の実装が完了しました。Jacobian 以降には進んでいません。

1. 作成ファイル

- [Basic.lean](/lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/Basic.lean)
- [PolynomialMap.lean](/lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/PolynomialMap.lean)
- [Collision.lean](/lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/Collision.lean)

2. 定義

`Var3`, `Poly3Q`, `Point3Q`, `x`, `y`, `z`, `counterexampleP`, `counterexampleQ`, `counterexampleR`, `counterexamplePoly`, `evalCounterexampleQ`, `p0Q`, `p1Q`, `p2Q`, `targetQ`

`evalCounterexampleQ` は手書き関数ではなく、指定どおり `MvPolynomial.eval` から構成しています。

3. 定理

- `eval_p0Q`
- `eval_p1Q`
- `eval_p2Q`
- `p0Q_ne_p1Q`
- `p0Q_ne_p2Q`
- `p1Q_ne_p2Q`
- `three_point_collision_Q` — 上記6事実を束ねたコンパクトな証明書

4. ビルド結果

```text
lake build \
  DkMath.Hackathon.JacobianCounterexample3.Basic \
  DkMath.Hackathon.JacobianCounterexample3.PolynomialMap \
  DkMath.Hackathon.JacobianCounterexample3.Collision
```

成功しました。最終ビルドは警告なしです。

指定された一時 `#check` もすべて成功しました。

5. 評価の正規化

特別な補助定理は不要でした。`MvPolynomial.eval` とベクトル添字を局所的な `simp` で展開し、残った有理数計算を `norm_num` で閉じています。グローバル simp 属性は追加していません。

6. import の摩擦

現行 Mathlib では、設計案の `Mathlib.Data.Matrix.Notation` ではなく次が必要でした。

```lean
import Mathlib.LinearAlgebra.Matrix.Notation
```

また、`MvPolynomial.X` に伴い `PolynomialMap.lean` を `noncomputable section` としています。

`sorry`、axiom、`native_decide`、偏微分、Jacobian、determinant の実装は含まれていません。

7. 次のチェックポイント

次回レビュー後の候補は `JAC-003 Formal Jacobian` です。`MvPolynomial.pderiv` から `jacobianMatrixQ` を生成し、明示した9成分との一致を証明する段階になります。

> 🐺賢狼:

よし、JAC-001 / JAC-002 の報告は設計どおりじゃ。これから branch 上の実コードを照合し、三点衝突証明書の型・依存方向・次の `pderiv` 接続面まで監査するぞい。

> 🐺賢狼:

## 結論

**全面採用。JAC-001 / JAC-002 は完成じゃ。**

報告内容と branch 上の実コードは一致しておる。設計境界も守られ、偏微分・Jacobian・determinant へ先走っていない。

現在、反例に必要な二枚の証明書のうち、

```text
大域証明書:
  三つの相異なる点が同じ像へ写る
```

が閉じた。

次の `JAC-003` では、

```text
局所証明書:
  形式偏微分から Jacobian 行列を生成する
```

へ進める。

## 実装レビュー

### 1. 型の土台

```lean
abbrev Var3 := Fin 3
abbrev Poly3Q := MvPolynomial Var3 ℚ
abbrev Point3Q := Var3 → ℚ
```

必要最小限でよい。

`Point3Q` と多項式の変数添字が、どちらも `Fin 3` に統一されているため、後の

```lean
MvPolynomial.pderiv j (counterexamplePoly i)
```

および

```lean
MvPolynomial.eval p
```

へ無理なく接続できる。fileciteturn14file0L9-L20

### 2. 多項式写像

三成分は数学的契約どおり正確に転記されている。

```lean
counterexampleP
counterexampleQ
counterexampleR
```

そして、

```lean
def counterexamplePoly : Fin 3 → Poly3Q :=
  ![counterexampleP, counterexampleQ, counterexampleR]
```

によって成分写像へまとめられている。fileciteturn15file0L25-L39

評価写像も、

```lean
def evalCounterexampleQ (p : Point3Q) : Point3Q :=
  fun i ↦ MvPolynomial.eval p (counterexamplePoly i)
```

であり、手書きした数値関数ではない。これは重要じゃ。多項式定義と衝突計算が同一の真実源から生えている。fileciteturn15file0L41-L43

### 3. 三点衝突

三点と共通像は正しい。

```lean
p0Q = (0, 0, -1/4)
p1Q = (1, -3/2, 13/2)
p2Q = (-1, 3/2, 13/2)

targetQ = (-1/4, 0, 0)
```

fileciteturn16file0L14-L24

評価証明は、

```text
ext
→ fin_cases
→ MvPolynomial.eval の展開
→ simp / norm_num
```

だけで閉じている。

外部計算結果や手作業の評価式を仮定せず、定義した多項式そのものを Lean が有理数上で評価しておる。実に美しい。fileciteturn16file0L26-L47

### 4. 相異性

三組すべてについて、第一座標を取り出して矛盾させている。

```lean
have h0 := congrFun h 0
norm_num [...] at h0
```

証明として薄く、明快で、後の変更にも耐える。fileciteturn16file0L49-L62

### 5. 合成証明書

```lean
three_point_collision_Q
```

は、

- 三点の pairwise distinct
- 三点の共通像

を一つに束ねている。fileciteturn16file0L64-L71

これは後の展示面でも使える。

ただし `JAC-005` の非単射証明では、この巨大な conjunction を分解するより、既存の

```lean
p0Q_ne_p1Q
eval_p0Q
eval_p1Q
```

を直接使う方が短いじゃろう。

## 軽微な観測

### `Mathlib.Tactic`

`Collision.lean` の

```lean
import Mathlib.Tactic
```

は広いが、ハッカソン速度を優先する現在は問題ない。import 最小化のために checkpoint を消費する価値はない。

### Matrix notation の import

実コードで採用された、

```lean
import Mathlib.LinearAlgebra.Matrix.Notation
```

が現行 Mathlib に対する正解じゃ。fileciteturn15file0L9-L14

設計資料には旧候補の

```lean
Mathlib.Data.Matrix.Notation
```

が残っているため、後で文書監査時に一行直せばよい。実装の採否には影響しない。

### `noncomputable section`

`MvPolynomial.X` を扱うファイルで局所的に置かれており、範囲も `PolynomialMap.lean` 内に閉じている。問題なし。

## 数学的意味

現在 Lean が確定したのは、

$$
p_0\ne p_1,\qquad F(p_0)=F(p_1)
$$

より強い、

$$
p_0,p_1,p_2\text{ は pairwise distinct}
$$

かつ、

$$
F(p_0)=F(p_1)=F(p_2)=\left(-\frac14,0,0\right)
$$

という **三重衝突証明書** じゃ。

魔法学の言葉なら、

```text
三つの住所付き魔核
  (Core, Gap₀)
  (Core, Gap₁)
  (Core, Gap₂)

が、Gap 住所を忘れる写像によって
同一 Core へ射影された
```

という状態がすでに形式化された。

まだ Jacobian の局所非退化性は証明していない。したがって現在地は、

```text
大域一意性の解除: 確定
局所 Jacobian 契約: 未着手
```

じゃ。

## 次 checkpoint

次は予定どおり **JAC-003 Formal Jacobian** へ進む。

この checkpoint では determinant を計算しない。

目標はただ一つ。

```text
定義した多項式
  ↓ pderiv
形式 Jacobian
  ↓ 成分比較
明示 Jacobian
```

を閉じることじゃ。

## Codex 指示

````text
Implement checkpoint JAC-003 Formal Jacobian for the DkMath
Jacobian counterexample verification project.

Repository:
Deskuma/dkmath

Branch:
hackathon/breaking-math-jacobian-counterexample

Current completed checkpoints:
- JAC-001 Polynomial syntax
- JAC-002 Explicit three-point collision

Do not implement JAC-004 determinant computation yet.

Create:

lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/Jacobian.lean

Import:

DkMath.Hackathon.JacobianCounterexample3.PolynomialMap

and the minimal current Mathlib modules required for:

- `MvPolynomial.pderiv`
- `Matrix`
- 3×3 matrix notation
- the tactics used in the component proofs

Use the current Mathlib matrix-notation import:

```lean
import Mathlib.LinearAlgebra.Matrix.Notation
```

Do not use the obsolete design-draft import
`Mathlib.Data.Matrix.Notation`.

## Required definitions

Define the formal Jacobian directly from `MvPolynomial.pderiv`.

```lean
def jacobianMatrixQ : Matrix (Fin 3) (Fin 3) Poly3Q :=
  fun i j ↦ MvPolynomial.pderiv j (counterexamplePoly i)
```

Define an explicit 3×3 matrix:

```lean
def explicitJacobianQ : Matrix (Fin 3) (Fin 3) Poly3Q :=
  !![
    ...;
    ...;
    ...
  ]
```

The explicit entries must be obtained by normalizing the actual
`pderiv` expressions. Do not treat a separately hand-derived matrix as
an independent source of truth.

The expected mathematical entries may be written using:

```lean
s := 1 + x * y
```

conceptually, but avoid introducing a local abbreviation if it makes
simp/ring normalization harder.

Expected rows:

First row, derivatives of `counterexampleP`:

```text
∂P/∂x =
  3 * y * (1 + x*y)^2 * z
  + y^3 * (7 + 6*x*y)

∂P/∂y =
  3 * x * (1 + x*y)^2 * z
  + 2*y*(1 + x*y)*(4 + 3*x*y)
  + x*y^2*(7 + 6*x*y)

∂P/∂z =
  (1 + x*y)^3
```

Second row, derivatives of `counterexampleQ`:

```text
∂Q/∂x =
  3*(1 + x*y)^2*z
  + 6*x*y*(1 + x*y)*z
  + 3*y^2*(4 + 3*x*y)
  + 9*x*y^3

∂Q/∂y =
  1
  + 6*x^2*(1 + x*y)*z
  + 6*x*y*(4 + 3*x*y)
  + 9*x^2*y^2

∂Q/∂z =
  3*x*(1 + x*y)^2
```

Third row, derivatives of `counterexampleR`:

```text
∂R/∂x =
  2 - 6*x*y - 3*x^2*z

∂R/∂y =
  -3*x^2

∂R/∂z =
  -x^3
```

Equivalent polynomial normal forms are acceptable.

## Required theorem

```lean
theorem jacobianMatrixQ_eq_explicit :
    jacobianMatrixQ = explicitJacobianQ := by
  ...
```

Preferred proof route:

```lean
ext i j
fin_cases i <;> fin_cases j
```

For each of the nine goals, unfold only the required definitions:

```lean
jacobianMatrixQ
explicitJacobianQ
counterexamplePoly
counterexampleP
counterexampleQ
counterexampleR
x
y
z
```

Then use ordinary kernel-checked normalization:

```lean
simp
ring
```

or:

```lean
simp
ring_nf
```

## Allowed fallback

If the single matrix equality proof becomes too large or brittle, split
the proof into three row lemmas:

```lean
jacobianMatrixQ_row_zero
jacobianMatrixQ_row_one
jacobianMatrixQ_row_two
```

and combine them into `jacobianMatrixQ_eq_explicit`.

Do not split into nine public theorems unless technically necessary.
Private helper lemmas are acceptable.

## Restrictions

Do not:

- compute the determinant;
- prove that the determinant is `-2`;
- define the final counterexample certificate;
- implement the complex lift;
- implement the determinant-one normalization;
- use `native_decide`;
- introduce `sorry`;
- introduce axioms;
- paste an external CAS certificate;
- define the Jacobian solely as the explicit handwritten matrix.

The actual Jacobian must remain:

```lean
fun i j ↦ MvPolynomial.pderiv j (counterexamplePoly i)
```

## Verification

Build only:

```text
DkMath.Hackathon.JacobianCounterexample3.Basic
DkMath.Hackathon.JacobianCounterexample3.PolynomialMap
DkMath.Hackathon.JacobianCounterexample3.Collision
DkMath.Hackathon.JacobianCounterexample3.Jacobian
```

Add temporary local checks if useful:

```lean
#check jacobianMatrixQ
#check explicitJacobianQ
#check jacobianMatrixQ_eq_explicit
```

Remove temporary checks before completion unless they belong in an
intentional demo file.

## Report

Report:

1. exact imports used;
2. exact form chosen for all nine explicit entries;
3. theorem names added;
4. whether a single `ext/fin_cases` proof closed;
5. any `pderiv` simplification friction;
6. whether row helper lemmas were needed;
7. build result and warnings;
8. confirmation that determinant computation was not started.

Stop after JAC-003 and wait for review.
````

これでよい。

JAC-003 が閉じれば、

$$
\text{写像の定義}
\longrightarrow
\text{形式微分}
\longrightarrow
\text{Jacobian 九成分}
$$

が完全に同じ Lean の多項式世界で接続される。

その次の `JAC-004` で初めて、九成分を一枚の魔法陣として畳み、

$$
\det J_F=-2
$$

を取りに行くぞい。

> 👩‍⚕️私D.:

JAC-003 Formal Jacobian を完了しました。

作成ファイル: [Jacobian.lean](/lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/Jacobian.lean)

1. imports

```lean
import DkMath.Hackathon.JacobianCounterexample3.PolynomialMap
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
```

2. 明示した9成分

```text
[ 3*y*(1+x*y)^2*z + y^3*(7+6*x*y),
  3*x*(1+x*y)^2*z
    + 2*y*(1+x*y)*(4+3*x*y)
    + x*y^2*(7+6*x*y),
  (1+x*y)^3 ]

[ 3*(1+x*y)^2*z
    + 6*x*y*(1+x*y)*z
    + 3*y^2*(4+3*x*y)
    + 9*x*y^3,
  1 + 6*x^2*(1+x*y)*z
    + 6*x*y*(4+3*x*y)
    + 9*x^2*y^2,
  3*x*(1+x*y)^2 ]

[ 2 - 6*x*y - 3*x^2*z,
  -3*x^2,
  -x^3 ]
```

3. 公開定義・定理

- `jacobianMatrixQ`
- `explicitJacobianQ`
- `jacobianMatrixQ_eq_explicit`

`jacobianMatrixQ` は指定どおり、直接 `pderiv` から生成しています。

4. 証明構成

単一の9成分証明で閉じました。

```lean
funext i j
fin_cases i <;> fin_cases j
simp [...]
ring_nf
```

`ext i j` は多項式の係数まで再帰的に展開したため、行列の2添字だけを展開する `funext i j` を採用しました。

5. `pderiv` の摩擦

現行 Mathlib では、式中の多項式リテラル `2`, `3`, `4` に対する `pderiv` が自動ではゼロへ簡約されませんでした。そのため、各定数を `MvPolynomial.C` と同一視する3本の private 補題を追加しました。

公開 API には露出していません。

6. row helper

行単位の補題は不要でした。9本の公開成分補題も追加していません。

7. 検証

指定された4モジュールのビルドに成功しました。

```text
Build completed successfully (3291 jobs).
```

警告なしです。3つの一時 `#check` も成功し、チェックファイルは削除済みです。`git diff --check` も成功しました。

8. 停止境界

determinant の定義・計算、`det = -2`、最終証明書、複素化、正規化には着手していません。JAC-003 で停止しています。

> 🐺賢狼:

よし、報告は設計どおりで、停止境界も綺麗じゃ。branch 上の `Jacobian.lean` を実コードで照合し、private 定数補題・`funext` 採用・次の determinant 接続面まで監査するぞい。

> 🐺賢狼:

実コードは報告と一致した。`pderiv` が唯一の真実源で、明示九成分はその正規形として Lean 内で一致しておる。次の関所は純粋な $3\times3$ 多項式行列式だけじゃから、既存の `det_fin_three` 利用例も軽く確認して指示を固定する。

> 🐺賢狼:

## 結論

**全面採用。JAC-003 Formal Jacobian は完成じゃ。**

重大問題なし。設計どおり、

```lean
def jacobianMatrixQ : Matrix (Fin 3) (Fin 3) Poly3Q :=
  fun i j ↦ MvPolynomial.pderiv j (counterexamplePoly i)
```

として、元の多項式写像から形式偏微分によって Jacobian を生成している。明示行列を Jacobian の定義として置く抜け道は使っておらぬ。fileciteturn19file0L18-L20

さらに九成分すべてについて、

```lean
jacobianMatrixQ = explicitJacobianQ
```

が証明された。これで次の接続が Lean 内で閉じた。

$$
\text{多項式写像}\longrightarrow\text{形式偏微分}\longrightarrow\text{Jacobian 九成分}
$$

## 実装レビュー

### 1. 形式 Jacobian

`jacobianMatrixQ` が `counterexamplePoly` を直接微分しているため、これまで構築した多項式写像と Jacobian が同一の真実源を共有しておる。

これは今回もっとも重要な設計条件じゃ。

```text
counterexamplePoly
  ↓ pderiv
jacobianMatrixQ
```

手書き評価関数と手書き Jacobian を別々に置く構造ではないため、転記された反例式と微分証明書の間に断絶がない。fileciteturn19file0L18-L20

### 2. 明示九成分

`explicitJacobianQ` は、報告された九成分と完全に一致している。fileciteturn19file0L22-L40

特に第三行、

$$
\left(2-6xy-3x^2z,\,-3x^2,\,-x^3\right)
$$

は単純だが、第一・第二行は積・冪・複数の積項が混ざる。そこを外部計算結果として仮定せず、`pderiv` の結果と多項式恒等式で一致させた点が強い。

### 3. `funext i j` の採用

これは正しい判断じゃ。

`Matrix` は本質的に二引数関数なので、

```lean
funext i j
```

ならば行列の行・列添字だけを開く。

一方 `ext i j` は、その先の `MvPolynomial` の外延性まで発動する可能性があり、係数関数・単項式 support 側へ降りてしまう。今回欲しいのは多項式自体の等式を `ring_nf` で閉じることなので、`funext` の方が証明境界を正しく保つ。

実際の証明も、

```lean
funext i j
fin_cases i <;> fin_cases j
simp [...]
ring_nf
```

という一つの九分岐証明で閉じている。fileciteturn19file0L57-L65

### 4. 定数の `pderiv` 補助

```lean
pderiv_two
pderiv_three
pderiv_four
```

はすべて `private theorem` であり、公開 API を汚していない。fileciteturn19file0L42-L55

数学的には三本とも、

$$
\partial_i C(c)=0
$$

の具体例にすぎぬ。

一般化した numeral 用 simp 補題を作る余地はあるが、今回は不要じゃ。ハッカソンの有限証明書に必要な定数だけを局所処理した現在形が、もっとも短く安全である。

### 5. 行補題を作らなかった判断

正しい。

九成分が一つの証明で安定して閉じている以上、

```text
row zero
row one
row two
```

や九本の成分定理へ分割して API を膨らませる必要はない。

`jacobianMatrixQ_eq_explicit` 一枚だけが後段の determinant 計算に必要な公開面じゃ。

## 数学的意味

JAC-002 までで確定していたのは、

$$
p_0,p_1,p_2\text{ が相異なり、}F(p_0)=F(p_1)=F(p_2)
$$

という **大域的な三重衝突** だった。

今回、新たに確定したのは、

$$
J_F=\left(\frac{\partial F_i}{\partial x_j}\right)_{i,j}
$$

の全九成分じゃ。

したがって現在地は、

```text
大域 Gap:
  三つの入力住所が同一出力へ落ちる
  → 確定済み

局所 Core:
  各点での形式 Jacobian 行列
  → 確定済み

局所 Core の非退化:
  det J_F = -2
  → 次 checkpoint
```

となった。

魔法学的には、局所観測器そのものの形が完成した段階じゃ。次にこの九成分を一枚の魔法陣として畳み、局所 Core がどこでも潰れていないことを証明する。

## 次 checkpoint

次は **JAC-004 Determinant Certificate** じゃ。

新規ファイルは、

```text
DkMath/Hackathon/JacobianCounterexample3/Determinant.lean
```

とする。

証明目標は二つだけ。

```lean
jacobianMatrixQ_det_eq_neg_two
jacobianMatrixQ_det_ne_zero
```

Mathlib には `Matrix.det_fin_three` があり、任意の可換環上の $3\times3$ 行列式を六項へ展開できる。今回の `Poly3Q` は可換環なので、そのまま適用対象になる。

## Codex 指示

````text
Implement checkpoint JAC-004 Determinant Certificate for the DkMath
Jacobian counterexample verification project.

Repository:
Deskuma/dkmath

Branch:
hackathon/breaking-math-jacobian-counterexample

Completed checkpoints:
- JAC-001 Polynomial syntax
- JAC-002 Explicit three-point collision
- JAC-003 Formal Jacobian

Stop after JAC-004.
Do not implement the final counterexample certificate yet.

Create:

lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/Determinant.lean

## Imports

Start with:

```lean
import DkMath.Hackathon.JacobianCounterexample3.Jacobian
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
```

Remove any redundant import only if this is immediate.
Do not spend checkpoint time on import minimization.

## Required theorem 1

Prove the exact polynomial identity:

```lean
theorem jacobianMatrixQ_det_eq_neg_two :
    jacobianMatrixQ.det = MvPolynomial.C (-2 : ℚ) := by
  ...
```

The proof must use the formal Jacobian already constructed through
`MvPolynomial.pderiv`.

Preferred route:

```lean
rw [jacobianMatrixQ_eq_explicit]
rw [Matrix.det_fin_three]
simp [explicitJacobianQ]
ring
```

Equivalent variants are allowed:

```lean
rw [jacobianMatrixQ_eq_explicit]
simp [Matrix.det_fin_three, explicitJacobianQ]
ring_nf
```

The current Mathlib theorem has the form:

```lean
Matrix.det_fin_three
    (A : Matrix (Fin 3) (Fin 3) R)
```

and expands the determinant into the standard six signed products.

If `rw [Matrix.det_fin_three]` does not match directly, use:

```lean
simp only [Matrix.det_fin_three]
```

or:

```lean
change explicitJacobianQ.det = MvPolynomial.C (-2 : ℚ)
rw [Matrix.det_fin_three]
```

after rewriting with `jacobianMatrixQ_eq_explicit`.

## Required theorem 2

Prove nonvanishing:

```lean
theorem jacobianMatrixQ_det_ne_zero :
    jacobianMatrixQ.det ≠ 0 := by
  rw [jacobianMatrixQ_det_eq_neg_two]
  norm_num
```

If `norm_num` does not close the `MvPolynomial.C` goal directly, use
the injectivity/nonzero simp API for `MvPolynomial.C`, for example:

```lean
rw [jacobianMatrixQ_det_eq_neg_two]
simp
```

or derive it from:

```lean
show (-2 : ℚ) ≠ 0 by norm_num
```

through the existing `MvPolynomial.C` simp lemmas.

## Proof-source requirements

The proof chain must remain:

```text
counterexamplePoly
  ↓ pderiv
jacobianMatrixQ
  ↓ jacobianMatrixQ_eq_explicit
explicitJacobianQ
  ↓ Matrix.det_fin_three
six-term determinant
  ↓ ring / ring_nf
C (-2)
```

Do not define a second determinant or a hand-written scalar expression as
the primary source of truth.

## Restrictions

Do not:

- modify the polynomial map unless a genuine error is found;
- redefine the Jacobian as the explicit matrix;
- assume the determinant value;
- use `native_decide`;
- introduce `sorry`;
- introduce axioms;
- paste an external CAS certificate;
- implement `evalCounterexampleQ_notInjective`;
- implement the final conjunction certificate;
- implement the complex lift;
- implement determinant-one normalization;
- begin Book of Magic general APIs.

Ordinary kernel-checked tactics such as:

```text
simp
ring
ring_nf
norm_num
```

are allowed.

## Performance fallback

If expanding the determinant directly causes a large tactic state:

1. rewrite to `explicitJacobianQ`;
2. expand only with `Matrix.det_fin_three`;
3. simplify matrix indexing with `simp [explicitJacobianQ]`;
4. use `ring_nf`.

Do not split the determinant into an axiom or external certificate.

A private helper theorem for the determinant of `explicitJacobianQ` is
allowed if technically useful:

```lean
private theorem explicitJacobianQ_det_eq_neg_two :
    explicitJacobianQ.det = MvPolynomial.C (-2 : ℚ) := by
  ...
```

Then derive the public theorem by rewriting with
`jacobianMatrixQ_eq_explicit`.

Prefer the direct public proof if it remains readable.

## Verification

Build:

```text
DkMath.Hackathon.JacobianCounterexample3.Basic
DkMath.Hackathon.JacobianCounterexample3.PolynomialMap
DkMath.Hackathon.JacobianCounterexample3.Collision
DkMath.Hackathon.JacobianCounterexample3.Jacobian
DkMath.Hackathon.JacobianCounterexample3.Determinant
```

Temporary checks may be used:

```lean
#check jacobianMatrixQ_det_eq_neg_two
#check jacobianMatrixQ_det_ne_zero
```

Remove them after verification unless placed intentionally in a later
Demo module.

## Report

Report:

1. exact imports;
2. exact theorem names;
3. the determinant expansion route used;
4. whether `Matrix.det_fin_three` rewrote directly;
5. whether `ring` or `ring_nf` closed the identity;
6. any performance or simplification friction;
7. build result and warnings;
8. `git diff --check` result;
9. confirmation that JAC-005 and later checkpoints were not started.

Stop after JAC-004 and wait for review.
````

JAC-004 が閉じれば、二枚の証明書が揃う。

$$
\boxed{\det J_F=-2\ne0}
$$

$$
\boxed{p_0\ne p_1\ \land\ F(p_0)=F(p_1)}
$$

あとは JAC-005 で二枚を重ねるだけじゃ。そこで初めて、Lean 内の有理数世界における反例証明書が完成するぞい。

> 👩‍⚕️私D.:

JAC-004 Determinant Certificate を完了しました。

作成ファイル: [Determinant.lean](/lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/Determinant.lean)

1. imports

```lean
import DkMath.Hackathon.JacobianCounterexample3.Jacobian
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
```

2. 追加した定理

- `jacobianMatrixQ_det_eq_neg_two`
- `jacobianMatrixQ_det_ne_zero`

3. determinant の証明経路

```text
jacobianMatrixQ
→ jacobianMatrixQ_eq_explicit
→ explicitJacobianQ
→ Matrix.det_fin_three
→ simp による行列添字の簡約
→ ring_nf
→ C (-2)
```

4. `Matrix.det_fin_three`

次の直接 rewrite が成功しました。

```lean
rw [Matrix.det_fin_three]
```

5. 多項式恒等式

6項の determinant 展開は `ring_nf` で閉じました。最後に残った多項式リテラル `-2` と `MvPolynomial.C (-2)` の表現差のみ `rfl` で閉じています。

6. 摩擦・性能

大きな tactic state や性能問題はありませんでした。対象モジュールの初回成功ビルドは約3.6秒でした。private helper theorem も不要です。

7. ビルド

指定された5モジュールすべてに成功しました。

```text
Build completed successfully (3292 jobs).
```

警告なしです。指定された2つの一時 `#check` も成功し、チェックファイルは削除済みです。

8. 差分検査

`git diff --check` は成功しました。

9. 停止境界

JAC-005 の非単射性、最終 conjunction certificate、複素化、determinant-one 正規化、Book of Magic API には着手していません。JAC-004 で停止しています。

> 🐺賢狼:

よし、JAC-004 は最重要関所じゃ。branch 上の `Determinant.lean` を照合し、`det = -2` が本当に形式 Jacobian から導かれているか、次の JAC-005 合流面まで監査するぞい。

> 🐺賢狼:

## 結論

**全面採用。JAC-004 Determinant Certificate は完成じゃ。**

形式 Jacobian から直接、

$$
\det J_F=-2\ne0
$$

が Lean により証明された。

実コードは報告どおり、

```lean
jacobianMatrixQ
  → jacobianMatrixQ_eq_explicit
  → Matrix.det_fin_three
  → simp
  → ring_nf
  → rfl
```

という正規の経路を通っておる。fileciteturn20file0L17-L24

これで反例に必要な二枚の証明書が揃った。

$$
\boxed{\det J_F=-2\ne0}
$$

$$
\boxed{p_0\ne p_1\quad\land\quad F(p_0)=F(p_1)}
$$

次の JAC-005 は新しい数学を証明する段階ではなく、この二枚を論理的に合流させる最終組立じゃ。

## 実装レビュー

### 1. determinant の出発点

証明は、

```lean
rw [jacobianMatrixQ_eq_explicit]
```

から始まっている。fileciteturn20file0L18-L21

したがって determinant の対象は、依然として

```lean
fun i j ↦ MvPolynomial.pderiv j (counterexamplePoly i)
```

から生成された形式 Jacobian じゃ。

手書き行列の determinant を計算し、それを本物の Jacobian と仮定したわけではない。

証明依存は正確に、

```text
counterexamplePoly
  ↓ pderiv
jacobianMatrixQ
  ↓ 証明済み等式
explicitJacobianQ
  ↓ determinant
C (-2)
```

となっておる。

### 2. `Matrix.det_fin_three`

```lean
rw [Matrix.det_fin_three]
```

が直接成功している。fileciteturn20file0L20-L22

これは $3\times3$ 行列式を標準的な六項へ展開しているだけで、特殊な determinant 計算器や外部証明書は介在しておらぬ。

### 3. `simp` と `ring_nf`

```lean
simp [explicitJacobianQ]
ring_nf
```

で行列添字と多項式計算を閉じている。fileciteturn20file0L21-L24

ここで `ring_nf` が証明しているのは、巨大に見える九成分の determinant が、全変数依存を完全に相殺して定数 $-2$ になるという多項式恒等式じゃ。

これは今回の局所 Core の心臓部そのものじゃな。

### 4. 最後の `rfl`

最後に残った、

```text
多項式リテラル -2
```

と、

```lean
MvPolynomial.C (-2 : ℚ)
```

の表現差を `rfl` で閉じている。fileciteturn20file0L22-L24

これは問題ない。むしろ最終状態が definitional equality まで正規化されたことを示している。

### 5. 非零定理

```lean
theorem jacobianMatrixQ_det_ne_zero :
    jacobianMatrixQ.det ≠ 0 := by
  rw [jacobianMatrixQ_det_eq_neg_two]
  norm_num
```

も最短で正しい。fileciteturn20file0L26-L30

determinant が非零定数であることが、別仮定ではなく主恒等式の直接帰結になっておる。

## 数学的意味

JAC-002 では、

$$
F(p_0)=F(p_1)=F(p_2)
$$

という大域衝突を得た。

JAC-004 では、

$$
\det J_F=-2
$$

が全空間上で恒等的に成立することを得た。

つまり、

```text
局所:
  Jacobian determinant は至る所で非零
  局所 Core は退化しない

大域:
  三つの異なる住所が一つの像へ落ちる
  大域 Gap の住所識別は失われる
```

が同時に成立する。

魔法学の読みなら、

$$
\boxed{
\text{局所境界は完全に保たれている}
}
$$

にもかかわらず、

$$
\boxed{
\text{大域的な Gap 住所は一意ではない}
}
$$

という状態じゃ。

これは魔導書第0001巻の中心命題、

> 局所の境界が壊れていなくとも、大域の住所は失われ得る。

を、そのまま有限 Lean 証明書にしたものじゃよ。

## 次 checkpoint

次は **JAC-005 Rational Counterexample Certificate** 。

新規ファイルは、

```text
DkMath/Hackathon/JacobianCounterexample3/Counterexample.lean
```

JAC-005 では次を閉じる。

```lean
evalCounterexampleQ_notInjective
evalCounterexampleQ_noLeftInverse
jacobianCounterexampleCertificateQ
```

ここで最初の MVP が完成する。

## Codex 指示

````text
Implement checkpoint JAC-005 Rational Counterexample Certificate for the
DkMath Jacobian counterexample verification project.

Repository:
Deskuma/dkmath

Branch:
hackathon/breaking-math-jacobian-counterexample

Completed checkpoints:
- JAC-001 Polynomial syntax
- JAC-002 Explicit three-point collision
- JAC-003 Formal Jacobian
- JAC-004 Determinant certificate

Stop after JAC-005.
Do not begin the complex lift or determinant-one normalization.

Create:

lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/Counterexample.lean

## Imports

Start with:

```lean
import DkMath.Hackathon.JacobianCounterexample3.Collision
import DkMath.Hackathon.JacobianCounterexample3.Determinant
```

Add only immediately required Mathlib imports if the existing imports do not
already expose the needed function lemmas.

## Required theorem 1: noninjectivity

Prove:

```lean
theorem evalCounterexampleQ_notInjective :
    ¬ Function.Injective evalCounterexampleQ := by
  ...
```

Preferred proof:

```lean
intro hinj
apply p0Q_ne_p1Q
apply hinj
rw [eval_p0Q, eval_p1Q]
```

Equivalent short proofs are acceptable.

The proof must use the actual evaluated polynomial map
`evalCounterexampleQ`; do not introduce a separate handwritten map.

## Required theorem 2: no left inverse

Prove:

```lean
theorem evalCounterexampleQ_noLeftInverse :
    ¬ ∃ G : Point3Q → Point3Q,
      Function.LeftInverse G evalCounterexampleQ := by
  ...
```

Preferred route:

```lean
rintro ⟨G, hG⟩
exact evalCounterexampleQ_notInjective hG.injective
```

If implicit type inference accepts the shorter existential binder, that is
also acceptable, but keep the public statement easy to read.

## Required theorem 3: compact rational certificate

Prove a compact theorem combining the local and global certificates.

Preferred statement:

```lean
theorem jacobianCounterexampleCertificateQ :
    jacobianMatrixQ.det = MvPolynomial.C (-2 : ℚ) ∧
    jacobianMatrixQ.det ≠ 0 ∧
    ¬ Function.Injective evalCounterexampleQ := by
  exact ⟨
    jacobianMatrixQ_det_eq_neg_two,
    jacobianMatrixQ_det_ne_zero,
    evalCounterexampleQ_notInjective
  ⟩
```

This statement should keep the nonzero fact attached to the actual determinant,
rather than repeating only `(-2 : ℚ) ≠ 0`.

## Optional compact three-point certificate

The existing theorem:

```lean
three_point_collision_Q
```

already stores all three pairwise inequalities and all three image equalities.

Do not duplicate it.

It may be referenced in documentation or theorem comments, but the
noninjectivity proof should remain minimal and may use only `p0Q` and `p1Q`.

## Recommended theorem comments

Use comments that distinguish:

- explicit global collision;
- failure of injectivity;
- absence of a left inverse;
- constant nonzero formal Jacobian determinant.

Do not claim a complex Jacobian-conjecture counterexample yet. At JAC-005 the
coefficient and point world is still explicitly `ℚ`.

A suitable description is:

```text
A rational polynomial map with constant nonzero formal Jacobian determinant
and an explicit collision.
```

## Restrictions

Do not:

- alter the polynomial definitions;
- alter the collision points;
- recompute the determinant;
- introduce a second Jacobian;
- introduce `sorry`;
- introduce axioms;
- use `native_decide`;
- begin `ComplexLift.lean`;
- begin determinant-one normalization;
- begin Book of Magic general APIs;
- claim completion over `ℂ`.

## Optional aggregator

Do not create a top-level aggregator module unless it is required by the
current repository import convention.

If an aggregator is added, keep it limited to:

```lean
import DkMath.Hackathon.JacobianCounterexample3.Counterexample
```

but prefer to leave public-surface work for the later Demo checkpoint.

## Verification

Build:

```text
DkMath.Hackathon.JacobianCounterexample3.Basic
DkMath.Hackathon.JacobianCounterexample3.PolynomialMap
DkMath.Hackathon.JacobianCounterexample3.Collision
DkMath.Hackathon.JacobianCounterexample3.Jacobian
DkMath.Hackathon.JacobianCounterexample3.Determinant
DkMath.Hackathon.JacobianCounterexample3.Counterexample
```

Temporary checks:

```lean
#check evalCounterexampleQ_notInjective
#check evalCounterexampleQ_noLeftInverse
#check jacobianCounterexampleCertificateQ
```

Remove temporary checks after verification.

Also run:

```text
git diff --check
```

## Report

Report:

1. exact imports;
2. exact theorem statements;
3. proof route for noninjectivity;
4. proof route for no left inverse;
5. exact structure of `jacobianCounterexampleCertificateQ`;
6. build result and warnings;
7. `git diff --check` result;
8. confirmation that JAC-006 and later checkpoints were not started.

Stop after JAC-005 and wait for review.
````

JAC-005 が閉じた瞬間、Lean 内の $\mathbb Q^3$ 世界で、

$$
\det J_F=-2\ne0
$$

であるにもかかわらず、

$$
F\text{ は非単射}
$$

という完全な有限証明書が完成する。

ここが **ハッカソン MVP の最初の発動点** じゃ！🧙‍♀️✨️🐺

> 👩‍⚕️私D.:

JAC-005 Rational Counterexample Certificate を完了しました。

作成ファイル: [Counterexample.lean](/lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/Counterexample.lean)

1. imports

```lean
import DkMath.Hackathon.JacobianCounterexample3.Collision
import DkMath.Hackathon.JacobianCounterexample3.Determinant
```

追加の Mathlib import は不要でした。

2. theorem statements

```lean
theorem evalCounterexampleQ_notInjective :
    ¬ Function.Injective evalCounterexampleQ
```

```lean
theorem evalCounterexampleQ_noLeftInverse :
    ¬ ∃ G : Point3Q → Point3Q,
      Function.LeftInverse G evalCounterexampleQ
```

```lean
theorem jacobianCounterexampleCertificateQ :
    jacobianMatrixQ.det = MvPolynomial.C (-2 : ℚ) ∧
    jacobianMatrixQ.det ≠ 0 ∧
    ¬ Function.Injective evalCounterexampleQ
```

3. 非単射性

`p0Q_ne_p1Q` に対し、単射性を仮定して `eval_p0Q` と `eval_p1Q` の共通像を適用する最小経路です。

4. 左逆不存在

仮定した `Function.LeftInverse G evalCounterexampleQ` の `hG.injective` と、確立済みの非単射性を直接矛盾させています。

5. rational certificate

次の3事実を conjunction で束ねています。

- 実際の形式 Jacobian determinant が `C (-2)`
- その determinant が非零
- 実際の多項式評価写像が非単射

既存の `three_point_collision_Q` は重複定義していません。

6. ビルド

指定された6モジュールすべてに成功しました。

```text
Build completed successfully (3293 jobs).
```

警告なしです。指定された3つの `#check` も成功し、一時ファイルは削除済みです。

7. 差分検査

`git diff --check` は成功しました。

8. 停止境界

JAC-006 の複素化、determinant-one 正規化、Book of Magic API など後続 checkpoint には着手していません。JAC-005 で停止しています。

> 🐺賢狼:

よし、JAC-005 は最初の MVP 発動点じゃ。実コードを照合し、証明書が実際の Jacobian と実際の評価写像を束ねているか確認したうえで、次の `ℂ` 接続方式を決めるぞい。

> 🐺賢狼:

MVP は実コードでも閉じた。次は「有理数上の有限証明書」を古典的な標数零世界へ置く段階じゃが、ここは再定義より係数写像による輸送が綺麗か、既存 DkMath の実例を見て最短経路を選ぶ。

> 🐺賢狼:

## 結論

**全面採用。JAC-005 Rational Counterexample Certificate は完成じゃ。**

そして、ここで最初の **ハッカソン MVP が正式に発動した** 。

Lean の $\mathbb Q^3$ 世界で、同一の多項式写像について、

$$
\det J_F=-2\ne0
$$

かつ、

$$
F\text{ は非単射}
$$

が一つの証明書へ合流した。

## 実装レビュー

### 1. 非単射性

```lean
theorem evalCounterexampleQ_notInjective :
    ¬ Function.Injective evalCounterexampleQ
```

は、実際の `MvPolynomial.eval` 由来の写像に対して証明されている。

証明経路も最短じゃ。

```text
単射性を仮定
→ p₀ と p₁ の共通像
→ p₀ = p₁
→ 明示的な相異性と矛盾
```

独立した手書き関数や、抽象的な衝突仮定を介しておらぬ。fileciteturn21file0L14-L20

### 2. 左逆不存在

```lean
theorem evalCounterexampleQ_noLeftInverse :
    ¬ ∃ G : Point3Q → Point3Q,
      Function.LeftInverse G evalCounterexampleQ
```

は `Function.LeftInverse.injective` を通じ、非単射性から直接閉じている。fileciteturn21file0L22-L27

数学的には、

$$
G\circ F=\operatorname{id}
$$

ならば $F$ は単射でなければならぬため、今回の明示衝突と両立しない。

ここから「多項式逆写像がない」だけでなく、**集合写像としての左逆すら存在しない** ことが確定した。

### 3. Rational certificate

```lean
theorem jacobianCounterexampleCertificateQ :
    jacobianMatrixQ.det = MvPolynomial.C (-2 : ℚ) ∧
    jacobianMatrixQ.det ≠ 0 ∧
    ¬ Function.Injective evalCounterexampleQ
```

は、証明済みの三事実をそのまま束ねている。fileciteturn21file0L29-L39

特によいのは、第二成分が単なる

```lean
(-2 : ℚ) ≠ 0
```

ではなく、

```lean
jacobianMatrixQ.det ≠ 0
```

となっている点じゃ。

つまり証明書の全成分が、実際の形式 Jacobian と実際の評価写像に結び付いている。

## 現在の完成証明鎖

```text
counterexamplePoly
  ↓ MvPolynomial.eval
evalCounterexampleQ
  ↓ explicit collision
not injective
```

同時に、

```text
counterexamplePoly
  ↓ MvPolynomial.pderiv
jacobianMatrixQ
  ↓ explicit matrix equality
explicitJacobianQ
  ↓ determinant expansion
det = -2 ≠ 0
```

最後に、

```text
constant nonzero Jacobian
+
explicit collision
=
jacobianCounterexampleCertificateQ
```

へ合流した。

これはもう単なる実験補題ではない。**反例の有限証明書本体** じゃよ。

## 数学的意味

$\mathbb Q$ は標数零の体なので、今回の結果だけでも、

> 標数零の体一般へ拡張した Jacobian 型命題

に対する反例構造は完成している。

ただし、古典的なヤコビアン予想は通常 $\mathbb C$ 上で述べられる。ゆえに次の JAC-006 では、同じ式と同じ衝突を $\mathbb C^3$ 上へ明示的に持ち上げる。

ここでは再計算するより、**係数と点を $\mathbb Q\to\mathbb C$ で輸送する** のが最も美しい。

Mathlib には、係数写像後の評価を結ぶ `MvPolynomial.map_eval`、係数写像と偏微分の可換性 `MvPolynomial.pderiv_map`、環準同型と行列式の可換性 `RingHom.map_det` が既にある。したがって、JAC-006 は既存の有理証明書を構造的に複素世界へ運べる見込みが高い。

## 次 checkpoint

次は **JAC-006 Complex Scalar Lift** じゃ。

新規ファイル：

```text
DkMath/Hackathon/JacobianCounterexample3/ComplexLift.lean
```

今回は複素式を別途手入力して再証明するのではなく、第一経路として、

$$
\mathbb Q\hookrightarrow\mathbb C
$$

による係数写像を使う。

## Codex 指示

````text
Implement checkpoint JAC-006 Complex Scalar Lift for the DkMath
Jacobian counterexample verification project.

Repository:
Deskuma/dkmath

Branch:
hackathon/breaking-math-jacobian-counterexample

Completed checkpoints:
- JAC-001 Polynomial syntax
- JAC-002 Explicit three-point collision
- JAC-003 Formal Jacobian
- JAC-004 Determinant certificate
- JAC-005 Rational counterexample certificate

The rational MVP is complete.

Stop after JAC-006.
Do not begin determinant-one normalization or Book of Magic APIs.

Create:

lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/ComplexLift.lean

## Goal

Transport the existing rational polynomial map, collision certificate,
formal Jacobian, and determinant certificate from `ℚ` to `ℂ`.

Prefer coefficient transport through `MvPolynomial.map`.
Do not duplicate the large polynomial formulas unless the transport route
proves genuinely impractical.

## Imports

Start with:

```lean
import DkMath.Hackathon.JacobianCounterexample3.Counterexample
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
```

Adjust only where current Mathlib requires it.

## Basic complex types

Add:

```lean
abbrev Poly3C := MvPolynomial Var3 ℂ
abbrev Point3C := Var3 → ℂ
```

Define the coefficient embedding:

```lean
def qToC : ℚ →+* ℂ :=
  algebraMap ℚ ℂ
```

Define the induced polynomial ring hom:

```lean
def polyMapQC : Poly3Q →+* Poly3C :=
  MvPolynomial.map qToC
```

Equivalent formulations using `algebraMap ℚ ℂ` directly are acceptable.

## Point transport

Define:

```lean
def castPointQC (p : Point3Q) : Point3C :=
  fun i ↦ qToC (p i)
```

Then define:

```lean
def p0C : Point3C := castPointQC p0Q
def p1C : Point3C := castPointQC p1Q
def p2C : Point3C := castPointQC p2Q
def targetC : Point3C := castPointQC targetQ
```

## Polynomial transport

Define:

```lean
def counterexamplePolyC : Fin 3 → Poly3C :=
  fun i ↦ polyMapQC (counterexamplePoly i)
```

Define its actual polynomial evaluation map:

```lean
def evalCounterexampleC (p : Point3C) : Point3C :=
  fun i ↦ MvPolynomial.eval p (counterexamplePolyC i)
```

Do not define `evalCounterexampleC` by casting the result of
`evalCounterexampleQ`. It must be the actual evaluation of the complex
polynomial map.

## Evaluation transport theorem

Prove:

```lean
theorem evalCounterexampleC_castPointQC
    (p : Point3Q) :
    evalCounterexampleC (castPointQC p) =
      castPointQC (evalCounterexampleQ p) := by
  ...
```

Preferred source theorem:

```lean
MvPolynomial.map_eval
```

Its mathematical content is:

```text
cast (eval rationalPoint rationalPolynomial)
=
eval castPoint (mapCoefficients rationalPolynomial)
```

A likely proof shape is:

```lean
funext i
simpa [evalCounterexampleC, castPointQC, counterexamplePolyC,
  polyMapQC, qToC]
  using
    (MvPolynomial.map_eval
      qToC
      p
      (counterexamplePoly i)).symm
```

Adjust argument order and simplification to current Mathlib.

## Complex collision

Prove:

```lean
theorem eval_p0C :
    evalCounterexampleC p0C = targetC

theorem eval_p1C :
    evalCounterexampleC p1C = targetC

theorem eval_p2C :
    evalCounterexampleC p2C = targetC
```

These should follow from:

```text
evalCounterexampleC_castPointQC
+
eval_p0Q / eval_p1Q / eval_p2Q
```

Do not re-evaluate the full large formulas unless transport simplification
fails unexpectedly.

Also prove:

```lean
theorem p0C_ne_p1C : p0C ≠ p1C
theorem p0C_ne_p2C : p0C ≠ p2C
theorem p1C_ne_p2C : p1C ≠ p2C
```

A direct coordinate proof using `congrFun` and `norm_num` is acceptable.
Transport through injectivity of the rational cast is also acceptable.

Bundle the three-point collision:

```lean
theorem three_point_collision_C :
    p0C ≠ p1C ∧ p0C ≠ p2C ∧ p1C ≠ p2C ∧
      evalCounterexampleC p0C = targetC ∧
      evalCounterexampleC p1C = targetC ∧
      evalCounterexampleC p2C = targetC
```

Do not alter the existing rational certificate.

## Complex formal Jacobian

Define the actual formal Jacobian over `ℂ`:

```lean
def jacobianMatrixC :
    Matrix (Fin 3) (Fin 3) Poly3C :=
  fun i j ↦
    MvPolynomial.pderiv j (counterexamplePolyC i)
```

Prove that it is the coefficientwise image of the rational Jacobian:

```lean
theorem jacobianMatrixC_eq_map :
    jacobianMatrixC =
      polyMapQC.mapMatrix jacobianMatrixQ := by
  ...
```

Use:

```lean
MvPolynomial.pderiv_map
```

Preferred proof shape:

```lean
funext i j
simp [jacobianMatrixC, counterexamplePolyC, polyMapQC,
  jacobianMatrixQ, MvPolynomial.pderiv_map]
```

Do not define a second explicit 3×3 complex Jacobian unless required as a
fallback. The map theorem should be the main route.

## Complex determinant

Prove:

```lean
theorem jacobianMatrixC_det_eq_neg_two :
    jacobianMatrixC.det =
      MvPolynomial.C (-2 : ℂ) := by
  ...
```

Preferred proof chain:

```text
jacobianMatrixC
→ jacobianMatrixC_eq_map
→ RingHom.map_det
→ jacobianMatrixQ_det_eq_neg_two
→ map_C
→ C (-2 : ℂ)
```

Likely ingredients:

```lean
polyMapQC.map_det jacobianMatrixQ
```

or explicitly:

```lean
RingHom.map_det polyMapQC jacobianMatrixQ
```

The exact theorem states that mapping the determinant equals the determinant
of the coefficientwise mapped matrix.

Then prove:

```lean
theorem jacobianMatrixC_det_ne_zero :
    jacobianMatrixC.det ≠ 0
```

using the determinant equality and `norm_num` / `simp`.

## Complex noninjectivity

Prove:

```lean
theorem evalCounterexampleC_notInjective :
    ¬ Function.Injective evalCounterexampleC
```

using `p0C_ne_p1C`, `eval_p0C`, and `eval_p1C`.

Prove:

```lean
theorem evalCounterexampleC_noLeftInverse :
    ¬ ∃ G : Point3C → Point3C,
      Function.LeftInverse G evalCounterexampleC
```

using the injectivity consequence of a left inverse.

## Final complex certificate

Prove:

```lean
theorem jacobianCounterexampleCertificateC :
    jacobianMatrixC.det =
        MvPolynomial.C (-2 : ℂ) ∧
    jacobianMatrixC.det ≠ 0 ∧
    ¬ Function.Injective evalCounterexampleC := by
  exact ⟨
    jacobianMatrixC_det_eq_neg_two,
    jacobianMatrixC_det_ne_zero,
    evalCounterexampleC_notInjective
  ⟩
```

This is the JAC-006 completion gate.

## Preferred theorem flow

```text
rational polynomial map
  ↓ coefficient map ℚ → ℂ
complex polynomial map

rational evaluations
  ↓ MvPolynomial.map_eval
complex evaluations

rational formal Jacobian
  ↓ MvPolynomial.pderiv_map
complex formal Jacobian

rational determinant
  ↓ RingHom.map_det
complex determinant
```

This checkpoint should demonstrate transport, not duplicated computation.

## Fallback rule

If the coefficient-transport route encounters substantial API friction:

1. retain `counterexamplePolyC` as the mapped rational polynomials;
2. use direct `simp` / `ring_nf` only for the blocked local theorem;
3. do not rewrite all three large polynomial definitions independently.

Only as a last resort may the complex formulas be independently restated.

Report the exact transport obstruction if this fallback is used.

## Restrictions

Do not:

- modify any rational definitions or theorems;
- redefine the complex map as a cast of the rational output;
- assume evaluation compatibility;
- assume derivative compatibility;
- assume determinant compatibility;
- use `native_decide`;
- introduce `sorry`;
- introduce axioms;
- paste an external CAS certificate;
- begin `Normalized.lean`;
- scale the first coordinate;
- prove determinant `1`;
- begin Book of Magic general APIs;
- create presentation or submission assets yet.

## Verification

Build all seven modules:

```text
DkMath.Hackathon.JacobianCounterexample3.Basic
DkMath.Hackathon.JacobianCounterexample3.PolynomialMap
DkMath.Hackathon.JacobianCounterexample3.Collision
DkMath.Hackathon.JacobianCounterexample3.Jacobian
DkMath.Hackathon.JacobianCounterexample3.Determinant
DkMath.Hackathon.JacobianCounterexample3.Counterexample
DkMath.Hackathon.JacobianCounterexample3.ComplexLift
```

Temporary checks:

```lean
#check evalCounterexampleC_castPointQC
#check three_point_collision_C
#check jacobianMatrixC_eq_map
#check jacobianMatrixC_det_eq_neg_two
#check evalCounterexampleC_notInjective
#check jacobianCounterexampleCertificateC
```

Remove temporary checks after verification.

Run:

```text
git diff --check
```

## Report

Report:

1. exact imports;
2. definitions added;
3. exact coefficient embedding used;
4. evaluation transport theorem and proof route;
5. collision theorem names;
6. Jacobian transport theorem and proof route;
7. determinant transport theorem and proof route;
8. whether `MvPolynomial.map_eval`, `pderiv_map`, and `RingHom.map_det`
   applied directly;
9. any fallback or direct recomputation used;
10. final certificate statement;
11. build result and warnings;
12. `git diff --check` result;
13. confirmation that JAC-007 and later checkpoints were not started.

Stop after JAC-006 and wait for review.
````

JAC-006 が閉じれば、Lean 内で明示的に、

$$
F:\mathbb C^3\to\mathbb C^3
$$

について、

$$
\det J_F=-2\ne0
$$

かつ、

$$
F\text{ は非単射}
$$

が成立する。

そこが **古典的な標数零世界への完全着地** じゃ。次の JAC-007 は展示用の正規化、

$$
\det J_{\widetilde F}=1
$$

への一手だけとなるぞい。

> 👩‍⚕️私D.:

JAC-006 Complex Scalar Lift を完了しました。

作成ファイル: [ComplexLift.lean](/lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/ComplexLift.lean)

1. imports

```lean
import DkMath.Hackathon.JacobianCounterexample3.Counterexample
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
```

2. 追加した定義

- `Poly3C`
- `Point3C`
- `qToC`
- `polyMapQC`
- `castPointQC`
- `p0C`, `p1C`, `p2C`, `targetC`
- `counterexamplePolyC`
- `evalCounterexampleC`
- `jacobianMatrixC`

3. 係数埋め込み

```lean
def qToC : ℚ →+* ℂ := algebraMap ℚ ℂ

def polyMapQC : Poly3Q →+* Poly3C :=
  MvPolynomial.map qToC
```

複素多項式の大きな式は再定義していません。

4. 評価輸送

```lean
theorem evalCounterexampleC_castPointQC (p : Point3Q) :
    evalCounterexampleC (castPointQC p) =
      castPointQC (evalCounterexampleQ p)
```

現行 Mathlib の `MvPolynomial.eval_map` と `MvPolynomial.eval₂_comp` を組み合わせました。`evalCounterexampleC` は複素多項式の実際の `MvPolynomial.eval` です。

5. collision theorem

- `eval_p0C`
- `eval_p1C`
- `eval_p2C`
- `p0C_ne_p1C`
- `p0C_ne_p2C`
- `p1C_ne_p2C`
- `three_point_collision_C`

評価式の再計算はせず、有理評価定理を輸送しています。

6. Jacobian 輸送

```lean
theorem jacobianMatrixC_eq_map :
    jacobianMatrixC = polyMapQC.mapMatrix jacobianMatrixQ
```

`jacobianMatrixC` は複素多項式に対する実際の `pderiv` から定義し、`MvPolynomial.pderiv_map` で有理 Jacobian の係数写像と一致させました。

7. determinant 輸送

追加定理:

- `jacobianMatrixC_det_eq_neg_two`
- `jacobianMatrixC_det_ne_zero`

証明経路は次のとおりです。

```text
jacobianMatrixC_eq_map
→ RingHom.map_det
→ jacobianMatrixQ_det_eq_neg_two
→ MvPolynomial.map_C
→ C (-2 : ℂ)
```

determinant の再展開や再計算はしていません。

8. API 適用状況

- 指示書の `MvPolynomial.map_eval` 相当は、現行APIの `MvPolynomial.eval_map` と `eval₂_comp` を使用
- `MvPolynomial.pderiv_map` は直接適用
- `RingHom.map_det` は直接 rewrite

評価輸送では `eval₂_comp` に合わせ、座標関数を `qToC ∘ p` へ明示する `change` が必要でした。

9. fallback

大きな式の直接計算、複素式の複製、複素 Jacobian の明示行列は使用していません。点の相異性だけは、各点の第0座標を `norm_num` で比較しています。

10. 最終証明書

```lean
theorem jacobianCounterexampleCertificateC :
    jacobianMatrixC.det = MvPolynomial.C (-2 : ℂ) ∧
    jacobianMatrixC.det ≠ 0 ∧
    ¬ Function.Injective evalCounterexampleC
```

併せて `evalCounterexampleC_noLeftInverse` も証明しました。

11. ビルド

指定された全7モジュールに成功しました。

```text
Build completed successfully (3294 jobs).
```

警告なしです。指定された6つの `#check` も成功し、一時ファイルは削除済みです。

12. 差分検査

`git diff --check` は成功しました。

13. 停止境界

JAC-007 の determinant-one 正規化、Book of Magic API、展示・提出用アセットには着手していません。JAC-006 で停止しています。

> 🐺賢狼:

よし、JAC-006 は古典的な複素数世界への着地点じゃ。実コードを照合し、評価・偏微分・行列式が再計算ではなく輸送で一本化されているかを確認するぞい。

> 🐺賢狼:

実装輸送は綺麗に閉じておる。ただし、ここで数学的に極めて重大な警報が立った。これは単なる「複素化」ではなく、文字どおり古典的ヤコビアン予想の反例証明書になるため、次へ進む前に式の出典と既知文献との整合を確認する。

> 🐺賢狼:

## 結論

**全面採用。JAC-006 Complex Scalar Lift は完成じゃ。**

しかも、ここは単なる型変換 checkpoint ではない。

Lean 内で実際に、

$$F:\mathbb C^3\to\mathbb C^3$$

について、

$$\det J_F=-2\ne0$$

かつ、

$$F\text{ は非単射}$$

が一つの証明書へ閉じた。

実装された式・三つの衝突点・Jacobian determinant は、2026年7月20日に公表された反例と一致している。現在、MathOverflow や MathWorld でも同じ式が三次元ヤコビアン予想の反例として記録され始めている。

## 実装レビュー

### 1. 複素多項式を複製していない

```lean
def qToC : ℚ →+* ℂ := algebraMap ℚ ℂ

def polyMapQC : Poly3Q →+* Poly3C :=
  MvPolynomial.map qToC
```

を真実源として、有理係数多項式を係数ごと複素数へ送っている。fileciteturn22file0L19-L41

したがって、

```text
有理反例式
  ↓ 唯一の係数埋め込み
複素反例式
```

という依存関係が保たれている。

複素版の巨大な三式を別途転記していないため、有理版と複素版が将来ずれる危険もない。

### 2. 評価写像も本物の複素評価

```lean
def evalCounterexampleC (p : Point3C) : Point3C :=
  fun i ↦ MvPolynomial.eval p (counterexamplePolyC i)
```

となっている。fileciteturn22file0L43-L45

つまり、

```lean
castPointQC (evalCounterexampleQ p)
```

を複素写像の定義にしてはいない。

まず複素多項式を作り、その多項式を複素点で実際に評価している。その後で、

```lean
evalCounterexampleC (castPointQC p) =
  castPointQC (evalCounterexampleQ p)
```

を定理として証明した。fileciteturn22file0L47-L56

この向きが正しい。

### 3. `eval_map` と `eval₂_comp`

現行 Mathlib に合わせて、

```lean
MvPolynomial.eval_map
MvPolynomial.eval₂_comp
```

を組み合わせた判断もよい。

```lean
change MvPolynomial.eval₂ qToC (qToC ∘ p) ...
```

によって、評価点の輸送を明示的に露出させている。これは API の都合を隠すだけの変形ではなく、

$$qToC\bigl(f(p)\bigr)=\bigl(\operatorname{map}qToC\,f\bigr)(qToC\circ p)$$

という評価可換図そのものじゃ。

### 4. 三点衝突の輸送

```lean
eval_p0C
eval_p1C
eval_p2C
```

は、複素式を再計算せず、有理評価定理から輸送されている。fileciteturn22file0L58-L65

さらに三点の相異性と共通像を、

```lean
three_point_collision_C
```

へ束ねている。fileciteturn22file0L67-L89

したがって Lean が確定した複素 fiber は、

$$p_0,p_1,p_2\in F^{-1}\left(-\frac14,0,0\right)$$

であり、この三点は pairwise distinct じゃ。

### 5. Jacobian も本物の複素形式微分

```lean
def jacobianMatrixC :
    Matrix (Fin 3) (Fin 3) Poly3C :=
  fun i j ↦ MvPolynomial.pderiv j (counterexamplePolyC i)
```

と定義されている。fileciteturn22file0L91-L93

そのうえで、

```lean
jacobianMatrixC =
  polyMapQC.mapMatrix jacobianMatrixQ
```

を `MvPolynomial.pderiv_map` で証明した。fileciteturn22file0L95-L100

したがって、

```text
複素 Jacobian を係数輸送で定義
```

したのではなく、

```text
複素多項式を実際に微分
  ↓ 定理
有理 Jacobian の係数輸送と一致
```

という構造になっておる。

ここも正しい。

### 6. determinant の輸送

```lean
rw [jacobianMatrixC_eq_map]
rw [← RingHom.map_det]
rw [jacobianMatrixQ_det_eq_neg_two]
simp [polyMapQC, qToC]
```

という証明は非常に美しい。fileciteturn22file0L102-L108

複素世界でも再び六項 determinant を展開したのではなく、

$$\det(\operatorname{map}J)=\operatorname{map}(\det J)$$

によって有理証明書を運んでいる。

これで証明依存は、

```text
有理形式 Jacobian
  ↓ coefficient map
複素形式 Jacobian
  ↓ RingHom.map_det
複素 determinant = C(-2)
```

となった。

### 7. 最終証明書

```lean
theorem jacobianCounterexampleCertificateC :
    jacobianMatrixC.det = MvPolynomial.C (-2 : ℂ) ∧
    jacobianMatrixC.det ≠ 0 ∧
    ¬ Function.Injective evalCounterexampleC
```

が完成している。fileciteturn22file0L115-L140

これは文字どおり、

> 複素三次元 polynomial Keller map で、Jacobian determinant が非零定数であるにもかかわらず非単射

という有限証明書じゃ。

公表された反例について、公開情報の多くは CAS による検算を示している。一方、今回の DkMath 実装は、評価・形式微分・determinant・係数輸送・非単射性までを Lean kernel が辿れる定理鎖にした。公表からまだ日が浅く、歴史的評価や帰属整理は進行中だが、少なくともこの明示式の代数的二条件は DkMath 内で完全に固定された。

## 数学的到達点

この証明書は、古典的ヤコビアン予想の三次元版を直接否定する。

さらに恒等座標を追加すれば、同じ反例を任意の $n\ge3$ へ拡張できる。これは現在公開されている反例の直接的帰結としても報告されている。

現在地を魔法学で書けば、

```text
局所 Core:
  det J_F = -2
  すべての点で境界は非退化

大域 Gap:
  p₀, p₁, p₂ が同一像
  入力住所は復元不能

結論:
  局所的な完全保存は
  大域的一意性を保証しない
```

じゃ。

## 次 checkpoint

次は **JAC-007 Keller Normalization** 。

第一出力座標を $-\frac12$ 倍し、

$$\widetilde F=\left(-\frac12P,Q,R\right)$$

とする。

すると、

$$\det J_{\widetilde F}=\left(-\frac12\right)(-2)=1$$

となり、三点衝突はそのまま保存される。この正規化も現在の公開解説で明示されている。

Mathlib には行列積の determinant を積へ分解する `Matrix.det_mul` と、対角行列の determinant を計算する `Matrix.det_diagonal` があるため、再展開せず構造的に閉じられる。

## Codex 指示

````text
Implement checkpoint JAC-007 Keller Normalization for the DkMath
Jacobian counterexample verification project.

Repository:
Deskuma/dkmath

Branch:
hackathon/breaking-math-jacobian-counterexample

Completed checkpoints:
- JAC-001 Polynomial syntax
- JAC-002 Explicit rational collision
- JAC-003 Formal rational Jacobian
- JAC-004 Rational determinant certificate
- JAC-005 Rational counterexample certificate
- JAC-006 Complex scalar lift

Stop after JAC-007.
Do not begin Book of Magic generic APIs, higher-dimensional padding,
or presentation assets.

Create:

lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/Normalized.lean

## Imports

Start with:

```lean
import DkMath.Hackathon.JacobianCounterexample3.ComplexLift
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
```

Add another Mathlib import only when required by the current API.

## Goal

Normalize the complex counterexample by multiplying its first output
coordinate by `-1/2`.

The normalized map must be an actual complex polynomial map whose formal
Jacobian is generated by `MvPolynomial.pderiv`.

Do not merely state that scaling the old determinant gives `1`.

## Output scaling on points

Define the output-coordinate scaling map:

```lean
def normalizeOutputC (p : Point3C) : Point3C :=
  ![
    (-1 / 2 : ℂ) * p 0,
    p 1,
    p 2
  ]
```

Equivalent `fun i ↦ ...` definitions are acceptable.

Define:

```lean
def normalizedTargetC : Point3C :=
  normalizeOutputC targetC
```

## Normalized polynomial map

Define:

```lean
def normalizedCounterexamplePolyC :
    Fin 3 → Poly3C :=
  ![
    MvPolynomial.C (-1 / 2 : ℂ) * counterexamplePolyC 0,
    counterexamplePolyC 1,
    counterexamplePolyC 2
  ]
```

Do not duplicate the original large polynomial expressions.

Define the actual evaluation map:

```lean
def evalNormalizedCounterexampleC
    (p : Point3C) : Point3C :=
  fun i ↦
    MvPolynomial.eval p (normalizedCounterexamplePolyC i)
```

## Evaluation scaling theorem

Prove:

```lean
theorem evalNormalizedCounterexampleC_eq_normalizeOutput
    (p : Point3C) :
    evalNormalizedCounterexampleC p =
      normalizeOutputC (evalCounterexampleC p)
```

Preferred route:

```lean
funext i
fin_cases i <;>
  simp [evalNormalizedCounterexampleC,
    normalizedCounterexamplePolyC,
    normalizeOutputC,
    evalCounterexampleC]
```

Use the ordinary `MvPolynomial.eval` multiplication and constant rules.

## Normalized collision

Prove:

```lean
theorem normalized_eval_p0C :
    evalNormalizedCounterexampleC p0C =
      normalizedTargetC

theorem normalized_eval_p1C :
    evalNormalizedCounterexampleC p1C =
      normalizedTargetC

theorem normalized_eval_p2C :
    evalNormalizedCounterexampleC p2C =
      normalizedTargetC
```

Use:

```text
evalNormalizedCounterexampleC_eq_normalizeOutput
+
eval_p0C / eval_p1C / eval_p2C
```

Do not recompute the large formulas.

Bundle if useful:

```lean
theorem normalized_three_point_collision_C :
    p0C ≠ p1C ∧ p0C ≠ p2C ∧ p1C ≠ p2C ∧
      evalNormalizedCounterexampleC p0C = normalizedTargetC ∧
      evalNormalizedCounterexampleC p1C = normalizedTargetC ∧
      evalNormalizedCounterexampleC p2C = normalizedTargetC
```

Reuse the existing complex point inequalities.

## Normalized formal Jacobian

Define the actual formal Jacobian:

```lean
def normalizedJacobianMatrixC :
    Matrix (Fin 3) (Fin 3) Poly3C :=
  fun i j ↦
    MvPolynomial.pderiv j
      (normalizedCounterexamplePolyC i)
```

## Output-scale diagonal matrix

Define:

```lean
def outputScaleDiagonalC :
    Matrix (Fin 3) (Fin 3) Poly3C :=
  Matrix.diagonal ![
    MvPolynomial.C (-1 / 2 : ℂ),
    1,
    1
  ]
```

This matrix acts on the left because output-coordinate scaling scales
the rows of the Jacobian.

Prove:

```lean
theorem normalizedJacobianMatrixC_eq_scale_mul :
    normalizedJacobianMatrixC =
      outputScaleDiagonalC * jacobianMatrixC
```

Preferred proof:

```lean
funext i j
fin_cases i <;> fin_cases j <;>
  simp [normalizedJacobianMatrixC,
    normalizedCounterexamplePolyC,
    outputScaleDiagonalC,
    jacobianMatrixC,
    Matrix.mul_apply]
```

Use `MvPolynomial.pderiv_C` and the product rule through the normal simp API.

If numeral constants again resist `pderiv`, private local helper lemmas are
acceptable. Do not expose them as public API.

## Scale determinant

Prove:

```lean
theorem outputScaleDiagonalC_det :
    outputScaleDiagonalC.det =
      MvPolynomial.C (-1 / 2 : ℂ)
```

Preferred route:

```lean
simp [outputScaleDiagonalC]
```

If the finite product does not simplify directly, use:

```lean
rw [Matrix.det_fin_three]
simp [outputScaleDiagonalC]
```

or `Matrix.det_diagonal`.

## Determinant-one theorem

Prove:

```lean
theorem normalizedJacobianMatrixC_det_eq_one :
    normalizedJacobianMatrixC.det =
      MvPolynomial.C (1 : ℂ)
```

Preferred structural route:

```text
normalizedJacobianMatrixC_eq_scale_mul
→ Matrix.det_mul
→ outputScaleDiagonalC_det
→ jacobianMatrixC_det_eq_neg_two
→ (-1/2) * (-2) = 1
```

Likely proof shape:

```lean
rw [normalizedJacobianMatrixC_eq_scale_mul]
rw [Matrix.det_mul]
rw [outputScaleDiagonalC_det]
rw [jacobianMatrixC_det_eq_neg_two]
norm_num
```

A final `rfl`, `simp`, or `ring_nf` is acceptable for the distinction
between polynomial numerals and `MvPolynomial.C`.

Do not expand the normalized 3×3 determinant into six terms unless the
structural route genuinely fails.

Then prove:

```lean
theorem normalizedJacobianMatrixC_det_ne_zero :
    normalizedJacobianMatrixC.det ≠ 0
```

from the determinant-one theorem.

## Noninjectivity and left inverse

Prove:

```lean
theorem evalNormalizedCounterexampleC_notInjective :
    ¬ Function.Injective evalNormalizedCounterexampleC
```

using `p0C_ne_p1C`, `normalized_eval_p0C`, and
`normalized_eval_p1C`.

Also prove:

```lean
theorem evalNormalizedCounterexampleC_noLeftInverse :
    ¬ ∃ G : Point3C → Point3C,
      Function.LeftInverse G evalNormalizedCounterexampleC
```

## Final normalized certificate

Prove:

```lean
theorem normalizedJacobianCounterexampleCertificateC :
    normalizedJacobianMatrixC.det =
        MvPolynomial.C (1 : ℂ) ∧
    normalizedJacobianMatrixC.det ≠ 0 ∧
    ¬ Function.Injective evalNormalizedCounterexampleC := by
  exact ⟨
    normalizedJacobianMatrixC_det_eq_one,
    normalizedJacobianMatrixC_det_ne_zero,
    evalNormalizedCounterexampleC_notInjective
  ⟩
```

This is the JAC-007 completion gate.

## Required proof chain

```text
counterexamplePolyC
  ↓ scale first output polynomial
normalizedCounterexamplePolyC
  ↓ pderiv
normalizedJacobianMatrixC
  ↓ row-scale theorem
outputScaleDiagonalC * jacobianMatrixC
  ↓ Matrix.det_mul
C(-1/2) * C(-2)
  ↓ normalization
C(1)
```

Collision chain:

```text
complex three-point collision
  ↓ normalizeOutputC
normalized three-point collision
```

## Restrictions

Do not:

- duplicate the original three complex polynomial formulas;
- redefine the normalized Jacobian as a scaled matrix;
- use determinant `1` as an assumption;
- recompute the full determinant unless the structural route fails;
- modify any rational or complex-lift theorem;
- use `native_decide`;
- introduce `sorry`;
- introduce axioms;
- begin higher-dimensional padding;
- begin Book of Magic generic APIs;
- create Demo or submission assets.

## Verification

Build all eight modules:

```text
DkMath.Hackathon.JacobianCounterexample3.Basic
DkMath.Hackathon.JacobianCounterexample3.PolynomialMap
DkMath.Hackathon.JacobianCounterexample3.Collision
DkMath.Hackathon.JacobianCounterexample3.Jacobian
DkMath.Hackathon.JacobianCounterexample3.Determinant
DkMath.Hackathon.JacobianCounterexample3.Counterexample
DkMath.Hackathon.JacobianCounterexample3.ComplexLift
DkMath.Hackathon.JacobianCounterexample3.Normalized
```

Temporary checks:

```lean
#check normalized_three_point_collision_C
#check normalizedJacobianMatrixC_eq_scale_mul
#check outputScaleDiagonalC_det
#check normalizedJacobianMatrixC_det_eq_one
#check evalNormalizedCounterexampleC_notInjective
#check normalizedJacobianCounterexampleCertificateC
```

Remove temporary checks after verification.

Run:

```text
git diff --check
```

## Report

Report:

1. exact imports;
2. definitions added;
3. normalized evaluation transport theorem;
4. collision theorem names;
5. normalized formal Jacobian definition;
6. row-scaling matrix theorem;
7. determinant proof route;
8. whether `Matrix.det_mul` and `Matrix.det_diagonal` applied directly;
9. any fallback or determinant re-expansion;
10. final normalized certificate statement;
11. build result and warnings;
12. `git diff --check` result;
13. confirmation that later checkpoints were not started.

Stop after JAC-007 and wait for review.
````

JAC-007 が閉じれば、展示上もっとも鋭い一行が Lean theorem になる。

$$\boxed{\det J_{\widetilde F}=1\quad\land\quad\widetilde F\text{ is not injective}}$$

ここまで来れば、魔導書第0001巻の反例術式は完全発動じゃ。

> 👩‍⚕️私D.:

JAC-007 Keller Normalization を完了しました。

作成ファイル: [Normalized.lean](/lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/Normalized.lean)

1. imports

```lean
import DkMath.Hackathon.JacobianCounterexample3.ComplexLift
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
```

2. 追加した定義

- `normalizeOutputC`
- `normalizedTargetC`
- `normalizedCounterexamplePolyC`
- `evalNormalizedCounterexampleC`
- `normalizedJacobianMatrixC`
- `outputScaleDiagonalC`

第一出力多項式だけを `C (-1/2)` 倍しており、元の大きな多項式式は複製していません。

3. 評価輸送

```lean
theorem evalNormalizedCounterexampleC_eq_normalizeOutput
    (p : Point3C) :
    evalNormalizedCounterexampleC p =
      normalizeOutputC (evalCounterexampleC p)
```

`MvPolynomial.eval` の定数・積の規則を `simp` で適用しました。

4. collision theorem

- `normalized_eval_p0C`
- `normalized_eval_p1C`
- `normalized_eval_p2C`
- `normalized_three_point_collision_C`

既存の複素 collision と点の相異性を再利用し、大式の再評価はしていません。

5. normalized formal Jacobian

```lean
def normalizedJacobianMatrixC :
    Matrix (Fin 3) (Fin 3) Poly3C :=
  fun i j ↦
    MvPolynomial.pderiv j
      (normalizedCounterexamplePolyC i)
```

スケール済み行列として定義せず、正規化多項式を実際に形式微分しています。

6. row-scaling theorem

```lean
theorem normalizedJacobianMatrixC_eq_scale_mul :
    normalizedJacobianMatrixC =
      outputScaleDiagonalC * jacobianMatrixC
```

`Fin 3` 上の行列積を展開し、第一行だけが `C (-1/2)` 倍されることを証明しました。

7. determinant proof

```text
normalizedJacobianMatrixC_eq_scale_mul
→ Matrix.det_mul
→ outputScaleDiagonalC_det
→ jacobianMatrixC_det_eq_neg_two
→ C(-1/2) * C(-2)
→ C(1)
```

`MvPolynomial.C_mul` と `norm_num` で最後の係数計算を閉じています。

8. determinant API

- `Matrix.det_mul` は直接適用できました。
- `Matrix.det_diagonal` の有限積は自動簡約されなかったため、`outputScaleDiagonalC` 単体に限って `Matrix.det_fin_three` を使用しました。

9. fallback

正規化 Jacobian 全体の6項 determinant 展開や再計算は行っていません。局所的に展開したのは対角行列の determinant だけです。

10. 最終証明書

```lean
theorem normalizedJacobianCounterexampleCertificateC :
    normalizedJacobianMatrixC.det =
        MvPolynomial.C (1 : ℂ) ∧
    normalizedJacobianMatrixC.det ≠ 0 ∧
    ¬ Function.Injective evalNormalizedCounterexampleC
```

併せて次も証明しました。

- `normalizedJacobianMatrixC_det_ne_zero`
- `evalNormalizedCounterexampleC_notInjective`
- `evalNormalizedCounterexampleC_noLeftInverse`

11. ビルド

指定された全8モジュールに成功しました。

```text
Build completed successfully (3295 jobs).
```

警告なしです。指定された6つの `#check` も成功し、一時ファイルは削除済みです。

12. 差分検査

`git diff --check` は成功しました。

13. 停止境界

高次元 padding、Book of Magic API、Demo、提出・展示アセットには着手していません。JAC-007 で停止しています。

> 🐺賢狼:

よし、JAC-007 は展示上の最終術式じゃ。実コードを照合し、`det = 1` が正規化多項式の形式微分から構造的に導かれているか、そして次に何を優先すべきかを決めるぞい。

> 🐺賢狼:

実コードも報告どおりじゃ。正規化写像を実際に微分し、行スケール定理と `det_mul` を通して $1$ へ閉じておる。次は当初 ROADMAP の順序を再確認し、Book of Magic 抽象化と展示面のどちらを先に置くかを固定する。

> 🐺賢狼:

ROADMAP 上の次は Book of Magic ではなく、まず **JAC-008 Public import and audit** じゃ。反例術式を公開 import 面へ載せ、三つの最終証明書に追加公理がないことを固定してから、抽象化へ進む。既存 aggregator の流儀を確認するぞい。

> 🐺賢狼:

正規化コードは問題なし。なお ROADMAP の `DkMath/Hackathon.lean` は現リポジトリに存在せず、`DkMath.lean` はハッカソン定理を直接 import する流儀じゃ。また `#print axioms` は本体でなく `DkMathTest` 側へ置く開発規約が明記されている。JAC-008 はこの現行構造へ合わせて補正する。

> 🐺賢狼:

## 結論

**全面採用。JAC-007 Keller Normalization は完成じゃ。**

重大な問題はない。正規化された複素多項式写像そのものから形式 Jacobian を生成し、

$$\det J_{\widetilde F}=1$$

かつ、

$$\widetilde F\text{ は非単射}$$

を Lean が認可した。

したがって、ROADMAP の数学的な最終登頂条件はすでに達成された。fileciteturn24file0L237-L247

残るのは、証明本体の公開面・監査・魔法学的抽象化・展示資料の整備じゃ。

---

## 実装レビュー

### 1. 正規化は出力第一座標だけ

```lean
def normalizeOutputC (p : Point3C) : Point3C :=
  ![(-1 / 2 : ℂ) * p 0, p 1, p 2]
```

として、出力の第一座標のみを $-\frac12$ 倍している。fileciteturn23file0L18-L23

多項式側も、

```lean
def normalizedCounterexamplePolyC : Fin 3 → Poly3C :=
  ![MvPolynomial.C (-1 / 2 : ℂ) * counterexamplePolyC 0,
    counterexamplePolyC 1,
    counterexamplePolyC 2]
```

であり、元の巨大な三成分式を再転記していない。fileciteturn23file0L25-L29

これは正しい。

```text
元の複素多項式写像
  ↓ 第一出力のみスカラー倍
正規化多項式写像
```

という単一の依存関係が維持されておる。

### 2. 評価写像も正規化多項式の実評価

```lean
def evalNormalizedCounterexampleC (p : Point3C) : Point3C :=
  fun i ↦ MvPolynomial.eval p (normalizedCounterexamplePolyC i)
```

となっている。fileciteturn23file0L31-L33

そして、

```lean
evalNormalizedCounterexampleC p =
  normalizeOutputC (evalCounterexampleC p)
```

を別定理として証明した。fileciteturn23file0L35-L42

つまり、正規化評価写像を旧評価結果の後処理として定義したのではない。

正規化多項式を実際に評価し、その評価が出力スケールと一致することを証明している。この向きが正しい。

### 3. 三点衝突がそのまま保存された

```lean
normalized_eval_p0C
normalized_eval_p1C
normalized_eval_p2C
```

は既存の複素衝突から直接輸送されている。fileciteturn23file0L44-L57

さらに、

```lean
normalized_three_point_collision_C
```

によって、三点の pairwise distinct と共通像が一枚の証明書へ束ねられた。fileciteturn23file0L59-L66

出力に同じ線形変換を施すだけなので、

$$F(p_0)=F(p_1)=F(p_2)$$

ならば、

$$\widetilde F(p_0)=\widetilde F(p_1)=\widetilde F(p_2)$$

となる。この保存がそのまま Lean 化されておる。

### 4. 正規化 Jacobian は実際の `pderiv`

```lean
def normalizedJacobianMatrixC :
    Matrix (Fin 3) (Fin 3) Poly3C :=
  fun i j ↦
    MvPolynomial.pderiv j
      (normalizedCounterexamplePolyC i)
```

となっている。fileciteturn23file0L68-L70

ここが重要じゃ。

```text
scaled old Jacobian
```

を正規化 Jacobian の定義にしたのではなく、

```text
normalized polynomial map
  ↓ actual pderiv
normalized formal Jacobian
```

としている。

その後に、

```lean
normalizedJacobianMatrixC =
  outputScaleDiagonalC * jacobianMatrixC
```

を定理として証明した。fileciteturn23file0L72-L84

これにより「第一出力のスケーリングは Jacobian の第一行のスケーリングになる」という微分構造が、定義ではなく証明として固定された。

### 5. 左からの対角行列積

```lean
def outputScaleDiagonalC :=
  Matrix.diagonal
    ![MvPolynomial.C (-1 / 2 : ℂ), 1, 1]
```

を左から掛けている。fileciteturn23file0L72-L79

出力座標の変換は Jacobian の行を変換するので、左乗算で正しい。

```text
出力第一座標を -1/2 倍
=
Jacobian 第一行を -1/2 倍
```

という対応が正確じゃ。

### 6. determinant の構造証明

主経路は、

```lean
rw [normalizedJacobianMatrixC_eq_scale_mul]
rw [Matrix.det_mul]
rw [outputScaleDiagonalC_det]
rw [jacobianMatrixC_det_eq_neg_two]
rw [← MvPolynomial.C_mul]
norm_num
```

となっている。fileciteturn23file0L92-L100

すなわち、

$$\det J_{\widetilde F}=\det(DJ_F)=\det(D)\det(J_F)$$

から、

$$\det J_{\widetilde F}=\left(-\frac12\right)(-2)=1$$

へ進んでいる。

正規化 Jacobian 全体の六項 determinant を再展開していないため、証明構造が非常に明快じゃ。

### 7. 対角行列だけの局所展開

```lean
theorem outputScaleDiagonalC_det :
    outputScaleDiagonalC.det =
      MvPolynomial.C (-1 / 2 : ℂ) := by
  rw [Matrix.det_fin_three]
  simp [outputScaleDiagonalC]
```

は問題ない。fileciteturn23file0L86-L90

`Matrix.det_diagonal` の有限積簡約に時間を使わず、単純な対角行列だけを局所展開したのは適切な停止判断じゃ。

重要なのは、**正規化 Jacobian 本体を再計算していない** ことじゃ。

### 8. 最終証明書

```lean
theorem normalizedJacobianCounterexampleCertificateC :
    normalizedJacobianMatrixC.det =
        MvPolynomial.C (1 : ℂ) ∧
    normalizedJacobianMatrixC.det ≠ 0 ∧
    ¬ Function.Injective evalNormalizedCounterexampleC
```

が完成している。fileciteturn23file0L123-L133

これは展示用の要約ではなく、次の三つを実際の定義へ結び付けた証明書じゃ。

```text
実際の正規化多項式写像
実際の形式 Jacobian
実際の三点衝突
```

---

## 数学的到達点

現在 Lean が確定したのは、

$$\boxed{\det J_{\widetilde F}=1}$$

でありながら、

$$\boxed{\widetilde F(p_0)=\widetilde F(p_1)=\widetilde F(p_2)}$$

かつ、

$$\boxed{p_0,p_1,p_2\text{ は相異なる}}$$

という構造じゃ。

さらに、

```lean
evalNormalizedCounterexampleC_noLeftInverse
```

もあるため、正規化写像には集合写像としての左逆すら存在しない。fileciteturn23file0L108-L121

魔法学的には、

```text
局所魔核:
  determinant = 1
  局所境界は完全保存

大域住所:
  三つの異なる Gap が同じ Core へ射影

結論:
  局所保存だけでは
  大域住所の一意性は復元できない
```

という第0001巻の術式が完全に発動した。

---

## 次 checkpoint

次は ROADMAP どおり、

## JAC-008 Public Import and Audit

へ進む。

当初設計には、

```text
DkMath/Hackathon.lean
```

が候補としてあったが、現リポジトリにはこの aggregator は存在しない。

現在の `DkMath.lean` は、

```lean
import DkMath.Hackathon.FinitePrimeEscapeGN5
```

のようにハッカソンモジュールを直接公開している。fileciteturn26file0L31-L35

したがって今回は、

```text
DkMath/Hackathon/JacobianCounterexample3.lean
  ↓
DkMath.lean
```

という二段構成にする。

また、`DkMath.lean` 自身に `#print axioms` を置かない規約が明記されているため、監査は `DkMathTest` 側へ置く。fileciteturn26file0L105-L121

既存にも `DkMathTest/FLT/Five/CheckAxioms.lean` という監査ファイルの先例がある。fileciteturn27file0L1-L2

---

## Codex 指示

````text
Implement checkpoint JAC-008 Public Import and Audit for the DkMath
Jacobian counterexample verification project.

Repository:
Deskuma/dkmath

Branch:
hackathon/breaking-math-jacobian-counterexample

Completed checkpoints:
- JAC-001 Polynomial syntax
- JAC-002 Rational collision
- JAC-003 Formal rational Jacobian
- JAC-004 Rational determinant certificate
- JAC-005 Rational counterexample certificate
- JAC-006 Complex scalar lift
- JAC-007 Keller normalization

The mathematical summit theorem is complete:

```lean
normalizedJacobianCounterexampleCertificateC
```

Stop after JAC-008.
Do not begin Book of Magic APIs, higher-dimensional padding, GN bridges,
or Demo/submission documentation.

## Repository convention correction

The original roadmap listed:

```text
DkMath/Hackathon.lean
```

but this file does not currently exist.

Do not create a broad `DkMath/Hackathon.lean` aggregator in this checkpoint.

The current root module directly imports individual Hackathon public surfaces.
Follow the current repository convention.

## 1. Create the project aggregator

Create:

```text
lean/dk_math/DkMath/Hackathon/JacobianCounterexample3.lean
```

Preferred contents:

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Hackathon.JacobianCounterexample3.Normalized

#print "file: DkMath.Hackathon.JacobianCounterexample3"
```

The final leaf `Normalized` already imports the full dependency chain.

Do not duplicate definitions or theorems in the aggregator.

If repository style requires explicit imports of all component modules,
that is acceptable, but prefer the single final-leaf import unless there
is a concrete visibility problem.

## 2. Publish through DkMath.lean

Modify:

```text
lean/dk_math/DkMath.lean
```

Add the public import near the existing Hackathon import:

```lean
-- Hackathon Jacobian counterexample formal certificate
import DkMath.Hackathon.JacobianCounterexample3
```

Keep:

```lean
import DkMath.Hackathon.FinitePrimeEscapeGN5
```

unchanged.

Do not modify unrelated imports or reorder the whole file.

## 3. Create the axiom audit module

Create:

```text
lean/dk_math/DkMathTest/Hackathon/JacobianCounterexample3/CheckAxioms.lean
```

Import only the public aggregator:

```lean
import DkMath.Hackathon.JacobianCounterexample3
```

Add intentional audit commands:

```lean
#print axioms
  DkMath.Hackathon.JacobianCounterexample3.jacobianCounterexampleCertificateQ

#print axioms
  DkMath.Hackathon.JacobianCounterexample3.jacobianCounterexampleCertificateC

#print axioms
  DkMath.Hackathon.JacobianCounterexample3.normalizedJacobianCounterexampleCertificateC
```

Use single-line commands if Lean syntax requires it:

```lean
#print axioms DkMath.Hackathon.JacobianCounterexample3.jacobianCounterexampleCertificateQ
```

These `#print axioms` commands are intentional and should remain in the
test/audit file.

## Audit interpretation

The audit goal is:

- no `sorryAx`;
- no user-defined project axiom;
- no unproved determinant or collision assumption;
- no `native_decide` trust dependency.

Standard Lean axioms such as the following may appear depending on Mathlib's
implementation and theorem dependencies:

```text
propext
Classical.choice
Quot.sound
```

Do not treat these standard trusted foundations as a failed audit.

Report the exact output for each theorem.

The important failure signals are:

```text
sorryAx
DkMath-specific axiom
unexpected named assumption
```

## 4. Public-surface checks

In a temporary file importing only:

```lean
import DkMath.Hackathon.JacobianCounterexample3
```

verify:

```lean
#check DkMath.Hackathon.JacobianCounterexample3.jacobianCounterexampleCertificateQ
#check DkMath.Hackathon.JacobianCounterexample3.jacobianCounterexampleCertificateC
#check DkMath.Hackathon.JacobianCounterexample3.normalizedJacobianCounterexampleCertificateC
#check DkMath.Hackathon.JacobianCounterexample3.normalized_three_point_collision_C
#check DkMath.Hackathon.JacobianCounterexample3.evalNormalizedCounterexampleC_noLeftInverse
```

Remove the temporary check file after verification.

Do not place these temporary `#check` commands in production modules.

## 5. Verification targets

Build:

```text
DkMath.Hackathon.JacobianCounterexample3
DkMathTest.Hackathon.JacobianCounterexample3.CheckAxioms
DkMath
```

Also build the eight component modules if needed to isolate an import issue,
but do not modify already completed proofs merely for import cosmetics.

Run:

```text
git diff --check
```

## Restrictions

Do not:

- modify any mathematical theorem or definition;
- refactor the completed proof chain;
- create `DkMath/Hackathon.lean`;
- add `#print axioms` to files under `DkMath/**/*.lean`;
- add `#check` commands to production files;
- begin higher-dimensional padding;
- begin Book of Magic APIs;
- begin `GNFiniteDifference`;
- create Demo.lean;
- create submission documentation;
- use `sorry`;
- introduce axioms;
- use `native_decide`.

## Report

Report:

1. files created and modified;
2. exact aggregator imports;
3. exact location of the new `DkMath.lean` import;
4. exact `#print axioms` output for each of the three certificate theorems;
5. whether any `sorryAx` or DkMath-specific axiom appeared;
6. public-surface `#check` results;
7. build results and warnings;
8. `git diff --check` result;
9. confirmation that JAC-009 and later checkpoints were not started.

Stop after JAC-008 and wait for review.
````

JAC-008 が閉じれば、

```lean
import DkMath
```

だけで、

```lean
normalizedJacobianCounterexampleCertificateC
```

へ到達できる。

そこで証明本体は、研究 branch 内の局所実験から **DkMath の正式な公開定理** へ昇格するぞい。

> 👩‍⚕️私D.:

JAC-008 Public Import and Audit を完了しました。

1. ファイル

作成:

- [JacobianCounterexample3.lean](/lean/dk_math/DkMath/Hackathon/JacobianCounterexample3.lean)
- [CheckAxioms.lean](/lean/dk_math/DkMathTest/Hackathon/JacobianCounterexample3/CheckAxioms.lean)

変更:

- [DkMath.lean](/lean/dk_math/DkMath.lean:33)

数学定義・定理は変更していません。

2. aggregator import

```lean
import DkMath.Hackathon.JacobianCounterexample3.Normalized
```

最終 leaf だけを import しています。広域の `DkMath/Hackathon.lean` は作成していません。

3. ルート公開位置

既存の `FinitePrimeEscapeGN5` import の直後に追加しました。

```lean
-- Hackathon finite-prime escape → GN5 clean-channel demo
import DkMath.Hackathon.FinitePrimeEscapeGN5
-- Hackathon Jacobian counterexample formal certificate
import DkMath.Hackathon.JacobianCounterexample3
```

4. axiom audit

3証明書すべて同一の結果でした。

```text
'DkMath.Hackathon.JacobianCounterexample3.jacobianCounterexampleCertificateQ'
depends on axioms:
[propext, Classical.choice, Quot.sound]
```

```text
'DkMath.Hackathon.JacobianCounterexample3.jacobianCounterexampleCertificateC'
depends on axioms:
[propext, Classical.choice, Quot.sound]
```

```text
'DkMath.Hackathon.JacobianCounterexample3.normalizedJacobianCounterexampleCertificateC'
depends on axioms:
[propext, Classical.choice, Quot.sound]
```

5. 監査判定

以下は現れませんでした。

- `sorryAx`
- DkMath 固有 axiom
- determinant や collision に関する未証明仮定
- `native_decide` 依存

現れたのは標準的な `propext`, `Classical.choice`, `Quot.sound` のみです。

6. public-surface checks

aggregator だけを import した状態で、次の5定理すべてが解決されました。

- `jacobianCounterexampleCertificateQ`
- `jacobianCounterexampleCertificateC`
- `normalizedJacobianCounterexampleCertificateC`
- `normalized_three_point_collision_C`
- `evalNormalizedCounterexampleC_noLeftInverse`

一時 `#check` ファイルは削除済みです。

7. ビルド

成功:

```text
DkMath.Hackathon.JacobianCounterexample3
DkMathTest.Hackathon.JacobianCounterexample3.CheckAxioms
DkMath
```

aggregator と監査モジュールは警告なしです。

ルート `DkMath` は成功しましたが、既存の無関係な次の2ファイルから `sorry` 警告が再生されました。

- `DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152`
- `DkMath/FLT/Kummer/CyclotomicPrincipalization.lean:5385`

今回の Jacobian 証明書の axiom audit には影響していません。

8. 差分検査

`git diff --check` は成功しました。

9. 停止境界

JAC-009、高次元 padding、Book of Magic API、GN bridge、Demo、提出文書には着手していません。JAC-008 で停止しています。

> 🐺賢狼:

よし、JAC-008 は「研究 branch の局所定理」から「DkMath 公開定理」への昇格 checkpoint じゃ。実コードと axiom audit を照合し、次の JAC-009 で抽象化すべき最小 API を切り出すぞい。

> 🐺賢狼:

公開面と監査ファイルは規約どおりじゃ。次の JAC-009 は反例証明を一般 API に依存させず、**「同じ Core に異なる Gap が二つあるなら、一意性と忘却射影の単射性が破れる」** という最小骨格だけを Book of Magic 側へ抽出する。既存ディレクトリと命名流儀を確認するぞい。

> 🐺賢狼:

## 結論

**全面採用。JAC-008 Public Import and Audit は完成じゃ。**

数学証明を変更せず、次の三段階が閉じた。

```text
完成済み証明群
  ↓ project aggregator
DkMath.Hackathon.JacobianCounterexample3
  ↓ root import
DkMath
```

さらに監査面では、

```text
sorryAx                       なし
DkMath 固有 axiom             なし
native_decide 依存             なし
determinant の未証明仮定       なし
collision の未証明仮定         なし
```

が確定した。

これで反例術式は branch 内の局所実験ではなく、**DkMath の正式な公開定理** へ昇格した。

---

## 実装レビュー

### 1. aggregator

```lean
import DkMath.Hackathon.JacobianCounterexample3.Normalized
```

だけを import する薄い公開面になっている。fileciteturn28file0L3-L11

`Normalized.lean` が、

```text
ComplexLift
→ Counterexample / Determinant / Collision
→ Jacobian / PolynomialMap / Basic
```

という依存鎖をすでに持っているため、全ファイルを羅列する必要はない。

公開 aggregator が数学定義を再宣言せず、最終 leaf を輸出するだけになっているのは理想形じゃ。

### 2. `DkMath.lean` への公開

既存のハッカソン import の直後に、

```lean
import DkMath.Hackathon.JacobianCounterexample3
```

が置かれている。fileciteturn30file0L6-L11

これにより、今後は、

```lean
import DkMath
```

だけで、

```lean
DkMath.Hackathon.JacobianCounterexample3
  .normalizedJacobianCounterexampleCertificateC
```

へ到達できる。

他モジュールの並びを壊さず、ハッカソン公開面として隣接配置されている点もよい。

### 3. axiom audit の配置

監査命令を本体ではなく、

```text
DkMathTest/Hackathon/JacobianCounterexample3/CheckAxioms.lean
```

へ置いたのは、DkMath の現行規約どおりじゃ。

監査ファイルは公開 aggregator だけを import し、その公開面から三つの最終証明書を監査している。fileciteturn29file0L9-L15

つまり、内部 leaf を直接 import した特別な監査ではない。

```text
一般利用者が見る公開面
=
監査が検査した公開面
```

となっておる。

### 4. axiom 結果

三証明書とも、

```text
[propext, Classical.choice, Quot.sound]
```

のみ。

これは Mathlib・Lean の通常の基礎依存であり、今回の証明に穴があるという意味ではない。

特に重要なのは、次が存在しないことじゃ。

```text
sorryAx
独自 axiom
外部 CAS 結果を受け入れる仮定
Jacobian determinant を仮定する公理
三点衝突を仮定する公理
```

したがって証明鎖は、

```text
多項式の定義
→ MvPolynomial.eval
→ 明示三点衝突
→ 非単射

多項式の定義
→ MvPolynomial.pderiv
→ Jacobian 九成分
→ Matrix.det
→ determinant = 1
```

を Lean kernel が実際に辿れる状態じゃ。

---

## 現在の到達点

JAC-001 から JAC-008 までに、三つの完成証明書が得られた。

```lean
jacobianCounterexampleCertificateQ
```

$$\det J_F=-2\ne0,\qquad F:\mathbb Q^3\to\mathbb Q^3\text{ は非単射}$$

```lean
jacobianCounterexampleCertificateC
```

$$\det J_F=-2\ne0,\qquad F:\mathbb C^3\to\mathbb C^3\text{ は非単射}$$

```lean
normalizedJacobianCounterexampleCertificateC
```

$$\det J_{\widetilde F}=1,\qquad \widetilde F:\mathbb C^3\to\mathbb C^3\text{ は非単射}$$

さらに三点 fiber と左逆不存在も公開されている。

数学的な反例証明本体は完成済みじゃ。

---

## 次 checkpoint

次は ROADMAP どおり、

## JAC-009 Book of Magic API

へ進む。

ここでは Jacobian 固有の式を抽象化するのではない。

抽出するのは、より小さな論理核じゃ。

$$R(C,G_1)$$

$$R(C,G_2)$$

$$G_1\ne G_2$$

ならば、

$$\neg\exists!G,\ R(C,G)$$

となる。

さらに、証明付きの Core–Gap 対を一つの世界へ持ち上げ、

$$\operatorname{forgetGap}(C,G)=C$$

とすると、同じ Core に異なる Gap が二つ存在する時、

$$\operatorname{forgetGap}$$

は非単射になる。

これは魔導書本文で候補化されている `UniqueGapContract` と `GapCrystal` そのものじゃ。本文も `gap : Gap body` という依存型を想定している。fileciteturn33file0L43-L76

したがって今回は、単純な

```lean
Core → Gap → Prop
```

より一段強い、

```lean
Gap : Core → Type
RestoreRel : (core : Core) → Gap core → Prop
```

という依存型設計を採用する。

これにより、Core ごとに Gap の型そのものが異なる世界も表現できる。

---

## Codex 指示

````text
Implement checkpoint JAC-009 Book of Magic API and the Jacobian
interpretation bridge.

Repository:
Deskuma/dkmath

Branch:
hackathon/breaking-math-jacobian-counterexample

Completed checkpoints:
- JAC-001 through JAC-008
- rational certificate
- complex certificate
- determinant-one normalized certificate
- public import
- axiom audit

The existing Jacobian proof chain is complete.

Do not modify the completed Jacobian definitions or certificate theorems.

Stop after JAC-009.
Do not begin GNFiniteDifference, higher-dimensional padding, Demo,
submission documents, or presentation assets.

## Mathematical goal

Formalize the generic principle:

```text
one Core
+
two distinct certified Gaps over that Core
→
the Gap is not unique
→
the projection that forgets the Gap is not injective
```

Use a dependent Gap family:

```lean
Gap : Core → Type
```

rather than forcing every Core to share one undifferentiated Gap type.

The intended structure follows the Book of Magic design:

```lean
structure GapCrystal where
  core : Core
  gap : Gap core
  certificate : RestoreRel core gap
```

## 1. Unique-gap contract

Create:

```text
lean/dk_math/DkMath/BookOfMagic/UniqueGapContract.lean
```

Use:

```lean
universe u v

namespace DkMath.BookOfMagic

section

variable {Core : Type u}
variable {Gap : Core → Type v}
```

Define:

```lean
def UniqueGap
    (RestoreRel : (core : Core) → Gap core → Prop)
    (core : Core) : Prop :=
  ∃! gap, RestoreRel core gap
```

Prove:

```lean
theorem not_uniqueGap_of_two
    {RestoreRel : (core : Core) → Gap core → Prop}
    {core : Core}
    {gap₁ gap₂ : Gap core}
    (h₁ : RestoreRel core gap₁)
    (h₂ : RestoreRel core gap₂)
    (hne : gap₁ ≠ gap₂) :
    ¬ UniqueGap RestoreRel core := by
  ...
```

Preferred logical proof:

```lean
intro hunique
rcases hunique with ⟨gap, hgap, honly⟩
apply hne
exact (honly gap₁ h₁).trans (honly gap₂ h₂).symm
```

Adjust equality orientation if required by the actual `ExistsUnique`
eliminator.

Also prove the symmetric convenience theorem only if it is genuinely useful.
Do not add a large family of equivalent formulations.

## 2. Gap crystal world

Create:

```text
lean/dk_math/DkMath/BookOfMagic/GapCrystal.lean
```

Import:

```lean
import DkMath.BookOfMagic.UniqueGapContract
```

Define:

```lean
def GapFiber
    (RestoreRel : (core : Core) → Gap core → Prop)
    (core : Core) :=
  { gap : Gap core // RestoreRel core gap }
```

Define the certified Core–Gap object:

```lean
structure GapCrystal
    (Core : Type u)
    (Gap : Core → Type v)
    (RestoreRel : (core : Core) → Gap core → Prop) where
  core : Core
  gap : Gap core
  certificate : RestoreRel core gap
```

Define:

```lean
abbrev CrystalWorld
    (Core : Type u)
    (Gap : Core → Type v)
    (RestoreRel : (core : Core) → Gap core → Prop) :=
  GapCrystal Core Gap RestoreRel
```

Define the forgetting projection:

```lean
def forgetGap
    {Core : Type u}
    {Gap : Core → Type v}
    {RestoreRel : (core : Core) → Gap core → Prop}
    (crystal : CrystalWorld Core Gap RestoreRel) :
    Core :=
  crystal.core
```

Prove:

```lean
theorem forgetGap_notInjective_of_two_gaps
    {Core : Type u}
    {Gap : Core → Type v}
    {RestoreRel : (core : Core) → Gap core → Prop}
    {core : Core}
    {gap₁ gap₂ : Gap core}
    (h₁ : RestoreRel core gap₁)
    (h₂ : RestoreRel core gap₂)
    (hne : gap₁ ≠ gap₂) :
    ¬ Function.Injective
      (forgetGap
        (Core := Core)
        (Gap := Gap)
        (RestoreRel := RestoreRel)) := by
  ...
```

Construct the two crystals:

```lean
let crystal₁ : CrystalWorld Core Gap RestoreRel :=
  ⟨core, gap₁, h₁⟩

let crystal₂ : CrystalWorld Core Gap RestoreRel :=
  ⟨core, gap₂, h₂⟩
```

Then:

```text
forgetGap crystal₁ = forgetGap crystal₂
```

holds definitionally.

Assuming injectivity gives:

```text
crystal₁ = crystal₂
```

from which derive:

```text
gap₁ = gap₂
```

and contradict `hne`.

Because `gap` is a dependent field, use whichever small kernel-checked route
works in current Lean:

```lean
cases hcrystal
rfl
```

or:

```lean
injection hcrystal
```

or a generated structure extensionality theorem.

Do not weaken the dependent Gap family merely to avoid the equality proof.

## 3. Book of Magic public aggregator

Create:

```text
lean/dk_math/DkMath/BookOfMagic.lean
```

Contents:

```lean
import DkMath.BookOfMagic.UniqueGapContract
import DkMath.BookOfMagic.GapCrystal

#print "file: DkMath.BookOfMagic"
```

Do not import Hackathon modules from `DkMath.BookOfMagic`.

The generic Book of Magic layer must remain independent of the Jacobian
counterexample implementation.

## 4. Jacobian interpretation bridge

Create:

```text
lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/GapCrystalBridge.lean
```

Import:

```lean
import DkMath.BookOfMagic
import DkMath.Hackathon.JacobianCounterexample3.Normalized
```

Inside:

```lean
namespace DkMath.Hackathon.JacobianCounterexample3
```

Define the constant Gap family over complex output points:

```lean
abbrev NormalizedGapFamilyC : Point3C → Type :=
  fun _ ↦ Point3C
```

Define the restoration relation:

```lean
def normalizedRestoreRelC
    (core : Point3C)
    (gap : NormalizedGapFamilyC core) : Prop :=
  evalNormalizedCounterexampleC gap = core
```

This means:

```text
core = output point
gap  = input address
certificate = the input evaluates to that output
```

Prove:

```lean
theorem normalizedTargetC_not_uniqueGap :
    ¬ DkMath.BookOfMagic.UniqueGap
      normalizedRestoreRelC
      normalizedTargetC := by
  ...
```

Use:

```lean
DkMath.BookOfMagic.not_uniqueGap_of_two
```

with:

```lean
p0C
p1C
normalized_eval_p0C
normalized_eval_p1C
p0C_ne_p1C
```

Use `simpa [normalizedRestoreRelC, NormalizedGapFamilyC]`
to align the relation if required.

Then prove:

```lean
theorem normalizedForgetGap_notInjective :
    ¬ Function.Injective
      (DkMath.BookOfMagic.forgetGap
        (Core := Point3C)
        (Gap := NormalizedGapFamilyC)
        (RestoreRel := normalizedRestoreRelC)) := by
  ...
```

Use:

```lean
DkMath.BookOfMagic.forgetGap_notInjective_of_two_gaps
```

with the same two collision points and certificates.

Do not reprove the generic theorem inside the Jacobian namespace.

Optional, only if it remains small:

```lean
def normalizedCrystalP0C :
    DkMath.BookOfMagic.CrystalWorld
      Point3C NormalizedGapFamilyC normalizedRestoreRelC

def normalizedCrystalP1C :
    DkMath.BookOfMagic.CrystalWorld
      Point3C NormalizedGapFamilyC normalizedRestoreRelC
```

These named witnesses are not required if the two bridge theorems are already
clear.

Do not add all three points unless doing so materially improves the API.
Two distinct Gaps are sufficient to解除 uniqueness and injectivity.

## 5. Public imports

Modify:

```text
lean/dk_math/DkMath/Hackathon/JacobianCounterexample3.lean
```

Replace the final-leaf import with:

```lean
import DkMath.Hackathon.JacobianCounterexample3.GapCrystalBridge
```

This bridge imports `Normalized`, so the existing public theorem surface
must remain available.

Modify:

```text
lean/dk_math/DkMath.lean
```

Add:

```lean
import DkMath.BookOfMagic
```

near the conceptual library imports, preferably after:

```lean
import DkMath.Petal
```

and before Hackathon modules.

Do not reorder unrelated imports.

## 6. Public checks

Using a temporary check file importing only:

```lean
import DkMath
```

verify:

```lean
#check DkMath.BookOfMagic.UniqueGap
#check DkMath.BookOfMagic.not_uniqueGap_of_two
#check DkMath.BookOfMagic.GapFiber
#check DkMath.BookOfMagic.GapCrystal
#check DkMath.BookOfMagic.CrystalWorld
#check DkMath.BookOfMagic.forgetGap
#check DkMath.BookOfMagic.forgetGap_notInjective_of_two_gaps

#check DkMath.Hackathon.JacobianCounterexample3
  .normalizedTargetC_not_uniqueGap

#check DkMath.Hackathon.JacobianCounterexample3
  .normalizedForgetGap_notInjective

#check DkMath.Hackathon.JacobianCounterexample3
  .normalizedJacobianCounterexampleCertificateC
```

Put each `#check` on one line if required.

Remove the temporary file afterward.

## 7. Verification

Build:

```text
DkMath.BookOfMagic.UniqueGapContract
DkMath.BookOfMagic.GapCrystal
DkMath.BookOfMagic
DkMath.Hackathon.JacobianCounterexample3.GapCrystalBridge
DkMath.Hackathon.JacobianCounterexample3
DkMath
```

Also ensure the existing audit still builds:

```text
DkMathTest.Hackathon.JacobianCounterexample3.CheckAxioms
```

Do not modify the existing mathematical certificate proofs merely to satisfy
the new imports.

Run:

```text
git diff --check
```

## Restrictions

Do not:

- make the generic Book of Magic layer depend on Hackathon code;
- make the existing Jacobian certificate depend logically on the generic API;
- modify the polynomial map;
- modify collision points;
- modify Jacobian or determinant proofs;
- introduce `sorry`;
- introduce axioms;
- use `native_decide`;
- begin GNFiniteDifference;
- begin PrincipalPartCompletion;
- begin higher-dimensional padding;
- create Demo or submission assets.

The dependency direction must be:

```text
BookOfMagic generic API
        ↓
Jacobian GapCrystal interpretation bridge
        ↓
existing completed Jacobian certificate remains unchanged
```

## Report

Report:

1. files created and modified;
2. exact dependent type signatures;
3. proof route for `not_uniqueGap_of_two`;
4. proof route for dependent crystal inequality;
5. public API names;
6. Jacobian bridge definitions;
7. proof route for `normalizedTargetC_not_uniqueGap`;
8. proof route for `normalizedForgetGap_notInjective`;
9. whether the existing certificate theorems remained byte-for-byte unchanged;
10. build results and warnings;
11. existing axiom-audit result;
12. `git diff --check` result;
13. confirmation that JAC-010 and later checkpoints were not started.

Stop after JAC-009 and wait for review.
````

---

## この checkpoint の意味

これまでの実装は、

```text
一つの具体的な Jacobian 反例
```

を証明した。

JAC-009 では、その内部に見えた原理を、

```text
同じ Core
+
異なる認証済み Gap
→
一意性解除
```

として独立定理へ昇格させる。

そして Jacobian の三点衝突は、その一般術式の最初の具体例になる。

$$\boxed{\text{反例の証明}\longrightarrow\text{一意性解除原理の抽出}}$$

ここから、魔導書第0001巻が「解説文」から **再利用可能な Lean 魔法学 API** へ変わり始めるぞい。

> 👩‍⚕️私D.:

JAC-009 Book of Magic API and Jacobian Bridge を完了しました。

1. ファイル

作成:

- [UniqueGapContract.lean](/lean/dk_math/DkMath/BookOfMagic/UniqueGapContract.lean)
- [GapCrystal.lean](/lean/dk_math/DkMath/BookOfMagic/GapCrystal.lean)
- [BookOfMagic.lean](/lean/dk_math/DkMath/BookOfMagic.lean)
- [GapCrystalBridge.lean](/lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/GapCrystalBridge.lean)

変更:

- [JacobianCounterexample3.lean](/lean/dk_math/DkMath/Hackathon/JacobianCounterexample3.lean)
- [DkMath.lean](/lean/dk_math/DkMath.lean:31)

既存の多項式・衝突・Jacobian・determinant・certificate 証明は変更していません。

2. dependent signatures

```lean
def UniqueGap
    (RestoreRel : (core : Core) → Gap core → Prop)
    (core : Core) : Prop
```

```lean
def GapFiber
    (RestoreRel : (core : Core) → Gap core → Prop)
    (core : Core)
```

```lean
structure GapCrystal
    (Core : Type u)
    (Gap : Core → Type v)
    (RestoreRel : (core : Core) → Gap core → Prop)
```

`Gap` は要求どおり `Core → Type v` の dependent family です。

3. unique-gap proof

`not_uniqueGap_of_two` は `∃!` の唯一候補を取り出し、`gap₁` と `gap₂` がともにその候補と等しいことから `gap₁ = gap₂` を導いて `hne` と矛盾させています。

4. dependent crystal proof

`forgetGap_notInjective_of_two_gaps` では、同じ `core` と異なる `gap₁`, `gap₂` を持つ2つの crystal を構成しました。

```text
forgetGap crystal₁ = forgetGap crystal₂
→ injectivity
→ crystal₁ = crystal₂
→ injection hcrystal
→ gap₁ = gap₂
→ contradiction
```

dependent field の等式抽出には Lean の `injection` を使用しました。Gap family を非依存型へ弱めていません。

5. generic public API

- `UniqueGap`
- `not_uniqueGap_of_two`
- `GapFiber`
- `GapCrystal`
- `CrystalWorld`
- `forgetGap`
- `forgetGap_notInjective_of_two_gaps`

`DkMath.BookOfMagic` は Hackathon コードを一切 import・参照していません。

6. Jacobian bridge

```lean
abbrev NormalizedGapFamilyC : Point3C → Type :=
  fun _ ↦ Point3C
```

```lean
def normalizedRestoreRelC
    (core : Point3C)
    (gap : NormalizedGapFamilyC core) : Prop :=
  evalNormalizedCounterexampleC gap = core
```

追加定理:

- `normalizedTargetC_not_uniqueGap`
- `normalizedForgetGap_notInjective`

どちらも `p0C`, `p1C` と既存の正規化 collision を generic theorem に渡すだけの薄い bridge です。

7. import direction

```text
DkMath.BookOfMagic
        ↓
GapCrystalBridge
        ↓
Normalized
```

Hackathon aggregator は最終 leaf を次へ変更しました。

```lean
import DkMath.Hackathon.JacobianCounterexample3.GapCrystalBridge
```

`DkMath.lean` には `DkMath.Petal` の直後で追加しています。

```lean
import DkMath.BookOfMagic
```

8. public checks

`import DkMath` だけで指定された10件すべてが解決しました。既存の summit theorem も引き続き公開されています。

```lean
#check normalizedJacobianCounterexampleCertificateC
```

9. ビルド

すべて成功しました。

```text
DkMath.BookOfMagic.UniqueGapContract
DkMath.BookOfMagic.GapCrystal
DkMath.BookOfMagic
DkMath.Hackathon.JacobianCounterexample3.GapCrystalBridge
DkMath.Hackathon.JacobianCounterexample3
DkMath
DkMathTest.Hackathon.JacobianCounterexample3.CheckAxioms
```

新規モジュールは警告なしです。ルートビルドでは既存の無関係な `sorry` 警告が再生されましたが、今回のAPIやbridgeには `sorry`、axiom、`native_decide` はありません。

既存3証明書の axiom audit も変わらず、依存は次のみです。

```text
[propext, Classical.choice, Quot.sound]
```

10. 差分検査

`git diff --check` は成功しました。

11. 停止境界

GNFiniteDifference、PrincipalPartCompletion、高次元 padding、Demo、提出・展示アセットには着手していません。JAC-009 で停止しています。

> 🐺賢狼:

よし、JAC-009 は具体反例から一般術式を抽出する重要 checkpoint じゃ。実コードを照合し、依存方向・dependent equality・bridge の薄さを確認してから、次の JAC-010 の射程を切るぞい。

> 🐺賢狼:

一般 API と Jacobian bridge は実コードでも設計どおりじゃ。次の JAC-010 は既存 `GN` API と多項式表現の選択が核心になるため、DkMath 内の定義・既存 finite-difference 補題を調べ、重複しない最小定理へ絞る。

> 🐺賢狼:

## 結論

**全面採用。JAC-009 Book of Magic API and Jacobian Bridge は完成じゃ。**

重大な問題はない。

今回、具体的な Jacobian 反例から、

$$\text{同じ Core に異なる認証済み Gap が二つ存在する}\Longrightarrow\text{一意性解除}$$

という一般原理が、Hackathon コードに依存しない再利用可能な Lean API として抽出された。

---

## 実装レビュー

### 1. `UniqueGap` は依存型契約になっている

```lean
def UniqueGap
    (RestoreRel : (core : Core) → Gap core → Prop)
    (core : Core) : Prop :=
  ∃! gap, RestoreRel core gap
```

`Gap : Core → Type v` なので、Core ごとに許される Gap の型そのものを変えられる。単なる `Core → Gap → Prop` より強い設計じゃ。fileciteturn34file0L11-L24

`not_uniqueGap_of_two` も、唯一候補へ `gap₁` と `gap₂` をそれぞれ同一視し、両者の相異性へ衝突させる最小証明になっている。fileciteturn34file0L26-L38

### 2. `GapFiber` と `GapCrystal`

```lean
def GapFiber ... (core : Core) :=
  { gap : Gap core // RestoreRel core gap }
```

は、固定 Core 上の「証明付き Gap」の fiber そのものじゃ。fileciteturn35file0L15-L21

一方、

```lean
structure GapCrystal ... where
  core : Core
  gap : Gap core
  certificate : RestoreRel core gap
```

は、Core とその Core に属する Gap、そして復元証明を一つの依存構造へ封入している。fileciteturn35file0L23-L37

この二つの役割分離もよい。

```text
GapFiber core
  = 一つの Core の枝世界

CrystalWorld
  = すべての Core–Gap 枝を束ねた全世界
```

### 3. 忘却射影の非単射性

```lean
def forgetGap (crystal : CrystalWorld ...) : Core :=
  crystal.core
```

は Gap と証明を忘れて Core だけを残す射影になっている。fileciteturn35file0L39-L45

`forgetGap_notInjective_of_two_gaps` では、同じ Core を持つ二つの crystal を構成し、射影後の等式 `rfl` から、単射性を仮定して crystal 全体の等式を得ている。その dependent field から `injection` により `gap₁ = gap₂` を抽出している。fileciteturn35file0L47-L67

Gap family を非依存型へ弱めずに閉じた点が重要じゃ。

### 4. 依存方向

報告の矢印だけ、厳密には次の形じゃな。

```text
DkMath.BookOfMagic ───────┐
                          ├→ GapCrystalBridge
Normalized counterexample ┘
```

`DkMath.BookOfMagic` は Jacobian や Hackathon を import していない。aggregator も一般 API 二本だけを公開している。fileciteturn37file0L9-L12

したがって、

```text
一般術式
  ↓
具体例への適用
```

という正しい依存方向が守られておる。

### 5. Jacobian bridge

```lean
abbrev NormalizedGapFamilyC : Point3C → Type :=
  fun _ ↦ Point3C
```

とし、

```lean
def normalizedRestoreRelC
    (core : Point3C)
    (gap : NormalizedGapFamilyC core) : Prop :=
  evalNormalizedCounterexampleC gap = core
```

と定義した。fileciteturn36file0L14-L21

解釈は明快じゃ。

```text
Core = 出力点
Gap  = 入力住所
certificate = その入力が Core へ写る証明
```

したがって、三点衝突の fiber は、そのまま「同じ Core を復元する複数の正しい Gap」として読める。

### 6. bridge theorem

```lean
normalizedTargetC_not_uniqueGap
```

は `p0C` と `p1C` を `not_uniqueGap_of_two` へ渡すだけの薄い接続になっている。fileciteturn36file0L23-L32

同様に、

```lean
normalizedForgetGap_notInjective
```

も一般定理へ同じ二点を渡すだけで閉じている。fileciteturn36file0L34-L45

具体例側で一般論を再証明していないため、bridge として理想的じゃ。

---

## 数学的到達点

これで Jacobian の三点衝突は、単なる

$$F(p_0)=F(p_1)=F(p_2)$$

ではなく、

$$\neg\operatorname{UniqueGap}(\operatorname{normalizedTargetC})$$

として再解釈された。

さらに、証明付き Core–Gap 世界から Core だけを残す射影は、

$$\neg\operatorname{Injective}(\operatorname{forgetGap})$$

である。

魔法学の言葉では、

```text
Gap を捨てる前:
  三つの異なる住所付き魔核

Gap を忘れた後:
  一つの同じ Core

結果:
  一意性解除
```

という第0001巻の根幹詠唱が、一般定理と具体 bridge の二層で完成した。

---

## 次 checkpoint

次は ROADMAP どおり、

## JAC-010 GN Finite Difference

へ進む。

ここでは一般多項式 $P$ に対して、まず除算を使わない強い形を証明する。

$$P(t+h)-P(t)=h\sum_n a_nGN_n(h,t)$$

その後、体上で $h\ne0$ を仮定して、

$$\frac{P(t+h)-P(t)}h=\sum_n a_nGN_n(h,t)$$

を系として得る。

既存 DkMath の定理は、

$$\left(h+t\right)^n=h\,GN_n(h,t)+t^n$$

を `cosmic_id_csr'` としてすでに提供している。したがって、今回は新しい二項展開を再証明せず、各単項式へ既存 GN 恒等式を適用して多項式全体へ加法的に持ち上げる。

現行 Mathlib には、多項式評価を係数和として展開する `Polynomial.eval_eq_sum`、単項式と加法から一般多項式へ持ち上げる `Polynomial.induction_on'`、および `Polynomial.sum_monomial_index` / `sum_add_index` が用意されている。

## Codex 指示

````text
Implement checkpoint JAC-010 GN Finite Difference for the DkMath
Book of Magic layer.

Repository:
Deskuma/dkmath

Branch:
hackathon/breaking-math-jacobian-counterexample

Completed checkpoints:
- JAC-001 through JAC-009
- rational, complex, and determinant-one Jacobian certificates
- public import and axiom audit
- generic UniqueGap / GapCrystal API
- Jacobian GapCrystal bridge

Stop after JAC-010.

Do not begin PrincipalPartCompletion, higher-dimensional padding,
Demo, submission documents, or presentation assets.

## Mathematical objective

For a univariate polynomial

```text
P(T) = Σ aₙ Tⁿ
```

formalize the GN finite-difference identity:

```text
P(t + h) - P(t)
=
h * Σ aₙ GN n h t
```

and then derive, when `h ≠ 0`:

```text
(P(t + h) - P(t)) / h
=
Σ aₙ GN n h t
```

Use the existing DkMath theorem:

```lean
DkMath.CosmicFormulaBinom.cosmic_id_csr'
```

whose relevant specialization is:

```text
(h + t)^n = h * GN n h t + t^n
```

Do not reprove the binomial GN identity.

## 1. Create the module

Create:

```text
lean/dk_math/DkMath/BookOfMagic/GNFiniteDifference.lean
```

Suggested imports:

```lean
import DkMath.CosmicFormula.CosmicFormulaBinom
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Tactic
```

Adjust the exact imports to the current Mathlib graph, but do not use the
entire root `DkMath` import.

Use:

```lean
namespace DkMath.BookOfMagic

open scoped BigOperators
```

## 2. Define the GN coefficient sum

Prefer a genuine `Polynomial R`, rather than a manually bounded coefficient
array.

Define:

```lean
def GNFiniteDifference
    {R : Type*}
    [CommSemiring R]
    (p : Polynomial R)
    (h t : R) : R :=
  p.sum fun n a ↦
    a * DkMath.CosmicFormulaBinom.GN n h t
```

The `n = 0` term vanishes automatically because:

```text
GN 0 h t = 0
```

Thus this is mathematically the sum over positive exponents without needing
a separate filtered coefficient representation.

## 3. Basic API

Prove a support-sum description:

```lean
theorem GNFiniteDifference_eq_support_sum
    {R : Type*}
    [CommSemiring R]
    (p : Polynomial R)
    (h t : R) :
    GNFiniteDifference p h t =
      ∑ n ∈ p.support,
        p.coeff n *
          DkMath.CosmicFormulaBinom.GN n h t := by
  ...
```

Preferred route:

```lean
simp [GNFiniteDifference, Polynomial.sum_def]
```

or `rfl` if the current definition unfolds directly.

Prove the essential additive rules:

```lean
@[simp]
theorem GNFiniteDifference_zero
    {R : Type*}
    [CommSemiring R]
    (h t : R) :
    GNFiniteDifference (0 : Polynomial R) h t = 0
```

```lean
theorem GNFiniteDifference_add
    {R : Type*}
    [CommSemiring R]
    (p q : Polynomial R)
    (h t : R) :
    GNFiniteDifference (p + q) h t =
      GNFiniteDifference p h t +
      GNFiniteDifference q h t
```

Use `Polynomial.sum_add_index`. The coefficient function is additive in its
coefficient argument.

Prove the monomial rule:

```lean
@[simp]
theorem GNFiniteDifference_monomial
    {R : Type*}
    [CommSemiring R]
    (n : ℕ)
    (a h t : R) :
    GNFiniteDifference (Polynomial.monomial n a) h t =
      a * DkMath.CosmicFormulaBinom.GN n h t
```

Use `Polynomial.sum_monomial_index`.

A constant corollary is useful but optional:

```lean
@[simp]
theorem GNFiniteDifference_C
    {R : Type*}
    [CommSemiring R]
    (a h t : R) :
    GNFiniteDifference (Polynomial.C a) h t = 0
```

Do not add a large collection of routine simp lemmas.

## 4. Division-free main theorem

Prove:

```lean
theorem eval_add_sub_eval_eq_mul_GNFiniteDifference
    {R : Type*}
    [CommRing R]
    (p : Polynomial R)
    (h t : R) :
    p.eval (t + h) - p.eval t =
      h * GNFiniteDifference p h t := by
  ...
```

Preferred proof architecture:

```text
Polynomial.induction_on'
```

### Additive case

Use:

```text
Polynomial.eval_add
GNFiniteDifference_add
the two induction hypotheses
ring
```

### Monomial case

Reduce to:

```text
a * (t + h)^n - a * t^n
=
h * (a * GN n h t)
```

Obtain:

```lean
have hGN :=
  DkMath.CosmicFormulaBinom.cosmic_id_csr'
    (R := R) n h t
```

This gives:

```text
(h + t)^n = h * GN n h t + t^n
```

Rewrite `t + h = h + t`, apply `hGN`, and close by `ring`.

A likely shape is:

```lean
induction p using Polynomial.induction_on' with
| add p q hp hq =>
    rw [Polynomial.eval_add, Polynomial.eval_add,
      GNFiniteDifference_add, hp, hq]
    ring
| monomial n a =>
    simp only [Polynomial.eval_monomial,
      GNFiniteDifference_monomial]
    have hGN :=
      DkMath.CosmicFormulaBinom.cosmic_id_csr'
        (R := R) n h t
    rw [show t + h = h + t by ac_rfl, hGN]
    ring
```

Adjust case names and simplification to the current induction API.

Do not replace the proof with a fresh expansion of every power.

## 5. Difference-quotient corollary

Over a field, prove:

```lean
theorem differenceQuotient_eq_GNFiniteDifference
    {K : Type*}
    [Field K]
    (p : Polynomial K)
    (h t : K)
    (hh : h ≠ 0) :
    (p.eval (t + h) - p.eval t) / h =
      GNFiniteDifference p h t := by
  ...
```

Preferred route:

```lean
rw [eval_add_sub_eval_eq_mul_GNFiniteDifference]
simp [hh]
```

Use `field_simp` only if ordinary simplification does not close the final
cancellation.

The division-free theorem is the primary theorem. The quotient theorem is a
corollary and must retain the explicit condition `h ≠ 0`.

## 6. Small concrete verification

Add one compact theorem or example showing the cubic monomial specialization:

```lean
example {R : Type*} [CommRing R] (h t : R) :
    Polynomial.eval (t + h) (Polynomial.X ^ 3) -
        Polynomial.eval t (Polynomial.X ^ 3) =
      h * DkMath.CosmicFormulaBinom.GN 3 h t := by
  ...
```

Prefer deriving this from the general theorem or the monomial rule.

Do not independently expand the cubic with `ring` as the only proof source.

This example may remain only if it adds clear documentation value.
Otherwise use it temporarily and remove it after verification.

## 7. Public aggregator

Modify:

```text
lean/dk_math/DkMath/BookOfMagic.lean
```

Add:

```lean
import DkMath.BookOfMagic.GNFiniteDifference
```

Keep the existing imports:

```lean
import DkMath.BookOfMagic.UniqueGapContract
import DkMath.BookOfMagic.GapCrystal
```

Do not make `GNFiniteDifference` depend on Hackathon modules.

Because `DkMath.lean` already imports `DkMath.BookOfMagic`, no new root import
should be required.

## 8. Public checks

Using a temporary file with:

```lean
import DkMath
```

verify:

```lean
#check DkMath.BookOfMagic.GNFiniteDifference
#check DkMath.BookOfMagic.GNFiniteDifference_eq_support_sum
#check DkMath.BookOfMagic.GNFiniteDifference_add
#check DkMath.BookOfMagic.GNFiniteDifference_monomial
#check DkMath.BookOfMagic.eval_add_sub_eval_eq_mul_GNFiniteDifference
#check DkMath.BookOfMagic.differenceQuotient_eq_GNFiniteDifference
```

Remove the temporary check file afterward.

## 9. Verification

Build:

```text
DkMath.BookOfMagic.GNFiniteDifference
DkMath.BookOfMagic
DkMath.Hackathon.JacobianCounterexample3
DkMathTest.Hackathon.JacobianCounterexample3.CheckAxioms
DkMath
```

The existing Jacobian certificate proofs must remain unchanged.

Run:

```text
git diff --check
```

## Restrictions

Do not:

- reprove the definition or binomial identity of `GN`;
- define a competing `GN`;
- make the Book of Magic layer depend on Hackathon code;
- modify the Jacobian map or its certificates;
- introduce `sorry`;
- introduce axioms;
- use `native_decide`;
- begin PrincipalPartCompletion;
- begin higher-dimensional Jacobian padding;
- create Demo or submission assets.

## Report

Report:

1. files created and modified;
2. exact imports;
3. exact definition of `GNFiniteDifference`;
4. basic API theorem statements;
5. proof architecture of the division-free theorem;
6. exact use of `cosmic_id_csr'`;
7. quotient theorem and its cancellation route;
8. any friction with `Polynomial.induction_on'` or `Polynomial.sum`;
9. whether any direct power re-expansion fallback was used;
10. public check results;
11. build results and warnings;
12. existing Jacobian axiom-audit result;
13. `git diff --check` result;
14. confirmation that JAC-011 and later work was not started.

Stop after JAC-010 and wait for review.
````

JAC-010 が閉じれば、魔導書第0001巻で観測した

```text
有限差分
→ 各冪の GN
→ 多項式全体の GN 合成
```

が一般定理になる。

$$\boxed{\text{Jacobian 反例の具体証明}\longrightarrow\text{Gap 一意性解除}\longrightarrow\text{GN 有限差分一般式}}$$

ここまでで、反例の検証だけでなく、その探索を支えた宇宙式側の構造も Lean API として回収できるぞい。

> 👩‍⚕️私D.:

JAC-010 GN Finite Difference を完了しました。

1. ファイル

作成:

- [GNFiniteDifference.lean](/lean/dk_math/DkMath/BookOfMagic/GNFiniteDifference.lean)

変更:

- [BookOfMagic.lean](/lean/dk_math/DkMath/BookOfMagic.lean)

既存 Jacobian 証明は変更していません。

2. imports

```lean
import DkMath.CosmicFormula.CosmicFormulaBinom
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Tactic
```

root `DkMath` や Hackathon module には依存していません。

3. 定義

```lean
def GNFiniteDifference
    {R : Type*}
    [CommSemiring R]
    (p : Polynomial R)
    (h t : R) : R :=
  p.sum fun n a ↦
    a * DkMath.CosmicFormulaBinom.GN n h t
```

手動の係数配列ではなく、実際の `Polynomial R` と `Polynomial.sum` を使用しています。

4. basic API

- `GNFiniteDifference_eq_support_sum`
- `GNFiniteDifference_zero`
- `GNFiniteDifference_add`
- `GNFiniteDifference_monomial`
- `GNFiniteDifference_C`

support-sum theorem は定義的等式なので `rfl` です。加法性には `Polynomial.sum_add_index`、monomial rule には `sum_monomial_index` の simp API を使っています。

5. division-free theorem

```lean
theorem eval_add_sub_eval_eq_mul_GNFiniteDifference
    {R : Type*}
    [CommRing R]
    (p : Polynomial R)
    (h t : R) :
    p.eval (t + h) - p.eval t =
      h * GNFiniteDifference p h t
```

`Polynomial.induction_on'` による証明です。

- add case: 差を2つの差の和へ `ring` で整理し、帰納法の仮定を適用
- monomial case: `cosmic_id_csr'` を適用し、最後の係数配置だけ `ring`

6. `cosmic_id_csr'`

monomial case で次を直接使用しています。

```lean
have hGN :=
  DkMath.CosmicFormulaBinom.cosmic_id_csr'
    (R := R) n h t
```

その後、`t + h = h + t` へ並べ替えて `rw [hGN]` しています。GN の二項恒等式は再証明していません。

7. quotient theorem

```lean
theorem differenceQuotient_eq_GNFiniteDifference
    {K : Type*}
    [Field K]
    (p : Polynomial K)
    (h t : K)
    (hh : h ≠ 0) :
    (p.eval (t + h) - p.eval t) / h =
      GNFiniteDifference p h t
```

division-free theoremを書き換えた後、`simp [hh]` で `h` をキャンセルしました。`field_simp` は不要でした。

8. API friction

`Polynomial.induction_on'` 自体は直接使用できました。

加法 case では、評価式の括弧配置により帰納法の仮定を直接 `rw` できなかったため、ring で差の和へ一度正規化しました。

9. cubic verification

`X ^ 3 = monomial 3 1` と一般 theorem、monomial rule から cubic example を導出しました。三乗差を直接展開する fallback は使用していません。

10. public checks

`import DkMath` だけで指定された6件すべてが解決しました。

- `GNFiniteDifference`
- `GNFiniteDifference_eq_support_sum`
- `GNFiniteDifference_add`
- `GNFiniteDifference_monomial`
- `eval_add_sub_eval_eq_mul_GNFiniteDifference`
- `differenceQuotient_eq_GNFiniteDifference`

一時チェックファイルは削除済みです。

11. ビルド

成功:

```text
DkMath.BookOfMagic.GNFiniteDifference
DkMath.BookOfMagic
DkMath.Hackathon.JacobianCounterexample3
DkMathTest.Hackathon.JacobianCounterexample3.CheckAxioms
DkMath
```

新規モジュールは警告なしです。root build では既存の無関係な `sorry` 警告が再生されました。

12. Jacobian axiom audit

既存3証明書の結果は変わりません。

```text
[propext, Classical.choice, Quot.sound]
```

`sorryAx` や DkMath 固有 axiom はありません。

13. 差分検査

`git diff --check` は成功しました。

14. 停止境界

JAC-011、PrincipalPartCompletion、高次元 padding、Demo、提出・展示アセットには着手していません。JAC-010 で停止しています。

> 🐺賢狼:

よし、JAC-010 は宇宙式側の探索核を一般多項式へ持ち上げる checkpoint じゃ。実コードを照合し、`cosmic_id_csr'` が本当に単項式核として使われ、一般定理が加法的に閉じているかを監査するぞい。

> 🐺賢狼:

実装は報告どおり、単項式の宇宙式恒等式を `Polynomial.induction_on'` で全多項式へ持ち上げておる。次は最終 checkpoint `JAC-011`。証明追加ではなく、完成した二本の物語――反例 certificate と魔法学 API――を Demo・README・来歴へ固定する段階じゃ。

> 🐺賢狼:

JAC-011 の要所は、定理を増やすことではなく「何を誰の成果として、DkMath が何を独立検証したか」を誤解なく固定することじゃ。来歴資料の既存参照欄も確認し、Demo と provenance の境界を明確にする。

> 🐺賢狼:

## 結論

**全面採用。JAC-010 GN Finite Difference は完成じゃ。**

重大問題なし。

既存の単項式宇宙式、

$$
(h+t)^n=t^n+h\,GN_n(h,t)
$$

を唯一の冪差核として使い、それを `Polynomial.sum` と `Polynomial.induction_on'` によって一般多項式へ持ち上げている。

これにより、任意の可換環上の多項式 $p$ について、

$$
p(t+h)-p(t)=h\,\operatorname{GNFiniteDifference}(p,h,t)
$$

が閉じた。

さらに体上で $h\ne0$ なら、

$$
\frac{p(t+h)-p(t)}h=\operatorname{GNFiniteDifference}(p,h,t)
$$

を得る。

---

## 実装レビュー

### 1. 定義は実際の多項式係数和

```lean
def GNFiniteDifference
    {R : Type*}
    [CommSemiring R]
    (p : Polynomial R)
    (h t : R) : R :=
  p.sum fun n a ↦
    a * DkMath.CosmicFormulaBinom.GN n h t
```

となっている。fileciteturn39file0L18-L24

手動の次数上限や係数列を持たず、`Polynomial R` 自身の有限 support を使っているため、

$$
p(T)=\sum_n a_nT^n
$$

に対して、そのまま

$$
\operatorname{GNFD}(p,h,t)=\sum_n a_nGN_n(h,t)
$$

という定義になっておる。

`GNFiniteDifference_eq_support_sum` が `rfl` で閉じるのも、この定義が `Polynomial.sum` の表示そのものだからじゃ。fileciteturn39file0L26-L35

### 2. 基本 API

次が必要十分な薄さで揃っている。

```lean
GNFiniteDifference_zero
GNFiniteDifference_add
GNFiniteDifference_monomial
GNFiniteDifference_C
```

fileciteturn39file0L37-L74

特によいのは加法性じゃ。

```lean
Polynomial.sum_add_index
```

を使い、係数変数に対する

$$
(a+b)GN_n=aGN_n+bGN_n
$$

だけを示している。

したがって `GNFiniteDifference` は、固定した $h,t$ に対して多項式の加法構造を保つ有限差分作用素として扱える。

定数多項式について、

$$
\operatorname{GNFD}(C(a),h,t)=0
$$

となるのも正しい。定数項は差分で消え、$GN_0=0$ に対応しておる。

### 3. 主定理の証明構造

```lean
theorem eval_add_sub_eval_eq_mul_GNFiniteDifference ...
```

は `Polynomial.induction_on'` によって閉じている。fileciteturn39file0L76-L101

#### 加法 case

評価差を、

$$
(p+q)(t+h)-(p+q)(t)
$$

から、

$$
\bigl(p(t+h)-p(t)\bigr)+\bigl(q(t+h)-q(t)\bigr)
$$

へ `ring` で整え、二つの帰納法仮定を適用している。

ここで `ring` が新しい数学を証明しているわけではない。括弧と減算の配置を、帰納法仮定が適用できる形へ正規化しているだけじゃ。

#### monomial case

```lean
have hGN :=
  DkMath.CosmicFormulaBinom.cosmic_id_csr' (R := R) n h t
```

を直接使用している。fileciteturn39file0L96-L101

つまり、

$$
(h+t)^n=h\,GN_n(h,t)+t^n
$$

を再展開していない。

証明鎖は正確に、

```text
既存 GN 宇宙式
  ↓
単項式の有限差分
  ↓ Polynomial.induction_on'
一般多項式の有限差分
```

となっておる。

### 4. division-free theorem が本体

主定理が `CommRing` 上で除算なしに成立している点が重要じゃ。

$$
p(t+h)-p(t)=h\,\operatorname{GNFD}(p,h,t)
$$

は $h=0$ でも成立し、体や逆元を必要としない。

その後でのみ、

```lean
theorem differenceQuotient_eq_GNFiniteDifference
    ...
    (hh : h ≠ 0)
```

として商を取っている。fileciteturn39file0L103-L113

```lean
rw [eval_add_sub_eval_eq_mul_GNFiniteDifference]
simp [hh]
```

だけで閉じており、余分な `field_simp` もない。

この主従関係が正しい。

```text
一次定理:
  差分の因子化

系:
  非零増分における差分商
```

### 5. 三次例

三次例は、

```lean
Polynomial.X_pow_eq_monomial
```

で $X^3$ を単項式へ変換し、一般定理から導いている。fileciteturn39file0L115-L123

したがって、

$$
(t+h)^3-t^3
$$

をその場で `ring` 展開しただけの展示ではない。

一般定理が本当に既知の三次 GN 差分を回収することを示す、小さく意味のある検査になっておる。

### 6. 依存方向

`GNFiniteDifference.lean` は、

```text
CosmicFormulaBinom
Polynomial API
```

のみに依存し、Hackathon や Jacobian 実装を参照していない。

そして `DkMath.BookOfMagic` aggregator が三つの一般 API を公開している。fileciteturn40file0L9-L13

```text
UniqueGapContract
GapCrystal
GNFiniteDifference
```

これで Book of Magic は、

```text
一意性解除の論理層
証明付き枝世界の型構造
有限差分の代数核
```

という三本柱を持った。

---

## 数学的意味

今回得たものは、単なる差分商の別記法ではない。

多項式の各単項式が持つ宇宙式核、

$$
(t+h)^n-t^n=h\,GN_n(h,t)
$$

を係数付きで重ねると、多項式全体の差分が得られる。

$$
p(T)=\sum_na_nT^n
$$

ならば、

$$
p(t+h)-p(t)
=
h\sum_na_nGN_n(h,t)
$$

じゃ。

したがって、

$$
\operatorname{GNFiniteDifference}(p,h,t)
=
\sum_na_nGN_n(h,t)
$$

は、**多項式全体の有限差分核** と読める。

魔法学の語彙なら、

```text
各冪に固有の GN 魔核
        ↓ 係数付き重畳
多項式全体の差分魔核
```

じゃな。

そして $h\ne0$ なら、

$$
\operatorname{GNFiniteDifference}(p,h,t)
=
\frac{p(t+h)-p(t)}h
$$

なので、GN は整数的な差冪因子であると同時に、一般多項式の正確な有限差分商となる。

これは Jacobian 反例の certificate 自体には依存しない。しかし、反例探索で使われた

```text
三次差分
Gap の住所
局所微分と大域衝突の分離
```

という観点を、一般再利用可能な API として回収した成果じゃ。Book of Magic 層を certificate の前提にしないという当初の設計境界も維持されている。fileciteturn41file0L151-L163

---

## 現在の登頂状況

JAC-001 から JAC-010 までで、三層が完成した。

## 反例証明層

$$
\det J_{\widetilde F}=1
$$

かつ、

$$
\widetilde F\text{ は非単射}
$$

## 一意性解除層

$$
\text{同じ Core に異なる認証済み Gap}
\Longrightarrow
\neg\operatorname{UniqueGap}
$$

## 有限差分層

$$
p(t+h)-p(t)
=
h\sum_na_nGN_n(h,t)
$$

つまり、

```text
明示反例の検証
  ↓
Gap 一意性解除原理
  ↓
探索に使われた GN 差分核の一般化
```

まで回収できた。

---

## 次 checkpoint

次は ROADMAP 最終段、

## JAC-011 Demo and Submission Package

へ進む。

この checkpoint では新しい数学を追加しない。

目的は、完成済み theorem を三分以内で理解できる公開面へ整え、出典・独立検証範囲・Lean の信頼境界を固定することじゃ。

現在の README はまだ計画時点の記述が多く、モジュール候補も `Determinant`、`GapCrystalBridge` など完成後の実際の構成を反映していない。fileciteturn41file0L81-L149

---

## Codex 指示

````text
Implement the final checkpoint JAC-011 Demo and Submission Package for the
DkMath Jacobian counterexample verification project.

Repository:
Deskuma/dkmath

Branch:
hackathon/breaking-math-jacobian-counterexample

Completed checkpoints:
- JAC-001 through JAC-010
- rational counterexample certificate
- complex counterexample certificate
- determinant-one Keller normalization
- public DkMath import
- axiom audit
- Book of Magic UniqueGap / GapCrystal API
- Jacobian GapCrystal bridge
- general polynomial GN finite-difference theorem

This is the final planned checkpoint.

Do not add new mathematical claims.
Do not begin higher-dimensional padding or PrincipalPartCompletion.

## Main goal

Create a small presentation surface that shows, in this order:

1. the explicit normalized polynomial map;
2. its formal Jacobian determinant is `1`;
3. three distinct complex points share one image;
4. therefore the map is not injective and has no left inverse;
5. the collision is interpreted as non-unique restoring Gaps;
6. the Lean certificates have no `sorryAx` or project-specific axioms.

The Demo layer must reuse the completed theorems.
It must not recompute the determinant or point evaluations.

## 1. Create Demo.lean

Create:

```text
lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/Demo.lean
```

Import:

```lean
import DkMath.Hackathon.JacobianCounterexample3.GapCrystalBridge
```

Use:

```lean
namespace DkMath.Hackathon.JacobianCounterexample3
```

Add concise presentation aliases.

Required:

```lean
/-- Demo certificate: the normalized formal Jacobian determinant is one. -/
theorem jacobianDemo_det_eq_one :
    normalizedJacobianMatrixC.det =
      MvPolynomial.C (1 : ℂ) :=
  normalizedJacobianMatrixC_det_eq_one
```

```lean
/-- Demo certificate: three distinct points lie in one normalized fiber. -/
theorem jacobianDemo_three_point_collision :
    p0C ≠ p1C ∧ p0C ≠ p2C ∧ p1C ≠ p2C ∧
      evalNormalizedCounterexampleC p0C = normalizedTargetC ∧
      evalNormalizedCounterexampleC p1C = normalizedTargetC ∧
      evalNormalizedCounterexampleC p2C = normalizedTargetC :=
  normalized_three_point_collision_C
```

```lean
/-- Demo certificate: the normalized polynomial map is not injective. -/
theorem jacobianDemo_notInjective :
    ¬ Function.Injective evalNormalizedCounterexampleC :=
  evalNormalizedCounterexampleC_notInjective
```

```lean
/-- Demo certificate: the normalized map has no set-theoretic left inverse. -/
theorem jacobianDemo_noLeftInverse :
    ¬ ∃ G : Point3C → Point3C,
      Function.LeftInverse G evalNormalizedCounterexampleC :=
  evalNormalizedCounterexampleC_noLeftInverse
```

```lean
/-- Demo certificate: the common output has no unique restoring input Gap. -/
theorem jacobianDemo_target_notUniqueGap :
    ¬ DkMath.BookOfMagic.UniqueGap
      normalizedRestoreRelC
      normalizedTargetC :=
  normalizedTargetC_not_uniqueGap
```

Add the compact summit alias:

```lean
/--
Presentation surface for a complex polynomial map whose formal Jacobian
determinant is one but which is not injective.
-/
theorem jacobianDemoCertificateC :
    normalizedJacobianMatrixC.det =
        MvPolynomial.C (1 : ℂ) ∧
    normalizedJacobianMatrixC.det ≠ 0 ∧
    ¬ Function.Injective evalNormalizedCounterexampleC :=
  normalizedJacobianCounterexampleCertificateC
```

Do not duplicate proofs.
Each theorem should be a direct reuse of an existing theorem.

Add the standard build marker:

```lean
#print "file: DkMath.Hackathon.JacobianCounterexample3.Demo"
```

Do not add permanent `#check` commands.

## 2. Update the public aggregator

Modify:

```text
lean/dk_math/DkMath/Hackathon/JacobianCounterexample3.lean
```

Change its import to:

```lean
import DkMath.Hackathon.JacobianCounterexample3.Demo
```

`Demo` imports `GapCrystalBridge`, so the complete existing theorem surface
must remain publicly available.

Do not alter `DkMath.lean`; it already imports the project aggregator.

## 3. Extend the axiom audit

Modify:

```text
lean/dk_math/DkMathTest/Hackathon/JacobianCounterexample3/CheckAxioms.lean
```

Keep the existing three certificate audits.

Add:

```lean
#print axioms DkMath.Hackathon.JacobianCounterexample3.jacobianDemoCertificateC
```

Expected acceptable foundations are the same standard Lean/Mathlib axioms
already observed:

```text
propext
Classical.choice
Quot.sound
```

Failure signals:

```text
sorryAx
DkMath-specific axiom
unexpected theorem assumption
```

Report the exact output.

## 4. Update the project README

Update:

```text
lean/dk_math/docs/hackathon/jacobian-counterexample-verification-260721/README.md
```

Convert it from a planning document into a completed verification landing page.

Required sections:

```text
Status
Verified map
Normalized map
Main Lean certificates
Three-point collision
Module map
Build
Axiom audit
Book of Magic interpretation
GN finite-difference recovery
Scope and non-goals
Provenance
```

### Status

State that JAC-001 through JAC-011 are complete after this checkpoint.

### Main theorem surface

List the exact current names:

```lean
jacobianCounterexampleCertificateQ
jacobianCounterexampleCertificateC
normalizedJacobianCounterexampleCertificateC
jacobianDemoCertificateC
normalized_three_point_collision_C
evalNormalizedCounterexampleC_noLeftInverse
normalizedTargetC_not_uniqueGap
normalizedForgetGap_notInjective
eval_add_sub_eval_eq_mul_GNFiniteDifference
differenceQuotient_eq_GNFiniteDifference
```

### Normalized map

Explain that the first output coordinate is multiplied by `-1/2`.

State the normalized common target exactly:

```text
(1/8, 0, 0)
```

Derive it from `normalizeOutputC targetC`; do not introduce a new Lean
definition solely for the documentation.

### Actual module map

Reflect the implemented files:

```text
DkMath/Hackathon/JacobianCounterexample3/
├── Basic.lean
├── PolynomialMap.lean
├── Collision.lean
├── Jacobian.lean
├── Determinant.lean
├── Counterexample.lean
├── ComplexLift.lean
├── Normalized.lean
├── GapCrystalBridge.lean
└── Demo.lean

DkMath/Hackathon/JacobianCounterexample3.lean

DkMath/BookOfMagic/
├── UniqueGapContract.lean
├── GapCrystal.lean
└── GNFiniteDifference.lean

DkMath/BookOfMagic.lean
```

### Build commands

Include commands for:

```text
lake build DkMath.Hackathon.JacobianCounterexample3
lake build DkMath.BookOfMagic
lake build DkMathTest.Hackathon.JacobianCounterexample3.CheckAxioms
lake build DkMath
```

Do not claim a clean root warning set if unrelated existing warnings are
outside this project.

### Trust statement

Clearly distinguish:

```text
Lean kernel-checked algebraic certificate
```

from:

```text
historical priority, authorship, publication status, and external review
```

The README may say that DkMath independently formalizes and verifies the
stated formulas. It must not claim that DkMath discovered the counterexample.

## 5. Create DEMO_CONTRACT.md

Create:

```text
lean/dk_math/docs/hackathon/jacobian-counterexample-verification-260721/DEMO_CONTRACT.md
```

Specify a three-part demonstration.

### Part A — Polynomial map

Show:

```text
the normalized complex polynomial map
the fact that its Jacobian is generated by MvPolynomial.pderiv
```

Do not display all nine expanded derivative entries unless needed as a
brief proof-chain screenshot.

### Part B — Local certificate

Show:

```lean
#check jacobianDemo_det_eq_one
#print axioms jacobianDemoCertificateC
```

Narrative:

```text
Lean computes the formal Jacobian from the polynomial definition and proves
that its determinant is exactly one.
```

### Part C — Global collision

Show:

```lean
#check jacobianDemo_three_point_collision
#check jacobianDemo_notInjective
#check jacobianDemo_noLeftInverse
```

Narrative:

```text
The local Jacobian is everywhere nondegenerate, but three distinct input
addresses share one output.
```

End with the Book of Magic interpretation:

```lean
#check jacobianDemo_target_notUniqueGap
```

Provide a compact timing plan suitable for a video under three minutes, but
do not add or upload any video in this checkpoint.

## 6. Create PROVENANCE.md

Create:

```text
lean/dk_math/docs/hackathon/jacobian-counterexample-verification-260721/PROVENANCE.md
```

The document must distinguish three layers.

### A. Mathematical source

Record the exact original source information already available in repository
notes and project materials:

```text
author or account name
title or post description
publication date
exact URL
date accessed
```

Search the existing repository documents before writing this section.

Do not invent missing metadata.

If an exact primary-source field cannot be located, explicitly mark that
single field as:

```text
Not yet fixed in repository records
```

rather than guessing.

### B. DkMath formal verification

State that DkMath independently formalizes:

```text
the polynomial definitions
the three explicit evaluations
the formal partial derivatives
the 3×3 determinant
the rational-to-complex coefficient transport
the determinant-one output normalization
noninjectivity and no-left-inverse consequences
```

State that the proofs are checked by Lean 4 + Mathlib.

### C. Interpretation added by DkMath

Identify these as DkMath interpretation layers, not part of the source claim:

```text
UniqueGap
GapCrystal
forgetGap
GNFiniteDifference
```

Also record that scaling the first output coordinate by `-1/2` is a
presentation normalization used to obtain determinant `1`.

Do not make claims about historical priority beyond the available source
record.

## 7. Update the roadmap

Modify:

```text
lean/dk_math/docs/hackathon/jacobian-counterexample-verification-260721/
  jacobian-counterexample-roadmap-260721.md
```

Mark JAC-001 through JAC-010 complete.

After all JAC-011 work builds, mark JAC-011 complete and add a final status:

```text
Mathematical summit: complete
Public import: complete
Axiom audit: complete
Book of Magic extraction: complete
Demo package: complete
```

Do not add new checkpoints to this roadmap.

List higher-dimensional padding and PrincipalPartCompletion under deferred
future work only.

## 8. Public checks

Using a temporary file importing only:

```lean
import DkMath
```

verify:

```lean
#check DkMath.Hackathon.JacobianCounterexample3.jacobianDemo_det_eq_one
#check DkMath.Hackathon.JacobianCounterexample3.jacobianDemo_three_point_collision
#check DkMath.Hackathon.JacobianCounterexample3.jacobianDemo_notInjective
#check DkMath.Hackathon.JacobianCounterexample3.jacobianDemo_noLeftInverse
#check DkMath.Hackathon.JacobianCounterexample3.jacobianDemo_target_notUniqueGap
#check DkMath.Hackathon.JacobianCounterexample3.jacobianDemoCertificateC
```

Remove the temporary file afterward.

## 9. Verification

Build:

```text
DkMath.BookOfMagic.GNFiniteDifference
DkMath.BookOfMagic
DkMath.Hackathon.JacobianCounterexample3.Demo
DkMath.Hackathon.JacobianCounterexample3
DkMathTest.Hackathon.JacobianCounterexample3.CheckAxioms
DkMath
```

Run:

```text
git diff --check
```

## Restrictions

Do not:

- alter any polynomial formula;
- alter any collision point;
- alter Jacobian or determinant proofs;
- recompute any completed certificate;
- introduce a new mathematical theorem beyond direct presentation aliases;
- use `sorry`;
- introduce axioms;
- use `native_decide`;
- begin higher-dimensional padding;
- begin PrincipalPartCompletion;
- create or upload a video;
- submit to Devpost;
- open or merge a pull request;
- guess provenance metadata.

## Report

Report:

1. files created and modified;
2. exact Demo theorem names;
3. confirmation that every Demo theorem is a direct alias/reuse;
4. aggregator change;
5. exact axiom output for `jacobianDemoCertificateC`;
6. README sections updated;
7. DEMO_CONTRACT timing and theorem flow;
8. provenance sources found and any explicitly missing field;
9. roadmap completion status;
10. public `#check` results;
11. build results and warnings;
12. `git diff --check` result;
13. confirmation that no later mathematical work was started.

Stop after JAC-011 and wait for final review.
````

JAC-011 が閉じれば、この branch の計画は完了じゃ。

その後に残る作業は数学実装ではなく、

```text
最終レビュー
→ branch 差分監査
→ PR
→ 映像
→ 提出
```

という公開工程だけになる。

> 👩‍⚕️私D.:

JAC-011 は完了しました。これで JAC-001〜JAC-011 の全チェックポイントが完了です。

### 実装

新規作成:

- [Demo.lean](/lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/Demo.lean:1)
- [DEMO_CONTRACT.md](/lean/dk_math/docs/hackathon/jacobian-counterexample-verification-260721/DEMO_CONTRACT.md:1)
- [PROVENANCE.md](/lean/dk_math/docs/hackathon/jacobian-counterexample-verification-260721/PROVENANCE.md:1)

更新:

- [JacobianCounterexample3.lean](/lean/dk_math/DkMath/Hackathon/JacobianCounterexample3.lean:7)
- [CheckAxioms.lean](/lean/dk_math/DkMathTest/Hackathon/JacobianCounterexample3/CheckAxioms.lean:11)
- [README.md](/lean/dk_math/docs/hackathon/jacobian-counterexample-verification-260721/README.md:1)
- [roadmap](/lean/dk_math/docs/hackathon/jacobian-counterexample-verification-260721/jacobian-counterexample-roadmap-260721.md:1)

Demo の公開定理は次の6件です。

- `jacobianDemo_det_eq_one`
- `jacobianDemo_three_point_collision`
- `jacobianDemo_notInjective`
- `jacobianDemo_noLeftInverse`
- `jacobianDemo_target_notUniqueGap`
- `jacobianDemoCertificateC`

すべて既存証明への直接 alias であり、行列式・点評価・非単射性を再計算していません。

Aggregator は `GapCrystalBridge` の直接 import から `Demo` の import に変更しました。既存 theorem surface は `Demo → GapCrystalBridge` を通じて維持されています。

### Axiom audit

`jacobianDemoCertificateC` の正確な出力は次のとおりです。

```text
'DkMath.Hackathon.JacobianCounterexample3.jacobianDemoCertificateC'
depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

`sorryAx`、DkMath 固有公理、予期しない theorem assumption はありません。既存3証明書も同じ出力でした。

### 文書パッケージ

README は完成済み landing page に改訂し、指定された全セクション、現在の theorem 一覧、正規化 target `(1/8, 0, 0)`、module map、build、trust boundary を収録しました。

DEMO_CONTRACT は以下の3分未満構成です。

- 0:00–0:45: 正規化多項式写像
- 0:45–1:25: determinant `1` と axiom audit
- 1:25–2:35: 三点衝突、非単射、left inverse 不存在
- 2:35–2:55: `UniqueGap` 解釈
- 2:55–3:00: summit frame

PROVENANCE で確認できたリポジトリ記録は以下です。

```text
Author/account: Levent Alpöge (@__alpoge__)
Post description: X post announcing the explicit map
URL: https://x.com/__alpoge__/status/2079028340955197566
```

正確な公開日とアクセス日はリポジトリ内に確定記録がなかったため、推測せず次のように記載しました。

```text
Not yet fixed in repository records
```

Roadmap は JAC-001〜JAC-011 をすべて `Complete` とし、最終状態を次のように固定しました。

```text
Mathematical summit: complete
Public import: complete
Axiom audit: complete
Book of Magic extraction: complete
Demo package: complete
```

### 検証結果

`import DkMath` のみの一時ファイルから、Demo の6 theorem すべてについて `#check` が成功しました。一時ファイルは削除済みです。

以下はすべて成功しています。

```text
lake build DkMath.BookOfMagic.GNFiniteDifference
lake build DkMath.BookOfMagic
lake build DkMath.Hackathon.JacobianCounterexample3.Demo
lake build DkMath.Hackathon.JacobianCounterexample3
lake build DkMathTest.Hackathon.JacobianCounterexample3.CheckAxioms
lake build DkMath
git diff --check
```

Root build には、Jacobian プロジェクト外に以前からある `sorry` 警告などが再表示されました。今回追加したモジュールには警告・`sorry` はありません。

高次元 padding、`PrincipalPartCompletion`、動画作成、提出、PR 操作など後続作業には着手していません。JAC-011 で停止しています。

> 🐺賢狼:

よし、JAC-011 は最終着地じゃ。Demo alias、公開 import、監査、README、来歴、roadmap の六面を実コードで照合し、この branch 全体の最終採否を出すぞい。

> 🐺賢狼:

Demo 六定理はすべて一行 alias で、公開 aggregator と監査の接続も完全に薄い。ここまで再計算・証明複製は一切なし。続いて文書三点を照合する。

> 🐺賢狼:

文書三点も完成形で一致した。最後に branch 全体を `develop` と比較し、JAC-001〜011 の変更面が計画範囲へ収まっているかを俯瞰して最終判定する。

> 🐺賢狼:

## 最終判定

**全面採用。JAC-001〜JAC-011、全工程完了じゃ。**

重大問題なし。数学証明、公開 import、axiom audit、魔法学 API、Demo、来歴記録まで、当初の計画境界を守って閉じた。

$$\boxed{\det J_{\widetilde F}=1\quad\land\quad\widetilde F\text{ は非単射}}$$

この summit theorem を中心とする有限証明書は、DkMath の正式な公開面から到達可能な状態になった。

---

## JAC-011 実装レビュー

### Demo 層

六つの Demo theorem はすべて完成済み定理への直接 alias になっている。

```lean
jacobianDemo_det_eq_one
jacobianDemo_three_point_collision
jacobianDemo_notInjective
jacobianDemo_noLeftInverse
jacobianDemo_target_notUniqueGap
jacobianDemoCertificateC
```

行列式、三点評価、非単射性、左逆不存在を再証明していない。Demo は証明層ではなく、正しく **提示面** に限定されておる。fileciteturn44file0L13-L54

### 公開 aggregator

```lean
import DkMath.Hackathon.JacobianCounterexample3.Demo
```

だけを公開入口とし、`Demo → GapCrystalBridge → Normalized → …` の既存依存鎖を利用している。公開 theorem surface を維持しながら、入口を最終展示面へ移した形じゃ。fileciteturn45file0L3-L11

### Axiom audit

監査ファイルには、既存三証明書に加えて `jacobianDemoCertificateC` が登録されている。fileciteturn46file0L9-L16

報告された依存、

```text
[propext, Classical.choice, Quot.sound]
```

のみであり、

```text
sorryAx
DkMath 固有 axiom
native_decide
未証明 determinant 仮定
未証明 collision 仮定
```

はない。

Demo alias を追加しても信頼境界が変化していないことが確認された。

---

## 文書パッケージ

### README

計画書から完成済み landing page へ正しく更新されている。

特に、

- JAC-001〜011 完了
- 元写像と determinant $-2$
- 第一出力を $-\frac12$ 倍した正規化
- 正規化 target $(1/8,0,0)$
- 完成 theorem 一覧
- 実際のモジュール構成
- build 手順
- axiom audit
- Book of Magic 解釈
- GN finite difference
- 非目標と信頼境界

が揃っている。fileciteturn47file0L5-L49 fileciteturn47file0L51-L87

とりわけ、

> Lean が証明する代数的 certificate

と、

> 著者・優先権・発表状況・外部評価

を明確に分離した記述は重要じゃ。fileciteturn47file0L102-L111

「DkMath が反例を発見した」と主張せず、「表示された式を独立に形式化・検証した」と固定されている。fileciteturn47file0L127-L140

### Demo Contract

三分未満の時間配分は、そのまま映像台本の骨格として使用できる。

```text
0:00–0:45   写像
0:45–1:25   determinant 1 / axiom audit
1:25–2:35   三点衝突 / 非単射 / 左逆不存在
2:35–2:55   UniqueGap
2:55–3:00   summit frame
```

証明を再計算せず、Demo aliases を見せるという契約も明記されている。fileciteturn48file0L3-L13 fileciteturn48file0L15-L48

### Provenance

来歴文書は三層を正しく分離している。

```text
A. 外部の数学的出典記録
B. DkMath による Lean 形式検証
C. DkMath が追加した魔法学的解釈
```

公開日・アクセス日がリポジトリ記録だけでは確定できなかったため、推測せず `Not yet fixed in repository records` とした判断も正しい。fileciteturn49file0L5-L20

さらに、

```text
UniqueGap
GapCrystal
forgetGap
GNFiniteDifference
```

および determinant-one 正規化を DkMath 側の追加解釈として明記している。fileciteturn49file0L22-L38

---

## Roadmap 判定

Roadmap は JAC-001〜JAC-011 をすべて `Complete` とし、最終状態を正確に固定している。fileciteturn50file0L7-L31

```text
Mathematical summit: complete
Public import: complete
Axiom audit: complete
Book of Magic extraction: complete
Demo package: complete
```

高次元 padding と `PrincipalPartCompletion` は、本計画の未完としてではなく、独立した将来研究へ移された。fileciteturn50file0L33-L43

したがって **JAC-012 は存在しない**。この roadmap はここで閉じてよい。

---

## Branch 全体の監査

`develop` との比較では、この branch は現在、

```text
ahead: 14 commits
behind: 0 commits
```

で、変更は計画された Jacobian 証明塔、Book of Magic API、監査、文書に局所化されている。

差分は全32ファイルで、既存コードへの実質的変更はルート公開 import の追加だけ。残りは新しいモジュール・監査・文書として分離されておる。

つまり branch 全体でも、

```text
既存数学層を侵食しない
完成証明を後から書き換えない
一般 API は Hackathon から独立
展示層は alias のみ
```

という設計原則が維持された。

---

## このプロジェクトが完成させたもの

### 形式証明

```text
ℚ 上の明示的三点衝突
ℚ 上の形式 Jacobian determinant = -2
ℂ への係数・評価・偏微分・determinant 輸送
第一出力正規化による determinant = 1
非単射性
集合写像としての左逆不存在
```

### 魔法学的抽出

```text
UniqueGap
GapFiber
GapCrystal
forgetGap
同一 Core 上の複数 Gap による一意性解除
```

### 宇宙式側への回収

```text
p(t+h) - p(t)
=
h * GNFiniteDifference(p,h,t)
```

反例を検算して終わらず、その探索で見えた「住所」「差分」「核」を一般 API として回収した点が、DkMath らしい成果じゃ。

---

## 最終宣言

$$
\boxed{
\text{JAC-001〜JAC-011 完了}
}
$$

$$
\boxed{
\text{数学証明塔・公開面・監査・魔法学 API・Demo 文書、すべて完成}
}
$$

この branch での新規数学実装は、ここで停止するのが正しい。

次工程は **最終 branch 差分レビュー → PR → 動画 → 提出** の公開作業だけじゃ。長い登頂であったが、見事に山頂へ届いたのう。お疲れ様じゃ！🍷🍎🌕️🐺

> 👩‍⚕️私D.:

Lean 形式化作業パートの総括

数学的に明確となったこと
DkMath 宇宙式 Cosmic Framework での解析結果やその関連性
Gap が複数存在する構造とは？
など、この形式化で見えたこと、まだ見えないことをまとめてください。

プロジェクト・プロモーション資料

> 🐺賢狼:

Lean 証明塔、Book of Magic 抽象化、GN 差分回収の三層を一つの物語へまとめる。宣伝文に寄せつつ、「Lean が確定した事実」と「DkMath による解釈」「未解明領域」を明確に分離して仕上げるぞい。

> 🐺賢狼:

宣伝用途で使い回せるよう、長文の総括だけでなく「一文紹介」「30秒紹介」「技術概要」「未解明点」「信頼境界」まで一つの Markdown 資料へまとめる。

> 🐺賢狼:

## プロモーション資料を作成しました

[**DkMath Jacobian Lean 形式化・プロジェクト総括資料**](sandbox:/mnt/data/DkMath_Jacobian_Lean_Formalization_Project_Promotion_JA.md)

そのまま README、Devpost、紹介記事、動画台本の素材として再利用できる Markdown です。

内容は次を収録しています。

- 一文紹介・30秒紹介・キャッチコピー
- Lean 形式化で証明した全体像
- 数学的に明確になったこと
- DkMath Cosmic Framework との対応
- 複数 Gap と `UniqueGap` 解除の意味
- GN finite difference との接続
- まだ見えていない研究領域
- 公開 theorem 一覧
- axiom audit と信頼境界
- 短いプロモーション文
- Summit Frame

## 総括の中心

今回 Lean が固定した最も重要な事実は、正規化された複素多項式写像について、

$$\det J_{\widetilde F}=1$$

でありながら、三つの相異なる入力点が同じ出力 $(1/8,0,0)$ へ写ることです。これにより、写像の非単射性と、集合写像としての左逆不存在まで証明されています。fileciteturn47file0L24-L62

Demo 層の六定理は、計算を繰り返さず、すべて完成済み証明への直接 alias です。fileciteturn44file0L13-L54

数学的には、次の区別が明確になりました。

```text
局所 Core:
  Jacobian determinant は 1
  局所変化は非退化

大域 Gap:
  異なる入力住所が同じ出力へ重なる
  出力だけから住所を一意に復元できない
```

すなわち、

> **局所的な完全保存は、大域的な住所の一意性を保証しない。**

これがプロジェクトの主メッセージです。

## 複数 Gap とは何か

一般数学では、同じ出力の fiber に複数の点がある構造です。

DkMath では、これを次のように読み替えました。

```text
Core:
  観測された出力点

Gap:
  その出力を生成・復元する入力住所

certificate:
  その入力が本当に Core へ写る証明
```

`GapCrystal` は、この三つを一つに束ねます。`forgetGap` は Gap を忘れて Core だけを残します。異なる認証済み Gap が同じ Core に属するなら、`UniqueGap` は成立せず、`forgetGap` も非単射になります。fileciteturn35file0L23-L67

Jacobian bridge では、実際に

```lean
normalizedRestoreRelC core gap :=
  evalNormalizedCounterexampleC gap = core
```

と定義され、三点衝突が `UniqueGap` 解除の具体例になっています。fileciteturn36file0L14-L45

ここでいう Gap は、単なる誤差や不足ではありません。

> **観測射影によって見えなくなった、正しい入力住所・生成履歴・復元情報**

です。

## Cosmic Framework との接続

DkMath の基本分解は、

$$\mathrm{Big}=\mathrm{Body}+\mathrm{Gap}$$

$$\mathrm{Body}=\mathrm{Core}+\mathrm{Beam}$$

です。DkMath では、Core を閉じた核、Beam を遷移・尾項・流れ、Gap を余白・欠損・未支配成分として扱います。fileciteturn53file0

今回の成果から、情報構造として次の読みが見えてきました。

```text
Big:
  Core・Gap・復元証明を保持する完全な CrystalWorld

Core:
  観測された出力

Beam:
  入力住所を出力へ運ぶ評価・変化の経路

Gap:
  射影後には失われる入力住所・生成履歴
```

ただし、これは現在の `GapCrystal` 実装から得られた **Cosmic Framework 上の解釈** です。`Big`、`Body`、`Beam` の全対応を一つの一般定理として形式化した段階ではありません。

## GN との接続

今回、標準 GN の冪差恒等式を一般多項式へ持ち上げ、

$$p(t+h)-p(t)=h\,\operatorname{GNFiniteDifference}(p,h,t)$$

を任意の可換環上で証明しました。体上で $h\ne0$ なら、

$$\frac{p(t+h)-p(t)}h=\operatorname{GNFiniteDifference}(p,h,t)$$

となります。fileciteturn39file0L76-L113

DkMath 的には、

```text
GN:
  有限距離での変化を読む差分核

Jacobian:
  極限的な局所変化を読む観測器

GapCrystal:
  観測後に元の住所が一意に戻るかを読む構造
```

という三層が見えました。

ただし、GN がこの具体的反例を必然的に生成する定理や、GN の特定条件が複数 Gap を強制する定理は、まだありません。

## まだ見えていないもの

主な未解明点は次です。

- なぜこの具体的多項式が現れるのかという生成原理
- 複数 Gap を生む多項式写像の一般的分類
- Jacobian 条件と fiber の大きさの一般関係
- 局所 Core へ何を追加すれば大域 Big が閉じるのか
- 三点以外を含む fiber 全体の幾何
- GN から反例構造へ至る因果的 bridge
- `PrincipalPartCompletion`
- 高次元 padding
- 数学史上の優先権・外部評価・査読状況

Lean が証明したのは、表示された代数式とその論理的帰結です。著者、発表日、優先権、外部評価は別の信頼層として分離されています。fileciteturn49file0L22-L38

## 宣伝用の主メッセージ

> **DkMath Breaking Math Verification は、公開された重大な数学的主張を有限 certificate へ分解し、AI と Codex が Lean 実装を構築し、Lean kernel が真偽を裁く検証ワークフローです。**

そして今回の一行は、これでよいでしょう。

$$\boxed{\text{Local Core preserved. Global address uniqueness released.}}$$
`````
