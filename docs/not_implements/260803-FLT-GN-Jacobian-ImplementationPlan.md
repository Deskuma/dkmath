# FLT・GN・Jacobian 宇宙式射影圏 実装計画

- Status: implementation plan / not implemented
- Date: 2026-08-03
- Branch at recording: `develop`
- Conversation ID: `6a7087d8-414c-83ee-a13a-9face5c381f6`
- Companion note: `260803-FLT-GN-Jacobian-CosmicProjectionCategory.md`
- Repository: `Deskuma/dkmath`

## 1. 目的

既存の FLT5、GN Framework、Jacobian 反例検証を変更せず、両者を同じ宇宙式復元インターフェースへ射影する。

第一目標は、次の二つの完成済み事実を同じ型の語彙で表示することである。

$$
\neg\exists x\in\mathbb N,\;x^5=GN_5(1,1)
$$

$$
\exists p_0\ne p_1,\;F(p_0)=F(p_1)=c
$$

宇宙式復元ファイバーとして読むと、前者は空ファイバー、後者は多重ファイバーである。

$$
\text{FLT5 local certificate}=\text{no restoration}
$$

$$
\text{Jacobian collision}=\text{multiple restorations}
$$

正常状態は一意復元である。

この三状態を共通 API で固定する。

## 2. 実装原則

1. 既存証明を再計算しない。
2. FLT5 の完成済み証明経路を改変しない。
3. Jacobian の多項式、点、行列式、衝突証明を改変しない。
4. `UniqueGap`、`GapFiber`、`GapCrystal` を再利用する。
5. 一般 API は `DkMath.BookOfMagic` 側へ置く。
6. FLT5 と Jacobian の具体的 bridge は上位の Demo / Hackathon 層へ置き、依存を逆流させない。
7. 圏論インスタンスは最初の目標にしない。
8. 各 checkpoint は独立して `lake build` できる大きさに保つ。
9. `sorry`、新規 axiom、`native_decide` を使用しない。
10. theorem surface と axiom surface を checkpoint ごとに監査する。

## 3. 現在の再利用対象

### 3.1 一般宇宙式

```text
DkMath.CosmicFormula.CosmicFormulaBinom
DkMath.CosmicFormula.CoreBeamGap
```

利用する中心構造は次である。

```lean
GN
Core
Beam
Gap
Big
big_eq_core_beam_gap
```

### 3.2 一般復元構造

```text
DkMath.BookOfMagic.UniqueGapContract
DkMath.BookOfMagic.GapCrystal
```

利用する中心構造は次である。

```lean
UniqueGap
not_uniqueGap_of_two
GapFiber
GapCrystal
CrystalWorld
forgetGap
forgetGap_notInjective_of_two_gaps
```

### 3.3 一般 GN 有限差分

```text
DkMath.BookOfMagic.GNFiniteDifference
```

利用する中心定理は次である。

```lean
eval_add_sub_eval_eq_mul_GNFiniteDifference
differenceQuotient_eq_GNFiniteDifference
```

### 3.4 FLT5 / GN5

```text
DkMath.FLT.Five.GN5
DkMath.FLT.Five.Main
DkMath.Hackathon.FinitePrimeEscapeGN5
```

利用する中心定理は次である。

```lean
add_pow_five_sub_eq_mul_GN5
GN5_one_one
GN_five_one_one_not_fifth_power
flt5Target
fermatFive_no_positive_solution
```

### 3.5 Jacobian 反例

```text
DkMath.Hackathon.JacobianCounterexample3.Normalized
DkMath.Hackathon.JacobianCounterexample3.GapCrystalBridge
DkMath.Hackathon.JacobianCounterexample3.Demo
```

利用する中心定理は次である。

```lean
normalized_eval_p0C
normalized_eval_p1C
p0C_ne_p1C
normalizedTargetC_not_uniqueGap
normalizedForgetGap_notInjective
jacobianDemoCertificateC
```

## 4. 予定モジュール構成

一般 API と具体例を分離する。

```text
lean/dk_math/DkMath/BookOfMagic/CosmicProjection/
├── Basic.lean
├── PowerRestore.lean
├── FunctionRestore.lean
├── FiberTheorems.lean
└── Morphism.lean                 # 後段、初期実装では任意

lean/dk_math/DkMath/BookOfMagic/CosmicProjection.lean

lean/dk_math/DkMath/Hackathon/FLTGNJacobianProjection/
├── FLT5Bridge.lean
├── JacobianBridge.lean
└── Demo.lean

lean/dk_math/DkMath/Hackathon/FLTGNJacobianProjection.lean

lean/dk_math/DkMathTest/BookOfMagic/CosmicProjection/
└── CheckAxioms.lean

lean/dk_math/DkMathTest/Hackathon/FLTGNJacobianProjection/
└── CheckAxioms.lean
```

多変数 GN は初期共通 API が安定してから別系統にする。

```text
lean/dk_math/DkMath/BookOfMagic/GNLineRestriction.lean
lean/dk_math/DkMath/BookOfMagic/MvGNFiniteDifference.lean
```

### 4.1 依存方向

許可する依存方向は次である。

```text
CosmicFormula
  ↓
BookOfMagic core API
  ↓
BookOfMagic.CosmicProjection
  ↓
Hackathon.FLTGNJacobianProjection
```

禁止する依存方向は次である。

```text
BookOfMagic.CosmicProjection
  → Hackathon.JacobianCounterexample3
```

一般 API が具体的ハッカソン成果へ依存すると、今後の再利用と import 最適化を妨げるためである。

## 5. Checkpoint CP-001 — 基準面監査

### 目標

実装前の theorem surface、import surface、axiom surface を固定する。

### 作業

1. 対象モジュールを個別 build する。
2. 使用予定 theorem 名を `#check` する一時ファイルを作る。
3. 完成済み summit theorem の `#print axioms` を記録する。
4. 現在の `DkMath.BookOfMagic.lean` import を記録する。
5. 一時ファイルを削除する。

### build

```bash
cd lean/dk_math
lake build DkMath.BookOfMagic
lake build DkMath.Hackathon.FinitePrimeEscapeGN5
lake build DkMath.Hackathon.JacobianCounterexample3
lake build DkMath.FLT.Five.Main
```

### 監査対象

```lean
#print axioms DkMath.Hackathon.GN_five_one_one_not_fifth_power
#print axioms DkMath.Hackathon.JacobianCounterexample3.jacobianDemoCertificateC
#print axioms DkMath.FLT.Five.fermatFive_no_positive_solution
```

### 成功条件

- theorem 名と namespace が確認できる。
- `sorryAx` がない。
- project-specific axiom がない。
- 既存 build failure がない。

### 停止条件

既存対象のいずれかが `develop` 上で build しない場合、新規実装を始めず基準面修復を別 checkpoint とする。

## 6. Checkpoint CP-002 — 復元系の最小型

### 目標

既存 `GapFiber` と `UniqueGap` を束ねる最小のパラメータ構造を実装する。

### 新規ファイル

```text
DkMath/BookOfMagic/CosmicProjection/Basic.lean
```

### 型案

```lean
universe u v

namespace DkMath.BookOfMagic.CosmicProjection

structure RestorationSystem where
  Core : Type u
  Gap : Core → Type v
  restore : (core : Core) → Gap core → Prop

end DkMath.BookOfMagic.CosmicProjection
```

### 状態述語

```lean
def HasRestoration
    (S : RestorationSystem) (core : S.Core) : Prop :=
  Nonempty (DkMath.BookOfMagic.GapFiber S.restore core)

def NoRestoration
    (S : RestorationSystem) (core : S.Core) : Prop :=
  ¬ HasRestoration S core

def UniqueRestoration
    (S : RestorationSystem) (core : S.Core) : Prop :=
  DkMath.BookOfMagic.UniqueGap S.restore core

def MultipleRestorations
    (S : RestorationSystem) (core : S.Core) : Prop :=
  ∃ gap₁ gap₂,
    S.restore core gap₁ ∧
    S.restore core gap₂ ∧
    gap₁ ≠ gap₂
```

### 基本定理

```lean
hasRestoration_iff_exists
noRestoration_iff_forall_not
multipleRestorations_not_unique
multipleRestorations_forgetGap_notInjective
```

### 注意

`NoRestoration`、`UniqueRestoration`、`MultipleRestorations` が一般型上で三分割を形成するとは主張しない。排中律や有限性、ファイバー濃度の決定可能性を API の前提に入れない。

### build

```bash
lake build DkMath.BookOfMagic.CosmicProjection.Basic
```

### 成功条件

- 既存 `not_uniqueGap_of_two` と `forgetGap_notInjective_of_two_gaps` を再利用する。
- 同じ証明を複製しない。
- 一般型に不要な `[DecidableEq]` や `[Fintype]` を要求しない。

## 7. Checkpoint CP-003 — 完全冪魔核の復元系

### 目標

$X=x^d$ を一般復元関係の特殊例として実装する。

### 新規ファイル

```text
DkMath/BookOfMagic/CosmicProjection/PowerRestore.lean
```

### 定義案

```lean
def powRestoreRel
    {R : Type*} [Monoid R]
    (d : ℕ) (core gap : R) : Prop :=
  gap ^ d = core

def powerRestorationSystem
    (R : Type*) [Monoid R] (d : ℕ) : RestorationSystem where
  Core := R
  Gap := fun _ => R
  restore := powRestoreRel d

def MagicCore
    {R : Type*} [Monoid R]
    (d : ℕ) (core : R) : Prop :=
  HasRestoration (powerRestorationSystem R d) core

def UniqueMagicCore
    {R : Type*} [Monoid R]
    (d : ℕ) (core : R) : Prop :=
  UniqueRestoration (powerRestorationSystem R d) core
```

### 基本定理

```lean
magicCore_iff_exists_pow_eq
not_magicCore_iff_no_pow_eq
```

定理の向きは既存 theorem との `simpa` が容易になるよう調整する。

### 非目標

初期段階では次を一般定理にしない。

```text
自然数上の d 次根の一意性
整数上の偶数冪の符号分類
体上の roots of unity による多重性
```

これらは復元ファイバーの具体例として後から追加できる。

### build

```bash
lake build DkMath.BookOfMagic.CosmicProjection.PowerRestore
```

## 8. Checkpoint CP-004 — 関数復元系

### 目標

任意の関数 $F:A\to B$ の fiber を宇宙式復元系として表す。

### 新規ファイル

```text
DkMath/BookOfMagic/CosmicProjection/FunctionRestore.lean
```

### 定義案

```lean
def functionRestoreRel
    (F : A → B) (core : B) (gap : A) : Prop :=
  F gap = core

def functionRestorationSystem
    (F : A → B) : RestorationSystem where
  Core := B
  Gap := fun _ => A
  restore := functionRestoreRel F
```

### 定理候補

```lean
function_hasRestoration_iff_mem_range
function_noRestoration_iff_not_mem_range
function_multipleRestorations_of_collision
function_notInjective_of_multipleRestorations
function_injective_iff_all_fibers_subsingleton
function_surjective_iff_all_hasRestoration
function_bijective_iff_all_uniqueRestoration
```

最後の同値は universe と `∃!` の扱いを確認してから追加する。最初は片方向定理へ分解してもよい。

### 既存 API との橋

`DkMath.Verification.CollisionCertificate` が利用可能なら、衝突証明書から `MultipleRestorations` への一般変換を置く。

```lean
CollisionCertificate.multipleRestorations
```

ただし `BookOfMagic` から `DkMath.Verification` への依存が重い場合は、具体 bridge 側へ置く。

### build

```bash
lake build DkMath.BookOfMagic.CosmicProjection.FunctionRestore
```

## 9. Checkpoint CP-005 — 共通 Fiber theorem surface

### 目標

空・一意・多重の三状態を扱う theorem surface を安定化する。

### 新規ファイル

```text
DkMath/BookOfMagic/CosmicProjection/FiberTheorems.lean
```

### 必須 theorem

```lean
multipleRestorations_not_unique
uniqueRestoration_not_multiple
noRestoration_not_unique
noRestoration_not_multiple
```

`noRestoration_not_unique` は `UniqueGap` が存在を含むことから得る。

### 任意 theorem

ファイバーが有限である具体的場合に限り、濃度 API を追加する。

```lean
fiberCard_eq_zero_iff
fiberCard_eq_one_iff
one_lt_fiberCard_iff
```

ただし一般層へ `[Fintype]` を漏らさない。有限版を別 section または別ファイルに分離する。

### aggregator 更新

```text
DkMath/BookOfMagic/CosmicProjection.lean
DkMath/BookOfMagic.lean
```

`DkMath.BookOfMagic.lean` へ新 aggregator import を追加する。

### build

```bash
lake build DkMath.BookOfMagic.CosmicProjection
lake build DkMath.BookOfMagic
```

## 10. Checkpoint CP-006 — FLT5 / GN5 bridge

### 目標

完成済み `GN_five_one_one_not_fifth_power` を、空の魔核復元ファイバーとして公開する。

### 新規ファイル

```text
DkMath/Hackathon/FLTGNJacobianProjection/FLT5Bridge.lean
```

### import

```lean
import DkMath.BookOfMagic.CosmicProjection
import DkMath.Hackathon.FinitePrimeEscapeGN5
```

### 必須 theorem

```lean
theorem GN_five_one_one_not_magicCore :
    ¬ DkMath.BookOfMagic.CosmicProjection.MagicCore
      5
      (DkMath.CosmicFormulaBinom.GN 5 1 1) := by
  -- Existing theorem only; no new number-theoretic proof.
  ...
```

既存 theorem は等式の向きが

```lean
GN 5 1 1 = x ^ 5
```

である。新 relation が

```lean
x ^ 5 = GN 5 1 1
```

を採用する場合は `eq_comm` で橋渡しする。

### 推奨 alias

```lean
GN5Projection_noRestoration
GN5Projection_emptyFiber
```

同じ内容の theorem を乱立させず、公開名は一つ、説明用 alias は最大一つにする。

### 非目標

- FLT5 全証明を `RestorationSystem` で再実装しない。
- 黄金整数降下法を一般 API へ移動しない。
- `fermatFive_no_positive_solution` を再証明しない。

### build

```bash
lake build DkMath.Hackathon.FLTGNJacobianProjection.FLT5Bridge
```

### 成功条件

新 theorem の proof が既存 theorem の変換だけで閉じる。

## 11. Checkpoint CP-007 — Jacobian bridge

### 目標

完成済み三点衝突を、関数復元系の多重ファイバーとして公開する。

### 新規ファイル

```text
DkMath/Hackathon/FLTGNJacobianProjection/JacobianBridge.lean
```

### import

```lean
import DkMath.BookOfMagic.CosmicProjection
import DkMath.Hackathon.JacobianCounterexample3.GapCrystalBridge
```

### 必須定理

```lean
theorem normalizedJacobianTarget_multipleRestorations :
    MultipleRestorations
      (functionRestorationSystem evalNormalizedCounterexampleC)
      normalizedTargetC := by
  refine ⟨p0C, p1C, ?_, ?_, p0C_ne_p1C⟩
  · exact normalized_eval_p0C
  · exact normalized_eval_p1C
```

実際の relation の unfold と等式の向きに応じて `simpa` を使う。

### 既存 theorem への一致

```lean
theorem normalizedJacobianTarget_not_uniqueRestoration :
    ¬ UniqueRestoration
      (functionRestorationSystem evalNormalizedCounterexampleC)
      normalizedTargetC :=
  multipleRestorations_not_unique
    normalizedJacobianTarget_multipleRestorations
```

さらに、既存 `normalizedTargetC_not_uniqueGap` と命題が definitionally equal または同値であることを確認する。

```lean
normalizedJacobian_notUnique_eq_existing
```

無理に等式 theorem にせず、双方向 implication でもよい。

### 非目標

- determinant を再計算しない。
- 三点評価を再計算しない。
- 新しい衝突点を探索しない。
- 二次元 Jacobian へ拡張しない。

### build

```bash
lake build DkMath.Hackathon.FLTGNJacobianProjection.JacobianBridge
```

## 12. Checkpoint CP-008 — 最小 Demo

### 目標

FLT5 と Jacobian が同じ復元 API 上に載ったことを一画面で示す。

### 新規ファイル

```text
DkMath/Hackathon/FLTGNJacobianProjection/Demo.lean
DkMath/Hackathon/FLTGNJacobianProjection.lean
```

### Demo theorem surface

```lean
/-- GN5 target has no fifth-power restoration. -/
theorem fltGNJacobianDemo_GN5_emptyFiber :=
  GN_five_one_one_not_magicCore

/-- The normalized Jacobian collision target has multiple restorations. -/
theorem fltGNJacobianDemo_Jacobian_multipleFiber :=
  normalizedJacobianTarget_multipleRestorations

/-- The Jacobian collision target violates unique restoration. -/
theorem fltGNJacobianDemo_Jacobian_notUnique :=
  normalizedJacobianTarget_not_uniqueRestoration
```

### Demo 文言

```text
same cosmic restoration interface
├── GN5: no restoring fifth-power Gap
└── Jacobian: multiple restoring input Gaps
```

### build

```bash
lake build DkMath.Hackathon.FLTGNJacobianProjection.Demo
lake build DkMath.Hackathon.FLTGNJacobianProjection
```

### 第一頂上判定

この checkpoint が通れば、共通射影の最小実装は完成とする。

まだ圏論インスタンス、多変数 GN、FLT5 全経路の再表現がなくてもよい。

## 13. Checkpoint CP-009 — axiom 監査と公開 import

### 目標

共通射影 theorem が Lean kernel-checked な既存証明だけに依存することを確認する。

### 新規ファイル

```text
DkMathTest/BookOfMagic/CosmicProjection/CheckAxioms.lean
DkMathTest/Hackathon/FLTGNJacobianProjection/CheckAxioms.lean
```

### 監査

```lean
#print axioms DkMath.Hackathon.FLTGNJacobianProjection.fltGNJacobianDemo_GN5_emptyFiber
#print axioms DkMath.Hackathon.FLTGNJacobianProjection.fltGNJacobianDemo_Jacobian_multipleFiber
#print axioms DkMath.Hackathon.FLTGNJacobianProjection.fltGNJacobianDemo_Jacobian_notUnique
```

### 公開 import

公開範囲を確認してから次のいずれかを選ぶ。

1. `DkMath.Hackathon` aggregator のみへ追加する。
2. 安定後に `DkMath.lean` へ追加する。

初期実装では 1 を優先し、一般 API の名前が安定する前に root import を膨らませない。

### build

```bash
lake build DkMathTest.BookOfMagic.CosmicProjection.CheckAxioms
lake build DkMathTest.Hackathon.FLTGNJacobianProjection.CheckAxioms
lake build DkMath.BookOfMagic
lake build DkMath.Hackathon.FLTGNJacobianProjection
```

### 追加検査

```bash
git diff --check
```

## 14. Checkpoint CP-010 — 復元系の射

### 開始条件

CP-008 と CP-009 が完了し、一般 API の型と名前が安定していること。

### 目標

復元系の間で Core、Gap、復元証明を保存する射を定義する。

### 新規ファイル

```text
DkMath/BookOfMagic/CosmicProjection/Morphism.lean
```

### 型案

```lean
structure RestorationHom (S T : RestorationSystem) where
  mapCore : S.Core → T.Core
  mapGap : {core : S.Core} → S.Gap core → T.Gap (mapCore core)
  map_restore :
    ∀ {core gap},
      S.restore core gap →
      T.restore (mapCore core) (mapGap gap)
```

### 必須実装

```lean
RestorationHom.id
RestorationHom.comp
```

### 必須法則

```lean
id_comp
comp_id
comp_assoc
```

### 保存定理候補

```lean
HasRestoration.map
MultipleRestorations.map_of_injective_gap
UniqueRestoration.map_of_bijective_gap
```

`MultipleRestorations` は `mapGap` が異なる Gap を潰す可能性があるため、無条件には保存されない。必要な単射条件を明示する。

この点は「射影が反例情報を潰さない」ための核心条件になる。

## 15. Checkpoint CP-011 — 圏論インスタンス

### 開始条件

`RestorationHom` の恒等射・合成・法則が安定していること。

### 目標

必要性が確認できた場合に限り、Mathlib `CategoryTheory` へ接続する。

### 選択肢

#### A. bundled category

`RestorationSystem` を対象、`RestorationHom` を射とする。

#### B. structured arrow / fibered category

次数 $d$、単位 $u$、係数環などを基底パラメータとし、各基底上に復元系を置く。

#### C. 圏論化しない

具体的射影と保存定理だけで研究上十分なら、Category instance を追加しない。

### 判断基準

次のいずれかに実用上必要な場合のみ実装する。

1. FLT5 と Jacobian の射影合成を theorem として再利用したい。
2. 複数理論の射影を同じ functor interface で管理したい。
3. 忘却写像と faithful / conservative 性を議論したい。
4. Core 基底上の fiber category として整理したい。

「圏」という名称を満たすだけのために依存と抽象度を増やさない。

## 16. Checkpoint CP-012 — 多変数 GN 線形制限

### 開始条件

最小共通射影が完成していること。CP-010、CP-011 は必須ではない。

### 目標

多変数多項式を点 $q$ と方向 $h$ に沿って一変数多項式へ制限する。

$$
p_{P,q,h}(s)=P(q+s h)
$$

### 調査対象

```text
MvPolynomial.eval
MvPolynomial.rename
MvPolynomial.bind₁
MvPolynomial.aeval
Polynomial.comp
Polynomial.eval₂
```

Mathlib の最も自然な API を選ぶ。手書き係数展開を避ける。

### 新規ファイル候補

```text
DkMath/BookOfMagic/GNLineRestriction.lean
```

### 定義案

```lean
def lineRestriction
    (P : MvPolynomial ι R)
    (q h : ι → R) : Polynomial R :=
  ...
```

### 定理候補

```lean
lineRestriction_eval
lineRestriction_zero
lineRestriction_one
lineRestriction_add
lineRestriction_mul
```

中心評価定理は次である。

$$
\operatorname{eval}(s,\operatorname{lineRestriction}(P,q,h))=P(q+s h)
$$

### 停止条件

MvPolynomial から Polynomial への変換が大規模な新 API を要求する場合、一度 scope を座標単項式または三次反例の具体式に縮小する。ただし具体式を手計算で再定義しない。

## 17. Checkpoint CP-013 — 多変数 GN 有限差分

### 目標

`lineRestriction` と既存 `GNFiniteDifference` を合成する。

### 新規ファイル候補

```text
DkMath/BookOfMagic/MvGNFiniteDifference.lean
```

### 定義案

```lean
def MvGNFiniteDifference
    (P : MvPolynomial ι R)
    (q h : ι → R)
    (s : R) : R :=
  GNFiniteDifference (lineRestriction P q h) s 0
```

引数配置は既存 GN の意味に合わせて監査する。

### 中心定理

$$
P(q+s h)-P(q)=s\,\operatorname{MvGNFiniteDifference}(P,q,h,s)
$$

### 写像版

多項式写像 $F:i\mapsto P_i$ に座標ごとに適用する。

$$
F(q+s h)-F(q)=s\,GN_F(q,h,s)
$$

型は `ι → MvPolynomial κ R`、`Matrix`、有限次元ベクトルのいずれが既存 Jacobian 実装と最も整合するか調査して決める。

## 18. Checkpoint CP-014 — Jacobian 零 Gap 断面

### 目標

多変数 GN 有限差分の $s=0$ 断面を形式偏微分と接続する。

期待する数学的形は次である。

$$
GN_F(q,h,0)=J_F(q)h
$$

### 注意

`GNFiniteDifference` の定義は係数付き $GN_n$ の和であり、$h=0$ の評価により形式微分係数が現れることをまず一変数で証明する。

一変数の先行 theorem 候補は次である。

```lean
GNFiniteDifference_zero_increment_eq_derivative
```

その後に line restriction の derivative と方向微分を接続する。

### 成功条件

既存 Jacobian 反例の `MvPolynomial.pderiv` から作られた Jacobian 行列と同じ形式偏微分を真実源にする。

手書き Jacobian を新しい定義源にしない。

## 19. Checkpoint CP-015 — 有限 Gap 衝突定理

### 目標

大域衝突を GN 有限差分消滅として表す。

$q_1=q+h$ とする。$F(q_1)=F(q)$ ならば、

$$
h\,GN_F(q,h,1)=0
$$

ベクトル方向とスカラー増分の設計によって実際の theorem 形は変わる。重要なのは、零 Gap の Jacobian 断面と有限 Gap の衝突を同じ GN object の異なる断面として並べることである。

### Jacobian 反例への bridge

既存の $p_0,p_1,p_2$ を用い、少なくとも一組について次を得る。

```lean
normalizedCollision_finiteGN_vanishes
```

この theorem は既存 point evaluation を再計算せず、一般有限差分定理と既存 collision equality を使う。

### 研究上の頂上

$$
\boxed{\text{Jacobian}=\text{GN の零 Gap 断面}}
$$

$$
\boxed{\text{collision}=\text{GN の有限 Gap 消滅}}
$$

この二つが同一 Lean module surface 上で確認できれば、GN Framework と Jacobian 反例の構造接続が完成する。

## 20. Checkpoint CP-016 — FLT5 全経路の射影目録

### 目標

FLT5 の既存証明を変更せず、どの theorem が宇宙式復元圏のどの状態変換に対応するかを文書と alias で記録する。

### 分類候補

```text
Fermat5Equation
  → primitive packet
  → signed Gap orientation
  → GN5 / cyclotomic body
  → golden factor restoration
  → unit-class fiber split
  → zero-sector descent
  → no restoration / contradiction
```

### 実装方針

- 原証明 theorem を直接 alias する。
- 新たな数学的内容を加えない。
- 各段階に `ProjectionStage` のような巨大 enum を先に作らない。
- 実際に共通化できる二段階以上が確認された時だけ構造化する。

### 成果物候補

```text
DkMath/FLT/Five/CosmicProjectionBridge.lean
DkMath/FLT/Five/docs/FLT5-CosmicProjection-Map.md
```

## 21. テスト戦略

### 21.1 focused build

各 checkpoint で新規 module のみを build する。

### 21.2 aggregator build

節目ごとに次を build する。

```bash
lake build DkMath.BookOfMagic
lake build DkMath.Hackathon.FLTGNJacobianProjection
lake build DkMath.FLT.Five.Main
lake build DkMath.Hackathon.JacobianCounterexample3
```

### 21.3 root build

公開 import を変更した checkpoint のみ `lake build DkMath` を実行する。

### 21.4 axiom audit

公開 theorem へ `#print axioms` を実行する。

失敗信号は次である。

```text
sorryAx
DkMath-specific axiom
unexpected theorem assumption
```

### 21.5 import audit

```bash
lake env lean <temporary-check-file>
```

最小 import から theorem が見えることを確認し、一時ファイルを削除する。

### 21.6 diff audit

```bash
git diff --check
```

## 22. リスクと対処

| Risk | 内容 | 対処 |
|---|---|---|
| 過剰抽象化 | 圏論型だけ増えて具体 theorem が接続できない | CP-008 Demo を第一頂上にする |
| import 逆流 | BookOfMagic core が Hackathon に依存する | concrete bridge を Hackathon 側へ置く |
| 定義重複 | `GapCrystal` と同型の新 structure を作る | 既存型を対象として再利用する |
| 等式方向 | `GN = x^5` と `x^5 = GN` が一致しない | `eq_comm` を局所 bridge で処理する |
| 一意性の誤読 | 複素数上の冪根は一般に一意でない | `MagicCore` と `UniqueMagicCore` を分離する |
| 三分律の過剰主張 | 一般ファイバーを空・一点・複数へ決定できない | 各状態を独立 Prop とする |
| 多変数化の肥大 | MvPolynomial の line restriction が複雑 | 一変数 theorem を先に完成し scope を縮小可能にする |
| 情報を潰す射 | mapGap が非単射で多重性を消す | 保存 theorem に単射条件を要求する |
| 証明再計算 | Jacobian determinant や FLT5 descent を再実装する | alias / bridge theorem のみ許可する |
| 公開主張過大 | 一般 FLT や JC2 の解決と誤読される | scope / non-goals を各 README に明記する |

## 23. 禁止事項

本計画の実装では、明示的な別合意なしに次を行わない。

1. FLT5 の既存証明ファイルを大規模 refactor しない。
2. Jacobian 反例の式、点、正規化を変更しない。
3. determinant や point evaluation を再証明しない。
4. 二次元 Jacobian 問題へ進まない。
5. 一般 FLT の証明を主張しない。
6. `PrincipalPartCompletion` を同時着手しない。
7. 圏論 instance を CP-008 より前に実装しない。
8. 新規 axiom、`sorry`、`native_decide` を導入しない。
9. 既存 namespace と theorem 名を無断で rename しない。
10. `develop` の unrelated warning を本計画の成果として解消したと主張しない。

## 24. Codex 実行単位

一回の Codex 指示は一 checkpoint に限定する。

標準指示の末尾に次を含める。

```text
Investigate the live repository before editing.
Reuse existing theorem surfaces.
Do not duplicate completed proofs.
Build the focused module after each change.
Run the requested axiom audit.
Run git diff --check.
Stop at the checkpoint boundary and write a report.
```

各 report は次を含む。

1. 調査した既存 theorem。
2. 作成・変更ファイル。
3. 新規 theorem surface。
4. 既存 theorem の再利用箇所。
5. build 結果。
6. axiom 出力。
7. warning。
8. `git diff --check`。
9. 次 checkpoint への障害。
10. 禁止された後続作業を開始していない確認。

## 25. 推奨実装順

短期の実装順は次である。

```text
CP-001 baseline audit
  ↓
CP-002 RestorationSystem
  ↓
CP-003 PowerRestore
  ↓
CP-004 FunctionRestore
  ↓
CP-005 Fiber theorem surface
  ↓
CP-006 FLT5 / GN5 bridge
  ↓
CP-007 Jacobian bridge
  ↓
CP-008 shared Demo
  ↓
CP-009 axiom and import audit
```

ここで一度停止し、共通射影の価値と API の自然さをレビューする。

第二期は次である。

```text
CP-010 morphisms
CP-011 optional Category instance
CP-012 line restriction
CP-013 multivariable GN
CP-014 Jacobian zero-Gap section
CP-015 finite-Gap collision
CP-016 FLT5 full projection inventory
```

圏論化と多変数 GN は独立に進められる。CP-011 を保留したまま CP-012 へ進んでもよい。

## 26. 最小完成条件

第一期の完成条件は次である。

```lean
#check DkMath.Hackathon.FLTGNJacobianProjection.
  fltGNJacobianDemo_GN5_emptyFiber

#check DkMath.Hackathon.FLTGNJacobianProjection.
  fltGNJacobianDemo_Jacobian_multipleFiber

#check DkMath.Hackathon.FLTGNJacobianProjection.
  fltGNJacobianDemo_Jacobian_notUnique
```

三 theorem が同じ `RestorationSystem` と fiber predicates を使用し、focused build と axiom audit を通ること。

数学的内容は既存証明から供給される。新規層の仕事は、両成果を同じ宇宙式型へ忠実に射影することである。

## 27. 最終完成像

最終的な構造図は次である。

$$
\begin{array}{ccccc}
\text{FLT5} & \xrightarrow{\Pi_5} & \mathcal C_{\mathrm{CF}} & \xleftarrow{\Pi_J} & \text{Jacobian} \\
& & \downarrow & & \\
& & \text{restoration fiber state} & &
\end{array}
$$

FLT5 / GN5 は空ファイバー証明書を与える。

Jacobian 反例は多重ファイバー証明書を与える。

一意復元が正常な中間状態である。

GN 有限差分は各理論の多項式変化を共通の Body / Gap 言語へ変換する。

射はこの復元情報を保存し、情報を潰さない条件を明示する。

これにより宇宙式は単なる一つの恒等式ではなく、異なる数学理論を受け入れ、正常状態と反例状態を同じ形式で比較できる Lean 上の共通中間表現となる。
