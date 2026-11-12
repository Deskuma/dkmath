# DkMath 実装設計書：宇宙式の入れ子・可換輸送と GN–Kummer 降下

- 文書 ID：`GN-Nested-State-Transport-261018-v0`
- 作成日：2026-10-18
- 状態：**DESIGN / 未実装**（既存成果・数学的導出・実装候補を区別する）
- 想定配置：`docs/dev/GN-Nested-State-Transport-261018-v0/DESIGN.md`
- 対象：`DkMath.Lib.Cosmic.*`、`DkMath.Lib.NumberTheory.*`、`DkMath.FLT.Kummer.*`
- 入力基準：2026-10-17 snapshot（`__snapshot-dk_math-lean-code-261017-2054.tar.gz`）と 2026-10-18 の検討

## 0. 要約・設計判断

**宇宙式の Core は分割・再結合できる。下位の Big は上位の基底になり、適切な新しい枠組みでは Core も別の Big の役割を担いうる。しかし、Core が自動的に完全 `d` 乗になるわけではない。** この区別を型と定理の仮定で固定する。

新しい汎用実装の主題は、単なる多項式の再展開ではなく、以下の三層の輸送である。

1. **代数的入れ子（値の保存）**：差分 Core を分割しても合計・終点が不変。分割順序も可換。
2. **GN／位相（情報配置の保存）**：差分を Gap と GN に因数分解し、円分位相間の可除性・分岐付値の配置を追跡。
3. **Kummer／State（条件付きの構造保存と深度減少）**：冪根抽出・単元補正・三位相再構成によって *異なる* State を構成し、分岐深度を減らす。

**実装決定**：既存の `GN` は置換しない。`GTail(p,1,...)` を標準の GN として利用。`GTail` の任意切断 `r` や項選択による移送は独立した研究道具として保つ。新しい `CoreNested` は既存の `GTailTransport` を再実装せず、**引数（基点・増分）方向の輸送**を担当する。

## 1. 用語と正規化（混同を防ぐ必須契約）

可換環 `R`、次数 `d : ℕ`、基点 `t : R`、増分 `u : R` について、

\[
\begin{aligned}
\operatorname{Big}_d(t,u)&=(t+u)^d,\\
\operatorname{Gap}_d(t)&=t^d,\\
\operatorname{Core}_d(t,u)&=(t+u)^d-t^d
   =u\,GN_d(u,t).
\end{aligned}
\]

従って `Big = Gap + Core`。これは標準宇宙式 `(x+u)^d = u^d + x·GN_d(x,u)` を `x := u`、旧 `u := t` として読み替えたもの。**既存 `GTail` の引数順**は `(d, r, 増分, 基点)` である。

`Core` はこの文書では `Big` から基点冪を差し引いた **差分**を表す。既存コード内の `Body/Gap/Core` の命名と機械的に同一視しない。

### FLT への埋め込み

奇素数 `p`、`g := x+y`、`t := -y` とする。

\[
\operatorname{Core}_p(-y,g)
=x^p+y^p=g\,GN_p(g,-y).
\]

ここで `x^p+y^p` は「元の宇宙式の Core」であって、`x^p` を Big とする宇宙式における Big と同一ではない。この差分が単元付き `p` 乗になり得ることが、Kummer の状態を導入する追加条件となる。

## 2. 第1層：代数的入れ子・可換図式

### 2.1 最小定義

\[
C_d(t,u):=(t+u)^d-t^d.
\]

### 2.2 主定理（何の数論的仮定も不要）

**(N1) 二段分割／telescoping**

\[
\boxed{C_d(t,a+b)=C_d(t,a)+C_d(t+a,b)}
\]

**(N2) 経路独立性／交換**

\[
\boxed{C_d(t,a)+C_d(t+a,b)=C_d(t,b)+C_d(t+b,a)}
\]

**(N3) 三段分割／結合の独立性**

\[
\boxed{C_d(t,a+b+c)=C_d(t,a)+C_d(t+a,b)+C_d(t+a+b,c)}
\]

**(N4) GN 表現への輸送**

\[
\boxed{(a+b)GN_d(a+b,t)
=a\,GN_d(a,t)+b\,GN_d(b,t+a)}
\]

(N4) は (N1) と `Core = step · GTail d 1 step base` の合成。移動順序についても (N2) と同様の GN 恒等式が得られる。

**重要な訂正**：以前の会話中に記載された `C_d(a+b,c)=C_d(a,b+c)+C_d(b,c)` は一般には偽。この文書では (N1) を正本とする。

### 2.3 Big/Core の役割交換の契約

`B₀=t^d`、`B₁=(t+a)^d`、`B₂=(t+a+b)^d` とすると、

\[
B_1=B_0+C_d(t,a),\quad B_2=B_1+C_d(t+a,b).
\]

`B₁` は下層の Big であり上層では次の移動の基点値になる。一方、`C_d(t,a)` がさらに `w^d` として新しい Big を演じるには、**`∃ w, C_d(t,a)=w^d` などの証人が別途必要**。これを一般定理の無条件な結論に混入させない。

### 2.4 Lean API 案（型の骨格・未ビルド）

```lean
namespace DkMath.Lib.Cosmic

variable {R : Type*} [CommRing R]

def powerCore (d : ℕ) (base step : R) : R :=
  (base + step) ^ d - base ^ d

-- N1: 最優先の実装対象
theorem powerCore_split (d : ℕ) (base a b : R) :
    powerCore d base (a + b) =
      powerCore d base a + powerCore d (base + a) b := by
  -- unfold powerCore; additive cancellation, associativity
  ...

-- N2: 異なる移動経路の可換性
theorem powerCore_swap (d : ℕ) (base a b : R) :
    powerCore d base a + powerCore d (base + a) b =
      powerCore d base b + powerCore d (base + b) a := by
  ...

-- 既存 GTail の r=1 への橋
theorem powerCore_eq_gtail_one (d : ℕ) (base step : R) :
    powerCore d base step =
      step * DkMath.CosmicFormula.GTail d 1 step base := by
  ...

end DkMath.Lib.Cosmic
```

`...` は設計書上の**未実装 proof sketch**。この断片は Lean ビルド済みと宣言しない。証明は `add_pow_eq_mul_GTail_one_add_gap`、`add_assoc`、`add_comm`、`sub_add_cancel`、`ring` 等を活用する。

## 3. 第2層：Gap–GN–Phase の分岐情報を保存する

奇素数 `p` に対して、`Rₚ=ℤ[ζₚ]`、`λ=1-ζₚ`。`g=x+y=λq` とする。

\[
\boxed{x^p+y^p=g\,GN_p(g,-y)}
\]

各位相 `i : Fin p` を

\[
T_i=(\zeta_p^i-1)/\lambda,\qquad Q_i=q+T_iy
\]

で正規化する（Lean では環内の除算ではなく、`λ·Tᵢ = ζᵢ−1` の証人を推奨）。全位相因子は `x+ζₚ^i y=λQᵢ`。従って

\[
\boxed{x^p+y^p=\lambda^p\prod_{i=0}^{p-1} Q_i},
\qquad
\boxed{GN_p(\lambda q,-y)=\lambda^{p-1}\prod_{i=1}^{p-1}Q_i}.
\]

剰余環 `Rₚ/(λ) ≃ 𝔽ₚ` で `Tᵢ ≡ -i`。`λ ∤ y` なら `i₀ = q̄/ȳ` が一意に存在し、`λ ∣ Qᵢ ↔ i = i₀`。

**(R1) 特別な位相への可除性集中（ゼロにも安全な形）**

\[
\boxed{\forall k\in\mathbb N,\ \lambda^{p+k}\mid(x^p+y^p)\iff\lambda^k\mid Q_{i_0}}
\]

非零なら、局所付値の有限値を用いて `v_λ(x^p+y^p)=p+v_λ(Qᵢ₀)` と書ける。

**(R2) Gap と GN の局所付値保存**（ゼロを除き付値を使う）

\[
v_\lambda(x^p+y^p)=v_\lambda(g)+v_\lambda(GN_p(g,-y)).
\]

ここで位相0が特別な場合、追加分岐は `g` に格納され、`GN` 単独には現れない。特別な位相が非零なら GN が追加分岐を保持する。**数値を保持する同一状態内の保存**と、後述の異なる State 間の降下を混同しない。

### 3.1 数値実験の基準

既存 `ramified_gn_numeric.py`／ログについて整数係数演算で再実行一致を確認。`p=3,5,7,11,13`、人工例390、GTail合同式1,865、原始根変更306、無作為800、すべて通過。これは (R1) と関連補題の回帰候補であり、Lean 証明や一般 `Stateₚ` 降下の代わりではない。

### 3.2 新規 API の望ましい形

`RamifiedGNPhaseBridge.lean` で、抽象的な環・素元・剰余射影・位相傾斜の packet を用いる（実装しやすい範囲から）。初期実装は **既存七次環上で** (R1) を接続する。その後で一般 `p` にパラメータ化する。付値版より先に `∣` の同値として証明し、ゼロ／単元／`k=0` を包括する。

`GNPhaseFactorization`、`GNSourceTransport`、`GNPhaseThreeTerm`、`CosmicRamifiedPrimePower` の再利用を優先し、円分積を重複して証明しない。

## 4. 第3層：Kummer State の条件付き輸送

### 4.1 State の意味

\[
\operatorname{State}_p(m):
\left\{
\begin{array}{l}
x,y,z\in R_p,\quad\varepsilon\in R_p^\times,\\
\operatorname{IsCoprime}(x,y),\\
\lambda\nmid y,\quad\lambda\nmid z,\\
x^p+y^p=\varepsilon(\lambda^m z)^p.
\end{array}\right.
\]

これは FLT7 の実装済み `SevenDescentState.State` の一般化案。**新旧状態で `x,y,z,ε` が同一とは要求しない**。再構成では値は通常変わり、保存するのは State を満たす条件である。

### 4.2 降下の内部順序

`Stateₚ(m+1)` → `λ ∣ x+y` → 同じ `q` から全位相の `Qᵢ` を形成 → 一意な `i₀` を選択 → 位相間 coprimality → 各イデアルの `p` 乗性 → class-group `p`-torsion-free により `Qᵢ=uᵢ bᵢ^p` を抽出 → `bᵢ₀=λ^m z′`（単元の扱いを別途確認） → 三位相線形恒等式 → 重み付き `p` 乗方程式 → Kummer 単元補題で係数比を `p` 乗化 → `Stateₚ(m)`。

ここで class-group 条件と単元補題は、GN の代数恒等式からは出てこない。

### 4.3 降下を成立させるプロバイダ条件

- `classGroupPTorsionFreeAt Rₚ p`、または `Nat.Coprime p (Fintype.card (ClassGroup Rₚ))` を満たす証明。
- `KummerUnitPowerCriterion Rₚ p`（環内の単元が整数に mod `p` で合同であるとき、その単元を `p` 乗として吸収）。
- 円分素元の非零性・素元性、剰余体 `ZMod p`、位相差の単元性。
- 原始性／非分岐性の輸送補題。

主目標は

\[
\boxed{\forall m\ge 1,\ \operatorname{Nonempty}(\operatorname{State}_p(m+1))\to\operatorname{Nonempty}(\operatorname{State}_p(m))}
\]

と、深度1の不存在 `¬ Nonempty (Stateₚ 1)`。これらから正深度 State を排除する。その後、**Case I と整数反例 → 正深度 State の入口**を別に接続して FLT を得る。これらを省略して「正則素数 FLT 一般化完了」と宣言しない。

### 4.4 型と定理の分離

- `CoreNested`：`CommRing` のみ。`m` も `p` も `ζ` も不要。
- `RamifiedGNPhaseBridge`：奇素数・円分環・分岐素元・剰余体。FLT の反例や類群は不要。
- `RegularStateTransport`：上記 + class-group + Kummer-unit 条件。降下定理はこの層のみに配置。
- 各 `Three/Five/Seven/Eleven/Thirteen` provider：次数固有の正則性・単元条件・入口を閉じる。

## 5. 既存ソースの再利用一覧（10月17日 snapshot で定理本体を確認）

| 既存ファイル（`DkMath/...`） | 代表 API | 利用方針 |
|---|---|---|
| `Lib/Cosmic/GTail.lean` | `add_pow_eq_mul_GTail_one_add_gap`, `add_pow_eq_prefix_add_xpow_mul_GTail` | Core/GN の基底 |
| `Lib/Cosmic/GTailSelection.lean` | `selectedGap_add_selectedBody` | 同一 Big に対する選択分割 |
| `Lib/Cosmic/GTailTransport.lean` | `selected_balance_transport`, `selectedBody_transport` | **項集合**変更の保存（新規入れ子とは区別） |
| `Lib/Cosmic/GNPhaseFactorization.lean` | `focused_pow_sub_pow_eq_prod_fin`, `GN_eq_nontrivial_phase_prod_range` | 位相積への架橋 |
| `Lib/Cosmic/GNSourceTransport.lean` | `map_phaseSource`, `map_phaseSource_pow` | 根・係数の正確な輸送 |
| `Lib/Cosmic/GNPhaseThreeTerm.lean` | `phaseSource_three_term_relation` | 三位相の代数恒等式 |
| `Lib/NumberTheory/CosmicRamifiedPrimePower.lean` | `prime_power_dvd_pow_sub_one_of_dvd_pred_power` | 一般分岐冪合同 |
| `Lib/NumberTheory/ClassGroupTorsionBridge.lean` | `classGroupPTorsionFreeAt_of_coprime_card` | PID を必須としない類群条件 |
| `Lib/NumberTheory/PrincipalIdealPower.lean` | `exists_unit_mul_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt` | 冪抽出 |
| `FLT/Kummer/GNKummerUnitAdapter.lean` | `KummerUnitPowerCriterion` | 汎用単元プロバイダ |
| `FLT/Kummer/SevenDescentState.lean` | `State`, `State.gn_equation` | State モデル |
| `FLT/Kummer/SevenDescentPhases.lean` | `State.quotient_dvd_iff`, `no_state_one` | 位相集中・基底矛盾の既存回帰 |
| `FLT/Kummer/SevenDescentPowers.lean` | `State.quotients_coprime`, `State.exists_quotient_roots` | 冪抽出の既存回帰 |
| `FLT/Kummer/SevenDescentStep.lean` | `State.three_phase_identity`, `descent_step` | 状態降下の既存回帰 |
| `FLT/Kummer/SevenDescentUnits.lean` | `ratio_seventh` | 単元比の冪化の既存回帰 |

## 6. 新規モジュール計画・依存グラフ

```text
DkMath.Lib.Cosmic.GTail
        │
        ▼
DkMath.Lib.Cosmic.CoreNested              （新規・第1層）
        │
        ├────> DkMath.Lib.Cosmic.GNPhaseFactorization （既存）
        │                   │
        │                   ▼
        │     DkMath.Lib.NumberTheory.RamifiedGNPhaseBridge
        │                   │                         （新規・第2層）
        └───────────────────┘
                            │
             既存：ClassGroupTorsionBridge / PrincipalIdealPower
             既存：GNKummerUnitAdapter / GNPhaseThreeTerm
                            │
                            ▼
             DkMath.FLT.Kummer.RegularStateTransport
                                            （新規・第3層）
                            │
                 p=7 regression → p=5 → p=3 → p=11/13
```

依存方向は `Lib.Cosmic` → `Lib.NumberTheory` → `FLT.Kummer` を厳守。逆向き import と完成済み FLT 定理への循環参照を禁止する。Facade への追加は、個別モジュールの focused build 合格後に行う。

## 7. 実装インストラクション（Codex 用）

### NST-001：CoreNested を最小構成で実装

- 作成：`DkMath/Lib/Cosmic/CoreNested.lean`。
- `powerCore`、`powerCore_split`、`powerCore_swap`、`powerCore_eq_gtail_one` と三段結合補題。
- `d=0`、`step=0`、`base=0`、負整数、`ℤ / 5ℤ`、`ℤ` の回帰。
- 成果：Big の値を変更せず分割順序を交換できることを kernel で確定。

### NST-002：GTailSelection/Transport との境界を定理化

- **基点・増分の変更**と **二項展開の項選択変更**を別軸として扱う。
- 少なくとも同じ Big の二つの表示が元の多項式値で一致する adapter を導出。
- `GTailTransport` の式を重複実装しない。

### NST-003：7次の RamifiedGNPhaseBridge を通す

- `State.quotient_spec`、`State.quotient_dvd_iff`、`State.product_quotients` から開始。
- `λ` のべきによる可除性同値 (R1) を構築する。`v(0)=∞` が問題になる付値 API は後回し。
- 位相0／非零位相の Gap–GN 分配を regression とする。

### NST-004：一般 p の phase packet へ持ち上げる

- `Fin p`、円分根、剰余 `ZMod p` と `λ` の素元性を整備。
- `phaseSlope` の残余 `−i`、特別な一位相、全位相積の正規化を次数非依存にする。
- 11・13 で `i₀=0` の扱いも検査。

### NST-005：Kummer 差し込み口の一般化

- 類群 `p`-torsion-free を受け取る冪抽出と `KummerUnitPowerCriterion` を使う。
- `weighted_successor → normalize_weighted → descent_step` を一般 `p` 化。
- FLT7 の `descent_step` を新実装から復元する独立回帰を先行する。

### NST-006：FLT5/3→11/13 の provider 接続

- まず 5 と3で既存の専用降下との対応を確認。その後 11・13。
- 既存 FLT 完成定理からの証明は禁止（再証明としての独立性を保つ）。
- 完成判定はそれぞれ正深度 State 不存在・Case I・初期 State 入口・最終 FLT の全接続。

## 8. 品質ゲート／「完成」の定義

**数学ゲート**

- (N1)–(N4) に反例がなく、`d=0` も成立。
- 差分恒等式が成り立つことと、ある Core が `p` 乗であることを区別。
- 位相0とそれ以外で、深度が Gap 側／GN 側のどちらに載るかを明示。
- 局所 Big の **値・付値保存**と State 間の **条件保存・深度減少**を混同しない。

**Lean ゲート**

- `lake env lean` または `lake build <focused target>` による検査（実環境に適したコマンドを選定）。
- 新規モジュールに `sorry`、`admit`、独自 `axiom` を含めない。
- `#print axioms` で新規核心定理を監査。既存の論理基盤公理以上が紛れ込まないこと。
- FLT3/5/7 既存経路を破壊せず、独立した新規経路で再構成できること。
- 必要な import のみ。`import Mathlib` の丸ごと追加を原則避ける。

**研究ゲート**

- Outcome A：代数入れ子・GN 位相保存・必要仮定の下で降下まで閉じる。
- Outcome B：恒等式と分岐集中は閉じるが、一般 Kummer State 接続が未完了。
- Outcome C：新しい型・条件または実例で一般化の障害が判明。反例を記録し命題を修正する。

## 9. リスクと禁止する推論

1. `C_d(t,u)` は一般に完全 `d` 乗 **ではない**。単なる役割交換から Kummer の冪抽出を結論しない。
2. `Big = Gap + Core` の値の保存は、異なる State の Big が等しいことを意味しない。
3. `GN` 単独の付値が全分岐次数を保存するとは限らない。位相0が選ばれると追加付値は Gap に載る。
4. `Qᵢ = uᵢ bᵢ^p` は位相商のイデアル `p` 乗性と類群条件が必要。因数分解恒等式だけからは得られない。
5. 任意の単元が `p` 乗になるわけではない。整数 mod `p` 合同などの仮定付き `KummerUnitPowerCriterion` を使う。
6. `Stateₚ(m+1) → Stateₚ(m)` だけでは一般 FLT は終わらない。`no_state_one`・初期入口・Case I も必要。
7. 数値実験の全通過は存在定理や一般証明ではない。独立に Lean kernel が検証する。

## 10. 最終的な設計原理

\[
\boxed{
\begin{gathered}
\text{同一 Big：差分の保存と経路独立}\\
\Downarrow\\
\text{Gap+GN：分岐情報の完全な配置}\\
\Downarrow\\
\text{Kummer：条件付きの冪抽出}\\
\Downarrow\\
\text{別の State：構造を保ち深度を減少}
\end{gathered}
}
\]

**この文書で最優先する実装は NST-001**。`powerCore_split` / `powerCore_swap` を最小限の抽象環で完成させることで、入れ子・移り変わり・乗り移りを表す語彙を数学的に固定する。NST-003 以降は、それを利用する FLT 降下理論の別層として厳格に分離する。

---

### 出典と検証範囲

既存 API 名と配置は、会話に添付された 2026-10-17 DkMath snapshot のソースに基づく。数学的な (N1)–(N4) は初等代数から導出可能。一般 p の位相集中・State 輸送は新規の**形式化目標**であり、Lean での追加実装・ビルドは本設計書では行っていない。数値実験は添付の Python とログにより再実行一致を確認した。
