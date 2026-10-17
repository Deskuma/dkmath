# GN Nested State Transport 実装報告（2026-10-18）

## 到達点

**Outcome A（算術条件付きの一般 State 降下）**。代数入れ子、一般素数の分岐集中、
類群と Kummer 単元条件を受け取る実際の一段再構成、および正深度 State の不存在を実装した。
3・5 は既存の算術補題を供給して一般 State の不存在を得た。7 は既存 State との相互変換を通して
新しい一般降下から一段遷移と不存在を復元した。

これは **すべての正則素数に対する FLT の完成ではない**。11・13 の具体的な類群条件・
Kummer 単元条件と、一般 Case I／整数反例の向き付けが残る。NST-006 全体は未完了。

## 設計番号ごとの実装範囲

| 段階 | 結果 | 実装した内容 |
|---|---|---|
| NST-001 | 完了 | `powerCore`、二段・三段分割、経路交換、GTail/GN 輸送、奇数冪和の入口 |
| NST-002 | 完了 | 任意の項選択と同じ Big を持つ adapter、二段移動と項選択の同時表示 |
| NST-003 | 完了 | 既存七次 `State.quotient` 上の任意深度 R1 |
| NST-004 | 完了（位相 packet 層） | 一般素数の負の幾何和 slope、剰余 `−i`、唯一の位相、全積・GN 積、分岐集中、一般円分数体 provider |
| NST-005 | 完了（明示した算術条件付き） | Dedekind 環上の類群 p-torsion 消去、同じ位相族の根の抽出、三位相再構成、単元比の冪化、一段降下、正深度排除 |
| NST-006 | 部分完了 | 3・5・7 の一般 State 回帰、11・13 の具体的円分体における位相回帰、一般の向き付け済み Case II 整数入口 |

NST-004 の「完了」は設計の phase packet／可除性 API の範囲である。
議事録にある剰余多項式の偏微分・単純根多項式 API や有限付値 API は追加していない。

## 配置と利用入口

以下はすべて `DkMath/` に対する相対パス。

- `Lib/Cosmic/CoreNested.lean`：最小の `CommRing` 層。
- `Lib/Cosmic/CoreNestedTransport.lean`：既存 `GTailTransport` の項選択との接続。
- `Lib/NumberTheory/RamifiedGNPhaseBridge.lean`：`RamifiedPhasePacket` と R1、Gap/GN の分配。
- `Lib/NumberTheory/CyclotomicRamifiedPhase.lean`：任意の奇素数円分数体 `𝓞 K` 上の実際の packet。
- `FLT/Kummer/RegularDescentState.lean`：State、不変条件、深度1排除、重み付き式の正規化。
- `FLT/Kummer/RegularDescentPowers.lean`：互いに素性、イデアル冪、類群消去、同じ根の分岐深度の剥離。
- `FLT/Kummer/RegularStateTransport.lean`：単元比・三位相の統合、`descent_step`、`no_state`、Case II 整数入口。
- `FLT/Kummer/CyclotomicRegularTransport.lean`：一般の円分算術条件、3・5 の具体的 State 排除。
- `FLT/Kummer/SevenRegularTransport.lean`：既存七次 carrier との接続と独立回帰。

低層は `import DkMath.Lib`、降下層は `import DkMath.FLT.Kummer` から到達する。
最小依存で使う場合は上記の各 owner module を直接 import する。

## 数学的契約

### 1. 代数的入れ子

`DkMath.Lib.Cosmic.powerCore d base step = (base + step)^d - base^d`。
引数順を `GTail d 1 step base` と区別する。`d = 0` とゼロ増分を除外しない。

`powerCore_split`、`powerCore_swap`、`powerCore_split_three` から
`mul_gtail_one_split`、`mul_gtail_one_swap` を導く。
`selected_nested_transport` は既存の選択分割の和から同じ基点冪を差し引き、二段入れ子に運ぶ。
Body 単独と差分 Core の同一視は行わない。

### 2. 分岐集中と位相0

`RamifiedPhasePacket` の入力は、原始 p 乗根、`λ = 1−ζ` の素元性、
剰余射 `R →+* ZMod p`、その核の λ 可除性との同値、および `ζ ↦ 1`。
FLT の反例・類群条件・降下を packet の入力にしていない。

`slope i = −∑ k < i, ζ^k` とするので、環内除算を使わず
`slope i * λ = ζ^i − 1` と `residue (slope i) = −i` を得る。
`quotient q y i = q + slope i * y` はすべて同じ `q,y` を共有する。
`λ ∤ y` のとき `distinguished q y` は唯一の λ 可除位相となる。

主定理は `powerCore_dvd_iff` と、その奇数冪和版 `sum_dvd_iff`：

```text
λ^(p+k) ∣ x^p+y^p  ↔  λ^k ∣ Q_i₀
```

`x+y=λq` と `λ ∤ y` を明示する。商や Core の非零性は要求しない。
`gtail_eq_product` は既存の非自明位相積を利用し、評価後の `q` を取り消さないため `q=0` でも成立する。

- 位相0：`gap_dvd_iff_of_distinguished_zero` が全追加深度を Gap `λq` に運ぶ。
  `not_dvd_gtail_of_distinguished_zero` により GN は λ^p で割れない。
- 非零位相：`gtail_dvd_iff_of_distinguished_ne_zero` が GN の λ^(p−1+k) 可除性を
  同じ一位相商の λ^k 可除性と同値にする。

### 3. 一般 State と実際の降下

名前空間は `DkMath.FLT.Kummer.RegularDescent`。
`State P m` は `x,y,z,epsilon` に加えて、`IsCoprime x y`、`λ ∤ y`、`λ ∤ z`、
`x^p+y^p=epsilon*(λ^m*z)^p` を保持する。

`Conditions P` は次の算術入力を明示する。

1. `Odd p`、`3 ≤ p`（素数性は型クラス引数）。
2. `(p : R) ∣ λ^(p−1)`。
3. `classGroupPTorsionFreeAt R p`。
4. `KummerUnitPowerCriterion R p`。

State 輸送にはさらに `IsDedekindDomain R` を使う。**PID や元の UFD は要求しない**。

証明の流れは次のとおり。

1. 正深度の式を剰余体へ送り、`λ ∣ x+y` と共通中心を得る。
2. 相異なる slope 差の単元性と元の原始性から、位相商を互いに素にする。
3. 全積から共通 λ^p を除去し、各商の主イデアルが p 乗であることを示す。
4. 積の非零性から各イデアル根の非零性を検査し、類群条件で主イデアル化する。
   既存の `exists_unit_mul_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt` を使う。
5. `IsIntegrallyClosed.pow_dvd_pow_iff` により、特別な根から λ^m を取り出す。
6. 同じ族から三つの相異なる位相を取り、既存 `phaseSource_three_term_relation` で
   重み付き p 乗方程式を作る。
7. 剰余逆元から Bezout 証人を作る。この工程も PID を仮定しない。
   Frobenius 合同と Kummer 単元条件で係数比だけを p 乗化する。
8. `normalize_weighted` により、同じ新しい `y,z` と原始性・非分岐性を備えた State を構成する。

`descent_step C m hm` は `hm : 1 ≤ m` の下で実際に
`Nonempty (State P (m+1)) → Nonempty (State P m)` を証明する。
遷移そのものを仮定に入れた provider ではない。
`no_state_one` と帰納法を組み合わせた `no_state C m hm` が正深度を排除する。

### 4. 具体的 provider と整数入口

- 3：既存の三次類数補題と `cubic_kummer_unit_power_criterion` を供給。
- 5：既存の五次類数補題と `quintic_kummer_unit_power_criterion` を供給。
- 7：既存の七次 PID と `concrete_kummer_unit_power_criterion` を供給。
  `State.toRegular` と `ofRegular` は状態不変条件をすべて輸送する。
  `State.ramified_depth_dvd_iff` は既存の `State.quotient` に対して R1 を与える。
  `descent_step_via_regular` は旧七次 `descent_step` を呼ばず一般降下を使う。

`initial_state_of_int_solution` は、標数0の環で整数の
`a^p+b^p=c^p`、`c≠0`、`IsCoprime a b`、`p ∣ c`、`p ∤ b` から
正深度 State を構成する。`not_int_solution_caseII` がこれを一般降下と接続する。
一般反例のすべてがこの向きになることや、Case I を排除したことは主張しない。

## 回帰と依存監査

- `DkMathTest/Lib/Cosmic/CoreNested.lean`：d=0、増分0、基点0、負整数、ZMod 5、
  任意の項選択、設計書で棄却された式の具体的な不成立。
- `DkMathTest/FLT/Kummer/RegularStateTransport.lean`：位相0／非零位相の分配、ゼロ Core、
  11・13 の具体的円分体、3・5・7 の一般 State 排除、深度0の実際の存在。
- `DkMathTest/FLT/Kummer/RegularTransportDependencyAudit.lean`：全新規公開宣言の公理監査と、
  核心根の型・opaque 本文・構造体 constructor を含む再帰依存監査。
  既存 FLT 完成定理、旧七次 `descent_step`／`no_state_one`、`sorryAx`、
  許可した論理基盤以外の公理への依存を拒否する。
  さらに一般冪抽出・単元補題が実際の依存に現れることを検査する。

通常の `lake build DkMath DkMath.FLT.Kummer`（10,549 jobs）、
`lake build DkMathTest`（11,440 jobs）、`lake env lean DkMathTest.lean`、
ルートのみを import するスモーク検証が合格した。
新規公開宣言75件は `propext`・`Classical.choice`・`Quot.sound` 以外の公理に依存しない。
既存ファイル由来の過去の警告と、新規定理の実際の依存は分けて監査した。

実行コマンドと短い監査結果は [検証証跡](evidence/validation.txt)、
スモーク入力は [RootSmoke.lean](evidence/RootSmoke.lean) に保存した。

## 残る境界

- 11・13 の具体的な類群 p-torsion-free 証明と Kummer 単元 criterion。
  現在のソースと同梱 Mathlib にこれらの provider は見当たらず、追加実装が必要。
- 一般 Case I の排除、原始整数反例の向き付け、自然数上の gcd 正規化との統合。
- 3・5 の既存完成経路を新しい一般 State に全面置換する作業。
- 11・13 の正深度全排除と最終 FLT。深度1の排除や位相回帰だけを完成と数えない。

元の設計書と議事録は設計・検討記録として保持し、この報告で実装済みの範囲を区別する。
