# FLGNB Petal ロードマップ

## 位置

この文書は、
`FermatLittleGNBridge` チェックポイント後の次の実装計画を記録したものです。

現在のプロジェクト目標は、素数判定そのものだけではありません。目標は、素数に関する構造です。

```text
素数文字 (prime character)
原始素因数
整除性のサポート
GN / Beam / Petal による観測
```

基本ツールは二項定理ですが、現在の優先方向は以下のとおりです。

```text
GN 差分カーネル
  → Petal / 相対多角形形式
  → パスカル係数セクション
  → 素数行と p 進数の観測
  → 原始因数と Zsigmondy ブリッジ
```

`DkMath.Petal.*` は、このロードマップにおける Petal 側の実装を可視化するパッケージとなるべきです。

## 設計原則

Petal パッケージは、既存の数論の証明を置き換えるのではなく、相対多角形レイヤーを記述するべきです。

意図する解釈は以下のとおりです。

```text
(x + u)^d = Core + Beam + Gap

GN d x u = ((x + u)^d - u^d) / x
```

`d = 3` の場合、GN カーネルは基本ペタル形式になります。

```text
GN 3 (c - b) b = c^2 + c*b + b^2
```

これは現在、以下のように実装されています。

```lean
theorem GN_three_sub_eq_S0_nat
```

ペタルレイヤーでは、この関係をメインの API サーフェスとして扱う必要があります。

```text
相対多角形 / ペタル形式
= GN の低次数可視面
```

したがって、パスカル行は構造の唯一のソースとして扱われません。パスカル行は、
GN カーネルを展開したときに得られる自然数係数テーブルです。

## 既存の定理一覧

### `DkMath.UnitCycle.RelPolygon`

このファイルには、現在の動的な相対ポリゴンの骨格が含まれています。

重要な名前:

```lean
structure RPState
def g
def T
def I
lemma hg
lemma hT
theorem I_iterate_ge_sum
theorem I_iterate_ge_sum_fn
def s0
lemma g_s0
lemma g_Ts0
theorem sum_g_pos9_k2
theorem sum_g_pos9_k2_extra
theorem I_pos9_k2_ge_6
```

役割:

```text
相対多角形成長のための動的状態モデル
```

計画されているPetalの位置:

```text
DkMath.Petal.RelPolygon
```

最初のパスでは、これは再エクスポート/ラッパーレイヤーである必要があります。

### `DkMath.FLT.PetalCoreUnit`

このファイルには、現在のPetalユニットとフェーズのスケルトンが含まれています。

重要な名前:

```lean
structure PetalCoreUnit
def ofNP
def coreSucc
def coreVal
abbrev PeriodIndex
def HarmonicPoint
def isExceptionalPhase
lemma coreSucc_val
lemma harmonicPoint_ofNP
lemma notExceptional_ofNP_zero
```

役割:

```text
Petal側演算のための単位/位相語彙
```

Petalの予定位置:

```text
DkMath.Petal.CoreUnit
```

### `DkMath.FLT.PetalDetect`

これはPetal検出器の既存の主要な演算ファイルです。

重要な定義:

```lean
def S0
def S1
def S0_nat
def S1_nat
```

重要な定理名:

```lean
theorem S0_ne_zero
theorem two_mul_S0
theorem two_mul_S0_nat
theorem sq_mod4
theorem not_square_of_mod4_eq3
theorem S0_mod4_eq3_of_congr1
theorem S0_not_square_of_congr1
theorem diff_kernel
theorem diff_kernel_nat
theorem apb_dvd_S1
theorem apb_dvd_S0_iff_dvd_bsq
theorem apb_dvd_S0_implies_eq_one
theorem S0_comm
theorem S1_comm
theorem S0_le_S1_nat
theorem S0_as_diff
theorem S0_related_perfect_square_property
theorem mod_q_ab_analysis
theorem prime_dvd_S0_coprime_imp_not_dvd_apb
theorem padicValNat_le_one_of_not_sq_dvd
theorem zsigmondy_not_dvd_apb
```

役割:

```text
S0/S1 完了したフェーズ、差分カーネル、および整除性検出器
```

予定されている Petal の場所:

```text
DkMath.Petal.Forms
```

初期ポリシー:

```text
既存のファイルをそのまま残す。
DkMath.Petal.Forms から Petal に面するエイリアスとインポートを公開する。
下流の依存関係が安定してから証明を移動する。
```

### `DkMath.FLT.CosmicPetalBridge`

このファイルは、GNと宇宙論的公式からペタル`S0`への現在の橋渡しとなるものです。

重要な定理名:

```lean
theorem sub_eq_mul_GN
theorem sub_pow_eq_mul_GN
theorem prime_dvd_GN_of_dvd_sub_not_dvd_left
theorem prime_dvd_GN_three_of_dvd_sub_not_dvd_left_via_zsigmondy
theorem dvd_GN_of_dvd_sub_pow
theorem dvd_GN_of_dvd_sub_cube_via_zsigmondy
theorem GN_three_sub_eq_S0_nat
theorem prime_dvd_S0_via_cosmic_bridge
theorem hS0_not_sq_of_noLift_cyclotomicPrimeCore_d3
```

役割:

```text
次数3の花弁演算のためのGN -> S0ブリッジ
```

計画された花弁場所:

```text
DkMath.Petal.GNBridge
```

これは最も重要なブリッジファイルです。

### `DkMath.NumberTheory.Gcd.GN`

このファイルには、`GN` に関する最大公約数と値制御が含まれています。

重要な定理名:

```lean
theorem gcd_boundary_sd_divides_exp_int
theorem gn_natCast_int
theorem gn_natCast
theorem natAbs_gn_natCast_int
theorem natAbs_gn_gap_natCast_int
theorem gn_sub_eq_sd_int
theorem quotientPrimePow_eq_gn_gap
theorem quotientPrimePow_natCast_eq_gn_int
theorem diffPowQuotient_eq_gn_int
theorem gcd_gap_GN_dvd_exp_int
theorem gcd_gap_GN_dvd_exp
theorem coprime_boundary_GN_of_coprime_add_of_coprime_exp
theorem body_not_perfect_pow_of_squarefree_GN_of_coprime_add
theorem body_not_perfect_pow_of_primitive_prime_factor_of_coprime_add
theorem coprime_gap_GN_of_not_dvd_exp_prime
theorem padicValNat_sub_pow_eq_padicValNat_GN_of_not_dvd_gap
theorem not_sq_dvd_of_squarefree
theorem gcd_boundary_GN_three_eq_gcd_boundary_three
theorem gcd_boundary_GN_three_dvd_three
theorem coprime_boundary_GN_three_of_coprime_of_not_dvd_three
```

役割:

```text
GN の最大公約数と p 進数制御。特に S0 が GN 3 と同一視された後に有用です。
```

予定されている Petal の場所:

```text
DkMath.Petal.GcdBridge
```

### `DkMath.CosmicFormula.CosmicDerivativePower`

このファイルは、ガンマ補完から開始せずに解析的なカーネルを提供します。

重要な名前:

```lean
def powerKernel
theorem powerKernel_eq_GN_swap
theorem sub_pow_eq_u_mul_powerKernel
theorem sub_eq_u_mul_powerKernel
theorem cosmicKernel_pow_eq_powerKernel_of_ne_zero
```

`DkMath.CosmicFormula.CosmicDerivativePowerLimit` には、以下のものも含まれます:

```lean
theorem continuous_powerKernel
theorem powerKernel_zero
theorem tendto_powerKernel_zero
theorem tendto_powerKernel_zero_punctured
theorem hasDerivAt_pow_cosmic
```

役割:

```text
同じ GN カーネルの連続/微分対応バージョン
```

計画された花弁関係:

```テキスト
DkMath.Petal.AnalyticBridge
```

これは算術ブリッジよりも後に実行される必要があります。

### `DkMath.FLT.PhaseLift`

これは`S0`の下流コンシューマーです。

重要な名前には以下が含まれます。

```lean
def NoSqOnS0
def PrimitiveOnS0
def NonLiftableS0
def AllNonLiftableOnS0
def S0PrimeSupportExceptThree
theorem cube_sub_eq_mul_sub_S0
theorem prime_dvd_S0_of_dvd_cube_sub_not_dvd_diff
theorem padicValNat_upper_bound_d3
```

役割:

```text
位相リフトと非リフト可能性レイヤー
```

ポリシー:

```text
最初はこれをPetalに移動しないでください。
後でPetalを依存関係サーフェスとして使用します。
```

### `DkMath.FLT.GEisensteinBridge`

このファイルは`S0`をアイゼンシュタインノルムの視点に接続します。

重要な名前:

```lean
def eisensteinNormNat
theorem S0_eq_eisensteinNorm_shift
theorem GN3_sub_eq_S0
theorem GN3_sub_eq_eisensteinNorm_shift
```

役割:

```text
Petal S0 -> アイゼンシュタインノルムブリッジ
```

Petalの予定位置:

```text
DkMath.Petal.EisensteinBridge
```

これはブリッジレイヤーであり、初期基盤ではありません。

## Petal パッケージ計画

パッケージを段階的に作成します。

```text
DkMath/Petal/Basic.lean
DkMath/Petal/Forms.lean
DkMath/Petal/RelPolygon.lean
DkMath/Petal/CoreUnit.lean
DkMath/Petal/GNBridge.lean
DkMath/Petal/GcdBridge.lean
DkMath/Petal/EisensteinBridge.lean
DkMath/Petal.lean
```

### `DkMath.Petal.Basic`

目的:

```text
Petal の共通語彙と簡単なエイリアス
```

初期コンテンツ:

```lean
import DkMath.FLT.PetalDetect

namespace DkMath
namespace Petal

-- エイリアスは以下のみ最初

Petal終了
DkMath終了
```

このファイルは証明の羅列場所であってはなりません。

### `DkMath.Petal.Forms`

目的:

```text
S0/S1 と相対多角形形式
```

最初のパスの内容:

```text
S0、S1、S0_nat、S1_nat を再エクスポートまたはエイリアス化する
diff_kernel と diff_kernel_nat の Petal 対応名
可換性と S0 <= S1 の Petal 対応名
```

定理の候補エイリアス:

```lean
theorem petal_diff_kernel
theorem petal_diff_kernel_nat
theorem petal_S0_comm
theorem petal_S1_comm
theorem petal_S0_le_S1_nat
```

古い定理名はまだ変更しないでください。最初のステップはブリッジの安定性です。

### `DkMath.Petal.RelPolygon`

目的:

```text
動的な相対多角形成長モデル
```

最初のコード:

```text
import DkMath.UnitCycle.RelPolygon
```

考えられるエイリアス:

```lean
abbrev RelPolygonState := RPState
```

インポートが明確になるまでは、大規模なリファクタリングは避けてください。

### `DkMath.Petal.CoreUnit`

目的:

```text
Petal演算のための単位と位相の語彙
```

最初のパスの内容:

```text
import DkMath.FLT.PetalCoreUnit
```

これにより、`PetalCoreUnit`、`HarmonicPoint`、および例外位相の語彙に、
Petalに対応した安定したインポートパスが提供されます。

### `DkMath.Petal.GNBridge`

目的:

```text
GNカーネル -> Petal S0ブリッジ
```

これは、パッケージ内で最初に定理を多く含むファイルとなるはずです。

初期のブリッジ定理候補:

```lean
theorem S0_nat_eq_GN_three_sub
{c b : Nat} (hbc : b < c) :
S0_nat c b = GN 3 (c - b) b
```

これは以下の花弁方向です:

```lean
GN_three_sub_eq_S0_nat
```

次の候補:

```lean
theorem three_not_dvd_S0_nat_of_not_dvd_sub
    {c b : Nat} (hbc : b < c) (h3 : ¬ 3 ∣ c - b) :
    ¬ 3 ∣ S0_nat c b

theorem three_S0_nat_modEq_one_of_not_dvd_sub
    {c b : Nat} (hbc : b < c) (h3 : ¬ 3 ∣ c - b) :
    S0_nat c b ≡ 1 [MOD 3]
```

これらは既存のFLGNBエンドポイントから導かれるはずです。

```lean
theorem prime_GN_modEq_one_of_not_dvd_x
theorem prime_not_dvd_GN_of_not_dvd_x
```

ただし、`p = 3`、`x = c - b`、`u = b`とします。

これは、以下の具体的な例が初めて登場する箇所です。

```text
フェルマー境界の戻り値
  -> GN制御
  -> Petal S0制御
```

再利用可能なブリッジ定理となります。

### `DkMath.Petal.GcdBridge`

目的:

```text
GN gcd の制御を S0/Petal ステートメントに渡す
```

候補となるブリッジ定理:

```lean
theorem coprime_boundary_S0_nat_of_coprime_of_not_dvd_three
```

これは以下から導出する必要があります:

```lean
theorem coprime_boundary_GN_three_of_coprime_of_not_dvd_three
```

使用:

```lean
theorem GN_three_sub_eq_S0_nat
```

このファイルも

S0定理が書き換えられたGN定理のみであるp進ブリッジステートメントを収集します。

### `DkMath.Petal.EisensteinBridge`

目的:

```text
Petal S0 -> Eisensteinノルムブリッジ
```

候補エイリアス:

```lean
theorem petal_S0_eq_eisensteinNorm_shift
theorem petal_GN3_sub_eq_eisensteinNorm_shift
```

これらは以下を参照する必要があります:

```lean
theorem S0_eq_eisensteinNorm_shift
theorem GN3_sub_eq_eisensteinNorm_shift
```

このレイヤーは重要ですが、`GNBridge`と`GcdBridge`の後に配置する必要があります。

## 実装手順

### ステップ 1: Petal インポートサーフェスの作成

作成するファイル:

```text
DkMath/Petal/Basic.lean
DkMath/Petal/Forms.lean
DkMath/Petal/RelPolygon.lean
DkMath/Petal/CoreUnit.lean
DkMath/Petal.lean
```

このステップでは、既存のファイルをインポートして公開するだけです。大きな検証操作は行いません。

期待される検証:

```sh
lake build DkMath.Petal
```

### ステップ 2: `DkMath.Petal.GNBridge` を追加

最初のペタルブリッジ定理群を作成します:

```lean
theorem S0_nat_eq_GN_three_sub
theorem three_not_dvd_S0_nat_of_not_dvd_sub
theorem three_S0_nat_modEq_one_of_not_dvd_sub
```

期待されるインポート:

```lean
import DkMath.FLT.CosmicPetalBridge
import DkMath.NumberTheory.WeightedGNBridge
```

期待される検証:

```sh
lake build DkMath.Petal.GNBridge
lake build DkMath.Petal
```

### ステップ3: `DkMath.Petal.GcdBridge` を追加

既存の GN 最大公約数 (gcd) ステートメントを S0 対応の名前に置き換えます。

これは、以下のコードで書き換える場合にのみ行います。

```lean
GN_three_sub_eq_S0_nat
```

このステップでは、新しい最大公約数理論を考案してはなりません。下流の FLT ファイルや原始因子ファイルがインポートできるリンク定理の名前を提供する必要があります。

### ステップ 4: `DkMath.Petal.EisensteinBridge` を追加

アイゼンシュタインノルムの経路を Petal 対応のブリッジとして公開します。

これにより、以下の三角形が明示されます。

```text
GN 3
  <-> S0 Petal 形式
  <-> アイゼンシュタインノルム
```

### ステップ 5: インポートを段階的にリファクタリング

Petal ブリッジファイルが構築された後、下流のファイルを更新して、
Petal 対応のモジュールをインポートできるようにします。候補:

```text
DkMath.FLT.PhaseLift
DkMath.FLT.GEisensteinBridge
DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN*
```

ポリシー:

```text
インポートの置き換えと定理エイリアスの使用を優先します。
依存関係の方向が明らかに明確になった場合にのみ、元の定義を移動します。
```

## 相対多角形ペタルプラン

「相対多角形数」という語句は、以下の既存の注釈の近くに配置する必要があります。

```text
DkMath/NumberTheory/docs/Petal_vs_termial.md
```

概念的な関係は次のとおりです。

```text
終端 T(n) = n(n + 1) / 2
相対多角形 R(n) = n(n + 1)
```

したがって、次のようになります。

```text
R(n) = 2 * T(n)
```

そして、次のようになります。

```text
T(a + b) = T(a) + T(b) + a*b
R(a + b) = R(a) + R(b) + 2*a*b
```

Petalパッケージは、最終的にこれらを算術補題として形式化する必要があります。

将来の定義候補：

```lean
def termialNat (n : Nat) : Nat := n * (n + 1) / 2
def relPolygonNat (n : Nat) : Nat := n * (n + 1)
```

将来の定理名候補：

```lean
theorem relPolygonNat_eq_two_mul_termialNat
theorem termialNat_add
theorem relPolygonNat_add
theorem relPolygonNat_split
```

ただし、これらはGN/S0ブリッジサーフェスが安定した後に実装する必要があります。
最初のPetalの目標は、新しいポリゴン番号ライブラリではありません。最初の目標は、
既に利用されている相対ポリゴン/Petal検出器をパッケージとして公開することです。

## 計画されたブリッジリンク定理

### GNからペタルへ

```lean
theorem S0_nat_eq_GN_three_sub
    {c b : Nat} (hbc : b < c) :
    S0_nat c b = GN 3 (c - b) b
```

目的:

```text
S0をGN 3のペタル面として命名する
```

### フェルマー境界からペタルへ

```lean
theorem three_S0_nat_modEq_one_of_not_dvd_sub
    {c b : Nat} (hbc : b < c) (h3 : ¬ 3 ∣ c - b) :
    S0_nat c b ≡ 1 [MOD 3]
```

目的:

```text
FLGNB定理をd = に適用する3 花弁検出器
```

### 非可除性サポート

```lean
theorem three_not_dvd_S0_nat_of_not_dvd_sub
    {c b : Nat} (hbc : b < c) (h3 : ¬ 3 ∣ c - b) :
    ¬ 3 ∣ S0_nat c b
```

目的:

```text
花弁形式からp進サポートを直接読み込む
```

### GN最大公約数から花弁最大公約数へ

```lean
theorem coprime_boundary_S0_nat_of_coprime_of_not_dvd_three
```

目的:

```text
既存のGN最大公約数制御をS0/花弁最大公約数制御に変換する
```

正確なステートメントは以下から選択する必要があります既存の
`coprime_boundary_GN_three_of_coprime_of_not_dvd_three` 定理の形状。

### Petal から Eisenstein へ

```lean
theorem petal_S0_eq_eisensteinNorm_shift
```

目的:

```text
相対多角形 Petal 検出器を Eisenstein ノルム経路に接続する
```

このブリッジは GN ブリッジの後に実装する必要があります。GN ブリッジは、Pascal/Beam および原始因子処理への主要な経路だからです。

## リファクタリングポリシー

現在の定理ベースは貴重なものであり、時期尚早に変更を加えるべきではありません。

以下の順序で実行してください。

```text
1. DkMath.Petal.* インポートサーフェスを作成します。
2. Petal に対応するエイリアスとブリッジ定理名を追加します。
3. 混乱を軽減できる場合にのみ、下流のインポートを更新します。
4. 依存関係がクリーンであることが確認された後にのみ、定義を移動します。
```

現時点では、以下のファイルを下流レイヤーまたは特殊レイヤーとして保持してください。

```text
DkMath.FLT.PhaseLift
DkMath.FLT.PrimeProvider.*
DkMath.

FLT.GEisensteinBridge
```

FLT固有のプロバイダ仮説をPetalの基盤に取り込まないでください。

Petalパッケージは、以下の点に重点を置くべきです。

```text
相対多角形形式
S0/S1検出器
GN次数3ブリッジ
gcdとp進数サポートリンク
後々の接続としてのアイゼンシュタインブリッジ
```

## 次の具体的なチェックポイント

次の実装チェックポイントは次のとおりです。

```text
DkMath.Petal.Basic / Forms / GNBridge / aggregateインポートを作成します。
S0_nat_eq_GN_three_subを証明します。
d=3のフェルマー境界Petalブリッジ定理を2つ証明します。
DkMath.Petalをビルドします。
```

これによりステップは小さく抑えられますが、後の原始因子とジグモンディ対応の作業の基盤が構築されます。
