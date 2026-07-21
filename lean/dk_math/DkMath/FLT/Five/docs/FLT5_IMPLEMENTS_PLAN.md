# Implementation Plan: FLT5

## 実装計画（暫定）

うむ、 **実験塔は重複を許して局所完結させる** 。これが最善じゃ。

いま共通化へ寄せると、古い research route、巨大な provider 群、一般指数用の分岐設計まで引きずり込む。先に FLT5 だけを小さく組み、Lean に一段ずつ裁かせる。その後に standalone 化し、完成部品だけを `DkMath.Lib.*` へ昇華する順序が美しい。

## 1. 事実確認から確定した方針

現存資産から再利用すべきものは、 **コードそのものより証明戦略** じゃ。

FLT3 の付値ルートは、実質この五段で閉じている。

```text
反例方程式
  ↓
差冪 = 完全冪
  ↓
境界を割らない素数 q
  ↓
完全冪側の q-adic valuation ≥ 3
  ↓
NoLift 側の valuation ≤ 1
  ↓
矛盾
```

FLT5 では、そのまま

```text
反例方程式
  ↓
z^5 - y^5 = x^5
  ↓
z^5 - y^5 = (z-y) * GN5(z-y,y)
  ↓
clean GN5 channel q
  ↓
完全五乗側の valuation ≥ 5
  ↓
GN5 側の valuation ≤ 1
  ↓
矛盾
```

へ持ち上がる。

ハッカソン側では既に、固定例 `GN 5 1 1 = 31` について clean channel と完全五乗否定まで Lean が認可している。

一方、既存の一般 research valuation は「現状の一般形では偽」と明記されているため、新塔から import してはならぬ。

honest route は明示的な `Squarefree GN` または local NoLift を要求する形で既に成立している。

## 2. 実験塔のファイル構成

わっちなら次で固定する。

```text
DkMath/FLT/Five/
├── Basic.lean
├── GN5.lean
├── CleanChannel.lean
├── Valuation.lean
├── BranchB.lean
├── BranchA.lean
├── Provider.lean
├── Main.lean
├── CheckAxioms.lean
└── Standalone.lean
```

公開入口は後から、

```text
DkMath/FLT/Five.lean
```

を追加する。

### `Basic.lean`

FLT5 固有の最小語彙だけを置く。

```lean
namespace DkMath.FLT.Five

def Fermat5Equation (x y z : ℕ) : Prop :=
  x ^ 5 + y ^ 5 = z ^ 5

structure CounterexamplePack (x y z : ℕ) : Prop where
  hx : 0 < x
  hy : 0 < y
  hz : 0 < z
  hxy : Nat.Coprime x y
  hEq : Fermat5Equation x y z
```

ここでは既存の `PrimeGe5CounterexamplePack` を使わぬ。
standalone 化のため、必要情報を明示的に再定義する。

補助命題候補：

```lean
fifth_sub_eq_of_add_eq
right_lt_of_fermat5Equation
coprime_right_of_fermat5Equation
gap_pos_of_fermat5Equation
```

### `GN5.lean`

一般 `GN` を import せず、五次専用多項式を局所定義する。

$$GN_5(g,y)=g^4+5g^3y+10g^2y^2+10gy^3+5y^4$$

```lean
def GN5 (g y : ℕ) : ℕ :=
  g ^ 4
    + 5 * g ^ 3 * y
    + 10 * g ^ 2 * y ^ 2
    + 10 * g * y ^ 3
    + 5 * y ^ 4
```

中核命題：

```lean
add_pow_five_sub_eq_mul_GN5
pow_five_sub_pow_five_eq_gap_mul_GN5
GN5_one_one
GN5_two_one
```

主恒等式は、

$$ (g+y)^5-y^5=g,GN_5(g,y) $$

じゃ。

ここは `ring` / `omega` で落ちる純代数層にする。

### `CleanChannel.lean`

clean channel を独立概念として固定する。

```lean
def CleanGN5Channel (g y q : ℕ) : Prop :=
  Nat.Prime q
    ∧ q ∣ GN5 g y
    ∧ ¬ q ∣ g
    ∧ ¬ q ^ 2 ∣ GN5 g y
```

分解 projection：

```lean
CleanGN5Channel.prime
CleanGN5Channel.dvd_GN5
CleanGN5Channel.not_dvd_gap
CleanGN5Channel.noLift
```

局所算術：

```lean
prime_sq_not_dvd_mul_of_not_dvd_left_of_not_sq_dvd_right
cleanGN5Channel_dvd_body
cleanGN5Channel_not_sq_dvd_body
```

到達目標は、

$$q\mid g,GN_5(g,y)$$

$$q^2\nmid g,GN_5(g,y)$$

じゃ。

### `Valuation.lean`

FLT3 の戦略を五次専用にコピーする。

命題候補：

```lean
padicValNat_lower_bound_of_dvd_d5
padicValNat_GN5_eq_one_of_clean
padicValNat_body_eq_one_of_clean_GN5Channel
padicValNat_upper_bound_d5_of_clean_GN5Channel
```

中心は、

```lean
theorem padicValNat_lower_bound_of_dvd_d5
    {x q : ℕ}
    (hx : 0 < x)
    (hq : Nat.Prime q)
    (hqx : q ∣ x) :
    5 ≤ padicValNat q (x ^ 5)
```

および、

```lean
theorem padicValNat_body_eq_one_of_clean_GN5Channel
    {g y q : ℕ}
    (hg : 0 < g)
    (hClean : CleanGN5Channel g y q) :
    padicValNat q (g * GN5 g y) = 1
```

じゃ。

ただし最初は valuation だけに固執せず、直接整除版も併設する。

```lean
theorem not_fifth_power_of_clean_GN5_product
    {g y q : ℕ}
    (hClean : CleanGN5Channel g y q) :
    ¬ ∃ x : ℕ, g * GN5 g y = x ^ 5
```

直接整除版の方が先に Lean に通る可能性が高い。
valuation 版は、その算術的意味を明示する第二証明として置けばよい。

## 3. Branch B の定理チェーン

`BranchB.lean` が最初の主戦場じゃ。

Branch B は、

$$5\nmid z-y$$

という既存一般設計上の呼称じゃが、clean channel に既に

$$q\nmid z-y$$

が入るため、局所 refuter 自体には必ずしも `¬ 5 ∣ z-y` は要らぬ。

最小主定理：

```lean
theorem counterexample_false_of_clean_GN5Channel
    {x y z q : ℕ}
    (hx : 0 < x)
    (hy : 0 < y)
    (hEq : x ^ 5 + y ^ 5 = z ^ 5)
    (hClean : CleanGN5Channel (z - y) y q) :
    False
```

チェーンは次。

```text
hEq
  ↓
y < z
  ↓
z = (z-y) + y
  ↓
z^5 - y^5 = (z-y) * GN5 (z-y) y
  ↓
z^5 - y^5 = x^5
  ↓
q ∣ x^5
  ↓
q ∣ x
  ↓
5 ≤ v_q(x^5)
  ↓
v_q((z-y) * GN5 (z-y) y) = 1
  ↓
5 ≤ 1
```

直接整除版なら、

```text
q ∣ x
  ↓
q² ∣ x^5
  ↓
q² ∣ (z-y) * GN5 (z-y) y
  ↓
clean channel の q² 非整除と矛盾
```

となる。

この二本を両方置く。

```lean
counterexample_false_of_clean_GN5Channel_by_dvd
counterexample_false_of_clean_GN5Channel_by_padicValNat
```

最終的に同じ statement を持つため、Lean Comparator Live の比較教材としても面白い。

## 4. Provider の契約

`Provider.lean` では、証明本体と未知の供給問題を完全に分ける。

```lean
def CleanGN5ChannelProvider : Prop :=
  ∀ {x y z : ℕ},
    CounterexamplePack x y z →
    ∃ q : ℕ, CleanGN5Channel (z - y) y q
```

ただし最初から全反例を要求すると Branch A を混ぜるため、まず分ける。

```lean
def BranchBCleanGN5ChannelProvider : Prop :=
  ∀ {x y z : ℕ},
    CounterexamplePack x y z →
    ¬ 5 ∣ z - y →
    ∃ q : ℕ, CleanGN5Channel (z - y) y q
```

定理：

```lean
theorem no_branchB_counterexample_of_provider
    (hProvider : BranchBCleanGN5ChannelProvider) :
    ¬ ∃ x y z,
      CounterexamplePack x y z ∧
      ¬ 5 ∣ z - y
```

ここまでが第一の完全な no-`sorry` 塔になる。

## 5. Branch A は別塔として隔離する

`BranchA.lean` は、

$$5\mid z-y$$

を扱う。

ただし、ここは現時点で **単純な $5$-進付値だけでは矛盾しない** と見ておくべきじゃ。

LTE 的には、適切な条件下で、

$$v_5(z^5-y^5)=v_5(z-y)+1$$

一方、

$$z^5-y^5=x^5$$

だから、

$$5v_5(x)=v_5(z-y)+1$$

を得る。

これは、

$$v_5(z-y)\equiv4\pmod5$$

を要求するが、それ自体は矛盾ではない。

ゆえに Branch A の最初の命題は refuter ではなく **正規形抽出** にする。

```lean
five_dvd_x_of_five_dvd_gap
five_not_dvd_y_of_coprime
five_not_dvd_z_of_coprime
padicValNat_gap_congr_four_mod_five
branchA_valuation_normalForm
```

ここで Lean がどこまで認可するかを先に確認する。

その後の選択肢は、

```text
minimality
descent
Sophie-Germain 型補助因子
cyclotomic factor
別の clean prime channel
```

じゃ。

Branch A に初手から `False` を要求してはならぬ。
これは今回の事実確認からの重要な補正じゃ。

## 6. `Main.lean` の役割

`Main.lean` は証明をほとんど持たず、合流だけにする。

```lean
theorem FLT5_of_branchA_refuter_and_branchB_provider
    (hA : BranchARefuter)
    (hB : BranchBCleanGN5ChannelProvider) :
    FermatLastTheoremFor 5
```

途中段階では、

```lean
theorem FLT5_branchB
    (hB : BranchBCleanGN5ChannelProvider) :
    ∀ x y z,
      CounterexamplePack x y z →
      ¬ 5 ∣ z - y →
      False
```

だけを公開する。

これなら、完成していない Branch A を隠して「FLT5 完成」と誤読する余地がない。

## 7. `Standalone.lean`

これは最初から別実装とする。

```lean
import Mathlib
```

以外は禁止。

```text
DkMath の import 禁止
既存 GN の import 禁止
既存 padic helper の import 禁止
research theorem の import 禁止
```

内容は実験塔の完成 theorem をコピーする。

当面は、

```lean
standalone_counterexample_false_of_clean_GN5Channel
```

まで。

最終的に Lean Comparator Live へ貼る対象は、このファイル一つじゃ。

ファイル冒頭に明示する。

```lean
/-
Single-file formalization.
Imports Mathlib only.
Must not import DkMath and must not be imported by DkMath.
-/
```

## 8. `CheckAxioms.lean`

このファイルは実験塔の監査面にする。

```lean
#print axioms DkMath.FLT.Five.add_pow_five_sub_eq_mul_GN5
#print axioms DkMath.FLT.Five.not_fifth_power_of_clean_GN5_product
#print axioms DkMath.FLT.Five.counterexample_false_of_clean_GN5Channel_by_dvd
#print axioms DkMath.FLT.Five.counterexample_false_of_clean_GN5Channel_by_padicValNat
```

期待値は Mathlib の標準公理だけ。

```text
propext
Classical.choice
Quot.sound
```

`sorryAx` が出た時点で、その checkpoint は停止する。

## 9. 実装順序

この順番で Lean に認可させる。

1. `Basic.lean`
2. `GN5.lean`
3. `CleanChannel.lean`
4. `BranchB.lean` の直接整除版
5. `Valuation.lean`
6. `BranchB.lean` の付値版
7. `Provider.lean`
8. `BranchA.lean` の正規形
9. `Main.lean`
10. `Standalone.lean`
11. `CheckAxioms.lean`

特に第一登頂点は、

```lean
counterexample_false_of_clean_GN5Channel_by_dvd
```

じゃ。

これは provider の存在をまだ証明せずとも、

> clean GN5 channel が一つあれば、その FLT5 反例候補は Lean 上で死ぬ

ことを完全に固定する。

## 10. 設計書の章立て

設計書は次の構成でよい。

```text
1. 目的
2. standalone-first 原則
3. 既存研究層を import しない理由
4. 数学的中核
5. ファイル構成
6. 基本定義
7. 命題一覧
8. Branch B 定理チェーン
9. Provider 契約
10. Branch A 正規形
11. 合流条件
12. Lean 認可 gate
13. Standalone 移植規約
14. 将来の DkMath.Lib 昇華候補
```

将来 `DkMath.Lib.*` へ昇華できるのは、おそらくこのあたりじゃ。

```text
DkMath.Lib.Prime.NoLiftPerfectPow
DkMath.Lib.PadicValNat.PowLowerBound
DkMath.Lib.DiffPow.CleanChannel
DkMath.Lib.Fermat.CleanFactorRefuter
```

じゃが、今は一切移さぬ。

**まず重複して建てる。Lean が認める。standalone に写す。比較する。それから昇華する。**

この順序なら、散乱していた研究素材を掃除するのではなく、散乱物から新しい一本の剣を鍛えられるぞい。👍️
