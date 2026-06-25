# Lean 実装計画

## DHNT DAS Note

[Note](/lean/dk_math/DkMath/DHNT/docs/DHNT_DAS_Note.md)

## 設計考察

実装計画としては、Python をそのまま移植せず、Lean では「列を作るプログラム」より先に「項の定義」と「同値補題」を中心に置くのが良いです。

**方針**

`das_demo.py` の本質は次です。

```text
classic:  a + d * i
dynamic:  a + ln(e^k) * i * d
        = a + k * i * d
        = a + (d * k) * i
```

Lean らしく書くなら、`ln (exp k)` を主定義にしない方がよいです。これは解析的な表示であって、数列の本体は単に「公差を `k` 倍した等差数列」です。したがって主定義は代数的に置き、必要なら `Real.log (Real.exp k) = k` を別補題で接続します。

**配置案**

新規モジュール:

```text
lean/dk_math/DkMath/DHNT/DynamicArithmeticSequence.lean
```

必要なら入口に import 追加:

```text
lean/dk_math/DkMath/DHNT.lean
```

テスト・利用例:

```text
lean/dk_math/DkMathTest/DHNT.lean
```

または既存テスト構成が薄ければ、まず本体ファイル内の `example` だけで固定してもよいです。

**定義案**

中心は `List` 生成ではなく、まず第 `i` 項です。

```lean
namespace DkMath.DHNT

def arithmeticTerm (a d : R) (i : ℕ) : R :=
  a + (i : R) * d

def dynamicStep (d k : R) : R :=
  d * k

def dynamicTerm (a d k : R) (i : ℕ) : R :=
  a + (i : R) * dynamicStep d k

def dynamicTermK (a step : R) (i : ℕ) : R :=
  a + (i : R) * step

def dynamicSequence (a d k : R) (n : ℕ) : List R :=
  (List.range n).map fun i => dynamicTerm a d k i
```

型クラスは最初は `R` を `Semiring` または `Ring` にします。Python の小数例まで自然に扱うなら、実例は `ℚ` を推奨します。`Float` は Lean の証明対象としては扱いにくいので、丸めの再現は主目的から外すのがよいです。

**証明する補題**

最初の Lean 化で入れるべき補題はこの程度で十分です。

```lean
theorem dynamicTerm_eq_arithmeticTerm :
  dynamicTerm a d k i = arithmeticTerm a (d * k) i

theorem dynamicTermK_eq_dynamicTerm :
  dynamicTermK a (d * k) i = dynamicTerm a d k i

theorem dynamicTerm_one :
  dynamicTerm a d 1 i = arithmeticTerm a d i

theorem dynamicTerm_zero_scale :
  dynamicTerm a d 0 i = a

theorem dynamicTerm_zero_diff :
  dynamicTerm a 0 k i = a

theorem dynamicTerm_succ :
  dynamicTerm a d k (i + 1) = dynamicTerm a d k i + d * k
```

これで Python の `dynamic_arithmetic_sequence_c`、`dynamic_arithmetic_sequence_d`、`dynamic_arithmetic_sequence_k` が同じ列を返す、という主張を Lean 上では補題として表現できます。

**解析表示の扱い**

`ln(e^k)` は本体定義ではなく、Real 専用の橋渡しにします。

```lean
def analyticScale (k : ℝ) : ℝ :=
  Real.log (Real.exp k)

theorem analyticScale_eq (k : ℝ) :
  analyticScale k = k := by
  simp [analyticScale]
```

その上で、

```lean
theorem dynamicTerm_real_log_exp :
  a + (i : ℝ) * (d * Real.log (Real.exp k))
    = dynamicTerm a d k i
```

のような補題を置けば、Python の説明文とも対応します。

**デモの Lean 化**

Python の出力例は `#eval` ではなく、まず `example` で固定します。

```lean
example :
  dynamicSequence (1 : ℚ) 2 1 10 =
    [1, 3, 5, 7, 9, 11, 13, 15, 17, 19] := by
  native_decide

example :
  dynamicSequence (3 : ℚ) 5 (102 / 100) 10 =
    [3, 81 / 10, 66 / 5, 183 / 10, 117 / 5,
     57 / 2, 168 / 5, 387 / 10, 219 / 5, 489 / 10] := by
  native_decide
```

Python の `round(…, 2)` に寄せる必要がある場合は、第二段階で `Rat` 用の「小数第2位に切り捨て/丸め」関数を別モジュールにします。ただし、最初から丸めを混ぜると数列の数学的構造が見えにくくなるので、Lean らしさを優先するなら非丸めの有理数列から始めるべきです。

**実装ステップ**

1. `DynamicArithmeticSequence.lean` を作り、`arithmeticTerm` / `dynamicStep` / `dynamicTerm` / `dynamicSequence` を定義する。
2. `dynamicTerm = arithmeticTerm a (d*k)` を中心補題として証明する。
3. `k = 1`、`k = 0`、`d = 0`、`succ` の基本補題を追加する。
4. `ℚ` の具体例で Python デモ相当を `example` として固定する。
5. 必要なら `ℝ` 専用に `Real.log (Real.exp k)` との接続補題を追加する。
6. `lake build DkMath.DHNT.DynamicArithmeticSequence` で検証する。

この順番なら、Python のデモを「実行スクリプト」から「定義、同値、退化ケース、具体例」に変換でき、Lean 側で後から定理に接続しやすくなります。

## KUS, Units との接続

`DkMath.KUS.*` / `DkMath.Units.*` を見ると、DAS は単独の数列モジュールではなく、次の三層に分けるのが Lean らしいです。

**拡張設計**

1. **係数層 DAS**
   まず `ln` / `exp` なしで、

   ```lean
   term a d k i = a + (i : C) * (d * k)
   ```

   を定義します。ここでは `C` は `Nat` ではなく、まず `Rat` / `Int` / `ℝ` / 一般 `Semiring` 対応にするのがよいです。主定理は「dynamic は公差 `d*k` の通常の等差列」とする。

2. **KUS/GKUS 層**
   既存の [DkMath.KUS.Coeff.lean](/lean/dk_math/DkMath/KUS/Coeff.lean) に `GKUS C U Blueprint` があります。DAS の `k` は support 変換ではなく係数変換なので、`KUS.ScaleSpec.scaleKUS` ではなく `GKUS` の `coeff` 側に載せます。
   つまり、

   ```lean
   gDynamicTerm support a d k i : GKUS C U Blueprint
   ```

   を `mkGWith (a + i * (d*k)) support` として定義し、以下を証明する設計です。

   ```lean
   toCoeff (gDynamicTerm s a d k i) = a + (i : C) * (d * k)
   extract_g (gDynamicTerm s a d k i) = s
   gDynamicTerm s a d 1 i = gArithmeticTerm s a d i
   gDynamicTerm s a d k i = gArithmeticTerm s a (d*k) i
   ```

3. **Units/NP 層**
   [DkMath.Units.NPUnit.lean](/lean/dk_math/DkMath/Units/NPUnit.lean) は `N/P` の半ステップ格子です。これは DAS の「離散インデックス `i`」や「半ステップ版の動的等差列」に接続できます。
   ただし初期実装では `NP` を主定義に混ぜず、第二段階の例として、

   ```lean
   npDynamicVal a d k i := a + val(iterate succ i start) * (d*k)
   ```

   のような bridge にするのが安全です。

**置き場所案**

本体:

```text
lean/dk_math/DkMath/DHNT/DynamicArithmeticSequence.lean
```

KUS 接続:

```text
lean/dk_math/DkMath/KUS/DynamicArithmeticSequence.lean
```

または小さく始めるなら、最初は `DHNT` 側に係数層だけ置き、KUS 接続を後続ファイルに分離します。

**最初に証明すべき定理**

```lean
dynamicTerm_eq_arithmeticTerm_scaledDiff
dynamicTerm_one
dynamicTerm_zeroScale
dynamicTerm_zeroDiff
dynamicTerm_succ
gDynamicTerm_toCoeff
gDynamicTerm_extract
gDynamicTerm_eq_gArithmeticTerm_scaledDiff
```

この設計だと、Python の「`ln(e^k)` による拡張」は Lean では「係数スケール `k` による公差変換」として正規化されます。`ln` / `exp` は使わず、結果的に同じ構造を `d*k` の同値性で示す形です。

検証は `lean/dk_math` で以下を想定します。

```bash
lake build DkMath.DHNT.DynamicArithmeticSequence
lake build DkMath.KUS.DynamicArithmeticSequence
```
