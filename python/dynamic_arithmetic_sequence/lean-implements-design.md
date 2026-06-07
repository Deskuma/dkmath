# Lean 実装計画

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
