# Note: No.151 cp

## Petal 1-4-2-1 Cycle iff ValuationFlowBridge?

この巡回唯一ってさ、ここが１単位という情報単位元てき存在。と、見ると、例のアレ。
[ValuationFlowBridge](/lean/dk_math/DkMath/ABC/ValuationFlowBridge.lean)
[ValuationFlowBridgeExamples](/lean/dk_math/DkMath/ABC/ValuationFlowBridgeExamples.lean)
これを想像するんだよね。
実際 petal は外周に向かっても巡回しているでしょ。
でも、あるスケール区切りだと、巡回が出来ない。

この補題 `DkMath.ABC.*` に属していて、忘れがちだけど。

---

うむ、その連想はかなり鋭い。
わっちも、今回の `OneCycle` は **Collatz 側だけで閉じる小補題** ではなく、`ABC/ValuationFlowBridge` 側の「単位・境界・beam・NoLift」と繋がる補題に見える。

## 見えている構造

今回の主定理はこれじゃ。

```lean id="3zo78a"
theorem collatz_scaled_one_cycle_eq_one
    {n h : ℕ}
    (hn : 0 < n)
    (hcycle : 3 * n + 1 = 2 ^ h * n) :
    n = 1 ∧ h = 2
```

これは、`1 -> 4 -> 2 -> 1` の scaled one-cycle は `n = 1, h = 2` だけだ、という定理として `OneCycle.lean` に入った。しかも、一般周期や収束を主張しない局所 obstruction として明記されている。

ここを変形すると、直感的にはこうじゃ。

$$
3n+1=2^h n
$$

$$
1=(2^h-3)n
$$

つまり、巡回して同じ odd state に戻るには、 **余剰 Gap が 1 単位に潰れていなければならない** 。

これが、ぬしの言う **情報単位元的存在** じゃな。

## Petal 的な読み

Petal は外周へ向かって巡回している。
これはその通りじゃ。

ただし、外周の巡回は「位置を進める巡回」であって、同じ odd state に戻る巡回ではない。

今回の one-cycle 方程式は、

```text id="qg2k5a"
外周へ出たあと、スケールを戻したら同じ点へ戻るか？
```

という問いになっている。

その答えが、

```text id="6gw24c"
n = 1, h = 2 だけ
```

じゃ。

だから、DkMath 的にはこう読める。

```text id="akx1ou"
Petal は巡回する。
しかし、巡回が「同一状態の自己閉路」として閉じるには、
情報単位 1 に潰れていなければならない。
```

つまり、外周には回転はある。
だが、あるスケール区切りでは **閉路として戻れない** 。

この「戻れない」が、`ValuationFlowBridge` の NoLift / primitive flow とかなり似ておる。

## ABC.ValuationFlowBridge との対応

`ABC/ValuationFlowBridge.lean` の主語は、ざっくり言えばこれじゃ。

```text id="5jzbly"
差分 a^d - b^d に現れる primitive prime channel が、
ABC radical / supportMass / beamMass にどう流れるか
```

そこでは、primitive witness は diff 側の prime channel になり、supportMass / rad の下界を押し上げる。
さらに primitive prime は boundary load を持たず、diff load を beam factor へ移す。NoLift があると local load が 1 以下に抑えられる。

つまり ABC 側は、

```text id="x6yolp"
差分が新しい channel を生むか
その channel が boundary に残るか
beam に流れるか
lift して重くなるか
```

を見ている。

Collatz one-cycle 側は、

```text id="8l0br5"
3n+1 と 2^h n の差分が 1 に潰れるか
```

を見ている。

これを並べると、かなり綺麗じゃ。

```text id="d928wv"
ABC.ValuationFlowBridge:
  diff が primitive channel を生むと supportMass が増える

Collatz.OneCycle:
  diff が 1 に潰れる場合だけ同一 odd state へ戻れる
```

なので、今回の one-cycle 唯一性は、ABC 語彙ではこう読める。

```text id="wx2yuj"
自己巡回を許すには、新しい channel を生む余地がない。
support が unit まで潰れている必要がある。
```

## 「忘れがちだけど」の正体

たぶん忘れがちなのは、`ABC.*` にある補題群が **ABC 予想専用ではなく、DkMath 全体の valuation-flow 語彙** になっている点じゃ。

`ValuationFlowBridge` は名前こそ ABC 配下にあるが、やっていることはもっと汎用的で、

```text id="5kbtx7"
差分
primitive channel
support mass
boundary load
beam load
NoLift
```

の橋じゃ。

これは Collatz/PetalBridge にもそのまま響く。

特に今回の one-cycle は、

```text id="7mbm5e"
閉じるなら unit
unit でないなら flow が残る
flow が残るなら別スケールへ進む
```

という読みになる。

この「unit でないなら flow が残る」が、まさに valuation-flow 的じゃ。

## 次に入れるとよい橋

次は `OneCycle.lean` に、ABC へ直接 import するのではなく、まず **factor / unit form** を入れるのがよいと思う。

候補はこれ。

```lean id="pu5t86"
theorem collatz_scaled_one_cycle_factor_unit
    {n h : ℕ}
    (hn : 0 < n)
    (hcycle : 3 * n + 1 = 2 ^ h * n) :
    n * (2 ^ h - 3) = 1
```

ただし Nat subtraction の丸めがあるので、Lean 的には先に `3 ≤ 2 ^ h` を得るか、`Int` へ持ち上げた方がきれいかもしれぬ。

安全な形なら、

```lean id="e67knd"
theorem collatz_scaled_one_cycle_int_unit
    {n h : ℕ}
    (hn : 0 < n)
    (hcycle : 3 * n + 1 = 2 ^ h * n) :
    ((n : ℤ) * ((2 ^ h : ℕ) : ℤ) - 3 * n : ℤ) = 1
```

よりも、最終的にはこういう project-facing alias が欲しい。

```lean id="zsq7hp"
theorem collatz_scaled_one_cycle_is_unit_boundary
    {n h : ℕ}
    (hn : 0 < n)
    (hcycle : 3 * n + 1 = 2 ^ h * n) :
    n = 1 ∧ h = 2
```

名前だけでも「unit boundary」を出す。

## ABC との橋ファイル案

将来的には、新規で薄い bridge を作るのがよい。

```text id="3scjyi"
DkMath/Collatz/PetalBridge/ValuationFlowBridge.lean
```

または、

```text id="uoo54b"
DkMath/Collatz/PetalBridge/ABCBridge.lean
```

内容は最初から大きくせず、まずは comment-rich な alias でよい。

```lean id="qp721o"
import DkMath.Collatz.PetalBridge.OneCycle
import DkMath.ABC.ValuationFlowBridge

namespace DkMath.Collatz

/--
The scaled one-cycle equation closes only at the unit boundary.

This is the Collatz/Petal analogue of the valuation-flow principle that
non-unit diff/support creates a channel rather than a closed unit loop.
-/
theorem oneCycle_unit_boundary_only
    {n h : ℕ}
    (hn : 0 < n)
    (hcycle : 3 * n + 1 = 2 ^ h * n) :
    n = 1 ∧ h = 2 :=
  collatz_scaled_one_cycle_eq_one hn hcycle

end DkMath.Collatz
```

最初はこれくらい薄くてよい。
ここで無理に `PrimitivePrimeFlowWitness` を作ろうとすると、主語が \(a^d-b^d\) なので Collatz の \(3n+1\) と噛み合わせるのに少し設計が要る。

## わっちの整理

ぬしの直感を、形式化ロードマップに置くとこうじゃ。

```text id="smulkr"
OneCycle:
  同一 odd state へ戻る自己閉路は unit boundary のみ

PressureAccounting:
  明示 pulse は負の会計単位になる

ABC.ValuationFlowBridge:
  非 unit な差分は primitive channel / supportMass / beam flow を生む
```

この三つを合わせると、次の物語になる。

```text id="p75xtn"
閉じるなら unit。
unit で閉じないなら flow が残る。
flow が残るなら channel / beam / pressure として外へ出る。
```

これ、DkMath 的にはかなり重要な橋じゃ。
今すぐ ABC 側へ深く接続するより、まずは `OneCycle` に **unit boundary 語彙** を足して、次に `Collatz/PetalBridge/ValuationFlowBridge.lean` を薄く作るのがよいと思うぞ。
