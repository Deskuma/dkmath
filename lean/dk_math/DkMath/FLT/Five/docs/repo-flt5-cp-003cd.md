# Report: FLT5 cp-003cd

## result

cp-003c,d を完了しました。

cp-003c は production 実装まで完了しています。[NormalForm.lean](/lean/dk_math/DkMath/FLT/Five/NormalForm.lean) に以下を追加しました。

```text
BranchBFifthPowerNormalForm
exists_branchB_fifthPowerNormalForm
BranchBFifthPowerCore
branchB_false_of_fifthPowerCore
```

反例から Lean が回収する正規形は次です。

```text
z - y = a^5
GN5 (a^5) y = b^5
x = a*b
z = y + a^5

0 < a
0 < b
Coprime a y
Coprime a b
Coprime b y
5 ∤ a
```

`GN5 g y ≡ g⁴ mod y` を使った `coprime_GN5_y_of_coprime` も証明済みです。

cp-003d の判定は Outcome C です。ただし、両ルートともかなり具体的な入口まで到達しました。

Route A は scratch Lean で次を証明しています。

```text
U = 2z² + zy + 2y²
V = zy

U² - 5V² = 4b⁵
norm (⟨U,V⟩ : Zsqrtd 5) = 4b⁵
```

止まっているのは、多項式変形ではなく実二次整数環上の本格的な下降です。特に黄金比基底による整数環、2 と 5 の例外因子、単数、共役因子の互いに素性、そして小さい反例の再構成が必要です。

Route B では、全 `Fin 25` 剰余類を `native_decide` で検査し、さらに一般の自然数へ持ち上げて次を scratch Lean で証明しました。

```text
CounterexamplePack x y z
¬ 5 ∣ z - y
    →
5 ∣ y ∨ 5 ∣ z
```

これは有力です。

- `5 ∣ y` は `x,y` の交換により自然差型 Branch A へ向かいます。
- `5 ∣ z` は `5 ∣ x+y` という signed/sum 型になります。

現在の `BranchACondition` は自然数差しか表現しないため、両者を統合する signed Branch-A packet と明示的な下降測度が、次の正確な不足部品です。

調査報告は [note-flt5-cp-003cd-survey.md](/lean/dk_math/DkMath/FLT/Five/docs/note-flt5-cp-003cd-survey.md) にまとめました。次の推奨経路は Route B です。

監査も更新しました。

- [CheckAxioms.lean](/lean/dk_math/DkMathTest/FLT/Five/CheckAxioms.lean)
- `lake build DkMathTest.FLT.Five.CheckAxioms DkMath.FLT.Five` 成功
- `sorryAx` なし
- `git diff --check` 成功
- `BranchA.lean` は未変更
- FLT5 最終定理は導入していません
