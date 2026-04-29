# review

おお、S2-O、これは **正しい整理** じゃ。
ここは新しい数学を足したというより、Chapter 2 の成長で太くなった依存を、ちゃんと層に分け直した作業じゃな。かなり良い。

## 1. 状況分析

今回の分割で、責務が綺麗になった。

```text
PowerGapBeam.lean
  高次差冪 Gap/Beam の純代数層

PowerGapBeamGcd.lean
  gcd / valuation / squarefree contradiction 層

PowerGapBeamGN.lean
  軽量 GN bridge 層

PowerGapBeamPrimitive.lean
  PrimitiveBeam / FLT contradiction wrapper 層
```

これはかなり良い構成じゃ。

特に重要なのは、`PowerGapBeamGN.lean` から

```lean
import DkMath.CosmicFormula.PowerGapBeamGcd
import DkMath.NumberTheory.PrimitiveBeam
```

を外した点じゃな。

これで `PowerGapBeamGN.lean` は、低次数の

$$
\operatorname{powerBeam}_3 \leftrightarrow GN_3,\qquad
\operatorname{powerBeam}_4 \leftrightarrow GN_4
$$

および valuation / squarefree の単純移送だけを担う軽量 bridge に戻った。
一方で、`PrimitiveBeam` 由来の重い依存や既存 `sorry` warning は `PowerGapBeamPrimitive.lean` に隔離された。

これは将来の保守性に効く。
研究が進むほど、「便利だから全部 import」は後でcompile costと依存循環の種になる。今回の整理はそれを未然に防いでおる。

## 2. 数学的には何が保たれたか

移動した補題の数学的役割はそのまま維持されている。

`PowerGapBeamPrimitive.lean` 側には、

$$
\operatorname{
    PrimitivePrimeFactorOfDiffPow(q,a,b,3)
}
$$

から

$$
q\mid |\operatorname{powerBeam}_3(b,a)|
$$

を得る

```lean
primitive_prime_dvd_powerBeam_three_natAbs
```

が残り、さらに

$$
GN \text{ 側 valuation/squarefree fuel}
\Rightarrow
\text{cubic FLT contradiction}
$$

を与える wrapper 群も移動された。

つまり、Chapter 2 の流れ

$$
\operatorname{PrimitiveBeam}
\to GN
\to \operatorname{PowerBeam}
\to \text{valuation contradiction}
\to \text{False}
$$

は壊れていない。
ただ、責務が正しいファイルへ移った。

これは **前進** じゃ。証明本体を変えず、配置だけ整えたのも安全でよい。

## 3. 実装評価

`CosmicFormula.lean` に `PowerGapBeamPrimitive` を import した判断は、現段階では OK じゃ。
ただし将来的に `DkMath.CosmicFormula` のトップ import を軽くしたくなった場合、

```text
DkMath.CosmicFormula
  軽量本体

DkMath.CosmicFormula.All
  examples / primitive / research bridge まで全部
```

のように分けてもよい。

今は Chapter 2 の連結性を確認する段階なので、トップに載せてよい。
公開導線の最適化は後で十分じゃ。

## 4. 次の提案

次は History にある三点のうち、まず **仮定供給の自動化** がよい。

### 4.1. `q ∤ 3` の供給

今は

```lean
hqnd : ¬ q ∣ 3
```

を外から渡している。

これは悪くないが、`PrimitivePrimeFactorOfDiffPow q a b 3` から出せる可能性があるなら、補助補題を作りたい。

ただし注意じゃ。
(q=3) は cubic では特別素数として現れ得る。したがって、無条件に

$$
q\nmid 3
$$

が primitive witness から出るとは限らぬかもしれない。

まずは既存定義を確認し、

* primitive witness が \(q\nmid d\) を含むのか
* あるいは (q=d) の exceptional branch があるのか
* `q ≠ 3` を追加仮定として扱うべきか

を切り分けるのがよい。

候補補題名は、もし成立するなら：

```lean
primitivePrimeFactorOfDiffPow_not_dvd_degree
```

あるいは d=3 専用なら：

```lean
primitivePrimeFactorOfDiffPow_three_not_dvd_three
```

ただし、成立しない可能性もある。ここは焦らぬ方がよい。

### 4.2. `hbeam_ne` の供給

今は

```lean
hbeam_ne : (powerBeam 3 (b : ℤ) (a : ℤ)).natAbs ≠ 0
```

を外から渡している。

こちらは、おそらく供給しやすい。
d=3 では

$$
\operatorname{powerBeam}_3(b,a)=a^2+ab+b^2
$$

なので、自然数 (a,b) で (b<a) なら、これは正のはずじゃ。

まず Nat / Int 変換が少し絡むが、候補補題はこう。

```lean
powerBeam_three_natAbs_ne_zero_of_pos_right
```

または実用寄りに、

```lean
powerBeam_three_natAbs_ne_zero_of_lt
    {a b : ℕ} (hab : b < a) :
    (powerBeam 3 (b : ℤ) (a : ℤ)).natAbs ≠ 0
```

これはかなり有用じゃ。
これが入れば、S2-N の wrapper から `hbeam_ne` を消せる可能性がある。

数学的には、

$$
a^2+ab+b^2>0
$$

を示せばよい。Lean では `norm_num`, `nlinarith`, `positivity` のどれが効くか次第じゃが、Int に cast するより Nat 側でまず非ゼロを示してから cast する方が楽かもしれぬ。

### 4.3. cubic 専用 wrapper の仮定削減

`hbeam_ne` が供給できたら、次に S2-N の二つの補題を薄くした版を作る。

```lean
flt_three_primitive_GN_val_le_one_contradiction'
```

または名前を整えて、

```lean
flt_three_primitive_GN_val_le_one_contradiction_of_lt
```

のようにして、

```lean
(hbeam_ne : ...)
```

を外し、

```lean
(hab_lt : b < a)
```

から内部で供給する。

すでに `hab_lt` は仮定にあるので、これは自然じゃ。

## 5. 構造体導入について

`FLTPowerGapBeamDatum` は、まだ一手待ってよい。

理由は、今まさに `hqnd` と `hbeam_ne` の自動供給を検討しているからじゃ。
この二つが整理されると、datum に持たせるべきフィールドがかなり減る。

構造体を作るなら、その後でよい。

現時点で候補は、cubic 専用なら：

```lean
structure CubicPrimitivePowerBeamContext where
  q a b : ℕ
  y : ℤ
  hprim : PrimitivePrimeFactorOfDiffPow q a b 3
  hab_lt : b < a
  hcop : Int.gcd (a : ℤ) (b : ℤ) = 1
  hflt : (b : ℤ)^3 + y^3 = (a : ℤ)^3
  hy_ne : y.natAbs ≠ 0
```

ただし `hqnd` を含めるかどうかは、上の調査次第じゃ。

## 6. 次の推奨順

わっちのおすすめはこれじゃ。

1. `powerBeam_three_natAbs_ne_zero_of_lt` を作る
2. それを使って `hbeam_ne` なし版の primitive contradiction wrapper を追加
3. `q ∤ 3` が primitive witness から供給できるか調査
4. 可能なら `hqnd` なし版も追加
5. その後、cubic 専用 datum 構造体を検討

この順なら、既存の流れを壊さずに wrapper の使いやすさを上げられる。

## 7. まとめ

S2-O は成功じゃ。

* `PowerGapBeamGN.lean` が軽量 bridge に戻った
* `PowerGapBeamPrimitive.lean` に重い primitive / contradiction wrapper が隔離された
* 既存 `sorry` warning の流入範囲も限定できた
* Chapter 2 の cubic primitive route は保たれたまま、依存構造が整理された

次は、仮定削減じゃな。
特に `hbeam_ne` はかなり消せそうじゃ。そこを閉じれば、d=3 primitive contradiction wrapper はかなり使いやすくなるぞ。
