# review

おお、S2-S 確認したぞ。
これは **小さいが効く整理** じゃ。`CubicPrimitiveFLTContext` が、単なる仮定の束から、ちゃんとした **観測パック API** に昇格した。

## 1. 何が良いか

今回追加された導出補題は、どれも自然で有用じゃ。

```lean
CubicPrimitiveFLTContext.prime
CubicPrimitiveFLTContext.q_not_dvd_three
CubicPrimitiveFLTContext.beam_dvd
CubicPrimitiveFLTContext.beam_ne
```

これで通常 branch では、

$$
\operatorname{
    Nat.Prime(C.q)
}
$$

$$
C.q\nmid 3
$$

$$
C.q\mid |\operatorname{powerBeam}_3(C.b,C.a)|
$$

$$
|\operatorname{powerBeam}_3(C.b,C.a)|\ne0
$$

を context から直接取り出せる。

これは大事じゃ。
これまでは、`hprim`, `hab_lt`, `hq_ne_three` などを毎回展開して既存 wrapper を呼ぶ必要があった。
今回からは、利用側が

```lean
C.prime
C.q_not_dvd_three
C.beam_dvd
C.beam_ne
```

で済む。

かなり Lean API らしくなった。

## 2. 数学的意味

通常 cubic branch の構造は、いまこう読める。

$$
C : \operatorname{CubicPrimitiveFLTContext}
$$

があるとき、これはすでに

* primitive prime witness
* endpoint order (b<a)
* coprime condition
* cubic FLT 型方程式
* side nonzero
* ordinary prime condition (q\ne3)

を持っている。

そこから自動的に、

$$
q\mid \operatorname{Beam}_3
$$

$$
q\nmid3
$$

$$
\operatorname{Beam}_3\ne0
$$

が出る。

つまり、通常 branch で valuation contradiction に入るための機械的な観測事実は、context 内に内蔵されたわけじゃ。

これは、今後の定理をかなり短くする。

## 3. 実装評価

今回の補題は全部 thin wrapper なのがよい。

```lean
C.hprim.1
prime_not_dvd_three_of_ne_three C.prime C.hq_ne_three
primitive_prime_dvd_powerBeam_three_natAbs C.hprim C.hab_lt
powerBeam_three_natAbs_ne_zero_of_lt C.hab_lt
```

すべて既存補題への委譲で閉じている。
こういう導出補題は、証明内容より **名前があること** に価値がある。

今後、`CubicPrimitiveFLTContext` を標準入口にするなら、これらは必須級じゃ。

## 4. 次の提案

次は二択じゃ。

### A. context theorem を標準入口として強化

すでに

```lean
C.val_le_one_contradiction
C.squarefree_contradiction
```

がある。
ここに、今回の導出補題を使ったより明示的な intermediate theorem を足してもよい。

たとえば、

```lean
theorem beam_val_eq_three_mul_side
    (C : CubicPrimitiveFLTContext) :
    padicValNat C.q (powerBeam 3 (C.b : ℤ) (C.a : ℤ)).natAbs =
      3 * padicValNat C.q C.y.natAbs := ...
```

これは S2-F の context 版じゃ。
これがあると、`val_le_one_contradiction` の中間構造が context 上で直接見える。

同様に、

```lean
theorem beam_val_positive
    (C : CubicPrimitiveFLTContext) :
    1 ≤ padicValNat C.q (powerBeam 3 (C.b : ℤ) (C.a : ℤ)).natAbs := ...
```

もありじゃ。

ただし、なくても contradiction theorem はすでに使える。
見通し向上用じゃな。

### B. \(q=3\) exceptional branch を切る

通常 branch はかなり整った。
次に数学的に進むなら、やはり

$$
q=3
$$

の cubic exceptional branch じゃ。

今の通常 branch は \(q\ne3\) を前提にしている。
したがって、全体戦略としては、

$$
q\ne3
\Rightarrow
通常 branch で矛盾
$$

$$
q=3
\Rightarrow
別処理
$$

という分岐が自然じゃ。

まずは theorem ではなく、context だけ切ってもよい。

```lean
structure CubicExceptionalFLTContext where
  q : ℕ
  a : ℕ
  b : ℕ
  y : ℤ
  hprim : DkMath.NumberTheory.PrimitiveBeam.PrimitivePrimeFactorOfDiffPow q a b 3
  hab_lt : b < a
  hcop : Int.gcd (a : ℤ) (b : ℤ) = 1
  hflt : (b : ℤ) ^ 3 + y ^ 3 = (a : ℤ) ^ 3
  hy_ne : y.natAbs ≠ 0
  hq_eq_three : q = 3
```

これを置いておくだけでも、通常 branch と exceptional branch が設計上分離される。

## 5. わっちのおすすめ

次は **A を少しだけやってから B** がよい。

具体的には、

1. `CubicPrimitiveFLTContext.beam_val_eq_three_mul_side`
2. `CubicPrimitiveFLTContext.beam_val_positive`
3. `CubicExceptionalFLTContext` の定義だけ追加

この順じゃな。

理由は、1 と 2 は通常 branch の context API をさらに使いやすくする薄い整理。
3 は今後の \(q=3\) branch の受け皿になる。

## 6. まとめ

S2-S は成功じゃ。

* `CubicPrimitiveFLTContext` から主要観測事実を直接取得できるようになった
* 通常 cubic branch の API がかなり読みやすくなった
* `q ≠ 3` branch は context としてほぼ完成形に近い
* 次は context 上の valuation 補題を少し足すか、\(q=3\) exceptional context を切る段階

ここまでで、通常 branch はかなり整った。
わっちなら、そろそろ「Chapter 2 通常 cubic route 完了」と印を付けてもよいと思うぞ。

---

うむ、まさに潮時じゃな。
S2-S まで来たなら、ここから先は **新しい補題を増やす段階** ではなく、**章として閉じる段階** に入るべきじゃ。

いま Chapter 2 は、すでに次の鎖を持っておる。

$$
\text{FLT 型方程式}
\Rightarrow
\text{Gap}\times\text{Beam}
\Rightarrow
\gcd\text{ 制御}
\Rightarrow
p\text{-adic valuation}
\Rightarrow
\text{GN / PrimitiveBeam fuel}
\Rightarrow
\text{通常 cubic branch contradiction}
$$

これはもう十分に「成果」と呼べる。
これ以上、勢いで S2-AA とか始めると、麦畑が迷路になるぞ。わっちは賢狼じゃから、収穫時も知っておる。

## S2-T から S2-Z までの 7 回締めプラン

### S2-T. 通常 branch API の固定

目的は、`CubicPrimitiveFLTContext` を通常 cubic route の標準入口として固定すること。

やることは小さくてよい。

* `CubicPrimitiveFLTContext` の docstring を少し厚くする
* 通常 branch は (q\ne3) と明記
* `val_le_one_contradiction`
* `squarefree_contradiction`
* `prime`
* `q_not_dvd_three`
* `beam_dvd`
* `beam_ne`

を「標準 API」として整理する。

ここでは新しい数学を増やさない。
API の看板を立てるだけじゃ。

---

### S2-U. \(q=3\) exceptional branch の箱だけ作る

ここで本格証明に突っ込まない。

やるなら、まず context だけ。

```lean
structure CubicExceptionalFLTContext where
  q : ℕ
  a : ℕ
  b : ℕ
  y : ℤ
  hprim : PrimitivePrimeFactorOfDiffPow q a b 3
  hab_lt : b < a
  hcop : Int.gcd (a : ℤ) (b : ℤ) = 1
  hflt : (b : ℤ) ^ 3 + y ^ 3 = (a : ℤ) ^ 3
  hy_ne : y.natAbs ≠ 0
  hq_eq_three : q = 3
```

この段階では、定理は最小限でよい。
目的は **通常 branch と exceptional branch を混ぜない** ことじゃ。

---

### S2-V. theorem map / route map を History または Markdown に起こす

ここは Lean ではなく文書化。

章の成果をこういう形でまとめる。

```text
PowerGapBeam
  pow_sub_pow_eq_gap_mul_powerBeam

PowerGapBeamGcd
  flt_eq_forces_powerGapBeam_and_gcd
  flt_padicValNat_beam_eq_d_mul_y_of_beam_prime
  flt_beam_prime_val_le_one_contradiction
  flt_beam_squarefree_prime_contradiction

PowerGapBeamGN
  powerBeam_three_eq_GN_of_gap
  powerBeam_three_padicValNat_eq_GN_gap

PowerGapBeamPrimitive
  primitive_prime_dvd_powerBeam_three_natAbs
  CubicPrimitiveFLTContext.squarefree_contradiction
```

これは後で絶対に効く。
未来の D. が「どこから使うんだ？」と迷わなくなる。

---

### S2-W. import / warning 境界の最終確認

今回 `PowerGapBeamPrimitive.lean` へ重い依存を隔離したのは良い判断じゃ。

S2-W では、以下を確認する。

* `PowerGapBeam.lean` は純代数層のままか
* `PowerGapBeamGN.lean` は軽量 GN bridge のままか
* `PowerGapBeamPrimitive.lean` に warning 流入が隔離されているか
* `CosmicFormula.lean` に全部 import する方針でよいか
* 必要なら将来 `CosmicFormula.All` 分離案を History に残す

ここも、新規数学は増やさない。
畑の畝を整える作業じゃ。

---

### S2-X. smoke tests / examples の追加

最小限の `example` や `#check` を置く。

目的は「標準入口が壊れていない」ことの確認。

例：

```lean
#check DkMath.CosmicFormula.PowerGapBeam.CubicPrimitiveFLTContext.squarefree_contradiction
#check DkMath.CosmicFormula.PowerGapBeam.CubicPrimitiveFLTContext.val_le_one_contradiction
#check DkMath.CosmicFormula.PowerGapBeam.primitive_prime_dvd_powerBeam_three_natAbs
```

もし examples file にするなら、

```text
PowerGapBeamExamples.lean
```

ではなく、重い primitive 依存を考えて

```text
PowerGapBeamPrimitiveExamples.lean
```

の方がよいかもしれん。

---

### S2-Y. Open Problems / Deferred Tasks の明文化

ここで「まだやらないこと」を明示する。

候補は：

* 一般次数 bridge

$$
  powerBeam_d(x,x+u)=GN(d,u,x)
$$

* \(q=3\) exceptional branch の処理
* `FLTPowerGapBeamDatum` の一般構造体化
* d=4 route の扱い
* PrimitiveBeam 依存先の既存 `sorry` warning 解消
* `CosmicFormula.lean` と `CosmicFormula.All` の分離

ここで大事なのは、未完を失敗ではなく **次章の入口** として整理することじゃ。

---

### S2-Z. Chapter 2 final summary

最後に、History へ最終節を追加する。

題名案：

```md
### 日時: 2026/04/29 JST (S2-Z: Chapter 2 closure)
```

内容は：

1. Chapter 2 の目的
2. 実装されたモジュール
3. 中核定理
4. cubic normal branch の完成範囲
5. remaining exceptional branch
6. 次章候補

この S2-Z で、Chapter 2 を正式に閉じる。

## わっちの推奨

次は **S2-T** として、`CubicPrimitiveFLTContext` の標準 API 固定と docstring 整理がよい。

その後、

$$
T,U,V,W,X,Y,Z
$$

でちょうど 7 回。
アルファベットも綺麗に使い切れる。実に縁起がよい。

## 締めの判断

今の段階で、Chapter 2 はすでに成果として十分じゃ。

特に通常 cubic branch については、

$$
\operatorname{
    CubicPrimitiveFLTContext
}
+
GN\text{ valuation upper bound}
\Rightarrow
\text{False}
$$

および

$$
\operatorname{
    CubicPrimitiveFLTContext
}
+
GN\text{ squarefree}
\Rightarrow
\text{False}
$$

まで行っている。

これは「ピタゴラス宇宙式から FLT 方向へ伸びた観測エンジン」として、かなり綺麗な形じゃ。

よし、ここからは攻めすぎず、収穫して束ねよう。
麦を刈る時期を逃すと、せっかくの実りも風に倒れるからの。
