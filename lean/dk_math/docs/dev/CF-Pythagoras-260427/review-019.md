# review

おお、S2-N 実装確認じゃ。
これはかなり大きな節目じゃよ、D.。ここでついに、

$$
\text{PrimitiveBeam}
\to
GN
\to
PowerBeam
\to
valuation\ contradiction
\to
False
$$

が **d=3 で一発 wrapper 化** された。

つまり Chapter 2 の cubic route は、ほぼ「研究用エンジン」として一巡したと言ってよい。

## 1. 状況分析

今回追加された主補題は二つじゃ。

```lean
flt_three_primitive_GN_val_le_one_contradiction
```

と

```lean
flt_three_primitive_GN_squarefree_contradiction
```

じゃな。

これらは、Nat 側の primitive prime witness

$$
\operatorname{
    PrimitivePrimeFactorOfDiffPow(q,a,b,3)
}
$$

から、S2-L の

$$
q\mid |\operatorname{powerBeam}_3(b,a)|
$$

を自動供給し、さらに GN 側の valuation 上界または squarefree 仮定を使って、d=3 の FLT 型方程式から `False` を出す。

これで、利用者が毎回

* Nat / Int cast
* (GN) から `powerBeam` への移送
* `hbeam` の供給
* valuation contradiction への接続

を手で行う必要がなくなった。

この「一発 wrapper」は価値が高い。
研究の流れが API として見えるからじゃ。

## 2. 数学的意味

構造はこうじゃ。

Nat 側で primitive prime witness がある。

$$
q\mid GN(3,a-b,b)
$$

これを S2-L で

$$
q\mid |\operatorname{powerBeam}_3(b,a)|
$$

へ運ぶ。

一方で、FLT 型方程式

$$
b^3+y^3=a^3
$$

を仮定すると、

$$
y^3=(a-b)\operatorname{powerBeam}_3(b,a)
$$

が得られる。

さらに、primitive / coprime 条件と (q\nmid3) により、(q) は Gap 側に入らない。
だから (q)-進付値は Beam 側だけから来る。

そして完全 3 乗性より、

$$
v_q(\operatorname{powerBeam}_3)=3v_q(y)
$$

が必要になる。

ここに GN 側の valuation 上界

$$
v_q(GN)\le1
$$

または squarefree 条件

$$
\operatorname{
    Squarefree(|GN|)
}
$$

が来ると、PowerBeam 側でも

$$
v_q(\operatorname{powerBeam}_3)\le1
$$

となり、矛盾する。

つまり今回の補題は、

> primitive prime witness と GN 側の薄い上界情報があれば、cubic FLT 型構造は破綻する

というエンジンじゃ。

かなり良い。

## 3. 実装評価

実装は薄くてよい。

```lean
hbeam := primitive_prime_dvd_powerBeam_three_natAbs hq hab_lt
```

で `hbeam` を供給し、あとは S2-M の contradiction wrapper に渡している。
これは S2-L と S2-M の役割分担が成功している証じゃ。

また、

```lean
hq.1
```

で `Nat.Prime q` を取り出している点もよい。
`PrimitivePrimeFactorOfDiffPow` の内部に prime 情報があるなら、それを使うのが自然じゃ。

一方で、

```lean
hqnd : ¬ q ∣ 3
```

はまだ明示仮定として残っている。
これは今の段階では問題ない。むしろ明示しておく方が、後で「primitive witness は (q\nmid d) を含むべきか？」を判断しやすい。

## 4. ここまでで何が完成したか

S2 の d=3 route は、次の形でまとまった。

$$
\operatorname{
    PrimitivePrimeFactorOfDiffPow(q,a,b,3)
}
$$

$$
\Longrightarrow q\mid GN(3,a-b,b)
$$

$$
\Longrightarrow q\mid |\operatorname{powerBeam}_3(b,a)|
$$

$$
\Longrightarrow v_q(\operatorname{powerBeam}_3)=3v_q(y)
$$

$$
\text{GN 側上界または squarefree}
\Longrightarrow v_q(\operatorname{powerBeam}_3)\le1
$$

$$
\Longrightarrow False
$$

これは **PrimitiveBeam fuel to cubic FLT contradiction** と呼べる段階じゃ。

もちろん、まだ「すべての cubic FLT 反例を自動で落とす」には追加条件の供給が必要じゃ。
だが、反例を落とすための主要な pipeline は接続済みになった。

## 5. 次の課題

次は三つある。

### 5.1. `q ∤ 3` を primitive witness から供給できるか調査

今は

```lean
hqnd : ¬ q ∣ 3
```

が明示仮定じゃ。

しかし `PrimitivePrimeFactorOfDiffPow q a b 3` の定義次第では、(q) が primitive prime なら (q\nmid 3) に近い性質が既に出せるかもしれぬ。

ただし注意が必要じゃ。
d=3 では (q=3) が特別素数として現れる場合がある。
Kummer / Wieferich / first case 的な分岐では (p=d) は別扱いになることが多い。

だから、単純に `hqnd` を消すべきとは限らん。
まずは既存 API に

```lean
primitive_prime_not_dvd_degree
```

のような補題があるか確認じゃな。

なければ、当面は `hqnd` を残してよい。

### 5.2. `hbeam_ne` を自動供給する補題

今は

```lean
hbeam_ne : (powerBeam 3 (b : ℤ) (a : ℤ)).natAbs ≠ 0
```

が明示仮定として残っている。

しかし、

$$
q\mid |\operatorname{powerBeam}_3|
$$

かつ (q) が素数なら、通常は Beam が 0 でないことを言いたくなる。
ただし Lean/Nat では (q\mid0) は真なので、割り切りだけでは非ゼロは出ない。

だが、もし (q) が primitive prime **factor** で「実際に因子として出る」ことに加え、対象が positive であるなどの情報があれば、非ゼロ性が出せるかもしれん。

低コストでやるなら、補助補題：

```lean
theorem powerBeam_three_natAbs_ne_zero_of_GN_ne_zero
```

または

```lean
theorem powerBeam_three_natAbs_ne_zero_of_gap_positive
```

を検討じゃ。

ただ、これも今は明示仮定でよい。
primitive package 側の positivity / nonzero API を見てからが安全じゃ。

### 5.3. ファイル分割

ここはそろそろ本気で考えてよい。

今の `PowerGapBeamGN.lean` は、

* `PowerGapBeam`
* `CosmicFormulaBinom`
* `PowerGapBeamGcd`
* `PrimitiveBeam`

を import していて、依存が重くなってきた。さらに依存先の既存 `sorry` warning も流入する。

整理案はこれ。

```text
DkMath/CosmicFormula/PowerGapBeamGN.lean
  軽量 GN bridge:
  - powerBeam_three_shift_eq_GN
  - powerBeam_four_shift_eq_GN
  - powerBeam_three_eq_GN_of_gap
  - powerBeam_four_eq_GN_of_gap
  - padicValNat / squarefree の単純移送

DkMath/CosmicFormula/PowerGapBeamPrimitive.lean
  重い primitive bridge:
  - import PrimitiveBeam
  - primitive_prime_dvd_powerBeam_three_natAbs
  - flt_three_primitive_GN_val_le_one_contradiction
  - flt_three_primitive_GN_squarefree_contradiction
```

この分割はかなり良いと思う。
`PowerGapBeamGN.lean` を軽く保ち、`PrimitiveBeam` 由来の warning や重依存を `PowerGapBeamPrimitive.lean` に隔離できる。

## 6. 構造体導入について

`FLTPowerGapBeamDatum` はまだ保留でよいが、かなり近づいてきた。

S2-N で primitive witness までつながったので、構造体に入れたい情報が少し見えてきた。

候補は：

```lean
structure CubicPowerBeamContradictionDatum where
  q : ℕ
  a b : ℕ
  y : ℤ
  hprim : PrimitivePrimeFactorOfDiffPow q a b 3
  hflt : (b : ℤ)^3 + y^3 = (a : ℤ)^3
  hcop : Int.gcd (a : ℤ) (b : ℤ) = 1
  hqnd : ¬ q ∣ 3
  hside_ne : y.natAbs ≠ 0
  hbeam_ne : (powerBeam 3 (b : ℤ) (a : ℤ)).natAbs ≠ 0
```

ただし、まだこれは急がなくてよい。
まずはファイル分割と `hqnd` / `hbeam_ne` の供給可能性を調べる方が先じゃ。

## 7. 次の推奨ステップ

わっちなら次はこの順じゃ。

1. `PowerGapBeamPrimitive.lean` を新設して、primitive 依存の補題を移動
2. `PowerGapBeamGN.lean` を軽量 bridge に戻す
3. `q ∤ 3` を primitive witness または追加補題から供給できるか探索
4. `hbeam_ne` を既存 positivity / nonzero API から供給できるか探索
5. その後、必要なら datum 構造体を設計

これが一番安全で、後戻りが少ない。

## 8. まとめ

S2-N は成功じゃ。

今回で、d=3 について

$$
PrimitiveBeam
\to GN
\to PowerBeam
\to valuation\ contradiction
\to False
$$

が no-sorry で一気通貫した。

Chapter 2 の cubic route は、もう **接続済みの理論部品** と言ってよい。
次は戦線を拡大するより、依存整理と仮定供給の自動化じゃな。

ここまで来ると、橋は架かった。
あとは橋の上を荷馬車が安全に通れるように、欄干と標識を整える段階じゃ。
