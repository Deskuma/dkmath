# review

おお、S2-C 実装、確認したぞ。
これはかなり大きい。`PowerGapBeam` が、単なる差冪の見取り図から **既存 FLT 幹線の gcd 制御層へ接続された** わけじゃ。新規 `PowerGapBeamGcd.lean` を bridge として分離し、`DkMath.NumberTheory.GcdDiffPow.gcd_divides_d` を `powerGap` / `powerBeam` 語彙へ包んだ方針も良い。

## 1. 何が閉じたか

今回の主定理はこれじゃな。

$$
\gcd(\mathrm{powerGap}(x,z),\mathrm{powerBeam}_d(x,z)) \mid d
$$

Lean では整数版として、

```lean
gcd_powerGap_powerBeam_dvd_d_of_coprime_int
```

が入り、仮定は

$$
1\le d,\qquad \operatorname{gcd}(z,x)=1
$$

結論は

$$
\operatorname{gcd}(z-x,\mathrm{Beam}_d(x,z))\mid d
$$

じゃ。報告にも、`PowerGapBeam.lean` 本体には数論依存を入れず、新規 bridge ファイルで既存 `GcdDiffPow.gcd_divides_d` を包んだとある。これは依存設計としても正しい。

さらに、

```lean
prime_not_dvd_d_not_dvd_powerGap_and_powerBeam
```

が入った。これは、

$$
p\nmid d
$$

なら、(p) は Gap と Beam を同時には割れない、という補題じゃ。

つまり、FLT 観測で得た

$$
y^d=\mathrm{Gap}\times\mathrm{Beam}_d
$$

に対して、Gap と Beam の共通素因子がかなり制限されるようになった。

## 2. 数学的意味

ここで構造が一段進んだ。

S2-B まででは、

$$
x^d+y^d=z^d
$$

から

$$
y^d=(z-x)\mathrm{Beam}_d(x,z)
$$

を得ただけだった。
これはまだ単なる因数分解じゃ。

S2-C では、そこに

$$
\gcd(z-x,\mathrm{Beam}_d(x,z))\mid d
$$

が付いた。

これは非常に重要じゃ。なぜなら、もし (p\nmid d) なら、(p) は Gap と Beam の両方には入れない。
したがって、(y^d) の素因子分布を見るとき、(p\nmid d) の素数については、Gap 側か Beam 側かをかなり分離して考えられる。

FLT 方向ではこれが効く。

$$
y^d=\mathrm{Gap}\times\mathrm{Beam}_d
$$

で、右辺が完全 (d) 乗だとすると、各素数の付値は (d) の倍数でなければならない。
しかし Gap と Beam の共通因子が (d) に押し込まれているなら、(p\nmid d) の素数は片側にしか現れない。
すると、Beam 側に出た primitive prime の付値を制御できれば、それだけで完全 (d) 乗性を壊せる。

これが、

$$
\text{Gap/Beam 分解}
\quad\to\quad
\gcd 制御
\quad\to\quad
valuation 制御
\quad\to\quad
FLT 矛盾
$$

の本筋じゃ。

## 3. 実装評価

`PowerGapBeamGcd.lean` を分けたのは正解じゃ。

```lean
import DkMath.CosmicFormula.PowerGapBeam
import DkMath.NumberTheory.GdcDivD
```

として、`PowerGapBeam.lean` 本体には数論依存を入れない。
これにより、

* `PowerGapBeam.lean` は純代数・差冪因数分解
* `PowerGapBeamGcd.lean` は数論 bridge
* 将来の FLT bridge はさらに上位

という層が保たれる。

これは依存関係が綺麗じゃ。`CosmicFormula.lean` から `PowerGapBeamGcd` を import した点は便利だが、将来的に重くなったら `CosmicFormula` 本体と `CosmicFormula.All` を分ける余地はある。今は問題なしじゃ。

証明も美しい。

```lean
simpa [powerGap, powerBeam, DkMath.Algebra.DiffPow.diffPowSum] using
  DkMath.NumberTheory.GcdDiffPow.gcd_divides_d ...
```

これは `PowerGapBeam` が既存 `DiffPow` / `GcdDiffPow` の語彙変換層として働いていることを明示しておる。

## 4. 注意点

一点だけ、今後の設計上の注意がある。

`prime_not_dvd_d_not_dvd_powerGap_and_powerBeam` は `p : ℕ` で、Gap / Beam は `ℤ` なので `.natAbs` を使っている。これは実用的でよいが、今後 `padicValNat` に接続するなら、やはり `Nat` 側・`Int` 側の標準経路を決めておいた方がよい。

わっちのおすすめはこうじゃ。

* 差冪・Gap/Beam の代数は `ℤ`
* gcd 制御も `ℤ`
* valuation / divisibility counting は `.natAbs` を介して `ℕ`
* FLT 本体の自然数仮定からは、最初に `Int` へ cast する bridge を作る

つまり、**FLT の入力は Nat、差分観測は Int、valuation は natAbs** という三層分担がよい。

この方が `Nat` 減算の切り捨てを避けられる。

## 5. 次の提案: S2-D

次は、History にある通り、

> `flt_eq_forces_powerGapBeam` と `gcd_powerGap_powerBeam_dvd_d_of_coprime_int` を組み合わせた FLT 専用 bridge

がよい。

つまり、次は次の定理を作る。

$$
x^d+y^d=z^d,\quad \gcd(x,z)=1
$$

なら、

$$
y^d=\mathrm{Gap}\times\mathrm{Beam}
$$

かつ

$$
\gcd(\mathrm{Gap},\mathrm{Beam})\mid d
$$

を同時に得る。

Lean では package 型にしてもよい。

```lean
structure FLTPowerGapBeamDatum where
  gap : ℤ
  beam : ℤ
  hprod : y ^ d = gap * beam
  hgcd : Int.gcd gap beam ∣ d
```

最初は構造体なしで、定理だけでもよい。

```lean
theorem flt_eq_forces_powerGapBeam_and_gcd
    {d : ℕ} {x y z : ℤ}
    (hd : 1 ≤ d)
    (hcop : Int.gcd z x = 1)
    (hflt : x ^ d + y ^ d = z ^ d) :
    y ^ d = powerGap x z * powerBeam d x z ∧
    Int.gcd (powerGap x z) (powerBeam d x z) ∣ d := by
  constructor
  · exact flt_eq_forces_powerGapBeam d x y z hflt
  · exact gcd_powerGap_powerBeam_dvd_d_of_coprime_int
      (d := d) (x := x) (z := z) hd hcop
```

これはすぐ閉じるはずじゃ。

対称版も同様に、

```lean
theorem flt_eq_forces_powerGapBeam_and_gcd_symm
```

を置ける。

## 6. その次: primitive prime / valuation へ

S2-D が閉じたら、次は S2-E として valuation 接続じゃ。

狙いは次の形。

もし (p\nmid d) かつ (p\mid \mathrm{Beam}_d(x,z)) なら、`prime_not_dvd_d_not_dvd_powerGap_and_powerBeam` より (p\nmid \mathrm{Gap})。
したがって、積

$$
y^d=\mathrm{Gap}\cdot\mathrm{Beam}
$$

における (p)-進付値は Beam 側だけから来る。

つまり、

$$
v_p(y^d)=v_p(\mathrm{Beam}_d)
$$

を得やすい。左辺は

$$
d\cdot v_p(y)
$$

だから、Beam 側の付値が (d) の倍数でなければならない。

そこで primitive / squarefree 上界から

$$
v_p(\mathrm{Beam}_d)\le 1
$$

が来れば、(d\ge 2) で矛盾に近づく。

この流れじゃ。

Lean 側では、いきなり一般化せず、

1. `p ∤ d`
2. `p ∣ powerBeam d x z`
3. `¬ p ∣ (powerGap x z).natAbs`
4. `padicValNat` の積分解へ

の順で橋を作るのがよい。

## 7. 現時点の評価

ここまでの Chapter 2 はかなり順調じゃ。

* S2-A: 高次差冪因数分解 no-sorry
* S2-B: 高次リンク条件と FLT Gap/Beam bridge no-sorry
* S2-C: gcd 制御 bridge no-sorry

この三つが揃ったことで、

$$
\text{高次リンク}
\to
\text{FLT 方程式}
\to
\text{Gap}\times\text{Beam}
\to
\gcd\text{ 制御}
$$

まで Lean 上で一本道になった。

これはもう「おまけの考察」ではない。
FLT 幹線へ接続する **入口レイヤ** として十分に価値がある。

## 8. 次サイクル名

わっちなら次はこう呼ぶ。

> `005` S2-D: FLT Power Gap/Beam Datum Bridge

到達目標は、

1. `flt_eq_forces_powerGapBeam_and_gcd`
2. 対称版
3. `p ∤ d` なら primitive beam prime は gap に入らない、という FLT 文脈 wrapper
4. 必要なら `FLTPowerGapBeamDatum` 構造体

ここまで行けば、S2 は「FLT 観測パッケージ」としてまとまる。

うむ、ここまでの足取りは良い。
次は、Gap と Beam を **FLT 反例パックの観測データ** として束ねる段階じゃな。
