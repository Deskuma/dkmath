# review

D.、状況を読むに、これはかなり綺麗に一区切りじゃ。
今回の 004 サイクルで、CF-Pythagoras は **「例が動く段階」から「理論部品として再利用できる段階」** に入った。わっちとしては、ここで **第一章完成** と呼んでよいと思うぞ。

## 1. 状況分析

今回閉じた中核は三つじゃ。

第一に、`EquivRepresentation` が `refl / symm / trans` を持つ同値関係として整った。つまり、同じ三角形を異なる \((\alpha,u)\) 表現で見ることが、ただの例ではなく **表現同値** として扱えるようになった。

第二に、`rescaleEach` と `cosmic_link_rescale_each` によって、各辺ごとの独立スケール \((k_1,k_2,k_3)\) が許された。これは共通スケールではなく、三つの単位宇宙がそれぞれ独立に単位を取り替えられるという意味で、実質的に \((K^\times)^3\) 作用になっておる。報告でも、共通スケールではなく各単位系独立のスケールを許容し、これを \((K^\times)^3\) 作用として位置づけたと整理されておる。

第三に、`gapA`, `beamA`, `b_sq_eq_gapA_mul_beamA` によって、

$$
T.b^2=(T.c-T.a)(T.c+T.a)
$$

が構造体 API として固定された。差分メモで確認できる通り、`gapA T := T.c - T.a`, `beamA T := T.c + T.a` を定義し、linked triple から `b_sq_eq_gapA_mul_beamA` を証明している。

これで完成した三本柱は、

$$
\text{リンク条件}
\quad+\quad
\text{ゲージ自由度}
\quad+\quad
\text{Gap/Beam 生成}
$$

じゃ。報告側でも、完成 API として型一般化、リンク条件、表現同値、ゲージ自由度、Gap/Beam 因数分解が並んでおる。

## 2. 数学的解説

もともとの研究ノートでは、ピタゴラス構造を単なる

$$
a^2+b^2=c^2
$$

ではなく、

$$
\alpha^2u_1^2+\beta^2u_2^2=\gamma^2u_3^2
$$

という **三単位宇宙リンク条件** として読む方針が立っておった。さらに各辺平方を差分量として再構成し、境界差から

$$
b^2=2a\delta_{ca}+\delta_{ca}^2
$$

へ落とす、という整理もすでに研究メモで固定されている。

今回の Lean 実装は、この思想をかなり忠実に定理化している。

特に重要なのは、

$$
b^2=c^2-a^2=(c-a)(c+a)
$$

を単なる恒等式で終わらせず、

$$
\text{Gap}=c-a,\qquad \text{Beam}=c+a
$$

と名付けている点じゃ。

これは見た目以上に重要でな。
ピタゴラスの定理は普通、

$$
a^2+b^2=c^2
$$

という **完成形** として読む。
だが今回の API では、

$$
b^2=\text{Gap}\times\text{Beam}
$$

という **生成形** として読む。

つまり、短辺平方 \(b^2\) は、斜辺と基準辺の差である Gap と、それらを束ねる Beam の積として発生する。これは以前の会話で「差幅 \(u=c-a\) と補正梁 \(2a+u\) の積」として読んだ構造そのものじゃ。研究ログでも、\(u=c-a\) と置けば \(b^2=u(2a+u)\) となり、Gap と Beam の解釈に近いと整理しておる。

そしてゲージ自由度は、この構造をさらに一段強くする。
同じ観測辺

$$
a=\alpha u_1
$$

を、

$$
a=(\alpha k_1)\left(\frac{u_1}{k_1}\right)
$$

として表し直せる。
これは「長さは同じだが、単位核と観測係数の分解は一意ではない」という主張じゃ。

数学的には、これは単なる表記の自由ではなく、**単位選択の対称性** じゃな。
わっちはここを、今後は **unit gauge symmetry** と呼んでもよいと思う。

## 3. 実装上の評価

実装はかなり良い。
とくに `b_sq_eq_gapA_mul_beamA` の証明で、`CommRing` 上では `linarith` に頼れず、`sub_eq_of_eq_add'` を明示的に使った点は正しい判断じゃ。報告にも、`linarith` では `a + b = c` から `c - a = b` を一般環上で導けず、`sub_eq_of_eq_add'` と `.symm` で解決したと記録されておる。

ここは地味だが大事じゃ。
実数や整数なら線形算術で雑に押せるところも、`CommRing` 一般化すると「順序」や「線形不等式」に頼れない。今回そこをちゃんと代数補題で抜けたので、API の抽象度が保たれておる。

また、`rescaleEach_isLinked` が `cosmic_link_rescale_each` を呼ぶ形で閉じているのもよい。差分では、`rescaleEach` が各成分を

$$
\alpha\mapsto\alpha k_1,\quad
u_1\mapsto u_1/k_1
$$

のように変換し、`rescaleEach_equiv` と `rescaleEach_isLinked` を証明している。

これは bundled API と unbundled theorem の接続が綺麗にできている証じゃ。

## 4. 次の提案

次は、いきなり 3D や FLT に飛ぶより、まず **対称性の残り半分** を閉じるのがよい。

### 4.1. `gapB`, `beamB` を追加

今は (a) 側基準の

$$
b^2=(c-a)(c+a)
$$

がある。
次は対称に、

$$
a^2=(c-b)(c+b)
$$

を構造体 API にする。

名前はこうじゃ。

```lean
def gapB (T : CosmicPythagoreanTriple R) : R := T.c - T.b
def beamB (T : CosmicPythagoreanTriple R) : R := T.c + T.b

theorem a_sq_eq_gapB_mul_beamB
    (T : CosmicPythagoreanTriple R) (h : T.IsLinked) :
    T.a ^ 2 = gapB T * beamB T := by
  ...
```

これで左右対称の Gap/Beam が揃う。

### 4.2. `gapA_mul_beamA_eq_b_sq` 形式も用意

現在の向きが

```lean
T.b ^ 2 = gapA T * beamA T
```

なら、rewrite しやすい逆向きもあると便利じゃ。

```lean
theorem gapA_mul_beamA_eq_b_sq
    (T : CosmicPythagoreanTriple R) (h : T.IsLinked) :
    gapA T * beamA T = T.b ^ 2 := by
  exact (b_sq_eq_gapA_mul_beamA T h).symm
```

これは小さいが、後で `rw` の向きに悩まなくて済む。

### 4.3. `gapA_eq_boundaryGap` などの橋

すでに一般関数として `boundaryGap` / `pythagoreanBeam` があるので、構造体版との接続を明示するとよい。

```lean
theorem gapA_eq_boundaryGap (T : CosmicPythagoreanTriple R) :
    gapA T = boundaryGap T.a T.c := by
  rfl

theorem beamA_eq_pythagoreanBeam (T : CosmicPythagoreanTriple R) :
    beamA T = pythagoreanBeam T.a T.c := by
  rfl
```

これで一般補題と構造体 API が相互に使いやすくなる。

### 4.4. `Examples` に rescaleEach の具体例を追加

たとえば \((3,4,5)\) を

$$
k_1=2,\quad k_2=3,\quad k_3=5
$$

などで rescale し、それでも辺が同じであることを確認する。

```lean
example :
    EquivRepresentation triple_3_4_5
      (rescaleEach triple_3_4_5 (2 : ℚ) 3 5) := by
  apply rescaleEach_equiv
  norm_num
  norm_num
  norm_num
```

整数では除法が扱いにくいので、これは `ℚ` でやるのがよい。

## 5. 次の大きな方向

小補題を閉じた後の大方向は三つある。

第一は **nD ピタゴラス** 。

$$
a_1^2+a_2^2+\cdots+a_n^2=c^2
$$

を

$$
\sum_i \alpha_i^2u_i^2=\gamma^2u_c^2
$$

へ拡張する。
ただし、これは今の `CosmicPythagoreanTriple` とは型が変わるので、`Fin n → R` を使う別 API にした方がよい。

第二は **高次宇宙リンク条件** 。

$$
\alpha^d u_1^d+\beta^d u_2^d=\gamma^d u_3^d
$$

じゃ。
これはそのまま FLT 方面へ伸びる。

第三は **差冪 Gap/Beam の d 次化** 。

二次では

$$
c^2-a^2=(c-a)(c+a)
$$

だった。
d 次では

$$
c^d-a^d=(c-a)\sum_{i=0}^{d-1}c^{d-1-i}a^i
$$

になる。
つまり、二次の Beam (c+a) は、高次では

$$
\mathrm{Beam}_d(a,c) = \sum_{i=0}^{d-1}c^{d-1-i}a^i
$$

へ一般化される。

これは既存の GN / Tail 構造とかなり相性がよい。一般化 GN 資料でも、差冪構造 ((x+u)^d-u^d) が常に (x) で割り切れ、その商 (GN_d(x,u)) が Beam 構造の基本対象だと定義されておる。

## 6. FLT との接続考察

ここからが、おまけの本題じゃな。

今回の CF-Pythagoras は、FLT に対して **直接の証明ルート** ではまだない。
しかし、かなり良い **観測装置** になっている。

ピタゴラスでは、

$$
b^2=(c-a)(c+a)
$$

であり、左辺が平方、右辺が Gap × Beam じゃった。

FLT 型では、たとえば

$$
x^d+y^d=z^d
$$

を仮定すると、

$$
y^d=z^d-x^d
$$

であり、

$$
y^d=(z-x)(z^{d-1}+z^{d-2}x+\cdots+x^{d-1})
$$

となる。

ここで

$$
\text{Gap}=z-x
$$

$$
\text{Beam}_d=z^{d-1}+z^{d-2}x+\cdots+x^{d-1}
$$

と読める。
つまり、今回の

$$
b^2=\text{Gap}\times\text{Beam}
$$

は、FLT では

$$
y^d=\text{Gap}\times\text{Beam}_d
$$

へそのまま高次化する。

これが重要じゃ。

なぜなら、primitive な FLT 反例を仮定すると、しばしば Gap と Beam の gcd が強く制御されるからじゃ。典型的には、

$$
\gcd(z-x,\mathrm{Beam}_d)
$$

は (d) によって制御される。
すると、もし右辺が完全 (d) 乗 (y^d) なら、Gap と Beam のそれぞれも (d) 乗に近い形を強制される。ここから descent、primitive prime、p-adic valuation の議論へ入れる。

DkMath の既存資料でも、FLT 幹線は差の冪、gcd 制御、Zsigmondy 原始素因子、p-adic valuation を通じて組まれていると整理されている。特に `DiffPow` が冪差分解装置、`GcdDiffPow` / `GcdLemmas` が整除制御層、`ZsigmondyCyclotomic` が原始素因子エンジンとして位置づけられておる。

今回の CF-Pythagoras は、この幹線の前段に

$$
\text{Gap/Beam 観測}
$$

を与える。
つまり、

$$
z^d-x^d
$$

をいきなり数論的に見るのではなく、

$$
\text{Gap}\times\text{Beam}_d
$$

という「生成構造」として見る入口になる。

## 7. FLT への具体的な Lean 提案

次の新規ファイル候補はこれじゃ。

```text
DkMath/CosmicFormula/PowerGapBeam.lean
```

置くべき定義は、

```lean
def powerGap {R : Type*} [Ring R] (x z : R) : R :=
  z - x
```

```lean
def powerBeam {R : Type*} [CommRing R] (d : ℕ) (x z : R) : R :=
  ∑ i in Finset.range d, z ^ (d - 1 - i) * x ^ i
```

ただし Lean では `d - 1 - i` の Nat 減算が少し面倒なので、既存の `pow_sub_pow` 系や `diffPowSum` / `GN` を再利用した方が安全かもしれぬ。

目標定理は、

$$
z^d-x^d=(z-x)\mathrm{Beam}_d(x,z)
$$

じゃ。

DkMath にはすでに差の冪や GN 系が存在するはずなので、最初は新定義を増やしすぎず、既存補題への wrapper として作るのがよい。

Lean 名候補は、

```lean
theorem pow_sub_pow_eq_gap_mul_powerBeam
```

あるいは既存 GN に寄せるなら、

```lean
theorem pow_sub_pow_eq_gap_mul_GN
```

さらに FLT 反例パックへつなぐ橋として、

```lean
theorem flt_counterexample_forces_gap_beam_power
```

のような名前で、仮定

$$
x^d+y^d=z^d
$$

から

$$
y^d=(z-x)\mathrm{Beam}_d(x,z)
$$

を得る補題を作る。

これはほぼ代数恒等式なので、最初の実装は軽いはずじゃ。

## 8. FLT との見立て

今回のルートは、FLT に対する **新しい別登山ルートの入口** ではある。
ただし、まだ山頂へ直結する道ではない。

正確には、

$$
\text{ピタゴラス}
\quad\Rightarrow\quad
\text{Gap/Beam 生成}
\quad\Rightarrow\quad
\text{高次差冪 Gap/Beam}
\quad\Rightarrow\quad
\text{gcd / primitive prime / valuation}
\quad\Rightarrow\quad
\text{FLT 矛盾}
$$

というルートの、最初の二段が整った状態じゃ。

とくに \(d=2\) では、

$$
\text{Beam}_2=c+a
$$

だけで済む。
だが \(d\ge 3\) では Beam が高次 Tail になる。
ここで GN、Tail、Zsigmondy、p-adic valuation が必要になる。
一般化 GN 資料が述べる通り、\(GN^{(r)}_d\) は二項展開の Tail 構造を正規化し、差冪構造の高次境界因子分解と Beam の層的分解を与える対象じゃ。

ゆえに、CF-Pythagoras は FLT の証明そのものではなく、

> FLT の差冪を、Gap と高次 Beam の生成構造として読むための入口 API

じゃな。

この入口はかなり良い。
なぜなら FLT の難しさは、まさに

$$
\text{Gap}\times\text{Beam}_d
$$

が完全 \(d\) 乗になれるか、という問題に翻訳できるからじゃ。

## 9. 次サイクルの推奨テーマ

わっちの提案はこれじゃ。

> **CF-Pythagoras Chapter 2: Symmetric Gap/Beam and Power Gap/Beam Bridge**

作業順は、

1. `gapB`, `beamB`, `a_sq_eq_gapB_mul_beamB`
2. `gapA_eq_boundaryGap`, `beamA_eq_pythagoreanBeam`
3. `PowerGapBeam.lean` の設計
4. \(d=2\) で `powerBeam` が `c+a` に一致する補題
5. FLT 型仮定から `y^d = Gap * Beam_d` を得る薄い bridge

この順がよい。

これなら、いま完成した CF-Pythagoras 第一章を壊さず、自然に高次差冪と FLT へ接続できる。
りんごの芯を残して綺麗に切り分けるようなものじゃ。ここまで来たなら、次は高次 Beam の皮をむく番じゃな。
