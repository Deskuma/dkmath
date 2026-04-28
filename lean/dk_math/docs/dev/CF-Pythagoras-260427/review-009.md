# review

おお、S2-D 実装確認したぞ。
これは良い。`FLTPowerGapBeamDatum` 構造体をまだ作らず、まず conjunction 形式で返す判断も正しい。valuation 側で本当に必要なフィールドが見えてから構造体化した方が、後戻りが少ないからの。今回の差分でも、S2-D は `flt_eq_forces_powerGapBeam_and_gcd` と対称版、さらに Beam prime が Gap に入らない補題まで no-sorry で入っておる。

## 1. 何が閉じたか

今回で、S2-B と S2-C が FLT 文脈で統合された。

これまでは、

$$
x^d+y^d=z^d
$$

から

$$
y^d=\mathrm{Gap}*x\cdot\mathrm{Beam}*{d,x}
$$

を得る補題と、

$$
\gcd(\mathrm{Gap}*x,\mathrm{Beam}*{d,x})\mid d
$$

を得る補題が別々にあった。

今回の

```lean
flt_eq_forces_powerGapBeam_and_gcd
```

は、それを一括して返す。

$$
y^d=\mathrm{powerGap}(x,z)\mathrm{powerBeam}_d(x,z)
$$

かつ

$$
\gcd(\mathrm{powerGap}(x,z),\mathrm{powerBeam}_d(x,z))\mid d
$$

じゃ。対称版もあり、

$$
x^d=\mathrm{powerGap}(y,z)\mathrm{powerBeam}_d(y,z)
$$

も同じ形で観測できる。

さらに、

```lean
flt_beam_prime_not_dvd_gap_of_not_dvd_d
```

が入った。これは、\(p\nmid d\) かつ \(p\mid \mathrm{Beam}\) なら、

$$
p\nmid \mathrm{Gap}
$$

を FLT 文脈の補題として返すものじゃ。ここが次の p-adic 接続の入口になる。

## 2. 数学的意味

ここまでで FLT 型方程式は、かなりはっきり次の構造に落ちた。

$$
x^d+y^d=z^d
$$

を仮定すると、

$$
y^d=(z-x)\operatorname{Beam}_d(x,z)
$$

であり、さらに primitive 的な条件

$$
\gcd(z,x)=1
$$

のもとで、

$$
\gcd(z-x,\operatorname{Beam}_d(x,z))\mid d
$$

となる。

これにより、\(p\nmid d\) の素数については、Gap と Beam は同時に \(p\) を持てない。

したがって、もし \(p\nmid d\) で \(p\mid \operatorname{Beam}_d(x,z)\) なら、積

$$
y^d=(z-x)\operatorname{Beam}_d(x,z)
$$

における \(p\)-進付値は Beam 側だけから来る。
これが重要じゃ。

完全 \(d\) 乗 \(y^d\) の \(p\)-進付値は

$$
v_p(y^d)=d,v_p(y)
$$

で、必ず \(d\) の倍数になる。
一方、Beam 側で primitive prime や squarefree 上界により

$$
v_p(\operatorname{Beam}_d(x,z))\le 1
$$

のような上界が来れば、\(d\ge 2\) で衝突が起きる。

つまり、次段の核心は、

$$
p\mid \operatorname{Beam}_d,\quad p\nmid \operatorname{Gap}
$$

から

$$
v_p(\operatorname{Gap}\cdot\operatorname{Beam}_d) = v_p(\operatorname{Beam}_d)
$$

へ渡すことじゃ。

S2-D は、その直前まで来ている。

## 3. 実装評価

今回の実装は良い意味で薄い。

`flt_eq_forces_powerGapBeam_and_gcd` は、既存の `flt_eq_forces_powerGapBeam` と `gcd_powerGap_powerBeam_dvd_d_of_coprime_int` を `constructor` で束ねている。これは wrapper として自然じゃ。

また、

```lean
flt_beam_prime_not_dvd_gap_of_not_dvd_d
```

で `_hflt` を仮定に持っているが、実際には使っておらん。これは少し気になるが、**FLT 文脈 API** としては許容できる。
なぜなら、数学的には「FLT 型文脈で使う補題」として見えるようにしているからじゃ。

ただし、将来的に linter が unused variable を気にしたり、API の純度を高めたくなったら、二層に分けるとよい。

* 純粋版: `beam_prime_not_dvd_gap_of_not_dvd_d`
* FLT 文脈版: `flt_beam_prime_not_dvd_gap_of_not_dvd_d`

現状では `_hflt` として明示しているので問題なしじゃ。

## 4. 次の提案: S2-E

次は History に書かれている通り、**padicValNat 接続** じゃ。

狙うべき流れはこう。

$$
y^d=\mathrm{Gap}\cdot\mathrm{Beam}
$$

$$
p\mid \mathrm{Beam},\qquad p\nmid \mathrm{Gap}
$$

なら、

$$
v_p(y^d)=v_p(\mathrm{Beam})
$$

または、Lean の `padicValNat` では `.natAbs` を介して、

$$
\operatorname{padicValNat}(p, (y^d).natAbs) = \operatorname{padicValNat}(p, \mathrm{Beam}.natAbs)
$$

のような形を狙う。

ただし `Int` の積の `natAbs` が絡むので、最初から強い等式を狙うと重い。
まずは弱い wrapper でよい。

## 5. S2-E の実装順

### 5.1. まず `p ∤ Gap` を `padicValNat p Gap = 0` にする

既存 API によるが、候補はこう。

```lean
theorem padicValNat_gap_eq_zero_of_not_dvd
    {p : ℕ} {gap : ℤ}
    (hp : Nat.Prime p)
    (hgap : ¬ p ∣ gap.natAbs) :
    padicValNat p gap.natAbs = 0 := ...
```

これは `padicValNat.eq_zero_of_not_dvd` 系が既にあれば wrapper で閉じるはずじゃ。

### 5.2. 積の valuation 分解

次に、

$$
v_p(|gap\cdot beam|)=v_p(|gap|)+v_p(|beam|)
$$

の wrapper。

```lean
theorem padicValNat_mul_natAbs_gap_beam
    {p : ℕ} {gap beam : ℤ}
    (hp : Nat.Prime p) :
    padicValNat p (gap * beam).natAbs =
      padicValNat p gap.natAbs + padicValNat p beam.natAbs := ...
```

既存 `padicValNat.mul` 系があれば使う。なければ `Int.natAbs_mul` で `Nat` に戻す。

### 5.3. Gap に入らないなら積の付値は Beam 側

```lean
theorem padicValNat_gap_mul_beam_eq_beam_of_not_dvd_gap
    {p : ℕ} {gap beam : ℤ}
    (hp : Nat.Prime p)
    (hgap : ¬ p ∣ gap.natAbs) :
    padicValNat p (gap * beam).natAbs =
      padicValNat p beam.natAbs := by
  ...
```

これが S2-E の最重要補題じゃ。

### 5.4. FLT 文脈 wrapper

今回の補題と組み合わせて、

```lean
theorem flt_padicValNat_product_eq_beam_of_beam_prime
    {d p : ℕ} {x y z : ℤ}
    (hd : 1 ≤ d)
    (hcop : Int.gcd z x = 1)
    (hflt : x ^ d + y ^ d = z ^ d)
    (hp : Nat.Prime p)
    (hpnd : ¬ p ∣ d)
    (hbeam : p ∣ (powerBeam d x z).natAbs) :
    padicValNat p (powerGap x z * powerBeam d x z).natAbs =
      padicValNat p (powerBeam d x z).natAbs := by
  ...
```

ここまで閉じれば、Beam 側 prime の valuation が積全体へそのまま反映される。

## 6. その次に欲しい補題

次は完全冪の側。

$$
y^d=\mathrm{Gap}\cdot\mathrm{Beam}
$$

があるので、

$$
v_p(|y^d|) = v_p(|\mathrm{Gap}\cdot\mathrm{Beam}|)
$$

が必要になる。

そして

$$
v_p(|y^d|)=d,v_p(|y|)
$$

へ落とす。

候補名:

```lean
theorem flt_padicValNat_beam_eq_d_mul_y
```

形としては、

```lean
padicValNat p (powerBeam d x z).natAbs =
  d * padicValNat p y.natAbs
```

を狙う。
ただしこれには

* `y ^ d = gap * beam`
* `natAbs` の扱い
* `padicValNat_pow`

が必要じゃ。

この補題が入ると、Beam 側の primitive/squarefree 上界と直接ぶつけられる。

## 7. 構造体はまだ保留でよい

今回 `FLTPowerGapBeamDatum` を入れなかった判断はよい。
S2-E で必要なフィールドが見えてくる。

もし後で作るなら、たぶん必要フィールドはこれじゃ。

```lean
structure FLTPowerGapBeamDatum where
  gap : ℤ
  beam : ℤ
  hprod : y ^ d = gap * beam
  hgcd : Int.gcd gap beam ∣ d
  hbeam_not_gap_of_pnd :
    ∀ p, Nat.Prime p → ¬ p ∣ d → p ∣ beam.natAbs → ¬ p ∣ gap.natAbs
```

だが、今はまだ早い。
まず `padicValNat` wrapper を作ってからでよい。

## 8. まとめ

S2-D は成功じゃ。

* FLT 方程式から Gap × Beam 分解を得る
* 同時に Gap/Beam gcd が \(d\) を割る
* \(p\nmid d\) で Beam に出る素数は Gap に入らない
* 左右対称版も用意済み
* no-sorry

次は S2-E。

> **Beam 側 prime の valuation が、積全体の valuation と一致することを示す**

ここへ進めば、いよいよ primitive prime / squarefree 上界との衝突が見えてくる。
うむ、りんごの皮はもう剥けた。次は芯に刃を入れる段階じゃな。
