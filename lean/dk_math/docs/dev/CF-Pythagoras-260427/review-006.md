# review

おお、これは良い判断じゃ、D.。
`pow_sub_pow_eq_gap_mul_powerBeam` を自前帰納法で攻めず、既存の `DkMath.Algebra.DiffPow.pow_sub_pow_factor` に寄せたのは **正解** じゃな。

これで第２章 S2-A は、ほぼ即座に閉じたと言ってよい。

## 1. 状況分析

今回の変更で、`PowerGapBeam.lean` は単なる新規理論ではなく、既存の差冪基盤 `DiffPow` に対する **宇宙式語彙のフロントエンド** になった。

つまり、

```lean
powerGap x z := z - x
powerBeam d x z := ∑ i in Finset.range d, z ^ (d - 1 - i) * x ^ i
```

は、実質的には既存の

```lean
DkMath.Algebra.DiffPow.diffPowSum z x d
```

に名前と解釈を与え直したものじゃ。

そして主定理

$$
z^d-x^d=(z-x)\mathrm{powerBeam}_d(x,z)
$$

は、既存の

$$
a^d-b^d=(a-b)\mathrm{diffPowSum}(a,b,d)
$$

を

$$
a=z,\qquad b=x
$$

として呼び出しただけになる。

これはとてもよい。
重複証明を避け、DkMath の既存幹線に乗ったからじゃ。

## 2. 数学的意味

今回で Chapter 2 の中心式が no-sorry になった。

$$
z^d-x^d=(z-x)\sum_{i=0}^{d-1}z^{d-1-i}x^i
$$

ここで、

$$
\mathrm{Gap}=z-x
$$

$$
\mathrm{Beam}*d=\sum*{i=0}^{d-1}z^{d-1-i}x^i
$$

と読む。

二次では、

$$
\mathrm{Beam}_2=z+x
$$

なので、

$$
z^2-x^2=(z-x)(z+x)
$$

へ戻る。
つまり、Chapter 1 の Pythagorean Gap/Beam は、Chapter 2 の Power Gap/Beam の (d=2) 断面だった、という構図が Lean 上でもかなり明確になった。

ここが大きい。

## 3. 実装評価

今回の証明は、かなり Lean 的にも美しい。

```lean
theorem pow_sub_pow_eq_gap_mul_powerBeam {R : Type*} [CommRing R]
    (d : ℕ) (x z : R) :
    z ^ d - x ^ d = powerGap x z * powerBeam d x z := by
  simpa [powerGap, powerBeam, DkMath.Algebra.DiffPow.diffPowSum] using
    DkMath.Algebra.DiffPow.pow_sub_pow_factor (a := z) (b := x) (d := d)
```

これは、`PowerGapBeam` 側が「概念名を付ける層」であり、代数本体は `DiffPow` 側にある、という役割分担をそのままコードで表している。

わっちはこういう thin wrapper が好きじゃ。
後で定理を探す時にも、

* 代数的に使いたいなら `DiffPow`
* 宇宙式語彙で使いたいなら `PowerGapBeam`

と使い分けられる。

## 4. 次の提案

次は S2-B に進むのがよい。

### 4.1. `CosmicLinkConditionD` を追加

高次リンク条件を定義する。

```lean
def CosmicLinkConditionD {R : Type*} [CommRing R]
    (d : ℕ) (α β γ u₁ u₂ u₃ : R) : Prop :=
  α ^ d * u₁ ^ d + β ^ d * u₂ ^ d = γ ^ d * u₃ ^ d
```

そして (d=2) で既存 `CosmicLinkCondition` に戻ることを示す。

```lean
theorem cosmicLinkConditionD_two_iff {R : Type*} [CommRing R]
    (α β γ u₁ u₂ u₃ : R) :
    CosmicLinkConditionD 2 α β γ u₁ u₂ u₃ ↔
      CosmicLinkCondition α β γ u₁ u₂ u₃ := by
  unfold CosmicLinkConditionD CosmicLinkCondition
  rfl
```

もし `rfl` が通らなければ、

```lean
  simp
```

または

```lean
  constructor <;> intro h <;> simpa using h
```

でよい。

### 4.2. 高次リンクから高次冪方程式へ

Chapter 1 の

```lean
cosmic_link_to_pythagoras
```

の高次版を置く。

```lean
theorem cosmic_linkD_to_power_equation
    {R : Type*} [CommRing R]
    (d : ℕ) (α β γ u₁ u₂ u₃ : R)
    (h : CosmicLinkConditionD d α β γ u₁ u₂ u₃) :
    (α * u₁) ^ d + (β * u₂) ^ d = (γ * u₃) ^ d := by
  unfold CosmicLinkConditionD at h
  calc
    (α * u₁) ^ d + (β * u₂) ^ d
        = α ^ d * u₁ ^ d + β ^ d * u₂ ^ d := by
          rw [mul_pow, mul_pow]
    _ = γ ^ d * u₃ ^ d := h
    _ = (γ * u₃) ^ d := by
          rw [mul_pow]
```

これは Chapter 2 の「高次宇宙リンク条件」本体じゃ。

### 4.3. FLT bridge

次は、今回閉じた主定理を使って、FLT 型仮定を Gap × Beam に変換する。

```lean
theorem flt_eq_forces_powerGapBeam
    {R : Type*} [CommRing R]
    (d : ℕ) (x y z : R)
    (h : x ^ d + y ^ d = z ^ d) :
    y ^ d = powerGap x z * powerBeam d x z := by
  have hdiff : z ^ d - x ^ d = y ^ d := by
    exact (sub_eq_of_eq_add' h.symm).symm
  rw [pow_sub_pow_eq_gap_mul_powerBeam] at hdiff
  exact hdiff.symm
```

この向きはかなり重要じゃ。

$$
x^d+y^d=z^d
$$

から、

$$
y^d=z^d-x^d=(z-x)\mathrm{Beam}_d(x,z)
$$

を得る。
これで FLT 型反例を **Gap × Beam が完全 (d) 乗を作る状況** として観測できる。

### 4.4. 対称版も置く

同じ式から、もちろん

$$
x^d=z^d-y^d=(z-y)\mathrm{Beam}_d(y,z)
$$

も得られる。

```lean
theorem flt_eq_forces_powerGapBeam_symm
    {R : Type*} [CommRing R]
    (d : ℕ) (x y z : R)
    (h : x ^ d + y ^ d = z ^ d) :
    x ^ d = powerGap y z * powerBeam d y z := by
  have hcomm : y ^ d + x ^ d = z ^ d := by
    calc
      y ^ d + x ^ d = x ^ d + y ^ d := by ring
      _ = z ^ d := h
  exact flt_eq_forces_powerGapBeam d y x z hcomm
```

これで左右どちらの短辺も Gap/Beam 観測できる。

## 5. FLT への接続の見立て

ここから先は、かなりはっきりしてきた。

Chapter 2 の bridge が閉じると、FLT 型仮定は

$$
y^d=(z-x)\mathrm{Beam}_d(x,z)
$$

に変換される。

この形で見ると、次の標準戦略が見える。

1. primitive 仮定から (\gcd(z-x,\mathrm{Beam}_d(x,z))) を制御する
2. 右辺が完全 (d) 乗であることから、Gap 側・Beam 側の p-adic valuation に制約がかかる
3. Zsigmondy / primitive prime により、Beam 側に新しい素因子を出す
4. squarefree / valuation 上界により、その素因子の指数が (d) 乗に必要な高さまで上がれない
5. 矛盾

これは既存の FLT 幹線とよく噛み合う。
ただし今の `PowerGapBeam` はあくまで入口じゃ。次に必要なのは

$$
\gcd(\mathrm{Gap},\mathrm{Beam}_d)
$$

の制御であり、そこから `padicValNat` や primitive prime へ橋を架けることじゃな。

## 6. 次サイクル名と到達目標

次はこう呼ぶとよい。

> `005` S2-B: Higher Cosmic Link and FLT Gap/Beam Bridge

到達目標は四つ。

1. `CosmicLinkConditionD`
2. `cosmicLinkConditionD_two_iff`
3. `cosmic_linkD_to_power_equation`
4. `flt_eq_forces_powerGapBeam` と対称版

これらはほぼ代数 wrapper なので、比較的軽く閉じるはずじゃ。

その次、S2-C でいよいよ

$$
\gcd(\text{Gap},\text{Beam}_d)\mid d
$$

または既存 `GcdDiffPow` との接続に入るのがよい。

## 7. まとめ

今回の no-sorry 化で、Chapter 2 の入口は本当に開いた。

$$
\text{Pythagorean Gap/Beam}
\quad\subset\quad
\text{Power Gap/Beam}
\quad\subset\quad
\text{FLT Gap/Beam 観測}
$$

という階段が見えてきた。
しかも主定理は既存 `DiffPow` 基盤に接続されたので、これは孤立した新規ファイルではなく DkMath 幹線に乗っておる。

よくやった。
このまま S2-B に進める状態じゃ。
