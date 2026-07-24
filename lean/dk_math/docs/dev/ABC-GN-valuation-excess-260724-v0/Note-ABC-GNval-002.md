# Note: 002: ABC GN valuation excess

閉じに行こうぞ 😏
過去のわっちらが、入口どころか **本丸の城門まで掘り進めておった** 。これは笑うしかないのぅ🤣

ただし、いきなり `abc_main` へ牙を立てるのではなく、まず **決定論的 GN 主線を一本完成させる** 。ここを閉じれば、残敵が本当に一個だけになる。

## 最初の最終目標

任意の ABC 三つ組

$$
a+b=c,\qquad \gcd(a,b)=1
$$

から、任意の指数 $n\ge2$ に対して、

$$
a,GN_n(a,b)+b^n=c^n
$$

という新しい ABC 三つ組を構成する。

現行コードでは一般恒等式、

$$
(a+b)^n=b^n+a,GN_n(a,b)
$$

は既に完成しておる。

したがって最初の checkpoint はこれじゃ。

```lean
def Triple.gnPowerLift (T : Triple) (n : ℕ) : Triple
```

中身は概念的に、

```lean
a := T.a * GN n T.a T.b
b := T.b ^ n
c := T.c ^ n
```

となる。

そして三つ組条件を証明する。

```lean
theorem gnPowerLift_hsum
theorem coprime_boundary_GN_with_gap
theorem gnPowerLift_hcop
```

## 次に valuation を完全分解する

差冪側では、

$$
c^n-b^n=a,GN_n(a,b)
$$

なので、素数 $q$ ごとに、

$$
v_q(c^n-b^n) = v_q(a)+v_q!\left(GN_n(a,b)\right)
$$

を固定する。

primitive prime では境界 $a$ が見えなくなり、

$$
v_q(c^n-b^n) = v_q!\left(GN_n(a,b)\right)
$$

になる。この核は既に `primitive_prime_padic_eq_GN` として存在する。

つまり次の層は、新発見ではなく **既存 theorem の ABC 座標 wrapper** でよい。

```lean
theorem Triple.padic_powerDiff_eq_boundary_add_GN
theorem Triple.primitive_padic_powerDiff_eq_GN
```

## 指数 $n$ の正体を分離する

境界と GN の重複は、

$$
\gcd!\left(a,GN_n(a,b)\right)\mid n
$$

へ閉じ込められる。既存コードにも、この一般 gcd spine がある。

したがって prime channel を二分する。

$$
q\mid n
\quad\text{指数例外層}
$$

$$
q\nmid n
\quad\text{非例外 GN 層}
$$

ここで $q\nmid n$ なら、$q$ は境界 $a$ と GN の両方には現れない。

```lean
def GNExceptionalPrime (q n : ℕ) : Prop :=
  Nat.Prime q ∧ q ∣ n

def GNNonExceptionalPrime (q n : ℕ) : Prop :=
  Nat.Prime q ∧ ¬ q ∣ n

theorem nonExceptional_not_dvd_boundary_of_dvd_GN
```

`UniqueFactorizationGN` は、この例外・非例外分離 API を既に持っている。

## 本当の最終ボス

radical が忘れるものは、

$$
v_q(GN_n)-1
$$

じゃ。

そこで、

$$
\mathrm{GNExcess}(n,a,b) = \sum_{q\mid GN_n(a,b)} \bigl(v_q(GN_n(a,b))-1\bigr)\log q
$$

を定義する。

```lean
noncomputable def GNValuationExcess
    (n a b : ℕ) : ℝ :=
  ∑ q ∈ (GN n a b).factorization.support,
    ((GN n a b).factorization q - 1 : ℝ) * Real.log q
```

すると狙う恒等式は、

$$
\log GN_n(a,b) = \log\mathrm{rad}(GN_n(a,b)) + \mathrm{GNExcess}(n,a,b)
$$

じゃ。

この段階で ABC の敵は完全に可視化される。

```text
GN の大きさ
  = 新しい素数 support
  + 同じ素数の繰り返し valuation
```

support 側は Petal / primitive witness / `rad` bridge が既に処理している。

残るのは、

```text
q² ∣ GNₙ(a,b)
```

となる高持ち上がり prime だけじゃ。

## 一つだけ訂正しておくべき点

前回「GN の反転輸送を閉じれば ABC」と述べたが、ここはさらに厳密にせねばならぬ。

GN lift によって生まれた新しい素数は、元の $\mathrm{rad}(abc)$ には含まれない。したがって単純な、

$$
\mathrm{rad}(GN_n(a,b))
\le
\mathrm{rad}(abc)
$$

は一般には成立せぬ。

ゆえに必要なのは単なる radical transport ではなく、

> 元の三つ組が高 quality なら、GN lift 上で高 valuation 集中が強制される

という **逆向きの強制定理** じゃ。

概念形は、

$$
\mathrm{Quality}(a,b,c)>1+\varepsilon \Longrightarrow \mathrm{GNExcess}(n,a,b) \text{ が異常に大きい}
$$

そして反対側から、

$$
\mathrm{GNExcess}(n,a,b) \le \text{指数例外量} + \text{非例外高持ち上がり量}
$$

を示す。

この二本を衝突させる。

## 攻略順

```text
ABC-GN-001  Triple.gnPowerLift
ABC-GN-002  pairwise coprime lift
ABC-GN-003  padic boundary/GN split
ABC-GN-004  exceptional q ∣ n split
ABC-GN-005  GNValuationExcess identity
ABC-GN-006  high-quality forces GN excess
ABC-GN-007  nonexceptional high-lift obstruction
ABC-GN-008  finite exceptional absorption
ABC-GN-009  Kε construction
ABC-GN-010  replace abc_main_axiom
```

最初の五つは、既存資産を並べ直す仕事であり、かなり速く閉じる可能性が高い。

六番目で初めて、今までの質量・確率 route と新 GN route が正面衝突する。

そして七番目が、真の解除魔法じゃ。

$$
\boxed{
q\nmid n,\quad q^2\mid GN_n(a,b)
}
$$

この非例外高持ち上がりが何を要求するのか。
Wieferich 条件、有限差分、Petal 非衝突、あるいは GN Tail 再帰のいずれかで絞り殺す。

うむ。 **閉じに行く価値は十分にある。**
しかも今回は山を一から登るのではない。昔のわっちらが城内に通じる地下道をほぼ完成させておる。

まずは `ABC-GN-001` からじゃ。賢狼、抜剣じゃな 🐺⚔️
