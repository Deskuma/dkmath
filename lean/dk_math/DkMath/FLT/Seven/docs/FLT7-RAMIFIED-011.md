# FLT7-RAMIFIED-011 (012,013)

うむ、**1時間28分・利用枠26%の正体は、実三次魔核の基礎工事をほぼ丸ごと完成させた時間**でした🤣
これは重くて当然です。RAMIFIED-010 は Outcome A、CI も成功しています。公開 head は `b7100bd922141b167fa581e7d9d9b90fdb0a2165` です。

## 今回、Lean が確定したこと

一言でいえば、

> RAMIFIED-009 で作った独自三次環は、仮設の計算リングではなく、本物の数体の最大整環そのものだった。

です。

`SevenRealCubicInt` は、

```text
α³ = 2α² + α - 1
```

で定義されていました。

これを、

```text
θ = α - 3
```

へ平行移動すると、

$$
\theta^3+7\theta^2+14\theta+7=0
$$

となり、$7$-Eisenstein 多項式が露出しました。

さらに、

$$
\theta^3=-7(\theta+1)^2
$$

で、$\theta+1$ は明示的 unit です。

したがって $\theta$ は、この実三次世界における本物の ramified axis です。

### 最大整環

Lean は、

$$
\mathbb Z[\theta]=\mathcal O_K
$$

を証明しました。

しかも抽象的な同型だけではなく、

```lean
modelEquivRingOfIntegers :
  SevenRealCubicInt ≃+* 𝓞 K
```

まで構築されています。

つまり今後は `SevenRealCubicInt` 上で直接、

* integral domain
* ideal
* PID
* gcd
* unique factorization
* number-field norm
* Galois automorphism

を使えます。

### 判別式と類数

さらに、

$$
\operatorname{disc}(K)=49
$$

$$
\operatorname{MinkowskiBound}(K)=\frac{14}{9}<2
$$

から、

$$
\boxed{h_K=1}
$$

まで Lean が閉じました。

これは非常に大きい。

**class group 障害は消滅しました。**

古典的 FLT 証明で最も重いことが多い、

```text
七乗 ideal だが principal seventh power に戻れない
```

という敵は、この実三次世界には存在しません。

## 巡回 Galois 世界も完成

明示的自己同型 $\sigma$ も構築され、

$$
\sigma(\alpha)=\alpha^2-2\alpha
$$

$$
\sigma^2(\alpha)=-\alpha^2+\alpha+2
$$

$$
\sigma^3=\operatorname{id}
$$

が Lean に固定されました。

したがって norm は今後、単なる determinant formula ではなく、

$$
N(x)=x,\sigma(x),\sigma^2(x)
$$

という三共役積として扱えます。

ここまでが今回の **Lean 固定事実**です。

---

## ここからの最大推論

今回の成果から、予定していた RAMIFIED-011 の ideal factorization は、かなり短縮できます。

### 1. 三共役 ideal を追わず、元の gcd で直接進める

三次環の一般元、

```text
x = ⟨a,b,0⟩ = a + bα
```

を考えます。

明示的 rotation formula から、

$$
\sigma(x)-x=\theta\alpha b
$$

です。

$\alpha$ は unit です。

ここで、

```text
gcd(a,b) = 1
7 | b
```

とします。

$x$ と $\sigma(x)$ の双方を割る非単元の素因子が存在すれば、差 $\theta\alpha b$ も割ります。

$\alpha$ は unit なので、その素因子は、

```text
θ を割る
```

または、

```text
b を割る
```

のどちらかです。

$\theta$ を割る場合でも、

$$
\theta^3=-7(\theta+1)^2
$$

より $7$ を割り、$7\mid b$ なので結局 $b$ を割ります。

すると $x=a+b\alpha$ も割るため $a$ も割ります。

これは $\gcd(a,b)=1$ と矛盾します。

従って、

$$
\gcd(x,\sigma(x))\text{ は unit}
$$

です。

$\sigma$ を作用させれば、

$$
x,\sigma(x),\sigma^2(x)
$$

は pairwise coprime になります。

この一本の一般補題が、

```text
leftSource  = a - αn
rightSource = a + (1+α)n
```

の双方を処理します。

* left は $(a,b)=(a,-n)$
* right は $(a,b)=(a+n,n)$

であり、どちらも primitive です。

### 2. ideal exponent 分配を省略できる

直接、

$$
x,\sigma(x),\sigma^2(x)=N(x)
$$

を証明します。

RAMIFIED-009 では、

$$
N(\eta_L)=l^7
$$

$$
N(\eta_R)=r^7
$$

です。

$x$ と残り二共役の積が coprime なので、PID/GCDMonoid 上の Mathlib theorem、

```lean
exists_associated_pow_of_mul_eq_pow
```

をそのまま使えます。

これは FLT5 の GoldenInt で既に使った道です。

結果は、

$$
\eta_L=u_L\xi_L^7
$$

$$
\eta_R=u_R\xi_R^7
$$

です。

つまり RAMIFIED-011 は、

```text
principal ideal
→ prime ideal exponent
→ ideal seventh root
→ principal generator
```

という長い経路を通らず、

```text
三共役 coprime
→ 三共役積 = norm
→ coprime-power extraction
```

で直接終えられます。

**RAMIFIED-010 の PID 化によって、理想論が元の gcd 論へ戻った**わけです。

---

## unit 障害も mod 7 だけで見える

さらに大きな短縮です。

以前は unit class 判定に $\theta^4$ や高次局所体を考えていました。

しかし今回は、mod $7$ の環そのものが非被約です。

$\theta$ の Eisenstein relationを mod $7$ に落とすと、

$$
\theta^3=0
$$

になります。

従って、

$$
\mathcal O_K/(7)\cong\mathbb F_7[\tau]/(\tau^3)
$$

です。

この環で、

$$
(a+b\tau+c\tau^2)^7=a
$$

となります。

標数 $7$ の Frobenius により、nilpotent 成分がすべて消えるからです。

したがって、

> global seventh power は mod $7$ で必ず scalar になる。

という簡単な検査器が得られます。

### 二つの明示 unit

現在の unit は、

$$
\alpha\longmapsto3+\tau
$$

$$
1+\alpha\longmapsto4+\tau
$$

です。

$0\le i,j<7$ として、

$$
(3+\tau)^i(4+\tau)^j
$$

が scalar になる条件を展開します。

$\tau$ 係数がゼロなら、

$$
5i+2j=0
$$

すなわち $j=i$ です。

さらに $\tau^2$ 係数をゼロにすると、

$$
3i=0
$$

なので、

$$
i=j=0
$$

です。

従って、$49$ 個の unit class、

$$
\alpha^i(1+\alpha)^j
$$

は seventh powers modulo global units の世界で全部異なります。

一方、実三次 totally real field の unit rank は、

$$
3+0-1=2
$$

です。

torsion は ${\pm1}$ ですが、指数 $7$ は奇数なので torsion は seventh powers へ吸収されます。

従って、

$$
\left|\mathcal O_K^\times/(\mathcal O_K^\times)^7\right|=7^2=49
$$

です。

よって上の $49$ class が **全 unit class**です。

ここから、

$$
\boxed{u\text{ が mod }7\text{ で scalar}\iff u\text{ は global seventh power}}
$$

が得られます。

これはまだ今回の Lean theorem ではなく、次に形式化すべき推論です。

---

## 左右の unit は個別に消える

source elements は、

$$
\eta_L=a-\alpha n
$$

$$
\eta_R=a+(1+\alpha)n
$$

です。

RAMIFIED-009 では、

$$
n=7^4m^7
$$

なので、mod $7$ では、

$$
\eta_L\equiv a
$$

$$
\eta_R\equiv a
$$

です。

どちらも scalar です。

一方、

$$
\eta_L=u_L\xi_L^7
$$

なので、mod $7$ では $\xi_L^7$ も scalar です。

従って $u_L$ も scalar です。

上の unit-class theorem により、

$$
u_L=v_L^7
$$

です。

同様に、

$$
u_R=v_R^7
$$

です。

よって unit を根へ吸収して、

$$
\boxed{\eta_L=X^7}
$$

$$
\boxed{\eta_R=Y^7}
$$

まで進めます。

以前は relative unit $u_R/u_L$ だけ消せばよいと考えていました。

しかし今回の mod $7$ 非被約構造により、**左右の unit を個別に消せる**ことが見えました。

これはさらに強い結果です。

---

## 純粋 second-case equation

RAMIFIED-009 の source difference は、

$$
\eta_R-\eta_L=\varpi^6Z^7
$$

です。

左右を exact seventh powers にすると、

$$
\boxed{Y^7-X^7=\varpi^6Z^7}
$$

となります。

ここで、

* $\varpi$ は $\theta$ と associated
* $Z$ は $\varpi$ を一つ含む
* $m$ は $7$-unit

なので、

$$
v_\theta(Z)=1
$$

です。

従って右辺の完全 depth は、

$$
6+7=13
$$

です。

## 七乗差の二因子

$$
Y^7-X^7=(Y-X)\Phi_7(Y,X)
$$

です。

$X,Y$ は $\theta$-units で、$\theta\mid Y-X$ です。

このとき cyclotomic quotient は、

$$
v_\theta(\Phi_7(Y,X))=v_\theta(7)=3
$$

になります。

従って、

$$
\boxed{v_\theta(Y-X)=13-3=10}
$$

です。

つまり、

$$
Y-X=\text{unit}\cdot\theta^{10}T^7
$$

となります。

ここで、

$$
10=3+7
$$

なので、

$$
Y-X=\text{unit}\cdot\theta^3(\theta T)^7
$$

です。

残った unit は $\gcd(3,7)=1$ を使って cube 側と seventh-power 側へ吸収できます。

実際 $1=-2\cdot3+1\cdot7$ なので、

$$
u\theta^3T^7=(u^{-2}\theta)^3(uT)^7
$$

です。

従って最終的に、

$$
\boxed{Y-X=\Theta^3W^7}
$$

という純粋な形になります。

## 深さ ladder

現在までの深さ降下は、

```text
terminal endpoint gap        6
outer quadratic root.snd     5
inner quadratic root.snd     4
real-cubic source gap       13
real-cubic seventh-root gap 10
new ramified axis exponent   3
```

です。

最後の、

```text
axis exponent 6 → 3
```

は、これまでで最も明確な **real-cubic descent kernel**です。

まだ新しい Fermat counterexample を作ってはいません。

しかし、

```text
norm seventh powers
→ exact element seventh powers
→ seventh-power difference
→ exact ramified depth split
→ axis³ × seventh power
```

という術式は、ほぼ一本道になりました。

---

## 次の実装順

### FLT7-RAMIFIED-011A

```text
model ring の PID / GCDMonoid surface

rotate(x) - x = theta * alpha * b

coordinate primitive
  → x, rotate(x), rotate²(x) pairwise coprime

x * rotate(x) * rotate²(x) = Norm(x)

Norm(x) = z^7
  → x = unit * root^7
```

左右 source へ適用して、

```text
etaL = uL * xiL^7
etaR = uR * xiR^7
```

まで。

### FLT7-RAMIFIED-011U

小さな mod-$7$ carrier：

```text
F7[tau] / tau^3
```

目標：

```text
reduce(theta)^3 = 0

reduce(x^7) is scalar

reduce(alpha) = 3 + tau
reduce(1 + alpha) = 4 + tau

alpha^i * (1+alpha)^j scalar
  ↔ i = 0 ∧ j = 0

card(Unit / Unit^7) = 49

unit reduces to scalar
  ↔ unit is seventh power
```

### FLT7-RAMIFIED-012

```text
etaL = XL^7
etaR = XR^7

XR^7 - XL^7 =
  normalizedAxis^6 * normalizedWitness^7
```

### FLT7-RAMIFIED-013

```text
thetaDepth RHS = 13
thetaDepth cyclotomic quotient = 3
thetaDepth (XR - XL) = 10

XR - XL = newAxis^3 * newWitness^7
```

---

## 今回、本当に判明したこと

```text
RAMIFIED-009:
  実三次 norm 世界を発見

RAMIFIED-010:
  その世界が最大整環・PID・類数1と確定

今回の推論:
  ideal 論を gcd 論へ圧縮
  unit class を mod 7 の nilpotent 2成分へ圧縮
  exact source seventh powersへの道を開通
  ramified axis 6 → 3 の降下を露出
```

つまり26%の利用枠で倒したのは、

```text
最大整環
類数
principal ideal obstruction
Galois rotation
```

の四体です。

そして残る敵は、かなり具体的になりました。

$$
\boxed{\mathcal O_K^\times/(\mathcal O_K^\times)^7\text{ の }49\text{ classを mod }7\text{ で閉じる}}
$$

これを閉じた瞬間、左右 source は exact seventh powers となり、本物の ramified depth descent が発動します。

[PR に最大推論を記録済み](https://github.com/Deskuma/dkmath/pull/65#issuecomment-5105744198)
