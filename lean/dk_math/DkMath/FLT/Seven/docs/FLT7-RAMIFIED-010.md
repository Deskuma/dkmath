# FLT7-RAMIFIED-010 (011,012)

## FLT7-RAMIFIED-009 判定

**Outcome A、全面採用です。** 🧠🧠✨️

RAMIFIED-009 は、receiver branch を判別式 $49$ の実三次環へ正しく接続しました。

```text
Norm(ηL) = l^7
Norm(ηR) = r^7

ηR - ηL = π n
n = 7^4 m^7

ηR - ηL = ϖ^6 Z^7
```

`SevenRealCubicInt` は可換環・乗法的 determinant norm・左右 cubic norm・ramified axis・明示的 unit inverse まで自前で保持しています。norm が七乗だから元も七乗、という飛躍を行わず、maximality・ideal・class group・unit class を独立義務として止めた境界も正確です。

公開 head は `ddabbde22980a7a9e8637eea65b4d29f77553809`、PR は open / draft / mergeable、Lean CI run 411 も成功しました。

ここから最大推論を始めます。

## 1. 最大整環への隠し扉は「平行移動」

現在の生成元を $\alpha$ とし、

$$
\theta=\alpha-3
$$

と置きます。

既存の関係、

$$
\alpha^3=2\alpha^2+\alpha-1
$$

へ代入すると、

$$
\boxed{\theta^3+7\theta^2+14\theta+7=0}
$$

です。

この多項式は $7$-Eisenstein です。

しかも、さらにまとまります。

$$
\boxed{\theta^3=-7(\theta+1)^2}
$$

ここで、

$$
\theta+1=\alpha-2
$$

は明示的 unit です。実際、

$$
(\alpha-2)(\alpha^2-1)=1
$$

となります。

現在の ramified axis、

$$
\pi=1+2\alpha
$$

も、この Eisenstein generator と unit 倍で一致します。

$$
\boxed{\pi=-\theta\alpha(\alpha+1)}
$$

$\alpha$ と $\alpha+1$ は unit なので、$\pi$ と $\theta$ は同じ唯一の ramified prime を表します。

これは RAMIFIED-010 の maximality を大幅に短縮します。

```text
現在の π:
  norm・cube・unit normalization に便利

新しい θ = α - 3:
  Eisenstein・maximality・local uniformizer に便利
```

両方を保持し、associate theorem で接続するのが最善です。

## 2. maximality はほぼ一手になる

order discriminant はすでに $49$ です。

* $q\ne7$ なら $q\nmid49$ なので、order index に $q$ は入りません。
* $q=7$ では $\theta$ の多項式が Eisensteinなので、局所環 $\mathbb Z_7[\theta]$ は完全整数環になります。

従って、

$$
\boxed{\mathbb Z[\alpha]=\mathbb Z[\theta]=\mathcal O_K}
$$

へ進めます。

別経路として、order index の二乗が $49$ を割るため、proper index は $7$ しかありません。index $7$ なら field discriminant が $1$ になりますが、非自明な三次体では不可能です。

Lean APIとの相性で、

```text
Eisenstein local maximality
```

または、

```text
discriminant/index exclusion
```

の短い方を選べます。

## 3. class number one も極小 bound

この体は三次 totally real、discriminant $49$ です。

Minkowski bound は、

$$
\frac{3!}{3^3}\sqrt{49}=\frac{14}{9}<2
$$

です。

各 ideal class は norm が $\frac{14}{9}$ 以下の integral ideal を含みます。しかし ideal norm は正整数なので、可能なのは norm $1$ だけです。

したがって、

$$
\boxed{h_K=1}
$$

です。

ここは巨大な class-group 計算ではありません。

```text
maximality
  ↓
disc = 49
  ↓
Minkowski bound = 14/9
  ↓
class number = 1
```

という一直線です。

## 4. 明示的な三次 Galois 回転

この実三次体は cyclic です。生成元上の回転は、

$$
\sigma(\alpha)=\alpha^2-2\alpha
$$

$$
\sigma^2(\alpha)=-\alpha^2+\alpha+2
$$

$$
\sigma^3(\alpha)=\alpha
$$

です。

これは `SevenRealCubicInt` の三座標上で直接定義できます。

この automorphism が重要なのは、source element の conjugate ideal coprimality を証明するためです。

左 source を、

$$
\eta_L=a-\alpha n
$$

とします。

もし prime ideal $\mathfrak q$ が $\eta_L$ と $\sigma(\eta_L)$ の双方を割れば、その差、

$$
\sigma(\eta_L)-\eta_L=-n(\sigma(\alpha)-\alpha)
$$

も割ります。

そして、

$$
\sigma(\alpha)-\alpha=\alpha(\alpha-3)=\alpha\theta
$$

です。

$\alpha$ は unit なので、共通 ideal は、

```text
θ を割る
```

または、

```text
n を割る
```

のどちらかです。

* $\theta$ を割る場合：$\eta_L\equiv a$ ですが $7\nmid a$ なので不可能。
* $n$ を割る場合：$\eta_L=a-\alpha n$ も割るため $a$ も割り、$\gcd(a,n)=1$ に反します。

よって三つの conjugate principal ideals は pairwise coprime です。

右 source も同様です。

## 5. norm 七乗から ideal 七乗へ

RAMIFIED-009 は、

$$
N(\eta_L)=l^7
$$

を固定しています。

三 conjugate ideals の積は、

$$
(\eta_L)(\sigma\eta_L)(\sigma^2\eta_L)=(l)^7
$$

です。

左の三 ideal は pairwise coprime なので、各 prime-ideal exponent は個別に $7$ の倍数でなければなりません。

従って、

$$
(\eta_L)=\mathfrak a_L^7
$$

です。

class number one により、

$$
\mathfrak a_L=(\xi_L)
$$

なので、ある unit $u_L$ が存在して、

$$
\boxed{\eta_L=u_L\xi_L^7}
$$

となります。

同様に、

$$
\boxed{\eta_R=u_R\xi_R^7}
$$

です。

ここまでで RAMIFIED-012 の element-level extraction のうち、unit 直前までが閉じます。

## 6. unit 問題は二個ではなく一個

以前の設計では、

```text
uL を七乗へ消す
uR を七乗へ消す
```

という二つの義務に見えていました。

しかし本当に必要なのは比だけです。

$$
q=u_Ru_L^{-1}
$$

が七乗、

$$
q=s^7
$$

なら、

$$
\eta_R=u_L(s\xi_R)^7
$$

なので source difference は、

$$
u_L\left((s\xi_R)^7-\xi_L^7\right)=\varpi^6Z^7
$$

です。

従って、

$$
(s\xi_R)^7-\xi_L^7=u_L^{-1}\varpi^6Z^7
$$

となります。

ここで任意の unit $u$ は、

$$
\boxed{u=(u^{-1})^6u^7}
$$

と分解できます。$1=-6+7$ の Bézout 分解です。

従って共通 unit $u_L^{-1}$ は、axis の六乗側と witness の七乗側へ必ず吸収できます。

つまり必要なのは、

$$
\boxed{u_R/u_L\text{ が七乗}}
$$

だけです。

unit 義務が半分以下になりました。

## 7. source difference は unit 比を局所七乗にする

RAMIFIED-009 は、

$$
\eta_R-\eta_L=\varpi^6Z^7
$$

を持っています。

$\eta_L$ と $\eta_R$ は ramified prime 上の unit なので、

$$
\frac{\eta_R}{\eta_L}
=1+\frac{\varpi^6Z^7}{\eta_L}
\in1+\mathfrak p^6
$$

です。

一方、

$$
\frac{\eta_R}{\eta_L}
=\frac{u_R}{u_L}
\left(\frac{\xi_R}{\xi_L}\right)^7
$$

です。

この局所体では $v_{\mathfrak p}(7)=3$ です。principal-unit filtration では、七乗写像が概ね、

$$
U_i\longrightarrow U_{i+3}
$$

を与えるため、

$$
U_6\subseteq(K_{\mathfrak p}^{\times})^7
$$

となります。

従って、

$$
\boxed{u_R/u_L\text{ は局所七乗}}
$$

です。

残る unit theorem は、非常に狭い形になります。

```lean
theorem globalUnit_isSeventhPower_of_localDepthSix
    (u : SevenRealCubicIntˣ)
    (hu : u ≡ 1 mod ramifiedPrime^6) :
    ∃ v, u = v^7
```

一般的な unit group の全分類を公開 API にする必要はありません。

## 8. 49 unit class の有限監査

unit rank は $2$ です。

候補 generator は、

$$
\alpha,\qquad1+\alpha
$$

です。

これらが unit group を生成することを確定すれば、unit modulo seventh powers は、

$$
(\mathbb Z/7\mathbb Z)^2
$$

で、候補は $49$ 個です。

$$
u_{i,j}=\alpha^i(1+\alpha)^j,\qquad0\le i,j<7
$$

ramified local seventh-power criterionとして、

$$
u_{i,j}^6\equiv1\pmod{\theta^4}
$$

を有限監査すると、私の独立計算では、

$$
\boxed{i=j=0}
$$

だけが通ります。

これはまだ Lean 固定前の予測ですが、意味は明確です。

$$
\boxed{\text{global unit class}\to\text{local unit class が injective}}
$$

従って、局所七乗である $u_R/u_L$ は global seventh power です。

## 9. 整数脳：signed-root gap の exact depth

同時に RAMIFIED-009B は独立して進められます。

記号を、

$$
a=\operatorname{innerRoot.fst},\qquad n=\operatorname{innerRoot.snd}=7^4m^7
$$

とします。

RAMIFIED-008・009 により、

$$
r^7-l^7=7an(a+n)
$$

です。

primitive 性と $v_7(n)=4$ から、

$$
7\nmid a,\qquad7\nmid(a+n),\qquad7\nmid m
$$

です。

従って、

$$
v_7(r^7-l^7)=5
$$

です。

$l,r$ は coprime な $7$-units で、$7\mid r-l$ です。LTE により、

$$
v_7(r^7-l^7)=v_7(r-l)+1
$$

なので、

$$
\boxed{v_7(r-l)=4}
$$

です。

これは inner quadratic coordinate の depth $4$ が、signed cubic roots の gap へ完全転送されたことを意味します。

## 10. 新しい inner 2×3 routing

次を定義します。

$$
r-l=7^4d
$$

$$
\Phi_7(r,l)=7E
$$

ここで、

$$
\Phi_7(r,l)=r^6+r^5l+r^4l^2+r^3l^3+r^2l^4+rl^5+l^6
$$

です。

$\gcd(l,r)=1$ と $7\mid r-l$ から、

$$
v_7(\Phi_7(r,l))=1
$$

であり、

$$
\gcd(|d|,|E|)=1
$$

です。

七乗差を分解し、$7^5$ を消去すると、

$$
\boxed{|d|\cdot|E|=|a|\cdot|a+n|\cdot|m|^7}
$$

となります。

右側の三因子も pairwise coprime です。

従って、また正式な `CoprimeTripleRouting` が作れます。

```text
                 |a|       |a+n|       |m|^7
              ┌────────┬──────────┬──────────┐
|d|           │  d11   │   d12    │   U^7    │
              ├────────┼──────────┼──────────┤
|E|           │  d21   │   d22    │   V^7    │
              └────────┴──────────┴──────────┘
```

これは RAMIFIED-006 の routing が、一段内側で再出現したものです。

```text
outer:
  root.snd × sndCore

inner:
  signed-root gap × cyclotomic quotient
```

完全な自己相似です。

## 11. quotient 側の prime support

$q\ne7$ が $E$ を割るとします。

すると、

$$
\Phi_7(r,l)\equiv0\pmod q
$$

で、$l,r$ は $q$-units です。

従って $r/l$ は $\mathbf F_q^\times$ 上の非自明な位数 $7$ の元です。

よって、

$$
\boxed{q\equiv1\pmod7}
$$

です。

つまり inner quotient $E$ に入る素数は、すべて $7$ 次根を持つ split-prime sector に限定されます。

```text
d:
  一般 prime channel

E:
  q ≡ 1 mod 7 の cyclotomic split channel
```

これは実三次 ideal 分解の整数 shadow です。

## 12. inner first-order congruence

$r=l+7^4d$ を七乗展開し mod $7^6$ で見ると、

$$
r^7-l^7\equiv7^5l^6d\pmod{7^6}
$$

です。

右辺は、

$$
7an(a+n)=7^5a(a+n)m^7
$$

です。

mod $7$ では、

$$
l^6=1,\qquad a+n\equiv a,\qquad m^7=m
$$

なので、

$$
\boxed{d\equiv a^2m\pmod7}
$$

です。

さらに receiver branch の residual-root 条件と cubic norm equationを組み合わせると、

$$
\boxed{a\equiv\pm1\pmod{49}}
$$

まで縮む見込みです。

すると、

$$
\boxed{d\equiv m\pmod7}
$$

になります。

terminal first-order unit sector が、inner depth-four 層で再生しています。

## 13. element-level 抽出後の純粋 second-case equation

ideal と relative unit class を消せれば、

$$
\boxed{X^7-Y^7=\Omega^6W^7}
$$

という実三次環上の純粋 equation が得られます。

ここで $\Omega$ は $\pi,\theta,\varpi$ と associate な ramified axis です。

現在の `normalizedWitness` は ramified axis を一つ含み、$m$ は $7$-unit なので、

$$
v_\Omega(W)=1
$$

です。

従って右辺の complete depth は、

$$
6+7=13
$$

です。

一方、

$$
X^7-Y^7=(X-Y)\Phi_7(X,Y)
$$

です。

$X,Y$ が $\Omega$-units で $\Omega\mid X-Y$ なら、局所展開から、

$$
\boxed{v_\Omega(\Phi_7(X,Y))=v_\Omega(7)=3}
$$

です。

従って、

$$
\boxed{v_\Omega(X-Y)=13-3=10}
$$

です。

すなわち、

$$
10=3+7
$$

なので、away prime factorization と class number one を使えば、

$$
\boxed{X-Y=\text{unit}\cdot\Omega^3T^7}
$$

へ進めます。

unit は $1=-2\cdot3+7$ により、三乗側と七乗側へ吸収できます。

よって最終的に、

$$
\boxed{X-Y=\widetilde\Omega^3\widetilde T^7}
$$

という **axis depth $6\to3$ の降下**が現れます。

現在までの depth ladder は、

```text
endpoint gap                  6
outer root.snd                5
inner root.snd                4

real-cubic source gap        13
seventh-root pair gap        10
normalized ramified core      3
```

です。

## 次の実装順

### FLT7-RAMIFIED-009B

既存 Int/Nat API だけで閉じます。

```text
gcd(|l|,|r|) = 1
7 ∤ l
7 ∤ r

v7(|r-l|) = 4
v7(|Φ7(r,l)|) = 1

r-l = 7^4*d
Φ7(r,l) = 7*E

|d|*|E| = |a|*|a+n|*|m|^7

CoprimeTripleRouting
d ≡ a^2*m mod 7

prime q ∣ E → q ≡ 1 mod 7
```

### FLT7-RAMIFIED-010A

```text
θ = α - 3
θ^3 + 7θ^2 + 14θ + 7 = 0
θ^3 = -7(θ+1)^2
IsUnit (θ+1)
π = unit * θ

irreducibility
integral-domain / number-field carrier
maximal order
```

### FLT7-RAMIFIED-010B

```text
disc K = 49
Minkowski bound = 14/9
class number = 1

σ(α) = α^2 - 2α
σ^3 = id
```

### FLT7-RAMIFIED-011

```text
source conjugate ideals pairwise coprime

(ηL) = idealL^7
(ηR) = idealR^7

ηL = uL * ξL^7
ηR = uR * ξR^7
```

### FLT7-RAMIFIED-011U

公開 theorem は unit 全分類ではなく、狭くします。

```text
uR / uL is local seventh power
  →
uR / uL is global seventh power
```

内部証明として unit generator と $49$ class audit を使います。

### FLT7-RAMIFIED-012

```text
X^7 - Y^7 = Ω^6 * W^7

vΩ(W) = 1
vΩ(Φ7(X,Y)) = 3
vΩ(X-Y) = 10

X-Y = Ω̃^3 * T^7
```

## 結論

RAMIFIED-009 の続きで、敵は三つに圧縮されました。

```text
1. θ = α-3 による Eisenstein maximality

2. source ideal の七乗抽出

3. 一個だけ残る relative unit class
```

そして relative unit が消えた瞬間、

$$
X^7-Y^7=\Omega^6W^7
$$

から、

$$
X-Y=\widetilde\Omega^3T^7
$$

への厳密な ramified depth drop が始まります。

**最大整環・class number・unit class は別々の巨大な敵ではありません。**

Eisenstein 軸 $\theta$ を中心に置けば、

```text
maximality
→ class number one
→ ideal seventh powers
→ relative unit one class
→ depth 13 = 10 + 3
```

という一本の術式になります。

ここが次の本街道です。
