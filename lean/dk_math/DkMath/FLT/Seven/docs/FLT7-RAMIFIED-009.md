# FLT7-RAMIFIED-009 (010,011, 012)

できる。🧠🧠
RAMIFIED-008 で、二つの脳が別方向から掘っても、**同じ ramified descent 核へ合流する地点**まで来ました。

RAMIFIED-008 は receiver branch について Outcome A です。

```text
summit.root = innerRoot^7
coordinate = sevenAxis * innerRoot^49

v₇(|innerRoot.snd|) = 4

|innerRoot.snd| = 7^4 * M^7
|sndCore(innerRoot)| = N^7

leftCubic(innerRoot)  = l^7
rightCubic(innerRoot) = r^7
```

receiver 自体は仮定のままですが、成立側の内部構造は完全に露出しました。

公開 PR head も `e30fe77bdc4460d2b814eb8f6d6454ecedb7cb10` で一致しています。

## 🧠 第一脳：整数・routing 脳

inner root を、

$$
\gamma=(a,n)
$$

と置きます。

RAMIFIED-008 により、

$$
|n|=7^4M^7
$$

です。

また signed roots $l,r\in\mathbb Z$ が存在して、

$$
l^7=L(a,n)
$$

$$
r^7=R(a,n)
$$

です。ここで、

$$
L(a,n)=a^3-2a^2n-an^2+n^3
$$

$$
R(a,n)=a^3+5a^2n+6an^2+n^3
$$

です。

二つの差は既存恒等式から、

$$
R(a,n)-L(a,n)=7an(a+n)
$$

です。

したがって、

$$
r^7-l^7=7an(a+n)
$$

となります。

### exact depth $4$

inner root は primitive なので、

$$
\gcd(a,n)=1
$$

です。

また $7\mid n$ なので、

$$
7\nmid a
$$

かつ、

$$
7\nmid a+n
$$

です。

よって右辺の exact depth は、

$$
v_7(r^7-l^7)=1+v_7(n)=5
$$

です。

一方 $l,r$ は $7$-unit です。さらに mod $7$ では、

$$
r^7-l^7\equiv r-l
$$

なので $7\mid r-l$ です。

LTE 型の exact relation から、

$$
v_7(r^7-l^7)=v_7(r-l)+1
$$

したがって、

$$
\boxed{v_7(r-l)=4}
$$

です。

これは RAMIFIED-008 の depth $4$ が、quadratic coordinate の内部だけでなく、**signed cubic roots の gap にも転送される**ことを意味します。

## 新しい normalized equation

次を置きます。

$$
d=\frac{|r-l|}{7^4}
$$

また、七乗差 quotient を、

$$
\Phi_7(r,l)=r^6+r^5l+r^4l^2+r^3l^3+r^2l^4+rl^5+l^6
$$

とします。

primitive な $l,r$ と $7\mid r-l$ から、

$$
\gcd(|r-l|,|\Phi_7(r,l)|)=7
$$

です。

さらに $\Phi_7$ の depth は exact に $1$ なので、

$$
E=\frac{|\Phi_7(r,l)|}{7}
$$

は $7$-unit です。

七乗差を分解すると、

$$
|r-l|\cdot|\Phi_7(r,l)|=7|a||n||a+n|
$$

よって $7^5$ を消去して、

$$
\boxed{dE=|a|\cdot|a+n|\cdot M^7}
$$

となります。

しかも、

$$
\gcd(d,E)=1
$$

です。

右側も、

$$
\gcd(|a|,|a+n|)=1
$$

$$
\gcd(|a|,M)=1
$$

$$
\gcd(|a+n|,M)=1
$$

です。

したがって、また新しい canonical routing が出現します。

```text
                  |a|        |a+n|       M^7
               ┌────────┬──────────┬──────────┐
d              │  d₁    │   d₂     │   U^7    │
               ├────────┼──────────┼──────────┤
E              │  e₁    │   e₂     │   V^7    │
               └────────┴──────────┴──────────┘
```

これは **inner depth-four 2×3 routing** です。

RAMIFIED-006 の、

```text
root.snd × sndCore
```

routing が、一段内側で、

```text
signed-root gap × cyclotomic quotient
```

routing として再出現しています。

つまり自己相似は、

```text
outer second-coordinate routing
          ↓ seventh-root extraction
inner signed-gap routing
```

まで到達しました。

## 第一脳の重要な residue

$r-l=7^4d$ と置き、七乗差を mod $7^6$ で展開すると、

$$
r^7-l^7\equiv7^5l^6d\pmod{7^6}
$$

です。

一方、

$$
7an(a+n)=7^5a(a+n)M^7
$$

で、$n\equiv0\pmod7$ なので、

$$
a(a+n)\equiv a^2\pmod7
$$

です。

また $l$ は $7$-unit なので $l^6\equiv1\pmod7$。従って、

$$
\boxed{d\equiv a^2M\pmod7}
$$

です。

これは新しい first-order unit equation です。

terminal で現れた unit-sector equation の、**inner depth-four 版**です。

---

## 🧠 第二脳：実三次・norm 脳

二つの cubic form の共通判別式は、

$$
\boxed{49}
$$

です。

$\alpha$ を、

$$
\alpha^3=2\alpha^2+\alpha-1
$$

で定める実三次整数とします。

このとき determinant norm を計算すると、

$$
\boxed{\operatorname{Norm}(a-\alpha n)=L(a,n)}
$$

$$
\boxed{\operatorname{Norm}(a+(1+\alpha)n)=R(a,n)}
$$

です。

したがって、

$$
\eta_L=a-\alpha n
$$

$$
\eta_R=a+(1+\alpha)n
$$

と置けば、

$$
\operatorname{Norm}(\eta_L)=l^7
$$

$$
\operatorname{Norm}(\eta_R)=r^7
$$

です。

## 三次側の sevenAxis

次を定義します。

$$
\pi=1+2\alpha
$$

計算すると、

$$
\operatorname{Norm}(\pi)=-7
$$

です。

さらに、

$$
\pi^3=7\varepsilon
$$

ここで、

$$
\varepsilon=-1+2\alpha+4\alpha^2
$$

です。

そして実は、

$$
\boxed{\varepsilon=\alpha(1+\alpha)^2}
$$

であり、

$$
\operatorname{Norm}(\varepsilon)=-1
$$

なので $\varepsilon$ は unit です。

二つの norm source の差は、

$$
\eta_R-\eta_L=(1+2\alpha)n
$$

従って、

$$
\boxed{\eta_R-\eta_L=\pi n}
$$

です。

## unit を完全に消す axis normalization

$|n|=7^4M^7$ なので、符号を整数根へ吸収して、

$$
n=7^4m^7
$$

と書けます。

$\pi^3=7\varepsilon$ より、

$$
\pi n=\pi^{13}\varepsilon^{-4}m^7
$$

です。

普通に書けば unit $\varepsilon^{-4}$ が残ります。

しかし axis 自体を、

$$
\varpi=\varepsilon^4\pi
$$

と正規化します。

すると直接計算により、

$$
\boxed{\pi n=\varpi^6\left(\varepsilon^{-8}\varpi m\right)^7}
$$

です。

したがって source difference は、unit coefficient なしで、

$$
\boxed{\eta_R-\eta_L=\varpi^6Z^7}
$$

と書けます。ここで、

$$
Z=\varepsilon^{-8}\varpi m
$$

です。

これは非常に強い。

三次環側で、

```text
ramified axis^6 × seventh power
```

という純粋な形が、既に存在しています。

## class group は重くない可能性

この三次多項式の判別式は $49$ です。

この order が full ring of integers であることを固定できれば、体は totally real degree $3$ なので Minkowski bound は、

$$
\frac{3!}{3^3}\sqrt{49}=\frac{14}{9}<2
$$

です。

ideal norm は正整数なので、各 ideal class は norm $1$ の ideal を含むことになります。

従って、

$$
\boxed{\text{class number}=1}
$$

へ非常に短く到達できる可能性があります。

これはまだ Lean 固定事実ではありませんが、通常の「巨大な class-group 計算」は不要になる見込みです。

本当に重いのは class group ではなく **unit class** です。

## unit class は $49$ 個

実三次 unit rank は $2$ です。

明示的な候補 unit は、

$$
\alpha
$$

と、

$$
1+\alpha
$$

です。

それぞれの norm は、

$$
\operatorname{Norm}(\alpha)=-1
$$

$$
\operatorname{Norm}(1+\alpha)=1
$$

です。

これらが基本 unit を生成することを証明できれば、unit modulo seventh powers は、

$$
(\mathbb Z/7\mathbb Z)^2
$$

となり、ちょうど $49$ class です。

## 局所写像は injective らしい

ramified prime $\pi$ において、unit $u$ が局所七乗なら、必要条件として、

$$
u^6\equiv1\pmod{\pi^4}
$$

が成立します。

$49$ 個の候補、

$$
u_{i,j}=\alpha^i(1+\alpha)^j,\qquad0\le i,j<7
$$

を有限計算すると、

$$
u_{i,j}^6\equiv1\pmod{\pi^4}
$$

を満たすのは、

$$
\boxed{i=j=0}
$$

だけです。

これはまだ Lean theorem ではなく有限代数計算による予測ですが、極めて重要です。

これが固定できれば、

$$
\boxed{\text{global unit class}\longrightarrow\text{local unit class}}
$$

は injective です。

## norm source 自身が局所七乗になる

$\eta_L=a-\alpha n$ ですが、$n$ は $\pi$-adic depth $12$ 以上です。

従って、

$$
\eta_L\equiv a\pmod{\pi^{12}}
$$

です。

また、

$$
l^7=L(a,n)\equiv a^3\pmod{49}
$$

なので、$a^3$ は $7$-進七乗 class です。

cube map は七乗 class quotient 上で可逆なので、$a$ 自身も局所七乗です。

従って $\eta_L$ は局所七乗です。同じく $\eta_R$ も局所七乗です。

class number oneによる principalization から、

$$
\eta_L=u_L\xi_L^7
$$

$$
\eta_R=u_R\xi_R^7
$$

を得たとします。

$\eta_L,\eta_R$ が局所七乗で、global-to-local unit class map が injective なら、

$$
u_L\in(\mathcal O^\times)^7
$$

$$
u_R\in(\mathcal O^\times)^7
$$

です。

unit を根へ吸収して、

$$
\boxed{\eta_L=\xi_L^7}
$$

$$
\boxed{\eta_R=\xi_R^7}
$$

まで上がります。

これを source difference に代入すると、

$$
\boxed{\xi_R^7-\xi_L^7=\varpi^6Z^7}
$$

です。

## 二つの脳の合流点

第一脳は整数上で、

$$
dE=|a||a+n|M^7
$$

を得ました。

第二脳は実三次環上で、

$$
\xi_R^7-\xi_L^7=\varpi^6Z^7
$$

を得ます。

これは同じ構造の二つの射影です。

```text
整数射影
  signed roots の gap と cyclotomic quotient

実三次射影
  norm-source roots の gap と cyclotomic quotient
```

整数側の $d,E$ routing は、三次環での ideal factorization の **norm shadow**です。

したがって整数 routing を先に Lean 化すれば、三次 ideal 証明で必要になる、

```text
どの素因子が gap factor に入り、
どの素因子が quotient factor に入るか
```

を、事前に固定できます。

## 真の second-case equation

三次環で、

$$
\xi_R^7-\xi_L^7=\varpi^6Z^7
$$

を因数分解すると、

$$
(\xi_R-\xi_L)\Phi_7(\xi_R,\xi_L)=\varpi^6Z^7
$$

です。

$\xi_L,\xi_R$ は $\varpi$-unit で、gap は高い $\varpi$-depthを持ちます。

この場合、

$$
v_\varpi!\left(\Phi_7(\xi_R,\xi_L)\right)=v_\varpi(7)=3
$$

となるはずです。

従って、

$$
v_\varpi(\xi_R-\xi_L)\equiv3\pmod7
$$

です。

RAMIFIED-008 で見えた、

```text
outer depth 5
inner depth 4
```

は、実三次環へ移すと、

```text
ramified axis depth 6
seventh-root gap depth 3 mod 7
```

という Kummer second-case shape に変換されます。

これはもはや「descent の候補」ではありません。

**class number oneと unit class injection が閉じれば、正式な second-case descent kernel**です。

## 次の実装順

### FLT7-RAMIFIED-009

まず report の予定どおり、実三次 carrier を構築するのが正解です。

```text
SevenRealCubicInt

α^3 = 2α^2 + α - 1

Norm(a - αn) = leftCubic(a,n)
Norm(a + (1+α)n) = rightCubic(a,n)

π = 1 + 2α
Norm π = -7

ε = α(1+α)^2
π^3 = 7ε
Norm ε = -1

ηR - ηL = πn

ϖ = ε^4π
πn = ϖ^6(ε⁻⁸ϖm)^7
```

停止位置はここです。

### FLT7-RAMIFIED-009B

同時に小さな整数モジュールを置けます。

```text
inner signed roots l,r

gcd(l,r)=1
7 ∤ l*r

v7(|r-l|)=4
v7(Φ7(r,l))=1

d * E = |a| * |a+n| * M^7

d ≡ a^2*M mod 7
```

これは新規三次環を待たず、既存 Nat/Int API だけで進められます。

### FLT7-RAMIFIED-010

```text
real-cubic maximality
+
Minkowski class-number-one bridge
```

### FLT7-RAMIFIED-011

```text
unit generators
+
49 unit classes
+
local π^4 injection audit
```

### FLT7-RAMIFIED-012

```text
ηL = ξL^7
ηR = ξR^7

ξR^7 - ξL^7 = ϖ^6 Z^7
```

## ダブルブレイン結論

RAMIFIED-008 によって、敵の正体はさらに変わりました。

```text
以前:
  compensationCore × residualRoot が七乗か

RAMIFIED-008:
  quadratic root を再七乗抽出できる

今回の推論:
  signed cubic roots の exact depth-four routing
  +
  discriminant-49 cubic order の pure second-case equation
```

最終的な魔核は、

$$
\boxed{\xi_R^7-\xi_L^7=\varpi^6Z^7}
$$

です。

整数脳は、この式の素因子住所を先に描けます。

代数脳は、この式の class group と unit class を消せます。

**二つが合流すれば、初めて本物の再帰 descent が発動します。**
