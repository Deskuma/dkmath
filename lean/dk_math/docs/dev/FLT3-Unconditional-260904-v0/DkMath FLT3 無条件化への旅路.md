# DkMath FLT3 無条件化への旅路

## 1. 長く残っていた最後の仮定

DkMath における FLT3 の証明は、以前からかなり深いところまで形式化されていた。

その中心には次の定理があった。

```lean
theorem FLT_d3_by_padicValNat {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hS0_not_sq :
      ∀ {q : ℕ}, Nat.Prime q →
        q ∣ c ^ 3 - b ^ 3 →
        ¬ q ∣ c - b →
        ¬ q ^ 2 ∣ S0_nat c b) :
    a ^ 3 + b ^ 3 ≠ c ^ 3
```

証明そのものは通っている。

問題はただ一つ。

`hS0_not_sq`

という追加仮定が残っていた。

これは、primitive prime $q$ が

$$
S_0(c,b)=c^2+cb+b^2
$$

を二乗以上の深さで割らない、という仮定であった。

FLT3 の式

$$
a^3+b^3=c^3
$$

から

$$
a^3=c^3-b^3=(c-b)(c^2+cb+b^2)
$$

となる。

primitive prime $q$ が $c-b$ を割らず $S_0$ 側へ入るなら、

$$
v_q(S_0)=v_q(a^3)=3v_q(a)
$$

である。

一方、`hS0_not_sq` があれば

$$
v_q(S_0)\le1
$$

となる。

つまり、

$$
3\le v_q(S_0)\le1
$$

という即時矛盾で FLT3 は閉じる。

非常に強い証明であった。

だが、その強さは `hS0_not_sq` に依存していた。

長い間、ここが FLT3 の魔核として残った。

---

## 2. NoLift を証明しようとしていた時代

当初の発想は自然であった。

「ならば `hS0_not_sq` 自体を証明してしまえばよい」

というものだった。

つまり primitive prime $q$ について、

$$
q\mid S_0
$$

なら

$$
q^2\nmid S_0
$$

を示そうとした。

この方向から Hensel lift、derivative、primitive divisor、valuation などを調べた。

GN3 の構造もこの文脈で整理された。

$$
GN_3(u,x)=u^2+3ux+3x^2
$$

そして

$$
S_0(c,b)=GN_3(c-b,b)
$$

である。

さらに primitive coordinates では、

$$
3\mid GN_3(u,x)\iff3\mid u
$$

や $q\ne3$ の primitive prime について、

$$
3\mid q-1
$$

という split-prime 条件も得られた。

derivative 側にも、

$$
q\nmid 2u+3x
$$

という simple-root 条件があった。

ここまで揃うと、一見すると

「primitive prime は simple root なのだから深く lift できないのではないか」

と思いたくなる。

しかし、これは違った。

---

## 3. 決定的な反例 — Deep Lift は存在する

転換点となったのが GN3 の具体例である。

$$
GN_3(17,1)=343=7^3
$$

したがって、

$$
7^2\mid GN_3(17,1)
$$

どころか

$$
7^3\mid GN_3(17,1)
$$

である。

つまり universal な

> primitive prime は二乗以上 lift しない

という命題そのものが偽だった。

`hS0_not_sq` は一般 GN3 に対して証明可能な性質ではない。

ここで FLT3 無条件化の問題設定そのものが変わった。

NoLift を証明するのではない。

むしろ hypothetical FLT3 counterexample では、

$$
v_q(GN_3)=3v_q(a)
$$

だから primitive prime は必ず **high-lift branch** に入る。

つまり FLT3 の仮想反例は、

> lift を避ける世界

ではなく、

> cube-depth lift を強制される世界

だった。

この認識が、証明全体の方向を変えた。

---

## 4. Local Hensel から Global Descent へ

GN3 Hensel 系の実装により、simple root の lift は有限深度で一意に追跡できることも分かった。

しかし Hensel 理論は、

「深い root が存在しない」

とは言わない。

むしろ深い branch があれば、それを追跡する。

したがって FLT3 に必要なのは local lifting の禁止ではなかった。

必要なのは、

> 深く lift した仮想反例そのものから、より小さい仮想反例を再構成する

ことであった。

ここで古典的な Eisenstein integer descent が、DkMath の GN3 / Cosmic Formula の構造と接続した。

---

## 5. FLT3U-003 — Eisenstein 整数の土台

DkMath には既に一般的な trace-one quadratic ring

```lean
TraceOneInt s
```

が存在していた。

FLT3 では

```lean
TraceOneInt (-1)
```

を採用し、

```lean
abbrev EisensteinInt := TraceOneInt (-1)
```

とした。

この basis は古典的な $\omega^2+\omega+1=0$ ではない。

DkMath の座標では

$$
\tau^2-\tau+1=0
$$

すなわち

$$
\tau^2=\tau-1.
$$

この convention を最後まで守ることが非常に重要だった。

norm は

$$
N(r+s\tau)=r^2+rs+s^2.
$$

conjugation は

$$
\overline{r+s\tau}=(r+s)-s\tau.
$$

そして ramifier を

$$
\lambda=1+\tau
$$

と置くと、

$$
N(\lambda)=3
$$

かつ

$$
\lambda^2=3\tau.
$$

さらに cube coordinate は

$$
(r+s\tau)^3=(r^3-3rs^2-s^3)+3rs(r+s)\tau.
$$

したがって第二座標は、

$$
((r+s\tau)^3)_{\rm snd}=3rs(r+s).
$$

この $r+s$ が、後の descent の中心となる。

---

## 6. FLT3U-004A — 3-adic routing

次に primitive FLT3 counterexample を mod $9$ で分類した。

仮想解

$$
a^3+b^3=c^3
$$

では $a,b,c$ のちょうど一つだけが $3$ で割れる。

その位置に応じて三つの orientation を作り、共通の packet に正規化した。

そこで現れた量は、

$$
\mathrm{carrier},
\qquad
\mathrm{residual},
\qquad
\mathrm{distinguished}.
$$

そして exact power split により、

$$
\mathrm{carrier}=9A^3,
$$

$$
\mathrm{residual}=3B^3,
$$

$$
\mathrm{distinguished}=3AB,
$$

さらに、

$$
\gcd(A,B)=1,
\qquad
3\nmid B
$$

を得た。

ここで prime $3$ の ramified load が完全に整理された。

---

## 7. FLT3U-004B — Ramifier を一度剥がす

signed Eisenstein element $\alpha$ に対して、

$$
\alpha=\lambda\beta
$$

となる $\beta$ を明示的に構成した。

すると norm は、

$$
N(\alpha)=3B^3
$$

および

$$
N(\lambda)=3
$$

より、

$$
N(\beta)=B^3.
$$

さらに座標計算から、

$$
\beta_{\rm snd}=3A^3.
$$

この二本の式が、その後すべてを動かした。

$$
N(\beta)=B^3
$$

$$
\beta_{\rm snd}=3A^3.
$$

---

## 8. FLT3U-005 — $\beta$ と共役の coprimality

次に、

$$
\beta
\quad\text{と}\quad
\overline\beta
$$

が common nonunit divisor を持たないことを証明した。

共通因子 $d$ があれば、

$$
d\mid\beta,
\qquad
d\mid\overline\beta
$$

なので、

$$
d\mid\beta-\overline\beta.
$$

そして

$$
N(\beta-\overline\beta)=27A^6.
$$

一方、

$$
N(\beta)=B^3.
$$

したがって $N(d)$ は $B^3$ と $27A^6$ の両方を割る。

しかし、

$$
\gcd(A,B)=1,
\qquad
3\nmid B.
$$

よって共通 norm は $1$ しかあり得ない。

したがって $d$ は unit。

これにより、

$$
\beta
\quad\text{と}\quad
\overline\beta
$$

は Eisenstein ring 上で relatively prime となった。

---

## 9. FLT3U-006A — Eisenstein ring を EuclideanDomain にする

cube extraction を安全に使うため、`TraceOneInt (-1)` に honest な `EuclideanDomain` instance を構成した。

まず norm の正定値性を確認した。

$$
N(r+s\tau)=0
\iff
r=s=0.
$$

そして rational plane 上で、

$$
N_{\mathbb Q}(u,v)=u^2+uv+v^2
$$

を平方完成すると、

$$
N_{\mathbb Q}(u,v)=\left(u+\frac v2\right)^2+\frac34v^2.
$$

skew rounding cell を取れば、

$$
N_{\mathbb Q}(u,v)\le\frac7{16}<1.
$$

よって任意の quotient に対して strict smaller remainder が取れる。

これで、

```lean
EuclideanDomain (TraceOneInt (-1))
```

が完成した。

---

## 10. FLT3U-006B — coprime cube extraction

Euclidean domain から `GCDMonoid` を得て、Mathlib の generic theorem

```lean
exists_associated_pow_of_mul_eq_pow
```

を利用した。

既に、

$$
\beta\overline\beta=B^3
$$

かつ $\beta,\overline\beta$ は coprime。

したがって、

$$
\beta=\varepsilon\gamma^3
$$

となる Eisenstein unit $\varepsilon$ と element $\gamma$ が存在する。

ここで unit を勝手に消さなかったことが重要だった。

三乗では unit cube map は全 unit に surjective ではない。

したがって、

$$
\beta=\gamma^3
$$

とはまだ言えない。

---

## 11. FLT3U-007 — 六単元と三 sector

Eisenstein unit を完全分類した。

norm $1$ の整数解、

$$
r^2+rs+s^2=1
$$

を解くと、座標はちょうど六つ。

$$
(1,0),
(-1,0),
(0,1),
(0,-1),
(-1,1),
(1,-1).
$$

つまり unit は、

$$
\pm1,
\quad
\pm\tau,
\quad
\pm\tau^2.
$$

そして既に、

$$
\tau^3=-1.
$$

したがって符号は cube factor に吸収できる。

結果、unit modulo cubes の canonical sector は三つだけ。

$$
1,
\qquad
\tau,
\qquad
\tau^2.
$$

よって、

$$
\beta=\rho\gamma^3
$$

ただし

$$
\rho\in\{1,\tau,\tau^2\}
$$

まで正規化できた。

---

## 12. FLT3U-008 — 二つの sector を消す

ここが非常に美しい局面だった。

$\gamma=r+s\tau$ とする。

$\tau$ sector の第二座標は、

$$
(\tau\gamma^3)_{\rm snd}=r^3+3r^2s-s^3.
$$

$\tau^2$ sector では、

$$
(\tau^2\gamma^3)_{\rm snd}=r^3-3rs^2-s^3.
$$

どちらも mod $3$ では、

$$
(\rho\gamma^3)_{\rm snd}
\equiv r^3-s^3
\equiv r-s
\pmod3.
$$

一方、元の packet では、

$$
\beta_{\rm snd}=3A^3.
$$

従って非自明 sector なら、

$$
3\mid r-s.
$$

すると、

$$
N(\gamma)=r^2+rs+s^2
$$

も $3$ で割れる。

しかし norm comparison から、

$$
N(\gamma)=B.
$$

従って、

$$
3\mid B,
$$

これは既知の

$$
3\nmid B
$$

と矛盾する。

よって $\tau$ と $\tau^2$ sector は両方消える。

残るのは $1$ sector のみ。

ついに、

$$
\beta=\gamma^3.
$$

---

## 13. 魔核が開く — $rs(r+s)=A^3$

$\gamma=r+s\tau$ とすると、

$$
(\gamma^3)_{\rm snd}=3rs(r+s).
$$

一方、

$$
\beta_{\rm snd}=3A^3.
$$

そして、

$$
\beta=\gamma^3.
$$

従って、

$$
3rs(r+s)=3A^3.
$$

整数上で $3$ を消して、

$$
rs(r+s)=A^3.
$$

これが descent の中心式となった。

同時に、

$$
r^2+rs+s^2=B.
$$

そして、

$$
\gcd(A,B)=1.
$$

ここまで来ると、古典的な無限降下が Lean 上で具体的な構造として見える。

---

## 14. FLT3U-009A — 三因子を cube に分解する

まず

$$
r,\qquad s,\qquad r+s
$$

が全て非零であることを示した。

そして natAbs を取る。

$$
|r|\,|s|\,|r+s|=A^3.
$$

次に三因子の pairwise coprimality を証明した。

任意の共通因子は $r,s$ の線形結合を通じて norm

$$
B=r^2+rs+s^2
$$

を割る。

同時に product equation から $A^3$ も割る。

しかし、

$$
\gcd(A,B)=1.
$$

従って common divisor は $1$ 。

よって、

$$
\gcd(|r|,|s|)=1,
$$

$$
\gcd(|r|,|r+s|)=1,
$$

$$
\gcd(|s|,|r+s|)=1.
$$

pairwise coprime な三数の積が cube なので、それぞれ cube でなければならない。

Mathlib の generic power splitting を使い、

$$
|r|=R^3,
$$

$$
|s|=S^3,
$$

$$
|r+s|=T^3.
$$

さらに、

$$
R,S,T>0
$$

かつ pairwise coprime。

そして、

$$
RST=A.
$$

---

## 15. Provenance 問題

ここで Lean 特有の重要な問題が発生した。

以前の `SignedThreeAdicPacket` は `a,b,c` を型 parameter として持っていたが、

```lean
packet.distinguished = a ∨
packet.distinguished = b ∨
packet.distinguished = c
```

という provenance を field に保持していなかった。

しかも packet は `Classical.choice` により選ばれていたため、後から「これは元のどの座標だったか」を復元できない。

このままでは strict decrease を元の $(a,b,c)$ と比較できない。

そこで、

```lean
SignedThreeAdicOriginPacket
```

を追加し、origin を明示的に保持した。

さらに power split でも同じ packet が使われたことを subtype equality で保持した。

これにより、

$$
\mathrm{distinguished}=3AB
$$

と、

$$
\mathrm{distinguished}\le abc
$$

を同じ origin 上で結べた。

従って、

$$
A<3AB=\mathrm{distinguished}\le abc.
$$

つまり、

$$
A<abc.
$$

そして既に、

$$
RST=A.
$$

だから、

$$
RST<abc.
$$

strict descent の測度がここで完成した。

---

## 16. FLT3U-009B — 符号を読み、新しい FLT3 解を作る

残る問題は符号だけだった。

元の恒等式は、

$$
r+s=(r+s).
$$

そして、

$$
|r|=R^3,
\qquad
|s|=S^3,
\qquad
|r+s|=T^3.
$$

また、

$$
rs(r+s)=A^3>0.
$$

この積が正であることから、可能な sign pattern は三つに絞られる。

### Case 1

 $r>0$ , $s>0$ 。

すると $r+s>0$ なので、

$$
R^3+S^3=T^3.
$$

新しい triple は、

$$
(R,S,T).
$$

### Case 2

 $r>0$ , $s<0$ 。

積が正なので $r+s<0$ 。

従って、

$$
R^3+T^3=S^3.
$$

新しい triple は、

$$
(R,T,S).
$$

### Case 3

 $r<0$ , $s>0$ 。

同様に $r+s<0$ 。

従って、

$$
S^3+T^3=R^3.
$$

新しい triple は、

$$
(S,T,R).
$$

 $r<0$ , $s<0$ は product positivity と矛盾する。

したがって必ず一つの positive primitive FLT3 solution が再構成される。

しかも pairwise coprimality は既にある。

そしてその積は permutation に関係なく、

$$
xyz=RST=A.
$$

よって、

$$
xyz<abc.
$$

ついに、

> 任意の positive primitive FLT3 counterexample から、より小さい positive primitive FLT3 counterexample が作れる

ことが Lean 上で完成した。

---

## 17. FLT3U-010 — 無限降下を strong induction で閉じる

ここから先は非常に短かった。

`PrimitiveCubicPack a b c` に対して measure を、

$$
m=abc
$$

とする。

すると descent theorem は、

$$
\exists x,y,z,\quad
PrimitiveCubicPack(x,y,z)
\land xyz<abc
$$

を与える。

従って `Nat.strong_induction_on` により、最小 counterexample は存在できない。

Lean theorem：

```lean
theorem primitiveCubicPack_false
    {a b c : ℕ}
    (p : PrimitiveCubicPack a b c) :
    False
```

そして primitive endpoint：

```lean
theorem FLT_d3_unconditional
    {a b c : ℕ}
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (hab : Nat.Coprime a b) :
    a ^ 3 + b ^ 3 ≠ c ^ 3
```

ここで、長く残っていた

```lean
hS0_not_sq
```

は完全に消えた。

`NoSqOnS0` も不要となった。

---

## 18. FLT3U-011 — 任意の正の自然数へ

最後に primitive assumption そのものも外した。

仮に、

$$
a^3+b^3=c^3
$$

で $a,b,c>0$ とする。

$$
d=\gcd(a,b)
$$

と置く。

すると、

$$
d\mid a,
\qquad
d\mid b.
$$

従って、

$$
d^3\mid a^3,
\qquad
d^3\mid b^3.
$$

よって equation から、

$$
d^3\mid c^3.
$$

したがって、

$$
d\mid c.
$$

そこで、

$$
a'=a/d,
\qquad
b'=b/d,
\qquad
c'=c/d.
$$

とすると、

$$
a',b',c'>0,
$$

$$
\gcd(a',b')=1,
$$

さらに scaled cancellation により、

$$
a'^3+b'^3=c'^3.
$$

つまり primitive counterexample が得られる。

しかしそれは既に `FLT_d3_unconditional` によって不可能。

従って最終 theorem：

```lean
theorem fermatThree_no_positive_solution
    (a b c : ℕ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c) :
    a ^ 3 + b ^ 3 ≠ c ^ 3
```

が完成した。

---

## 19. 最終 public surface

独立した FLT3 proof tower の入口として、

```lean
import DkMath.FLT.Three
```

を新設した。

endpoint は、

```lean
DkMath.FLT.Three.FLT_d3_unconditional
```

および、

```lean
DkMath.FLT.Three.fermatThree_no_positive_solution
```

である。

legacy の

```lean
DkMath.FLT.Main
```

は変更していない。

古い conditional theorem も削除していない。

新しい proof tower はそれとは独立して存在する。

---

## 20. 証明全体を一行で見る

最終的な旅路はこうなった。

```text
positive FLT3 counterexample
    ↓
gcd normalization
    ↓
primitive cubic packet
    ↓
signed 3-adic routing
    ↓
carrier = 9 A³
residual = 3 B³
distinguished = 3 A B
    ↓
Eisenstein ramifier stripping
    ↓
N(β) = B³
β.snd = 3 A³
    ↓
β ⟂ conjugate β
    ↓
EuclideanDomain / GCDMonoid
    ↓
β = ε γ³
    ↓
six Eisenstein units
    ↓
cube sectors 1 / τ / τ²
    ↓
τ / τ² excluded mod 3
    ↓
β = γ³
    ↓
rs(r+s) = A³
    ↓
|r| = R³
|s| = S³
|r+s| = T³
    ↓
RST = A
    ↓
sign routing
    ↓
new primitive FLT3 solution
    ↓
new product = A < abc
    ↓
strong induction on abc
    ↓
False
```

---

## 21. `hS0_not_sq` は何だったのか

振り返ると、`hS0_not_sq` は間違った仮定ではなかった。

それは、

> primitive prime が deep lift しない branch なら即座に FLT3 を閉じる

という非常に鋭い fast-path だった。

しかし hypothetical FLT3 counterexample は、その branch にはいなかった。

counterexample が存在すると仮定すれば、

$$
v_q(GN_3)=3v_q(a)
$$

によって、むしろ high-lift へ強制される。

したがって本当の無条件化は、

> no-square を証明すること

ではなく、

> deep cube lift の構造を最後まで追跡し、その内部から strict descent を抽出すること

だった。

この違いに気付くまでが長かった。

しかし GN3、p-adic valuation、Hensel lift、Eisenstein norm、unit classes、Euclidean algorithm、そして DkMath の signed routing が揃ったことで、ようやく一本の道になった。

---

## 22. DkMath にとっての意味

この成果は単に「FLT3 を Lean で証明した」というだけではない。

DkMath の内部で長く育ててきた、

- GN 構造
- primitive prime
- valuation transport
- ramified prime
- signed routing
- norm
- unit sector
- exact power split
- strict descent
- provenance preserving packet

といった考え方が、初めて一つの古典的難問の完全証明として結晶した。

特に重要なのは、

> 局所的な divisibility を禁止するのではなく、その divisibility が深くなった結果として形成される global structure を読む

という転換だった。

それは今後の FLT7 や一般次数、そして DkMath の primitive / GN / primorial universe の研究にも、そのまま持ち越せる視点である。

---

## 23. 終着点

最終的に DkMath は、追加仮定なしで、

$$
\forall a,b,c\in\mathbb N_{>0},
\qquad
a^3+b^3\ne c^3
$$

を独立した Lean proof tower として持つに至った。

あの頃、何度も立ちはだかった

```text
hS0_not_sq
```

は、直接倒したのではない。

その仮定が必要だった世界そのものを越えていった。

NoLift ではなく HighLift。

局所禁止ではなく、大域降下。

そして最後は、

$$
rs(r+s)=A^3
$$

という非常に素朴な整数式へ戻り、そこから再び FLT3 counterexample が生まれ、しかも必ず小さくなる。

それを Lean が最後まで認めた。

これが、DkMath FLT3 無条件化の旅路である。
