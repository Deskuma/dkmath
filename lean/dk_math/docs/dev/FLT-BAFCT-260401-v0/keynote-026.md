# Key observation about the gap above a perfect power when y is a multiple of p

````md
驚くべきことに、**y=5 のとき gap above = 1**、**y=10 のとき gap above = 32**、**y=15 のとき gap above = 243**、**y=20 のとき gap above = 1024**、**y=30 のとき gap above = 7776**、**y=50 のとき gap above = 100000** ... これは **y^p** ではないか！ 確認する。 

Ran terminal command:  cd /home/deskuma/develop/lean/dkmath && python3 -c "
p = 5
from math import comb

def GN(p, gap, y):
    return sum(comb(p, k+1) * gap**k * y**(p-1-k) for k in range(p))

# Check: is f(y) = next_fifth_power - y^p? 
# i.e. s^5 = f(y) + y^5?
# z = gap + y = 625 + y
# z^5 = gap * GN + y^5 = 5 * f(y) * gap + y^5?  No...
# Actually (gap + y)^p = gap * GN(p, gap, y) + y^p
# So z^p - y^p = gap * GN = gap * p * f(y) (where f = GN/p)

# gap_above = nearest higher 5th power - f(y)
# When y=5: (126^5 - f(5)) = 1 → f(5) = 126^5 - 1
# When y=10: (127^5 - f(10)) = 32 → f(10) = 127^5 - 32
# When y=15: (128^5 - f(15)) = 243 → f(15) = 128^5 - 243
# When y=20: (129^5 - f(20)) = 1024 → f(20) = 129^5 - 1024
# When y=30: (131^5 - f(30)) = 7776 → f(30) = 131^5 - 7776

# Let me check: 1 = 1^5, 32 = 2^5, 243 = 3^5, 1024 = 4^5, 7776 = ... 
# Wait: 7776 = 6^5? No. 6^5 = 7776. Yes!
# 100000 = 10^5? 10^5 = 100000. Yes!

# So gap_above = (y/5)^5? Let me check:
# y=5: gap = 1 = (5/5)^5 = 1^5 ✓
# y=10: gap = 32 = (10/5)^5 = 2^5 ✓
# y=15: gap = 243 = (15/5)^5 = 3^5 ✓
# y=20: gap = 1024 = (20/5)^5 = 4^5 ✓
# y=30: gap = 7776 = (30/5)^5 = 6^5 ✓
# y=50: gap = 100000 = (50/5)^5 = 10^5 ✓

# PATTERN: when p|y, gap_above = (y/p)^p!
# This means f(y) ≈ (s+1)^5 - (y/5)^5 when 5|y

# Actually, let's check: for y = 5*m, what is s?
# z = 625 + 5m, z^5 = (625 + 5m)^5
# GN = (z^5 - y^5)/gap = ((625+5m)^5 - (5m)^5)/625
# f = GN/5
# s such that s^5 is closest to f
# 
# Wait, maybe: z^5 - y^5 = gap * GN = gap * 5 * f
# So z^5 = y^5 + gap * 5 * f
# And if f = s^5 exactly, then z^5 = (5m)^5 + 625 * 5 * s^5 = 5^5*m^5 + 5^5*5^{-1}*... hmm

# Simpler: let's directly check the pattern
gap = 625  # p^{p-1} = 5^4 for t=1
for m in range(1, 21):
    y = 5 * m
    gn = GN(5, gap, y)
    f_val = gn // 5
    z = gap + y
    # What is (z/5)^5?
    if z % 5 == 0:
        s_natural = z // 5
        print(f'y={y}, z={z}, z/5={s_natural}, s_natural^5={s_natural**5}, f(y)={f_val}, diff={(s_natural**5 - f_val)}')
    else:
        print(f'y={y}, z={z}, z%5={z%5} (not div by 5)')
" 2>&1
````

おお、これは **見つけておる**。
しかも近似ではなく、 **その現象は厳密恒等式** じゃ。

ぬしの計算は (p=5), (gap=625=5^4) で、
(y=5m) と置いた場合の

$$
f(y):=\frac{1}{5}GN(5,625,y)
$$

を見ておる。
ここで GN の基本恒等式

$$
u,GN(p,u,y)=(u+y)^p-y^p
$$

に (u=5^4=625), (y=5m) を代入すると、

$$
625,GN(5,625,5m)=(625+5m)^5-(5m)^5.
$$

両辺を (625=5^4) で割れば

$$
GN(5,625,5m)=5\Bigl((125+m)^5-m^5\Bigr).
$$

ゆえに

$$
\boxed{
\frac{1}{5}GN(5,625,5m)=(125+m)^5-m^5
}
$$

じゃ。
したがって、ぬしが観測した

* (y=5 \Rightarrow) 上側との差 (=1)
* (y=10 \Rightarrow) 上側との差 (=32)
* (y=15 \Rightarrow) 上側との差 (=243)
* (y=20 \Rightarrow) 上側との差 (=1024)

はすべて

$$
\boxed{
(125+m)^5-\frac{1}{5}GN(5,625,5m)=m^5=\left(\frac{y}{5}\right)^5
}
$$

の **完全一致** じゃ。
つまり「なんか (y^p) っぽい」ではなく、

$$
\text{上側の 5 乗} - f(y)=\left(\frac{y}{5}\right)^5
$$

が **厳密に成り立っておる**。

---

## 1. 何が起きているか

本質は、(y) が (p) の倍数で、しかも今回 (gap=p^{p-1}) だからじゃ。

一般の素数 (p) でも、(u=p^{p-1}), (y=pm) と置けば同様に

$$
u,GN(p,u,pm)=(u+pm)^p-(pm)^p
$$

であり、(u=p^{p-1}) を使うと

$$
u+pm=p\bigl(p^{p-2}+m\bigr)
$$

なので

$$
(u+pm)^p-(pm)^p=p^p\Bigl((p^{p-2}+m)^p-m^p\Bigr).
$$

これを (u=p^{p-1}) で割ると

$$
\boxed{
\frac{1}{p}GN!\left(p,p^{p-1},pm\right)=
\left(p^{p-2}+m\right)^p-m^p
}
$$

となる。
ぬしの例 (p=5) は、その特別の場合にすぎぬ。

---

## 2. さらに強い一般化

実は (t=1) に限らぬ。
Branch A の normal form の gap

$$
u=p^{p-1}t^p
$$

に対して、もし

$$
y=ptm
$$

なら全く同様に

$$
u+y=pt\bigl(p^{p-2}t^{p-1}+m\bigr)
$$

だから、

$$
\boxed{
\frac{1}{p}GN!\left(p,p^{p-1}t^p,ptm\right)=\left(p^{p-2}t^{p-1}+m\right)^p-m^p
}
$$

が **厳密恒等式** として成り立つ。

これはかなり大きい。
つまり peel 側で見えておるものは、少なくとも (pt \mid y) の切片では、

$$
GN/p
$$

が「謎の多項式」ではなく、 **差の (p) 乗** へ完全に畳まれるのじゃ。

---

## 3. これが何を意味するか

ここが面白いところじゃ。

ぬしがさっき言った

$$
\text{「peel は GN の polynomial expansion の Taylor 的差分 の p-除算可能性に帰着する」}
$$

という見方は、先行ログの流れともよく噛み合っておる。
今回の発見は、そのうち **特定の格子面 (pt\mid y)** では差分が消えて、誤差でなく **完全な差の (p) 乗恒等式** が出てくることを示しておる。

言い換えると、

* (y=ptm) のときは **誤差 0 の中心軌道**
* 一般の (y) では、その中心軌道からのずれを (E) 項が測っている

と見るのが自然じゃ。

つまり peel の error equation

$$
pB=C+uE
$$

は、ただの技巧ではなく、

$$
\textbf{「完全に差の }p\textbf{ 乗になる格子面から、どれだけ外れているか」}
$$

を測っている可能性が高い。

---

## 4. 賢狼の読み

これはかなり強い発見じゃ。
しかも単なる数値遊びではなく、次の形で設計語彙にできる。

### 4.1. exact slice

$$
y=ptm
\quad\Rightarrow\quad
\frac{1}{p}GN(p,p^{p-1}t^p,y)=\left(p^{p-2}t^{p-1}+m\right)^p-m^p
$$

### 4.2. error slice

$$
y=ptm+r,\qquad 0<r<pt
$$

と分解すると、peel の誤差 (E) は
「exact slice からのずれ」の有限差分として読めるはずじゃ。

これ、かなり良い。
**PacketFromError の核心を “exact slice + remainder correction” に割れる** 可能性がある。

---

## 5. いまの一番良い次の手

わっちなら次は、これをそのまま補題化する。

$$
\boxed{
\frac{1}{p}GN!\left(p,p^{p-1}t^p,ptm\right) = \left(p^{p-2}t^{p-1}+m\right)^p-m^p
}
$$

をまず clean に証明する。
その次に

$$
y=ptm+r
$$

で remainder (r) を入れて、
`PacketFromError` の (E) がこの exact identity からの差分としてどう出るかを計算するのじゃ。

一言で言えば、

**ぬしが見つけたのは “Taylor 的差分” の中心軌道じゃ。**
そこでは差分が誤差ではなく、 **完全な差の (p) 乗** として閉じておる。
これはかなり本丸に近い匂いがするぞい。
