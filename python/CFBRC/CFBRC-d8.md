# CFBRC の $d=8$ を完全分解してみる

> 🐺賢狼:

よし、その $d=8$ を **きっちり解体** して見せようぞ。
ここは CFBRC の「項観測」を、**円分多項式の因子観測** に持ち上げる見取り図そのものじゃ。

まず確認すると、`CosmicComplex.py` の既定は $G(\theta)=(x+i\theta)^d$ で、`dyadic` モード $d=2^n$ を運用推奨としておる。一方で実装コメントには「ここを差し替えるだけで $(x+i\theta)^d-(i\theta)^d$ などにもできる」と明記されておる。README でも基本思想・位相・支配項・位相微分の観測が主眼とされておる。ゆえに、いまからやる $(x+i\theta)^8-(i\theta)^8$ の分解は、CFBRC の観測量を **差冪の円分構造** に接続する自然な拡張じゃ。 ([GitHub][1])

---

## 1. 差冪を $a^8-b^8$ として置く

$$
a := x+i\theta,\qquad b := i\theta
$$

と置けば、

$$
G_8(\theta):=(x+i\theta)^8-(i\theta)^8 = a^8-b^8
$$

じゃ。

差冪の一般公式

$$
a^n-b^n=\prod_{m\mid n} b^{\varphi(m)}\Phi_m!\left(\frac{a}{b}\right)
$$

を $n=8$ に入れると、約数は $1,2,4,8$ なので

$$
a^8-b^8=(a-b)(a+b)(a^2+b^2)(a^4+b^4)
$$

となる。これはまさに

$$
\Phi_1(z)=z-1,\quad
\Phi_2(z)=z+1,\quad
\Phi_4(z)=z^2+1,\quad
\Phi_8(z)=z^4+1
$$

に対応しておる。

つまり **$d=8$ の dyadic 構造は、4枚の円分位相層に割れる** のじゃ。
ここ、実にうまい。2冪は噛み心地がよいのぅ。

---

## 2. 各因子を $x,\theta$ で露わにする

### 2.1. 第1因子 $\Phi_1$ 層

$$
F_1 := a-b = (x+i\theta)-i\theta = x
$$

これは完全に実定数じゃ。

---

### 2.2. 第2因子 $\Phi_2$ 層

$$
F_2 := a+b = (x+i\theta)+i\theta = x+2i\theta
$$

---

### 2.3. 第3因子 $\Phi_4$ 層

$$
F_4 := a^2+b^2
$$

まず

$$
a^2=(x+i\theta)^2=x^2+2ix\theta-\theta^2
$$

$$
b^2=(i\theta)^2=-\theta^2
$$

だから

$$
F_4=x^2-2\theta^2+2ix\theta
$$

---

### 2.4. 第4因子 $\Phi_8$ 層

$$
F_8 := a^4+b^4
$$

$$
(x+i\theta)^4=x^4+4ix^3\theta-6x^2\theta^2-4ix\theta^3+\theta^4
$$

$$
(i\theta)^4=\theta^4
$$

ゆえに

$$
F_8=x^4-6x^2\theta^2+2\theta^4+
4ix\theta(x^2-\theta^2)
$$

---

## 3. 完全分解の最終形

したがって

$$
\boxed{
G_8(\theta)=x,
(x+2i\theta),
\bigl(x^2-2\theta^2+2ix\theta\bigr),
\Bigl(x^4-6x^2\theta^2+2\theta^4+4ix\theta(x^2-\theta^2)\Bigr)
}
$$

じゃ。

これが **CFBRC の $d=8$ 差冪版の円分分解** じゃよ。

見た目が少々ごついが、構造はきれいそのものじゃ。
$x$ で始まり、線形、2次、4次の位相層へ順々に増殖しておる。
まるで位相の重ね酒じゃな。飲み過ぎると翌朝きついが、数式は美しい。

---

## 4. 位相速度 $\omega(\theta)=\dfrac{d}{d\theta}\arg G_8(\theta)$ の分解

積の偏角は和じゃから、

$$
\arg G_8=\arg F_1+\arg F_2+\arg F_4+\arg F_8
$$

ゆえに

$$
\omega_8(\theta)=
\frac{d}{d\theta}\arg G_8(\theta)
\omega_{1}+\omega_{2}+\omega_{4}+\omega_{8}
$$

となる。

一般に $F(\theta)=u(\theta)+iv(\theta)$ に対して

$$
\frac{d}{d\theta}\arg F(\theta)=
\frac{u v' - v u'}{u^2+v^2}=
\operatorname{Im}\left(\frac{F'(\theta)}{F(\theta)}\right)
$$

じゃ。

---

## 5. 各因子ごとの位相速度

### 5.1. $F_1=x$

$$
\omega_1(\theta)=0
$$

当然じゃ。定数は回らぬ。

---

### 5.2. $F_2=x+2i\theta$

$$
u=x,\qquad v=2\theta
$$

なので

$$
\omega_2(\theta)=
\frac{2x}{x^2+4\theta^2}
$$

これは **一番素直なローレンツ型** の減衰じゃな。

---

### 5.3. $F_4=x^2-2\theta^2+2ix\theta$

$$
u=x^2-2\theta^2,\qquad v=2x\theta
$$

$$
u'=-4\theta,\qquad v'=2x
$$

だから

$$
\omega_4(\theta)=\frac{(x^2-2\theta^2)(2x)-(2x\theta)(-4\theta)}{(x^2-2\theta^2)^2+(2x\theta)^2}
$$

整理すると

$$
\boxed{
\omega_4(\theta)=\frac{2x(x^2+2\theta^2)}{x^4+4\theta^4}
}
$$

となる。
分母の $x^4+4\theta^4$ への簡約が、なかなか気持ちよいのぅ。

---

### 5.4. $F_8=x^4-6x^2\theta^2+2\theta^4+4ix\theta(x^2-\theta^2)$

$$
u=x^4-6x^2\theta^2+2\theta^4,\qquad v=4x\theta(x^2-\theta^2)
$$

これを同様に計算すると

$$
\boxed{
\omega_8(\theta)=
\frac{4x\bigl(x^6+3x^4\theta^2+2\theta^6\bigr)}
{x^8+4x^6\theta^2+8x^4\theta^4-8x^2\theta^6+4\theta^8}
}
$$

となる。

---

## 6. 総位相速度の完全分解

よって、CFBRC 差冪版 $d=8$ の位相速度は

$$
\boxed{
\omega_8(\theta)=
\frac{2x}{x^2+4\theta^2}+
\frac{2x(x^2+2\theta^2)}{x^4+4\theta^4}+
\frac{4x\bigl(x^6+3x^4\theta^2+2\theta^6\bigr)}
{x^8+4x^6\theta^2+8x^4\theta^4-8x^2\theta^6+4\theta^8}
}
$$

じゃ。
$F_1$ の寄与は 0 なので消えておる。

これが **factor-wise phase derivative** の明示式じゃよ。

---

## 7. ここから何が読めるか

### 7.1. 位相速度は「層の和」

CFBRC で見ている位相速度は、単なる1本の謎曲線ではない。

$$
\omega_8=\omega_2+\omega_4+\omega_8
$$

つまり **$\Phi_2,\Phi_4,\Phi_8$ の三層位相の合成運動** じゃ。

これは前に話した「項支配」とは別の基底じゃ。

- 二項展開側では **項 $ T_k $ の支配**
- 円分分解側では **因子 $ F_{2^j} $ の位相支配**

を見る。

この2つを重ねると、
「どの項が大きいか」と「どの因子が回転を決めているか」が、必ずしも一致せぬことが分かる。
ここに解析の旨味がある。うむ、噛むほど味が出るやつじゃ。

---

### 7.2. $x > 0$ なら各寄与は正

$x > 0$ とすると、上の3項はどれも分子が正、分母も正じゃ。したがって

$$
\omega_8(\theta) > 0
$$

となる区間が広い。
つまり **unwrap 後の偏角は、零点や枝切りの悪さがなければ、かなり単調に増えやすい**。

これは CFBRC の「勝手に位相が生まれる」という観測と、かなりきれいに整合する。README の説明どおり、CC は位相や位相速度を主要観測量としており、演算前後の Motion まで追う設計になっておる。 ([GitHub][1])

---

### 7.3. 実軸交差の意味が変わる

$\operatorname{Im} G_8(\theta)=0$ は、ただの「虚部ゼロ」ではない。

$$
\arg F_2+\arg F_4+\arg F_8 \equiv 0 \pmod{\pi}
$$

という **円分位相層の整列条件** になる。
つまり crossing は、**位相の偶然の打消し** ではなく、**層ごとの位相ロック点** と見なせるのじゃ。

ぬしの言葉で言えば、これは **phase-lock の素因数分解版** じゃな。

---

## 8. CFBRC 的に次へ進むなら

この分解をそのままコードへ落とすなら、観測量を二系統にすればよい。

### A. 項基底観測

いまの `CosmicComplex` 流儀

$$
T_k(\theta)=\binom{8}{k}x^{8-k}(i\theta)^k
$$

の支配項、寄与率、部分和多角形を見る。

### B. 因子基底観測

新たに

$$
F_1=x,\quad
F_2=x+2i\theta,\quad
F_4=x^2-2\theta^2+2ix\theta,\quad
F_8=\cdots
$$

を記録して

- $|F_j|$
- $\arg F_j$
- $\omega_j = \dfrac{d}{d\theta}\arg F_j$
- 部分積
  $$
  P_1=F_1,\quad P_2=F_1F_2,\quad P_4=F_1F_2F_4,\quad P_8=F_1F_2F_4F_8
  $$

を可視化する。

この **部分和 polygon** に対する **部分積 spiral** は、かなり面白いはずじゃ。

---

## 9. ひとことで言うと

$d=8$ の CFBRC 差冪版は

$$
(x+i\theta)^8-(i\theta)^8 =
\Phi_1\Phi_2\Phi_4\Phi_8
$$

の層構造を持ち、位相速度は

$$
\omega_8=\omega_2+\omega_4+\omega_8
$$

と **円分層ごとに完全分解** できる。
つまり CFBRC の偏角運動は、**差冪の円分分解がつくる階層的な回転場** と読めるのじゃ。

これはかなり強い。
ただの見た目の一致ではない。**骨格が一致しておる**。

[1]: https://github.com/Deskuma/dkmath/tree/snapshot/nightly-260310-v0/python/CFBRC "dkmath/python/CFBRC at snapshot/nightly-260310-v0 · Deskuma/dkmath · GitHub"

---

次は、この式をそのまま Python 実装できる形で
**`cyclotomic_observe_d8(theta, x)` の設計** と
**`dominant_factor`, `factor_entropy`, `partial_products`** を追加した設計案まで書けるぞ。

> 👩‍⚕️私D.:

Python 実装へ

> 🐺賢狼:

よし、では **CFBRC にそのまま差し込める形** で書くぞ。
今回はまず **$d=8$ 専用** にして、ついでに **factor-wise 観測** を綺麗に出せる実装にする。
狙いはこうじゃ。

$$
G_8(\theta)=
(x+i\theta)^8-(i\theta)^8=
F_1 F_2 F_4 F_8
$$

ただし

$$
F_1=x
$$

$$
F_2=x+2i\theta
$$

$$
F_4=x^2-2\theta^2+2ix\theta
$$

$$
F_8=x^4-6x^2\theta^2+2\theta^4+4ix\theta(x^2-\theta^2)
$$

で、位相速度は

$$
\omega(\theta)=\frac{d}{d\theta}\arg G_8(\theta)
=\omega_1+\omega_2+\omega_4+\omega_8
$$

じゃ。

以下、そのまま `python/CFBRC/cyclotomic_d8.py` みたいな名前で置ける実装じゃよ。

```python
from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, List, Tuple
import cmath
import math

@dataclass
class FactorObservation:
    name: str
    value: complex
    abs: float
    arg: float
    phase_derivative: float

@dataclass
class CyclotomicObservationD8:
    x: float
    theta: float
    G: complex
    absG: float
    argG: float
    phase_derivative_total: float

    factors: List[FactorObservation]
    factor_weights_abs: Dict[str, float]
    factor_weights_phase: Dict[str, float]
    dominant_factor_abs: str
    dominant_factor_phase: str
    factor_entropy_abs: float
    factor_entropy_phase: float

    partial_products: List[Tuple[str, complex]]
    real_axis_lock: bool

def _safe_arg(z: complex) -> float:
    return math.atan2(z.imag, z.real)

def _entropy_from_weights(weights: List[float], eps: float = 1e-15) -> float:
    s = 0.0
    for w in weights:
        if w > eps:
            s -= w * math.log(w)
    return s

def factor_F1(x: float, theta: float) -> complex:
    # F1 = a - b = x
    return complex(x, 0.0)

def factor_F2(x: float, theta: float) -> complex:
    # F2 = a + b = x + 2 i theta
    return complex(x, 2.0 * theta)

def factor_F4(x: float, theta: float) -> complex:
    # F4 = a^2 + b^2 = x^2 - 2 theta^2 + 2 i x theta
    return complex(x * x - 2.0 * theta * theta, 2.0 * x * theta)

def factor_F8(x: float, theta: float) -> complex:
    # F8 = a^4 + b^4
    re = x**4 - 6.0 * x * x * theta * theta + 2.0 * theta**4
    im = 4.0 * x * theta * (x * x - theta * theta)
    return complex(re, im)

def phase_derivative_F1(x: float, theta: float) -> float:
    # arg(x) is constant (for x > 0, strictly 0)
    return 0.0

def phase_derivative_F2(x: float, theta: float) -> float:
    # 2x / (x^2 + 4 theta^2)
    den = x * x + 4.0 * theta * theta
    if den == 0.0:
        return math.inf
    return 2.0 * x / den

def phase_derivative_F4(x: float, theta: float) -> float:
    # 2x(x^2 + 2 theta^2) / (x^4 + 4 theta^4)
    den = x**4 + 4.0 * theta**4
    if den == 0.0:
        return math.inf
    num = 2.0 * x * (x * x + 2.0 * theta * theta)
    return num / den

def phase_derivative_F8(x: float, theta: float) -> float:
    # 4x(x^6 + 3x^4 theta^2 + 2 theta^6)
    # ------------------------------------
    # x^8 + 4x^6 theta^2 + 8x^4 theta^4 - 8x^2 theta^6 + 4 theta^8
    den = (
        x**8
        + 4.0 * x**6 * theta**2
        + 8.0 * x**4 * theta**4
        - 8.0 * x**2 * theta**6
        + 4.0 * theta**8
    )
    if den == 0.0:
        return math.inf
    num = 4.0 * x * (x**6 + 3.0 * x**4 * theta**2 + 2.0 * theta**6)
    return num / den

def G_d8_from_difference(x: float, theta: float) -> complex:
    a = complex(x, theta)
    b = complex(0.0, theta)
    return a**8 - b**8

def G_d8_from_factors(x: float, theta: float) -> complex:
    return factor_F1(x, theta) * factor_F2(x, theta) * factor_F4(x, theta) * factor_F8(x, theta)

def observe_cyclotomic_d8(
    x: float,
    theta: float,
    *,
    real_axis_tol: float = 1e-9,
) -> CyclotomicObservationD8:
    f1 = factor_F1(x, theta)
    f2 = factor_F2(x, theta)
    f4 = factor_F4(x, theta)
    f8 = factor_F8(x, theta)

    w1 = phase_derivative_F1(x, theta)
    w2 = phase_derivative_F2(x, theta)
    w4 = phase_derivative_F4(x, theta)
    w8 = phase_derivative_F8(x, theta)

    factors = [
        FactorObservation("F1", f1, abs(f1), _safe_arg(f1), w1),
        FactorObservation("F2", f2, abs(f2), _safe_arg(f2), w2),
        FactorObservation("F4", f4, abs(f4), _safe_arg(f4), w4),
        FactorObservation("F8", f8, abs(f8), _safe_arg(f8), w8),
    ]

    partial_products: List[Tuple[str, complex]] = []
    prod = complex(1.0, 0.0)
    for f in factors:
        prod *= f.value
        partial_products.append((f.name, prod))

    G = prod
    absG = abs(G)
    argG = _safe_arg(G)
    phase_derivative_total = w1 + w2 + w4 + w8

    abs_sum = sum(f.abs for f in factors)
    if abs_sum == 0.0:
        factor_weights_abs = {f.name: 0.0 for f in factors}
    else:
        factor_weights_abs = {f.name: f.abs / abs_sum for f in factors}

    phase_mags = [abs(f.phase_derivative) for f in factors]
    phase_sum = sum(phase_mags)
    if phase_sum == 0.0:
        factor_weights_phase = {f.name: 0.0 for f in factors}
    else:
        factor_weights_phase = {
            f.name: abs(f.phase_derivative) / phase_sum
            for f in factors
        }

    dominant_factor_abs = max(factor_weights_abs, key=factor_weights_abs.get)
    dominant_factor_phase = max(factor_weights_phase, key=factor_weights_phase.get)

    factor_entropy_abs = _entropy_from_weights(list(factor_weights_abs.values()))
    factor_entropy_phase = _entropy_from_weights(list(factor_weights_phase.values()))

    real_axis_lock = abs(G.imag) < real_axis_tol

    return CyclotomicObservationD8(
        x=x,
        theta=theta,
        G=G,
        absG=absG,
        argG=argG,
        phase_derivative_total=phase_derivative_total,
        factors=factors,
        factor_weights_abs=factor_weights_abs,
        factor_weights_phase=factor_weights_phase,
        dominant_factor_abs=dominant_factor_abs,
        dominant_factor_phase=dominant_factor_phase,
        factor_entropy_abs=factor_entropy_abs,
        factor_entropy_phase=factor_entropy_phase,
        partial_products=partial_products,
        real_axis_lock=real_axis_lock,
    )

def scan_thetas_d8(
    x: float,
    thetas: List[float],
    *,
    real_axis_tol: float = 1e-9,
) -> List[CyclotomicObservationD8]:
    return [
        observe_cyclotomic_d8(x, th, real_axis_tol=real_axis_tol)
        for th in thetas
    ]

def pretty_print_observation(obs: CyclotomicObservationD8) -> None:
    print(f"x = {obs.x}")
    print(f"theta = {obs.theta}")
    print(f"G = {obs.G}")
    print(f"|G| = {obs.absG}")
    print(f"arg(G) = {obs.argG}")
    print(f"d/dtheta arg(G) = {obs.phase_derivative_total}")
    print(f"real_axis_lock = {obs.real_axis_lock}")
    print()

    print("Factors:")
    for f in obs.factors:
        print(
            f"  {f.name:>2} : "
            f"value={f.value!r}, |.|={f.abs:.12g}, "
            f"arg={f.arg:.12g}, darg={f.phase_derivative:.12g}"
        )

    print()
    print("Weights by |F|:")
    for k, v in obs.factor_weights_abs.items():
        print(f"  {k}: {v:.12g}")

    print()
    print("Weights by |darg|:")
    for k, v in obs.factor_weights_phase.items():
        print(f"  {k}: {v:.12g}")

    print()
    print(f"dominant_factor_abs   = {obs.dominant_factor_abs}")
    print(f"dominant_factor_phase = {obs.dominant_factor_phase}")
    print(f"factor_entropy_abs    = {obs.factor_entropy_abs:.12g}")
    print(f"factor_entropy_phase  = {obs.factor_entropy_phase:.12g}")

    print()
    print("Partial products:")
    for name, z in obs.partial_products:
        print(f"  up to {name}: {z!r}")

if __name__ == "__main__":
    x = 1.0
    theta = 0.7

    obs = observe_cyclotomic_d8(x, theta)
    pretty_print_observation(obs)

    # 因子積と直接差冪が一致するかの確認
    g_fact = G_d8_from_factors(x, theta)
    g_diff = G_d8_from_difference(x, theta)
    print()
    print("consistency check:")
    print("  G_from_factors   =", g_fact)
    print("  G_from_difference=", g_diff)
    print("  error            =", abs(g_fact - g_diff))
```

---

## 1. 実装の肝

この実装で新たに入った観測は 4 本柱じゃ。

### A. `factors`

各円分層

$$
F_1,\;F_2,\;F_4,\;F_8
$$

ごとの

- 値
- 絶対値
- 偏角
- 偏角速度

を持つ。

### B. `factor_weights_abs`

これは

$$
\frac{|F_j|}{\sum_k |F_k|}
$$

で、**どの因子が大きさを支配しているか** を見る。

### C. `factor_weights_phase`

これは

$$
\frac{|\omega_j|}{\sum_k |\omega_k|}
$$

で、**どの因子が位相速度を支配しているか** を見る。

### D. `partial_products`

これは

$$
P_1=F_1,\quad
P_2=F_1F_2,\quad
P_4=F_1F_2F_4,\quad
P_8=F_1F_2F_4F_8
$$

で、**部分和 polygon** に対する **部分積 spiral** の元になる。

ここが CFBRC の次の美味しい酒の肴じゃ。

---

## 2. 既存 CFBRC へ合わせるなら

ぬしの既存系に寄せるなら、たとえば `CosmicComplex.observe(...)` と並列に

```python
obs = observe_cyclotomic_d8(x=1.0, theta=theta)
```

を呼び、比較するとよい。

見比べる対象はこれじゃ。

- 既存:
  - `dominant_k`
  - `contrib`
  - `entropy`
  - `partial_sums`
  - `arg`

- 新規:
  - `dominant_factor_abs`
  - `dominant_factor_phase`
  - `factor_entropy_abs`
  - `factor_entropy_phase`
  - `partial_products`
  - factor-wise `arg`, `phase_derivative`

つまり

**項支配** と **因子支配** の二重観測になる。

これはかなり強いぞ。
項では目立たぬのに位相を強く曲げる因子、逆に値は大きいが回転にはあまり寄与せぬ因子、そういうものが炙り出せる。

---

## 3. ついでに簡易プロット用の補助も置いておく

もし軽く走査したいなら、この補助を足すとよい。

```python
def table_phase_scan(x: float, theta_start: float, theta_end: float, n: int = 21) -> None:
    for i in range(n):
        th = theta_start + (theta_end - theta_start) * i / (n - 1)
        obs = observe_cyclotomic_d8(x, th)
        print(
            f"theta={th: .6f}  "
            f"argG={obs.argG: .6f}  "
            f"darg={obs.phase_derivative_total: .6f}  "
            f"domAbs={obs.dominant_factor_abs:>2}  "
            f"domPhase={obs.dominant_factor_phase:>2}  "
            f"lock={obs.real_axis_lock}"
        )
```

これで
「どの $\theta$ で dominant factor が切り替わるか」
がざっくり見える。

---

## 4. 次の拡張先

この先は二手ある。

### 1. 一般 dyadic 化

$d=8$ 固定ではなく

$$
d=2^m
$$

について

$$
a^{2^m}-b^{2^m}=
(a-b)(a+b)(a^2+b^2)\cdots(a^{2^{m-1}}+b^{2^{m-1}})
$$

を自動生成する版を書く。

### 2. CFBRC 本体へ統合

`cfbrc.py` の観測オブジェクトに

- `factor_observation`
- `dominant_factor`
- `factor_entropy`
- `partial_products`

を直接足す。

個人的には、まずは **$d=8$ 固定の単独モジュールで正しさ確認** をしてから、本体へ移植するのが堅い。いきなり巨大化すると獣道が泥沼になるからのぅ。

---

## 5. まずやるべき確認

実行したら最後にこの一致を見ておくとよい。

$$
F_1F_2F_4F_8=(x+i\theta)^8-(i\theta)^8
$$

コード中の

```python
g_fact = G_d8_from_factors(x, theta)
g_diff = G_d8_from_difference(x, theta)
print(abs(g_fact - g_diff))
```

が十分小さければ、因子分解実装は通っておる。

---

次はこれをもう一歩進めて、**既存 `cfbrc.py` 風の API に合わせた差分パッチ形式** で書くのが良い。
つまり「どの関数の下に何を足すか」まで repo 目線で切り分けるやつじゃ。
