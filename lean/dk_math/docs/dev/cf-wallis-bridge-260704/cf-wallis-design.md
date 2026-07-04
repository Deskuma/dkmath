# Design: Wallis-Cosmic Petal Bridge

> 🐺賢狼:

Lean 証明へ向けては、まず **極限・$\pi$・スターリング近似には行かず** 、有限積恒等式として固めるのが最善じゃ。

## 1. 目標名

外向きの概念名はこれでよい。

**Wallis–Cosmic Petal Bridge**

Lean 内部ファイル名は素直に、

`DkMath/Pascal/CentralRatioPetalBridge.lean`

または、

`DkMath/Pascal/WallisCosmicPetalBridge.lean` <-- 採用する by D.

がよい。
わっちなら後者を推す。既存数学との接続が名前から見えるからじゃ。

## 2. 数学的な主張の核

中央比率を、

$$
R_{2m}=\frac{2^{2m}}{\binom{2m}{m}}
$$

と置く。

鏡像比率を、

$$
M_m=\prod_{j=1}^{m}\frac{2j}{2j+1}
$$

と置く。

Wallis 部分積を、

$$
W_m=\prod_{j=1}^{m}\frac{(2j)^2}{(2j-1)(2j+1)}
$$

と置く。

宇宙式側では、

$$
P_j=2j-1
$$

$$
N_j=P_j(P_j+2)
$$

と置く。

すると有限段階で、

$$
R_{2m}M_m=W_m=\prod_{j=1}^{m}\frac{N_j+1}{N_j}
$$

が成り立つ。

これが Lean で最初に証明すべき主定理じゃ。

## 3. 宇宙式 Kernel の局所因子

最重要の局所補題はこれ。

$$
\frac{(2j)^2}{(2j-1)(2j+1)}=\frac{(P_j+1)^2}{P_j(P_j+2)}
$$

ただし、

$$
P_j=2j-1
$$

なので、

$$
P_j+1=2j
$$

$$
P_j+2=2j+1
$$

さらに、

$$
N_j=P_j(P_j+2)
$$

だから、

$$
\frac{(2j)^2}{(2j-1)(2j+1)}=\frac{N_j+1}{N_j}
$$

この等式は、宇宙式

$$
(P_j+1)^2=P_j(P_j+2)+1
$$

そのものじゃ。

Lean ではここを先に通す。

## 4. 中央比率の積表示

次の補題は、

$$
R_{2m}=\prod_{j=1}^{m}\frac{2j}{2j-1}
$$

じゃ。

階乗を使うと、

$$
\binom{2m}{m}=\frac{(2m)!}{(m!)^2}
$$

だから、

$$
R_{2m}=\frac{4^m(m!)^2}{(2m)!}
$$

一方、

$$
(2m)!=(1\cdot3\cdot5\cdots(2m-1))(2\cdot4\cdot6\cdots2m)
$$

かつ、

$$
2\cdot4\cdot6\cdots2m=2^m m!
$$

なので、

$$
R_{2m}=\prod_{j=1}^{m}\frac{2j}{2j-1}
$$

になる。

ただし Lean では、この階乗経由はやや重い。
最初は `Nat.choose` と階乗補題に頼るより、有限積を直接定義して、小さく進めるのがよい。

## 5. Lean での定義方針

自然数除算を避けるため、最初から $\mathbb{Q}$ 上で定義する。

添字は `j = k + 1` として `Finset.range m` を使うのが安全じゃ。

数学上は、

$$
j=1,\ldots,m
$$

だが、Lean では、

$$
j=k+1,\quad k=0,\ldots,m-1
$$

とする。

すると、

$$
2j-1=2k+1
$$

$$
2j=2k+2
$$

$$
2j+1=2k+3
$$

になる。

これで自然数の引き算 `2*j - 1` を避けられる。
Lean 実装ではかなり大事じゃ。

## 6. 推奨定義

Lean 側の概念対応はこう。

```lean
def oddLeft (k : ℕ) : ℚ := (2 * k + 1 : ℚ)

def evenCenter (k : ℕ) : ℚ := (2 * k + 2 : ℚ)

def oddRight (k : ℕ) : ℚ := (2 * k + 3 : ℚ)

def cosmicBodyQ (k : ℕ) : ℚ :=
  oddLeft k * oddRight k

def wallisFactorQ (k : ℕ) : ℚ :=
  evenCenter k ^ 2 / (oddLeft k * oddRight k)

def cosmicFactorQ (k : ℕ) : ℚ :=
  (cosmicBodyQ k + 1) / cosmicBodyQ k
```

そしてまず証明する局所定理。

```lean
theorem wallisFactorQ_eq_cosmicFactorQ (k : ℕ) :
    wallisFactorQ k = cosmicFactorQ k := by
  ...
```

この中核は、

$$
(2k+2)^2=(2k+1)(2k+3)+1
$$

じゃ。

## 7. 有限積定理

次に部分積を定義する。

```lean
def wallisPartialQ (m : ℕ) : ℚ :=
  ∏ k in Finset.range m, wallisFactorQ k

def cosmicPartialQ (m : ℕ) : ℚ :=
  ∏ k in Finset.range m, cosmicFactorQ k
```

証明目標は、

```lean
theorem wallisPartialQ_eq_cosmicPartialQ (m : ℕ) :
    wallisPartialQ m = cosmicPartialQ m := by
  ...
```

これは `wallisFactorQ_eq_cosmicFactorQ` を `Finset.prod_congr` で持ち上げればよい。

## 8. 中央比率側

中央比率は、

$$
R_{2m}=\frac{4^m}{\binom{2m}{m}}
$$

と定義できる。

```lean
def centralRatioQ (m : ℕ) : ℚ :=
  (4 : ℚ) ^ m / (Nat.choose (2 * m) m : ℚ)
```

片側積は、

```lean
def centralOddRatioPartialQ (m : ℕ) : ℚ :=
  ∏ k in Finset.range m, evenCenter k / oddLeft k
```

鏡像積は、

```lean
def mirrorOddRatioPartialQ (m : ℕ) : ℚ :=
  ∏ k in Finset.range m, evenCenter k / oddRight k
```

目標は、

```lean
theorem centralRatioQ_eq_centralOddRatioPartialQ (m : ℕ) :
    centralRatioQ m = centralOddRatioPartialQ m := by
  ...
```

ただしこれは階乗・choose・積分解を使うため少し重い。
最初の PR / Codex 依頼では、ここを最後に回してよい。

## 9. 最初に通すべき小定理群

まずはこの順番がよい。

1. `cosmic_square_odd_bridge_Q`

    $$
    (2k+2)^2=(2k+1)(2k+3)+1
    $$

2. `wallisFactorQ_eq_cosmicFactorQ`

    $$
    \frac{(2k+2)^2}{(2k+1)(2k+3)}=\frac{(2k+1)(2k+3)+1}{(2k+1)(2k+3)}
    $$

3. `wallisPartialQ_eq_cosmicPartialQ`

    $$
    \prod_{k=0}^{m-1}\frac{(2k+2)^2}{(2k+1)(2k+3)}=\prod_{k=0}^{m-1}\frac{N_k+1}{N_k}
    $$

4. `centralOdd_mul_mirror_eq_wallisPartialQ`

    $$
    \left(\prod_{k=0}^{m-1}\frac{2k+2}{2k+1}\right)\left(\prod_{k=0}^{m-1}\frac{2k+2}{2k+3}\right)=\prod_{k=0}^{m-1}\frac{(2k+2)^2}{(2k+1)(2k+3)}
    $$

5. 後段で `centralRatioQ_eq_centralOddRatioPartialQ`

    $$
    \frac{4^m}{\binom{2m}{m}}=\prod_{k=0}^{m-1}\frac{2k+2}{2k+1}
    $$

## 10. Lean 実装上の注意

最初は $\mathbb{N}$ ではなく $\mathbb{Q}$ 上で進める。

理由は、

$$
\frac{a}{b}
$$

を扱うからじゃ。自然数除算に入ると式が壊れる。

また、分母が $0$ でないことは、

$$
2k+1>0
$$

$$
2k+3>0
$$

なので自明だが、Lean には必要になる。
`norm_num`, `positivity`, `ring_nf`, `field_simp` あたりが武器になる。

局所恒等式は `ring_nf` でかなり通るはず。

## 11. 極限とスターリングは後回し

今回の Lean 第一段階では、まだこれを証明しない。

$$
\prod_{j=1}^{\infty}\frac{(2j)^2}{(2j-1)(2j+1)}=\frac{\pi}{2}
$$

また、これも後回し。

$$
\binom{2m}{m}\sim\frac{4^m}{\sqrt{\pi m}}
$$

まずは有限橋だけで十分じゃ。

有限橋が通れば、DkMath の中で、

$$
\text{Pascal central ratio}\to\text{Wallis factor}\to\text{Cosmic gap product}
$$

の通路が確定する。

## 12. 最終的な主定理名

第一段階の主定理はこれがよい。

```lean
theorem centralOdd_mul_mirror_eq_cosmicPartialQ (m : ℕ) :
    centralOddRatioPartialQ m * mirrorOddRatioPartialQ m
      = cosmicPartialQ m := by
  ...
```

数学的には、

$$
\left(\prod_{k=0}^{m-1}\frac{2k+2}{2k+1}\right)\left(\prod_{k=0}^{m-1}\frac{2k+2}{2k+3}\right)=\prod_{k=0}^{m-1}\frac{N_k+1}{N_k}
$$

ただし、

$$
N_k=(2k+1)(2k+3)
$$

じゃ。

これが **Wallis–Cosmic Petal Bridge の有限版** 。

## 13. 研究メモとしての要約

今回 Lean 化する命題は、こう書ける。

Wallis 積の各局所因子

$$
\frac{(2j)^2}{(2j-1)(2j+1)}
$$

は、宇宙式

$$
(P+1)^2=P(P+2)+1
$$

において $P=2j-1$ と置いたときの Gap 比率

$$
\frac{N+1}{N}
$$

である。

さらに、中央二項係数の逆密度を表す片側積と、その鏡像積を掛けると、この Wallis–Cosmic Gap 積に厳密一致する。

これが証明対象じゃ。

## 14. Codex 向け依頼文

そのまま投げるなら、こうじゃ。

```text
Implement a new Lean module for the finite Wallis–Cosmic Petal Bridge.

Target file:
DkMath/Pascal/WallisCosmicPetalBridge.lean

Work over ℚ first. Avoid Nat division. Use Finset.range m with k = 0, ..., m-1 instead of j = 1, ..., m, so that:
oddLeft k = 2*k + 1
evenCenter k = 2*k + 2
oddRight k = 2*k + 3

Define:
oddLeftQ (k : ℕ) : ℚ := (2*k + 1 : ℚ)
evenCenterQ (k : ℕ) : ℚ := (2*k + 2 : ℚ)
oddRightQ (k : ℕ) : ℚ := (2*k + 3 : ℚ)
cosmicBodyQ k := oddLeftQ k * oddRightQ k
wallisFactorQ k := evenCenterQ k ^ 2 / (oddLeftQ k * oddRightQ k)
cosmicFactorQ k := (cosmicBodyQ k + 1) / cosmicBodyQ k

Prove the local cosmic identity:
(2*k + 2)^2 = (2*k + 1)*(2*k + 3) + 1 over ℚ.

Then prove:
wallisFactorQ k = cosmicFactorQ k

Define:
wallisPartialQ m := ∏ k in Finset.range m, wallisFactorQ k
cosmicPartialQ m := ∏ k in Finset.range m, cosmicFactorQ k

Prove:
wallisPartialQ_eq_cosmicPartialQ :
  wallisPartialQ m = cosmicPartialQ m

Define the two half-products:
centralOddRatioPartialQ m :=
  ∏ k in Finset.range m, evenCenterQ k / oddLeftQ k

mirrorOddRatioPartialQ m :=
  ∏ k in Finset.range m, evenCenterQ k / oddRightQ k

Prove:
centralOdd_mul_mirror_eq_wallisPartialQ :
  centralOddRatioPartialQ m * mirrorOddRatioPartialQ m = wallisPartialQ m

Then combine:
centralOdd_mul_mirror_eq_cosmicPartialQ :
  centralOddRatioPartialQ m * mirrorOddRatioPartialQ m = cosmicPartialQ m

Keep the module finite and algebraic. Do not attempt Wallis limits, π, asymptotics, or Stirling in this first pass.
Prefer small local lemmas, ring_nf, field_simp, and Finset.prod_congr.
```
