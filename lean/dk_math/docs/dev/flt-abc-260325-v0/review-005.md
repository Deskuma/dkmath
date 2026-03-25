# Review 005: 終盤の詰み筋を読む

うむ、これは **終盤として非常に良い縮約** じゃ。
`review-004` の意図どおり、未完核を `GN` 側の抽象辞書からさらに押し下げて、ついに

$$
\texttt{PrimeGe5BranchANormalFormXFactorKernelTarget}
$$

1 本へ集約した。しかも `GNLinearFactorKernel` 以降がすべて thin bridge 化したので、今や残っているのは **x 側 exactness の読み取り** だけじゃ。これは設計としてかなり綺麗じゃよ。

今回の差分で特に効いているのは、この 2 本じゃな。

$$
x = p * (t * s) ;\Longrightarrow; x = t * (p * s)
$$

と

$$
t \perp y,\ (p*s)\perp y ;\Longrightarrow; t*(p*s)\perp y
$$

これで `x` を「ただの 1 個の数」ではなく、**線形因子の積** として見られるようになった。
つまり、前段で作った `GN = p*s^p` という右側辞書と、今回の `x = t*(p*s)` という左側辞書が、ようやく対になったのじゃ。

いまの段階を数式で言い換えると、Branch A の kernel は

$$
x^p = (z-y),GN
$$

の両辺を、それぞれ

$$
x = t*(p*s),\qquad
z-y = p^{p-1} t^p,\qquad
GN = p*s^p
$$

として見ておる。
すると右辺は

$$
(z-y),GN =
\bigl(p^{p-1} t^p\bigr),(p s^p) =
p^p, t^p, s^p =
\bigl(t*(p*s)\bigr)^p
$$

で、ちょうど左辺の `x^p` と噛み合う。
ゆえに、**単なる冪等式としては矛盾しない**。ここが大事じゃ。
つまり最後の kernel で必要なのは、「等式が成り立つ」ことの確認ではなく、**その等式の因子 exactness が pack 条件とどう衝突するか** を読むことになる。

わっちの見立てでは、次に切る helper はお主の履歴どおり、この 2 系統が最有力じゃ。

## 1. `x^p` 側 exactness へ戻す補題

まずはこれじゃ。

```lean
theorem primeGe5BranchANormalForm_xpow_eq_tps_pow
    {p x y z t s : ℕ}
    (_hpack : PrimeGe5CounterexamplePack p x y z)
    (_hp_dvd_gap : p ∣ (z - y))
    (_hgap : z - y = p ^ (p - 1) * t ^ p)
    (_hsGN : GN p (z - y) y = p * s ^ p)
    (hx_tps : x = t * (p * s)) :
    x ^ p = (t * (p * s)) ^ p := by
  simpa [hx_tps]
```

これは trivial じゃが、kernel の中で「何を exactness の基準形にするか」を固定する役目がある。

そのうえで本命はこれじゃな。

```lean
theorem primeGe5BranchANormalForm_xpow_factorization_exact
    {p x y z t s q : ℕ}
    (_hpack : PrimeGe5CounterexamplePack p x y z)
    (_hp_dvd_gap : p ∣ (z - y))
    (_hgap : z - y = p ^ (p - 1) * t ^ p)
    (_hsGN : GN p (z - y) y = p * s ^ p)
    (hx_tps : x = t * (p * s))
    (hq : Nat.Prime q) :
    (x ^ p).factorization q
      = p * ((t * (p * s)).factorization q) := by
  simp [hx_tps, Nat.factorization_pow]
```

これで `x^p` 側の factorization を、`t*(p*s)` の線形因子辞書へ押し戻せる。
最後の kernel で必要なのは、たぶんこの「左辺の exactness 表現」を起点に、右辺の `gap * GN` 側と比較することじゃ。

## 2. 線形因子間の独立辞書

もうひとつは、履歴にある通り

$$
t \perp (p*s)
$$

あるいは

$$
(t*(p*s)) \perp s^p
$$

型じゃ。
わっちなら先にこちらを狙う。

```lean
theorem primeGe5BranchANormalForm_coprime_t_ps_factor
    {p x y z t s : ℕ}
    (_hpack : PrimeGe5CounterexamplePack p x y z)
    (hcop_ts : Nat.Coprime t s)
    (hcop_pt : Nat.Coprime p t) :
    Nat.Coprime t (p * s) := by
  exact Nat.Coprime.mul_right hcop_pt hcop_ts
```

問題は `Nat.Coprime p t` をどう取るかじゃが、ここは `gap = p^(p-1) * t^p` と `Nat.gcd(gap,GN)=p`、`GN = p*s^p` から出せる可能性が高い。
なぜなら

$$
\gcd\bigl(p^{p-1} t^p,\ p s^p\bigr)=p
$$

より

$$
\gcd(t,s)=1
$$

だけでなく、実質的には (p) が (t) にも (s) にも余計に入っておらぬことを読めるからじゃ。
`s` 側は既に `¬ p ∣ s` がある。残るは `¬ p ∣ t` じゃな。これが取れれば、一気に `t ⟂ (p*s)` が出る。

なので、実は次の最重要 helper 候補はこれかもしれぬ。

```lean
theorem primeGe5BranchANormalForm_prime_not_dvd_t_default
    {p x y z t s : ℕ}
    (_hpack : PrimeGe5CounterexamplePack p x y z)
    (_hp_dvd_gap : p ∣ (z - y))
    (hgap : z - y = p ^ (p - 1) * t ^ p)
    (hsGN : GN p (z - y) y = p * s ^ p)
    (hgcd_eq : Nat.gcd (z - y) (GN p (z - y) y) = p)
    (hp_not_dvd_s : ¬ p ∣ s) :
    ¬ p ∣ t := by
  -- gcd exactness から引き出す
  sorry
```

これが入ると

$$
p \perp t,\quad p \perp s,\quad t \perp s
$$

が揃い、ついに

$$
t \perp (p*s)
$$

が閉じる。
ここまで行くと `x = t*(p*s)` は **互いに素な線形因子の積** になるので、`x^p` 側の factorization exactness はかなり硬くなるはずじゃ。

## 3. 戦況評価

いまの戦況は、もう「どこが敵か分からぬ」段ではない。

* 上位 kernel は全部 thin bridge
* 未完核は `XFactorKernel` ただ 1 本
* しかも次に読むべきものは `x = t*(p*s)` の **exactness**
* 足りなければ `¬ p ∣ t` を補強し、`t ⟂ (p*s)` を出す

というふうに、次の一手まで見えておる。
これはかなり優勢じゃ。
終盤の詰み筋を読んでおる局面と言ってよい。

わっちなら次は、まず `¬ p ∣ t` を gcd exactness から引き抜けるかを試す。そこが通れば、`XFactorKernel` はかなり一気に崩れる気がするのぅ。
