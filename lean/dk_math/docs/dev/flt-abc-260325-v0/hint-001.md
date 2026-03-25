うむ、その整理でよい。
そして一つ、賢狼から **さらに締まる見立て** を足すなら、こうじゃ。

\[
\text{第1補題は } \texttt{gapShape} \text{ を要らぬ}
\]

じゃ。
Branch A では、すでに手元の lower layer だけで

\[
GN\bigl(p,z-y,y\bigr)=p\cdot s^p
\]

まで先に落とせる公算が高い。
理由は、お主がもう揃えておる 2 本、

\[
q\neq p \text{ 側の no-shared}
\quad+\quad
\nu_p(GN)=1
\]

が、それだけで **GN 側の factorization 完全再構成** に足りるからじゃ。

なので、最短路の補題列は、わっちなら次の形にする。

## 1. GN 再注入は `gapShape` なしで先に閉じる

まずはこれじゃ。

```lean
/--
Branch A では GN 自体が `p * s^p` 形になる。
`gapShape` はまだ使わない。
-/
theorem primeGe5BranchAGN_eq_p_mul_pow_math
    {p x y z : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hp_dvd_gap : p ∣ (z - y)) :
    ∃ s : ℕ, GN p (z - y) y = p * s ^ p := by
  -- 設計：
  -- 1. N := GN p (z - y) y と置く
  -- 2. `p_dvd_GN_and_not_sq_when_p_dvd_gap` から
  --      p ∣ N ∧ ¬ p^2 ∣ N
  --    よって `N.factorization p = 1`
  -- 3. `gapNePNoSharedPrimeOnGN_branchA_math` と
  --    `x^p = gap * N` から、
  --    任意の q ≠ p について `p ∣ N.factorization q`
  -- 4. w := N / p と置くと、全 q で `p ∣ w.factorization q`
  -- 5. `exists_eq_pow_of_factorization_dvd` で `w = s^p`
  -- 6. よって `N = p * s^p`
  sorry
```

ここが一番大事じゃ。
お主の案だと第1補題は `gapShape` を仮定しておったが、実はそれを前段へ押し上げられる。
つまり、Branch A から得られる剛体は本当は

\[
GN = p\cdot s^p
\]

の方でもある、ということじゃな。

---

## 2. `gapShape` と GN-shape を合成して `x` の形を固定する

次は witness kernel に入る前の正規形じゃ。

```lean
/--
Branch A witness から
`gap`, `GN`, `x`
の 3 つを同時に正規形へ揃える。
-/
theorem primeGe5BranchANormalForm_of_witness
    {p x y z t : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hp_dvd_gap : p ∣ (z - y))
    (ht : z - y = p ^ (p - 1) * t ^ p) :
    ∃ s : ℕ,
      GN p (z - y) y = p * s ^ p ∧
      x = p * (t * s) := by
  rcases primeGe5BranchAGN_eq_p_mul_pow_math hpack hp_dvd_gap with ⟨s, hs⟩
  refine ⟨s, hs, ?_⟩
  -- `x^p = gap * GN` に `ht`, `hs` を代入すると
  --   x^p = p^p * (t*s)^p = (p*(t*s))^p
  -- となるので、自然数の p 乗の単射性から
  --   x = p * (t*s)
  -- を得る
  sorry
```

この 2 本目で得られる最終像は

\[
z-y = p^{,p-1} t^p,\qquad
GN = p,s^p,\qquad
x = p(ts)
\]

じゃ。
この三つ組が、わっちの見るところ **局所 kernel の本当の入力** じゃな。

注意点として、単に

\[
p \mid x
\]

だけを出しても、まだ弱い。
`hxy : \mathrm{Coprime}(x,y)` と `p \nmid y` だけでは即 `False` にはならぬ。
ゆえに第2補題は「`x = p*r`」で止めず、**`x = p*(t*s)` まで固定** する方がよい。

---

## 3. kernel は `False` を直接狙うより「normal form refuter」に分ける

いまの `BranchAShapeWitnessKernelTarget` をそのまま閉じてもよいが、
デバッグしやすさと責務分離のためには、間にこの 1 枚を挟むのが綺麗じゃ。

```lean
/--
Branch A の局所数学核。
ここだけが「normal form をどう矛盾へ送るか」を担う。
-/
abbrev PrimeGe5BranchANormalFormRefuterTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    False
```

そして witness kernel は薄い橋にする。

```lean
theorem primeGe5BranchAShapeWitnessKernel_of_normalFormRefuter
    (hRef : PrimeGe5BranchANormalFormRefuterTarget) :
    BranchAShapeWitnessKernelTarget := by
  intro p x y z t hpack hp_dvd_gap ht
  rcases primeGe5BranchANormalForm_of_witness hpack hp_dvd_gap ht with
    ⟨s, hsGN, hsx⟩
  exact hRef hpack hp_dvd_gap ht hsGN hsx
```

これで外側は完全に `descent` 殻のまま、
中身だけが **局所 gcd/valuation 衝突核** になる。

---

## 4. ここから先の「局所矛盾」は何を狙うべきか

ここはまだ 2 通りあるが、いずれも normal form を使うのがよい。

### 4.1. gcd の exactness を詰める道

`gap = p^(p-1)t^p` と `GN = p s^p` から

\[
\gcd(z-y, GN) = p \cdot \gcd(t,s)^p
\]

型の評価へ寄せ、既存の

\[
\gcd(gap, GN) \mid p
\]

と衝突させる道じゃ。
これが通れば、

\[
\gcd(t,s)=1
\]

を強制できる。
さらに `x = pts` と `hxy`、`gap_coprime_right` などを組み合わせて、
(t) や (s) のどちらかに「入ってはいけない素因子」が入ることを導ければ、そのまま局所 refuter になる。

### 4.2. valuation の exactness を詰める道

normal form から

\[
\nu_q(x)=\nu_q(t)+\nu_q(s)
\quad (q\neq p)
\]

や

\[
\nu_p(x)=1+\nu_p(t)+\nu_p(s)
\]

を読む。
これを pack 側の既存正規化や、将来の descent input へ渡す制約に変換する。
これは局所矛盾そのものというより、「局所 kernel を closure するための valuation dictionary」じゃな。

---

## 5. いま切るべき最小セット

結論として、いま切るべき skeleton はこの 4 本で十分じゃ。

```lean
theorem primeGe5BranchAGN_eq_p_mul_pow_math ...
theorem primeGe5BranchANormalForm_of_witness ...
abbrev PrimeGe5BranchANormalFormRefuterTarget : Prop := ...
theorem primeGe5BranchAShapeWitnessKernel_of_normalFormRefuter ...
```

これで、

* 外殻は `descent` のまま
* 数学核は `局所 gcd/valuation 衝突`
* `GN 再注入` は補助補題

という、お主の見立てがそのまま Lean の責務分解に落ちる。

そして一番良い点は、`primeGe5BranchAGN_eq_p_mul_pow_math` が閉じた瞬間、
Branch A の内部像が

\[
(gap,\ GN,\ x) =
\bigl(p^{p-1}t^p,\ p s^p,\ p t s\bigr)
\]

へ固定されることじゃ。
ここまで来れば、もう `via_FLT` で誤魔化す場所はほとんど残らぬ。

必要なら次に、この 4 本のうち **第1補題の proof script の流れ** を、Lean の tactic 順まで落として切るぞい。
