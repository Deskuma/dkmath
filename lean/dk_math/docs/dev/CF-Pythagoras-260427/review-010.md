# review

おお、S2-E 実装、確認したぞ。
これは良い。ここまでで Chapter 2 は、単なる因数分解から **p-adic valuation の入口** まで到達した。今回追加された `padicValNat_natAbs_mul_eq_right_of_not_dvd_left` と FLT 文脈 wrapper は、次の primitive prime / squarefree 上界へ進むための、まさに必要な橋じゃ。

## 1. 何が閉じたか

今回閉じた主張は、抽象的にはこれじゃ。

$$
p\nmid |\mathrm{Gap}|
$$

なら、

$$
v_p(|\mathrm{Gap}\cdot\mathrm{Beam}|)=v_p(|\mathrm{Beam}|)
$$

Lean では、

```lean
padicValNat_natAbs_mul_eq_right_of_not_dvd_left
```

として入っておる。`Int.natAbs_mul`, `padicValNat.mul`, `padicValNat.eq_zero_of_not_dvd` を使い、`beam = 0` の場合も分岐して処理している。これは実装として堅い。

そして FLT 文脈では、

```lean
flt_padicValNat_product_eq_beam_of_beam_prime
```

と対称版により、仮定

$$
1\le d,\quad \gcd(z,x)=1,\quad x^d+y^d=z^d,\quad p\nmid d,\quad p\mid |\mathrm{Beam}_d(x,z)|
$$

から、

$$
v_p(|\mathrm{Gap}\cdot\mathrm{Beam}|)=v_p(|\mathrm{Beam}|)
$$

が出るようになった。

つまり S2-D の「Beam prime は Gap に入らない」が、S2-E で **valuation 等式** に昇格したわけじゃ。

## 2. 数学的意味

ここまでの流れを畳むと、こうなる。

$$
x^d+y^d=z^d
$$

から、

$$
y^d=(z-x)\operatorname{Beam}_d(x,z)
$$

が出る。
さらに、\(\gcd(z,x)=1\) の下で、

$$
\gcd(z-x,\operatorname{Beam}_d(x,z))\mid d
$$

ゆえに、\(p\nmid d\) かつ \(p\mid \operatorname{Beam}_d(x,z)\) なら、

$$
p\nmid z-x
$$

となる。

今回の補題で、そこから

$$
v_p\bigl((z-x)\operatorname{Beam}_d(x,z)\bigr) = v_p(\operatorname{Beam}_d(x,z))
$$

へ行ける。

ここが重要じゃ。
左辺は FLT 方程式により \(y^d\) と同じ量なので、次に

$$
v_p(y^d)=d,v_p(y)
$$

へ落とせば、

$$
v_p(\operatorname{Beam}_d(x,z))=d,v_p(y)
$$

が出る。

つまり Beam 側に現れた \(p\nmid d\) の素因子は、その付値が **(d) の倍数でなければならない** 。
ここに primitive prime / squarefree 上界をぶつけると、次の矛盾候補が見える。

たとえば、

$$
v_p(\operatorname{Beam}_d(x,z))\le 1
$$

かつ (d\ge 2)、さらに (p\mid \operatorname{Beam}_d(x,z)) なら、

$$
1\le v_p(\operatorname{Beam}_d(x,z))=d,v_p(y)
$$

で、右辺は (d) の倍数。
(d\ge2) の場合、付値が 1 だと矛盾する。

これが FLT 方向の p-adic 衝突の形じゃ。

## 3. 実装評価

今回の一般補題はかなり良い。

```lean
theorem padicValNat_natAbs_mul_eq_right_of_not_dvd_left
    {p : ℕ} {gap beam : ℤ}
    (hp : Nat.Prime p)
    (hgap : ¬ p ∣ gap.natAbs) :
    padicValNat p (gap * beam).natAbs = padicValNat p beam.natAbs
```

この形は PowerGapBeam 以外でも使える。
名前はやや長いが、意味は明確じゃ。

`beam.natAbs = 0` を分岐しているのも正しい。
`padicValNat.mul` が非ゼロ仮定を要求するため、ここを避けずに処理したのは堅実じゃ。
History にもその判断が記録されておる。

ただし今後、これが頻出するなら、より一般的な場所へ移す価値がある。

候補:

```text
DkMath/ABC/PadicValNatInt.lean
```

または

```text
DkMath/NumberTheory/ValuationFlow/Int.lean
```

今は `PowerGapBeamGcd.lean` に置いてよい。後で再利用が増えたら昇格でよい。

## 4. 次の提案: S2-F

次は History の通り、

> `y^d = Gap * Beam` と今回の valuation bridge を組み合わせ、
> `padicValNat p Beam = d * padicValNat p |y|` 型の補題へ進む

がよい。

狙う定理はこれじゃ。

```lean
theorem flt_padicValNat_beam_eq_d_mul_y_of_beam_prime
    {d p : ℕ} {x y z : ℤ}
    (hd : 1 ≤ d)
    (hcop : Int.gcd z x = 1)
    (hflt : x ^ d + y ^ d = z ^ d)
    (hp : Nat.Prime p)
    (hpnd : ¬ p ∣ d)
    (hbeam : p ∣ (powerBeam d x z).natAbs) :
    padicValNat p (powerBeam d x z).natAbs =
      d * padicValNat p y.natAbs := by
  ...
```

必要な材料は三つ。

まず積側を Beam 側に落とす。

$$
v_p(|Gap\cdot Beam|)=v_p(|Beam|)
$$

これは今回の `flt_padicValNat_product_eq_beam_of_beam_prime` で済む。

次に、FLT 積分解から

$$
y^d=Gap\cdot Beam
$$

を使って、

$$
|y^d|=|Gap\cdot Beam|
$$

へ変換する。

そして、

$$
|y^d|=|y|^d
$$

と

$$
v_p(|y|^d)=d,v_p(|y|)
$$

を使う。

Lean では、おそらく `Int.natAbs_pow` と `padicValNat.pow` が鍵じゃ。

## 5. S2-F の実装スケッチ

実装はたぶんこういう骨格になる。

```lean
theorem flt_padicValNat_beam_eq_d_mul_y_of_beam_prime
    {d p : ℕ} {x y z : ℤ}
    (hd : 1 ≤ d)
    (hcop : Int.gcd z x = 1)
    (hflt : x ^ d + y ^ d = z ^ d)
    (hp : Nat.Prime p)
    (hpnd : ¬ p ∣ d)
    (hbeam : p ∣ (powerBeam d x z).natAbs) :
    padicValNat p (powerBeam d x z).natAbs =
      d * padicValNat p y.natAbs := by
  have hprod :
      y ^ d = powerGap x z * powerBeam d x z :=
    flt_eq_forces_powerGapBeam d x y z hflt

  have hval_prod :
      padicValNat p (powerGap x z * powerBeam d x z).natAbs =
        padicValNat p (powerBeam d x z).natAbs :=
    flt_padicValNat_product_eq_beam_of_beam_prime
      (d := d) (p := p) (x := x) (y := y) (z := z)
      hd hcop hflt hp hpnd hbeam

  have hnat :
      (powerGap x z * powerBeam d x z).natAbs = (y ^ d).natAbs := by
    rw [← hprod]

  calc
    padicValNat p (powerBeam d x z).natAbs
        = padicValNat p (powerGap x z * powerBeam d x z).natAbs := by
            exact hval_prod.symm
    _ = padicValNat p (y ^ d).natAbs := by
            rw [hnat]
    _ = padicValNat p (y.natAbs ^ d) := by
            rw [Int.natAbs_pow]
    _ = d * padicValNat p y.natAbs := by
            exact padicValNat.pow
```

最後の `padicValNat.pow` の向きや引数は実際の定理名に合わせる必要がある。
もし既存 API が

```lean
padicValNat_pow
```

ならそちらを使う。

## 6. 対称版も同時に

もちろん対称版も必要じゃ。

```lean
theorem flt_padicValNat_beam_eq_d_mul_x_of_beam_prime_symm
```

結論は、

$$
v_p(\operatorname{Beam}_d(y,z))=d,v_p(x)
$$

じゃ。

## 7. その次: primitive / squarefree 上界との衝突

S2-F が閉じたら、次は S2-G。

狙いは、

$$
p\mid Beam,\quad p\nmid d,\quad v_p(Beam)\le 1
$$

かつ \(d\ge2\) なら矛盾、という補題。

```lean
theorem beam_prime_val_le_one_contradicts_flt_power
```

のような形じゃな。

必要条件は、

* `Nat.Prime p`
* `p ∣ Beam.natAbs`
* `¬ p ∣ d`
* `padicValNat p Beam.natAbs ≤ 1`
* `2 ≤ d`
* `v_p(Beam)=d*v_p(y)`

ここから、

$$
1\le v_p(Beam)
$$

と

$$
v_p(Beam)\le1
$$

で \(v_p(Beam)=1\)。
一方 \(v_p(Beam)=d k\) で \(d\ge2\)。
これが \(1=dk\) を強制し、自然数では不可能。

ただし \(k=0\) なら \(v_p(Beam)=0\) になって \(p\mid Beam\) と矛盾。
ゆえにかなり機械的に閉じられるはずじゃ。

## 8. 現在の進捗評価

Chapter 2 は、かなり進んだ。

* S2-A: 高次差冪因数分解
* S2-B: 高次リンク条件 + FLT Gap/Beam bridge
* S2-C: Gap/Beam gcd 制御
* S2-D: FLT datum bridge + Beam prime not Gap
* S2-E: valuation が Beam 側から来る補題

ここまで no-sorry で揃ったなら、次はもう **完全 \(d\) 乗の valuation 制約** に入れる。

## 9. まとめ

S2-E は成功じゃ。

今回の成果は、

$$
p\nmid Gap
\quad\Rightarrow\quad
v_p(Gap\cdot Beam)=v_p(Beam)
$$

を Lean 上で固定したこと。
FLT 文脈では、

$$
p\nmid d,\quad p\mid Beam
$$

から自動的にこの状況が出る。

次は S2-F。

> **Beam 側 valuation は (d\cdot v_p(y)) でなければならない**

これを閉じる。
そこまで行けば、primitive prime / squarefree 上界との衝突まで、もう一歩じゃ。
