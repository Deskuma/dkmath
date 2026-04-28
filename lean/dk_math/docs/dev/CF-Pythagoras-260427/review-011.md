# review

おお、S2-F 実装、確認したぞ。
これはかなり重要な到達点じゃ。ついに

$$
v_p(\mathrm{Beam}_d)=d,v_p(\text{side})
$$

という **完全 (d) 乗側の付値制約** まで Lean 上で橋がつながった。報告どおり、`flt_padicValNat_beam_eq_d_mul_y_of_beam_prime` と対称版が no-sorry で入っておる。

## 1. 何が閉じたか

今回の主定理は、片側で言えばこれじゃ。

$$
x^d+y^d=z^d
$$

かつ

$$
p\nmid d,\qquad p\mid |\mathrm{Beam}_d(x,z)|
$$

さらに primitive 的条件

$$
\gcd(z,x)=1
$$

と (y\ne0) のもとで、

$$
v_p(|\mathrm{Beam}_d(x,z)|)=d,v_p(|y|)
$$

を得る。

Lean 名では、

```lean
flt_padicValNat_beam_eq_d_mul_y_of_beam_prime
```

じゃな。対称に、

```lean
flt_padicValNat_beam_eq_d_mul_x_of_beam_prime_symm
```

も入っている。

つまり、S2-B から S2-F までで次の鎖が no-sorry でつながった。

$$
x^d+y^d=z^d
$$

$$
y^d=\mathrm{Gap}\cdot\mathrm{Beam}
$$

$$
p\nmid d,\quad p\mid \mathrm{Beam}
\Rightarrow
p\nmid \mathrm{Gap}
$$

$$
v_p(\mathrm{Gap}\cdot\mathrm{Beam})=v_p(\mathrm{Beam})
$$

$$
v_p(\mathrm{Beam})=v_p(y^d)=d,v_p(y)
$$

ここまで来ると、もはや観測ではなく、FLT 反例に対する **p-adic 制約抽出器** じゃ。

## 2. 数学的意味

この補題が意味していることは鋭い。

Beam 側に \(p\nmid d\) の素数が現れるなら、その Beam 側での指数は、完全 \(d\) 乗の指数と一致せねばならぬ。
すなわち、

$$
v_p(\mathrm{Beam}_d)
$$

は \(d\) の倍数である。

ところが、primitive prime や squarefree Beam の議論で、

$$
v_p(\mathrm{Beam}_d)\le 1
$$

が来るなら、\(d\ge2\) ではほぼ破綻する。

なぜなら \(p\mid \mathrm{Beam}\) より

$$
1\le v_p(\mathrm{Beam})
$$

であり、さらに

$$
v_p(\mathrm{Beam})=d,v_p(y)
$$

だから、右辺は \(d\) の倍数。
\(2\le d\) で \(v_p(\mathrm{Beam})\le1\) なら、可能性は \(v_p(\mathrm{Beam})=1\) しかないが、\(1=d,v_p(y)\) は自然数では無理じゃ。

つまり、次に必要なのは本当に

$$
v_p(\mathrm{Beam})\le1
$$

を供給する側だけになってきた。

## 3. 実装判断の評価

`padicValNat.pow` が底の非ゼロ仮定を要求するため、`y.natAbs ≠ 0` / `x.natAbs ≠ 0` を定理に明示仮定として追加した判断は正しい。

ここを無理に `p ∣ Beam` から導こうとすると、Beam や side のゼロケースで苦しむ。
FLT primitive package 側なら (x,y,z>0) や非ゼロ性は自然に持っているはずなので、ここでは明示仮定にしておくのが一番健全じゃ。

実装も綺麗じゃ。

* `flt_eq_forces_powerGapBeam` で積分解
* `flt_padicValNat_product_eq_beam_of_beam_prime` で積の valuation を Beam に移す
* `Int.natAbs_pow` で \(|y^d|=|y|^d\)
* `padicValNat.pow` で \(v_p(|y|^d)=d v_p(|y|)\)

という流れがそのまま Lean の `calc` に乗っている。

## 4. 次の提案: S2-G

次は History にある通り、**valuation 上界との衝突補題** じゃ。

まずは完全に一般的な算術補題として、PowerGapBeam から少し独立した形で置くとよい。

狙いはこれ。

```lean
theorem padicValNat_eq_d_mul_and_le_one_contradiction
    {d v k : ℕ}
    (hd : 2 ≤ d)
    (hv_pos : 1 ≤ v)
    (hv_le_one : v ≤ 1)
    (hv_eq : v = d * k) :
    False := by
  ...
```

ただし (k=padicValNat p y.natAbs), (v=padicValNat p Beam.natAbs) じゃ。

もっと直接には、次の形。

```lean
theorem flt_beam_prime_val_le_one_contradiction
    {d p : ℕ} {x y z : ℤ}
    (hd1 : 1 ≤ d)
    (hd2 : 2 ≤ d)
    (hcop : Int.gcd z x = 1)
    (hflt : x ^ d + y ^ d = z ^ d)
    (hy_ne : y.natAbs ≠ 0)
    (hp : Nat.Prime p)
    (hpnd : ¬ p ∣ d)
    (hbeam : p ∣ (powerBeam d x z).natAbs)
    (hbeam_le_one :
      padicValNat p (powerBeam d x z).natAbs ≤ 1) :
    False := by
  ...
```

証明の流れはこうじゃ。

1. `hbeam` から

$$
1\le v_p(\mathrm{Beam})
$$

を得る。既存に `padicValNat.one_le_of_dvd` 系があれば使う。

1. `hbeam_le_one` と合わせて

$$
v_p(\mathrm{Beam})=1
$$

を得る。

1. S2-F から

$$
v_p(\mathrm{Beam})=d,v_p(y)
$$

を得る。

1. よって

$$
1=d,v_p(y)
$$

1. しかし \(2\le d\) なら \(d,v_p(y)\) は \(0\) または \(2\) 以上。矛盾。

Lean では、`omega` が使えるなら最後はかなり楽じゃ。

## 5. S2-G 実装スケッチ

```lean
theorem flt_beam_prime_val_le_one_contradiction
    {d p : ℕ} {x y z : ℤ}
    (hd1 : 1 ≤ d)
    (hd2 : 2 ≤ d)
    (hcop : Int.gcd z x = 1)
    (hflt : x ^ d + y ^ d = z ^ d)
    (hy_ne : y.natAbs ≠ 0)
    (hp : Nat.Prime p)
    (hpnd : ¬ p ∣ d)
    (hbeam : p ∣ (powerBeam d x z).natAbs)
    (hbeam_le_one :
      padicValNat p (powerBeam d x z).natAbs ≤ 1) :
    False := by
  have hval_eq :
      padicValNat p (powerBeam d x z).natAbs =
        d * padicValNat p y.natAbs :=
    flt_padicValNat_beam_eq_d_mul_y_of_beam_prime
      (d := d) (p := p) (x := x) (y := y) (z := z)
      hd1 hcop hflt hy_ne hp hpnd hbeam

  have hval_pos :
      1 ≤ padicValNat p (powerBeam d x z).natAbs := by
    -- use existing padicValNat_one_le_of_prime_dvd / padicValNat.one_le_of_dvd
    ...

  have hval_eq_one :
      padicValNat p (powerBeam d x z).natAbs = 1 := by
    omega

  have hone :
      1 = d * padicValNat p y.natAbs := by
    simpa [hval_eq_one] using hval_eq

  omega
```

もし `omega` が渋ければ、最後は手動で、

* `padicValNat p y.natAbs = 0` なら右辺 \(0\)
* 正なら右辺 \(\ge d\ge2\)

の分岐でも閉じられる。

対称版も同様に置く。

```lean
flt_beam_prime_val_le_one_contradiction_symm
```

## 6. その次: 上界供給 bridge

S2-G が閉じたら、残る問題は

$$
v_p(\mathrm{Beam})\le1
$$

をどこから供給するかじゃ。

候補は二つ。

### 6.1. squarefree Beam

Beam の squarefree 性があれば即座に

$$
v_p(\mathrm{Beam})\le1
$$

が出る。

名前候補:

```lean
beam_padicValNat_le_one_of_squarefree
```

既存の `ZsigmondyCyclotomicSquarefree` や `PrimitiveBeam` に近い補題があるはずじゃ。以前の計画でも、squarefree `GN` なら valuation が高々 1 になる spine が置かれている。

### 6.2. primitive prime valuation upper bound

primitive prime \(p\) が Beam 側に出て、かつ既存 primitive valuation 上界があれば、

$$
v_p(\mathrm{Beam})\le1
$$

を直接供給できる。

これが本命じゃな。

## 7. 現在の Chapter 2 進捗

ここまでの S2 は、かなり見事に積み上がっている。

* S2-A: \(z^d-x^d=Gap\cdot Beam_d\)
* S2-B: FLT 型方程式から Gap × Beam へ
* S2-C: \(\gcd(Gap,Beam)\mid d\)
* S2-D: \(p\nmid d\), \(p\mid Beam\) なら \(p\nmid Gap\)
* S2-E: \(v_p(Gap\cdot Beam)=v_p(Beam)\)
* S2-F: \(v_p(Beam)=d,v_p(side)\)

次は、

* S2-G: \(v_p(Beam)\le1\) と \(p\mid Beam\) を仮定した抽象矛盾
* S2-H: その上界を primitive / squarefree API から供給する bridge

という流れじゃ。

## 8. まとめ

S2-F は成功じゃ。
これで、Beam 側素因子が FLT の完全 (d) 乗制約により **(d) 倍の付値を持たざるをえない** ところまで形式化された。

次は一気に衝突させる段階。

$$
p\mid Beam,\quad v_p(Beam)\le1,\quad 2\le d
$$

と

$$
v_p(Beam)=d,v_p(side)
$$

をぶつけて False を出す。

ここまで閉じれば、Chapter 2 は「FLT 反例を Gap/Beam/valuation で拒否する抽象エンジン」の形を帯びてくるぞ。
