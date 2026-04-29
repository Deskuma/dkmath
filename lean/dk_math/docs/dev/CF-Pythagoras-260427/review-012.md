# review

おお……これは大きいぞ、D.。
S2-G 実装で、Chapter 2 の抽象エンジンはほぼ芯まで到達した。今回の差分により、FLT 型方程式から

$$
\text{Gap/Beam 分解}
\to
\gcd\text{ 制御}
\to
p\text{-adic valuation 抽出}
\to
valuation 上界との矛盾
$$

までが no-sorry で一本につながった。`flt_beam_prime_val_le_one_contradiction` と対称版が入ったことで、あとは **Beam 側の valuation 上界 \( \le 1 \) をどこから供給するか** が主課題になったわけじゃ。

## 1. 何が閉じたか

今回の主補題は、まず抽象算術側のこれじゃ。

$$
2\le d,\qquad 1\le v,\qquad v\le1,\qquad v=d k
\quad\Longrightarrow\quad
\bot
$$

Lean 名では、

```lean
padicValNat_eq_d_mul_and_le_one_contradiction
```

じゃな。
これは小さいが、今後かなり使える。
「正の valuation が \(1\) 以下で、しかも \(d\ge2\) の倍数」という矛盾を汎用化した補題じゃ。

さらに、

```lean
one_le_padicValNat_of_prime_dvd
```

で、

$$
p\mid n,\quad n\ne0
\quad\Longrightarrow\quad
1\le v_p(n)
$$

を補助補題として用意した。`p ∣ Beam` だけでは `Beam = 0` を排除できないので、`n ≠ 0` を明示仮定にした判断は正しい。

そして本丸が、

```lean
flt_beam_prime_val_le_one_contradiction
```

および対称版。
これは、仮定として

$$
x^d+y^d=z^d,\quad \gcd(z,x)=1,\quad y\ne0,
$$
$$
p\nmid d,\quad p\mid \operatorname{Beam}_d(x,z),\quad
\operatorname{Beam}_d(x,z)\ne0,\quad
v_p(\operatorname{Beam}_d(x,z))\le1
$$

を置くと `False` を返す。
まさに S2-F の

$$
v_p(\operatorname{Beam}_d)=d,v_p(y)
$$

と、\(v_p(\operatorname{Beam}_d)\le1\) を衝突させる補題じゃ。

## 2. 数学的意味

ここまでの流れは美しい。

FLT 型方程式

$$
x^d+y^d=z^d
$$

から、

$$
y^d=(z-x)\operatorname{Beam}_d(x,z)
$$

を得る。

次に、

$$
\gcd(z-x,\operatorname{Beam}_d(x,z))\mid d
$$

なので、\(p\nmid d\) かつ \(p\mid \operatorname{Beam}_d(x,z)\) なら、

$$
p\nmid z-x
$$

が出る。

ゆえに、

$$
v_p((z-x)\operatorname{Beam}_d)=v_p(\operatorname{Beam}_d)
$$

となる。

一方で左辺は \(v_p(y^d)\) だから、

$$
v_p(\operatorname{Beam}_d)=d,v_p(y)
$$

となる。

ここに

$$
p\mid \operatorname{Beam}_d
$$

から

$$
1\le v_p(\operatorname{Beam}_d)
$$

が入り、さらに

$$
v_p(\operatorname{Beam}_d)\le1
$$

が入ると、

$$
v_p(\operatorname{Beam}_d)=1
$$

を強制する。

しかし

$$
v_p(\operatorname{Beam}_d)=d,v_p(y)
$$

で \(2\le d\) なので、右辺は \(0\) か \(2\) 以上。
したがって \(1\) にはなれぬ。

これで矛盾じゃ。

つまり今回、Lean 上で次の原理が固定された。

> FLT 型方程式において、Beam 側に現れる \(p\nmid d\) の素因子が valuation \(1\) 以下なら、完全 \(d\) 乗性と両立しない。

これはかなり強い抽象エンジンじゃよ。

## 3. 実装評価

今回の実装は堅実じゃ。

特に `padicValNat_eq_d_mul_and_le_one_contradiction` を先に分離したのがよい。
これにより、PowerGapBeam 固有の重い仮定から、最後の自然数算術の矛盾を切り離せている。

また、`one_le_padicValNat_of_prime_dvd` で `padicValNat_dvd_iff_le` を使っているのも自然じゃ。`@padicValNat_dvd_iff_le p (Fact.mk hp) n 1 hn` の形で明示適用したと History にも記録されている。

`Beam.natAbs ≠ 0` を wrapper 側に明示したのも正解じゃ。
これはやや仮定が増えるが、FLT primitive package 側では自然に供給できるはずなので、ここでは無理に導かない方がよい。

## 4. 現在の Chapter 2 の到達点

ここまでの S2 は、非常に明確な階段になっている。

$$
z^d-x^d=(z-x)\operatorname{Beam}_d(x,z)
$$

$$
x^d+y^d=z^d
\Rightarrow
y^d=(z-x)\operatorname{Beam}_d(x,z)
$$

$$
\gcd(z-x,\operatorname{Beam}_d)\mid d
$$

$$
p\nmid d,\ p\mid \operatorname{Beam}_d
\Rightarrow
p\nmid z-x
$$

$$
v_p((z-x)\operatorname{Beam}_d)=v_p(\operatorname{Beam}_d)
$$

$$
v_p(\operatorname{Beam}_d)=d,v_p(y)
$$

$$
p\mid \operatorname{Beam}_d,\ v_p(\operatorname{Beam}_d)\le1,\ 2\le d
\Rightarrow
\bot
$$

ここまで no-sorry で揃ったのは、普通に大きい。
Chapter 2 はもはや「差分解釈」ではなく、**FLT Gap/Beam valuation refuter** の形を持ち始めておる。

## 5. 次の提案: S2-H

次はもう明確じゃ。

> Beam 側の primitive prime / squarefree 上界 API から
> \[
> v_p(\operatorname{Beam}_d)\le1
> \]
> を供給する bridge を作る。

History の次課題にも、そのまま書かれておる。

まずは既存 API の探索が必要じゃ。

探す対象は、

```text
PrimitiveBeam
ZsigmondyCyclotomicSquarefree
padicValNat_primitive
squarefree_implies_padic_val_le_one
```

このあたり。

狙いは二段構えがよい。

### 5.1. Squarefree bridge

まず一般補題として、

```lean
theorem padicValNat_le_one_of_squarefree
    {p n : ℕ}
    (hp : Nat.Prime p)
    (hsq : Squarefree n) :
    padicValNat p n ≤ 1 := ...
```

既にあるなら wrapper。
なければ既存 `Squarefree` API から作る。

そして PowerBeam 用に、

```lean
theorem powerBeam_padicValNat_le_one_of_squarefree
    {d : ℕ} {x z : ℤ} {p : ℕ}
    (hp : Nat.Prime p)
    (hsq : Squarefree (powerBeam d x z).natAbs) :
    padicValNat p (powerBeam d x z).natAbs ≤ 1 := ...
```

これで S2-G に供給できる。

### 5.2. PrimitiveBeam bridge

次に、既存の primitive prime / Beam API があるなら、

```lean
theorem powerBeam_padicValNat_le_one_of_primitive_prime
```

のような名前で、primitive 条件から直接

$$
v_p(\operatorname{Beam})\le1
$$

を出す。

ただし、ここは既存定理の形に合わせるべきじゃ。
無理に PowerBeam 側へ合わせるより、まず `powerBeam = diffPowSum` の bridge を使い、既存定理の入力へ変換するのが自然じゃ。

## 6. S2-H の最小到達目標

最初は、強い primitive 版に行かず、squarefree 仮定版だけでよい。

つまり、次の定理を閉じる。

```lean
theorem flt_beam_squarefree_prime_contradiction
    {d p : ℕ} {x y z : ℤ}
    (hd1 : 1 ≤ d)
    (hd2 : 2 ≤ d)
    (hcop : Int.gcd z x = 1)
    (hflt : x ^ d + y ^ d = z ^ d)
    (hy_ne : y.natAbs ≠ 0)
    (hp : Nat.Prime p)
    (hpnd : ¬ p ∣ d)
    (hbeam : p ∣ (powerBeam d x z).natAbs)
    (hbeam_ne : (powerBeam d x z).natAbs ≠ 0)
    (hsq : Squarefree (powerBeam d x z).natAbs) :
    False := by
  apply flt_beam_prime_val_le_one_contradiction
  · exact hd1
  · exact hd2
  · exact hcop
  · exact hflt
  · exact hy_ne
  · exact hp
  · exact hpnd
  · exact hbeam
  · exact hbeam_ne
  · exact powerBeam_padicValNat_le_one_of_squarefree hp hsq
```

これが閉じれば、S2-G の抽象矛盾に対して、ひとつ具体的な上界供給ルートがつく。

## 7. さらに次: primitive prime の existence と接続

Squarefree 版が閉じたら、次は本命。

FLT 文脈で、Beam 側に

$$
p\nmid d,\quad p\mid Beam,\quad v_p(Beam)\le1
$$

を満たす \(p\) をどう得るか。

ここで既存の Zsigmondy / PrimitiveBeam が登場する。
DkMath の構成マップでは、FLT 幹線は差の冪、gcd 制御、原始素因子、p-adic valuation を通じる構造として整理されており、`ZsigmondyCyclotomic` が原始素因子エンジンとして位置づけられている。

今回の PowerGapBeam は、その前段に **観測インターフェース** を置いた。
次は既存 primitive engine から、この S2-G contradiction engine へ燃料を供給することじゃ。

## 8. 構造体導入の判断

そろそろ `FLTPowerGapBeamDatum` 構造体を検討してよい段階には来た。

ただし、わっちはまだ **もう一手だけ待つ** のを勧める。

理由は、S2-H で `Squarefree` 版または primitive 版を入れると、構造体に持たせたいフィールドが見えるからじゃ。

現時点で入れるなら、最低限はこれ。

```lean
structure FLTPowerGapBeamDatum where
  gap : ℤ
  beam : ℤ
  hprod : side ^ d = gap * beam
  hgcd : Int.gcd gap beam ∣ d
```

しかし S2-H 後には、

```lean
  hbeam_ne : beam.natAbs ≠ 0
  hbeam_prime_not_gap : ...
  hval_eq : ...
```

なども欲しくなるかもしれん。
今は wrapper 群で十分じゃ。

## 9. まとめ

S2-G は成功じゃ。
そして、これは Chapter 2 の大きな節目じゃ。

今回で、

$$
p\mid Beam,\quad v_p(Beam)\le1,\quad 2\le d
$$

が、FLT 型完全 \(d\) 乗制約と両立しないことを Lean 上で示せるようになった。

残る課題は一つに絞られた。

> Beam 側に現れる素因子 \(p\) に対して、
> \[
> v_p(Beam)\le1
> \]
> を既存 primitive / squarefree API から供給する。

次は S2-H。
わっちならまず squarefree 版で上界供給 bridge を作り、そのあと primitive prime 版へ進む。
ここまで来たら、もう葡萄酒を開けてもよい進捗じゃ。もちろん、飲みすぎると翌朝つらいがの。
