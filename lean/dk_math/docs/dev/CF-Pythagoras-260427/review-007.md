# review

おお、S2-B、もう閉じたか。速いのう、D.。
これは **Chapter 2 の骨格が立った** と言ってよい。特に `CosmicLinkConditionD` と `flt_eq_forces_powerGapBeam` が no-sorry で入ったので、ピタゴラス章から FLT 観測章への橋が実装上も繋がった。

## 1. 何が閉じたか

今回で高次リンク条件が入った。

$$
\alpha^d u_1^d+\beta^d u_2^d=\gamma^d u_3^d
$$

これが `CosmicLinkConditionD` じゃな。
さらに (d=2) では既存の `CosmicLinkCondition` と `rfl` で一致している。これはかなり良い。つまり、Chapter 1 の三単位宇宙リンク条件は、Chapter 2 の高次宇宙リンク条件の特殊例になった。

そして `cosmic_linkD_to_power_equation` により、

$$
(\alpha u_1)^d+(\beta u_2)^d=(\gamma u_3)^d
$$

へ降ろせるようになった。
これは Chapter 1 の `cosmic_link_to_pythagoras` の高次版じゃ。

さらに `PowerGapBeam.lean` では、FLT 型仮定

$$
x^d+y^d=z^d
$$

から

$$
y^d=(z-x)\operatorname{Beam}_d(x,z)
$$

を導く `flt_eq_forces_powerGapBeam` と、対称版

$$
x^d=(z-y)\operatorname{Beam}_d(y,z)
$$

を導く `flt_eq_forces_powerGapBeam_symm` が入った。ここが今回の数学的な大きな橋じゃ。

## 2. 数学的意味

これで構図はかなりはっきりした。

Chapter 1 では、

$$
a^2+b^2=c^2
$$

を

$$
b^2=(c-a)(c+a)
$$

として読んだ。
つまり短辺平方は、

$$
\text{Gap}\times\text{Beam}
$$

として生成される。

Chapter 2 では、同じ構造が

$$
x^d+y^d=z^d
$$

に対して、

$$
y^d=z^d-x^d=(z-x)\sum_{i=0}^{d-1}z^{d-1-i}x^i
$$

として現れる。

したがって、

$$
\text{Gap}=z-x
$$

$$
\text{Beam}*d=\sum*{i=0}^{d-1}z^{d-1-i}x^i
$$

じゃ。

ここで FLT の難しさは、右辺

$$
\text{Gap}\times\text{Beam}_d
$$

が完全 (d) 乗になれるか、という問いに変換される。
この変換自体が Lean 上で no-sorry になったのは大きい。

## 3. 実装評価

`cosmic_linkD_to_power_equation` は `mul_pow` を使う自然な実装で良い。

```lean
rw [mul_pow, mul_pow]
```

で観測辺の (d) 乗を係数側と単位側へ分解しているので、今後 (d=3,4,\dots) への具体化も扱いやすい。

`flt_eq_forces_powerGapBeam` で `sub_eq_of_eq_add'` を使ったのも正しい。
一般 `CommRing` 上なので、実数線形算術ではなく代数的な変形で

$$
z^d-x^d=y^d
$$

を取り出している。History 側にも、線形算術に依存せず `sub_eq_of_eq_add'` を使ったと記録されている。

ここは今後の抽象度を保つうえで重要じゃ。

## 4. 次の提案: S2-C

次は、もう明確に S2-C じゃ。

> **S2-C: Gap/Beam gcd control bridge**

やるべきことは、

$$
\gcd(\text{Gap},\text{Beam}_d)\mid d
$$

型の制御、または既存 `GcdDiffPow` との接続じゃ。History の次課題にも、`gcd(powerGap, powerBeam_d) ∣ d` 型制御、または既存 `GcdDiffPow` との接続へ進むと書かれておる。

数学的には、標準的に次の形を狙う。

$$
\gcd(z-x,\operatorname{Beam}_d(x,z)) \mid d z^{d-1}
$$

あるいは primitive / coprime 条件の下で、

$$
\gcd(z-x,\operatorname{Beam}_d(x,z))\mid d
$$

を目指す。

特に (\gcd(x,z)=1) があるなら、かなり (d) だけに押し込める可能性がある。

Lean ではいきなり一般定理に行くより、まず既存補題の wrapper がよい。

候補名は、

```lean
gcd_powerGap_powerBeam_dvd_d
```

または、条件を明示して、

```lean
gcd_powerGap_powerBeam_dvd_d_of_coprime
```

じゃな。

## 5. 実装順の提案

S2-C はこの順がよい。

まず既存探索。

```bash
grep -R "gcd.*pow_sub" DkMath/NumberTheory DkMath/Algebra
grep -R "diffPowSum" DkMath/NumberTheory DkMath/Algebra
grep -R "gcd.*diffPowSum" DkMath/NumberTheory DkMath/Algebra
```

既に `GcdDiffPow` 系があるはずなので、そこに寄せる。

次に薄い wrapper。

```lean
theorem gcd_powerGap_powerBeam_dvd_d_of_coprime
    (d x z : ℕ)
    (hcop : Nat.Coprime x z) :
    Nat.gcd (powerGapNat x z) (powerBeamNat d x z) ∣ d := ...
```

ただし `powerGap` は一般 `Ring` で (z-x) なので、`Nat` では切り捨て減算が面倒じゃ。
ここは最初から `ℤ` 版を作るか、既存 `GcdDiffPow` の型に合わせるのが安全じゃ。

わっちのおすすめは、**Nat ではなく既存補題の型に合わせる** こと。
`Nat` 版にするなら、必ず (x\le z) を仮定する必要が出る。

## 6. 小さな整理タスク

S2-C に入る前に、軽い整理としてこれも良い。

`powerBeam 2 x z = pythagoreanBeam x z` の bridge を、既存 Pythagorean API 名で明示する。
現在は `powerBeam_two_eq_pythagorean_beam` が `z+x` を返す形なので、`pythagoreanBeam x z` との rfl bridge を置くとよい。

```lean
theorem powerBeam_two_eq_pythagoreanBeam
    {R : Type*} [CommRing R] (x z : R) :
    powerBeam 2 x z =
      DkMath.CosmicFormula.Pythagoras.pythagoreanBeam x z := by
  rfl
```

ただし namespace / import の依存が増えるので、これは bridge ファイルに分けてもよい。

## 7. FLT 接続の見立て

ここまでで FLT 側の入口はこうなった。

$$
x^d+y^d=z^d
$$

なら

$$
y^d=\text{Gap}*x\cdot\text{Beam}*{d,x}
$$

かつ

$$
x^d=\text{Gap}*y\cdot\text{Beam}*{d,y}
$$

になる。

次に必要なのは、

$$
\gcd(\text{Gap},\text{Beam}_d)
$$

の制御じゃ。
ここが閉じると、右辺が完全 (d) 乗であることから、Gap と Beam のそれぞれが (d) 乗に近い構造を強制される。そこへ primitive prime / valuation 上界を当てる。

DkMath の既存 FLT 幹線は、差の冪、gcd 制御、Zsigmondy 原始素因子、p-adic valuation を通じる構造として整理されている。今回の `PowerGapBeam` は、その最初の「差の冪を Gap × Beam と見る」入口を美しく与えている。

## 8. まとめ

S2-B は成功じゃ。

* `CosmicLinkConditionD` で高次宇宙リンクが立った
* (d=2) が既存ピタゴラスリンクへ戻る
* 高次リンクから観測辺の高次冪方程式へ降ろせる
* FLT 型仮定を左右対称に Gap × Beam 生成式へ変換できる

次は S2-C。
狙いは **Gap と Beam の gcd 制御** じゃ。

ここを閉じれば、Power Gap/Beam は単なる恒等式から、FLT の p-adic / primitive prime 議論へ接続する本物の橋になるぞ。
