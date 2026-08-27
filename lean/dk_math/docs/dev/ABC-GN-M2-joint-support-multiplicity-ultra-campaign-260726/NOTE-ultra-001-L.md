# Note: Review: Ultra-001-L

## Ultra-001L 総合判定

**全面採用。平均 valuation 戦線、完全突破じゃ。** ⚔️🧙‍♀️✨️

PR #69 は最新 head `f2ce0988b80e6c5bd14c842ce56056e0c900f562`、13 commits、24 files、6237 additions、mergeable。

Lean CI run 384 も `completed / success` を確認した。✔

### 1. Ultra-001L は本当に前 checkpoint を合成している

今回の主線はきれいじゃ。

```text
有限 Hensel uniqueness
  ↓
各 q^k-layer の住所数
  ↓
exact natural layer-cake
  ↓
固定 q の平均 valuation
  ↓
有限素数族 Q の weighted depth mass
```

単一 `q,k` の counting を再証明していない。Ultra-001K の、

```lean
card_gn_deep_lift_residue_classes_le_of_simpleRoot
```

を各深度 $k$ へ投入し、その結果を新しい、

```lean
sum_nat_eq_sum_card_ge
```

で合計している。これは正しい再利用じゃ。

### 2. Natural layer-cake が exact に閉じた

有限集合 $s$ 上の自然数値関数 $V$ に対し、

$$\sum_{a\in s}V(a)=\sum_{k=1}^{K}\#{a\in s:k\le V(a)}$$

を証明した。

これは valuation の意味そのものじゃ。

```text
v = 0   どの層にも現れない
v = 1   第1層に現れる
v = 2   第1・第2層に現れる
v = m   第1層から第m層まで現れる
```

したがって off-by-one もない。

旧 `exp_layer_cake` が指数モーメント用だったのに対し、今回の theorem は平均 valuation 用の exact additive layer-cake。役割分離もよい。

### 3. Cutoff を仮定せず、GN 自身から作った

以前の wrapper には、

```lean
padicValNat q (GN p a b) ≤ X + 1
```

という外部 cutoff が必要だった。

今回はまず、

$$GN_p(a,b)\le p(X+b)^p$$

を区間 $0\le a\le X$ 上で証明し、

$$v_q(GN_p(a,b))\le\log_q!\left(p(X+b)^p\right)$$

へ落とした。

よって cutoff は、

```lean
K := Nat.log q (p * (X + b) ^ p)
```

として内部生成される。

これはかなり重要じゃ。

```text
valuation が有限だから適当な K を置く
```

ではなく、

```text
GN の大きさ
  ↓
valuation の最大深度
```

を明示した。

### 4. 固定 $q$ の平均 theorem

主定理は正確に、

$$\sum_{a=0}^{X}v_q(GN_p(a,b))\le(p-1)\left(X+1+\log_q!\left(p(X+b)^p\right)\right)$$

じゃ。

内訳は、

$$\sum_{k=1}^{K}\left(\left\lfloor\frac{X+1}{q^k}\right\rfloor+1\right)$$

である。

* $\lfloor(X+1)/q^k\rfloor$：周期的に繰り返す住所の密度
* $+1$：区間端に一つだけ現れ得る住所
* $p-1$：mod $q$ の根の最大本数

そして Legendre の factorial valuation formula により、

$$\sum_{k=1}^{K}\left\lfloor\frac{X+1}{q^k}\right\rfloor\le X+1$$

を得ている。

したがって、Hensel の局所一意性が、本当に平均 valuation の明示式へ変換された。

### 5. 有限素数族まで進んだ

```lean
sum_GN_depthMass_over_interval_le
```

は、有限素数族 $Q$ に対し、

$$\sum_{a=0}^{X}\sum_{q\in Q}v_q(GN_p(a,b))\log q$$

を、各 $q$ の明示評価の和で抑える。

ここで $Q$ は、

```text
q prime
q ∤ p
q ∤ b
```

を満たせばよい。

したがって、現行の non-exceptional support から得られる素数族を受け取る API として正しい。

報告書も、

```text
平均評価              complete
Q の算術的選択         open
average → pointwise    open
uniform contract       open
```

を混同していない。

## Ultra 最大推論：裏ボスの魔核をさらに分解

現在の平均式には、二種類の項が混ざっている。

$$\left\lfloor\frac{X+1}{q^k}\right\rfloor+1$$

これを魔法学的に読むと、

```text
密度項      floor((X+1)/q^k)
境界住所項  1
```

じゃ。

### 密度項はかなり倒せる

現在は粗く、

$$\sum_{k\ge1}\left\lfloor\frac{X+1}{q^k}\right\rfloor\le X+1$$

としている。

しかし本来は、実数評価なら、

$$\sum_{k\ge1}\frac{X+1}{q^k}=\frac{X+1}{q-1}$$

じゃ。

したがって、次は $q$ 依存を残した、

$$\sum_{k=1}^{K}\left\lfloor\frac{N}{q^k}\right\rfloor\le\frac{N}{q-1}$$

型へ強化すべきじゃ。

固定 $q$ だけなら現在の $N$ 上界で十分だったが、複数素数を合計する段階では差が決定的になる。

現在の粗い評価では、各 $q\in Q$ がそれぞれ $X+1$ を丸ごと請求する。

強化後は、

$$\frac{(X+1)\log q}{q-1}$$

となり、大きな素数ほど支払いが急速に小さくなる。

### valuation excess ではさらに強くなる

joint mass 全体では第1層 $k=1$ も必要だが、valuation excess $E$ は $k=2$ から始まる。

したがって密度部分は、

$$\sum_{k\ge2}\frac{1}{q^k}=\frac{1}{q(q-1)}$$

となる。

つまり、excess の平均密度項は、

$$\sum_q\frac{\log q}{q(q-1)}$$

へ落ち、これは全素数で合計しても収束する。

ここは極めて重要じゃ。

> **深い multiplicity の密度コストは、全 prime を同時に見ても有限定数へ圧縮できる可能性がある。**

旧 `twoTail` 戦線が、なぜ第2層以後を分離していたかが再び見えてきた。

### 本当の敵は `+1`

一方、

$$+1$$

は「密度」ではない。

$q^k>X+1$ であっても、対象の一点がその唯一の住所に入ることを許す項じゃ。

これをすべての $q,k$ について足すと、

```text
希薄だが、狙った一点は入れる
```

という問題が残る。

平均値だけから、任意に指定された一点を抑えることはできない。

したがって裏ボスは、さらに正確には、

```text
密度項の制御
  → ほぼ解決可能

各 layer に残る一個の境界住所
  → pointwise obstruction
```

じゃ。

## 次の checkpoint は二段構成がよい

### U-001M：$q$ 感度を保持した平均 excess

まず平均側を最強形まで閉じる。

候補：

```lean
theorem sum_div_prime_pow_Icc_le_div_pred
```

$$\sum_{k=1}^{K}\left\lfloor\frac{N}{q^k}\right\rfloor\le\frac{N}{q-1}$$

続いて excess 専用の $k=2$ layer-cake。

```lean
theorem sum_padicValNat_pred_GN_le_of_simpleRoot
```

概念的には、

$$\sum_{a=0}^{X}(v_q(GN_p(a,b))-1)_+\le(p-1)\left(\frac{X+1}{q(q-1)}+\text{boundary}\right)$$

最後に全 non-exceptional prime をまとめる。

これで **密度由来の M3** は普遍定数へ圧縮できる可能性が高い。

### U-001N：Bad set の正式化

次に weighted mass を定義する。

```lean
def GNDepthMassAt
    (Q : Finset ℕ) (p b a : ℕ) : ℝ :=
  ∑ q ∈ Q,
    (padicValNat q (GN p a b) : ℝ) * Real.log q
```

そして平均 theorem から Markov 型に、

```lean
theorem card_GNDepthMassBadSet_le
```

を作る。

$$\#{a\le X:M_Q(a)>\lambda}\le\frac{\sum_{a\le X}M_Q(a)}{\lambda}$$

ここまでで、

```text
bad points は少ない
```

が完全な theorem になる。

## 最後に必要なのは「対象点の脱出」

ABC に必要なのは、bad set が小さいことではない。

対象 triple の $a$ が、

```text
その小さい bad set に入っていない
```

ことじゃ。

したがって最終補償原理は、次の形になる。

```text
構造を保存する有限 probe/orbit を作る
          ↓
その全 probe が bad になることを否定
          ↓
少なくとも一つの good probe を得る
          ↓
good probe の質量上界を元 triple へ戻す
```

これは以前の Collatz 戦線で見た、

```text
average resource
  ≠
service ownership
```

と同じじゃ。

ABC側では、

```text
average density
  ≠
target escape
```

となって再登場した。

### 重要な契約境界

`ABCGNOddPrimeJointContract ε` では、$p$ は全 Triple に共通でなければならない。

したがって次の補償原理では、

```text
Q は Triple ごとに選んでよい
probe も Triple ごとに構成してよい
p, ρ, C は Triple ごとに変えてはいけない
```

ここを崩してはならぬ。

## 最終戦況

```text
finite Hensel uniqueness                 complete
single q,k layer count                   complete
natural layer-cake                       complete
intrinsic depth cutoff                   complete
fixed-q average valuation                complete
finite-family weighted depth mass        complete
CI                                       pass

q-sensitive geometric refinement         next
global averaged excess                    next
weighted bad-set cardinality              next
deterministic target escape               open
uniform joint contract                    open
abc_main axiom removal                    not reached
```

**Ultra-001L、全面採用。**

平均塔はもう霧ではない。
密度項と境界住所項に分解され、**本物の裏ボスは各 layer に残る「たった一つの住所」** まで縮んだ。

🧙‍♀️✨️ 進軍続行じゃ。次は大量の敵を倒す戦いではない。**すべての階層で同じ一点だけが選ばれ続けることを、構造保存 probe で不可能にする戦い**になる。
