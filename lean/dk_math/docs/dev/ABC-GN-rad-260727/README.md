# README - ABC-STG

## 解説

## ABC-STG-001

うむ……これは本当に、**部品は全部あったのに、最短の橋だけ誰も架けていなかった** という話じゃ。

最新 snapshot には既に、

* `Triple.hsum : a + b = c`
* `Triple.hcop : Nat.Coprime a b`
* `sqTail c := c / rad c`
* `nat_eq_sqTail_mul_rad : c = sqTail c * rad c`
* `rad_mul_coprime'`

がある。

それなのに、

$$
c\operatorname{rad}(ab)=\operatorname{sqTail}(c)\operatorname{rad}(abc)
$$

という **ABC 本体の完全相殺式** が存在しない。検索しても見つからなかった。

これは最優先で固定すべきじゃ。

### 1. 最小 checkpoint

新規ファイル案：

```text
DkMath/ABC/SquareTailGapIdentity.lean
```

まず解析も対数も除算も入れず、`Nat` の完全等式だけを閉じる。

中心定理はこれだけじゃ。

$$
c\operatorname{rad}(ab)=\operatorname{sqTail}(c)\operatorname{rad}(abc)
$$

除算を一切使わず、自然数上で正確に閉じる。

### 2. この定理が固定するもの

この等式を分数として読めば、

$$
\frac{c}{\operatorname{rad}(abc)}=\frac{\operatorname{sqTail}(c)}{\operatorname{rad}(ab)}
$$

じゃ。

左辺は従来の ABC quality 超過核。

右辺は、

* 分子：出力 (c) に蓄積した重複素因子層
* 分母：入力 (a,b) が供給した異なる素数の支持

という直接会計になっている。

したがって、新しい量を作ったのではない。

> **ABC で既に測っていた比率の正体を、整数の完全等式として展開した。**

という theorem じゃ。

### 3. 次 checkpoint

次に、上の自然数定理だけを使って実数版を追加する。

```lean
theorem Triple.c_div_rad_abc_eq_sqTail_div_rad_ab
    (T : Triple)
    (hc : T.c ≠ 0) :
    (T.c : ℝ) / (rad (T.a * T.b * T.c) : ℝ) =
      (sqTail T.c : ℝ) / (rad (T.a * T.b) : ℝ)
```

その後に対数版。

```lean
theorem Triple.log_abcGap_eq_log_sqTail_sub_log_rad_ab
    (T : Triple)
    (ha : 0 < T.a)
    (hb : 0 < T.b) :
    Real.log (T.c : ℝ) -
        Real.log (rad (T.a * T.b * T.c) : ℝ) =
      Real.log (sqTail T.c : ℝ) -
        Real.log (rad (T.a * T.b) : ℝ)
```

これで ABC Gap を正式に定義できる。

```lean
noncomputable def Triple.abcGap (T : Triple) : ℝ :=
  Real.log (T.c : ℝ) -
    Real.log (rad (T.a * T.b * T.c) : ℝ)
```

そして別座標定理を置く。

```lean
theorem Triple.abcGap_eq_squareTailDebt
    (T : Triple)
    (ha : 0 < T.a)
    (hb : 0 < T.b) :
    T.abcGap =
      Real.log (sqTail T.c : ℝ) -
        Real.log (rad (T.a * T.b) : ℝ)
```

### 4. GN は別の層に隔離する

ぬしの全連鎖について、一点だけ型を分ける必要がある。

一般の ABC triple では、必ずしも (c) が (d) 乗ではない。

したがって普遍層は、

$$
a+b=c=\operatorname{sqTail}(c)\operatorname{rad}(c)
$$

ここまで。

宇宙式層は、追加 witness を持つ特殊な場合として、

$$
c=(x+u)^d=x\,GN_d(x,u)+u^d
$$

とする。

Lean では混ぜずに、後から次の pack を置くのが正しい。

```lean
structure Triple.CosmicPowerWitness (T : Triple) where
  d : ℕ
  x : ℕ
  u : ℕ
  hc : T.c = (x + u) ^ d
```

そして witness がある場合だけ宇宙式へ接続する。

### 5. 今回の発見の位置

率直に言えば、これまでのわっちらは、

```text
c の sqTail
GN の valuation excess
lift radical
joint pressure
```

を個別には見ておった。

しかし、

```text
c / rad(abc)
```

から共通の `rad(c)` を消去し、

```text
sqTail(c) / rad(ab)
```

へ戻す最短操作を、本丸の theorem として見ていなかった。

難しい定理が不足していたのではない。

**既存の二つの完全分解を同じ一行に置いていなかった。**

まず `ABC-STG-001` として、この自然数の完全等式だけを固定する。これは小さいが、ABC 全体の主語を GN から (a+b=c) へ戻す、かなり重要な checkpoint じゃ。
