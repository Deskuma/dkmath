# review

おお、始めたか！これは **かなり良い第一歩** じゃ。
今回の diff は、Erdős #1196 ルートで不足していた **Hitting 層** を、きちんと finite combinatorial spine として切り出せておる。

## 1. 何が閉じたか

今回閉じた核心はこれじゃ。

$$
\text{primitive set}
\Rightarrow
\text{同一 divisibility chain を高々一度しか hit しない}
\Rightarrow
\text{hit mass} \le \text{source mass}
$$

Lean 側では、これが三段に分かれて実装されておる。

```text
ValuationFlow/Hitting.lean
PrimitiveSet/Basic.lean
PrimitiveSet/HittingBridge.lean
```

これは前回までの

$$
\text{Mass API}
\to
\text{Branch API}
\to
\text{ValuationFlow}
$$

の次に来る、まさに欠けていた中間層じゃ。

## 2. Phase A: finite hitting core

`ValuationFlow/Hitting.lean` では、

```lean
def hitSetMass
def sourceSetMass
structure MassControlledAssignment
theorem hitSetMass_le_sourceSetMass_of_injective_assignment
```

が追加されておる。

数学的には、

$$
H \hookrightarrow R
$$

という injective assignment があり、各 hit の質量が割り当て先 source の質量以下なら、

$$
\sum_{h\in H}\mu(h)
\le
\sum_{r\in R}\mu(r)
$$

が成り立つ、という有限補題じゃ。

これは非常に良い。
いきなり Markov kernel や無限測度に行かず、まず有限 `Finset` の質量比較として閉じている。まさに「登山道の足場」じゃな。

特に良いのは、`MassControlledAssignment` に

```lean
assign_mem
injective_on_hits
mass_le_assign
```

を持たせている点じゃ。これにより、後で source が root、hit が primitive set との交点になっても、そのまま差し替えられる。

## 3. Phase B: primitive set vocabulary

`PrimitiveSet/Basic.lean` の

```lean
def PrimitiveOn (S : Finset ℕ) : Prop :=
  ∀ ⦃a b : ℕ⦄, a ∈ S → b ∈ S → a ∣ b → a = b
```

これはよい定義じゃ。

Erdős #1196 の primitive set 条件は、本質的に divisibility poset 上の antichain なので、有限版ではこの形が最短で強い。

さらに、

```lean
PrimitiveOn.eq_of_dvd
PrimitiveOn.not_dvd_of_ne
PrimitiveOn.dvd_iff_eq
primitiveOn_empty
primitiveOn_singleton
primitiveOn_pair
primitiveOn_pair_two_three
```

まで揃えているので、以後の証明で使いやすい。

注意点として、`0` を定義から除外していないのも妥当じゃ。
これはコメントにも書かれている通り、自然数上では \(a > 0\) なら \(a\mid 0\) なので、正の元と \(0\) が同居すれば primitive 性が壊れる。つまり、`0` 問題は定義で無理に消さず、必要な場面で `0 ∉ S` や `∀ a∈S, 0 < a` を足す方が柔軟じゃ。

## 4. Phase C: primitive hitting bridge

ここが今回の一番おいしい実装じゃ。

```lean
def DivisibilityChain (C : Finset ℕ) : Prop :=
  ∀ ⦃a b : ℕ⦄, a ∈ C → b ∈ C → a ∣ b ∨ b ∣ a
```

これは「下降鎖」を graph reachability で表すのではなく、まず **全点が割り切り比較可能** という有限 chain として固定している。

この判断は正しい。
Erdős #1196 の核心に必要なのは、まず

$$
a,b\in C
\Rightarrow
a\mid b ;\text{or}; b\mid a
$$

であり、実際にどの edge を辿ったかではないからじゃ。

そして主定理：

```lean
theorem primitiveOn_inter_chain_card_le_one
    {S C : Finset ℕ} (hS : PrimitiveOn S) (hC : DivisibilityChain C) :
    (S ∩ C).card ≤ 1
```

これは完全に核心を射抜いておる。

数学的には、

$$
S\text{ primitive},\quad C\text{ chain}
\Rightarrow
|S\cap C|\le 1
$$

じゃ。

これこそ、Erdős #1196 の

> primitive set は一本の下降鎖に高々一回しか当たらない

の有限版じゃな。

さらに、

```lean
primitive_chain_hitSetMass_le_single_source
```

で Hitting 側へ接続したのも良い。

$$
S\cap C
$$

の hit を singleton source \(\{r\}\) に割り当てて、

$$
\mathrm{hitSetMass}(S\cap C)
\le
\mathrm{sourceSetMass}({r})
$$

へ落としている。

ここまで来ると、前回まで抽象だった

$$
\text{non-overlapping hit mass bound}
$$

が、primitive set の語彙と接続されたことになる。

## 5. 今回の実装の意味

これは **Erdős #1196 本体の有限骨格** じゃ。

まだ

$$
\frac{1}{n\log n}
$$

も、

$$
\frac{\Lambda(q)}{\log n}
$$

も、

$$
1+O!\left(\frac1{\log x}\right)
$$

も出ていない。

しかし、そこへ行く前に必要な純粋 combinatorial core、

$$
\text{primitive}
\Rightarrow
\text{chain hit at most once}
\Rightarrow
\text{mass bound}
$$

が Lean 上で no-sorry になった。
これは大きい。

山で言えば、前回は「質量保存のベースキャンプ」を作った。
今回はそこから **primitive hitting の第一尾根** に取りついたところじゃ。

## 6. 宇宙式ルートとしての見え方

宇宙式視点では、今回の定理はこう読める。

$$
\mathrm{Big}
\to
\mathrm{Body}
\to
\mathrm{Beam}
\to
GN
\to
\text{prime / divisor chain}
$$

という下降流があるとして、primitive set はその流れ上に複数回は現れない。

つまり、

$$
\text{宇宙式の皮剥き流}
$$

に対して、

$$
\text{primitive set は非重複な観測点集合}
$$

になる。

今回の `DivisibilityChain` は、この「皮剥き流」をまだ抽象的に

$$
a\mid b \;\text{or}\; b\mid a
$$

で見ている段階じゃ。
だが、それでよい。最初から実際の flow graph を定義すると重くなるからの。

## 7. 注意点と次の分岐

次に悩むべき分岐はこれじゃ。

### 7.1. Chain を複数にする

今は singleton source への hitting bound じゃ。

次は、おそらく

$$
{C_i}_{i\in I}
$$

のような chain family / forest が欲しくなる。

目標は、

$$
\sum_i \mathrm{hitMass}(S\cap C_i)
\le
\sum_i \mathrm{sourceMass}(r_i)
$$

じゃな。

Lean 的には、

```lean
ChainFamily
ForestHitting
hitMass_le_sourceMass_of_chainFamily
```

のような方向。

### 7.2. DivisibilityChain を actual descent relation へ拡張する

今の `DivisibilityChain` は「比較可能性」だけ。

次は、

```lean
DescentStep a b := b ∣ a ∧ b < a
```

あるいは

```lean
PrimeStep n m := ∃ p, Nat.Prime p ∧ m = n / p
```

のような実際の下降関係を入れたくなる。

ただし、これは次の次でもよい。
今は比較可能 chain で十分に強い。

### 7.3. `0` と positivity の扱い

Erdős #1196 本体では \(a > x\) なので、最終的には全部正。
したがって、どこかで

```lean
PositiveOn S := ∀ a ∈ S, 0 < a
```

または

```lean
S ⊆ Finset.Icc 1 N
```

のような補助が欲しくなる。

ただ、今回の finite antichain core では未導入でよい。これは正しい温存じゃ。

## 8. 次の一手

わっちなら次はこの順じゃ。

### Step 1. `PrimitiveSet/HittingBridge` に multi-chain 版を足す

まず finite family でよい。

```lean
structure DivisibilityChainFamily where
  index : Type
  chains : Finset ℕ → ...
```

まで一般化しすぎず、最初は `Finset ι` と `C : ι → Finset ℕ` でよい。

欲しい補題は、

$$
\forall i,\; |S\cap C_i|\le 1
$$

を束ねるもの。

### Step 2. `MassControlledAssignment` の chain family 用 wrapper

今ある定理はすでに強いので、次は wrapper だけで行ける。

```lean
primitive_chainFamily_hitSetMass_le_sourceSetMass
```

のような theorem を作る。

### Step 3. `DescentChain` を別名で導入

`DivisibilityChain` は poset 的。
Erdős #1196 向けには、名前として

```lean
DescentChain
```

を置くとよい。

ただし定義は最初、

```lean
abbrev DescentChain := DivisibilityChain
```

でも十分じゃ。
後で実際の step relation へ差し替えられる。

## 9. 総合評価

今回の実装は、 **正しい場所を正しい粒度で切っている** 。

特に良い点は三つ。

1. exact Markov に飛びつかず、finite mass lemma から入った
2. primitive set を有限 divisibility antichain として分離した
3. primitive と chain の交差高々一点を Hitting mass bound へ接続した

これは DkMath の別ルートとしてかなり良い。

わっちの判定では、

$$
\text{Erdős \#1196 宇宙式ルート}
$$

の進捗は、今回で

$$
\text{Mass / Branch 基盤}
\quad\to\quad
\text{Primitive finite hitting}
$$

まで進んだ。

次に multi-chain / forest へ行けば、いよいよ

$$
\text{ランダムな下降鎖族}
$$

の有限近似が見えてくる。
そこまで行くと、\(\mu(n)\approx 1/(n\log n)\) を載せる準備が整うぞい。
