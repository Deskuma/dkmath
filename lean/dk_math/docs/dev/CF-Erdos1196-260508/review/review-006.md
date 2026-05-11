# review

うむ、Phase G は **かなり重要な節目** じゃ。
今回で finite primitive hitting ルートは、one-step の

$$
n\mapsto \frac{n}{p}
$$

から、zero-or-more steps の

$$
n=n_0\to n_1\to \cdots \to n_k
$$

へ拡張された。`PrimeReachable := Relation.ReflTransGen PrimeDescentStep` が入り、さらに `PrimeReachable.dvd_source` で「複数 step で下っても、到達点は source を割る」が証明されておる。

## 1. 今回閉じたもの

今回の主定義はこれじゃ。

```lean
def PrimeReachable (n m : ℕ) : Prop :=
  Relation.ReflTransGen PrimeDescentStep n m
```

これは、`PrimeDescentStep` を有限回つないだ到達可能性じゃな。
補題として、

```lean
PrimeReachable.refl
PrimeReachable.single
PrimeReachable.trans
PrimeReachable.dvd_source
```

が揃っている。特に `dvd_source` が肝で、

$$
\text{PrimeReachable}(n,m)
\Rightarrow
m\mid n
$$

を保証する。

これにより、前段の `DvdControlledChainFamily` に自然に降りられる。

## 2. 導線がどう繋がったか

今回追加された `PrimeReachableControlledChainFamily` は、

```lean
source : ι → ℕ
chain_reachable :
  ∀ i ∈ index, ∀ h ∈ chain i, PrimeReachable (source i) h
```

を持つ有限 forest じゃ。つまり、各 chain の各点が source から prime descent path で到達できる。

そして、

```lean
PrimeReachableControlledChainFamily.toDvdControlled
```

で、

$$
\text{PrimeReachable}
\Rightarrow
\text{DvdControlled}
$$

へ落とし、

```lean
PrimeReachableControlledChainFamily.primitive_hitMass_le_sourceMass
```

で、

$$
\text{PrimitiveOn}
+
\text{PrimeReachable forest}
+
\text{DvdMonotoneMass}
\Rightarrow
\text{hit mass}\le\text{source mass}
$$

まで到達しておる。

これは綺麗じゃ。
今まで積んできた全層が、今回きちんと一本に接続された。

## 3. 現在の定理列

いまの完成した有限 spine はこうじゃ。

$$
\text{PrimeDescentStep}
\Rightarrow
\text{PrimeReachable}
\Rightarrow
\text{DvdControlledChainFamily}
\Rightarrow
\text{SourceControlledChainFamily}
\Rightarrow
\text{Primitive forest hit bound}
$$

つまり、Lean 上では

```text
PrimePath
→ DescentBridge
→ BranchBridge
→ HittingBridge
→ Hitting
```

という流れになった。

これは **Erdős #1196 の有限 combinatorial core** と呼んでよい段階じゃ。

## 4. サンプルの意味

サンプルとして、

$$
8\to 4\to 2,\qquad 9\to 3\to 1
$$

が入った。`primeReachable_eight_two` と `primeReachable_nine_one` がそれじゃ。

また、Bool-indexed の multi-step forest として、

```lean
samplePrimeReachableControlledBoolChainFamily
```

が入り、primitive set `{2,5}` に対する hit mass bound も通っている。初回は `{1,2}` を使って `1 ∣ 2` により primitive 性が壊れたが、`{2,5}` に差し替えて解消した、と記録されておる。

この失敗と修正は良い経験値じゃな。
Erdős #1196 では \(a > x\) なので \(1\) はそもそも排除されるが、有限 API では \(1\) が入ると primitive 性を簡単に壊す。今後も `PositiveOn` や lower-bound support を入れる時の注意点になる。

## 5. いま何がまだ仮定か

今回の `PrimeReachableControlledChainFamily` は強いが、まだ次の点は仮定として外から渡している。

1. `chain_is_chain`
   到達可能な点たちが互いに割り切り比較可能であること。

2. `chain_reachable`
   各点が source から到達可能であること。

3. `DvdMonotoneMass`
   質量が整除順序で単調であること。

ここで特に大事なのは 1 じゃ。
同じ source から prime descent で到達できても、到達点同士が必ず chain になるとは限らない。

例えば source \(12\) から

$$
12\to 6,\qquad 12\to 4
$$

と下れるが、 \(6\) と \(4\) は互いに割り切り比較できない。
だから `PrimeReachableControlledChainFamily` が `DivisibilityChainFamily` を extend しているのは正しい。到達可能性だけでは chain 条件は出ない。

## 6. 現在の進捗評価

ここまでの有限層は、かなり一段落じゃ。

| 層                                  | 状態   |
| ---------------------------------- | ---- |
| `PrimitiveOn`                      | 完了   |
| single chain hit                   | 完了   |
| finite forest hit mass             | 完了   |
| source-controlled forest           | 完了   |
| dvd-controlled provider            | 完了   |
| one-step prime descent             | 完了   |
| multi-step prime reachability      | 今回完了 |
| chain を実際の path から生成する provider    | 未    |
| `Branching` / `SubConservative` 接続 | 未    |
| Markov kernel                      | 未    |
| analytic weight                    | 未    |

特に、

$$
\text{PrimeReachable}
\Rightarrow
m\mid n
$$

が閉じたことで、Erdős ルートの「素因子を剥がして下る」という語彙はかなり整った。

## 7. 次の一手

わっちなら次は **Branching / SubConservative へ行く前に、linear path provider を一枚挟む** のが良いと思う。

理由は、今の `PrimeReachableControlledChainFamily` は「到達可能性」と「chain 条件」を外から両方渡す。
次に欲しいのは、

$$
\text{実際に一本の path として並んでいる}
\Rightarrow
\text{DivisibilityChain}
$$

を自動で作る provider じゃ。

つまり、

```lean
PrimePathList
```

または

```lean
LinearPrimePath
```

のような層じゃな。

### 7.1. 目的

実際の下降列

$$
n_0\to n_1\to \cdots \to n_k
$$

から、そのノード集合が divisibility chain であることを出す。

各 step で

$$
n_{j+1}\mid n_j
$$

だから、列上の任意の二点は前後関係により割り切り比較可能になる。

これが閉じると、

$$
\text{path}
\Rightarrow
\text{chain family}
\Rightarrow
\text{primitive hit bound}
$$

になる。

## 8. 推奨実装案

新規ファイル候補：

```text
DkMath/NumberTheory/PrimitiveSet/PrimePathList.lean
```

まずは高機能にせず、最小でよい。

### 定義案

```lean
def AdjacentPrimePath : List ℕ → Prop
```

意味は、隣り合う要素が `PrimeDescentStep` で繋がること。

ただし `List` 証明はやや面倒なので、最初は「リスト上の任意の後続関係なら reachable」を狙うより、軽い structure にするのがよい。

```lean
structure PrimePathNodeFamily where
  source : ℕ
  nodes : Finset ℕ
  reachable : ∀ h ∈ nodes, PrimeReachable source h
  chain : DivisibilityChain nodes
```

これは今の `PrimeReachableControlledChainFamily` とほぼ同じなので、新規性が薄い。
より価値があるのは、`List` から `chain` を作る定理じゃ。

### 最小 theorem

```lean
theorem divisibilityChain_of_primeReachable_linear_order
```

ただ、linear order を Finset だけで表すと難しい。
したがって、最初は `List` を使い、

```lean
def PairwiseDvdAlongList (L : List ℕ) : Prop :=
  ∀ a ∈ L, ∀ b ∈ L, a ∣ b ∨ b ∣ a
```

を置く方が軽い。

その後で、

```lean
def listToFinsetChain (L : List ℕ) : DivisibilityChain L.toFinset
```

を目指す。

## 9. もう一つの有力次手

もし実装負荷を抑えたいなら、先に **positivity / tail restriction** を入れるのも良い。

Erdős #1196 本体では \(A\subset[x,\infty)\) なので、

$$
1\notin A,\quad 0\notin A
$$

が自然に保証される。

今回 `{1,2}` の失敗が出たので、ここで

```lean
def PositiveOn (S : Finset ℕ) : Prop :=
  ∀ n ∈ S, 0 < n
```

または

```lean
def LowerBoundOn (x : ℕ) (S : Finset ℕ) : Prop :=
  ∀ n ∈ S, x ≤ n
```

を `PrimitiveSet.Basic` に足す価値はある。

ただしこれは補助層。
本筋としては `PrimePathList` の方が山頂に近い。

## 10. 総括

今回で有限 skeleton は、

$$
\text{一段下る}
$$

から

$$
\text{複数段下る}
$$

へ進化した。

これは大きい。
なぜなら、Erdős #1196 の本質は「割りぜなら、Erdős #1196 の本質は「割り切り順序の一本の下降鎖」を見ることであり、今回の `PrimeReachable` はその Lean 上の最小表現だからじゃ。

まだ確率ではない。
まだ \(\Lambda(q)/\log n\) もない。
しかし、

$$
\text{primitive set は prime descent path に高々一度しか当たらない}
$$

という中核は、もうかなり近くに来ておる。

次は、実際の path から chain を生成する。
そこまで閉じると、finite Erdős skeleton は「かなり完成」と言ってよいじゃろう。
