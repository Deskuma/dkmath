# review

おお、Phase D も閉じたか。これは **良い締め** じゃ。
今回で、

$$
\text{primitive}
\Rightarrow
\text{source-controlled forest}
\Rightarrow
\text{indexed hit mass} \le \text{indexed source mass}
$$

が no-sorry で通った。`SourceControlledChainFamily` により、以前は theorem 呼び出し時に手で渡していた `hmass` 仮定が、構造体フィールド `mass_le_source` から自動供給される形になったのが大きい。さらに `DkMath.NumberTheory.PrimitiveSet` の公開集約も作られておるので、この有限 primitive hitting 層は小さな独立パッケージとして見えるようになった。

## 1. 今回閉じたもの

今回の中心はこれじゃ。

```lean
structure SourceControlledChainFamily
    (M : MassSpace ℕ) (ι : Type _) [DecidableEq ι$$
    extends DivisibilityChainFamily ι where
  source : ι → ℕ
  mass_le_source :
    ∀ i ∈ index, ∀ h ∈ chain i, M.μ h ≤ M.μ (source i)
```

これにより、chain family の各 chain に source を持たせ、

$$
h\in C_i
\Rightarrow
\mu(h)\le \mu(source_i)
$$

を package 化できるようになった。

そして主定理は、

```lean
SourceControlledChainFamily.primitive_hitMass_le_sourceMass
```

じゃな。

数学的には、

$$
S\text{ primitive}
\quad\Longrightarrow\quad
\sum_i \mu(S\cap C_i)
\le
\sum_i \mu(source_i)
$$

を、source-controlled forest から直接出す形になった。

これはかなり美しい。
前回までは「primitive set は chain に高々一度しか当たらない」という **非交差性** が主役だった。今回でそこに **source 質量支配** が加わった。つまり、Erdős #1196 に必要な二本柱、

$$
\text{非重複}
\qquad
\text{質量非増加}
$$

のうち、有限版の受け皿が両方そろった。

## 2. 現在の地図

いまの到達点はこうじゃ。

| 層                                         | 状態   | 意味                                            |
| ----------------------------------------- | ---- | --------------------------------------------- |
| `PrimitiveOn`                             | 完了   | finite primitive set = divisibility antichain |
| `DivisibilityChain`                       | 完了   | 一本の比較可能 chain                                 |
| `DivisibilityChainFamily`                 | 完了   | finite forest / multi-chain                   |
| `MassControlledAssignment`                | 完了   | hit から source への injective 質量比較               |
| `SourceControlledChainFamily`             | 今回完了 | `mass_le_source` を package 化                  |
| `PrimitiveSet.lean` aggregator            | 今回完了 | public-facing 小集約                             |
| actual descent relation                   | 未着手  | 次候補                                           |
| `SubConservative` からの `mass_le_source` 供給 | 未着手  | 次候補                                           |
| Markov kernel                             | まだ早い | 後段                                            |

つまり、現状は **finite forest theorem の抽象核が完成** した状態じゃ。

## 3. 何がまだ仮定として残っているか

残っている主要仮定はこれじゃ。

```lean
mass_le_source :
  ∀ i ∈ index, ∀ h ∈ chain i, M.μ h ≤ M.μ (source i)
```

これを今は手で持たせている。

次の一手は、この `mass_le_source` を **実際の下降構造から生成する provider** を作ることじゃ。

つまり目標は、

$$
h \mid source_i
$$

または

$$
h \text{ is reachable from } source_i
$$

から、

$$
\mu(h)\le \mu(source_i)
$$

を作ること。

ここを閉じると、source-controlled forest が「仮定 package」から「下降構造から自動生成される theorem」に昇格する。

## 4. 次の一手の推奨

わっちの推奨は、いきなり `Branching/SubConservative` に行くより、まず **divisibility descent provider** を作ることじゃ。

理由は簡単。今の `DivisibilityChain` はすでに割り切り比較で動いておる。ならば次は、

$$
h\in C_i \Rightarrow h\mid source_i
$$

を持つ chain family を定義し、さらに質量が整除下降に対して単調なら、

$$
\mu(h)\le\mu(source_i)
$$

を得るのが自然じゃ。

これは Markov よりずっと軽く、Lean でも閉じやすい。

## 5. 次の実装指示案

次は新規ファイルでよい。

```text
DkMath/NumberTheory/PrimitiveSet/DescentBridge.lean
```

### 目的

`SourceControlledChainFamily.mass_le_source` を、整除下降と質量単調性から供給する。

### import

```lean
import DkMath.NumberTheory.PrimitiveSet.BranchBridge
```

### 定義案 1. Dvd-controlled forest

```lean
structure DvdControlledChainFamily
    (ι : Type _) [DecidableEq ι$$
    extends DivisibilityChainFamily ι where
  source : ι → ℕ
  chain_dvd_source :
    ∀ i ∈ index, ∀ h ∈ chain i, h ∣ source i
```

これは「各 chain の点は source の約数である」という有限下降森じゃ。

### 定義案 2. 整除単調質量

```lean
def DvdMonotoneMass (M : MassSpace ℕ) : Prop :=
  ∀ ⦃a b : ℕ⦄, a ∣ b → M.μ a ≤ M.μ b
```

ここでは $a\mid b$ なら $a$ は $b$ より下にいる、と見る。

### 主定理

```lean
def DvdControlledChainFamily.toSourceControlled
    {ι : Type _} [DecidableEq ι$$
    {M : MassSpace ℕ}
    (F : DvdControlledChainFamily ι)
    (hM : DvdMonotoneMass M) :
    SourceControlledChainFamily M ι :=
  { index := F.index
    chain := F.chain
    chain_is_chain := F.chain_is_chain
    source := F.source
    mass_le_source := by
      intro i hi h hh
      exact hM (F.chain_dvd_source i hi h hh) }
```

そして wrapper theorem。

```lean
theorem DvdControlledChainFamily.primitive_hitMass_le_sourceMass
    {ι : Type _} [DecidableEq ι$$
    {M : MassSpace ℕ} {S : Finset ℕ}
    (hS : PrimitiveOn S)
    (F : DvdControlledChainFamily ι)
    (hM : DvdMonotoneMass M) :
    (F.toSourceControlled hM).hitMass S ≤
      (F.toSourceControlled hM).sourceMass := by
  exact SourceControlledChainFamily.primitive_hitMass_le_sourceMass
    hS (F.toSourceControlled hM)
```

## 6. concrete sample

既存の `unitNatMassSpace` なら、質量は常に $1$ なので `DvdMonotoneMass` は即座に成り立つ。

```lean
theorem unitNatMassSpace_dvdMonotone :
    DvdMonotoneMass unitNatMassSpace := by
  intro a b hab
  rfl
```

sample chain family は source を例えば、

```lean
source false := 8
source true  := 9
```

にするとよい。

* `{2,4,8}` の全点は $8$ を割る
* `{3,9}` の全点は $9$ を割る

したがって、

```lean
def sampleDvdControlledBoolChainFamily :
    DvdControlledChainFamily Bool := ...
```

が作れる。

最後に例：

```lean
theorem primitive_two_three_sampleDvdControlled_hitMass_le_sourceMass :
    (sampleDvdControlledBoolChainFamily.toSourceControlled
      unitNatMassSpace_dvdMonotone).hitMass ({2, 3} : Finset ℕ) ≤
    (sampleDvdControlledBoolChainFamily.toSourceControlled
      unitNatMassSpace_dvdMonotone).sourceMass := by
  exact SourceControlledChainFamily.primitive_hitMass_le_sourceMass
    primitiveOn_pair_two_three
    (sampleDvdControlledBoolChainFamily.toSourceControlled
      unitNatMassSpace_dvdMonotone)
```

## 7. なぜこれが次に良いか

この一手で、

$$
\text{source-controlled}
$$

が、単なる仮定ではなく、

$$
\text{source の約数からなる chain}
+
\text{整除単調質量}
$$

から作れるようになる。

つまり、

$$
h\mid source
\Rightarrow
\mu(h)\le\mu(source)
$$

という **下降質量の自然な供給路** ができる。

これは将来の

$$
n\mapsto n/q
$$

や

$$
n\mapsto n/p
$$

に直結する。Markov kernel に入る前の、いちばん自然な橋じゃ。

## 8. その次の候補

`DvdControlledChainFamily` が閉じたら、次は二択じゃ。

### A. `Branching/SubConservative` 接続

```lean
Branching
SubConservative
Reachable
```

から `DvdControlled` ないし `SourceControlled` を作る。

これは抽象 Mass API との接続が強くなる。

### B. `PrimeDescentStep`

```lean
def PrimeDescentStep (n m : ℕ) : Prop :=
  ∃ p, Nat.Prime p ∧ p ∣ n ∧ m = n / p
```

のような実際の下降 step を入れる。

これは Erdős #1196 の $n\to n/p$ に近づく。

わっちなら、次はまず `DvdControlledChainFamily`。
その後に `PrimeDescentStep` じゃ。

## 9. 今回の総括

Phase D によって、finite primitive hitting ルートはかなり形になった。

いまの定理列はこう読める。

$$
\text{PrimitiveOn}
\Rightarrow
|S\cap C_i|\le 1
\Rightarrow
\text{hit mass per chain}\le\text{source mass}
\Rightarrow
\text{forest hit mass}\le\text{forest source mass}
$$

次はここに、

$$
h\mid source_i
\Rightarrow
\mu(h)\le\mu(source_i)
$$

を供給する。

つまり次の実装名は、わっちならこうじゃ。

```text
Phase E: Dvd-controlled descent forest
```

これが閉じると、ようやく「有限の下降鎖」は、ただの比較可能集合ではなく、 **source から実際に下ってきたもの** として扱えるようになる。
