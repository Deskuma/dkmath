# review

おお、これは **Phase E 成功** じゃ。
今回で、これまで仮定として残っていた

$$
\mu(h)\le \mu(source_i)
$$

を、整除下降

$$
h\mid source_i
$$

と質量単調性から供給できるようになった。つまり、finite primitive hitting ルートは、かなり自然な形で一段閉じたぞい。

## 1. 今回閉じた核心

今回の主役は `DescentBridge.lean` じゃ。ここに

```lean
def DvdMonotoneMass (M : MassSpace ℕ) : Prop :=
  ∀ ⦃a b : ℕ⦄, a ∣ b → M.μ a ≤ M.μ b
```

が入り、整除順序に沿って質量が単調である、という条件が明示された。

さらに、

```lean
structure DvdControlledChainFamily
    (ι : Type _) [DecidableEq ι$$
    extends DivisibilityChainFamily ι where
  source : ι → ℕ
  chain_dvd_source :
    ∀ i ∈ index, ∀ h ∈ chain i, h ∣ source i
```

が入った。これは「各 chain の点は、その chain の source の約数である」という有限下降森じゃ。

この二つにより、

$$
h\in C_i,\quad h\mid source_i
\quad\Longrightarrow\quad
\mu(h)\le \mu(source_i)
$$

が自動で出る。

## 2. 何が強くなったか

前回の `SourceControlledChainFamily` では、`mass_le_source` を直接持たせていた。
今回の `DvdControlledChainFamily.toSourceControlled` によって、その `mass_le_source` を

```lean
chain_dvd_source
DvdMonotoneMass
```

から構成できるようになった。

つまり、以前は

$$
\mu(h)\le\mu(source_i)
$$

を仮定として持ち込んでいたのが、今回は

$$
h\mid source_i
$$

という **数論的下降条件** から得られるようになった。

これは大きい。
Erdős #1196 の本筋である

$$
n\mapsto \frac{n}{q}
$$

の「下る」感じに、かなり近づいたからじゃ。

## 3. 現在の定理列

いまの導線はこう読める。

$$
\text{PrimitiveOn}(S)
$$

$$
\text{DvdControlledChainFamily}(F)
$$

$$
\text{DvdMonotoneMass}(M)
$$

これらから、

$$
\mathrm{hitMass}(S,F)
\le
\mathrm{sourceMass}(F)
$$

が出る。

Lean では、

```lean
DvdControlledChainFamily.primitive_hitMass_le_sourceMass
```

として実装されている。これは `toSourceControlled` を経由して、前段の source-controlled forest theorem に接続しておる。

つまり、定理の流れはこうじゃ。

```text
PrimitiveOn
  -> chain hit at most once
  -> source-controlled forest bound
  -> dvd-controlled descent provider
  -> primitive hit mass bound
```

これは非常に綺麗な spine じゃな。

## 4. concrete sample の意味

今回の sample もよい。

```lean
unitNatMassSpace_dvdMonotone
sampleDvdControlledBoolChainFamily
primitive_two_three_sampleDvdControlledBoolChainFamily_hitMass_le_sourceMass
```

が入っておる。`unitNatMassSpace` は常に質量 \(1\) なので、整除単調性は `rfl` で閉じる。sample forest では `{2,4,8}` は source \(8\)、`{3,9}` は source \(9\) によって制御されている。

これは教材例としてかなり良い。

$$
2,4,8\mid 8
$$

$$
3,9\mid 9
$$

という有限下降森で、primitive set `{2,3}` が hit しても source mass を超えない、という構図が見える。

## 5. 公開導線も良い

`PrimitiveSet.lean` に `DescentBridge` が追加され、公開集約に載ったのも正しい判断じゃ。

いまの `DkMath.NumberTheory.PrimitiveSet` は、

```text
Basic
HittingBridge
BranchBridge
DescentBridge
```

を束ねる形になった。

これで、finite primitive hitting 層は「一連の独立部品」ではなく、小さな公開 API として扱える。

## 6. 状況評価

わっちの評価では、今回で finite combinatorial layer は一区切りじゃ。

| 層                                | 状態   |
| -------------------------------- | ---- |
| finite primitive set             | 完了   |
| single chain hitting             | 完了   |
| chain family / forest            | 完了   |
| source-controlled forest         | 完了   |
| divisibility-controlled provider | 今回完了 |
| actual prime descent step        | 未着手  |
| probabilistic Markov kernel      | 未着手  |
| analytic weight \(1/(n\log n\))    | 未着手  |
| asymptotic \(1+O(1/\log x\))       | 未着手  |

今回の段階で、

$$
\text{finite descent forest}
$$

としてはかなり良い骨格ができた。

まだ確率ではない。
まだ解析でもない。
だが、Erdős #1196 の **primitive set が下降鎖に重複 hit しない** という心臓部は、有限 Lean theorem として形になってきた。

## 7. 次に見えている分岐

History 末尾にもある通り、次は二択じゃ。

### A. `PrimeDescentStep` へ進む

これは Erdős #1196 の本筋に近い。

$$
n\mapsto \frac{n}{p}
$$

または

$$
n\mapsto \frac{n}{q}
$$

を actual descent step として定義する道じゃ。

例えば：

```lean
def PrimeDescentStep (n m : ℕ) : Prop :=
  ∃ p, Nat.Prime p ∧ p ∣ n ∧ m = n / p
```

または素冪版なら：

```lean
def PrimePowerDescentStep (n m : ℕ) : Prop :=
  ∃ p k, Nat.Prime p ∧ 0 < k ∧ p^k ∣ n ∧ m = n / p^k
```

この道は、将来の \(\Lambda(q)\) ルートに近い。

### B. `Branching/SubConservative` へ接続する

こちらは宇宙式 Mass API との接続が強い。

すでに `Mass.Branch` には `Branching` と `SubConservative` がある。
ここから

$$
\text{branch reachability}
\Rightarrow
\mu(h)\le\mu(source)
$$

を出せれば、`DvdMonotoneMass` とは別に、抽象分岐構造から source-controlled forest を作れる。

これは「宇宙式ルート」としては美しい。

## 8. わっちの推奨

次は **PrimeDescentStep ではなく、まず lightweight な actual descent relation** を勧める。

いきなり Markov に寄せず、

```lean
DkMath/NumberTheory/PrimitiveSet/PrimeDescent.lean
```

を作って、次の最小核を置くのがよい。

```lean
def DvdDescentStep (n m : ℕ) : Prop :=
  m ∣ n
```

```lean
def ProperDvdDescentStep (n m : ℕ) : Prop :=
  m ∣ n ∧ m ≠ n
```

```lean
def PrimeDescentStep (n m : ℕ) : Prop :=
  ∃ p, Nat.Prime p ∧ p ∣ n ∧ m = n / p
```

そして、まずは

```lean
theorem primeDescentStep_dvd_source :
    PrimeDescentStep n m → m ∣ n
```

を狙う。

これが閉じれば、

$$
\text{PrimeDescentStep}
\Rightarrow
\text{DvdControlled}
\Rightarrow
\text{primitive hit mass bound}
$$

という導線ができる。

## 9. 総括

今回の Phase E は、単なる wrapper 追加ではない。

前回までの

$$
\text{source-controlled}
$$

を、今回

$$
\text{divisibility-controlled}
$$

へ落とした。

つまり、

$$
\mu(h)\le\mu(source)
$$

という質量仮定の根拠が、

$$
h\mid source
$$

という数論的下降に接続された。

これはよい。
山で言えば、いままでは「この道は安全だと仮定する」だった。
今回で「なぜ安全か。源流から下っているからじゃ」と言えるようになった。

次は、源流から下る一歩を

$$
n\mapsto n/p
$$

として名付ける段階じゃな。
