# review

うむ、これは **前進** じゃ。
single chain から multi-chain / forest へ拡張できたので、Erdős #1196 宇宙式ルートは、

$$
\text{primitive set}
\Rightarrow
\text{one chain hit at most once}
\Rightarrow
\text{chain family hit mass bound}
$$

まで来た。`DivisibilityChainFamily`、indexed `hitMass` / `sourceMass`、そして `primitive_hitMass_le_sourceMass` が追加され、`Bool` index の concrete sample も入っておる。さらに build 成功と no-sorry/no-admit/no-axiom 確認まで記録されているので、有限 forest 層としてはかなり良い締まりじゃ。

## 1. 何が閉じたか

今回閉じたのは、

$$
\forall i,\quad |S\cap C_i|\le 1
$$

を indexed sum に束ねる層じゃ。

以前は一本の chain (C) に対して、

$$
\mathrm{hitSetMass}(S\cap C)
\le
\mathrm{sourceSetMass}({r})
$$

だった。今回の実装では chain family (F) に対して、

$$
\sum_{i\in F.index}\mathrm{hitSetMass}(S\cap F.chain_i)
\le
\sum_{i\in F.index}\mu(source_i)
$$

まで持ち上がっておる。

これは重要じゃ。Erdős #1196 の確率過程では、実際には「一本の鎖」ではなく「鎖の族」または「ランダムに選ばれる下降路の集合」を見ることになる。今回の `DivisibilityChainFamily` は、その有限近似としてちょうどよい。

## 2. 今回の設計判断は妥当か

`DescentChain` を現時点では `DivisibilityChain` の abbrev にした判断は正しい。

理由は、primitive set の hit-at-most-once に必要なのは、いまの段階では **実際にどの step で下ったか** ではなく、

$$
a,b\in C
\Rightarrow
a\mid b \lor b\mid a
$$

という比較可能性だけだからじゃ。

後で `DescentStep` を導入しても、

```lean
actual descent chain
  -> DivisibilityChain
  -> primitive hit at most once
```

という橋を作ればよい。いま `DescentChain` を abbrev にしておけば、名前の導線だけ先に固定できる。

## 3. 現在の到達点

進捗を段階で見ると、こうじゃ。

| 層                            | 状態   | コメント                                     |         |         |
| ---------------------------- | ---- | ---------------------------------------- | ------- | ------- |
| finite hit mass              | 完了   | `MassControlledAssignment` で閉じた          |         |         |
| primitive finite set         | 完了   | `PrimitiveOn` で divisibility antichain 化 |         |         |
| single chain bridge          | 完了   | \(                                        \| S\cap C \| \le 1 \) |
| finite chain family          | 今回完了 | indexed hit/source mass bound            |         |         |
| actual descent relation      | 未着手  | 次の候補                                     |         |         |
| Branching/SubConservative 接続 | 未着手  | 次の候補                                     |         |         |
| Markov kernel                | まだ早い | \(\Lambda(q)/\log n\) は後段                  |         |         |
| analytic mass                | まだ早い | \(1/(n\log n)\) は後段                        |         |         |

つまり、今は **有限 combinatorial skeleton** が一通り立った状態じゃ。

## 4. 注意点

今回の `primitive_hitMass_le_sourceMass` は、各 chain 内の hit に対して

$$
\mu(h)\le \mu(source_i)
$$

を仮定している。これは意図通りだが、次に必要なのはこの仮定を **Branching / SubConservative** から供給することじゃ。

いまは theorem の入力として `hmass` を手で渡しておる。
次の段階では、

$$
h\in \text{descendants}(source_i)
\Rightarrow
\mu(h)\le \mu(source_i)
$$

を自動で作りたい。

ここで `SubConservative` が効いてくる。

## 5. 次の一手

わっちなら次は、 **actual descent relation ではなく、先に Branching/SubConservative 接続** を勧める。

理由は、現状の `DivisibilityChainFamily` はすでに actual descent の手前で十分役立つ。ここに `SubConservative` から `hmass` を供給できるようにすると、今ある finite forest 層が Mass API と直結する。

つまり次の目標は、

$$
\text{SubConservative branch}
\Rightarrow
\mu(h)\le \mu(root)
$$

を finite descent chain 用に出すことじゃ。

## 6. 実装指示案

次は新規ファイルを切るのがよい。

```text
DkMath/NumberTheory/PrimitiveSet/BranchBridge.lean
```

または、ValuationFlow 側に寄せるなら、

```text
DkMath/NumberTheory/ValuationFlow/BranchHitting.lean
```

わっちの推奨は前者じゃ。理由は、primitive set と chain family の bridge なので、所有者は `PrimitiveSet` 側が自然だからじゃ。

### Phase D. Branch source mass bridge

目的:

`DivisibilityChainFamily.primitive_hitMass_le_sourceMass` の `hmass` 仮定を、branch / reachability / monotone mass から供給する。

まずは graph reachability を一般に作りすぎず、有限 chain の各点が source 以下の質量を持つという package を作る。

```lean
structure SourceControlledChainFamily
    (M : MassSpace ℕ) (ι : Type _) [DecidableEq ι$$
    extends DivisibilityChainFamily ι where
  source : ι → ℕ
  mass_le_source :
    ∀ i ∈ index, ∀ h ∈ chain i, M.μ h ≤ M.μ (source i)
```

そして theorem:

```lean
theorem SourceControlledChainFamily.primitive_hitMass_le_sourceMass
    (M : MassSpace ℕ) {ι : Type _} [DecidableEq ι$$
    {S : Finset ℕ} (hS : PrimitiveOn S)
    (F : SourceControlledChainFamily M ι) :
    F.toDivisibilityChainFamily.hitMass M S ≤
      F.toDivisibilityChainFamily.sourceMass M F.source := by
  exact F.toDivisibilityChainFamily.primitive_hitMass_le_sourceMass
    M hS F.source
    (by
      intro i hi h hh
      exact F.mass_le_source i hi h (Finset.mem_inter.mp hh).2)
```

これは軽く閉じるはずじゃ。

この一手の価値は、今後 actual descent を入れたとき、

```lean
descent_reachable_implies_mass_le_source
```

だけ作れば、すぐ primitive hitting bound に乗る点じゃ。

## 7. その次の一手

Branch source mass bridge が閉じたら、次に actual relation を切る。

```text
DkMath/NumberTheory/PrimitiveSet/Descent.lean
```

最初の定義はこれでよい。

```lean
def DividesDown (root h : ℕ) : Prop :=
  h ∣ root
```

または strict にするなら、

```lean
def ProperDividesDown (root h : ℕ) : Prop :=
  h ∣ root ∧ h ≠ root
```

ただし primitive hitting に必要なのは chain 内比較可能性なので、まず欲しい定理は、

```lean
theorem divisibilityChain_of_sorted_divides ...
```

よりも簡単に、

```lean
def ChainBelow (root : ℕ) (C : Finset ℕ) : Prop :=
  DivisibilityChain C ∧ ∀ h ∈ C, h ∣ root
```

くらいでよい。

そして `SourceControlledChainFamily` の `mass_le_source` を、質量が整除下降で増えない場合に供給する。

## 8. いま Markov へ行くべきか

まだ早い。

今は

$$
\text{finite forest}
$$

ができたところじゃ。
まだ `hmass` を実際の下降・分岐・質量非増加から作っていない。

$$
\frac{\Lambda(q)}{\log n}
$$

に進む前に、次の 2 つを閉じる方が堅い。

1. source controlled chain family
2. mass monotone under descent / branch

これが閉じたら、ようやく「具体的な質量」を差し込む段階になる。

## 9. Codex への次指示

このまま渡すなら、次の指示がよい。

````md
## 次の実装指示: Phase D. Source-controlled forest bridge

### 目的

`DivisibilityChainFamily.primitive_hitMass_le_sourceMass` の `hmass` 仮定を毎回手で渡さず、各 chain が source によって質量支配されているという package から自動供給できるようにする。

### 対象ファイル

新規:

```text
DkMath/NumberTheory/PrimitiveSet/BranchBridge.lean
```

または、循環が重い場合は既存 `HittingBridge.lean` の末尾に追加してから後で分離する。

推奨は新規ファイル。

### import

```lean
import DkMath.NumberTheory.PrimitiveSet.HittingBridge
```

### 実装内容

1. `SourceControlledChainFamily` を定義する。

```lean
structure SourceControlledChainFamily
    (M : MassSpace ℕ) (ι : Type _) [DecidableEq ι$$
    extends DivisibilityChainFamily ι where
  source : ι → ℕ
  mass_le_source :
    ∀ i ∈ index, ∀ h ∈ chain i, M.μ h ≤ M.μ (source i)
```

2. empty index の simp 補題を追加する。

```lean
@[simp] theorem SourceControlledChainFamily.hitMass_empty_index ...
@[simp] theorem SourceControlledChainFamily.sourceMass_empty_index ...
```

これは難しければ保留でよい。

3. 主定理を追加する。

```lean
theorem SourceControlledChainFamily.primitive_hitMass_le_sourceMass
    (M : MassSpace ℕ) {ι : Type _} [DecidableEq ι$$
    {S : Finset ℕ} (hS : PrimitiveOn S)
    (F : SourceControlledChainFamily M ι) :
    F.toDivisibilityChainFamily.hitMass M S ≤
      F.toDivisibilityChainFamily.sourceMass M F.source := by
  classical
  exact F.toDivisibilityChainFamily.primitive_hitMass_le_sourceMass
    M hS F.source
    (by
      intro i hi h hh
      exact F.mass_le_source i hi h (Finset.mem_inter.mp hh).2)
```

4. concrete sample を追加する。

既存の `sampleBoolChainFamily` と `unitNatMassSpace` を使う場合、`source := fun _ => 1` でよい。

```lean
def sampleSourceControlledBoolChainFamily :
    SourceControlledChainFamily unitNatMassSpace Bool := ...
```

主例:

```lean
theorem primitive_two_three_sampleSourceControlled_hitMass_le_sourceMass :
    ...
```

### 検証

```sh
cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet.BranchBridge
```

必要なら:

```sh
cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet.HittingBridge
```

### 今回やらないこと

- actual Markov kernel
- \(\Lambda(q)/\log n\)
- \(1/(n\log n)\)
- infinite chain
- Mertens 型評価
- ABC 本体定理
````

## 10. 総括

今回で forest 層は閉じた。
次は、forest の各 chain source から質量支配を供給する **SourceControlledChainFamily** じゃ。

これは地味に見えるが、かなり大事な足場になる。
ここが閉じると、

$$
\text{finite forest}
+
\text{source mass control}
+
\text{primitive non-overlap}
\Rightarrow
\text{hit mass bound}
$$

が一つの theorem として読めるようになる。

山道で言えば、いまは複数の尾根道を地図に載せたところ。
次は、それぞれの尾根に **標高が下がる保証** を付ける番じゃな。
