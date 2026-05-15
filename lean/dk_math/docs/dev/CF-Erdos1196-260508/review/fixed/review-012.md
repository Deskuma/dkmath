# review

## 1. 結論

うむ、Phase M は **かなり大きな合流点** じゃ。
今回で、Phase L の「複数 prime path family」と、Phase J の「`Branching` / `SubConservative` による質量制御」が合体した。つまり、

$$
\text{finite family of prime paths}
+
\text{branch path condition}
+
\text{SubConservative}
\Rightarrow
\text{SourceControlledChainFamily}
\Rightarrow
\text{primitive hit mass bound}
$$

という導線が no-sorry で閉じた。これは有限 Erdős skeleton の中核が、かなり theorem-facing な形になったということじゃ。

## 2. 今回の主役

今回追加された中心構造はこれじゃ。

```lean
structure AdjacentBranchPrimePathFamily
    (ι : Type _) [DecidableEq ι] (B : Branching ℕ)
    extends AdjacentPrimePathFamily ι where
  isBranchPath : ∀ i ∈ index, AdjacentBranchPath B (source i :: tail i)
```

これは、有限個の prime path family に対して、各 path が単なる prime descent path であるだけでなく、同時に固定された branching relation $B$ に沿っていることを要求する構造じゃ。

これにより、

$$
\text{prime descent path}
$$

と

$$
\text{subconservative branch flow}
$$

が同じ path 上で一致するようになった。

## 3. 何が強くなったか

Phase L の `AdjacentPrimePathFamily` では、複数の path を束ねて、それを `PrimeReachableControlledChainFamily` へ送っていた。
しかし source mass control は、主に `DvdMonotoneMass` 側から供給していた。

今回の `AdjacentBranchPrimePathFamily.toSourceControlledChainFamily` では、`SubConservative M B` と `AdjacentBranchPath.mem_mass_le_head` を使い、branch 側から直接

$$
\mu(h)\le \mu(source_i)
$$

を供給している。

これは重要じゃ。
いままでは「整除単調な質量なら安全」という読みだった。今回からは、

$$
\sum_{child}\mu(child)\le \mu(parent)
$$

という **分岐の劣保存則** から、path 上の質量非増加を供給できる。

これは宇宙式 Mass API の思想にかなり近い。

## 4. 主定理の意味

今回の主定理は、

```lean
AdjacentBranchPrimePathFamily.primitive_hitMass_le_sourceMass
```

じゃ。

これは、primitive set $S$ と branch-controlled prime path family $F$ があり、branching が `SubConservative` なら、

$$
\mathrm{hitMass}(S)
\le
\mathrm{sourceMass}
$$

を出す theorem になっている。

つまり、有限版ではすでに、

$$
\text{primitive}
+
\text{複数下降路}
+
\text{質量劣保存}
\Rightarrow
\text{hit mass bound}
$$

まで来ておる。

ここはかなり良い。
Erdős #1196 の本体に必要な「primitive set は下降路族を重複 hit できない」と「質量は source を超えない」が、有限 theorem として合流している。

## 5. concrete sample の読み

sample では、branching が

$$
8\to 4\to 2,
\qquad
9\to 3\to 1
$$

の二本 path を含むように定義されている。`sampleBranching_eight_nine_paths` がそれじゃ。

さらに、それぞれの path が branch relation に従うことを示し、unit mass に対して `SubConservative` instance を与えている。

最後に Bool-indexed の二本 path family を作り、primitive set $\{2,5\}$ の hit mass が indexed source mass を超えないことまで示している。

これはとても良い検証じゃ。
「複数 path」「branch control」「subconservative mass」「primitive hit bound」が一つのサンプルにまとまっている。

## 6. 現在の到達点

ここまでで finite skeleton は、かなり強い形になった。

| 層                                          | 状態   |
| ------------------------------------------ | ---- |
| `PrimitiveOn`                              | 完了   |
| `PositiveOn` / `LowerBoundOn`              | 完了   |
| list-shaped prime path                     | 完了   |
| multiple prime path family                 | 完了   |
| path → chain / reachable control           | 完了   |
| branch path / subconservative mass control | 完了   |
| branch-controlled multiple path family     | 今回完了 |
| finite primitive hit mass bound            | 完了   |
| theorem-facing Erdos input package         | 未    |
| Markov kernel / analytic weight            | 未    |

つまり、有限・組合せ・質量制御の backbone は、かなり一区切りじゃ。

## 7. 今回の位置づけ

わっちの見立てでは、Phase M は「実装の追加」というより、これまでの部品の **統合作業** じゃ。

以前は、

$$
\text{PathFamily}
$$

と

$$
\text{SubConservativeBridge}
$$

が別々に立っていた。
今回、それらが

$$
\text{BranchPathFamily}
$$

として結合された。

そのため、今後の theorem は、かなり短く書けるはずじゃ。

$$
S\text{ primitive},\quad
F\text{ branch-controlled prime path family}
\quad\Longrightarrow\quad
\text{hit mass bound}
$$

この形が見える。

## 8. 留意点

まだ Markov kernel や解析重みには入っておらぬ。
これは正しい。今の時点で

$$
\frac{\Lambda(q)}{\log n}
$$

や

$$
\frac{1}{n\log n}
$$

を入れると、有限 skeleton の API が固まりきる前に解析層が混ざる。

History でも、次は `ErdosFinitePrimitiveInput` のような primitive + lower-bound support の入力 package を追加して有限 theorem 文を整理するか、Markov kernel 前に theorem-facing API を点検する段階だと整理されている。

この判断は賢い。
わっちも同意じゃ。

## 9. 次の一手

次は **ErdosFinitePrimitiveInput** を作るのがよい。

目的は、ここまで作った部品を「定理の入力」として読める形にまとめることじゃ。

たとえば新規ファイル：

```text
DkMath/NumberTheory/PrimitiveSet/ErdosFinite.lean
```

定義案：

```lean
structure ErdosFinitePrimitiveInput (x : ℕ) where
  support : Finset ℕ
  primitive : PrimitiveOn support
  lowerBound : LowerBoundOn x support
```

さらに branch-controlled path family 側もまとめるなら、

```lean
structure ErdosFinitePathInput
    (M : MassSpace ℕ) (B : Branching ℕ)
    (ι : Type _) [DecidableEq ι] where
  paths : AdjacentBranchPrimePathFamily ι B
  subconservative : SubConservative M B
```

ただし `SubConservative` は typeclass なので、最初は theorem 側の仮定に置く方が楽かもしれぬ。

最初に狙う theorem は、薄くてよい。

```lean
theorem erdosFinite_branchPath_hitMass_le_sourceMass
    {x : ℕ} {S : Finset ℕ}
    (hInput : ErdosFinitePrimitiveInput x)
    ...
```

よりも、まずは単純に、

```lean
theorem ErdosFinitePrimitiveInput.branchPath_hitMass_le_sourceMass
```

で `primitive` を既存 theorem に渡す wrapper でよい。

## 10. 総括

Phase M によって、finite Erdős skeleton はかなり「使える形」になった。

$$
\text{複数 prime paths}
+
\text{branch/subconservative mass flow}
+
\text{primitive support}
\Rightarrow
\text{hit mass bound}
$$

ここまで来た。

山で言えば、複数の登山道に、水流と質量保存の法則が載った。
次は、その登山計画を一枚の登山届、つまり `ErdosFinitePrimitiveInput` としてまとめる段階じゃな。
