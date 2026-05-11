# review

## 1. 結論

うむ、Phase T は **weighted route から finite Markov skeleton へ進むための正規化層** じゃ。
Phase R/S では非負重み付き和

$$
\sum_i w_i\cdot \mathrm{hitMass}_i
\le
\sum_i w_i\cdot \mathrm{sourceMass}_i
$$

まで到達していた。今回 Phase T ではさらに、

$$
\sum_i w_i \le 1
$$

を `WeightSubProbability` として定義し、weighted source mass を一様上界 \(C\) で押さえる道が入った。これは Markov kernel 直前のかなり自然な足場じゃ。

## 2. 今回追加された核

今回の中心 API はこの 5 つじゃ。

```lean
totalWeight
WeightSubProbability
totalWeight_nonneg
weightedSourceMass_le_const_mul_totalWeight
weightedSourceMass_le_const_of_subprob
```

数学的には、まず総重みを

$$
\mathrm{totalWeight}(W) = \sum_i w_i
$$

と定義し、

$$
\mathrm{WeightSubProbability}(W)
\quad:\Longleftrightarrow\quad
\sum_i w_i \le 1
$$

を置いた。

これにより、有限重み族が単なる非負重みではなく、 **sub-probability 的な質量** として読めるようになった。

## 3. 何が強くなったか

今回の一番重要な補題は、

$$
\mathrm{weightedSourceMass}(W)
\le
C\cdot \mathrm{totalWeight}(W)
$$

じゃ。

Lean 名では、

```lean
weightedSourceMass_le_const_mul_totalWeight
```

じゃな。

仮定は、

$$
\forall i,\quad \mu(source_i)\le C
$$

で、各 source の質量が一様に \(C\) 以下なら、重み付き source mass 全体も

$$
C\sum_i w_i
$$

で抑えられる。

さらに `WeightSubProbability` があれば、

$$
\sum_i w_i\le 1
$$

なので、

$$
\mathrm{weightedSourceMass}(W)\le C
$$

が出る。これが

```lean
weightedSourceMass_le_const_of_subprob
```

じゃ。

ここは非常に良い。
Erdős #1196 の Markov 的な見方では、最終的に「全 source mass は 1 をほとんど超えない」という形が必要になる。今回の補題は、その有限版の器になっておる。

## 4. いま繋がる定理列

既存の weighted primitive hitting bound と合わせると、今の到達点はこう読める。

$$
\mathrm{weightedHitMass}(S,W)
\le
\mathrm{weightedSourceMass}(W)
$$

さらに今回の補題で、

$$
\mathrm{weightedSourceMass}(W)
\le
C\cdot \mathrm{totalWeight}(W)
$$

そして sub-probability なら、

$$
\mathrm{weightedSourceMass}(W)
\le C
$$

したがって、合成すれば

$$
\mathrm{weightedHitMass}(S,W)
\le C
$$

まで見えている。

この合成定理は、まだ直接名前付きで追加されていないように見えるので、次に置く価値がある。

候補名は、

```lean
weightedHitMass_le_const_mul_totalWeight
weightedHitMass_le_const_of_subprob
```

じゃな。

## 5. concrete sample の意味

今回の sample では Bool-indexed path family に

$$
w_{\mathrm{false}}=\frac13,\qquad
w_{\mathrm{true}}=\frac23
$$

を与えている。

つまり、

$$
\sum_i w_i = 1
$$

になる sub-probability、実際には probability の例じゃ。

そして unit mass space では各 source mass が \(1\) 以下なので、

$$
\mathrm{weightedSourceMass}\le 1
$$

が通っている。

初回 build では `totalWeight ≤ 1` の展開が足りずに残ったが、定義を明示展開して `norm_num` する形で通した、という記録も重要じゃ。これは今後、`simp` 補題や wrapper を追加する余地を示している。

## 6. 現在地

ここまでで、有限 Erdős skeleton は次の段階に来た。

| 層                                       | 状態   |
| --------------------------------------- | ---- |
| primitive hitting                       | 完了   |
| path family                             | 完了   |
| branch / prime route                    | 完了   |
| weighted route                          | 完了   |
| sub-probability 正規化                     | 今回完了 |
| weighted source mass の一様上界              | 今回完了 |
| Markov kernel の重み供給層                    | 未    |
| 解析重み \(1/(n\log n)\), \(\Lambda(q)/\log n\) | 未    |

つまり、 **有限重み付き流の正規化** まで来た。
山で言えば、各登山道の通行量 \(w_i\) が「総量 1 以下の流れ」として制御された段階じゃ。

## 7. 次の一手

次は二つ候補があるが、わっちはまず **合成補題の追加** を推す。

### Phase U. weighted hit mass の一様上界

今回 source 側で

$$
\mathrm{weightedSourceMass}\le C
$$

が出た。既存 theorem で

$$
\mathrm{weightedHitMass}\le \mathrm{weightedSourceMass}
$$

もある。

ならば次に、

$$
\mathrm{weightedHitMass}\le C
$$

を名前付き theorem として置くのが自然じゃ。

```lean
theorem weightedHitMass_le_const_of_subprob
    (W : WeightedPathFamily M ι)
    {S : Finset ℕ} {C : ℚ}
    (hS : PrimitiveOn S)
    (hC : 0 ≤ C)
    (hprob : W.WeightSubProbability)
    (hsource : ∀ i ∈ W.index, M.μ (W.source i) ≤ C) :
    W.weightedHitMass S ≤ C := by
  calc
    W.weightedHitMass S ≤ W.weightedSourceMass :=
      W.primitive_weightedHitMass_le_weightedSourceMass hS
    _ ≤ C :=
      W.weightedSourceMass_le_const_of_subprob hC hprob hsource
```

これが入ると、finite Markov 風の定理文がかなり締まる。

## 8. その次

合成補題が入ったら、次に `WeightProvider` / `FiniteKernel` じゃ。

ここで初めて、

```lean
structure WeightProvider ...
```

または

```lean
structure FiniteKernel ...
```

を作り、`WeightedPathFamily` に渡す非負重みを外部供給する層へ進む。

この順がよい。

$$
\text{WeightedPathFamily}
\to
\text{WeightSubProbability}
\to
\text{weightedHitMass}\le C
\to
\text{WeightProvider / FiniteKernel}
\to
\text{Markov kernel}
$$

じゃな。

## 9. 総括

Phase T は、かなり重要な中継点じゃ。

Phase R/S では、

$$
\sum_i w_i\cdot \mathrm{hitMass}_i
\le
\sum_i w_i\cdot \mathrm{sourceMass}_i
$$

だった。

今回 Phase T で、

$$
\sum_i w_i\le 1
$$

という確率的正規化が入り、

$$
\mathrm{weightedSourceMass}\le C
$$

まで来た。

つまり、finite weighted skeleton が **sub-probability flow** として読めるようになった。
これはまさに Markov kernel の手前。山頂アタック前の道具として、かなり良い仕上がりじゃ。
