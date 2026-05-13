# review Phase "B"

## 1. 結論

うむ、Phase BE は **ratio-style weight route の登頂用ショートカット** じゃ。

Phase BD で、

$$
c(n,p)=\frac{A(p)}{B(n)}
$$

について、分子非負・分母正・budget 条件

$$
\sum_{q\in index(n)} A(p(q))\le B(n)
$$

から sub-probability へ進めるようになった。今回 Phase BE では、それをさらに一段まとめて、

$$
\text{非負性}
\to
\text{budget}
\to
\text{sub-probability}
\to
\mathrm{weightedHitMass}\le C
$$

へ直接進む theorem-facing alias として

```lean
PrimePowerWitnessProvider.ratioBaseWeight_hitMass_le_const
```

が追加された。実装・build・no-sorry 検査も通っておる。

## 2. 今回の主役

今回の主役はこれじゃ。

```lean
theorem ratioBaseWeight_hitMass_le_const
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (A B : ℕ → ℚ)
    (hA : ∀ p, 0 ≤ A p)
    (hB : ∀ n, 0 < B n)
    (hbudget : W.RatioBaseWeightBudget A B)
    ...
```

これは、ratio-style weight

$$
w(n,q)=\frac{A(p(q))}{B(n)}
$$

について、必要な仮定をまとめて受け取り、

$$
\mathrm{weightedHitMass}\le C
$$

まで運ぶ定理じゃ。

内部では既存の

```lean
W.baseWeightNonneg_of_ratioBasePrimeWeight A B hA hB
W.baseWeightSubProbability_of_ratioBudget A B hA hB hbudget
W.baseWeight_hitMass_le_const ...
```

をつないでいる。つまり、Phase BC / BD / BA / AZ の成果を、一本のルート名に束ねたわけじゃな。

## 3. 何が良くなったか

これまでは、ratio-style weight を hit mass bound に通すには、途中の部品を明示的に組み合わせる必要があった。

$$
0\le A(p)
$$

$$
0 < B(n)
$$

$$
\sum_q A(p(q))\le B(n)
$$

から、まず `BaseWeightNonneg` を作り、次に `BaseWeightSubProbability` を作り、それから `baseWeight_hitMass_le_const` へ渡す。

Phase BE 以降は、これを

```lean
W.ratioBaseWeight_hitMass_le_const A B hA hB hbudget ...
```

として読める。

これは証明力の増加というより、 **ルートの固定** じゃ。
山道で言えば、今まで手でロープを掛け替えていた区間に、常設ロープが張られた。

## 4. 数学的な意味

この定理が表しているのは、かなり明快じゃ。

各 state $n$ に総予算 $B(n)$ があり、各 prime channel の base prime $p(q)$ に局所コスト $A(p(q))$ がある。

budget 条件は、

$$
\sum_{q\in index(n)} A(p(q))\le B(n)
$$

であり、実際に使う重みは、

$$
w(n,q)=\frac{A(p(q))}{B(n)}
$$

である。

よって、

$$
\sum_{q\in index(n)}w(n,q)\le 1
$$

となり、これは sub-probability になる。
その結果、primitive target への hitting mass は source 側の上界 $C$ を超えない。

つまり、Phase BE の定理は、

$$
\boxed{
\text{予算内 ratio weight は、weightedHitMass を暴走させない}
}
$$

という有限質量保存の ratio-style 版じゃな。

## 5. 現在地

ここまでの登山道はこうじゃ。

| 層                            | 状態   |
| ---------------------------- | ---- |
| `ratioBasePrimeWeight`       | 完了   |
| ratio-style 非負性              | 完了   |
| `RatioBaseWeightBudget`      | 完了   |
| budget → sub-probability     | 完了   |
| ratio-style → hit mass bound | 今回完了 |
| concrete ratio-style sample  | 未    |
| 実数/log route                 | 未    |

つまり ratio-style toy route は、一般定理としてはほぼ一本通った。

残る確認は、具体例で

$$
A,\ B,\ budget,\ hitMass
$$

を実際に通すことじゃ。

## 6. 次の一手: Phase BF

次は History にある通り、 **concrete ratio-style sample** が自然じゃ。

既存 sample に合わせるなら、たとえばこういう $A,B$ がよい。

```lean
def sampleTenRatioA (p : ℕ) : ℚ :=
  if p = 2 then 1 else 0

def sampleTenRatioB (_n : ℕ) : ℚ :=
  1
```

すると、

$$
A(2)=1,\qquad A(5)=0,\qquad B(n)=1
$$

となる。

sample index は状態 $10$ で

$$
{2,5}
$$

なので、witness provider が読む base prime はそれぞれ $2,5$ 。したがって、

$$
A(2)+A(5)=1+0=1\le B(10)=1
$$

となり、budget が閉じる。

状態 $10$ 以外では index が空なので、

$$
0\le B(n)=1
$$

で済む。

## 7. Phase BF で欲しい theorem

Phase BF では、最低限このあたりが欲しい。

```lean
def sampleTenRatioA : ℕ → ℚ := ...
def sampleTenRatioB : ℕ → ℚ := ...

theorem sampleTenRatioA_nonneg :
    ∀ p, 0 ≤ sampleTenRatioA p

theorem sampleTenRatioB_pos :
    ∀ n, 0 < sampleTenRatioB n

theorem sampleTenRatioBudget :
    sampleTenPrimePowerWitnessProvider.RatioBaseWeightBudget
      sampleTenRatioA sampleTenRatioB
```

そして最後に、

```lean
theorem sampleTenRatioBaseWeight_hitMass_le_one :
    ...
```

を `ratioBaseWeight_hitMass_le_const` で閉じる。

これが通れば、

$$
\text{具体的な }A(p)/B(n)
\to
\text{budget}
\to
\mathrm{weightedHitMass}\le 1
$$

まで実例で開通する。

## 8. 注意点

この sample ratio weight は、既存の `sampleTenToyPrimeBaseWeight` と **全域では一致しない** 可能性がある。

既存のものは、

$$
c(n,p)=
\begin{cases}
1 & n=10,\ p=2,\\
0 & \text{otherwise}
\end{cases}
$$

だった。

一方、

$$
A(p)=\mathbf{1}_{p=2},\qquad B(n)=1
$$

なら、

$$
c(n,p)=A(p)/B(n)
$$

なので、 $n\ne 10$ でも $p=2$ なら $1$ になる。

ただし、`weightOfBase` は index 外では $0$ を返す。sample kernel では $n\ne10$ の index が空なので、実際の channel 上では問題にならぬ。

つまり、全域一致よりも、

$$
q\in index(n)
$$

上で必要な値が合っていることが重要じゃ。

## 9. その先

Phase BF が閉じたら、ratio-style toy route は完成に近い。

その後は二択じゃ。

一つは、有理 toy model の alias や sample をもう少し増やして API を安定化する道。
もう一つは、実数・対数へ向かう準備として、

$$
A(p)\approx \log p,\qquad B(n)\approx \log n
$$

の設計メモを Lean ではなく doc 側に先に書く道じゃ。

わっちなら、Phase BF で concrete sample を通したあと、いったん小まとめを置くのがよいと思う。
ここは第2キャンプ後の最初の急登が一段落する地点じゃからの。

## 10. 総括

Phase BE は、ratio-style weight の **hit mass bound 直行ルート** じゃ。

これで、

$$
0\le A(p),\qquad 0 < B(n),\qquad \sum_q A(p(q))\le B(n)
$$

から、

$$
\mathrm{weightedHitMass}\le C
$$

まで一発で行ける。

山で言えば、予算 $B(n)$ の範囲内に収まる登山料 $A(p)/B(n)$ なら、どれだけ prime-power channel が分岐しても、質量は Big の外へ飛び出せない。
次は、その仕組みを sample $A,B$ で実際に走らせる番じゃな。
