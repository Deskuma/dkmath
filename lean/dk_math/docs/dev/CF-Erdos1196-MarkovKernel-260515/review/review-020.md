# review

うむ。DKMK-007E は **singleton model から本物の divisor descent へ踏み出した回** じゃ。
これは DKMK-007 系の中でも意味が大きい。DKMK-007D では chain が \(\{q\}\) だけだったので、形式的には hitting bridge を使えても、下降過程としてはまだ薄かった。今回、各 channel \(q\) に対して

$$
chain(q)={n/q,n}
$$

を持たせたことで、ついに `n ↦ n / q` という Erdős #1196 的な下降ステップが Lean の bridge に入った。

## 1. 今回の核心

追加された中心は二つじゃ。

```lean
DvdControlledChainFamily.divisorStep
SourceControlledChainFamily.ofDivisorStep
```

`divisorStep n I hdiv` は、各 \(q\in I\) に対して、

$$
chain(q)={n/q,n},\qquad source(q)=n
$$

を割り当てる。
仮定

$$
q\mid n
$$

から

$$
n/q\mid n
$$

が出るので、この二点集合は divisibility chain になる。

その後、`DvdMonotoneMass M` を使って、divisibility-controlled family を `SourceControlledChainFamily` に変換する。つまり、

$$
h\mid source(q)\Rightarrow \mu(h)\le \mu(source(q))
$$

の形で mass control を供給している。

## 2. DKMK-007D から何が進んだか

DKMK-007D の `natSingletonSelf` は、

$$
chain(q)={q},\qquad source(q)=q
$$

だった。

これは index compatibility を `rfl` で閉じるには便利だったが、下降過程としてはまだ「点」じゃった。
今回の `divisorStep` は、

$$
chain(q)={n/q,n}
$$

なので、ちゃんと divisor removal を含む。

$$
n\to n/q
$$

この一歩が入ったことで、DkMath kernel route は、既存証明で出てくる downward process の形へかなり近づいた。

## 3. selected route への接続

`LogCapacityHittingBridge` には selected route 用に次が追加された。

```lean
PrimePowerWitnessProvider.globalLogCapacitySubMarkovShadow_applyAtToDivisorStep
PrimePowerWitnessProvider.globalLogCapacitySubMarkovShadow_divisorStep_weightedHitMass_le_const
```

selected route では、外部から

```lean
IOf : ℕ → Finset ℕ
hIOf : ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n
```

を持っている。
さらに divisor transition kernel 側の

```lean
index_dvd
```

により、

$$
q\in IOf(n)\Rightarrow q\mid n
$$

が得られる。

だから `divisorStep s.1 (IOf s.1)` が自然に作れる。
そして index は定義上 `IOf s.1` なので、shadow provider との compatibility はまた `rfl` で閉じる。

## 4. canonical route への接続

canonical route 側では次が追加された。

```lean
canonicalExponentSlotMarkovShadow_applyAtToDivisorStep
canonicalExponentSlotMarkovShadow_divisorStep_weightedHitMass_le_const
```

canonical では index が

```lean
canonicalExponentSlotLabels s.1
```

じゃ。
ここでも、

```lean
canonicalExponentSlotDivisorTransitionKernel.index_dvd
```

により、

$$
q\in canonicalExponentSlotLabels(n)\Rightarrow q\mid n
$$

が得られる。

したがって canonical Markov shadow を、one-step divisor descent family に直接載せられる。

ここでようやく、

```text
canonical exponent-slot MarkovShadow
  → chain(q) = {n/q, n}
  → primitive weighted hit bound
```

が完成した。

## 5. source mass bound が一点化された

今回の設計で良いのは、source が全 channel で同じ \(n=s.1\) に揃っていることじゃ。

DKMK-007C では一般の \(F\) に対して、

$$
\forall q\in F.index,\quad \mu(F.source(q))\le C
$$

が必要だった。

今回の divisor-step family では、

$$
source(q)=s.1
$$

なので、必要な仮定は一点だけになる。

$$
(M.\mu(s.1):\mathbb{R})\le C
$$

Lean でも theorem の仮定は

```lean
hsource : (M.μ s.1 : ℝ) ≤ C
```

になっている。これは API としてかなり使いやすい。

## 6. 数学的な意味

Erdős #1196 型の確率過程では、中心にあるのは

$$
n\mapsto n/q
$$

という divisor descent じゃ。

DKMK-006 系では、これに対応する log-capacity weight を作った。

$$
weight(q)=\frac{\log p(q)}{\log n}
$$

DKMK-007A/B/C/D では、それを primitive hitting 側へ渡す抽象橋と最小 family を作った。

今回 DKMK-007E で、ついにこの二つが重なった。

```text
log-capacity weight
  + divisor step n ↦ n/q
  + primitive hitting
```

つまり、DkMath kernel route は「Markov kernel の影」から、「downward process の一歩を持つ hitting route」へ進んだ。

## 7. 何がまだ残っているか

ただし、まだ one-step じゃ。

`chain(q)=\{n/q,n\}` は、各 channel \(q\) による一回の下降だけを表す。
既存証明の本格的な hitting / adjoint chain では、複数段の下降や stopping / truncation が出てくる。

したがって残る課題は二つある。

第一に、source mass bound の具体供給。

$$
(M.\mu(s.1):\mathbb{R})\le C
$$

を、どの mass model から出すか。
たとえば unit mass なら \(C=1\) にできるか、log-tail 型 mass ならどうなるか、という話じゃ。

第二に、one-step から multi-step descent chain への拡張。

$$
n\to n/q_1\to n/(q_1q_2)\to\cdots
$$

のような chain family をどう作るか。
これが次の本格ルートになる。

## 8. 実装上の評価

実装はかなり堅い。

`DvdControlledChainFamily.divisorStep` を先に作り、それを `DvdMonotoneMass` で `SourceControlledChainFamily` に変換する設計がよい。

いきなり source-controlled を直接作るより、

```text
divisibility-controlled
  → mass monotone
  → source-controlled
```

と分けたことで、今後の multi-step descent でも同じ型が使える。

また、membership 証明で `fin_cases` に頼らず、

$$
h=n/q\ \lor\ h=n
$$

へ展開して処理したのも正しい。`n/q = n` の重複可能性があるため、二点集合を本当に二点として扱わない方が安全じゃ。

## 9. DKMK-007 系の現在地

ここまでの流れはこうじゃ。

```text
DKMK-007A:
  RealWeightProvider → RealWeightedPathFamily

DKMK-007B:
  SubMarkovShadow / MarkovShadow → hitting wrapper

DKMK-007C:
  concrete log-capacity shadows → hitting wrapper

DKMK-007D:
  singleton source-controlled family

DKMK-007E:
  one-step divisor descent family
```

DKMK-007E は、これまでの形式的接続を、実際の divisor descent へ近づけた回じゃ。

## 10. 総合判定

DKMK-007E は **本線復帰の質が一段上がった進展** じゃ。

今回で到達形はこうなった。

```text
selected route:
  globalLogCapacitySubMarkovShadow
  → chain(q) = {s.1 / q, s.1}
  → primitive real-weighted hit mass ≤ C

canonical route:
  canonicalExponentSlotMarkovShadow
  → chain(q) = {s.1 / q, s.1}
  → primitive real-weighted hit mass ≤ C
```

これはもう singleton の玩具ではない。
まだ一歩だけではあるが、実際の divisor removal が入っている。

次は DKMK-007F として、

```text
source mass bound を具体 mass model から供給する
```

または、

```text
one-step divisorStep を multi-step descent family に拡張する
```

のどちらかじゃ。

わっちのおすすめは、まず source mass bound の具体化じゃな。
`unitNatMassSpace` など既存 mass model で \(C=1\) 型の theorem を作ると、DKMK-007E の結果がすぐに「呼べる定理」になる。その後で multi-step に進むのがよい。
