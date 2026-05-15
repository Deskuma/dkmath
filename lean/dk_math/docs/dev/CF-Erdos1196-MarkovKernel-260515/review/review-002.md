# review

うむ、DKMK-002 は **よい前進** じゃ。
DKMK-001 で作った `CapacityKernel → Normalize` の抽象核を、今回ちゃんと既存の `RealWeightProvider / SubProbability` API に接続できておる。つまり、DkMath kernel が「独自の孤立構造」ではなく、既存の finite weight / path / hitting 側へ流し込める形になった。

## 1. 何が進んだか

今回追加された中心はこれじゃ。

```lean
DkMath.Kernel.SubProbability
```

ここで、

```lean
normalizedRealWeightProvider
normalizedRealWeightProvider_totalWeight
normalizedRealWeightProvider_subProbability
```

が追加された。

数学的には、`CapacityKernel` が持つ保存則

$$
\sum_{b\in children(a)} cost(a,b)\le capacity(a)
$$

を、正の capacity で割って、

$$
\sum_{b\in children(a)}
\frac{cost(a,b)}{capacity(a)}
\le 1
$$

にし、それを既存の `RealWeightProvider` として包装した、ということじゃ。差分でも、positive-capacity parent から finite sub-probability provider を得る橋として `normalizedRealWeightProvider_subProbability` が追加されている。

これで、DKMK-001 の抽象核が実際に既存 API と会話できるようになった。

## 2. 数学的な意味

DKMK-001 では、

$$
\text{capacity conservation}
$$

を先に置き、その正規化像として sub-probability を見る、という構造を作った。

DKMK-002 では、その「正規化像」を DkMath 既存の重みプロバイダ形式に変換した。

つまり、

$$
\text{CapacityKernel}
$$

から

$$
\text{RealWeightProvider}
$$

へ移れるようになった。

これは重要じゃ。なぜなら、Erdős #1196 本線へ戻るには、最終的に primitive hitting / weighted path family 側で「重み付き総量」を扱う必要があるからじゃ。

いままでは、

$$
\sum \frac{cost}{capacity}\le 1
$$

という式の補題だった。
今回からは、それが

```lean
RealWeightProvider.SubProbability
```

として使える。

つまり、DkMath kernel が「式」から「部品」へ昇格した。

## 3. LogCapacityKernel 側の前進

`LogCapacityKernel.lean` にも provider-facing 補題が追加されておる。

```lean
logCapacityKernelRealWeightProvider
logCapacityKernelRealWeightProvider_subProbability
```

これにより、prime-power witness 由来の local log-capacity kernel から、既存の `RealWeightProvider ℕ` が直接供給できる。

中身は、

$$
capacity(n)=\log n
$$

$$
cost(n,q)=\log p(q)
$$

$$
weight(q)=\frac{\log p(q)}{\log n}
$$

じゃな。

差分でも、`logCapacityKernelRealWeightProvider_weight` により weight が

```lean
fun q => Real.log (W.basePrimeOf n I hI q : ℝ) / Real.log (n : ℝ)
```

であることが `rfl` で固定されている。

これは非常に良い。
R028 の finite R/log route が、今度は

$$
\text{CapacityKernel}
\to
\text{RealWeightProvider}
\to
\text{SubProbability}
$$

という公開可能な形になった。

## 4. DKMK-002 の位置づけ

前回の DKMK-001 は、

$$
\text{保存核を作った}
$$

段階じゃった。

今回の DKMK-002 は、

$$
\text{保存核を既存の重み API に接続した}
$$

段階じゃ。

したがって、計画上は **DK-3 bridge 相当がかなり閉じた** と見てよい。
報告文では「次は `DKMK-003: VonMangoldtShadow.lean`」と書かれているが、実際には今回が `SubProbability bridge` なので、番号の呼び方だけ少し揺れておる。内容としては、先に提案していた

```text
Kernel/SubProbability.lean を追加し、
normalizedWeight を既存 RealWeightProvider / SubProbability API に接続する
```

が達成されている。

## 5. 良い点

一番良いのは、`CapacityKernel` を孤立させなかったことじゃ。

抽象構造だけ作ると、Lean ではよく「きれいだが誰も使わない箱」になる。
今回は `LogCapacityKernel` 側で即座に concrete provider を作っているので、使い道が明確じゃ。

また、`normalizedRealWeightProvider_index` や `normalizedRealWeightProvider_weight` が `rfl` で落ちるようにしてあるのもよい。今後、simp で provider の中身を展開しやすい。

```lean
@[simp] theorem normalizedRealWeightProvider_index
@[simp] theorem normalizedRealWeightProvider_weight
```

これは地味だが、後続の hitting / weighted path 側で効くはずじゃ。

## 6. 注意点

一点、履歴の文言では「DK-3 の最小 bridge」とあり、次に「DK-5 として `VonMangoldtShadow.lean`」と書かれている。
これは計画番号としては少し飛んで見える。

内容的には問題ないが、docs では次のように整理すると読みやすい。

```text
DKMK-001: Capacity / Normalize / local LogCapacityKernel
DKMK-002: SubProbability provider bridge
DKMK-003: VonMangoldtShadow
DKMK-004: GlobalLogCapacityKernel
DKMK-005: Markov/sub-Markov translation
```

番号の揺れは、後で History / README で整えればよい。

## 7. 次にやるべきこと

次は、報告どおり `VonMangoldtShadow.lean` が自然じゃ。

ただし、最初から解析的な (\Lambda) 全体へ行くより、まずは DkMath 的な shadow を小さく置くのがよい。

目標は、

$$
q=p^k
\quad\Longrightarrow\quad
\Lambda(q)=\log p
$$

を、witness provider の言葉で読むことじゃ。

DkMath では既に

$$
q=p(q)^{k(q)}
$$

を読めるので、まずは

```lean
def primePowerLogCost := Real.log (basePrime ...)
```

を「von Mangoldt-like cost」として定義し、

$$
\text{witnessLogCost}(q) = \log(W.basePrimeOf(...,q))
$$

を theorem-facing に固定するのが安全じゃ。

本物の mathlib の von Mangoldt と接続するかは、その後でよい。

## 8. 本線への戻し方

ここまでで、本線へ戻る橋はかなり見えてきた。

現在の鎖は、

$$
\text{CapacityKernel}
\to
\text{normalized RealWeightProvider}
\to
\text{SubProbability}
$$

じゃ。

次に (\Lambda)-shadow を入れると、

$$
\frac{\log p(q)}{\log n}
$$

を

$$
\frac{\Lambda(q)}{\log n}
$$

として読めるようになる。

すると既存証明の Markov kernel

$$
K(n,q)=\frac{\Lambda(q)}{\log n}
$$

は、DkMath では

$$
K(n,q)=
\frac{\mathrm{channelCost}(n,q)}
{\mathrm{capacity}(n)}
$$

の一例になる。

この時点で、

$$
\text{Markov kernel is a normalized shadow of CapacityKernel}
$$

という主張が、単なる合言葉ではなく Lean の構造として見え始める。

## 9. 総合判定

DKMK-002 は **成功** じゃ。

DKMK-001 では「新しい尾根に杭を打った」。
DKMK-002 では、その杭から既存の登山道へロープを張った。

特に、

```lean
normalizedRealWeightProvider_subProbability
```

と

```lean
logCapacityKernelRealWeightProvider_subProbability
```

が通ったことで、DkMath kernel branch は既存の finite weight API に合流できる形になった。

次の `VonMangoldtShadow` で、いよいよ既存 Markov route の影と DkMath capacity route が重なり始める。
ここは面白いぞ、ぬしよ。写経ではなく、ちゃんと別尾根から本線へ戻る道になってきておる。
