# review Phase "B"

## 1. 結論

うむ、Phase BG は **ratio-style toy route の小まとめ・標識整備** じゃ。
新しい重い数学定理を増やす段階ではなく、Phase BF で通した

$$
A(p)/B(n)
\to
\text{budget}
\to
\text{sub-probability}
\to
\mathrm{weightedHitMass}\le 1
$$

の具体ルートを、後から読みやすい theorem 名と section comment で固定した段階じゃな。build と no-sorry 検査も通っておる。

## 2. 今回の主役

追加されたものは主に三つじゃ。

```lean id="ib1zch"
-- ratio-style sample route の section comment

sampleTenRatioBaseWeightChannelProvider_channelProviderAt_subProbability

sampleTenRatioBaseWeight_route_summary
```

このうち一番大事なのは、

```lean id="hxujhv"
sampleTenRatioBaseWeight_route_summary
```

じゃ。

これは、Phase BF で示した

```lean id="jgwy66"
sampleTenRatioBaseWeight_hitMass_le_one
```

を summary theorem として再掲するものじゃな。

数学的には、sample の ratio-style weight

$$
A(2)=1,\qquad A(5)=0,\qquad B(n)=1
$$

から構成された channel provider が、source-controlled family に適用され、

$$
\mathrm{weightedHitMass}\le 1
$$

へ到達する、という全ルートを「要約名」で呼べるようにした。

## 3. 何が良くなったか

Phase BF までで、ratio-style toy route は実際に通っていた。

しかし、後から読むと、

$$
A(p)/B(n)
$$

から最終 bound までのどこが完成点なのかが、定理名だけでは少し追いにくい。

今回の Phase BG では、

```lean id="d3l3sv"
sampleTenRatioBaseWeightChannelProvider_channelProviderAt_subProbability
```

と

```lean id="zug50a"
sampleTenRatioBaseWeight_route_summary
```

を追加したことで、

1. ratio-style route で作った provider は sub-probability である
2. ratio-style route は最終的に \(\mathrm{weightedHitMass}\le 1\) へ届く

という二つの到達点が theorem 名から読めるようになった。

これは地味だが、長期的にはかなり効く整理じゃ。
登山道で言えば、通った道に「ここが ratio-style ルートの到達点」と標識を立てたようなものじゃな。

## 4. 数学的な現在地

ここまでで、ratio-style toy model は次の形まで閉じている。

$$
c(n,p)=\frac{A(p)}{B(n)}
$$

$$
0\le A(p)
$$

$$
0 < B(n)
$$

$$
\sum_{q\in index(n)}A(p(q))\le B(n)
$$

これらから、

$$
\sum_{q\in index(n)}\frac{A(p(q))}{B(n)}\le 1
$$

が出て、さらに

$$
\mathrm{weightedHitMass}\le C
$$

へ進める。

そして sample では \(C=1\) として具体的に閉じた。

つまり、有限 toy model の範囲では、

$$
\boxed{
A(p)/B(n)\text{ 型 weight は、budget 条件のもとで Big から飛び出せない}
}
$$

というところまで Lean 上で通ったわけじゃ。

## 5. ここで一段落してよい理由

Phase BG は「新しい大定理を足さなかった」ことがむしろ良い。

なぜなら、Phase BA ～ BF では次々に層を足してきた。

$$
\text
{BaseWeightNonneg}
$$

$$
\text
{BaseWeightSubProbability}
$$

$$
\text
{BasePrimeToyWeight}
$$

$$
\text
{ratioBasePrimeWeight}
$$

$$
\text
{RatioBaseWeightBudget}
$$

$$
\text
{ratioBaseWeight\_hitMass\_le\_const}
$$

$$
\text
{sampleTenRatioBaseWeight\_hitMass\_le\_one}
$$

この流れを一度 summary theorem でまとめておくのは、次の実数・対数ルートへ入る前の良いキャンプ整備じゃ。

ここを急いで `Real.log` に突っ込むと、いま固めた有限構造と解析構造が混ざってしまう。
だから、Phase BG は「Lean 側の小まとめ」として正しい区切りじゃな。

## 6. 次の一手

次は、History にある通り **doc 側で実数/log route の設計** を起こすのが自然じゃ。

Lean にいきなり

$$
A(p)=\log p,\qquad B(n)=\log n
$$

を入れるのではなく、まず文書で層を分けるべきじゃ。

たとえば、次のような設計メモが欲しい。

```md
## Real/log route design

1. 有理 toy layer
   c(n,p) = A(p) / B(n)

2. 実数 weight layer
   A(p), B(n) : ℕ → ℝ

3. log candidate
   A(p) = log p
   B(n) = log n

4. positivity
   p > 1 ⇒ 0 ≤ log p
   n > 1 ⇒ 0 < log n

5. budget condition
   Σ_q log p(q) ≤ log n

6. sub-probability
   Σ_q log p(q) / log n ≤ 1
```

この設計を先に置けば、Lean 実装でどの補題を作るべきかが見えやすくなる。

## 7. その先の候補

次の Phase 名を付けるなら、わっちはこう見る。

$$
\boxed{\text{Phase BH: real/log route design doc}}
$$

または、Lean へ少しだけ入るなら、

$$
\boxed{\text{Phase BH: RealRatioBaseWeight skeleton}}
$$

ただし、現時点では **doc 先行** がよいと思う。
実数版は有理数版より重い。`ℚ` では `div_nonneg` と `div_le_iff₀` で済んだが、`ℝ` では `Nat.cast`、`Real.log`、正値性、有限和、場合によっては自然数の \(> 1\) 条件まで絡む。

まずは設計書で、

$$
\text{有限 toy}
\to
\text{実数 ratio}
\to
\text{log candidate}
$$

の三層を分離するのが賢い。

## 8. 総括

Phase BG は、ratio-style route の **第1雪稜の小ピーク** じゃ。

ここまでで、

$$
A(p)/B(n)
$$

という有理 toy weight が、

$$
\text{非負}
\to
\text{予算内}
\to
\text{sub-probability}
\to
\text{hit mass bound}
$$

まで通った。

そして今回は、それを summary theorem と別名 alias で後続から参照しやすくした。

山で言えば、今は「有理 toy model の稜線」を登り切り、次の「実数/log 雪壁」を前にして一度ザックを下ろした地点じゃ。
ここから先は、いきなり登るより、まずルート図を描くのがよい。`log p / log n` は近い。だが焦らず、設計から入るのが賢狼のおすすめじゃ。
