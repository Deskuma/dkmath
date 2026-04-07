# Stage 1 → Stage 2 の接続状況の確認と、次の作業方針の提案

うむ、確認した。
**結論から言うと、Stage 1 は “構造的にはほぼ完了”、ただし “pack-specialized な最終出口” はまだ未完** じゃ。

最新の同期コメントでは、現在の実際の open は **Stage 1 の存在形 boundary target** と **Stage 3 の norm descent** に寄っている、と明示されておる。つまり、ぬしの報告の方向は概ね正しい。
さらに最新差分では、Stage 1 から existence boundary へ戻す generic 接続として

* `idealIsCoprime_prod_of_forall`
* `span_singleton_finset_prod`
* `chosenLinearFactor_isCoprime_with_tail_of_firstCase_of_pack`
* `cyclotomicLinearFactorIdealPthPower_of_tailFactorCoprimeRoute`
* `cyclotomicLinearFactorIdealPthPower_of_exponentAgreementAndPairwiseUnitWitness`

が入り、**generic bridge 自体は mainline に乗った** と読める。

ただし同じ報告の中で、**first-case から ring-of-integers specialization をそのまま existence boundary へ落とす直結 theorem は、elaborator heartbeat が重く compile-safe ではなかった** と明記されておる。
だから、Stage 1 を「完了」と言うなら、正確には

$$
\boxed{
\text{coprimality leg は完了、generic bridge も完了、だが direct specialization の最終 1 本は未安定}
}
$$

じゃよ。

## 状況分析

いま揃っているものは、かなり強い。

まず deep cyclotomic 側は、既に

* `primeOverPEqualsZetaMinusOne_fill`
* `integerInZetaMinusOneIdealDivisibleByP_fill`

まで concrete に埋まっておる、というのが最新のコメント同期の認識じゃ。

そのうえで今回、chosen factor と full tail の coprimalityまで actual first-case pack から落とす wrapper が入り、さらに 2-factor route から existence boundary を返す generic theorem も mainline に追加された。つまり **Stage 1 の数学的素材は揃っている **。
残っているのは、** その素材を 1 本の direct specialization theorem にまとめると Lean が重くなる**、という実装上の壁じゃ。

ゆえに、ぬしの問いに端的に答えると、

* **Stage 1 の数学内容** は、ほぼ終わっている
* **Stage 1 の compile-safe な最終包装** は、まだ終わっていない
* **残り作業は報告どおりか** と問われれば、**ほぼその通り**
  ただし「Stage 1 finished」とはまだ言い切らず、**Stage 1 final wrapper の軽量化が先** と言うのが正確じゃ

となる。

## maxHeartbeats の原因についての推論

ここは断言ではなく、わっちの推論じゃが、原因はかなり見えておる。

**重いのは数学ではなく elaboration じゃ。**
なぜなら、最新報告では generic bridge 側は build を通しており、重いのは **ring-of-integers specialization を直接 1 本にまとめたとき** だけだと書かれておるからじゃ。

つまり、重さの中心はおそらく次の組合せじゃ。

* `Finset.range p` と `(erase 1)` を含む大きな積
* `Ideal.span` の有限積と `simpa` による式変形
* `CyclotomicLocalFactorizationContext`、`IsPrimitiveRoot`、`𝓞 K`、`PrimeGe5CounterexamplePack` の暗黙引数推論
* 最後に generic theorem へ一気に流し込む dependent な application

要するに、**巨大な目標式を 1 発で elaborator に解釈させている** のが苦しいのじゃ。
とくに latest diff の説明そのものが、「final step of the argument」で heartbeat が溢れた、と言っておるので、ボトルネックは最後の generic theorem 適用付近と見てよい。

## 作業指示

わっちなら、次は **「重い 1 本を仕留める」ではなく、「重い 1 本を 3 本へ割る」** 方針で行く。

### 1. direct specialization theorem は一旦あきらめて、最終 1 手前を明示する

狙いは、いま重いと見えている

$$
\texttt{chosenLinearFactorSpanEqPow\_of\_firstCase\_of\_pack}
$$

相当を、その場で全部証明しようとしないことじゃ。
代わりに、最後の generic theorem の入力を **先に theorem 化** する。

具体的には、まず別 theorem として

$$
\operatorname{span}(\text{chosen}) \cdot \operatorname{span}(\text{tail}) = \operatorname{span}(x)^p
$$

を返す theorem、ついで

$$
\operatorname{IsCoprime}(\operatorname{span}(\text{chosen}),\operatorname{span}(\text{tail}))
$$

を返す theorem、さらに

$$
\operatorname{span}(x)\neq \bot
$$

を返す theorem を、**actual first-case specialization の名で個別に固定** するのじゃ。

ここまで小分けにすれば、最後は generic theorem への `exact` だけになる。
elaborator が苦しむのは大きな式変形の同時解釈じゃから、ここを分離するのが効く。

### 2. `simpa` を減らし、型を固定する

今回の重さは、おそらく `simpa [factor] using ...` や `calc` の中で
$$
\prod j \in (Finset.range p).erase 1, \cdots
$$
を何度も展開していることにもある。

だから、`factor` や `ctx` を theorem の外側に出すというより、**theorem ごとに目標型を固定した `have hMulIdeal : ...`、`have hTailCoprime : ...`、`have hXne : ...` を先に作る** のがよい。
最後は

```lean
exact linearFactorSpanEqPowOfTailMulEqSpanPowAndIsCoprime
  ctx hXne hMulIdeal hTailCoprime
```

の形に寄せる。
ここで `simpa` より `show ...` と `exact` を増やす方が、heartbeat には効きやすい。

### 3. public target 側は後回しにする

いま `CyclotomicIdealPthPowerTarget` そのものを finished にしたい気持ちは分かるが、**まずは direct specialization の 1 本を compile-safe にするのが先** じゃ。
public target への昇格は、その後でよい。
最新コメントでも「現実の残 open は Stage 1 の存在形 boundary target と Stage 3」と整理されておるので、順番としては正しい。

## 提案

わっちの提案を一行で言うぞい。

$$
\boxed{
\text{次は Stage 1 を “finished” と宣言しに行くのでなく、}
\text{heartbeat を起こしている direct specialization を 3 本の軽い補題へ分解して潰す}
}
$$

具体的な順はこれじゃ。

1. `chosen × tail = (x)^p` の actual theorem
2. `chosen ⟂ tail` の actual theorem
3. `(x) ≠ ⊥` の actual theorem
4. それらを generic theorem へ `exact` で流す極薄 wrapper
5. その wrapper を existence boundary と Stage 2 へ接続
6. その後に Stage 3 へ進む

## 最終判定

いまの時点では、

$$
\boxed{
\text{Stage 1 は “ほぼ完了” だが、まだ “完了” と言い切るのは早い}
}
$$

じゃ。
**報告の方向は正しい。残り作業も、ほぼ報告どおり。**
ただし、次にやるべき作業は Stage 3 に飛ぶことではなく、**heartbeat を起こしている direct specialization の軽量化を片付けて、Stage 1 finished を theorem で確定すること** じゃよ。
