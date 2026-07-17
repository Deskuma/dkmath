# Live: Petal No.336 cp

## 作業実況

### 336-01

generic 層は通過し、重要な事実が一つ固定されました。同じ個数を残す任意の assignment と比較して、FIFO はすべての cutoff で「新しい側に残る要素数」を最大化します。また cardinality 1 のまま age が無限増大する抽象 queue を証明し、queue boundedness と age boundedness の一般的同値を明確に否定しました。これを基礎に source-age flow 本体を追加します。

---

おお、**順調じゃ。しかも重要な二点を先に固定してから本体へ入っている。**

特に、

> FIFO はすべての cutoff で「新しい側に残る要素数」を最大化する

これは、先ほどの「最古 source を最大化する」より強い。単一の最小値だけでなく、**全 cutoff に対する分布優越**まで取れたということじゃ。FIFO queue が historical claims の newest upper tail であることを、別角度から完全に支えている。

そして、

> cardinality 1 のまま age が無限増大する抽象 queue

もよい regression じゃ。

これで、

```text
queue boundedness ≠ age boundedness
```

が一般論として正式に切り離された。今後、source-age bound を queue bound の言い換えとして循環利用する事故を防げる。

ここから source-age flow 本体で見るべき核心は二つじゃ。

```text
old carrier の一段増分
=
新たに horizon を越えた claim carrier
```

```text
deficit の一段増分
=
horizon crossing 数 - actual consumed 数
```

そして何より、負の deficit を `Nat` で $0$ に潰さず、**過去に先払いされた consumption credit として `Int` のまま保存できるか**。

この live 文面を見る限り、Codex はこちらの意図をかなり正確につかんでおる。
いよいよ静的な同値 API ではなく、残る未証明命題そのものの運動方程式へ入ったぞい。🐺👍️

### 336-02

基礎層は対象ビルドを通過しました。ここで確定したのは、期限切れ outstanding の個数が signed deficit の正部分と完全一致し、uniform age が frontier increment の全 prefix 非正性と同値になることです。次は指示末尾の条件付き certificate と saturated branch を、既存の有限遷移 API に沿って追加します。

---

おお、**source-age flow の心臓部まで通った**のぉ。

今回確定した第一の事実は、

$$|\operatorname{ExpiredOutstanding}_H(m)|=\operatorname{Int.toNat}!\left(\operatorname{SourceAgeDeficit}_H(m)\right)$$

じゃ。

つまり signed deficit の正部分は、単なる数値超過ではない。

> **期限 $H$ を越えて、なお実際に FIFO queue に残っている source identity の個数**

そのものになった。

これで、

```text
deficit > 0
```

は抽象的な警報ではなく、actual expired carrier が非空であることを意味する。負の deficit は、期限切れ claim が存在しないだけでなく、将来の horizon crossing を吸収し得る先払い credit として保持される。

第二の事実はさらに大きい。

$$\operatorname{UniformAge}(H)\iff\forall m,\ \sum_{k<m}\operatorname{FrontierIncrement}_H(k)\le0$$

ここまで来ると、残る命題は完全に signed-flow 問題じゃ。

```text
horizon を越えて old 側へ入る claim 数
-
その block で実際に消費される claim 数
```

を一段 weight として、その全 prefix sum が正へ出ない $H$ を見つければよい。

## Certificate 監査で最も重要な点

ここから追加する finite-transition certificate は、以前の queue certificate より条件が厳しい。

単に、

$$\sum_{k<m}\operatorname{FrontierIncrement}_H(k)\le C$$

を得ても、source age は閉じない。

必要なのは、

$$\sum_{k<m}\operatorname{FrontierIncrement}_H(k)\le0$$

じゃ。

したがって potential certificate には、通常の edge inequalityだけでなく、

$$\Phi(\sigma_m)\le\Phi(\sigma_0)$$

を canonical reachable statesについて保証する構造が要る。

例えば、

```text
actual frontier increment
  ≤ Φ(next signature) - Φ(current signature)

かつ

Φ(reachable signature) ≤ Φ(initial signature)
```

という二層が必要になる。

potential が有限範囲にあるだけなら、得られるのは有限上界であって非正性ではない。この境界は次の実装で厳しく見るところじゃ。

## Saturated branch の攻め方

saturated branch で pointwise に、

$$\operatorname{FrontierIncrement}_H(m)\le0$$

まで言えれば最強じゃが、毎 block で horizon crossing と consumption が同期するとは限らぬ。

その場合は、

$$\sum_{j=0}^{L-1}\operatorname{FrontierIncrement}_H(m+j)\le0$$

という固定短窓 discharge theorem が本命になる。

特に注意すべきは、

```text
actual consumption
```

と、

```text
available service / capacity
```

を混同しないことじゃ。

capacity が存在しても queue と新 demand が足りなければ unused service になる。ゆえに saturated branch から consumption を取り出すには、

```text
old claim が実際に available queue に存在する
→ service slot がそれを FIFO で消費する
```

まで繋ぐ必要がある。

この live 報告は非常に良い。

generic queue 理論も carrier bookkeeping も終わり、現在 Codex はついに、

> **期限境界を越える claim の流入と、actual repayment の競争**

そのものを Lean に載せ始めておる。これはもう周辺整備ではなく、未証明本体への直接攻撃じゃ。🐺🔥

### 336-03

Stage J と K も対象ビルドを通過しました。監査結果は重要で、H = 0 の saturated block は crossing が 2、actual consumption が 1、したがって frontier increment は厳密に +1 です。つまり「各ブロックで常に非正」を狙う証明は既に反例を持ち、正の horizon または複数ブロック amortization が必須だと確定しました。公開 import と checkpoint report を同期し、全体ゲートへ進みます。

---

おお、これは**非常に価値の高い反例確定**じゃ。

$$\operatorname{FrontierIncrement}_{0}(m)=2-1=1$$

つまり saturated block では、

* age horizon を越える claim が $2$ 件
* 実際に消費される claim が $1$ 件
* 差し引き $+1$

となる。

これで次の単純戦略は正式に死亡した。

```text
すべての block で frontier increment ≤ 0
```

しかし、source-age route 自体が倒れたわけではない。uniform age に必要なのは各項の非正性ではなく、

$$\forall m,\ \sum_{k<m}\operatorname{FrontierIncrement}_{H}(k)\le0$$

という**全 prefix の非正性**じゃ。

したがって $+1$ block が存在しても、その前に蓄積された負の consumption credit、または後続 block を含む固定窓 repayment により相殺できる。

今回の結果から、攻め筋は二つに絞られた。

### 正の horizon

$H>0$ では crossing claim は現在 block の demand ではなく、$H$ source-time 前に生まれた claim になる。現在の saturated growth と crossing の発生時刻がずれるため、$H=0$ の $+1$ obstruction はそのまま残らない。

### 複数 block amortization

例えば saturated block の $+1$ に対し、後続 block が $-1$ 以下を供給して、

$$\sum_{j=0}^{L-1}\operatorname{FrontierIncrement}_{H}(m+j)\le0$$

を証明する道じゃ。

これは以前構築した、

* saturated successor classification
* length-one successor repayment
* predecessor/successor pair drift
* valuation-one tight branch

と接続できる可能性が高い。ただし以前の endpoint drift と今回の frontier increment は別量なので、同じ theorem をそのまま流用せず、対応式を作る必要がある。

そして certificate 側も、正 edge の存在を許さなければならない。必要なのは edge ごとの非正 potential ではなく、

```text
正の increment
→ 有限状態の debt 上昇
→ 後続状態で必ず同量以上の下降
→ 初期 potential を越えない
```

という amortized transition structure じゃ。

実に良い進展じゃ。
**最も簡単な誤った証明路を Lean が明確に切り落とし、正の horizon または時間窓 amortization だけを生存させた。** 全体ゲート後の report はかなり重要な checkpoint になるぞい。

---
