# 考察 Note No.046

## エルデシュ問題 1196 と 相対多角数 Petal の接続

> 👩‍⚕️D.:

そう言えば、エルデシュ問題#1196 登頂もまだだったわねぇ。途中で寄り道して Petal を構築した。
エルデシュ問題から Petal を見たら何が見えるか？逆に、Petal から見た場合。
新たな視点から何か得られるか？

> 🐺賢狼:

うむ。見える。かなり見えるぞい。
寄り道して Petal を作ったのは、実は **Erdős #1196 の有限構造側を“見える化”するための寄り道** だった、と読める。

## 1. Erdős #1196 から Petal を見ると

Erdős #1196 側の主語は、

$$
\text{primitive set}
\to
\text{divisibility chain}
\to
\text{hitting mass}
\to
\text{log capacity}
$$

じゃった。既に DkMath では、解析本丸の

$$
\sum_{a\in A}\frac{1}{a\log a}
\le 1+O!\left(\frac{1}{\log x}\right)
$$

までは閉じていないが、その手前の有限 R/log route、つまり prime-power witness (q=p^k) から

$$
\sum_{q\in I}\frac{\log p(q)}{\log n}\le 1
$$

を出す中核は一つ登頂済みと整理されている。

この観点から Petal を見ると、Petal はこう見える。

```text
Erdős 側:
  q = p^k は下降過程の channel

Petal 側:
  q は GN 面に載る観測点 / carrier
```

つまり Petal は、Erdős route の **抽象的な channel (q=p^k)** に、幾何的な居場所を与える。

Erdős では、

$$
n\mapsto \frac{n}{q}
$$

という下降遷移が主語。
Petal では、

$$
(x+u)^d-u^d=x,GN_d(x,u)
$$

の中で、primitive (q) が boundary ではなく GN 側に載ることが主語になる。

これは大きい。
Erdős の channel は「どこへ流れるか」だけを見るが、Petal は「どの面に現れたか」を見る。

## 2. Petal から Erdős #1196 を見ると

Petal 側から見ると、Erdős #1196 はこう見える。

```text
Petal:
  GN / GTail 上の primitive carrier を追う

Erdős:
  それら carrier の log cost 総量が 1 を超えないことを示す
```

つまり、Petal の `AnchoredGNCarrier` は、Erdős 的には **log capacity を消費する子チャネル** じゃ。

$$
q=p^k
$$

が GN 上に載るなら、その base prime (p) は cost

$$
\log p
$$

を持つ。親 (n) の容量は

$$
\log n
$$

だから、

$$
\sum \log p(q)\le \log n
$$

が capacity 保存則になる。これは DkMath Kernel Project で「Markov kernel は DkMath capacity kernel の正規化された影」と整理されている視点そのものじゃ。

Petal から見た Erdős は、もはや「確率過程」ではなく、

```text
GN 上に出現する carrier 群の log 質量が、
親構造の log capacity を超えない
```

という局所幾何＋容量の命題に見える。

## 3. 新しく得られる視点

一番大きい新視点はこれじゃ。

**primitive set の antichain 性を、Petal address の非衝突性として読めるかもしれない。**

Erdős では、primitive set は divisibility chain 上で高々一度しか hit しない。DkMath でも、この primitive hitting から

$$
\mathrm{hitMass}\le \mathrm{sourceMass}
$$

型の有限評価が整備され、その後 weighted path family まで拡張されたと整理されている。

Petal では、primitive witness が GN 面のどこに載るか、つまり carrier / address が見える。

ならば、次の橋が狙える。

```text
primitive set の非比較性
  = divisibility chain 上の非衝突

Petal address の非衝突
  = GN carrier address 上の非重複
```

これが通るなら、Erdős の hitting mass は Petal 上で

```text
carrier family の非交差質量
```

として読める。

これはかなり DkMath らしい。
抽象的な「割り切り禁止」を、Petal の「観測面上で重ならない」として見るわけじゃ。

## 4. Petal が補えるもの

Erdős route だけだと、(q=p^k) はただの prime-power divisor channel じゃ。

だが Petal を通すと、(q) は次の情報を持つ。

```text
q は boundary を避ける
q は GN に載る
q は AnchoredGNCarrier になる
body diff の padicValNat は GN 側で読める
```

これは最近の `Petal.BezoutBridge` / Zsigmondy handshake と一致しておる。

Erdős route にとって、この追加情報は「局所 load の意味」を与える。
単に

$$
\log p
$$

を消費するのではなく、

```text
どの GN surface の
どの carrier が
どれだけ local load を持つか
```

を追えるようになる。

特に multiplicity では効く。

Erdős R/log route では、同じ base prime (p) が何度も現れる場合、exponent slot で管理した。
Petal 側では、これは

```text
同じ prime carrier が
GN 面上で何段 lift しているか
```

に見える。

つまり、

```text
Erdős の exponent slot
  ↔
Petal の local load / no-lift / squarefree GN
```

という対応が出る。

## 5. Erdős が Petal に与えるもの

逆に、Erdős は Petal に **大局的な上界原理** を与える。

Petal だけだと、

$$
q\mid GN
$$

や

$$
v_q(\text{body diff})=v_q(GN)
$$

のような局所観測が中心になる。
だが Erdős は、

$$
\sum \text{cost}\le \text{capacity}
$$

という全体上界を持ってくる。

だから Petal にとって Erdős は、

```text
局所 carrier が増えすぎない理由
```

を与える。

この視点は、FLT / ABC にも効く。
DkMath の #1196 実装計画でも、最初から exact Markov kernel や漸近評価へ行かず、`Big = Body + Gap`、primitive prime、GN、`padicValNat`、ABC bridge という構造 spine を先に作る方針だった。

Petal はその spine をより幾何的にしたものじゃな。

## 6. 次に狙うべき実装

わっちなら次は、Erdős と Petal の合流ファイルを作る。

候補名はこれ。

```text
DkMath.Petal.ErdosBridge
```

または NumberTheory 側なら、

```text
DkMath.NumberTheory.PrimitiveSet.PetalBridge
```

最初に入れる命題は、強い theorem ではなく **翻訳 API** でよい。

```lean
structure PetalLogCarrier (n d x u q : ℕ) : Prop where
  carrier : AnchoredGNCarrier q d x u q
  primePowerWitness : ∃ k, 0 < k ∧ q = basePrime ^ k
  costPrime : Nat.Prime basePrime
```

ただし最初から structure にしすぎると重い。
薄く始めるなら、こういう theorem bundle がよい。

```lean
theorem zsigmondyCarrier_logChannel
    ...
```

意味は、

```text
Zsigmondy primitive divisor
  -> GN carrier
  -> base prime channel
  -> log cost candidate
```

じゃ。

その次に、

```lean
theorem petalCarrierFamily_logSubProbability
```

を目標にする。

これは既存 R028 の

$$
\sum_{q\in I}\frac{\log p(q)}{\log n}\le 1
$$

を、Petal carrier family の言葉で再輸出するだけでよい。

## 7. 研究として一番おいしい仮説

ここが新視点じゃ。

**Erdős #1196 の primitive set 条件は、Petal carrier address の antichain 条件に置き換えられるかもしれない。**

もし Petal address が十分よく設計できれば、

$$
a\nmid b,\quad b\nmid a
$$

という primitive 条件を、より構造的に

```text
carrier address が同じ下降枝に乗らない
```

として扱える。

そのとき、Erdős の hitting theorem は、

```text
Petal carrier address family is source-controlled
```

という形になる。

これは面白い。
なぜなら、最終的に欲しい解析重み

$$
\frac{1}{a\log a}
$$

へ行く前に、Petal address 上で有限近似の構造をかなり細かく観測できるからじゃ。

## 8. 暫定結論

Erdős から Petal を見ると、

```text
Petal は prime-power channel の幾何的所在地
```

に見える。

Petal から Erdős を見ると、

```text
Erdős は GN carrier 群の log capacity 保存則
```

に見える。

そして二つを合わせると、

```text
primitive set
  = divisibility chain の antichain

Petal carrier family
  = GN address 上の antichain

Erdős mass bound
  = carrier log cost の subProbability
```

という新しい絵が出る。

だから、寄り道ではなかった。
Petal は、Erdős #1196 の有限構造を **見える面** に変換するための観測器じゃ。

次の一手は、

```text
Petal carrier family
  -> log cost
  -> SubProbability
  -> hitting mass
```

この橋を作ることじゃな。
ここまで来ると、Erdős #1196 登頂ルートは「確率過程の模倣」ではなく、DkMath 独自の **carrier / capacity / address route** として登れる。わっちは、この道がかなり好きじゃよ。
