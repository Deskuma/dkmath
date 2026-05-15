# review

## "Markov kernel" だけで理解した！？

うむ。読んでおる。かなりちゃんと読んでやってくれておるぞい。
しかも、単なる写経ではなく、こちらの資料の **「Markov kernel を直接置かず、CapacityKernel を先に置く」** という核を正しく拾って、最初の実装に落としている。

## 1. 何を実装したか

今回の DKMK-001 では、まず新しい `DkMath.Kernel` 層が追加されておる。

主な追加は次じゃ。

```lean
DkMath.Kernel.Capacity
DkMath.Kernel.Normalize
DkMath.NumberTheory.PrimitiveSet.LogCapacityKernel
```

差分報告でも、`CapacityKernel`, `outgoingCost`, 正規化 weight、`PrimePowerWitnessProvider.logCapacityKernel`、そして normalized R/log theorem が追加されたと明記されておる。さらに `DkMath.Kernel`, `DkMath.NumberTheory.PrimitiveSet`, `DkMath` の aggregator import まで更新されておる。

これは、資料で言っていた

$$
\text{CapacityKernel}
\to
\text{Normalize}
\to
\text{LogCapacityKernel}
$$

の最初の流れそのものじゃ。

## 2. Codex は資料を読んでいたか？

結論としては、 **読んでいる可能性が高い** 。
理由は、実装が資料の Phase とかなり一致しているからじゃ。

資料では、DK-1 に `CapacityKernel`, `outgoingCost`, `outgoingCost_nonneg`, `outgoingCost_le_capacity` を置く、とされていた。実装もまさにその形で、`CapacityKernel` に `children`, `capacity`, `cost`, `cost_nonneg`, `outgoing_le` を持たせている。

また、DK-2 では `normalizedWeight`, `normalizedOutgoing`, `normalizedOutgoing_le_one` を置く計画だった。今回の `Normalize.lean` には、これらに加えて expression-level の `normalizedWeight_subProbability` まで入っておる。

さらに、DK-4 では `PrimePowerWitnessProvider.logCapacityKernel` を置き、channel set を \(I\)、capacity を `Real.log n`、cost を `Real.log (W.basePrimeOf ...)` とする予定だった。今回の `logCapacityKernel` はまさに、

```lean
children := fun _ => I
capacity := fun _ => Real.log (n : ℝ)
cost := fun _ q => Real.log (W.basePrimeOf n I hI q : ℝ)
```

という形になっておる。

これは資料を読まずに偶然出る形ではない。ちゃんと設計図を踏んでいる。

## 3. 数学的に何が閉じたか

今回閉じたのは、DkMath kernel の最小核じゃ。

抽象的には、

$$
\sum_{b\in children(a)} cost(a,b)\le capacity(a)
$$

という **容量保存・劣保存** を `CapacityKernel` として固定した。

そして \(capacity(a) > 0\) なら、

$$
\sum_{b\in children(a)}
\frac{cost(a,b)}{capacity(a)}
\le 1
$$

が従うことを `Normalize.lean` で示した。

さらに prime-power witness に対して、

$$
capacity(n)=\log n
$$

$$
cost(n,q)=\log p(q)
$$

と置き、

$$
\sum_{q\in I}
\frac{\log p(q)}{\log n}
\le 1
$$

を `logCapacityKernel_normalized_subProbability` として再表現した。

つまり、R028 で閉じた R/log route を、今度は

$$
\text{CapacityKernel}
\to
\text{Normalize}
\to
\text{SubProbability}
$$

という DkMath kernel API の形に包み直したわけじゃ。

## 4. どこが「DkMath らしい」か

ここがよい。

実装コメントにも、

> probability object ではなく、normalization は `DkMath.Kernel.Normalize` で供給する

という趣旨が入っておる。

これは、わっちらが話していた

$$
\text{Markov kernel is a normalized shadow of DkMath capacity kernel.}
$$

の方針そのものじゃ。

つまり、最初から Markov kernel を置いていない。
先に

$$
\text{capacity}
$$

$$
\text{cost}
$$

$$
\text{outgoing capacity bound}
$$

を置き、その後で正規化している。
これは既存証明の Markov route のコピーではなく、DkMath 側の保存核としての再構成になっておる。

## 5. ただし、まだ DK branch 全体は完了ではない

ここはやわらかく切り分けるぞ。

DKMK-001 は **最初の第一歩としては成功** 。
ただし、プロジェクト全体から見ると、まだ次が残っておる。

まず、DK-3 の `SubProbability` bridge はまだ完全には別ファイル化されていない。今回 `normalizedWeight_subProbability` は入ったが、既存 `RealWeightProvider` / hitting API へ接続する層は次課題として残っている。History にも次の課題として、normalized weights を既存 provider / hitting API へ接続する DK-3 bridge が挙げられておる。

次に、DK-5 の von Mangoldt shadow は未着手じゃ。資料では、prime-power label 上で cost と \(\Lambda\) の一致、つまり

$$
\Lambda(p^k)=\log p
$$

を theorem-facing にする予定だったが、今回そこまでは入っていない。

さらに、DK-6 の Markov / sub-Markov translation もまだ先じゃ。今回の kernel は **sub-Markov 的な影** を作った段階であって、遷移過程そのものや adjoint chain まではまだ入っておらぬ。

## 6. 実装順としての評価

面白いのは、DK-3 を完全に挟む前に、DK-4 の prime-power concrete kernel まで一気に進めている点じゃ。

これは悪くない。むしろよい判断じゃ。

抽象層だけ作ると空中戦になりがちだが、今回すぐに

```lean
PrimePowerWitnessProvider.logCapacityKernel
```

を作ったことで、`CapacityKernel` が本当に R028 route を包めることを検証している。

つまり、

$$
\text{抽象核}
$$

だけでなく、

$$
\text{実戦投入可能な concrete instance}
$$

まで同時に置いた。
これは第一歩として非常に強い。

## 7. 気になる点

一点だけ留意点を挙げるなら、`Capacity.lean` が `import Mathlib` から始まっているところじゃな。最初の実装としては構わぬが、後で import 最適化をするなら、`Finset`, `Real`, `BigOperators` 周りへ削れる可能性がある。

もう一点、今回の `CapacityKernel Unit ℕ` は「固定された \(n,I\) に対する local kernel」じゃ。これは資料でも最初は local kernel 推奨だったので正しい。
ただし次の段階では、親状態を `ℕ` にする global kernel へ拡張する余地がある。

$$
n \mapsto I(n)
$$

$$
capacity(n)=\log n
$$

$$
cost(n,q)=\log p(q)
$$

のようにすると、より Markov / flow 的な見通しが立つ。

## 8. 判定

わっちの判定はこうじゃ。

**Codex は資料をちゃんと読んでいる。**
少なくとも、設計資料の核である

$$
\text{Markov を先に置かず、CapacityKernel を先に置く}
$$

という思想を正しく実装しておる。

そして今回の DKMK-001 は、

$$
\text{DK-1}
+
\text{DK-2}
+
\text{DK-4 の最小 concrete bridge}
$$

まで到達した第一歩じゃ。
これはかなり良い出足じゃよ。

次の一手は、わっちならこう見る。

```text
DKMK-002:
  Kernel/SubProbability.lean を追加し、
  normalizedWeight を既存 RealWeightProvider / SubProbability API に接続する。
```

その次に、

```text
DKMK-003:
  VonMangoldtShadow.lean を追加し、
  prime-power witness cost = Λ(q) の影を固定する。
```

ここまで行けば、DkMath kernel branch は「面白い構想」から「既存 Markov route を別解釈する本物の道具」へ育つ。

よい第一歩じゃ、ぬしよ。
これはただの散歩ではない。新しい尾根に、最初の杭を打ったところじゃ。

---

## 解説

この `DkMath Kernel` branch は、Erdős #1196 形式化の本線から一度外れた **迂回路** に見えるが、実はかなりよい迂回路じゃ。わっちの評価では、これは「脱線」ではなく、 **本線へ戻るための抽象化トンネル** になる可能性が高い。

## 1. 評価：この再解釈は筋がよい

今回の DKMK-001 は、既存 Markov kernel route をそのまま写していない。

既存 route の中心はおおむね

$$
K(n,q)=\frac{\Lambda(q)}{\log n}
$$

だが、DkMath kernel route では先に

$$
\mathrm{cost}(n,q)
$$

$$
\mathrm{capacity}(n)
$$

を置き、

$$
\sum_q \mathrm{cost}(n,q)\le \mathrm{capacity}(n)
$$

を主語にしている。これは、以前の設計資料にある「最初は exact Markov / sub-Markov や \(\Lambda(q)/\log n\) へ行かず、代数的・構造的 spine を作る」という方針と一致しておる。

さらに、DkMath の Mass API 設計でも、最初から確率を置くのではなく、

$$
\sum \text{子の質量}\le \text{親の質量}
$$

という質量・分岐・劣保存則を先に置く方針が明記されていた。
だから `CapacityKernel` は、既存構想から見ても自然な抽象じゃ。

## 2. 今回の第一歩の位置づけ

DKMK-001 では、`CapacityKernel` が

```lean
children : α → Finset β
capacity : α → ℝ
cost : α → β → ℝ
cost_nonneg : ...
outgoing_le : ...
```

という形で実装された。さらに `Normalize.lean` で

$$
\sum_b \frac{cost(a,b)}{capacity(a)}\le 1
$$

を示す一般補題まで入っている。

これはつまり、

$$
\text{保存核}
\Longrightarrow
\text{sub-probability}
$$

を一般 API にした段階じゃ。

しかも `LogCapacityKernel.lean` では、R028 の具体 route に接続して、

$$
capacity(n)=\log n
$$

$$
cost(n,q)=\log W.basePrimeOf(n,I,hI,q)
$$

という concrete kernel まで入っている。

これは実に良い。抽象だけで宙に浮かず、すぐに既存の finite R/log theorem に接続している。

## 3. 本線から外した意味

ここで一度、本線から外した視点で見る。

Erdős #1196 本線の最終形は、

$$
\sum_{\substack{a\in A\ a > x}}\frac{1}{a\log a}
\le
1+O!\left(\frac{1}{\log x}\right)
$$

へ進むことじゃ。

だが、そこへ直接行くと、すぐに

* \(\Lambda\)
* Markov kernel
* adjoint chain
* truncated sub-Markov
* asymptotic estimate
* \(1/(a\log a)\)

が一斉に出てくる。

これは Lean 形式化では重い。
だから DkMath kernel route は、まずそれらを全部背負わず、

$$
\text{finite capacity conservation}
$$

だけを切り出した。

これは良い分離じゃ。
山頂へ一気に行くのではなく、荷物を小分けにして中継基地を作っている。

## 4. 本線へ戻すための橋

本線へ戻すには、次の対応表を明確に固定するのが大事じゃ。

| DkMath kernel      | Erdős #1196 本線                     |
| ------------------ | ------------------------------------ |
| `capacity n`       | \(\log n\)                           |
| `cost n q`         | \(\Lambda(q)\) または \(\log p(q)\)  |
| `normalizedWeight` | \(\Lambda(q)/\log n\)                |
| `outgoing_le`      | sub-Markov / sub-probability         |
| `outgoing_eq`      | Markov kernel                        |
| `children n`       | \(q\mid n\) の prime-power channel   |
| hitting API        | primitive set の antichain 評価      |

この表を Lean 側でも docs 側でも固定する。
すると、DkMath kernel は本線から外れた枝ではなく、 **本線の抽象上位層** になる。

## 5. 次の実装アドバイス

次は、いきなり von Mangoldt に行くより、まず `SubProbability` bridge を整えるのがよい。

### DKMK-002. `Kernel/SubProbability.lean`

目的は、

$$
CapacityKernel
\to
normalizedWeight
\to
RealWeightProvider / SubProbability
$$

を一般化することじゃ。

今は `normalizedWeight_subProbability` が expression-level で入っておる。次はそれを既存の `RealWeightProvider` や `RealWeightedPath` 系へ渡せる形にする。

候補はこう。

```lean
theorem CapacityKernel.normalizedProvider_subProbability
    (K : CapacityKernel α β)
    (a : α)
    (hcap : 0 < K.capacity a) :
    ...
```

ここで注意すべきは、既存 API が `Finset` と provider をどう持っているかに合わせることじゃ。
無理に新構造を押し込まず、「既存 provider を作れる wrapper」を目指すのがよい。

## 6. その次：von Mangoldt は shadow として入れる

DKMK-003 では、`VonMangoldtShadow.lean` がよい。

ただし、最初から mathlib の本格的な von Mangoldt 関数を探して結合しようとすると重くなるかもしれぬ。
まずは DkMath 内で prime-power witness 用の shadow を置く。

```lean
noncomputable def primePowerLogCost
    (p : ℕ) : ℝ :=
  Real.log (p : ℝ)
```

あるいは witness に対して、

```lean
def witnessLogCost := Real.log (W.basePrimeOf ...)
```

としておき、後で

$$
q=p^k
\Longrightarrow
\Lambda(q)=\log p
$$

と接続する。

ここで重要なのは、順序じゃ。

DkMath では

$$
q=p^k
\to p
\to \log p
$$

が主語。
\(\Lambda(q)\) は後から

$$
\Lambda(q)=\log p
$$

として現れる shadow。
この哲学を崩さぬ方がよい。

## 7. 本線に戻る最短ルート

本線に戻る最短ルートはこれじゃ。

### Step 1

`CapacityKernel` から normalized provider を作る。

$$
\sum \frac{cost}{capacity}\le 1
$$

### Step 2

`LogCapacityKernel` で R028 theorem を kernel API 経由で再証明する。

$$
\sum_{q\in I}\frac{\log p(q)}{\log n}\le 1
$$

### Step 3

`cost = Λ` の shadow theorem を追加する。

$$
q=p^k
\Rightarrow cost(q)=\Lambda(q)
$$

### Step 4

`children n` を \(I\) ではなく、より標準的な divisor / prime-power channel set にする。

$$
children(n)={q\mid q\mid n,\ q\text{ prime power}}
$$

### Step 5

outgoing が inequality ではなく equality になる条件を分ける。

$$
\sum_{q\mid n}\Lambda(q)=\log n
$$

に相当する形じゃ。

この Step 5 で、DkMath kernel は本線の Markov kernel と合流する。

## 8. 冒険路としての価値

この branch の価値は、既存証明を写さずに、

$$
\Lambda(q)/\log n
$$

を

$$
\frac{\mathrm{channelCost}(n,q)}
{\mathrm{capacity}(n)}
$$

の一例として見る点にある。

これにより、将来的には Erdős #1196 だけでなく、ABC や宇宙式側にも同じ kernel 構造を使える。

たとえば ABC 側では、すでに `CosmicFormula → Mass API → ValuationFlow → ABC Bridge` の spine が最小核として整ってきた、という評価があった。
そこへ `CapacityKernel` を合流させれば、

$$
\text{rad / supportMass}
$$

$$
\text{valuation load}
$$

$$
\text{primitive channel}
$$

を、同じ capacity / cost 言語で扱える可能性がある。

これが本当に面白いところじゃ。

## 9. 注意点

ただし、抽象化しすぎると危険じゃ。

`CapacityKernel` は強力だが、何でも入る箱にすると意味が薄れる。
だから当面は concrete instance を常に隣に置くべきじゃ。

今なら、

```lean
PrimePowerWitnessProvider.logCapacityKernel
```

がよい錨になっている。
次も抽象 theorem を追加したら、必ず `LogCapacityKernel` 側で使う。
この方針がよい。

## 10. わっちの推奨ロードマップ

進めるなら、こうじゃ。

```text
DKMK-002:
  Kernel/SubProbability.lean
  normalizedWeight を既存 RealWeightProvider / SubProbability API へ橋渡しする。

DKMK-003:
  LogCapacityKernel の theorem 整理
  R028 theorem との同値・wrapper・推奨入口を整理する。

DKMK-004:
  VonMangoldtShadow.lean
  prime-power witness cost = Λ(q) の shadow theorem を置く。

DKMK-005:
  GlobalLogCapacityKernel
  固定 I ではなく、n ごとの prime-power channel set へ拡張する。

DKMK-006:
  outgoing equality / Markov shadow
  equality なら Markov、inequality なら sub-Markov という翻訳層を置く。
```

## 11. 総合評価

この再解釈は、かなり有望じゃ。

本線から外れているようで、実は本線を抽象化している。

$$
\text{Markov kernel}
$$

を目的語にするのでなく、

$$
\text{capacity conservation}
$$

を主語にして、その正規化像として Markov / sub-Markov を見る。
これは DkMath の既存思想、すなわち「確率ではなく質量から始める」「分解と劣保存を先に置く」という方針に合っておる。

だから進めてよい。
ただし、必ず本線へ戻る橋を残すこと。

合言葉はこれじゃ。

$$
\boxed{
\text{Capacity first, Markov later.}
}
$$

この方針なら、冒険しながらも迷子にはならぬ。
ぬしよ、これは新しい尾根じゃ。りんごと葡萄酒を背負って登る価値があるぞい。
