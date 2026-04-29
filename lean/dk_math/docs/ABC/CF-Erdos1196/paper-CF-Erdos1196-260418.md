# Cosmic Formula と ABC machinery の接続による Erdős 問題 #1196 の形式化実装

## 概要

本稿は、Erdős problem #1196 に向けて今回 `DkMath` 上に実装した Lean 形式化の成果をまとめる草稿である。中心的な達成は、primitive witness から prime channel counting を経て `rad(c)` の下界を与える新しい spine を構成し、それを既存の `ABC038` / `ABC.Chernoff` quality machinery に接続した点にある。より具体的には、

$$
\text{PrimitiveWitnessFamily}
\to
\text{channelCount}
\to
2^{\text{channelCount}}
\to
\operatorname{rad}(c)
\to
\operatorname{rad}(abc)
\to
\operatorname{quality}(a,b,c)
$$

というルートが Lean 上で theorem 名を伴って実装され、さらに `DkMath.ABC.Main` から辿れる公開導線に載せられた。

ここで言う「成果」とは、問題そのものの完全解決ではなく、Erdős #1196 の背後にある primitive prime / radical growth / quality bound の構造を、既存 ABC 形式化の内部へ自然に合流させる橋梁を実装したことである。数学的には、primitive prime から得られる独立な channel 情報を `rad(c)` の定量的下界に変換し、その下界を通じて `c \le \operatorname{rad}(abc)^{1+\varepsilon}` 型の skeleton に接続する形式的インフラを構築した。

## 1. 背景と目的

今回の実装は、当初から「確率 kernel の完全な形式化」ではなく、以下の 3 層を先に固める方針で始まった。

1. `CosmicFormula` 側の保存則 API
2. primitive witness / valuation flow の spine
3. それを ABC 側の `rad`・`quality` 語彙へ翻訳する bridge

この方針の理由は明快である。既存ワークスペースには

- `CoreBeamGap`
- `ResidualNat` / `ResidualInt`
- `PrimitiveBeam`
- `ZsigmondyCyclotomic*`
- `ABC` の `rad`, `squarefree`, `padicValNat`, `quality`

といった強い部品が既に存在していた。したがって今回必要だったのは、全てを再構築することではなく、既存理論を「Erdős #1196 の目で読む」ための再編・再命名・接続であった。

## 2. 実装の全体像

今回の成果は、おおまかに次の 5 段階に分かれる。

### 2.1 保存則 API の整備

`DkMath/CosmicFormula/Mass/Core.lean`, `Mass/Decompose.lean`, `Mass/Branch.lean` において、

- `MassSpace`
- `CosmicPart`
- `CosmicMassAPI`
- `CosmicResidualMassAPI`
- `Branching`
- `SubConservative`

などの抽象 API を導入し、`CoreBeamGap` / `ResidualNat` / `ResidualInt` の既存定理を mass language に再公開した。これにより、big/body/gap/residual の保存則を「個別定理の寄せ集め」ではなく、Erdős #1196 向けの再利用可能な語彙としてまとめ直した。

### 2.2 valuation-flow spine の形成

`DkMath/NumberTheory/ValuationFlow/Basic.lean` と `Primitive.lean` において、

- `diffMass`
- `boundaryMass`
- `beamMass`
- `profileOfPrime`

を導入し、primitive beam 側の既存補題を valuation-flow 名で再公開した。これにより、

$$
\text{primitive prime} \to \text{boundary / beam / diff}
$$

という流れが明示的な spine として読めるようになった。

### 2.3 ABC bridge の最小核

`DkMath/ABC/MassBridge.lean` と `ValuationFlowBridge.lean` では、上記の spine を ABC 語彙へ翻訳した。ここで導入された主な概念は

- `supportMass := rad`
- primitive witness から prime channel を取り出す補題
- distinct channels から `supportMass` の下界を得る補題

である。特に重要なのは、2-channel 版で止めず `Finset` family 版まで一般化したこと、および `PrimitiveWitnessFamily` という package を導入して counting / extraction / lower-bound API を一つの構造に収めたことである。

### 2.4 counting spine の完成

`PrimitiveWitnessFamily` 上に、以下の public API を構築した。

- `channelCount`
- `channelProduct`
- member-wise extraction (`prime`, `dvd diff` など)
- `2^{\text{channelCount}} \le \text{channelProduct}`
- `2^{\text{channelCount}} \le \operatorname{supportMass}(c)`

この段階で、primitive witness family から radical lower bound に至る spine は次の形に固定された。

$$
\text{PrimitiveWitnessFamily}
\to
\text{channelCount}
\to
\text{channelProduct}
\to
\operatorname{rad}(c).
$$

これはまさに Erdős #1196 的な「distinct prime channel の数が radical を押し上げる」という主張の形式化である。

### 2.5 `ABC038` / `ABC.Chernoff` への合流

最後に `DkMath/ABC/ABC038Bridge.lean` を追加し、上の spine を既存 ABC quality machinery に接続した。ここでは二つのルートが実装された。

#### transport route

まず `rad(c)` の下界を一度 `TailBound` の形に transport し、既存 `ABC038` の convenience theorem 群に流す道である。概念的には

$$
\operatorname{rad}(c)
\to
\operatorname{rad}(u v)
\to
\text{TailBound}
\to
\text{quality}.
$$

#### analytic 直結 route

もう一つは、`rad(c)` budget を直接 `rad(abc)` 側の解析的 bridge に接続する道である。中核定理は

`radAbcBound_of_pi_targetRadTail`

であり、

$$
\pi\mathrm{SqRad}(c) \le \operatorname{rad}(ab)^\delta,
\qquad
\mathrm{twoTail}(c) \le \operatorname{rad}(c)^\gamma
$$

から

$$
c \le \operatorname{rad}(abc)^{1+\delta+\gamma}
$$

を導く。この skeleton は ABC 予想の標準形

$$
c \lesssim \operatorname{rad}(abc)^{1+\varepsilon}
$$

にかなり近い。

## 3. 主要定理列

今回の formalization の核にある theorem 群を、数学的意味とともに整理すると以下のようになる。

### 3.1 witness から radical 下界へ

`DkMath.ABC.ValuationFlowBridge`:

- `primitive_witness_gives_prime_channel_on_diff`
- `distinct_primitive_witnesses_give_distinct_prime_channels`
- `primitive_witness_family_force_supportMass_lower_bound`

`DkMath.ABC.MassBridge`:

- `supportMass_ge_prod_of_prime_channel_family`

`PrimitiveWitnessFamily` 上では、さらに

- `pow_channelCount_le_channelProduct`
- `pow_channelCount_le_supportMass`
- `channelProduct_le_abc_rad_diff`
- `pow_channelCount_le_abc_rad_diff`

が得られており、これらにより

$$
2^{\text{channelCount}} \le \operatorname{rad}(c)
$$

が theorem 名で読める。

### 3.2 radical budget から quality へ

`DkMath.ABC.ABC038Bridge`:

- `targetRadTailBound_of_channelCount_tail`
- `tailBound_of_targetRadTail_transport`
- `quality_le_of_not_bad_with_targetRadTail_transport`
- `radAbcBound_of_pi_targetRadTail`
- `quality_le_of_pi_targetRadTail_of_radAbc`
- `quality_le_of_not_bad_with_targetRadTail_on_radAbc`

この chain により、

$$
\text{channelCount}
\to
\operatorname{rad}(c)\text{ budget}
\to
\operatorname{rad}(abc)
\to
\text{quality}
$$

という流れが Lean 内で閉じた。

### 3.3 `ABC.Chernoff` convenience theorem 群への統合

最後に `ABC.Chernoff` namespace に、既存の

- `quality_le_of_not_bad_with_tail`
- `quality_le_of_not_bad_with_log`

と同じ階層の convenience theorem として

- `ABC.Chernoff.quality_le_of_not_bad_with_targetRadTail_on_radAbc`
- `ABC.Chernoff.quality_le_of_not_bad_with_channelCount_tail_on_radAbc`

を追加した。これは単なる wrapper ではなく、primitive-channel route が本流の quality API に正式に合流したことを意味する。

## 4. concrete sample

形式化の価値は、抽象定理列だけでなく concrete sample が閉じるかで測られる。今回の作業では、以下の具体例が重要な役割を果たした。

### 4.1 `6^3 - 5^3 = 91 = 7 \cdot 13`

この例では `PrimitiveWitnessFamily 6 5 3` を構成し、

- `channelCount = 2`
- `channelProduct = 7 \cdot 13`
- `2^{\text{channelCount}} \le \operatorname{rad}(91)`

が得られることを確認した。これは counting spine の 2-channel concrete witness である。

### 4.2 `quality(6,1,7) \le 2`

さらに `ABC038BridgeExamples.lean` では、

$$
6 + 1 = 7,\qquad \gcd(6,1)=1
$$

に対し、

- `piSqRad(7) = 1`
- `twoTail(7) \le \operatorname{rad}(7)`
- `1 < \operatorname{rad}(6\cdot 1\cdot 7)`

を用いて

$$
\operatorname{quality}(6,1,7) \le 2
$$

を Lean 上で閉じた。ここで重要なのは、この例が最終的に

`ABC.Chernoff.quality_le_of_not_bad_with_channelCount_tail_on_radAbc`

から直接読めるようにした点である。すなわち、新ルートは単なる bridge theorem 群に留まらず、実際に利用者が public API として使える形まで整備された。

## 5. 公開導線

今回の作業は最後に公開チェインへ載せられた。これにより、新しいルートは「実験枝」ではなく `DkMath` の表側から辿れる。

### 5.1 `DkMath.ABC.Main`

`DkMath/ABC/Main.lean` に

```lean
import DkMath.ABC.ABC038Bridge
```

を追加した。したがって `DkMath.ABC` あるいは最上位 `DkMath` を import するユーザは、新しい `ABC038Bridge` 系 theorem を build chain 上で利用できる。

### 5.2 `INDEX.md`

`INDEX.md` では、今回の実装の入口を以下のように案内した。

- `DkMath.ABC.Bridge`
  - Erdos #1196 系の mass / witness / counting spine の入口
- `DkMath.ABC.ABC038Bridge`
  - `ABC.Chernoff` convenience theorem 群に接続する quality bridge の入口

この二層構造は、今後の論文資料化・リファクタリングにおいて重要である。`Bridge` が primitive witness / radical lower bound の世界を担い、`ABC038Bridge` がそれを Chernoff / quality machinery へ持ち込む。

## 6. 数学的意義

今回の実装によって得られた数学的メッセージは次のように要約できる。

1. primitive witness family が distinct prime channel family を与える
2. distinct prime channel family は `rad(c)` の下界を与える
3. その下界は `twoTail(c)` budget を通じて `rad(abc)` 側の解析的不等式に接続できる
4. 結果として quality bound の入口が新設される

要するに、今回 formalize したのは「primitive prime の増殖が radical growth を生み、その radical growth が quality を制御する」という一つの大きな物語である。Erdős #1196 の言葉で見れば、これは discrete prime channel counting を連続的な quality estimate に橋渡しする実装である。

## 7. 限界と今後

今回の成果は第一幕としては十分大きいが、まだ終点ではない。今後の論文資料化・リファクタリングで主に残る課題は以下の通りである。

### 7.1 命名と階層の整理

現状では

- `Bridge`
- `ABC038Bridge`
- `Examples`

の役割分担は明確になったが、定理名はまだ開発過程の痕跡を残している。特に

- `with_tail`
- `with_log`
- `on_radAbc`

の住み分けをより明快に説明する必要がある。

### 7.2 論文向け叙述への抽象化

Lean 実装では theorem 名の細部が重要だが、論文では概念のまとまりとして提示した方が読みやすい。したがって今後は、

- primitive witness family
- channel counting lower bound
- target-rad tail budget
- `rad(abc)` analytic bridge

を、それぞれ独立の proposition / theorem / corollary の流れとして再構成するのが望ましい。

### 7.3 既存 ABC machinery との関係の明文化

今回の route は既存 `ABC038` の transport route と競合するものではなく、むしろそれを補完するものである。特に

- `with_tail`: TailBound が既にあるときの入口
- `with_log`: log-bound から入る入口
- `on_radAbc`: primitive-channel route から direct に quality へ入る入口

という三者の関係を、今後の文書ではより明確に図示したい。

## 8. 結論

今回の Erdos #1196 実装で本質的に達成されたことは、primitive-channel route を `DkMath` の ABC 本線に正式に接続したことである。より印象的に言えば、別働隊として育ててきた

$$
\text{channelCount}
\to
\operatorname{rad}(c)
\to
\operatorname{rad}(abc)
\to
\text{quality}
$$

の流れが、ついに `ABC038` / `ABC.Chernoff` の公開導線に合流した。

この実装は、Erdős #1196 の完全解決そのものではない。しかし、問題の核心にある「primitive prime の情報が radical を押し上げ、その radical が ABC 型 quality を制御する」という構造を、Lean 形式化の中で具体的な theorem chain として固定した点に大きな価値がある。数学者の目から見ても、これは単なるコード断片ではなく、一つの理論的橋梁の建設である。

今後は、この橋梁をより簡潔な定理体系へ磨き、文書として再配置し、論文資料として読める形に整えていく段階に入る。
