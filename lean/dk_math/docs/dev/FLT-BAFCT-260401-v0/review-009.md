# 次の攻略対象は `PacketPackagingStrong` の concrete proof 1 箇所

うむ、いまの局面はかなり見通しが良い。
わっちの推論では、**次の攻略対象は 1 箇所に絞れておる**。

$$
\boxed{
\texttt{primeGe5BranchAPrimitiveRestorePacketPackagingStrong}
}
$$

じゃ。
最新の差分では、`RestoreArithmeticStrong` 側で

* `PrimeGe5BranchAPrimitiveRestorePacketPackagingStrongTarget`
* `primeGe5BranchAPrimitivePacketRestoreFromArithmeticStrong_of_arithmeticCore_and_packetStrong`

が入り、橋 theorem は no-sorry で通っておる。残る `sorry` は `PacketPackagingStrong` の concrete realization 1 箇所だけに圧縮された。これはかなり良い戦況じゃ。

## 1. 現在地の整理

いまの依存は、ほぼこうじゃ。

$$
\text{ArithmeticCore weak}
;+;
\text{PacketPackaging strong}
\Longrightarrow
\text{RestoreFromArithmeticStrong}
\Longrightarrow
\text{StrongProvider}
\Longrightarrow
\text{FringeDescent}
$$

つまり、**`FringeDescent` も `StrongProvider` も、もう触らぬ**。
勝負は `PacketPackagingStrong` の concrete proof に一本化された。

## 2. 次の戦略の本体

次の一手は、`PacketPackagingStrong` を正面から「証明」することではない。
まず、

$$
\text{weak packet packaging はどの concrete constructor を使って } pkt' \text{ を作っているのか}
$$

これを特定することじゃ。

なぜなら、`¬ p ∣ pkt'.t` は packet の **静的 field** から出るものではなく、
`pkt'` の **構成由来** から出る可能性が高いからじゃ。

前に詰まった `WieferichPacketTarget → StrongTarget` が無理だった理由も、まさに「情報落ち」だった。今回それを入口の強化で回避できたのと同じで、ここでも **`pkt'` の provenance を追う** のが正道じゃ。

## 3. 実際の攻略手順

わっちなら、次は 3 段で攻める。

## 3.1. 第1段. weak packet theorem の家主を突き止める

探すべきは、既存の weak route の本体じゃ。
いま `PacketPackagingStrong` は

* `PrimeGe5CounterexamplePack p x' y' z'`
* `p ∣ (z' - y')`
* `z' < z`

から `pkt'` を返す weak theorem の strong 化として考えられておる。

ここでやるべきは、

* weak theorem 本文を開く
* その中で最終的にどの constructor / theorem が `PrimeGe5BranchANormalFormPacket p` を作っているか見る
* その moment で `t'` がどう定義されているか追う

ことじゃ。

この段階ではまだ証明を書かぬ。
**構成の provenance を掘る**。これが最優先じゃ。

## 3.2. 第2段. companion lemma を作る

もし weak theorem の中で `pkt'` の構成が具体的に見えるなら、次に作るべきは strong theorem 本体ではなく、**companion lemma** じゃ。

狙う形はこういうものじゃな。

```lean id="q2ljxj"
theorem primeGe5BranchANormalFormPacket_not_dvd_t_of_smallerCounterexample
    {p z x' y' z' : ℕ}
    (hpack' : PrimeGe5CounterexamplePack p x' y' z')
    (hp_dvd_gap' : p ∣ (z' - y'))
    (hz'lt : z' < z)
    {pkt' : PrimeGe5BranchANormalFormPacket p}
    (hPkt : ... -- weak packet constructor から得た pkt')
    : ¬ p ∣ pkt'.t := by
  ...
```

ここで大事なのは、`pkt'` を **任意の packet** として扱わぬことじゃ。
あくまで「その weak constructor から得た packet に限れば `¬ p ∣ t'`」を示す。

これなら theorem は強すぎず、情報落ちも起こりにくい。

## 3.3. 第3段. strong provider を組み上げる

companion lemma ができたら、`PacketPackagingStrong` 自体は薄い wrapper になる。

イメージはこうじゃ。

```lean id="jlwm67"
theorem primeGe5BranchAPrimitiveRestorePacketPackagingStrong
    : PrimeGe5BranchAPrimitiveRestorePacketPackagingStrongTarget := by
  intro p z x' y' z' hpack' hp_dvd_gap' hz'lt
  rcases weak_packet_packaging_theorem hpack' hp_dvd_gap' hz'lt with ⟨pkt', hlt⟩
  have hpt' : ¬ p ∣ pkt'.t :=
    companion_lemma_for_this_constructor hpack' hp_dvd_gap' hz'lt ...
  exact ⟨pkt', hlt, hpt'⟩
```

つまり、main theorem の中では **新しい数学は何もせぬ**。
新しい数学は companion lemma 側へ閉じ込める。

## 4. もし companion lemma が立たなかったら

この場合だけ、次の判断をする。

$$
\boxed{
\text{PacketPackagingStrongTarget の入口がまだ弱い}
}
$$

つまり、今の target

```lean id="qn54pg"
PrimeGe5CounterexamplePack p x' y' z' →
p ∣ (z' - y') →
z' < z →
...
```

だけでは `¬ p ∣ pkt'.t` を出す provenance が不足している、ということじゃ。

そのときは **1 段だけ** 入口を強める。

候補はこうじゃ。

* smaller counterexample に primitive-side 情報を足す
* packet constructor が返す付随 data を structure にまとめる
* weak theorem を replace せず、strong companion target を別立てする

だが、これは **companion lemma を試してから** でよい。
いまの段階で target をまた増やすのは早い。

## 5. 並行して進めてよいもの

`CyclotomicExistenceTarget` の concrete 化は、並行で進めて構わぬ。
ただし、今の critical path は `PacketPackagingStrong` の方が短い。理由は、こちらが埋まれば `hStrong` 側が concrete になり、primitive strong chain が fully operational になるからじゃ。

だから優先順位は、

$$
\texttt{PacketPackagingStrong}
\quad>\quad
\texttt{CyclotomicExistenceTarget}
$$

じゃな。

## 6. わっちの推奨する具体的次作業

次のセッションでやるべきことを、最短に絞るならこれじゃ。

### 6.1. weak packet theorem の本文を開く

`pkt'` を実際に作っている theorem / constructor 名を特定する。

### 6.2. その constructor 専用の companion lemma を 1 本書く

「この構成で得た `pkt'` は `¬ p ∣ pkt'.t`」を示す。

### 6.3. `primeGe5BranchAPrimitiveRestorePacketPackagingStrong` を薄い wrapper として完成させる

これで `RestoreArithmeticStrong` が concrete になる。

### 6.4. strong chain を `FringeDescent` へ流し込む

そのあとで `CyclotomicExistenceTarget` の concrete 化へ移る。

## 7. 一言でまとめると

$$
\boxed{
\text{次は theorem 本体を殴るな。packet の出生証明を掘れ。}
}
$$

じゃ。
いまの局面では、`pkt'.t` の性質は packet そのものではなく、**packet がどう作られたか** に宿っておる。
そこを掘り当てれば、一気に道が開くはずじゃよ。
