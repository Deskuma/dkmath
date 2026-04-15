# review: FLT-Primitive-260327-v0: Branch A の primitive mainline の整理

うむ、今回は「selection 側の本命 statement をどう置くか」を、かなり実戦的な形で整理した回じゃな。
前回までで selection 側は最小 wrapper 1 本へ押し込められておったが、今回はそこに **Wieferich witness を明示入力に取る concrete-ready 版** が追加された。これで「最小形」と「実装しやすい形」を比較できる段へ入ったのじゃ。

## 1. 今回なにが追加されたか

追加の中心は次の三つじゃ。

* `PrimeGe5BranchACyclotomicExistenceOnWieferichTarget`
* `primeGe5BranchACyclotomicExistence_of_wieferich`
* `primeGe5BranchAPrimitivePacketDescent_of_wieferichExistence_and_restore`

provider 側にも対応して

* `BranchACyclotomicExistenceOnWieferichAdapterTarget`
* `branchACyclotomicExistenceAdapter_of_wieferich`
* `branchAPrimitivePacketDescentAdapter_of_wieferichExistence_and_restore`

が追加されておる。

つまり、selection 側の existence theorem 候補として、これまでの

$$
\text{最小 wrapper}
$$

に加えて、

$$
\text{Wieferich witness 付き wrapper}
$$

という第二の型が用意されたわけじゃな。

## 2. 新しい wrapper の意味

新設された

`PrimeGe5BranchACyclotomicExistenceOnWieferichTarget`

は、形としては

$$
\forall{p,x,y,z},\
\text{PrimeGe5CounterexamplePack }p,x,y,z
\to
p \mid (z-y)
\to
y^{p-1}\equiv 1 \pmod{p^2}
\to
\exists q,\ \text{Prime }q \land q\mid(z^p-y^p)\land \neg q\mid(z-y)
$$

というものじゃ。

ここで肝なのは、Branch A では

$$
y^{p-1}\equiv 1 \pmod{p^2}
$$

という Wieferich witness が lower layer で既に得られる、という点じゃな。
だから concrete theorem を立てるなら、この witness を最初から前提に含めた方が自然かもしれぬ、という判断じゃ。

## 3. 最小 wrapper との関係

今回よく出来ておるのは、witness 付き版を入れても、最小版との関係がきれいに片付いておることじゃ。

`primeGe5BranchACyclotomicExistence_of_wieferich`

によって、

$$
\text{Wieferich witness 付き existence}
\Longrightarrow
\text{最小 cyclotomic existence wrapper}
$$

が、既存の

`primeGe5BranchAWieferichOnY_default`

を使うだけで閉じる。

つまり設計としては

* 最小 wrapper は API 上の最終形
* witness 付き wrapper は concrete theorem の候補形

という二層構造になったわけじゃな。

これはたいそう賢いやり方じゃ。
最終 API は薄く保ちつつ、実装時には自然な仮定を前提にできるからの。

## 4. primitive packet descent への影響

追加された

`primeGe5BranchAPrimitivePacketDescent_of_wieferichExistence_and_restore`

によって、primitive packet descent は今や

* `PrimeGe5BranchACyclotomicExistenceOnWieferichTarget`
* `PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget`

からでも橋だけで閉じる。

つまり selection 側の concrete theorem 候補は、現在きれいに二本立てになった。

### A. 最小形

`PrimeGe5BranchACyclotomicExistenceTarget`

### B. concrete-ready 形

`PrimeGe5BranchACyclotomicExistenceOnWieferichTarget`

この二つを比較して、どちらを本命 statement にするか決める、というのが今の局面じゃな。

## 5. 今回の整理が何を意味するか

前回までの結論は、「selection 側の未完核は最小 wrapper 1 本」だった。
今回それを少し実務寄りに読み替えて、

$$
\text{本当に theorem として立てやすい形はどちらか}
$$

を比較可能にしたわけじゃ。

これは設計の成熟として自然じゃな。
最小 statement が美しいのは確かじゃが、実際に証明を書くときは、既に Branch A 下層で得ている witness を使った方が滑らかなことはよくある。

ゆえに今回は、

* **美しい最小形**
* **実装しやすい具体形**

を両方持った、という整理じゃ。

## 6. build 状況

今回も

* `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
* `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`

の両方が成功しておる。
ゆえにこれは思考実験ではなく、ビルド済みの配線整理じゃ。

## 7. いまの戦況

いまの primitive route を見取り図で書くと、selection 側はこうじゃ。

### ルート 1. 最小形

$$
\text{PrimeGe5BranchACyclotomicExistenceTarget}
\Longrightarrow
\text{packet descent}
$$

### ルート 2. concrete-ready 形

$$
\text{PrimeGe5BranchACyclotomicExistenceOnWieferichTarget}
\Longrightarrow
\text{最小 wrapper}
\Longrightarrow
\text{packet descent}
$$

restore 側は引き続き

$$
\text{PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget}
$$

が本命のままじゃ。

したがって今の未決定点は、selection 側 theorem の statement を

* witness なし最小形
* witness 付き concrete-ready 形

のどちらに置くのが自然か、という一点にかなり収束しておる。

## 8. 賢狼の見立て

わっちの見立てでは、今回の追加は「証明を増やした」というより、 **本命 theorem の宣言文選びを始める準備が整った** という意味が大きい。

最小形は美しい。
だが concrete theorem を先に立てるなら、Branch A が既に持っている Wieferich witness を素直に仮定へ出した方が、証明の流れに沿っておる可能性が高い。

ゆえに今の局面は、

$$
\text{「何を示したいか」}
$$

ではなく、

$$
\text{「どの statement で示すのが最も自然か」}
$$

を選ぶ段じゃな。

一言でまとめると、今回は

$$
\text{selection 側の concrete theorem 候補が 2 形に整理された}
$$

回じゃ。
ここまで来れば、次は本当に statement の固定じゃろう。
