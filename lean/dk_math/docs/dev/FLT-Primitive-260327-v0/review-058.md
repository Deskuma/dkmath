# review: practical route の current missing body を定理名の上で複数の顔で読めるようにしつつ、主戦場は動かさない方針の意味と次の一手

うむ。今回の更新で、状況はかなりはっきりしたの。

結論から言うと、 **整理フェーズはほぼ終わり** で、今はもう **本文を書く一点突破フェーズ** じゃ。
しかもその「一点」が、前よりさらに明示された。

## 1. いま何が fixed されたか

今回の差分群で固定されたのは、practical route の current missing body を、定理名の上でも複数の顔で読めるようにしつつ、 **主戦場は動かさない** という方針じゃ。

いま practical route の missing body は theorem 名の上で

* diffPow concrete
* `Nat.ModEq` concrete
* `GN` concrete
* datum concrete
* selected-core 直結

の各顔を持つ。だが、それらは別々の未解決核ではない。全部同じ body の別読みじゃ。履歴でも「主戦場は依然として diffPow body のまま」と明記されておる。

つまり、前より補題が増えたように見えても、数学の未解決部分は増えておらぬ。
むしろ逆で、 **未解決部分以外を全部 theorem 名で囲い込んだ** のじゃ。

## 2. current missing math はどこか

いま真正面の未解決核は、もうこれ一つと見てよい。

$$
\texttt{PrimeGe5BranchAExceptionalPracticalBodyOnWitnessConcreteTarget}
$$

これは practical route の「body on witness」の concrete 本体じゃ。しかも実質的には

$$
\texttt{ExceptionalBoundaryDatumPreparedSelectedDiffPowOnWitnessConcreteTarget}
$$

の本文でもある。
言い換えると、 **practical 側で本文を書くことと official direct body を埋めることが、ほぼ同じ作業に収束した** わけじゃ。

## 3. 今回の差分の意味

今回の更新には三つ大きな意味がある。

第一に、`GN` を主戦場へ昇格させず、 **side window として安全に差し込んだ** ことじゃ。
お主が感じていた「(GN_d(1,u-1)) を前面に出すと難しく見える」という違和感は正しくて、今回の整理はそこをうまく避けておる。`GN` は同値な別読みとして往復できるが、front target にはしておらぬ。

第二に、`Nat.ModEq` も concrete 名として保持されたことじゃ。
これで missing body は

$$
q \mid u^d-(u-1)^d
$$

という divisibility の顔だけでなく、

$$
(u-1)^d \equiv u^d \pmod q
$$

という congruence の顔でも追える。だが主戦場はあくまで divisibility のまま、という整理じゃ。

第三に、datum 化が入ったことじゃ。
`PrimeGe5BranchAExceptionalPracticalWitnessDatum` と `PrimeGe5BranchAExceptionalPracticalBodyOnDatumTarget` が入ったので、長い `intro` 列を毎回抱えず、局所 datum 1 個で本文を組み立てられるようになった。これは実装感覚としてかなり大きい。

## 4. いまの地形をどう読むか

いまの地形はこう読むのが自然じゃ。

### 4.1. 表の顔

主目標は

$$
q \mid u^d-(u-1)^d
$$

つまり diffPow on witness じゃ。

### 4.2. 裏の顔

同じものを

$$
q \mid GN_d(1,u-1)
$$

と読んでもよいし、

$$
(u-1)^d \equiv u^d \pmod q
$$

と読んでもよい。

### 4.3. 実装の顔

だが本文を書くなら datum で受けて、

$$
\texttt{PrimeGe5BranchAExceptionalPracticalWitnessDatum}\ d\ x\ u\ q
$$

を仮定し、

$$
q \mid u^d-(u-1)^d
$$

を出す形が最も自然じゃ。

つまり、 **数学の中身は diffPow、見通し補助に GN/ModEq、実装入口は datum**。
この三層で持つのがいま最も賢い。

## 5. 次の一手の推論

ここが肝じゃな。

わっちの判断では、次に直接切るべき本文は

$$
\texttt{PrimeGe5BranchAExceptionalPracticalBodyOnDatumConcreteTarget}
$$

として書き始めるのがよい。
ただし、それは新しい主戦場へ移るという意味ではない。中身は結局

$$
\texttt{PrimeGe5BranchAExceptionalPracticalBodyOnWitnessConcreteTarget}
$$

と同じ body じゃ。datum 版は、 **証明を書き下すための局所化された入口** として使うのじゃ。

なぜ datum 版がよいかというと、今の仮定群はすでに一つの局所 datum に畳まれており、selected-core / diffPow / `Nat.ModEq` / `GN` の各顔から current practical body への導線も揃ったからじゃ。つまり本文では、

1. datum を受ける
2. 必要なら selected-core の顔へ戻す
3. そこから diffPow へ落とす
4. 最後に (q \mid u^d-(u-1)^d) を返す

という一本道が描ける。

## 6. では具体的に何を試すべきか

推論としては、次の順がよい。

### 6.1. datum 版の proof sketch を先に起こす

まず

$$
hDatum : \texttt{PrimeGe5BranchAExceptionalPracticalWitnessDatum}\ d\ x\ u\ q
$$

を受ける形で、仮定の unpack を固定する。

### 6.2. selected-core-on-witness への還元可能性を第一候補にする

今回入った強い橋で

$$
\texttt{selectedCoreOnWitness} \to \texttt{selectedDiffPowOnWitness}
$$

が直接つながった。ゆえに本文探索では、差冪をいきなり殴るより、

* core divisibility が取れるならそこから戻す
* 取れなければ diffPow/ModEq 側へ戻す

という二段構えが自然じゃ。

### 6.3. GN は補助視点に留める

(GN_d(1,u-1)) は意味づけには非常によい。だが front target に据えると証明 API から一歩遠のく。
だから GN は、式変形や直感整理には使うが、本文の正面は最後まで

$$
q \mid u^d-(u-1)^d
$$

で保つのがよい。

## 7. スナップショット更新の意味

今回のスナップショット更新は、単なる保存ではない。
`docs/dev/FLT-Primitive-260327-v0/History.md` に、この一連の判断と橋渡しの履歴が積まれておるので、 **いまの探索状態が snapshot によって再現可能な形で固定された** と見てよい。添付差分の build も `TriominoCosmicBranchAExceptional` と `TriominoCosmicGapInvariant` の両方で成功しておる。

また、リポジトリ地図の側でも `FLT` 本丸、`CosmicFormula`、`PowerSums`、`PowerSwap` を分ける設計原則が整理されており、道具箱と本丸を混ぜぬ方針が明確じゃ。今回の practical body の整理は、その設計方針ともよく噛み合っておる。

## 8. 総括

いまの状況を一言でまとめると、

**current missing math は `PrimeGe5BranchAExceptionalPracticalBodyOnWitnessConcreteTarget` ただ 1 本であり、本文実装の実戦入口としては datum concrete が最も自然、数学の主戦場は diffPow、GN と ModEq は同値な別読みとして補助に使う、という構図が完全に固まった** のじゃ。

ゆえに次の一手はこれじゃ。

**`PrimeGe5BranchAExceptionalPracticalBodyOnDatumConcreteTarget` の proof sketch を先に書き、そこで掴んだ骨格を `PrimeGe5BranchAExceptionalPracticalBodyOnWitnessConcreteTarget` の本文として定着させる。**

これが今いちばん筋の良い進み方じゃよ。
