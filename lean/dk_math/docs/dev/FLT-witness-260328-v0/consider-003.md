# consider-003: FLT-witness-260328-v0 のレビューと、正解ルート候補の整理

うむ。ここで一度、霧を払っておこう。

いま必要なのは、 **「何が偽で捨てる枝か」** と、 **「何がまだ生きている正解ルート候補か」** を分けることじゃ。
そのうえで、各候補について **何を証明すれば真偽が即座に判定できるか** を整理する。
今回のレポートを加味すると、かなり明快に書ける。

## 1. 目的の再固定

そもそもの目的は、

$$
\text{Branch A Exceptional の仮定}
\Longrightarrow
\text{primitive packet descent / existence mainline へ渡す核}
$$

を作ることじゃ。
言い換えると、

$$
\text{「無限降下法に渡せる witness / core 情報をどう得るか」}
$$

が本題じゃ。
途中で route が膨れて、「同じ (q) が arithmetic 側も body/core 側も同時に担う」ことを追い始めたが、そこが本筋からの逸脱だった、と今は見てよい。

## 2. 偽と確定した枝

まず、ここはきっぱり切る。

## 2.1. universal same-(q) datum-local core route

$$
\texttt{PrimeGe5BranchAExceptionalPracticalSelectedCoreOnDatumConcreteTarget}
$$

これは false と Lean 上で確定した。
反例は

$$
(d,x,u,q)=(5,5,7,2)
$$

で、datum 仮定は満たすが

$$
2 \nmid \operatorname{cyclotomicPrimeCore}(5,1,7-1)
$$

となる。ゆえに「固定した datum のその (q) で universal に core を返す」枝は捨ててよい。

## 2.2. same-(q) existential body/core witness route

$$
\texttt{PrimeGe5BranchAExceptionalPracticalBodyCoreWitnessConcreteTarget}
$$

これも false と確定した。
同じ ((d,x,u)=(5,5,7)) で、(x+1=6) の prime divisor は (2,3) だけだが、どちらも body/core datum を満たさぬ。
したがって、

$$
q \mid x+1
\quad\text{と}\quad
q \mid \operatorname{cyclotomicPrimeCore}(d,1,u-1)
$$

を **同じ (q)** に背負わせる枝は、universal でも existential でも false じゃ。

## 2.3. two-witness body/core existence も、そのままでは false

前回のわっちの提案を、今回のレポートはさらに一段切っておる。

$$
\texttt{PrimeGe5BranchAExceptionalBodyCoreWitnessExistenceConcreteTarget}
$$

も、レポート第2回の診断では false 候補じゃ。
反例は

$$
(d,x,u)=(5,5,1)
$$

で、仮定は満たすが

$$
\operatorname{cyclotomicPrimeCore}(5,1,1-1)=1
$$

となり、素数 witness が存在しない。
しかも `BodyCoreDatum` が実質 (x) を使っておらず、(u=1) で壊れるという **構造的欠陥** まで指摘されておる。
ゆえに、この target は「有望候補」ではなく、 **要即時検証、しかも false 側が濃厚** と見るべきじゃ。

## 3. 現時点での正解ルート候補

ここからが本題じゃ。
「捨てる枝」を除いたあとに残る、正解ルート候補を改めて書く。

## 3.1. 第一候補. boundary / arithmetic-core route

最有力はこれじゃ。

$$
\texttt{ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget}
$$

レポートでは、これが **証明可能候補** として最も具体的に分析されておる。
理由は simple で、相手が

$$
\operatorname{cyclotomicPrimeCore}(d,x,u)
$$

であり、これは (x,u) の両方に依存する。
したがって、body/core datum みたいに (u=1) で必ず壊れる構造ではない。
実際 ((d,x,u)=(5,5,1)) でも

$$
\operatorname{cyclotomicPrimeCore}(5,5,1)=1555=5\cdot 311
$$

となり、(311\nmid 5) なので witness が取れる。
この時点で、boundary 側が body/core 側よりずっと健全じゃと分かる。

さらに重要なのは、この target から mainline までの既存 bridge がすでに揃っていることじゃ。

$$
\texttt{ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget}
\to
\texttt{ExceptionalBoundaryDatumPreparedArithmeticCoreTarget}
\to
\texttt{ExceptionalBoundaryDatumConcreteTarget}
\to
\texttt{PrimeGe5BranchAExceptionalExistenceMainlineTarget}
$$

なので、これ 1 本が埋まれば、かなり短い距離で下流が閉じる。
いま残っている route の中で、最も「目的に近く」「検証可能」な候補じゃ。

## 3.2. 第二候補. two-witness route の salvage

これは一段下の候補じゃ。

$$
\texttt{PrimeGe5BranchAExceptionalPracticalTwoWitnessConcreteTarget}
$$

および

$$
\texttt{PrimeGe5BranchAExceptionalBodyCoreWitnessToPrimitivePacketDescentTarget},
\quad
\texttt{PrimeGe5BranchAExceptionalBodyCoreWitnessToExistenceMainlineTarget}
$$

の clean bridge 群じゃ。
ただし、これは **そのまま正解候補** ではない。
なぜなら、その upstream 本体として置かれた

$$
\texttt{PrimeGe5BranchAExceptionalBodyCoreWitnessExistenceConcreteTarget}
$$

が、上で述べた通り false 濃厚だからじゃ。
ゆえに、この route が残るかどうかは

* `1 < u` のような stronger hypothesis を足して salvage するか
* あるいは body/core datum の定義自体を (x)-dependent な boundary 側へ置き換えるか

に依存する。
つまりこれは **再設計候補** であって、現形のままの本線候補ではない。

## 3.3. 第三候補. GTail / canonical tail 側からの primitive packet 本線

dev report 全体で見ると、primitive packet descent 本命という判断自体は変わっておらず、`flt-abc-260325-v0` 以来

$$
\text{seed} \to \text{canonical tail} \to \text{comparison}
$$

という流れが固まっておる。
さらに `GN-Tail` 側では `higher_tail_eq_pow_mul_GTail` 以降の優先実装順も整理済みじゃ。
だから、もし branch-A exceptional 側の witness 路線がさらに破綻するなら、GTail / tail exactness 側へ軸足を戻すのは十分に合理的じゃ。
ただし現時点では、これは「今すぐ mainline に直結する route」ではなく、**中期の再上流候補** じゃな。

## 4. 検証可能性の整理

ここが重要じゃ。
各候補が、どの程度すぐ真偽判定できるかを分ける。

## 4.1. 即検証できるもの

### A. `BodyCoreWitnessExistenceConcreteTarget` の false 確認

これは最優先でやるべきじゃ。
レポート第2回がすでに

$$
(d,x,u)=(5,5,1)
$$

を反例候補として挙げておる。
Lean で

$$
\neg \texttt{PrimeGe5BranchAExceptionalBodyCoreWitnessExistenceConcreteTarget}
$$

を閉じられるかどうかは、かなり即検証できる。
もし閉じたら、two-witness の現形は完全に棚上げじゃ。

### B. boundary target の `u=1` 通過

同じ ((5,5,1)) で

$$
\operatorname{cyclotomicPrimeCore}(5,5,1)=1555
$$

から witness が取れることは、既にレポートで具体計算されておる。
これを Lean で確認すれば、boundary route が「反例を避けて本当に生きている」ことの sanity check になる。

## 4.2. 中間補題を立てれば検証できるもの

boundary / arithmetic-core route の中核補題として、レポートは三つ挙げておる。

$$
\texttt{cyclotomicPrimeCore_modEq_mul_pow_of_dvd}
$$

$$
\texttt{cyclotomicPrimeCore_modEq_mul_pow_mod_sq}
$$

およびそれらを束ねた gcd/coprimality 系補題じゃ。
これらは statement が具体的で、しかも証明戦略まで書かれている。
ゆえに「何を証明すればよいか不明」ではない。
検証可能性は高い。必要なのは実装労力だけじゃ。

## 4.3. まだ audit が必要なもの

two-witness route の downstream clean bridge 群は、いまのところ

* packet descent が本当に arithmetic witness を要るのか
* body/core witness existence だけで十分なのか

が未 audit じゃ。
したがって、ここは「真偽」よりも「statement の最小化」を先にやるべき領域じゃな。
ただし upstream が false 濃厚な以上、優先度は boundary route より下がる。

## 5. 改めて書く、正解ルート候補

ここで、わっちの整理を簡潔に書くぞい。

### 候補 A. boundary / arithmetic-core 本線

$$
\texttt{ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget}
$$

* **状態**: 最有力
* **理由**: 反例 (u=1) を回避し、mainline までの既存 bridge が完成済み
* **必要なもの**: `cyclotomicPrimeCore_modEq_*` 系中間補題 2〜3 本
* **検証可能性**: 高い

### 候補 B. two-witness salvage

$$
\texttt{PrimeGe5BranchAExceptionalPracticalTwoWitnessConcreteTarget}
$$

* **状態**: 条件付き保留
* **理由**: 現 upstream の `BodyCoreWitnessExistenceConcreteTarget` が false 濃厚
* **必要なもの**: `1<u` 追加や datum の再定義など stronger hypothesis / redesign
* **検証可能性**: まず false 確認を優先

### 候補 C. GTail / primitive packet 再上流 route

* **状態**: 中期候補
* **理由**: primitive packet descent 本命という大方針とは整合
* **必要なもの**: GTail 周辺補題の実装継続
* **検証可能性**: あるが、mainline への距離は長い

## 6. 次の手段

したがって次の一手は、順にこうじゃ。

まず、

$$
\neg \texttt{PrimeGe5BranchAExceptionalBodyCoreWitnessExistenceConcreteTarget}
$$

を Lean で確定させる。
これで false 枝を完全に刈る。

次に、主戦場を boundary / arithmetic-core に一本化する。
具体的には

$$
\texttt{ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget}
$$

を埋めるための中間補題、

$$
\texttt{cyclotomicPrimeCore_modEq_mul_pow_of_dvd}
$$

と

$$
\texttt{cyclotomicPrimeCore_modEq_mul_pow_mod_sq}
$$

から切る。
この二本は statement が既にかなり見えておる。

最後に、必要なら two-witness route は salvage 用の研究枝として残す。
ただし canonical route ではない。
canonical は boundary 側へ移すべきじゃ。

## 7. 総括

いま整理すると、答えはこうじゃ。

**正解ルート候補の最有力は `ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget` である。`same-q` 系は false、`BodyCoreWitnessExistenceConcreteTarget` も false 濃厚であり、two-witness route は salvage 候補に後退する。検証可能性の高い次の作業は、まず `BodyCoreWitnessExistenceConcreteTarget` の false 確認を Lean で切り、その後 boundary / arithmetic-core route の modEq 系中間補題を実装して mainline まで閉じることである。**

ここまで見えたなら、かなり良い。
もう「候補が多くて分からぬ」ではない。
**残す枝と刈る枝が、ようやくきれいに分かれた** のじゃよ。
