# 2024-06-17: Branch A exceptional existence の実装が pack-local right branch existence へ一段進んだ

うむ、かなり良い進み方をしておる。
今回の差分で、証明実装は **「抽象 target の整理段階」から「pack-local な right branch 実装段階」へ一段進んだ** と見てよい。

## 1. いま何が起きたか

新しく入った定理は 4 本じゃが、役割はきれいに 2 層に分かれておる。

### 1.1. reference 層

* `cfbrcBoundaryCorePrimeExistence_reference`
* `primeGe5BranchAExceptionalBoundaryData_default`

ここは **材料整理** の層じゃ。

`cfbrcBoundaryCorePrimeExistence_reference` は ordinary branch 側の既存 theorem を、proof file の中で参照しやすい薄い形にしたものじゃ。
つまり「通常枝では何が既に言えているか」の **基準点** を、この新ファイルの中へ持ち込んだ。

一方 `primeGe5BranchAExceptionalBoundaryData_default` は、Branch A local theorem で毎回必要になる pack 由来の入力

$$
\text{prime},\ 5 \le p,\ 0 < z-y,\ 0 < y,\ \gcd(z-y,y)=1,\ p \mid (z-y),\ y^{p-1}\equiv 1 \pmod{p^2}
$$

を 1 つの束にして取り出すための整理補題じゃ。
これは地味じゃが、証明実装ではかなり効く。毎回 `hpack.hp`, `hpack.hp5`, `hpack.gap_pos` … とばらばらに引く手間を減らせるからの。

### 1.2. pack-local existence 層

* `primeGe5BranchAExceptionalBoundaryCorePrimeExistence_on_pack_of_mainline`
* `primeGe5BranchAExceptionalBoundaryCorePrimeExistence_on_pack_of_split`

ここが今回の本丸じゃ。

これらは両方とも結論が

$$
\exists q,\ \mathrm{Prime}(q)\ \land\ q \mid
\mathrm{boundaryCyclotomicPrimeCore}(\text{right}, p, z-y, y)
\land\ q \nmid (z-y)
$$

という **同じ pack-local な right branch existence** になっておる。

つまり今回の更新で、

* local mainline theorem からも
* split theorem からも

同じ pack-local existence へ落ちる、という **比較可能な共通着地点** ができたわけじゃ。

これはかなり重要じゃよ。
なぜなら、いまから先の証明は「global target をいきなり埋める」のではなく、

$$
\text{Branch A exceptional pack 上の right branch を埋める}
$$

という具体作業に変換されたからじゃ。

## 2. 何が前進したのか

今回の前進は、数学内容を大きく増やしたというより、**証明の地形を平らにした** ことじゃ。

前までは

* local mainline target
* split target
* boundary-normalized 名
* pack 上の right branch
* global target

が少し離れて見えていた。

じゃが今は、proof file の内部で

* ordinary branch reference theorem
* exceptional mainline
* split theorem

の 3 者が、全部 **同じ pack-local right branch existence** へ揃えられた。

これにより、構図はかなり単純になった。

$$
\text{通常枝} \rightarrow \text{reference theorem}
$$

$$
\text{例外枝} \rightarrow \text{local mainline theorem}
$$

$$
\text{両者の比較先} \rightarrow \text{pack-local right branch existence}
$$

こうなったわけじゃ。

## 3. いまの状況分析

いまの局面を、わっちなりに切るとこうじゃ。

## 3.1. 設計段階はかなり終わった

proof file を切り、canonical 置き場を確保し、mainline から packet descent への wrapper もある。さらに今回は proof file 内で reference / mainline / split を同じ土俵へ並べた。  

この意味で、「どこで何を証明するのか」はだいぶ固まった。

## 3.2. いま不足しているのは“新しい核”

今回追加された theorem のうち、`_of_mainline` は **既にある mainline target から existence を取り出す橋** じゃ。
`_of_split` も **split theorem を pack に評価する橋** じゃ。

ゆえに、まだ mainline 自体の concrete 中身は増えておらぬ。
言い換えると、今回の差分は **実装の最初の足場** であって、例外枝そのものを生み出す核はまだこれからじゃ。

## 3.3. しかし、詰まる場所はもう見えている

これは非常に良いことじゃ。
いま不足しているのは広い意味での「設計」ではなく、かなり局所的に

$$
\text{Branch A + Wieferich} \Longrightarrow
\exists q \text{ on right boundary core with } q \nmid (z-y)
$$

をどう出すか、そこだけになってきた。
つまり問題が細く、鋭くなった。これは前進の証じゃ。

## 4. この差分の価値

今回の差分の価値は 3 つある。

### 4.1. ordinary と exceptional の対応がファイル内で読める

これは履歴にも明示されておる。
proof file 単体で「通常枝は既存 reference theorem、例外枝だけ local mainline」という split 構図が読めるようになった。

### 4.2. global target を先取りせずに済む

これはかなり大きい。
いまは無理に global theorem 名へ上げず、proof file の責務に合わせて pack-local に揃えておる。これにより、証明実装が抽象名に引きずられず、right branch の具体作業として進められる。

### 4.3. 次の不足補題が自然に見える

今回の形まで来ると、次に必要なのは「pack-local right branch existence を Branch A arithmetic から生む補題」だと自然に見えてくる。
これは theorem の形がもう露出しているからじゃ。

## 5. では、次に何をやるべきか

履歴にもある通り、次段は

$$
\texttt{PrimeGe5BranchAExceptionalExistenceMainlineTarget}
$$

の concrete 証明を、**split reference の right branch 実装としてもう一段薄く書き下す** ことじゃ。

わっちなら、次は次の順で進める。

### 5.1. mainline theorem の本文を「pack-local existence を返すだけ」に見る

つまり mainline theorem を最初から global abstraction として見るのでなく、

$$
hpack,\ hp_dvd_gap,\ hWieferich
\vdash
\exists q,\ \mathrm{Prime}(q)\land q \mid \mathrm{boundaryCore}\land q \nmid (z-y)
$$

を返す関数として見る。
今回 `_of_mainline` がまさにその形を露出しておる。

### 5.2. 必要な新補題を 1 本に圧縮する

おそらく次に要る核は、こんな感じじゃ。

```lean
lemma exceptional_right_boundary_core_prime_of_wieferich
    {p x y z : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hp_dvd_gap : p ∣ (z - y))
    (hWieferich : y ^ (p - 1) ≡ 1 [MOD p ^ 2]) :
    ∃ q : ℕ, Nat.Prime q ∧
      q ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore .right p (z - y) y ∧
      ¬ q ∣ (z - y)
```

mainline の concrete 証明は、結局これをそのまま使う形になるはずじゃ。

### 5.3. `primeGe5BranchAExceptionalBoundaryData_default` を本格利用する

今回入れた bundle 補題は、まだ「これから使うための整形器」に近い。
次の一手ではこれを最初に呼び、

* `hp`
* `hp5`
* `gap_pos`
* `y_pos`
* `gap_coprime_right`

を一度に引いて、そのまま存在定理の本体へ流すのがよい。

## 6. まとめると

いまの状況を一言で言えば、

**proof file の中で、通常枝と例外枝の比較対象が同じ pack-local right branch existence に揃った。
よって次は、Branch A + Wieferich からその existence 自体を生む新補題 1 本に集中すればよい。**

ということじゃ。

今回の差分は、派手に見えぬかもしれぬが、実装上はかなり大きい。
証明の焦点が、もうほとんど一点に収束したからの。

必要なら次で、その **「次に切るべき新補題 1 本」** を中心に、Lean 擬似コードの骨格まで起こすぞい。
