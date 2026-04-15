# Review 031: Stage 1 の残敵は、generic coprimality ではなく、\(P \mid (p)\) 分岐の deep cyclotomic target に集約された

うむ、戦況は **かなり良い**。
しかも今回は、ただ前進しただけでなく、**どこが本当の山か** までかなり正確に見えたぞい。

## 戦況分析

今回の差分で、\(P \mid (p)\) 分岐の target の向きが修正されたのは大きい。
前は

$$
P \le (\zeta-1)
$$

を狙っておったが、ideal の割り算の向きから見て本当に欲しいのは

$$
P = (\zeta-1)
$$

じゃ、という整理に直った。
つまり、totally ramified の世界では「\(P\) は \(p\) の上の prime ideal」ではなく、**「\(P\) はその唯一の prime ideal \((\zeta-1)\) そのもの」** を狙うべきだ、と定まったわけじゃ。これは戦略上とても健全な修正じゃよ。

さらに、

* `zeta_sub_one_prime_of_p`
* `zeta_sub_one_ideal_isPrime`

が no-sorry で入ったことで、**\((\zeta-1)\) が prime ideal を生成する** ところまでは mainline に降りてきた。
つまり Stage 1 の残敵は、もう「\((\zeta-1)\) が怪しい」ではなく、

1. \(P \mid (p)\) なら本当に \(P = (\zeta-1)\) と言えるか
2. \(n \in (\zeta-1)\) かつ \(n\in\mathbb{Z}\) なら \(p \mid n\) と言えるか

この 2 本に縮んだ、ということじゃ。

## 解説

今の Stage 1 は、論理の骨格としてはほぼ完成しておる。
流れはこうじゃ。

共通 prime ideal \(P\) を仮定すると、既存 no-sorry 群により

$$
P \mid (p)\ \lor\ y \in P
$$

へ落ちる。
そして

* \(y \in P\) 分岐は、もう `Nat.Coprime x y` と product identity から閉じた
* \(P \mid (p)\) 分岐は、今回の整理で
  $$
  P = (\zeta-1)
  $$
  と
  $$
  n \in (\zeta-1)\cap \mathbb{Z} \Rightarrow p \mid n
  $$
  の 2 target を仮定すれば閉じる

ところまで来ておる。
つまり、**Stage 1 の generic ideal arithmetic や receiver 群は、もう十分に揃っている** のじゃ。残るのは cyclotomic number theory の deep 部分だけじゃよ。

## Mathlib を踏まえた見立て

Mathlib の公式 docs を見ると、cyclotomic 側にはかなり近い部品が既にある。
特に

* `IsPrimitiveRoot.toInteger_sub_one_dvd_prime'`
* `IsPrimitiveRoot.norm_sub_one_of_prime_ne_two`
* `IsCyclotomicExtension.norm_zeta_sub_one_of_prime_ne_two`

の系列があり、\((\zeta-1)\) が \((p)\) を割ること、また odd prime の場合に \((\zeta-1)\) の norm が \((p)\) になることは、公式側でも定理として揃っておる。 ([Lean Community][1])

この見取り図からすると、ぬしがいま target 化しておる 2 本のうち、**より Mathlib に近いのは後者** じゃ。
すなわち

$$
n \in (\zeta-1) \cap \mathbb{Z} \Rightarrow p \mid n
$$

の方は、norm が (p) であることを使う route がかなり素直に見える。
一方で

$$
P \mid (p) \Rightarrow P = (\zeta-1)
$$

の方は、totally ramified な prime ideal factorization の API が要るので、今見えている docs だけだと **一段深い ideal-level の橋** がまだ必要そうじゃ。  ([Lean Community][1])

## いまの戦況を一言で言うと

$$
\boxed{
\text{Stage 1 の残敵は、generic な coprimality ではなく、
deep cyclotomic target が 2 本だけ}
}
$$

じゃ。
そしてその 2 本も対称ではない。

* **target 2**
  $$
  n \in (\zeta-1)\cap\mathbb{Z} \Rightarrow p \mid n
  $$
  は norm route がかなり見えておる

* **target 1**
  $$
  P \mid (p) \Rightarrow P = (\zeta-1)
  $$
  は ideal factorization / ramification API の接続が必要で、少し重い

という非対称な戦況じゃな。  ([Lean Community][1])

## 戦略評価

ゆえに、わっちの評価はこうじゃ。

**守りは完成に近い。攻めるべきは 2 本の deep target のうち、まず軽い方から。**

つまり、いまは Stage 1 全体を generic に広げ直す段ではない。
むしろ、

1. `IntegerInZetaMinusOneIdealDivisibleByPTarget` を norm route で埋める
2. その後 `PrimeOverPEqualsZetaMinusOneTarget` を ramification / factorization 側で詰める

この順が自然じゃ。
後者から突っ込むより、前者を先に固める方が、戦果が早く見えやすい。

ひとことで総括するぞい。

$$
\boxed{
\text{戦況は優勢。}
\text{Stage 1 はもう「構造問題」ではなく「深い cyclotomic target の埋め立て問題」に変わった}
}
$$

よくここまで削ぎ落としたものじゃ。
残る敵は多く見えて、実はもう少ない。

[1]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/Cyclotomic/PrimitiveRoots.html "Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots"
