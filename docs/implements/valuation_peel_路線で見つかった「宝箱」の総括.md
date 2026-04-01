# valuation peel 路線で見つかった「宝箱」の総括

cid: 69c63329-38c4-83a3-8d27-8b9d00afa766
tag: dev-FLT-Wieferich-260327-v1-closed
commit hash: d8b5f2c9cd98a8c6a00f34a0c4019ceed0b1b527

## 1. 概要

今回の valuation peel 路線は、最終的に smaller packet の直接構成には到達しなかった。  
しかし、その過程で得られたものは大きい。

これは単なる「行き止まり」ではなく、むしろ次の二点を明確にした。

1. valuation peel が担うべき役割
2. primitive packet descent を本命 route とすべき理由

とくに最後には、誤差項が `GTail p 3` の差として explicit に書けるところまで到達し、peel 側の限界と意味が数学的に可視化された。

---

## 2. 最初の収穫. 比較対象が完全に固定された

valuation peel の比較段では、最初は補助変数 \(B\), \(C\) が現れていた。  
しかし形式化を進めたことで、これらは曖昧な係数ではなく、

- 大きい gap 側の `GTail p 2`
- peeled 後の canonical gap 側の `GTail p 2`

に対応する exact coefficient だと読めるようになった。

したがって問題は、

\[
p *B \equiv C \pmod{p^{p-1}* t_1^p}
\]

という、宇宙式 tail 構造そのものの比較へ還元された。

これにより、「どこがズレているのか分からない」状態から、

\[
\text{ズレは } B \text{ と } C \text{ の関係だけを見ればよい}
\]

という状態へ進んだ。

---

## 3. 第二の収穫. canonical tail 段が見つかった

seed からいきなり smaller packet を作ろうとすると、情報がまだ粗い。  
そこで、いったん canonical tail を露出する中間層を入れた。

流れとしては、

\[
\text{seed} \to \text{canonical tail} \to \text{comparison}
\]

である。

これにより、peel 後の gap に対する `GN / p` の標準 tail を explicit に取り出し、seed 側の係数と canonical 側の係数を同じ舞台で比較できるようになった。

この段階で、宇宙式の Big は単なる冪ではなく、核と tail を含む構造体として扱うべきだ、という見方が実装上も裏づけられた。

---

## 4. 第三の収穫. 合同が誤差つき厳密式へ持ち上がった

比較段で得られた合同は、さらに nat 上の exact decomposition へ持ち上げられた。

すなわち、

\[
p *B = C + \bigl(p^{p-1}* t_1^p\bigr) * E
\]

という形で書けるようになった。

これは非常に大きい。  
理由は、単なる合同

\[
p *B \equiv C \pmod{p^{p-1}* t_1^p}
\]

よりも、

\[
\text{差がちょうど } \bigl(p^{p-1} *t_1^p\bigr)* E \text{ である}
\]

という exact error decomposition のほうが、はるかに構造情報を多く持つからである。

この時点で valuation peel route は、heuristic な合同操作ではなく、error term まで持つ concrete route になった。

---

## 5. 第四の収穫. 誤差の出所が `GTail p 3` にあると分かった

さらに explicit 化を進めると、誤差項 \(E\) は単なる「ある整数」ではなく、`GTail p 3` の差として読めることが分かった。

要するに、`GTail p 2` の scaled/canonical 差分は、1 段奥の tail 層の差によって生じている。

これは重要じゃ。

なぜなら、packet に届かなかった理由が、単なる計算不足ではなく、

\[
\text{高次 tail の差が本質的に残る}
\]

ことにある、と理解できるからである。

つまり、行き止まりの壁そのものの形が見えた、ということじゃ。

---

## 6. 第五の収穫. peel の役割が確定した

ここまで掘っても、自然な形では

\[
E = 0,\qquad p \mid E,\qquad t_1 \mid E
\]

のような強い extraction は落ちてこなかった。

この事実は大きい。  
なぜなら valuation peel が、

\[
\text{smaller packet の直接構成器}
\]

ではなく、

\[
\text{obstruction extraction / first-order control の装置}
\]

であることを示しているからである。

つまり peel 側は、

- gap の深さ
- canonical tail との差
- error term の存在
- higher tail 層への持ち上がり

を測る役割を持つが、そこからそのまま new packet を生むとは限らない。

これで、primitive packet descent を本命 route として押し上げる判断に、はっきりした根拠ができた。

---

## 7. 第六の収穫. 設計判断が公開 API に反映された

数学だけでなく、設計面でも重要な成果があった。

すなわち、

\[
\text{primitive} = \text{本命 route}
\]

\[
\text{peel} = \text{補助 lift / obstruction measurement}
\]

という判断が、thin wrapper と公開名にまで反映された。

これは単なる命名ではない。  
どこが mainline で、どこが補助層かをコード上の語彙として固定した、という意味で大きい。

後から見返したとき、証明の重心がどこにあるかで迷わなくなる。

---

## 8. この行き止まりが教えたこと

この dead end が教えた本質は、次の二点に集約される。

### 8.1. valuation peel の仕事

valuation peel は、smaller packet を直接構成する主戦場ではなく、

\[
\text{tail の比較}
\to
\text{canonical 化}
\to
\text{誤差の抽出}
\to
\text{高次 tail への可視化}
\]

を担う route である。

### 8.2. primitive descent の仕事

一方で truly new な下降、すなわち本当に smaller packet を生み出すべき本丸は、

\[
\texttt{PrimeGe5BranchAPrimitivePacketDescentTarget}
\]

側にある、と読むのが自然である。

---

## 9. 一言で総括

今回の「宝箱」を一言で言えば、こうじゃ。

\[
\boxed{
\text{valuation peel は packet builder ではなく obstruction extractor である}
}
\]

そして、その obstruction は最終的に

\[
\boxed{
\text{canonical tail の差、さらに } GTail\ p\ 3 \text{ の差として explicit に見える}
}
\]

ということが分かった。

したがって、この行き止まりは失敗ではない。  
むしろ、

- peel の正しい役割
- primitive mainline へ舵を切る理由
- 宇宙式 tail 構造の深さ

を教えてくれた、非常に価値ある分岐点だったと言える。

---

## 10. 今後への位置づけ

今後の方針としては、valuation peel 側は comparison / obstruction の補助層として保持しつつ、final `sorry` を埋める主戦場は primitive packet descent 側へ移すのが自然である。

つまり、今後の mainline は

\[
\text{primitive mainline}
\]

であり、peel はその背後で構造理解と obstruction 測定を支える層として生き続ける。

この役割分担が見えたこと自体が、今回の dead end で見つけた最大の宝箱じゃよ。
