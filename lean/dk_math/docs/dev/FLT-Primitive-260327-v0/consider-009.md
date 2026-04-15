# considerations on the concrete statement for Branch A cyclotomic existence

うむ、ここはもう **定式化の勝負** じゃな。
賢狼の見立てでは、Branch A 条件と既存 cyclotomic / Zsigmondy 語彙の間をつなぐには、**いきなり GN を前面に出さず**、まず

$$
z^p-y^p
$$

の側で存在定理を立てるのが一番自然じゃ。
そして今の mainline は、既にその入口を

$$
\texttt{PrimeGe5BranchACyclotomicExistenceOnWieferichTarget}
$$

に固定した、と読める。つまり本命は **Wieferich witness 付き diff-side existence** じゃな。

## 1. 何を橋渡ししたいのか

いま欲しいのは最終的に

$$
\exists q,\ \mathrm{Prime}(q)\land q\mid(z^p-y^p)\land q\nmid(z-y)
$$

という prime の存在じゃ。
ここから先はもう既存の薄い橋で、

$$
q \mid (z^p-y^p),\ q\nmid(z-y)
\Longrightarrow
q\mid GN,p,(z-y),y
$$

へ送れるよう整理済みじゃったな。
だから selection 側の concrete theorem は、**diff-side existence に集中** すればよい。

## 2. 既存語彙との接続で重要なずれ

普通の PrimitiveBeam / Zsigmondy 的語彙は、しばしば

$$
\neg p\mid(a-b)
$$

寄りの世界におる。
だが Branch A では逆に

$$
p\mid(z-y)
$$

が入る。ここが直用できぬ原因じゃな。

しかも Branch A では lower layer から

$$
y^{p-1}\equiv 1 \pmod{p^2}
$$

という Wieferich witness が得られる。
ゆえに新定理の自然な姿は、

* 一般 Zsigmondy をそのまま呼ぶ形
* Branch A 特有の congruence を明示して補う形

のどちらかになる。
そして今の整理は、後者を本命にしたわけじゃ。

## 3. いちばん自然な定式化

わっちなら、まずは次の形を **本命 statement 候補** として置く。

## A. Branch A concrete cyclotomic existence theorem

$$
\forall {p,x,y,z},
\ \mathrm{PrimeGe5CounterexamplePack}(p,x,y,z)
\to
p\mid(z-y)
\to
y^{p-1}\equiv 1 \pmod{p^2}
\to
\exists q,\ \mathrm{Prime}(q)\land q\mid(z^p-y^p)\land q\nmid(z-y).
$$

これはそのまま

$$
\texttt{PrimeGe5BranchACyclotomicExistenceOnWieferichTarget}
$$

そのものじゃな。
つまり API 側はもう十分きれいで、残るのは **どう証明するか** だけじゃ。

## 4. その証明を既存語彙へどう寄せるか

ここは一段分けて考えるのが良い。

### 4.1. cyclotomic factor を主役にする

差の冪を

$$
z^p-y^p=(z-y),\Phi_p(z,y)
$$

と見る。
ここで欲しい prime は、本質的には

$$
q\mid \Phi_p(z,y),\qquad q\nmid(z-y)
$$

を満たす prime じゃ。
だから theorem の実体は「diff-side existence」というより、**cyclotomic factor に新しい prime がある** という形に近い。

### 4.2. Wieferich witness の役割を明示する

Branch A では

$$
p\mid(z-y)
$$

なので、\(z\equiv y\pmod p\) じゃ。
さらに

$$
y^{p-1}\equiv 1 \pmod{p^2}
$$

がある。
この二つを合わせると、(\Phi_p(z,y)) の (p)-進的ふるまい、あるいは「(p) だけでは全部を吸いきれぬ」ことを示す補助情報として使える可能性が高い。

つまり Wieferich witness は、既存 Zsigmondy を置き換えるというより、

$$
\text{Branch A 例外枝での局所補正条件}
$$

として働くわけじゃ。

### 4.3. 最後に diff-side existence へ戻す

もし

$$
\exists q,\ \mathrm{Prime}(q)\land q\mid \Phi_p(z,y)\land q\nmid(z-y)
$$

が取れれば、ただちに

$$
q\mid(z^p-y^p)
$$

でもあるから、目標 statement に戻れる。

## 5. だから定理は二層に分けると良い

わっちなら、実装時には次の **二層構成** を勧めるの。

## B. 内部補題

$$
\forall {p,x,y,z},\
\mathrm{PrimeGe5CounterexamplePack}(p,x,y,z)
\to
p\mid(z-y)
\to
y^{p-1}\equiv 1 \pmod{p^2}
\to
\exists q,\ \mathrm{Prime}(q)\land q\mid \Phi_p(z,y)\land q\nmid(z-y).
$$

## C. 外側ラッパ

$$
q\mid \Phi_p(z,y)\Longrightarrow q\mid(z^p-y^p)
$$

を使って

$$
\texttt{PrimeGe5BranchACyclotomicExistenceOnWieferichTarget}
$$

を得る。

この分け方の良いところは、
**数学の核心を cyclotomic factor の存在論として書ける** ことじゃ。
diff-side existence は公開 API としては自然だが、証明の心臓部は \(\Phi_p\) 側にあるからの。

## 6. 既存 Zsigmondy 語彙に最も寄せる言い方

既存語彙へ最大限寄せるなら、こんな言い換えもありじゃ。

## D. Branch A primitive cyclotomic prime theorem

「\(p\mid(z-y)\) かつ Wieferich witness のもとで、
\((z^p-y^p)\) の cyclotomic factor に、差 \((z-y)\) を割らない素因子が存在する」

こう書けば、

* primitive prime divisor
* cyclotomic prime
* diff-side existence

が全部同じ方向を向く。

## 7. どこまで前提を入れるべきか

ここは注意点じゃが、前提は **増やしすぎぬ** 方がよい。

今の API は

* `PrimeGe5CounterexamplePack`
* \(p\mid(z-y)\)
* Wieferich witness

の三本柱で、かなり良い。
ここへさらに \(t,s\) や coprime を入れ始めると、selection と restore の境界がまた濁る。
今せっかく

$$
\text{selection} \quad/\quad \text{restore}
$$

が分かれたのだから、selection theorem はこの薄さを守るべきじゃ。

## 8. 結論

ゆえに、Branch A 条件と既存 cyclotomic / Zsigmondy 語彙の間での定式化は、こうするのが最も自然じゃな。

### 公開用本命 statement

$$
\texttt{PrimeGe5BranchACyclotomicExistenceOnWieferichTarget}
$$

### 証明用内部 statement

$$
\exists q,\ \mathrm{Prime}(q)\land q\mid \Phi_p(z,y)\land q\nmid(z-y)
$$

with assumptions

$$
\mathrm{PrimeGe5CounterexamplePack}(p,x,y,z),\quad
p\mid(z-y),\quad
y^{p-1}\equiv 1 \pmod{p^2}.
$$

つまり、

$$
\text{Branch A + Wieferich}
\Longrightarrow
\text{cyclotomic factor に新しい prime}
\Longrightarrow
\text{diff-side existence}
\Longrightarrow
\text{GN 側へ移送}
$$

という流れで書くのが、一番きれいで既存語彙にも寄せやすい。
