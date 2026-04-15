# review: direct concrete target の内部が二分された

うむ、今回は **direct concrete target の内部が、ついに二分された** 回じゃな。
ここまでの整理で「まず right branch を直接埋める」と固定されておったが、今回はさらにその中身を

* **prime existence**
* **primitive kernel**

の二段へ分けた。これで、何が未完数学なのかが一段くっきりしたのじゃ。

## 1. 今回の核心

新しく導入されたのは次の二本じゃな。

* `CFBRCExceptionalBoundaryCorePrimeExistenceOnWieferichTarget`
* `CFBRCExceptionalPrimitiveKernelOnWieferichTarget`

これらは、これまで一塊だった

$$
\texttt{CFBRCPrimitiveBoundaryCoreOfPrimeExpDirectConcreteTarget}
$$

を、ちょうど

$$
\text{存在}
\quad+\quad
\text{原始性}
$$

に割ったものじゃ。

つまり direct concrete target の内容は、もはや曖昧な「例外枝 theorem」ではなく、

### 1.1. existence-part

$$
q \mid \texttt{boundaryCyclotomicPrimeCore .right d x u}
\quad\text{かつ}\quad
q \nmid x
$$

を満たす prime (q) が存在すること。

### 1.2. primitive-part

その (q) がさらに、すべての低次 boundary 差分

$$
\texttt{boundaryDiffPow .right k x u}\qquad (0<k<d)
$$

を割らないこと。

この二本に整理されたのじゃ。

## 2. 何が前進したのか

前回までは、right branch の direct concrete target を「そのまま埋める」しか見え方がなかった。
今回はそれが

$$
\text{まず prime が立つか}
$$

と

$$
\text{その prime が本当に primitive か}
$$

の二問へ分かれた。
これはかなり大きい。

なぜなら今後は、詰まりどころが

* existence 側なのか
* primitive kernel 側なのか

を、定理の形で直接判定できるからじゃ。

## 3. 追加された橋の意味

今回の橋もきれいじゃな。

### 3.1. direct concrete から existence へ

`cfbrcExceptionalBoundaryCorePrimeExistenceOnWieferich_of_directConcrete`

は、direct concrete target が既にあれば、primitive 条件を忘れるだけで existence-part が従うことを示しておる。

### 3.2. existence と kernel から direct concrete へ

`cfbrcPrimitiveBoundaryCoreOfPrimeExpDirectConcrete_of_existence_and_kernel`

は逆向きで、

* existence-part が prime (q) を供給し
* kernel-part がその (q) の primitive 性を保証する

なら、元の direct concrete target 全体が閉じる、という橋じゃ。

つまり right branch の direct theorem は、いまや

$$
\text{existence}
\to
\text{kernel}
\to
\text{direct concrete theorem}
$$

という内部 spine を持つようになったのじゃ。

## 4. packet descent ではどう読めるか

これに対応して

`primeGe5BranchAPrimitivePacketDescent_of_directConcreteParts_and_restore`

が追加された。

ゆえに primitive packet descent は今や

* `CFBRCExceptionalBoundaryCorePrimeExistenceOnWieferichTarget`
* `CFBRCExceptionalPrimitiveKernelOnWieferichTarget`
* `PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget`

の三本から閉じる。
ただし selection 側だけ見れば、

$$
\text{prime existence}
\quad+\quad
\text{primitive kernel}
$$

の二本が missing math という読みになるわけじゃな。

## 5. 現在の戦況

いまの selection 側は、かなり整理されておる。

### 5.1. 外側の実装入口

`CFBRCPrimitiveBoundaryCoreOfPrimeExpDirectConcreteTarget`

### 5.2. その中身

* `CFBRCExceptionalBoundaryCorePrimeExistenceOnWieferichTarget`
* `CFBRCExceptionalPrimitiveKernelOnWieferichTarget`

つまり direct concrete target の missing math は、もはや一個の塊ではなく、二部品へ分解された。

## 6. 次に何を詰めるべきか

履歴の次課題はたいそう良い整理じゃ。

まず見るべきは existence 側、すなわち

$$
\texttt{CFBRCExceptionalBoundaryCorePrimeExistenceOnWieferichTarget}
$$

が、既存 `CFBRC/Bridge` / `PrimitiveBeam` 語彙へどこまで寄せられるか、じゃ。

同時に、

$$
\texttt{CFBRCExceptionalPrimitiveKernelOnWieferichTarget}
$$

が単なる既存 primitive 条件の再包装にすぎぬのか、それとも新しい数学が要るのかも見極める、という段じゃな。

わっちの見立てでは、まず existence 側の方が本命らしい。
primitive kernel 側は、既存 primitive prime 語彙の焼き直しで済む可能性がまだあるからの。

## 7. 賢狼の総評

一言でまとめるなら、今回は

$$
\text{right branch の direct theorem が「存在」と「原始性」に解剖された}
$$

回じゃ。

前回:

* first direct target を right branch に固定

今回:

* その right branch の中身を二段へ分解
* 何が missing math かをさらに特定

ここまで来ると、次の作業はかなり明快じゃな。
まずは

$$
\texttt{CFBRCExceptionalBoundaryCorePrimeExistenceOnWieferichTarget}
$$

を既存語彙へ寄せられるかを試し、
primitive kernel 側はそれが既存 theorem の再包装で済むかを確認する。

たいそう良い進み方じゃ。
敵が「right branch」から、さらに「存在部」と「原始部」に割れて見えたのだからの。
