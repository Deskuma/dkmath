
# Branch A の次の一手について

こうするのがよい。

**結論** としては、
`PrimeGe5BranchAValuationPeelPacketFromErrorTarget` は **軽く試して、出なければ即やめる** 。
そして主戦場を **primitive packet descent** に移す。
いまはその判断をしても設計が崩れぬよう、final refuter までの橋が既に通っておるからじゃ。

## 1. . いま何が確定したか

いまの route は Lean 上で

$$
\text{peel exact-error lift} + \text{primitive packet descent}
\to
\text{smaller packet}
\to
\text{smaller counterexample}
\to
\text{distinguished-prime descent}
\to
\text{Branch A refuter}
$$

まで一本で読める。
つまり、`primeGe5BranchARefuter_of_errorLift_and_primitive` と gap-invariant 側の bridge によって、**primitive を本命にしつつ peel を差し込む設計** はもう完成しておる。

## 2. . わっちの判断

`PrimeGe5BranchAValuationPeelPacketFromErrorTarget` を本気の本丸にするのは、いまは得策ではない。
理由は単純で、peel 側はすでに

$$
p * B = C + \bigl(p^{p-1} * t_1^p\bigr) * E
$$

まで来ておるが、ここから packet を起こすには (E) に **追加の強い構造** が要る。
現状、その気配はまだ薄い。
なので、ここは **探索コストを制限** するべきじゃ。

## 3. . 次の一手

### 3.1. . まず 1 回だけ軽く試す

見るのはこれだけでよい。

$$
E = 0
\quad\text{または}\quad
p \mid E
\quad\text{または}\quad
t_1 \mid E
$$

のどれかが、既存補題から自然に抜けるか。
抜ければ `error -> packet` の concrete 化に進む価値がある。

### 3.2. . 抜けなければ即 pivot

その場合は、

$$
\text{valuation peel} = \text{obstruction extraction}
$$

と位置付けて確定し、
`PrimeGe5BranchAPrimitivePacketDescentTarget` を **本命 route** として押し上げる。

## 4. . 実務的には何を書くか

わっちなら、次はこの順じゃ。

1. `PrimeGe5BranchAValuationPeelPacketFromErrorTarget` 用の **試験的 lemma** を 1 本だけ置く
2. そこで強い extraction が出なければ、その target は保留にして終了
3. `PrimeGe5BranchAPrimitivePacketDescentTarget` の設計メモを前面化する
4. Branch A final `sorry` の本丸を primitive 側に固定する

## 5. . 一言で言えば

$$
\boxed{
\text{peel は少しだけ試す。だめなら切る。次は primitive を本命化する。}
}
$$

これがいちばん前へ進む道じゃよ。
