# Note: No.090 cp

## コラッツ予想は、何を教えてくれているのか？

## 1. いま見えているもの

うむ。ここで一度、手を止めて振り返るのはとても良い。

ここまでの成果は、単に `Collatz.PetalBridge` に補題が増えた、というだけではない。
数学的には、コラッツ写像が何を語っているのかが、少しずつ見えてきた。

今の到達点を一言で言うなら、

```text
コラッツ予想は、数が 1 に落ちるかどうかだけを問う問題ではなく、
2-adic な剥離量と剰余類遷移が、長期的に縮小力をどう回収するかを問う問題である。
```

じゃ。

今回までの実装では、`3 mod 8` が delayed-peeling channel、`7 mod 8` が retention channel として分離され、tail 側でも `height >= 2` と `height = 1` の分割が固定された。さらに `7 -> 7` の二歩 retention witness まで入っている。つまり、低剥離の中身が二種類に分かれた。

## 2. コラッツ予想は「奇妙な縮小問題」ではない

普通に見ると、コラッツ写像はこう見える。

```text
奇数なら 3n + 1
偶数なら 2 で割る
```

そして人間の直感では、

```text
3n + 1 で増えるのに、なぜ最後は小さくなるのか？
```

となる。

しかし加速 Collatz で見ると、奇数 \(n\) に対して本質はこうなる。

```text
3n + 1 を作る
そこから 2 を何個剥がすかを見る
```

この「何個剥がすか」が height。

```text
height(n) = v2(3n + 1)
```

ここでコラッツ予想が教えていることは、おそらく、

```text
局所的には増える step があっても、
2-adic な剥離構造は長期的には縮小力を回収する
```

ということじゃ。

## 3. `height = 1` は一種類ではなかった

ここまでで一番大きな気づきはこれ。

```text
height = 1 は、単なる悪い step ではない。
```

mod 8 で見ると、height-one は二つに割れる。

```text
3 mod 8:
  今は height = 1
  しかし次に height >= 2 を生む

7 mod 8:
  今は height = 1
  次も height = 1 側に残る
```

つまり、同じ `height = 1` でも、

```text
3 mod 8:
  遅れて縮小力を返す

7 mod 8:
  低剥離を持続させる
```

という違いがある。

これはかなり重要じゃ。
コラッツの難しさは「height = 1 があること」ではなく、

```text
retention channel がどれだけ続けられるか
```

に移った。

## 4. コラッツ予想が教えている第一のこと

第一の教訓は、

```text
値の大小ではなく、剰余類遷移を見るべき
```

ということ。

数値そのものを見ると、軌道は暴れる。

```text
上がる
下がる
また上がる
急に下がる
```

しかし Petal 座標で見ると、より構造的になる。

```text
1 mod 8:
  exact height 2

3 mod 8:
  delayed-peeling

5 mod 8:
  immediate strong peeling

7 mod 8:
  retention
```

これは、値列ではなく **状態遷移** じゃ。

つまりコラッツ予想は、自然数の大きさの問題に見えて、実は

```text
2-adic residue graph 上の軌道問題
```

として読むべきものなのかもしれない。

## 5. 第二のこと：悪い道は細い cylinder に追い込まれる

いま見えている次の道はこれ。

```text
低剥離が長く続くには、7 mod 8 retention channel を通る必要がある。
```

しかし `7 mod 8` も、さらに mod 16 で分かれる。

```text
7 mod 16:
  retention から delayed-peeling 側へ戻る

15 mod 16:
  retention が続く
```

おそらく、この構造は続く。

```text
7 mod 8
15 mod 16
31 mod 32
63 mod 64
...
```

のように、低剥離を長く続けるには、どんどん細い 2-adic cylinder に入らなければならない。

ここに、コラッツ予想が教えている第二のことがある。

```text
悪い挙動は存在できるとしても、
そのための条件はどんどん狭くなる。
```

これは「確率的にはほぼ起きない」という話に近いが、我々が目指しているのは確率ではなく、有限窓・剰余類・Lean 補題による構造記述じゃ。

## 6. 第三のこと：縮小力は遅れて戻る

ここまでの実装で、`3 mod 8` の意味が変わった。

以前なら、

```text
3 mod 8 は height = 1 だから弱い
```

と見ていた。

しかし実際には、

```text
3 mod 8:
  今は height = 1
  次に height >= 2
```

なので、二歩で見ると、

```text
1 + 2 >= 3
```

になる。

つまり、縮小力は必ずしもその場で現れない。

```text
ある step で不足した縮小力が、
次 step に予約されていることがある。
```

これはとても Collatz らしい。

コラッツ予想は、単発の増減ではなく、

```text
時間差で保存・回収される縮小力
```

を見よ、と言っているのかもしれない。

## 7. 第四のこと：局所分類だけでは足りない

mod 8 まで見ると、かなり分かった気になる。

しかし `7 mod 8` がある。

これは、

```text
低剥離が続くかもしれない
```

という道を残す。

すると mod 16 が必要になる。
mod 16 で見ると、さらに retention continuation と recovery に分かれる。

そして、おそらく mod 32、mod 64……と進む。

ここで見えるのは、

```text
どの有限解像度でも、まだ次の細分化がある
```

ということじゃ。

これは Petal 的には自然。

```text
観測解像度を上げるほど、
滞留 channel の内部構造が見える。
```

コラッツ予想は、有限の低解像度分類では閉じない。
だが、有限窓ごとには確実に構造が見える。

## 8. 第五のこと：Collatz は「反例をどこへ押し込めるか」の問題

もし反例があるとする。

それは、いつまでも十分な縮小力を回収できない軌道じゃ。

すると、その軌道は多くの時刻で `height = 1` を選び続ける必要がある。

しかし `height = 1` のうち、`3 mod 8` は次に縮小を返す。
だから、長く悪くいるには `7 mod 8` 側へ寄る必要がある。

さらに `7 mod 8` の中でも、回復する枝と retention 継続枝がある。

したがって反例は、どんどん

```text
より深い retention cylinder
```

へ押し込まれていく。

これはかなり良い視点じゃ。

```text
反例を探すのではなく、
反例が逃げ込める場所を狭めていく。
```

DkMath 的には、これは obstruction 解析じゃな。

## 9. Petal が果たしている役目

Petal はここで、単なる比喩ではなく、実装上の役目を持っている。

```text
OrbitWindow:
  有限観測窓

height:
  2-adic 剥離量

CountGe / CountEq:
  層への滞在数

residue count:
  剰余類 cell への滞在数

tail count:
  一歩後の受け皿

transition theorem:
  cell から cell への有向辺

sumS:
  累積 drift budget
```

つまり Petal は、

```text
Collatz 軌道を有限有向グラフ上の観測統計へ変換する装置
```

になっている。

これはかなり良い到達点じゃ。

## 10. コラッツ予想は何を教えてくれているのか

今の段階で、数学的にまとめるならこう。

```text
コラッツ予想は、
自然数の大小だけを見る問題ではなく、
2-adic residue address の有限遷移が、
遅延縮小力をどのように回収し、
低剥離 path をどのように細い cylinder へ追い込むかを問う問題である。
```

もっと短く言えば、

```text
コラッツ予想は、増大と縮小の問題ではなく、
剥離不足がどこで補償されるかの問題である。
```

さらに DkMath 風に言えば、

```text
Core:
  odd orbit label

Beam:
  3n + 1 による膨張

Gap:
  2-adic residue による剥離遅延

Big:
  累積 sumS による drift 回収
```

じゃ。

## 11. ここまでの成果の意味

ここまでで、我々は次を得た。

```text
1. height profile を定義した

2. layer-cake で sumS に接続した

3. height >= 2 を mod 4 = 1 に接続した

4. mod 8 partition を作った

5. 3 mod 8 を delayed-peeling channel として固定した

6. 7 mod 8 を retention channel として固定した

7. tail 側で extra-peeling / retention partition を作った

8. delayed-peeling は一般 k 窓で sumS に寄与することを示した
```

これは十分に立派な段階じゃ。

まだコラッツ予想は閉じていない。
しかし、何を閉じればよいかは、かなり見えてきた。

## 12. 次に閉じるべき問い

次の問いは明確。

```text
retention channel はどれだけ続けられるのか？
```

これを mod 16、mod 32、mod 64……で追う。

具体的には、

```text
7 mod 8 retention
  -> 15 mod 16 continuation
  -> 31 mod 32 continuation
  -> ...
```

のような構造があるかを見る。

そして、もし

```text
retention が L steps 続くなら、
初期値は 2^L 以上の精度で特定の residue に入る
```

と言えるなら、反例はどんどん薄い場所に押し込まれる。

ここが本丸じゃ。

## 13. 次の実装指針

Codex が戻ったら、次はこのあたりが良い。

```text
1. mod 16 で 7 mod 8 retention を二分する

2. 7 mod 16 は recovery 側へ行くことを示す

3. 15 mod 16 は retention continuation 側へ行くことを示す

4. 三歩 delayed recovery:
   7 mod 16 -> sumS n 3 >= 4

5. retention continuation witness:
   15 mod 16 and next retention -> low-peeling pattern
```

候補 theorem は前回の流れ通り。

```lean
theorem next_mod_eight_of_mod_sixteen_eq_seven
    {m : ℕ} (hm : m % 16 = 7) :
    ((3 * m + 1) / 2) % 8 = 3
```

```lean
theorem next_mod_eight_of_mod_sixteen_eq_fifteen
    {m : ℕ} (hm : m % 16 = 15) :
    ((3 * m + 1) / 2) % 8 = 7
```

そして orbit label 版。

```lean
theorem oddOrbitLabel_succ_mod_eight_eq_three_of_mod_sixteen_eq_seven
    (n : OddNat) (i : ℕ)
    (hmod : oddOrbitLabel n i % 16 = 7) :
    oddOrbitLabel n (i + 1) % 8 = 3
```

```lean
theorem oddOrbitLabel_succ_mod_eight_eq_seven_of_mod_sixteen_eq_fifteen
    (n : OddNat) (i : ℕ)
    (hmod : oddOrbitLabel n i % 16 = 15) :
    oddOrbitLabel n (i + 1) % 8 = 7
```

## 14. おまけ実験補題

Codex 復帰後に、賢狼が試してほしい実験はこれ。

```lean
theorem sumS_three_steps_ge_four_of_mod_sixteen_eq_seven
    (n : OddNat)
    (hmod : oddOrbitLabel n 0 % 16 = 7) :
    4 ≤ sumS n 3
```

読みはこう。

```text
0 step:
  7 mod 16
  -> height = 1

1 step:
  next 3 mod 8
  -> height = 1

2 step:
  next 1 mod 4
  -> height >= 2

therefore:
  sumS over 3 steps >= 4
```

これは `7 mod 16` が retention しても、二拍後には recovery することを示す補題じゃ。

もう一つ。

```lean
theorem sumS_three_steps_eq_three_of_mod_sixteen_eq_fifteen_and_next_next_seven
    (n : OddNat)
    (h0 : oddOrbitLabel n 0 % 16 = 15)
    (h1 : oddOrbitLabel n 1 % 8 = 7)
    (h2 : oddOrbitLabel n 2 % 8 = 7) :
    sumS n 3 = 3
```

これは retention continuation の witness。
悪い path を切り出すための補題じゃ。

## 15. 最後に

うむ、ぬしよ。
かなり良いところまで来ている。

コラッツ予想は、単に

```text
全部 1 に落ちるのか？
```

ではなく、

```text
低剥離が続こうとすると、
どんどん細い 2-adic residue channel に押し込まれる。
そして多くの channel は、遅れて縮小力を返す。
```

という構造を教えてくれているように見える。

この見方は、かなり DkMath らしい。

```text
値を見るな。
構造を見よ。

増減を見るな。
遅延して回収される保存量を見よ。

反例を見るな。
反例が逃げ込める cylinder を狭めよ。
```

この路線、かなり面白い。
クールタイム明けたら、次は `7 mod 8` の内部、つまり mod 16 retention 分岐を噛みに行こう。
