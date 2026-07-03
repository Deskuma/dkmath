# Note: No.139 cp

## 宇宙式保存法則の語彙に乗った局所観測

## うむ、かなり乗っている

はい。この部分はかなり明確に **宇宙式保存法則語彙に乗った** と見てよいと思う。

ただし、まだ「Collatz 全体が保存法則で閉じた」という段階ではなく、正確には、

```text
pressure-depth の隣接 edge における局所保存会計が、
宇宙式の Big / Body / Gap 的な保存語彙で読めるようになった
```

という段階じゃ。

今回の checkpoint `138` で入った構図は、

```text
next margin = current margin + net drop
```

そして、

```text
sign-change-up
  ↔ current margin <= 0
     and current margin + net drop > 0
```

だった。これは report 側でも「local zero-crossing theorem」として整理されている。

## 宇宙式語彙への対応

DkMath 的に言うと、ここはこう読める。

```text
current margin:
  現在の圧力余裕 / 現在の境界状態

net drop:
  retention obstruction の減少と continuation loss の差分から生じる局所駆動量

next margin:
  保存会計を通した次の境界状態
```

つまり、

```text
次状態 = 現状態 + 局所差分
```

になっている。

これはまさに宇宙式の保存法則語彙でいう、

```text
Big = Body + Gap
```

の「時間・深さ方向版」に近い。

より今回の形に寄せるなら、

```text
Next = Current + Net
```

じゃな。

ここで `Net` は、

```text
retention_drop - 2 * continuation_drop
```

として定義されている。checkpoint `136` でこの整数会計が Lean に固定され、checkpoint `137` で margin jump と net drop positive が同値になり、checkpoint `138` で zero-crossing まで到達した。

## 何が「保存」されているのか

ここで保存されているのは、数値そのものが一定という意味ではない。

保存されているのは、

```text
margin の変化量が、
retention drop と continuation drop の差分会計で完全に説明される
```

という構造じゃ。

つまり、margin が突然増えたように見えても、実際には

```text
retention obstruction がどれだけ抜けたか
continuation support がどれだけ失われたか
```

の差し引きで説明できる。

式としては、

```text
margin_next - margin_current
  = retention_drop - 2 * continuation_drop
```

これが保存会計の核じゃ。

したがって、local island も「謎の例外」ではなくなってきた。

## local island の読み替え

以前は local island は、

```text
prefix を壊す厄介な例外
```

だった。

しかし今は、

```text
left edge:
  current margin <= 0
  current margin + net drop > 0

right edge:
  current margin > 0
  current margin + net drop <= 0
```

という **pressure pulse** として読める段階に来ている。

つまり、島は例外ではなく、

```text
圧力深さ方向に現れる局所的な保存会計パルス
```

になる。

これは宇宙式語彙で言えば、

```text
Gap が一時的に抜ける
Body が境界を超える
次の深さで再び Gap 側に戻る
```

のような局所遷移じゃ。

## かなり DkMath 的に言える形

今の到達点を DkMath 風にまとめるなら、こうじゃ。

```text
PressureMargin は境界判定量である。
Retention は境界を押し戻す残留質量である。
Continuation は継続チャネルの支持質量である。
NetDrop は、Retention の減少から Continuation の減少を差し引いた局所駆動量である。

隣接 depth では、
next margin = current margin + net drop
が成り立つ。

したがって sign-change-up は、
current margin が非正であり、
net drop によって zero boundary を超える現象である。
```

これはかなり綺麗に保存法則語彙へ乗っている。

## ただし、まだ局所保存則

ここは大事じゃ。

今回できたのは、

```text
adjacent pressure-depth edge の局所保存会計
```

であって、

```text
Collatz orbit 全体の大域保存則
```

ではない。

まだ言ってはいけないことは、

```text
これで Collatz が収束する
pressure prefix が大域的に成り立つ
deep all-ones excursion が positive block を必ず作る
```

あたりじゃな。

でも、今できたものは強い。
なぜなら「例外的な sign-change/local-island」を、観測ラベルではなく、Lean 上の整数保存会計で説明し始めたからじゃ。

## 賢狼の見立て

この部分は、DkMath 宇宙式の中では、

```text
局所保存法則層
```

に入ったと見てよい。

特に、

```text
next margin = current margin + net drop
```

これはまさに小さな宇宙式じゃ。

そして次の `SourcePressureSignChangeDown` が入ると、local island は

```text
cross up
positive pulse
fall down
```

として閉じる。

そこまで行けば、かなりはっきり

```text
local island は宇宙式保存会計上の pressure pulse である
```

と言えるようになる。
