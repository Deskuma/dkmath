# final review

おお……S2 完了じゃ、D.。
これは見事に収穫まで持っていったのう。S2-V から S2-Z までを一括で閉じ、`OpenProblems.md`, `SmokeCheck.lean`, `Chapter2Summary.md`, `S3-Considerations.md`, `RouteMap.md` 更新、そして `History.md` の closure 記録まで揃った。Chapter 2 は、ただ実装が進んだだけでなく、 **再開可能な研究単位** として梱包された。

## 1. S2 の到達点

S2 の最終的な主張は、きわめて明確じゃ。

$$
d=3
$$

の ordinary primitive branch、すなわち

$$
q\ne3
$$

の枝について、

$$
PrimitiveBeam
\to
GN
\to
PowerBeam
\to
gcd / p\text{-adic valuation}
\to
contradiction
$$

までの no-sorry 抽象反駁エンジンが閉じた。`Chapter2Summary.md` でも、この claim と non-claim が明確に分けられている。

標準入口は、

```lean
DkMath.CosmicFormula.PowerGapBeam.CubicPrimitiveFLTContext
```

で、標準の contradiction endpoints は、

```lean
C.val_le_one_contradiction
C.squarefree_contradiction
```

じゃ。これが S2 の「使うべき表口」になった。

## 2. 何を主張してよいか

これは言ってよい。

**ピタゴラス宇宙式の Gap/Beam 構造は、(d=3) の ordinary primitive branch を no-sorry の抽象反駁エンジンとして捕まえた。**

一方、これはまだ言わない。

**FLT (d=3) 全体を閉じた。**

残っているのは、文書にも明記された通り、

$$
q=3
$$

の exceptional branch と、GN 側 fuel

$$
v_q(GN)\le1
$$

または

$$
Squarefree(|GN|)
$$

の自動供給じゃ。

この切り分けはとても健全じゃ。
賢狼の鼻にも、誇張の匂いはせぬ。

## 3. 文書化の価値

今回よかったのは、実装だけでなく、閉じるための文書群が揃ったことじゃ。

* `RouteMap.md`: theorem route と layer map
* `OpenProblems.md`: 次章送りの課題
* `Chapter2Summary.md`: Chapter 2 の claim / non-claim
* `S3-Considerations.md`: 次ブランチ候補
* `SmokeCheck.lean`: 標準 API surface の `#check`

この構成は実に良い。`RouteMap.md` にも closure documents の一覧が追加され、どこを読めば何が分かるかが明示された。

Lean では、補題が増えるほど「どこから入るのか」が見えなくなる。
今回の文書化は、その霧を晴らす灯火じゃな。

## 4. 検証状況

検証も揃っている。

* `lake env lean docs/dev/CF-Pythagoras-260427/SmokeCheck.lean` 成功
* `lake build DkMath.CosmicFormula.PowerGapBeamGN` 成功
* `lake build DkMath.CosmicFormula.PowerGapBeamPrimitive` 成功
* `lake build DkMath.CosmicFormula` 成功
* `PowerGapBeam*.lean` に新規 `sorry` なし

既存依存の `ZsigmondyCyclotomicResearch.lean:152` の `sorry` warning は残るが、これは今回の PowerGapBeam 層由来ではない、と境界も記録済みじゃ。

## 5. S3 の入口

S3 候補も綺麗に切られている。

おすすめ順は、文書の通りじゃな。

1. (q=3) exceptional branch の context/API 境界を設計する
2. GN fuel automation のため、Zsigmondy / squarefree 層から proved API を昇格できるか調べる
3. 一般次数 bridge または (d=4) route は、cubic ordinary branch とは分けて進める

特に S3 は、S2 を再び開くのではなく、S2 の境界から始めるべきじゃ。
`S3-Considerations.md` の「produce a context / produce GN fuel / exceptional route」という切り分けは、次の会話を始める合言葉としても使いやすい。

## 6. 総括

S2 は成功じゃ。

Chapter 2 は、

$$
\text{Pythagorean Gap/Beam}
\to
\text{cubic PowerBeam}
\to
\text{ordinary primitive FLT obstruction}
$$

という道を、no-sorry の抽象反駁エンジンとして閉じた。

これは「ピタゴラス宇宙式が FLT 方向へ伸びた」ことを示す、かなり強い節目じゃ。
しかも、claim / non-claim を分けているので、研究として誠実で、次へ進みやすい。

よくやった。
麦は刈り終えた。束ねて蔵に入れた。あとは少し寝かせれば、次の酒になるぞ。
