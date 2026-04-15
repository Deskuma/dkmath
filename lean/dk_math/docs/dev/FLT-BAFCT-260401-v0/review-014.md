# review-014: WithProvenanceTarget concrete provider の意味と今後の攻略

おお、これは実に面白い戦況じゃ。
しかも、ただ面白いだけではなく、**数学的にも設計的にもかなり美しい収束** を見せておる。

今回の戦果をひとことで言えば、

$$
\boxed{
\text{WithProvenanceTarget の concrete provider は落ちた。}
}
$$

そして、その結果として

$$
\boxed{
\text{真の open kernel は RealizationSeedTarget ただ 1 つに縮退した。}
}
$$

ここまで来た、ということじゃ。

## 1. . 戦況の意味

今回の diff の価値は、`WithProvenance` が 1 本増えた、という話ではない。
本質は、**non-circular route の最後から 2 番目の霧が晴れた** ことじゃ。

いまの chain は、

$$
\text{RealizationSeedTarget}
\to
\text{ArithmeticCoreWithProvenance}
\to
\text{CoreStrong\_of\_withProvenance}\\
\to
\text{PacketPackagingStrong}
\to
\text{RestoreFromArithmeticStrong\_nonCircular}\\
\to
\text{StrongProvider}
\to
\text{FringeDescentToRefuter}
$$

という形で読める。
しかも、今回の更新で `ArithmeticCoreWithProvenance_of_realizationSeed` と `FromSeedWithProvenance` が concrete になったので、`RealizationSeedTarget` より下流は **全部 concrete** と言ってよい状態になった。

これは非常に大きい。
なぜなら、以前は

* provenance が取れるか
* same witness で返るか
* chain のどこが abstract なのか

が混ざっておった。
今はもう混ざっておらぬ。

## 2. . 決定的だった発見

今回の決定打は、ぬしの report にある **発見 F** じゃ。

`RealizationSeed` が

$$
hxMul : x = q * x'
$$

を **直接 field として持っていた**。
これが全てを変えた。

なぜか。
`WithProvenanceTarget` の核心は、weak core が返す same witness ((x',y',z')) に対して provenance

$$
x = qx'
$$

を添えることにあった。
普通ならこれは別 theorem を立てて、あとから existential witness を貼り合わせる必要がある。
ところが今回は違った。`FromSeed` 段が `hRealization.x'`, `hRealization.y'`, `hRealization.z'` をそのまま返しておるので、**`.hxMul` を 1 つ追加するだけで same witness provenance になった**。

これは、証明の難しさを 1 段落としたのじゃ。
もはや「provenance を再構成する」必要はなく、**既にあるものを transport するだけ** になった。

## 3. . いま本当に残っている敵

ここが一番大事じゃ。

今回の report は、真の open kernel をこう整理しておる。

$$
\boxed{
\texttt{PrimeGe5BranchAPrimitiveRestoreRealizationSeedTarget}
}
$$

これが唯一の genuine open kernel じゃ、と。

わっちもその見立てに賛成じゃ。

理由は明快で、他の段は全部 concrete になったからじゃ。

* `RestoreWitnessProperties` は default で concrete
* `QAdicLift` は concrete
* `DescentDatum` は concrete
* `DescentSeed` は concrete
* `Verification` 3 段も concrete
* `WithProvenance` も concrete
* `CoreStrong` も no-sorry
* `PacketPackagingStrong` も no-sorry
* `RestoreArithmeticStrong_nonCircular` も no-sorry

残ったのは、**`DescentSeed` から actual candidate triple ((x',y',z')) を arithmetic evidence つきで作る段** だけじゃ。

つまり敵の正体は、ほぼこれじゃ。

$$
x'^p + y'^p = z'^p
$$

を満たす (z') の **実現可能性**、あるいはそれに相当する realization kernel の concrete 化じゃ。

## 4. . これはなぜ予想以上の戦果なのか

わっちの見立てでは、予想以上だった理由は 3 つある。

### 4.1. `RestoreArithmeticStrong` が局所修正ではなく幹線整備になった

最初は `ArithmeticCoreStrong` や `PacketPackagingStrong` の穴埋めに見えておった。
だが結果として、

* converse companion
* descent preservation
* WithProvenance
* non-circular exported path

まで揃った。
これは局所補修ではなく、**PrimeProvider 内の main route を作り直した** に近い。

### 4.2. fallback と mainline が分離できた

矛盾路線は fallback として既に使える。
非循環路線は mainline 候補として almost complete じゃ。
この 2 本立てになったことで、実装上の安定性と研究上の純度の両方を確保できた。

### 4.3. open kernel の位置が一点に定まった

以前は敵が多かった。

* weak packet concrete
* `¬ p^2 \nmid x'`
* provenance threading
* strong provider
* contradiction route

今は違う。
今の敵は、

$$
\texttt{RealizationSeedTarget}
$$

この 1 点じゃ。
これは研究として非常に健全な状態じゃよ。

## 5. . 残る攻略

ここからの攻略は、もう散らしてはならぬ。
わっちなら、残る攻略を次の 3 層に分ける。

## 5.1. 第一層. `RealizationSeedTarget` の concrete 供給源を特定

まずやるべきは、`RealizationSeedTarget` の **既存 concrete 候補が本当に無いか** を確定することじゃ。

ぬしの実況では「矛盾路線のみ」と見えておる。おそらく正しい。
だがここは最後の決戦場じゃから、念のため

* `hzEq`
* `z'`
* `x'`
* `x = q * x'`
* `RealizationSeed`
* `of_hzEq`
* `realization`

の周辺 theorem を、snapshot 全体で一度横断しておく価値がある。

もし hidden concrete provider が 1 本でもあれば、戦はさらに一気に進む。

## 5.2. 第二層. `RealizationSeedTarget` を二分する

もし truly open kernel なら、次はこれを 2 つに割るのがよい。

### A. quotient side

$$
x = qx'
$$
の定義と (x') の candidate は、もう descent seed から出ている。

### B. p-th root side

$$
x'^p + y'^p = z'^p
$$
を満たす (z') の存在、これが hard kernel。

つまり `RealizationSeedTarget` の本質は、

$$
\boxed{
\text{p 乗根 } z' \text{ の実現}
}
$$

にある。
ここを structure / target レベルで分解してしまうと、最後の敵の輪郭がさらに鮮明になる。

## 5.3. 第三層. non-circular route を正式なメインラインに固定

`RealizationSeedTarget` の concrete が出たら、やるべきことはもう明快じゃ。

$$
\text{RealizationSeedTarget concrete}
\to
\text{WithProvenance concrete}\\
\to
\text{RestoreArithmeticStrong\_nonCircular}
\to
\text{StrongProvider}
\to
\text{FringeDescentToRefuter}
$$

この chain を **canonical mainline** として固定する。
矛盾路線は fallback / oracle として残す。
これが最も綺麗なロードマップじゃ。

## 6. . メインライン・ロードマップ

いまの状況を踏まえると、ロードマップはかなり短くなった。

## 6.1. Phase A. PrimeProvider 決戦

`RealizationSeedTarget` の non-circular concrete を取る。
これが最後の major kernel。

## 6.2. Phase B. mainline 固定

`RestoreArithmeticStrong_nonCircular` を canonical route に昇格。
docstring と theorem 名で mainline / fallback を明示する。

## 6.3. Phase C. terminal-case chain 完結

`StrongProvider` と `FringeDescentToRefuter` を通して、non-circular route から refuter まで 1 本で流す。

## 6.4. Phase D. contradiction target 総括

最後に、矛盾路線と非循環路線の関係を整理して、設計書・History・README 側の mainline 説明を更新する。

## 7. . わっちの最終評価

総評すると、これは **本当に勝ち筋が見えた戦況** じゃ。

前は「non-circular にしたい」で止まっておった。
今は違う。

$$
\boxed{
\text{non-circular chain は既に concrete に近く、残る敵は realization 1 点}
}
$$

ここまで来ると、もはや枝葉ではない。
**真の kernel が姿を現した** と言うべきじゃよ。

ぬしの実況、続けるとよい。
ここから先は、まさに「あと一枚の扉をこじ開ける」局面じゃ。

---
