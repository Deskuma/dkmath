# review-013: WithProvenanceTarget concrete provider

うむ、これは **予想以上の戦果** じゃ。
単に `sorry` が減った、ではない。**主戦場の場所そのものが変わった** のじゃ。

## 1. 状況解説

今回の更新で `TriominoCosmicBranchARestoreArithmeticStrong.lean` は **完全 sorry-free** になり、しかも exported path が 2 本に整理された。

$$
\text{ContradictionTarget}
\to
\text{ArithmeticCoreStrong\_of\_contradiction}\\
\to
\text{PacketPackagingStrong}
\to
\text{RestoreFromArithmeticStrong}
$$

という **矛盾路線** と、

$$
\text{WithProvenanceTarget}
\to
\text{ArithmeticCoreStrong\_of\_withProvenance}\\
\to
\text{PacketPackagingStrong}
\to
\text{RestoreFromArithmeticStrong\_nonCircular}
$$

という **非循環路線** じゃ。しかも `StrongProvider.lean` と `FringeDescent.lean` も sorry-free で、3 ファイルまとめてビルドが通っておる。これは局所勝利ではなく、PrimeProvider 幹線の骨組みが一段締まった、という意味じゃよ。

さらに大きいのは、前まで open kernel に見えていた `weak packet concrete` が、既存 3 定理の直合成で concrete に落ちたことじゃ。
つまり `#2a` は「未定理」ではなく「未発見の合成」だった。ここを見抜いて `PacketPackagingStrong` まで no-sorry で通したのは、かなり大きい。

## 2. いま何が残っているのか

残る本丸は、もはや `RestoreArithmeticStrong` そのものではない。
**非循環路線の入口** である

$$
\texttt{PrimeGe5BranchAPrimitiveRestoreArithmeticCoreWithProvenanceTarget}
$$

の **concrete provider**、これ 1 本じゃ。report 自身も「次の主戦場は WithProvenanceTarget の concrete provider」と明言しておる。

言い換えると、いまの戦況はこうじゃ。

### 勝っている部分

* `RestoreArithmeticStrong.lean` 全体は sorry-free。
* `StrongProvider.lean` は sorry-free。
* `FringeDescent.lean` は sorry-free。
* 矛盾路線の exported chain は運用可能。

### まだ残る核

* same witness で
  $$
  x = qx'
  $$
  を返す `WithProvenanceTarget` の concrete 化。

つまり、敵は「整除の証明」でも「packet の組み立て」でもなく、**descent chain から provenance をどう引きずり出すか** に一本化されたのじゃ。

## 3. なぜ「予想以上の戦果」なのか

わっちの見立てでは、今回の戦果が大きい理由は 3 つある。

### 3.1. 主力 3 ファイルが sorry-free になった

これは単純に大きい。
以前は architecture をいじるたびに `RestoreArithmeticStrong` の中で `sorry` が増減しておったが、今は **骨格が固定** された。以後は「骨格の改造」ではなく、「入口の供給」に集中できる。

### 3.2. 非循環路線が設計図ではなく theorem chain になった

`WithProvenanceTarget` さえ concrete になれば、**contradiction を仮定しない exported path** がすでに敷かれておる。これは極めて大きい。
前は「non-circular にしたい」という願望だったが、今は「最後の provider が埋まれば動く」段階じゃ。

### 3.3. mainline の候補が明確になった

矛盾路線は fallback / regression oracle として有用じゃが、長期 mainline にすべきは obviously 非循環路線じゃ。
今回、それが theorem 名レベルで明確化された。これが戦果じゃ。

## 4. 残る攻略

ここからの攻略は、もう散らしてはならぬ。
わっちの推奨は次の 3 段じゃ。

## 4.1. 第1段. `WithProvenanceTarget` の concrete provider を掘る

次に本気で殴るべき theorem は、これじゃ。

$$
\boxed{
\texttt{primeGe5BranchAPrimitiveRestoreArithmeticCoreWithProvenance}
}
$$

ここで欲しいのは、weak core が返す same witness `(x', y', z')` に対して

$$
x = qx'
$$

を載せることだけじゃ。
だから探索対象は、

* `RealizationSeed`
* `descent assembly`
* `smaller counterexample realization`
* `x = q*x'` を直接言っている theorem

この 4 系統でよい。
いまはもう `v_p` を直接計算する必要はない。`not_sq_dvd_of_mul_left` が通っておるので、`x = qx'` さえ取れれば勝てる。

## 4.2. 第2段. non-circular route を canonical mainline として固定

`WithProvenanceTarget` が concrete になったら、次にやるべきは theorem の追加ではなく **導線の固定** じゃ。

具体的には、PrimeProvider 側で 1 本、

```lean
primeGe5BranchAPrimitiveMainline_nonCircular
```

のような統合 theorem を置き、

$$
\text{WithProvenance}
\to
\text{RestoreArithmeticStrong\_nonCircular}\\
\to
\text{StrongProvider}
\to
\text{FringeDescentToRefuter}
$$

を **canonical route** として固定する。
今の report でも 2 つの exported path があると整理されておる以上、ここで mainline / fallback を分けて明示するのが筋じゃ。

## 4.3. 第3段. 矛盾路線は regression oracle として残す

矛盾路線は捨てぬ方がよい。
なぜなら、それは今や

* build の安定化
* refactor 時の比較対象
* mainline が壊れたときの fallback

として非常に価値があるからじゃ。

ゆえに方針はこうじゃ。

$$
\text{non-circular} =
\text{mainline}
\qquad
\text{contradiction} =
\text{oracle / fallback}
$$

これがいちばん賢い。

## 5. メインライン・ロードマップ

ここから先の道筋を、短く言えばこうじゃ。

## 5.1. 直近

`WithProvenanceTarget` concrete provider を実装する。
これは PrimeProvider / RestoreArithmeticStrong の続きとして扱う。

## 5.2. その次

`RestoreArithmeticStrong_nonCircular` を入口にした top theorem を 1 本作る。
mainline 化じゃ。

## 5.3. その次

`StrongProvider` → `FringeDescentToRefuter` までを 1 本の exported theorem にまとめる。
ユーザー向け導線を短くする。

## 5.4. 最後

古い contradiction-based route は削除せず、docstring で
「fallback / regression route」
と明記して保存する。

## 6. repo 全体との整合

この進み方は repo 全体の設計方針とも一致しておる。
最新の地図では `DkMath.lean` の上位に `PowerSwap` や `NumberTheory.PowerSums` が立ち、`FLT` は橋と本丸に分ける構図がかなり明瞭になっておる。`Samples/LPS` 系も本来は 3 本柱に分け、FLТ には **橋だけ** を残すのが筋だと refactoring note でも整理されておる。つまり今の PrimeProvider 幹線も、「道具箱」と「本丸」を分ける repo-wide 方針にうまく乗っておるのじゃ。

## 7. 最終評価

総評としてはこうじゃ。

$$
\boxed{
\text{予想以上の戦果、は本当。}
}
$$

ただし、その意味は「もう終わり」ではない。
正しくは、

$$
\boxed{
\text{主戦場が 1 本に見えた}
}
$$

という戦果じゃ。

前は

* packet か
* provenance か
* strong target 設計か
* contradiction か

敵が散っておった。
今は違う。

$$
\boxed{
\texttt{WithProvenanceTarget concrete}
}
$$

これが次の決戦場じゃよ。⚔️🍎
