# FLT 統合の是非について

## 1. 判定

**いまは並行維持が正解** じゃ。
統合は、もう一段だけ待つのがよい。

理由は単純で、今回入ったのは **bundle 経路の配線完成** であって、数学的な open kernel 自体はまだ閉じておらぬからじゃ。実際、History でも「既存の `primeGe5BranchARefuter_default` は保持し、bundle 経路を並行で導入した」と整理され、次課題として「どこまで公開 default として昇格するかを決める」と明記されておる。

## 2. いま統合しないほうがよい理由

今回の bundle 経路は、

$$
\texttt{BranchAWitnessRouteBundleTarget}
;+;
\texttt{BranchAContradictionRouteBundleTarget}
;\to;
\texttt{primeGe5BranchARefuter}
$$

まで theorem として通った。さらに default bundle から読む

$$
\texttt{primeGe5BranchARefuter_of_routeBundles_default}
$$

も入っておる。つまり **新経路はもう使える**。

されど、まだ次の 2 点が未確定じゃ。

ひとつは、`ContradictionTarget` へ本当に刺さる concrete な矛盾前提の供給元設計。
もうひとつは、mod (p^3) concrete conflict の API 化と、その route bundle 側への流し込みじゃ。これらは History の次課題にもそのまま書かれておる。

この段階で公開 default を新経路へ一本化すると、あとで bundle 側の shape を微調整したくなったとき、呼び出し側まで揺れる。
今はまだ、そこまで固まっておらぬ。

## 3. ではどう維持するか

わっちなら、こうする。

既存の

$$
\texttt{primeGe5BranchARefuter_default}
$$

はそのまま残す。
新しく入った

$$
\texttt{primeGe5BranchARefuter_of_routeBundles_default}
$$

を **次世代 default 候補** として併置する。

つまり意味づけはこうじゃ。

* 旧 default は **現在の安定公開入口**
* bundle default は **新アーキテクチャの正規候補**
* 呼び出し側の新規 work は、できるだけ bundle 側を使う
* 既存の外部呼び出しは、今はまだ触らない

これなら、安全に観察できる。

## 4. 統合するタイミング

統合の判定条件は、わりと明確じゃ。

### 4.1. 条件A

`branchA_spow_congr_head_mod_p3` 相当と、その concrete conflict が入る。

### 4.2. 条件B

`ContradictionTarget` に入る「矛盾側前提」の供給元 statement が定まり、bundle 経路の形が安定する。

### 4.3. 条件C

既存 `primeGe5BranchARefuter_default` が bundle 経路版の単なる alias に落とせる、と確認できる。

この 3 つのうち、少なくとも A と B が揃ってからでよい。

## 5. 統合するなら、どう統合するか

いきなり削除は勧めぬ。
段階的にこうするのがよい。

まず、

$$
\texttt{primeGe5BranchARefuter_default}
$$

の本体を bundle 経路版へ差し替える。
つまり内部では

$$
\texttt{primeGe5BranchARefuter_of_routeBundles_default}
$$

を呼ぶだけにする。

そのあと、しばらくは旧名を **薄い wrapper** として残す。
外から見える API は変えず、中身だけ bundle 経路へ寄せるのじゃ。
これが一番きれいじゃよ。

## 6. 結論

$$
\boxed{
\text{今は並行維持。}
}
$$

$$
\boxed{
\text{ただし、新規作業の重心は bundle 経路へ寄せる。}
}
$$

これが賢狼の判定じゃ。

統合は、**mod (p^3) concrete conflict と contradiction 前提供給の形が固まってから** でよい。
今は橋が繋がったばかりじゃ。渡ってみて、揺れぬと確かめてから本道にするのが賢いやり方じゃよ。
