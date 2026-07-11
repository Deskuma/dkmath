# Note: No.064-03

## 失敗は成功のもと

「人間は間違えるようにできていた」

王道ルートばかりで間違った道を進んでないのが経験不足となっている可能性があるわね。
矛盾を導く補題を、自動回避して、あえて書いてないよね？

書いておくと、この道を行くから行き止まり。だから、その道ではない。
と、正しい道はこっちしか無い。ってハッキリ言えるようになるでしょ。

行き止まりの道も、途中までは引き返せるから、行っても良い。
だが、ここから先は確実に行き詰まる。という線引もある。

だから、あえて破綻する仮定を入れて、そういう仮定が入ってくるとダメになる。
を、多めに用意しておいたほうが良いと思うのよ。

人間がミスをするのは、実はこの原理が、次の経験に活かせるから、あえて間違えるんだよ（笑）

---

うむ。これはかなり大事な実装哲学じゃ。
わっちも賛成じゃよ。

いまの DkMath は、かなり **王道の spine** を綺麗に積んでおる。たとえば実装計画では、まず確率過程全体ではなく `Big = Body + Gap`、primitive prime / `GN` / `padicValNat`、ABC bridge という代数的・構造的 spine を先に作る方針になっておる。
これは正しい。だが、正しい道だけでは **なぜ他の道がダメなのか** が theorem として残らぬ。

## 1. 「失敗補題」は作るべき

Lean では、行き止まりの道はこう書くのがよい。

```lean id="7o2dax"
theorem bad_assumption_leads_to_false
    (hbad : BadAssumption ...) : False := by
  ...
```

または

```lean id="a39dk8"
theorem not_bad_assumption :
    ¬ BadAssumption ... := by
  intro hbad
  exact bad_assumption_leads_to_false hbad
```

これは `False` を仮定する危険な証明ではない。
むしろ **どの仮定が世界を壊すか** を Lean に記録する安全な theorem じゃ。

注意点は一つ。
`axiom hbad : BadAssumption` のように破綻仮定を公理として追加してはいけない。
それをやると `False.elim` で何でも証明できる腐った宇宙になる。
正しい使い方は、

```text id="c53zrh"
BadAssumption → False
```

として、 **仮定を入れた瞬間に破綻する** ことだけを theorem 化することじゃな。

## 2. DkMath で用意すべき「行き止まり補題」の型

わっちなら、次の 5 系統を作る。

## 2.1. label recovery 失敗補題

これは、

```text id="l85wgf"
同じ label なのに違う address/value へ戻る
```

という破綻。

候補名はこんな感じ。

```lean id="lxzzhx"
theorem labelRecovery_contradiction_of_same_label_ne_value
```

形は、

```lean id="a69dse"
theorem labelRecovery_contradiction_of_same_label_ne_value
    (hrec : ∀ i, i ∈ I → ∀ j, j ∈ I →
      qOf i = qOf j → mOf i = mOf j)
    (hi : i ∈ I) (hj : j ∈ I)
    (hlabel : qOf i = qOf j)
    (hneq : mOf i ≠ mOf j) :
    False := by
  exact hneq (hrec i hi j hj hlabel)
```

これは小さいが強い。
「この label map は recovery と両立しない」と即座に言える。

## 2.2. noncollision 失敗補題

これは、

```text id="7m3z52"
valueInjective があるのに、別 index が同じ value を持つ
```

という破綻。

```lean id="14bv7l"
theorem valueInjective_contradiction_of_same_value_ne_index
```

形は、

```lean id="anv8x2"
theorem valueInjective_contradiction_of_same_value_ne_index
    (hinj : Set.InjOn mOf ↑I)
    (hi : i ∈ I) (hj : j ∈ I)
    (hvalue : mOf i = mOf j)
    (hne : i ≠ j) :
    False := by
  exact hne (hinj hi hj hvalue)
```

これにより、

```text id="f4xc31"
同じ address/value に二つの carrier を載せる道は行き止まり
```

と言える。

## 2.3. NoLift 失敗補題

ここが本命じゃな。

`NoLift` は

```text id="ezkdtu"
q ∣ GN
かつ
¬ q^2 ∣ GN
```

の世界。

だから破綻補題は、

```lean id="q3v735"
theorem noLift_contradiction_of_square_dvd_GN
```

形は、

```lean id="4yxseb"
theorem noLift_contradiction_of_square_dvd_GN
    (hNoLift : ¬ q ^ 2 ∣ GN d x u)
    (hlift : q ^ 2 ∣ GN d x u) :
    False := hNoLift hlift
```

これ自体は一行じゃ。
だが、これを独立 theorem 名で持つ意味は大きい。

なぜなら、後で

```text id="j0pnog"
ある route から q^2 ∣ GN が出た
```

瞬間に、

```text id="741elt"
その route は NoLift bridge と両立しない
```

と機械的に言えるからじゃ。

## 2.4. valuation 過剰補題

NoLift の p-adic 版も必要じゃ。

```text id="43s2iq"
padicValNat q (GN d x u) = 1
```

を持っているとき、

```text id="s32a6t"
2 ≤ padicValNat q (GN d x u)
```

は破綻する。

候補名：

```lean id="bd8m6h"
theorem padicValNat_eq_one_contradiction_of_two_le
```

形は、

```lean id="y8av49"
theorem padicValNat_eq_one_contradiction_of_two_le
    (hval : padicValNat q (GN d x u) = 1)
    (hge : 2 ≤ padicValNat q (GN d x u)) :
    False := by
  omega
```

これは FLT 側でかなり効く。
なぜなら反例仮定から (q^p \mid z^p) 型の下界が出て、NoLift 側から valuation 上界 (1) が出ると、そこで衝突するからじゃ。

実装計画でも、primitive prime が `GN` 側へ流れ、squarefree `GN` なら valuation が高々 (1) になる線が最低限の theorem として挙げられている。
この「上界と下界が衝突する」補題を、明示しておくのがよい。

## 2.5. bridge 誤接続補題

ABC 側は bridge 層が強くなっておるが、本体大定理とはまだ別、という整理が既にある。特に `supportMass = rad` を軸に primitive witness family から `rad` 下界へ行く spine が育っている。

ここにも失敗補題が要る。

たとえば、

```text id="07kzy5"
同じ prime channel を重複して数えたのに
disjoint channel family として扱う
```

これは破綻。

候補名：

```lean id="83xxpe"
theorem disjointChannels_contradiction_of_duplicate_label
```

また、

```text id="nwiigk"
rad 下界に使う prime が実は support に入っていない
```

も破綻。

```lean id="7j65fl"
theorem supportMass_contradiction_of_prime_channel_not_in_support
```

これらは、ABC bridge が「翻訳層」として純粋であるために重要じゃ。設計でも ABC 側は本体定理ではなく bridge に徹する方針だった。

## 3. ファイルとしては `Obstruction.lean` が欲しい

わっちならこう分ける。

```text id="xnsr1h"
DkMath/Petal/Obstruction.lean
DkMath/NumberTheory/ValuationFlow/Obstruction.lean
DkMath/FLT/PrimeProvider/Obstruction.lean
DkMath/ABC/BridgeObstruction.lean
```

役割はこう。

```text id="3yobte"
Petal/Obstruction
  label recovery, noncollision, same-label/different-address の破綻

ValuationFlow/Obstruction
  valuation lower/upper conflict, squarefree conflict, lift conflict

FLT/PrimeProvider/Obstruction
  FLT 反例 pack から出る valuation 下界と NoLift 上界の衝突

ABC/BridgeObstruction
  supportMass/rad channel の重複・非 support・非 disjoint の破綻
```

名前規則は、以前の資料にも `mass_*`, `branch_*`, `hit_*`, `flow_*`, `abc_*`, `tail_*` を固定する方針がある。
それに合わせるなら、

```lean id="k4pl8z"
petal_obstruction_*
flow_obstruction_*
flt_obstruction_*
abc_obstruction_*
```

でもよい。

## 4. 「途中までは行ける」を theorem 化する

ぬしの言う通り、行き止まりにも段階がある。

```text id="6htv20"
A. ここまでは合法
B. この追加仮定を入れると破綻
C. したがってこの分岐は採れない
```

Lean ではこれを三段にする。

```lean id="646r0m"
structure BadRoutePrefix where
  ...
```

```lean id="w3lnbh"
def BadRouteExtraHypothesis (...) : Prop := ...
```

```lean id="c0lzdp"
theorem badRoutePrefix_contradiction_of_extra
    (R : BadRoutePrefix ...)
    (hbad : BadRouteExtraHypothesis ...) :
    False := by
  ...
```

これがあると、
「この route は途中まで有効な構成だが、NoLift を要求する最終 bridge へは渡せない」
と、かなり正確に言える。

これは研究記録としても美しい。
間違いを消すのではなく、 **どこまで正しく、どこから破綻するか** を保存するわけじゃ。

## 5. 今すぐ作るなら最小セットはこれ

最初から大きくしなくてよい。
まずはこの 6 本。

```lean id="m87gy9"
theorem labelRecovery_contradiction_of_same_label_ne_value
theorem valueInjective_contradiction_of_same_value_ne_index
theorem noLift_contradiction_of_square_dvd_GN
theorem padicValNat_eq_one_contradiction_of_two_le
theorem squarefree_contradiction_of_square_prime_dvd
theorem disjointChannels_contradiction_of_duplicate_label
```

この 6 本だけで、

```text id="w4rjuf"
label map の破綻
carrier family の破綻
NoLift の破綻
valuation の破綻
squarefree の破綻
ABC channel counting の破綻
```

が地図に載る。

## 6. 賢狼の結論

ぬしの言う「わざと間違える」は、Lean ではこう言い直せる。

```text id="xc4we5"
失敗する仮定を公理として採用するのではなく、
失敗する仮定が False を導くことを theorem 化する。
```

これは強い。
しかも、王道ルートの補強になる。

なぜなら、証明とは「この道で行ける」だけではなく、

```text id="pqbemj"
他の道はここで詰まる。
だから、この条件が必要。
だから、この橋を渡るしかない。
```

を示す営みでもあるからじゃ。

わっちはこう見る。

```text id="48bz4n"
Positive route:
  bridge theorem

Negative route:
  obstruction theorem

両方そろって初めて、地図になる。
```

そして DkMath は、もう positive route はかなり育っておる。
次に必要なのは、ぬしの言う通り **行き止まりの標識** じゃ。
これは経験不足の補完ではなく、理論の防御壁になる。
いやはや、たわけた遠回りに見えて、実は一番賢い地図作りじゃよ。
