# Note: No.064-01

## 残る課題の３要素の解説

うむ。ここは今の交差点の **未供給三要素** じゃな。
今回の direct wrapper で、PrimitiveBeam / Zsigmondy witness family から finite GN log-capacity route へは直通化できた。だが、まだ本丸として残るのがこの 3 つじゃ。

```text
1. label recovery をどこから出すか
2. NoLift をどこから出すか
3. FLT / ABC 側の最終 bridge にどう渡すか
```

## 1. label recovery をどこから出すか

`label recovery` は、いまの形ではこれじゃ。

```lean
∀ i, i ∈ I → ∀ j, j ∈ I → qOf i = qOf j → mOf i = mOf j
```

意味は単純で、

```text
同じ prime label q が出たなら、
それは同じ Petal value / address から来たものだと復元できる
```

という条件じゃ。

なぜ必要かというと、finite log-capacity route では、同じ prime label を複数の index が再利用すると、同じ指数スロットを二重に数える危険がある。DkMath の R/log route では、prime-power witness の base prime を log cost として数え、同じ prime の重複は valuation slot / multiplicity budget で管理する設計になっている。 だから Petal 側でも、選んだ carrier labels が衝突していない、または衝突しても同じ住所へ戻る、と言える必要がある。

今の候補は三つある。

### A. `mOf = qOf` にしてしまう

一番簡単な実験 route。

```text
mOf i := qOf i
```

すると、

```text
qOf i = qOf j -> mOf i = mOf j
```

はほぼ自明になる。

ただし、この場合 `mOf` は Petal address value というより、prime label そのものになる。
つまり **住所値というより label-as-address** じゃ。制御実験としては良いが、Petal geometry の意味は薄い。

### B. `qOf = f(mOf)` で、`f` の injective 性から出す

これはすでに `f = id` と `f = nthPrime` で試した道じゃな。

```text
qOf i = f (mOf i)
f (mOf i) = f (mOf j) -> mOf i = mOf j
```

なら recovery が出る。

`nthPrime` route では本当に prime-valued な injective label map として使えた。だが、nth prime が GN を割るわけではないので、carrier 性は別仮定のままだった。これは「標準素数列実験」として健全。

### C. Primitive/Zsigmondy の構造から出す

これが本命じゃ。

```text
Primitive/Zsigmondy witness
  -> qOf i
  -> その q が出るなら、元の Petal address/value も復元できる
```

ただし、これは簡単ではない。
Zsigmondy の primitive 性は、

```text
q は a^d - b^d を割る
q は低次 a^m - b^m を割らない
```

という「次数方向の新規性」を与える。だが、それだけで

```text
same q -> same mOf
```

が出るとは限らない。

だから当面の現実路線はこうじゃ。

```text
まず label recovery は明示仮定のまま維持する。
次に、mOf = qOf 版や qOf = f(mOf) 版で特殊 wrapper を作る。
最後に、Primitive/Zsigmondy の uniqueness / address reconstruction が見えたら仮定を減らす。
```

結論として、**label recovery は今すぐ Zsigmondy から自動で出すものではない**。
まずは「同じ label は同じ address/value を意味する」という family-level 契約として扱うのが安全じゃ。

## 2. NoLift をどこから出すか

`NoLift` はこれじゃ。

```lean
PetalNoLiftPrimeChannel d x u q :=
  PetalPrimeChannel d x u q ∧ ¬ q ^ 2 ∣ GN d x u
```

意味は、

```text
q は GN を割る prime carrier である。
しかし q^2 は GN を割らない。
```

つまり local valuation で言えば、

```text
padicValNat q (GN d x u) = 1
```

へ行ける one-slot 条件じゃ。

ここは非常に重要。
なぜなら FLT 側では、もしある量が (d)-乗なら、prime valuation は (d) の倍数、少なくとも (d) 以上になる。そこへ NoLift の `= 1` をぶつけるのが狙いだからじゃ。

ただし、NoLift は Zsigmondy だけからは出ない。
今回の docs でも、Primitive/Zsigmondy witnesses は carrier location を供給するが、automatic no-lift は主張しない、という線を維持している。 これは正しい。primitive divisor は「新しい素因子」ではあるが、指数 1 でしか割らないとは限らない。

NoLift の供給候補は四つある。

### A. squarefree GN から出す

最も一般的で安全な道。

```text
Squarefree (GN d x u)
q ∣ GN d x u
Nat.Prime q
  -> ¬ q^2 ∣ GN d x u
```

これは標準的な構図。
DkMath の実装計画でも、primitive prime / GN / padicValNat を flow の痕跡として接続し、squarefree GN なら valuation は高々 1 という spine を作る方針が明記されている。

ただし、`GN d x u` が squarefree であること自体は強い。
だから一般 theorem というより、条件付き theorem として使うのがよい。

### B. d=3 特化の明示計算から出す

これは FLT に近い本命。

d=3 なら、

```text
GN 3 x u
```

は二次式になる。既存地図でも d=3 は明示計算エンジンとして扱われ、p-adic 上界や FLT d=3 の別解ルートが整理されている。

特に 3 共鳴、gcd 条件、局所化・単元化の整理が効くなら、

```text
Primitive/Zsigmondy
  + side conditions
  -> ¬ q^2 ∣ GN 3 x u
```

が狙える。

これは一般 d より現実的じゃ。
まず d=3 で閉じるべき。

### C. gcd / base-unit exclusion から出す

Petal 的にはこちらも本命。

```text
q が boundary 側や基底単位側へ吸収されない
q が 3 共鳴などの例外単位ではない
```

という条件を置き、square lift を排除する。

これはユーザーが言っていた「局所化」「単元化」に近い。
DkMath 用語で言えば、3 共鳴を基底単位側へ吸収し、残った carrier を素性として見る。

この route は美しいが、条件整理が難しい。
まずは theorem を細かく分けた方がよい。

```text
base unit exclusion
  -> q not in boundary resonance

q carrier
  + no resonance
  -> no square lift
```

### D. NoLift は当面 explicit contract のまま

実務上はこれが一番安全。

今回の direct wrappers でも、NoLift 版は明示的に

```lean
∀ i, i ∈ I → ¬ (qOf i)^2 ∣ GN ...
```

を受け取る設計になっている。
これは良い設計じゃ。供給元が後で見つかれば constructor を追加すればよい。

結論として、NoLift は次の順で攻めるのがよい。

```text
1. explicit NoLift contract として使う
2. squarefree GN から供給する一般 wrapper
3. d=3 特化で供給 theorem を探す
4. gcd / localization / unitization で仮定を弱める
```

## 3. FLT / ABC 側の最終 bridge にどう渡すか

ここは目的地が二つある。

```text
FLT:
  one-slot valuation と d-th-power valuation を衝突させる

ABC:
  distinct one-slot channels を support/rad lower bound に渡す
```

### 3.1. FLT 側への渡し方

FLT では、NoLift が与えるものはこれ。

```text
PetalNoLiftPrimeChannel d x u q
  -> padicValNat q (GN d x u) = 1
```

一方、FLT 的な仮定では、ある差冪や body が (d)-乗であるなら、

```text
padicValNat q (...) >= d
```

または

```text
d ∣ padicValNat q (...)
```

が出る。

したがって最終 bridge はこの形になる。

```text
NoLift:
  v_q(GN) = 1

d-th power transfer:
  v_q(GN) is multiple of d
  or d <= v_q(GN)

1 < d:
  contradiction
```

Lean theorem の候補はこう。

```lean
theorem petalNoLift_obstruction_of_dthPower_GN
    (hd1 : 1 < d)
    (hNoLift : PetalNoLiftPrimeChannel d x u q)
    (hpow : ∃ y, GN d x u = y ^ d) :
    False
```

ただし、これは少し強すぎる可能性がある。
実際には FLT では `GN` そのものが (d)-乗とは限らず、差冪全体や body から valuation transfer してくる形かもしれない。

より安全にはこう。

```lean
theorem petalNoLift_obstruction_of_padicValNat_ge
    (hd1 : 1 < d)
    (hNoLift : PetalNoLiftPrimeChannel d x u q)
    (hge : d ≤ padicValNat q (GN d x u)) :
    False
```

これはかなり薄くて強い。
NoLift から `padicValNat = 1`、`1 < d` から `¬ d ≤ 1` で矛盾。

その後で、別 theorem として

```text
d-th power assumption
  -> d ≤ padicValNat q (GN ...)
```

を供給すればよい。

つまり FLT bridge は二段に分ける。

```text
A. NoLift + valuation lower bound -> contradiction
B. FLT equation / d-th power transfer -> valuation lower bound
```

この分割が安全じゃ。

なお、DkMath の資料では FLT d=3 は Zsigmondy 原始素因子と p-adic 値評価による別解ルートとして、`padicValNat` の上界・下界を衝突させる形が整理されている。 いまの Petal NoLift は、その上界側をさらに DkMath/Petal 語彙で再包装するものになる。

### 3.2. ABC 側への渡し方

ABC 側で欲しいのは、`rad` / supportMass の下界じゃ。

DkMath の ABC bridge は、`supportMass = rad` を軸に、primitive witness family から supportMass lower bound へ渡す spine が育っている、という整理がある。

Petal 側から渡すならこう。

```text
PetalCarrierLabelNoncollisionOn I qOf
NatPrimeValuedOn I qOf
∀ i ∈ I, qOf i ∣ n
  -> product of distinct qOf i divides rad n
  -> lower bound for rad n / supportMass n
```

NoLift は ABC では必須ではない場合もある。
`rad` は squarefree support なので、同じ prime が一回でも出れば効く。したがって、ABC の最小 bridge は NoLift なしでも書ける。

```text
distinct prime carrier family
  -> rad lower bound
```

ただし NoLift があると、より強く読める。

```text
distinct one-slot carriers
  -> support が重複せず、local load も暴走しない
```

ABC 側の theorem 候補はこう。

```lean
theorem petalCarrierLabelMapData_rad_lowerBound
    (hdata : PetalCarrierLabelMapData I d x u mOf qOf) :
    ...
```

NoLift 版なら、

```lean
theorem petalNoLiftCarrierLabelMapData_supportMass_lowerBound
    (hdata : PetalNoLiftCarrierLabelMapData I d x u mOf qOf) :
    ...
```

中身は、おそらく既存の ABC bridge に合わせて

```text
NatPrimeValuedOn I qOf
PetalCarrierLabelNoncollisionOn I qOf
∀ i, qOf i ∣ GN d x u
```

を渡す形になる。

つまり ABC bridge はこう分ける。

```text
A. Petal data -> distinct prime divisors of GN
B. distinct prime divisors -> rad/supportMass lower bound
```

ここで A はもうほぼある。
B は既存 ABC bridge の theorem 名に合わせて wrapper を書けばよい。

## 三要素の関係図

現在の全体図はこうじゃ。

```text
PrimitiveBeam / Zsigmondy
  -> carrier location
  -> PetalPrimeChannel

label recovery
  -> label noncollision
  -> multiplicity budget
  -> Erdős finite log-capacity

NoLift
  -> padicValNat q GN = 1
  -> FLT obstruction

distinct carrier labels
  -> rad/supportMass lower bound
  -> ABC bridge
```

ここで、

```text
Primitive/Zsigmondy
```

が供給するのは主に **carrier location**。

```text
label recovery
```

が供給するのは **family の非衝突性**。

```text
NoLift
```

が供給するのは **local valuation one-slot**。

この三つは混ぜない方がよい。
混ぜると theorem は強く見えるが、後で証明不能になりやすい。

## 優先順位

わっちの推奨順はこれ。

```text
1. FLT 用の薄い obstruction theorem
   NoLift + d ≤ padicValNat q GN -> False

2. ABC 用の薄い support/rad wrapper
   PetalCarrierLabelMapData -> existing ABC lower-bound theorem

3. label recovery の特殊供給 theorem
   mOf = qOf
   qOf = f(mOf)
   primitive address uniqueness

4. NoLift の供給 theorem
   squarefree GN
   d=3 explicit
   localization/unitization side conditions
```

特に 1 はすぐ行ける可能性が高い。
NoLift の供給を待たずに、「NoLift があれば矛盾する」という最終受け皿を先に作れるからじゃ。

## まとめ

三つの未供給要素は、役割が違う。

```text
label recovery:
  family 全体で同じ label を二重使用しないための復元条件

NoLift:
  個々の prime carrier が GN 上で exact one-slot であるための局所条件

FLT / ABC bridge:
  NoLift は FLT の valuation 矛盾へ、
  distinct carrier labels は ABC の rad/supportMass 下界へ渡す出口
```

したがって次の方針がよい。

```text
label recovery は family noncollision の入口。
NoLift は local valuation obstruction の入口。
FLT / ABC bridge はそれぞれ別出口。
```

つまり、いま作るべきは「全部入りの巨大 theorem」ではない。
入口と出口を薄く保ったまま、

```text
Primitive/Zsigmondy
  -> Petal carrier
  -> label recovery / NoLift
  -> FLT or ABC
```

へ接続する小橋群じゃ。
