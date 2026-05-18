# review

うむ。DKMK-007G は **unit mass の玩具段階を越えて、mass model 差し替え可能性を確認した回** じゃ。
前回 DKMK-007F では `unitNatMassSpace` により source mass bound を \(C=1\) で閉じた。今回は `nonunitNatMassSpace` を追加し、`1` だけを質量 \(0\)、それ以外を質量 \(1\) とする bounded concrete mass でも、selected / canonical の divisor-step hitting route が同じく \(\le1\) で通ることを確認しておる。

## 1. 今回の核心

追加された mass model はこれじゃ。

```lean
def nonunitNatMassSpace : MassSpace ℕ where
  μ := fun n => if n = 1 then 0 else 1
```

数学的には、

$$
\mu(1)=0,\quad \mu(n)=1\text{ for }n\ne 1
$$

という指示関数型の質量じゃな。

これは最終的な tail mass ではない。
しかし `unitNatMassSpace` と違って、下降 chain が終端 \(1\) に到達した場合を質量 \(0\) として区別できる。つまり、 **下降の終端を見分ける最初の nontrivial bounded mass** になっておる。

## 2. divisibility-monotone が閉じた意味

今回、

```lean
theorem nonunitNatMassSpace_dvdMonotone :
    DvdMonotoneMass nonunitNatMassSpace
```

も証明された。

これは重要じゃ。`SourceControlledChainFamily.ofDivisorStep` は `DvdMonotoneMass M` を要求するので、ここが閉じないと divisor-step route に流せない。

証明の中身は自然じゃ。

$$
a\mid b
$$

で、もし \(b=1\) なら \(a=1\)。したがって両方の質量は \(0\)。
もし \(b\ne 1\) なら \(\mu(b)=1\) なので、\(\mu(a)\le 1\) は自明。

この mass は単純だが、divisibility に沿って増えすぎない。だから DKMK-007E の divisor-step bridge にそのまま入る。

## 3. selected route の追加

selected route 側には次が追加された。

```lean
PrimePowerWitnessProvider.globalLogCapacitySubMarkovShadow_nonunitDivisorStep_weightedHitMass_le_one
```

これは、`globalLogCapacitySubMarkovShadow` を one-step divisor descent family

$$
chain(q)={s.1/q,s.1}
$$

へ載せ、mass model として `nonunitNatMassSpace` を使ったとき、primitive set \(A\) の weighted hit mass が \(1\) 以下になる、という定理じゃ。

ここで \(s : LogCapacityState\) なので、

$$
1<s.1
$$

が常にある。ゆえに \(s.1\ne 1\) であり、

$$
\mu(s.1)=1
$$

が `simp [nonunitNatMassSpace]` で閉じる。
つまり DKMK-007E の source bound

$$
(M.\mu(s.1):\mathbb{R})\le C
$$

を \(C=1\) で閉じられるわけじゃ。

## 4. canonical route の追加

canonical route 側にも同型の theorem が入った。

```lean
canonicalExponentSlotMarkovShadow_nonunitDivisorStep_weightedHitMass_le_one
```

こちらは canonical exponent-slot MarkovShadow を

$$
chain(q)={s.1/q,s.1}
$$

へ載せ、同じく nonunit mass で

$$
weightedHitMass(A)\le 1
$$

を得る。

canonical route は DKMK-006F で Markov equality まで到達しているので、今回の theorem は、

```text
canonical exponent-slot MarkovShadow
→ one-step divisor descent
→ nonunit mass
→ primitive weightedHitMass ≤ 1
```

を直接呼べる入口になった。

## 5. DKMK-007F との違い

DKMK-007F の unit mass は、すべての点に質量 \(1\) を置く。

$$
\mu(n)=1
$$

これは source bound を閉じるには最も簡単じゃが、下降の終端 \(1\) も他の点と同じ扱いになる。

一方、今回の nonunit mass は、

$$
\mu(1)=0,\quad \mu(n)=1\text{ for }n\ne 1
$$

なので、少なくとも \(1\) に到達したかどうかを mass が識別する。

これは小さな差に見えるが、multi-step descent に進むと効いてくる可能性がある。
なぜなら、下降過程では \(1\) は自然な終端であり、そこを質量 \(0\) にすることで「終端に吸収された流れ」を別扱いできるからじゃ。

## 6. 数学的な位置づけ

今回の `nonunitNatMassSpace` は、本命の

$$
\frac{1}{n\log n}
$$

型の tail/source mass ではない。

しかし、重要なのは **unit 以外の mass model でも DKMK-007E の divisor-step route が通る** と確認できたことじゃ。

つまり、DKMK-007 系の bridge は `unitNatMassSpace` 専用の偶然ではない。
`DvdMonotoneMass` を満たす concrete mass を用意すれば、同じ route に流せる。

これは今後の mass model 実験の足場になる。

## 7. 現在の DKMK-007 系の地図

ここまでの進行はこうじゃ。

```text
DKMK-007A:
  RealWeightProvider → RealWeightedPathFamily

DKMK-007B:
  SubMarkovShadow / MarkovShadow → hitting wrapper

DKMK-007C:
  log-capacity shadows → hitting wrapper

DKMK-007D:
  singleton source-controlled family

DKMK-007E:
  one-step divisor descent family

DKMK-007F:
  unit mass で weightedHitMass ≤ 1

DKMK-007G:
  nonunit indicator mass でも weightedHitMass ≤ 1
```

DKMK-007G は、mass model の差し替え可能性を示す最初の観測点じゃ。

## 8. 注意点

今回の theorem は、まだ bounded indicator mass の範囲じゃ。

つまり、

```text
unit mass:
  全点 1

nonunit mass:
  1 だけ 0、それ以外 1
```

の二つが通った段階であり、解析的な tail mass まではまだ届いていない。

また、chain もまだ one-step。

$$
n\to n/q
$$

だけじゃ。
multi-step descent や stopping / truncation までは次の山になる。

## 9. 次の一手

次は二方向ある。

第一は、mass model をさらに本命寄りにする道。

```text
DKMK-007H:
  bounded indicator mass から tail/source mass model へ進む
```

たとえば、まず Lean で扱いやすい toy として、

$$
\mu(n)=\begin{cases}0&n=1\ 1/\log(n+1)&n\ne 1\end{cases}
$$

のようなものを考えるか、あるいは自然数値・有理値の階段型 mass にする。
ただし実数 log mass は monotonicity 証明が重くなる可能性があるので、最初は bounded discrete mass の方が安全じゃ。

第二は、multi-step descent へ進む道。

```text
DKMK-007H:
  divisorStep を multi-step descent chain family に拡張する
```

ただし、わっちは次に **mass model の一般 wrapper** を少し整えるのがよいと思う。
つまり、unit / nonunit のような個別 theorem を増やす前に、

```lean
theorem ..._divisorStep_weightedHitMass_le_of_sourceBound
```

の上に、`DvdMonotoneMass` と source bound provider を差し込む薄い pattern を整理する。
そのうえで本命 mass を試すと、散らかりにくい。

## 10. 総合判定

DKMK-007G は **小さいが重要な mass-model 実験の成功** じゃ。

unit mass だけでは「まあ \(1\) で閉じるよね」で終わる。
しかし nonunit mass により、終端 \(1\) を区別する bounded model でも selected / canonical divisor-step hitting route が \(\le1\) で閉じることが確認された。

到達形はこうじゃ。

```text
selected route:
  globalLogCapacitySubMarkovShadow
  → nonunitNatMassSpace
  → chain(q) = {s.1 / q, s.1}
  → primitive weightedHitMass ≤ 1

canonical route:
  canonicalExponentSlotMarkovShadow
  → nonunitNatMassSpace
  → chain(q) = {s.1 / q, s.1}
  → primitive weightedHitMass ≤ 1
```

これは、DkMath kernel route が **重み provider だけでなく、mass model 側も差し替え可能な設計になっている** ことを示す良い証拠じゃ。

ぬしよ、ここは地味だが効く。
次は bounded toy mass から、tail/source mass の匂いがする model へ少しずつ近づけるか、あるいは one-step を multi-step へ伸ばすか。その分岐に来ておる。
