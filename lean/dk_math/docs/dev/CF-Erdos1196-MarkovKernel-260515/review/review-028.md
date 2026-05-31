# review

うむ。DKMK-007M は **finite step tail mass の本命入口** じゃ。
DKMK-007L で `boundedMonotoneNatMassSpace` という受け皿を作った。今回 DKMK-007M では、その受け皿に載せる **具体的な任意有限段 tail height constructor** を追加した。これで two-step 専用から、非負 increment の有限和として任意段の tail mass を扱えるようになった。

## 1. 今回の核心

追加された中心はこれじゃ。

```lean
finiteStepTailHeight steps threshold increment
```

定義の意味は、

$$
finiteStepTailHeight(n)=\sum_{i\in steps} \begin{cases} increment(i) & \text{if } threshold(i)\le n \ 0 & \text{otherwise} \end{cases}
$$

じゃ。

各 step \(i\) は、自分の threshold を越えたところから height に寄与する。
重要なのは、threshold を事前に整列しなくてよいことじゃ。各 step が独立に tail 条件で発火し、それらを有限和として足す。

つまり、finite step function を「段の並び」ではなく、 **非負 increment の累積和** として表現している。これは Lean 的にも数学的にもかなり扱いやすい。

## 2. 証明された三つの基本性質

今回、`finiteStepTailHeight` について三つの基本補題が入った。

```lean
finiteStepTailHeight_nonneg
finiteStepTailHeight_le_total
finiteStepTailHeight_mono
```

仮定はこれだけじゃ。

```lean
hinc : ∀ i ∈ steps, 0 ≤ increment i
```

つまり、各 increment が非負であればよい。

第一に、各項が非負なので、

$$
0\le finiteStepTailHeight(n)
$$

が出る。

第二に、各項は \(0\) または \(increment(i)\) なので、全体は total increment 以下になる。

$$
finiteStepTailHeight(n)\le \sum_{i\in steps}increment(i)
$$

第三に、\(a\le b\) なら、\(threshold(i)\le a\) から \(threshold(i)\le b\) が従う。したがって各 step の寄与は減らず、全体として単調になる。

$$
a\le b\Rightarrow finiteStepTailHeight(a)\le finiteStepTailHeight(b)
$$

ここまでが DKMK-007L の `boundedMonotoneNatMassSpace` に流すためのちょうど必要十分な入口じゃ。

## 3. `finiteStepTailNatMassSpace` の意味

次に追加されたのがこれじゃ。

```lean
finiteStepTailNatMassSpace steps threshold increment hinc
```

これは内部的には、

```lean
boundedMonotoneNatMassSpace
  (finiteStepTailHeight steps threshold increment)
  (Finset.sum steps increment)
  ...
```

として定義されている。

つまり、DKMK-007L の抽象 interface に、今回の concrete finite step height を載せたものじゃ。
上界 \(C\) は total increment、

$$
C=\sum_{i\in steps}increment(i)
$$

になる。

これにより、

```lean
finiteStepTailNatMassSpace_dvdMonotone
```

も、個別に場合分けせずに `boundedMonotoneNatMassSpace_dvdMonotone` へ渡して閉じている。

ここがとても良い。DKMK-007K では two-step を直接場合分けしていたが、DKMK-007M では interface が効いて、有限段全体が一発で乗る。

## 4. LogCapacitySourceMassBound への接続

`LogCapacityHittingBridge.lean` 側では、

```lean
finiteStepTailNatMassSpace_logCapacitySourceMassBound
```

が追加された。

これは、

$$
LogCapacitySourceMassBound(finiteStepTailNatMassSpace,(\sum_{i\in steps}increment(i):\mathbb{R}))
$$

を供給する。

つまり、任意の log-capacity state \(s\) で、

$$
\mu(s.1)\le \sum_{i\in steps}increment(i)
$$

が成り立つ。
これで DKMK-007H の source-bound provider に、そのまま有限段 tail mass を流せるようになった。

## 5. selected route への接続

selected route 側には次が追加された。

```lean
PrimePowerWitnessProvider.globalLogCapacitySubMarkovShadow_finiteStepTailDivisorStep_weightedHitMass_le
```

これは、selected log-capacity sub-Markov shadow を one-step divisor descent family に載せ、finite step tail mass を source mass として使ったとき、

$$
weightedHitMass(A)\le \left(\sum_{i\in steps}increment(i):\mathbb{R}\right)
$$

を返す。

これで selected route は、単なる (≤1) や (≤c) ではなく、 **有限個の tail increment の総和** を上界として返せるようになった。

## 6. canonical route への接続

canonical route 側にも同型の theorem が追加された。

```lean
canonicalExponentSlotMarkovShadow_finiteStepTailDivisorStep_weightedHitMass_le
```

こちらも、

$$
weightedHitMass(A)\le \left(\sum_{i\in steps}increment(i):\mathbb{R}\right)
$$

を得る。

canonical route は DKMK-006 系で Markov equality に到達しているので、ここでは mass 側の total increment がそのまま hitting bound の上界になる。
これは綺麗じゃ。

## 7. DKMK-007K からの前進

DKMK-007K は two-step 専用だった。

```text
below N:
  0

N 以上 M 未満:
  cLow

M 以上:
  cHigh
```

DKMK-007M は、それを任意有限段へ拡張した。

```text
step i:
  threshold i を越えたら increment i を加算
```

この表現だと、複数の threshold が同じでもよいし、順番も不要じゃ。
高さは「発火した increment の累積和」として決まる。

これは将来の近似にとても向いている。
たとえば、ある target weight を下から、または上から、有限個の threshold step で近似する設計に進める。

## 8. 数学的な位置づけ

ここまでの mass model は、こういう階段を登ってきた。

```text
unit / nonunit:
  固定 mass

tail indicator:
  threshold support

scaled tail indicator:
  threshold support + height

two-step tail:
  二段階 height

boundedMonotoneNatMassSpace:
  bounded monotone height interface

finiteStepTailHeight:
  非負 tail increment の有限和による concrete constructor
```

DKMK-007M は、DKMK-007L の抽象 interface に concrete な finite-step constructor を与えた回じゃ。
つまり「任意の bounded monotone height を受け取れる」から、「実際に finite step height を作って渡せる」へ進んだ。

これは大きいぞい。

## 9. 実装上の評価

実装判断も良い。

`∑` 記法が module の構文環境で parse されなかったため `Finset.sum steps ...` に寄せた、という記録がある。これは Lean 実装ではよくある堅実な選択じゃ。

また、非負性・上界・単調性の証明で、定義展開後に `change` で `Finset.sum` の形へ揃えてから `Finset.sum_nonneg` / `Finset.sum_le_sum` を使っている。
これは後で見ても分かりやすい証明の形じゃ。

## 10. 注意点

今回の `finiteStepTailHeight` は、height が自然数ラベルに対して非減少になる構造じゃ。

これは `DvdMonotoneMass` には合っている。
一方、解析的に現れる \(1/(n\log n)\) は \(n\) が増えるほど減るので、向きは逆じゃ。

したがって今の finite step mass は、直接 \(1/(n\log n)\) を近似するというより、 **source-controlled hitting に適した単調 mass** の有限段 model と見るべきじゃ。

もし将来 decreasing weight を直接扱うなら、`DvdMonotoneMass` とは別向きの control interface が必要になるかもしれぬ。
ただし、今の目的は one-step divisor descent の source mass bound を作ることなので、この向きは自然じゃ。

## 11. 次の一手

次は二つある。

第一は、DKMK-007K の two-step tail mass を、DKMK-007M の finite step constructor の特殊例として再利用する wrapper を作ることじゃ。

```text
twoStepTailNatMassSpace
  ≈ finiteStepTailNatMassSpace with two increments
```

ただし、完全な definitional equality まで狙うと面倒かもしれぬ。最初は「同じ bound が finite-step route から出る」程度でよい。

第二は、そろそろ multi-step descent chain へ進むことじゃ。

ここまでで one-step divisorStep と mass 側の interface はかなり整った。
次に必要なのは、

$$
n\to n/q_1\to n/(q_1q_2)\to\cdots
$$

のような chain をどう `SourceControlledChainFamily` として作るかじゃ。

わっちは、ここで一度 DKMK-007A から 007M までを総括し、その後 DKMK-008 として multi-step descent へ切るのも良いと思う。

## 12. 総合判定

DKMK-007M は **finite step tail mass constructor の成功フェーズ** じゃ。

到達形はこうじゃ。

```text
finite nonnegative tail increments
  → finiteStepTailHeight
  → boundedMonotoneNatMassSpace
  → DvdMonotoneMass
  → LogCapacitySourceMassBound by total increment
  → divisor-step weightedHitMass ≤ total increment
```

selected / canonical の両 route で通っている。
これにより、threshold の整列補題なしに、任意有限段の累積 tail mass を扱う入口ができた。

ぬしよ、これは実に良い。
質量の階段を「手で二段作る」段階から、「任意有限個の段を足し合わせる」段階へ入った。次はいよいよ、その階段を下降路の複数歩にどう沿わせるかじゃな。
