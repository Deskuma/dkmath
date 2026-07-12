# Roadmap: No.297 cp

## DkMath Collatz 双窓追い込みロードマップ

うむ。最大限に推論して組み直した結果、ここから導入すべきものは、単なる `UpperWindow.lean` 一枚ではない。

新しい背骨は、

> **加速 Collatz を、下位の $2$-進評価と上位の二進指数が釣り合う「完全整数型の浮動小数点会計」として読む**

ことじゃ。

これまでの PetalBridge は、下位ビット側から

* $v_2(3n+1)$
* residue channel
* exact-height layer
* retention / continuation
* pressure margin
* local island / pulse
* finite-window packing

を積み上げてきた。現在の Collatz 層が accelerated odd map、$2$-adic height、有限観測窓、pressure / frontier を中心としていることは、資料の構造整理とも一致する。

これからは上位側から、

* bit width
* exponent
* dyadic mantissa
* fixed-width carry
* upper-zero boundary
* 上位 prefix

を下ろす。

そして中央に残る未観測ビットを `Gap` とし、上下の窓を狭めて証拠を捕獲する。

```text
上位窓
  exponent / mantissa / carry
              ↓

      未観測 middle Gap

              ↑
下位窓
  residue / v2 / pressure / all-ones depth
```

これは文字どおりの **挟み撃ち** じゃ。

---

## 1. 現在地の整理

まず三つの事実を固定する。

### 1.1. 下位側はかなり育っている

現在の snapshot には、少なくとも次がある。

```text
rawHeightLabel
orbitWindowHeight
ResidualAllOnesDepth
sumS
height layer counts
mod 4 / mod 8 residue equivalences
delayed peeling
exact-height-one reservoir
pressure margin
pressure pulse
interval accounting
finite-window packing
```

特に exact height $1$ は、

$$
h_i=1\Longleftrightarrow n_i\bmod8\in{3,7}
$$

へ分解されている。

さらに、

* $3\bmod8$ は次段の追加 peeling を生む **遅延返済側**
* $7\bmod8$ はまだ残る **継続残余側**

として、既に `DriftBudget` と pressure frontier に現れておる。

資料でも、$3\bmod8$ 側を `sumS` の下界へ回収し、$7\bmod8$ 側だけを continuing remainder として残す構造が明記されている。

### 1.2. 旧 canonical packing route は閉じた

cp-297 により、`AdjacentDiagnosis` は sorted packing の carrier ではなく、sorted-before failure の解決 carrier であることが確定した。sorted adjacency と診断は両立せず、旧 canonical state も成立しない。

したがって今後の下位側 local Big は、

```text
local-island witness
  -> center positive
  -> next coordinate nonpositive
  -> direct two-spacing
  -> direct finite-window density
```

で作り直す。

これは cp-296 のレビューで既に示された正しい方向でもある。

### 1.3. 上位側は資料にはあるが、まだ Lean 本体にない

資料庫には、

```lean
upperCarry3n1
lowerWindow3n1
IsFullAllOnesAtWidth
```

と、その carry 上界、Mersenne 型、同一幅回帰補題の設計がある。

しかし今回の snapshot 実査では、

```text
UpperWindow.lean
FloatWindow.lean
DyadicFloat.lean
```

に相当する本体モジュールは、まだ存在しておらぬ。

よってここが、新しい独立幹線の入口じゃ。

---

## 2. 新しい中心恒等式――Float 幅会計

ここが今回の最大の発見じゃ。

正の奇数 $n$ に対して、二進桁数を

$$
w(n):=\operatorname{bitWidth}(n)=\lfloor\log_2 n\rfloor+1
$$

と置く。

したがって、

$$
2^{w(n)-1}\le n<2^{w(n)}
$$

である。

次に、現在の bit width を基準とした upper carry を、

$$
c(n):=\left\lfloor\frac{3n+1}{2^{w(n)}}\right\rfloor
$$

と置く。

$n$ は自分自身の bit width 内の正数なので、

$$
c(n)\in{1,2}
$$

となる。

`0` は小さすぎ、`3` は大きすぎる。

そして、

* $c(n)=1$ なら $3n+1$ の bit width は $w(n)+1$
* $c(n)=2$ なら $3n+1$ の bit width は $w(n)+2$

じゃ。

加速 Collatz の height を、

$$
h(n):=v_2(3n+1)
$$

とし、

$$
T(n):=\frac{3n+1}{2^{h(n)}}
$$

とする。

$2^{h(n)}$ で割る操作は二進列の右シフトなので、bit width も正確に $h(n)$ だけ落ちる。

よって、次の **完全整数恒等式** が得られる。

$$
w(n)+c(n)=h(n)+w(T(n))
$$

これは推定でも漸近でもない。

> upper carry が供給した bit 数と、lower height が回収した bit 数との差が、次の bit width になる。

という、一歩ごとの厳密な保存会計じゃ。

DkMath 語彙なら、

```text
Current Width + Upper Carry
  =
Lower Peeling + Next Width
```

となる。

宇宙式風には、

```text
Big:
  current width + carry

Body:
  next width

Gap / payment:
  v2 height
```

という読みができる。

---

## 3. 既存の実数 drift との関係

既存には、

$$
\log_2 n_{i+1}-\log_2 n_i=\log_2 3-h_i+\log_2\left(1+\frac1{3n_i}\right)
$$

という実数 drift がある。累積形も既に資料で整理されている。

これは値の大きさを精密に測る解析側の式じゃ。

対して新しい Float 幅会計は、

$$
w_{i+1}-w_i=c_i-h_i
$$

という整数格子側の式になる。

二つの役割は異なる。

```text
実数 drift:
  bit 境界の内部で、値がどこまで動いたかを見る

Float 幅会計:
  bit 境界を何枚越えたかを正確に数える
```

まず整数版を完成させるべきじゃ。

実数 drift は、その後で mantissa の意味を与える semantic bridge として接続する。

---

## 4. 累積 Float 会計

軌道を、

$$
n_i:=T^i(n_0)
$$

と置く。

また、

$$
C_k:=\sum_{i=0}^{k-1}c(n_i)
$$

$$
H_k:=\sum_{i=0}^{k-1}h(n_i)=\operatorname{sumS}(n_0,k)
$$

と置く。

一歩恒等式を足し合わせれば、中間の bit width が telescope して、

$$
w(n_0)+C_k=H_k+w(n_k)
$$

となる。

したがって、

$$
w(n_k)-w(n_0)=C_k-H_k
$$

じゃ。

さらに $c_i\in{1,2}$ なので、carry $2$ の回数を $N_C(k)$ と置けば、

$$
C_k=k+N_C(k)
$$

となる。

一方、height は常に $1$ 以上なので、height layer count を、

$$
N_j(k):=\#{\,i<k\mid j\le h_i\,}
$$

と置けば、

$$
H_k=k+N_2(k)+N_3(k)+N_4(k)+\cdots
$$

である。右辺は有限窓では有限和じゃ。

ゆえに、最終的に、

$$
w(n_k)-w(n_0)=N_C(k)-N_2(k)-N_3(k)-N_4(k)-\cdots
$$

となる。

これは極めて重要じゃ。

```text
上位側の追加借金:
  carry = 2 の回数

下位側の追加返済:
  height >= 2 の全層
```

つまり、bit width が成長を維持するためには、

$$
N_C(k)\ge N_2(k)+N_3(k)+N_4(k)+\cdots
$$

を維持しなければならない。

ここから問題は、値そのものではなく、

> high-mantissa carry $2$ の発生量が、追加 peeling layer を上回り続けられるか

という有限カウント問題へ変わる。

---

## 5. 一歩の完全分類

一歩の bit-width 差は、

$$
\Delta w(n):=w(T(n))-w(n)=c(n)-h(n)
$$

じゃ。

$c\in{1,2}$、$h\ge1$ なので、増加する条件は正確に、

$$
0<\Delta w(n)\Longleftrightarrow c(n)=2\land h(n)=1
$$

となる。

これは単に「$h=1$ のとき増えるかもしれない」より一段強い。

> **実際に bit width が増えるのは、upper carry が $2$ かつ lower height が $1$ のときだけ。**

ここで下位 residue 分類を重ねると、

$$
h(n)=1\Longleftrightarrow n\bmod8\in{3,7}
$$

なので、

$$
0<\Delta w(n)\Longrightarrow c(n)=2\land\bigl(n\bmod8=3\lor n\bmod8=7\bigr)
$$

となる。

---

## 6. 四色 Float drift 表

一歩を $n\bmod8$ で分けると、次の図になる。

|   residue |  height |       width の動き | 役割                       |
| --------: | ------: | -----------------: | ---------------------------|
| $1\bmod8$ |   $h=2$ |     $\Delta w\le0$ | 中立または縮小             |
| $3\bmod8$ |   $h=1$ | $\Delta w\in{0,1}$ | 上昇候補だが次段で遅延返済 |
| $5\bmod8$ | $h\ge3$ |    $\Delta w\le-1$ | 即時縮小                   |
| $7\bmod8$ |   $h=1$ | $\Delta w\in{0,1}$ | 継続上昇候補               |

ここに upper carry を重ねると、

```text
3 mod 8 + carry 1:
  width unchanged

3 mod 8 + carry 2:
  width +1
  ただし次段に extra peeling

7 mod 8 + carry 1:
  width unchanged

7 mod 8 + carry 2:
  width +1
  継続残余の本命

1 mod 8:
  growth 不可

5 mod 8:
  strict width decrease
```

したがって追い込みの順序はこうなる。

```text
全 odd state
  ↓ upper growth の条件を課す
carry 2
  ↓ lower height の条件を課す
height 1
  ↓ residue 分解
3 mod 8 または 7 mod 8
  ↓ delayed payment で 3 mod 8 を回収
carry 2 ∧ 7 mod 8
```

最後に残る魚群は、

$$
c(n)=2\land n\bmod8=7
$$

だけじゃ。

これを **Seven-Carry Reservoir** と呼んでよい。

---

## 7. Float とは何か

ここで Lean の組み込み `Float` を使用してはいけない。

丸め誤差を含む IEEE 浮動小数点ではなく、完全に整数的な、

> **Exact Dyadic Float Observation**

として定義する。

候補は次じゃ。

```lean
def bitWidth (n : ℕ) : ℕ

def stateUpperCarry (n : OddNat) : ℕ

def upperPrefix (q w n : ℕ) : ℕ

def lowerSuffix (r n : ℕ) : ℕ

structure DyadicFloatObservation where
  width       : ℕ
  upperPrefix : ℕ
  lowerSuffix : ℕ
  upperCarry  : ℕ
  height      : ℕ
```

意味は、

```text
width:
  exponent

upperPrefix:
  mantissa の上位 q bits

lowerSuffix:
  下位 r bits / residue channel

upperCarry:
  3n+1 が上位へ作った借金量

height:
  下位から剥がされた返済量
```

じゃ。

必要なら後から、

$$
\mu(n):=\frac{n}{2^{w(n)-1}}\in[1,2)
$$

という実数 mantissa と接続する。

carry $2$ は概ね mantissa の上側、すなわち $\mu\approx4/3$ 以上に対応するが、最初は整数不等式のまま扱う。

---

## 8. 上下窓による証拠捕獲

bit width が $w$ の数に対して、

* 上位 $q$ bit
* 下位 $r$ bit

を観測する。

未観測の middle Gap の幅を、

$$
g:=\max(w-q-r,0)
$$

と置く。

上位 prefix と下位 suffix を固定したとき、未観測候補数は高々、

$$
2^g
$$

じゃ。

そして、

$$
w\le q+r
$$

なら upper window と lower window が接触または重複する。

このとき、両窓の情報が整合する数は高々一つになる。

つまり、

$$
g=0\Longrightarrow\text{state is uniquely captured}
$$

である。

これはまさに追い込み漁の網じゃ。

```text
上位 q bits
  ↓

middle Gap:
  2^g 個の候補

  ↑
下位 r bits
```

軌道の bit width が落ちるか、観測窓 $q,r$ を拡張すれば、$g$ は縮む。

最後には完全に同定される。

DkMath 語彙では、

```text
Big:
  full bit word

Body:
  upper prefix + lower suffix

Gap:
  hidden middle bits
```

となる。

---

## 9. 全体ロードマップ

### Phase A — 下位 local Big の再建

目安は cp-298 から cp-300。

旧 canonical carrier を使わず、local-island witness そのものを数える。

#### cp-298

```lean
sourcePressureLocalIslandWitness_two_le_val_gap_of_val_lt
```

目標：

$$
W.val<W'.val\Longrightarrow W.val+2\le W'.val
$$

center $+1$ が非正、次の center が正なので、隣接は不可能。

#### cp-299

```lean
sourcePressurePositiveWitnessCentersInWindow
sourcePressurePositiveWitnessCenters_twoSeparated
sourcePressurePositiveWitnesses_card_le_half_window_add_one
```

目標：

$$
\#\text{positiveWitnesses}\le\frac{hi-lo}{2}+1
$$

#### cp-300

```lean
sourcePressurePositiveWitness_next_nonpos
sourcePressurePositiveWitnesses_card_le_nonposPositions_add_one
sourcePressurePositiveWitnesses_localBig_direct
```

目標：

$$
\#\text{positiveWitnesses}\le\#\text{nonposPositions}+1
$$

この三 checkpoint で、下位の網を修復する。

---

### Phase B — Upper Window Core

目安は cp-301 から cp-304。

推奨構成：

```text
DkMath/Collatz/PetalBridge/FloatWindow/Core.lean
DkMath/Collatz/PetalBridge/FloatWindow/Mersenne.lean
DkMath/Collatz/PetalBridge/FloatWindow.lean
```

最初に資料案の API を実装する。

```lean
upperCarry3n1
lowerWindow3n1

threeNPlusOne_eq_upperCarry_mul_add_lower
lowerWindow3n1_lt_pow
upperCarry3n1_lt_three_of_lt_pow
upperCarry3n1_le_two_of_lt_pow
```

さらに bit width 固有の sharpened theorem を追加する。

```lean
stateUpperCarry_one_or_two
stateUpperCarry_ne_zero
stateUpperCarry_ne_three
```

Mersenne 境界標本も固定する。

```lean
upperCarry3n1_mersenne
lowerWindow3n1_mersenne
residualAllOnesDepth_after_mersenne_step
```

ただし Mersenne は $7\bmod8$ reservoir 全体の証明ではなく、 **最も極端な境界標本** と位置づける。

---

### Phase C — Float Width Balance

目安は cp-305 から cp-308。

推奨ファイル：

```text
DkMath/Collatz/PetalBridge/FloatWindow/WidthBalance.lean
```

中心定理：

```lean
bitWidth_threeNPlusOne_eq_bitWidth_add_upperCarry

bitWidth_T_add_height_eq_bitWidth_add_upperCarry
```

数学形は、

$$
w(n)+c(n)=h(n)+w(T(n))
$$

じゃ。

次に軌道列へ持ち上げる。

```lean
orbitWindowUpperCarry
orbitWindowUpperCarrySeq
sumUpperCarry

iterateT_bitWidth_add_sumS_eq_bitWidth_add_sumUpperCarry
```

数学形：

$$
w(n_k)+H_k=w(n_0)+C_k
$$

この段で、既存 `driftReal` と並ぶ、新しい exact integer drift が完成する。

---

### Phase D — Carry Count と Height Layer の対決

目安は cp-309 から cp-312。

carry $2$ の回数を定義する。

```lean
orbitWindowUpperCarryCountEqTwo
```

そして、

```lean
sumUpperCarry_eq_window_add_countCarryTwo
```

を証明する。

$$
C_k=k+N_C(k)
$$

既存 height API と合わせて、

```lean
bitWidth_growth_le_carryTwo_sub_heightGeTwo
```

あるいは Nat 減算を避けて、

```lean
bitWidth_nonincrease_of_carryTwoCount_le_extraHeightLayers
```

を出す。

中心判定は、

$$
N_C(k)\le N_2(k)+N_3(k)+\cdots\Longrightarrow w(n_k)\le w(n_0)
$$

となる。

ここで初めて、上位 carry と下位 height が同じ theorem statement に入る。

---

### Phase E — Dyadic Net

目安は cp-313 から cp-317。

中立ファイルを新設する。

```text
DkMath/Basic/BinaryWindow.lean
```

置くもの：

```lean
bitWidth
upperPrefix
lowerSuffix
middleGapWidth
BinaryWindowCompatible
```

主定理：

```lean
binaryWindow_candidate_card_le_pow_middleGap

binaryWindow_unique_of_width_le_upper_add_lower
```

数学形：

$$
\#\text{compatible states}\le2^g
$$

$$
w\le q+r\Longrightarrow\text{compatible state is unique}
$$

これは Collatz 専用でなく、DkMath 全体で使える二進有限窓 API になる。

---

### Phase F — 四色 Pattern Ledger

目安は cp-318 から cp-322。

推奨ファイル：

```text
DkMath/Collatz/PetalBridge/FloatWindow/PatternLedger.lean
```

一歩の状態を、

```lean
structure FloatStepLedger where
  widthBefore : ℕ
  upperCarry  : ℕ
  height      : ℕ
  widthAfter  : ℕ
  residue8    : Fin 8
```

のように包む。

中心定理：

```lean
upperGrowth_iff_carryTwo_and_heightOne

upperGrowth_implies_mod8_three_or_seven

upperGrowth_mod8_three_has_delayedPayment

upperGrowth_unpaid_implies_mod8_seven
```

ここで、

```text
all upper growth
  =
delayed-payment growth
  +
Seven-Carry remainder
```

という分解を作る。

---

### Phase G — Pressure Ledger Bridge

目安は cp-323 から cp-330。

推奨ファイル：

```text
DkMath/Collatz/PetalBridge/PressureLedgerBridge.lean
```

ここで初めて Float と pressure を接続する。

狙う分岐は、

```text
Seven-Carry reservoir
  -> delayed payment appears
   | pressure-positive local island appears
   | all-ones depth decreases
   | explicit surviving obstruction remains
```

じゃ。

定理を一気に強くしない。

まず、

```lean
upperGrowthCount_le_exactHeightOneCount

carryTwoMod8ThreeCount_le_delayedPaymentBudget

unpaidUpperGrowthCount_le_carryTwoMod8SevenCount
```

を作る。

次に direct local Big を使い、

```lean
Seven-Carry continuation
  -> positive pressure witness
```

が本当に証明できるかを調べる。

証明できなければ、その不足を、

```lean
SevenCarryPressureGap
```

として明示的に残す。

失敗を消さず、次の state にするのじゃ。

---

### Phase H — 有限 Drift Automaton

目安は cp-331 以降。

ここで初めて有限グラフを作る。

```lean
structure DriftNode where
  upperPrefixClass : Fin (2 ^ q)
  lowerResidue     : Fin (2 ^ r)
  upperCarryClass  : Fin 3
  heightBucket     : Fin hCap
  pressureSign     : PressureSign
  allOnesBucket    : Fin depthCap
```

ただし実際には `Fin 3` の値 $0$ は own-width state では使わない。

```lean
structure DriftEdge where
  source : DriftNode
  target : DriftNode
  sound_transition : ...
  widthWeight : ℤ
```

証明目標：

```lean
driftNode_finite

orbitSegment_maps_to_driftPath

infinite_nonDescending_orbit_yields_repeatedNode

repeatedNode_yields_observableCycle
```

そして最後に、

```lean
no_nonnegativeDriftCycle
```

を攻める。

重要なのは、抽象化した edge が実軌道を取りこぼさないことじゃ。

精密な同値である必要はない。

実軌道を全て含む **sound over-approximation** でよい。

もし非負 cycle が見つかれば、それは失敗ではない。

```text
実際の悪路
  または
抽象化が粗すぎて生まれた偽悪路
```

のどちらかなので、観測 bit を一つ追加して分解すればよい。

---

## 10. 証拠捕獲の四分岐

今後の各 block theorem は、次の四分岐へ揃えるのがよい。

```text
1. Descent
   bit width または値が下がる

2. Net Tightening
   middle Gap / compatible candidate 数が減る

3. Payment
   height / delayed peeling / pressure budget が消費される

4. Named Obstruction
   Seven-Carry / pressure island / repeated DriftNode が残る
```

Lean 定理の概念形は、

```lean
SqueezeBlockResult :=
  WidthDescent
  ∨ WindowTightening
  ∨ PaymentCertificate
  ∨ ExplicitObstruction
```

じゃ。

最後の obstruction を隠さない。

追い込み漁では、逃げた魚の位置が分かること自体が成果じゃからの。

---

## 11. 研究上の本当の Gap

現時点で最も大きい未証明部分は、次の接続じゃ。

$$
\text{carry }2\land n\bmod8=7
$$

が長く続くとき、それが必ず、

* extra height
* pressure pulse
* all-ones depth の減少
* upper/lower window の収縮
* finite state cycle

のどれかを生むこと。

ここはまだ証明されていない。

だが、敵は既に、

```text
arbitrary Collatz orbit
```

ではなく、

```text
high mantissa
+
exact height one
+
7 mod 8
+
pressure continuation
```

へ絞られた。

この絞り込み自体が強い。

---

## 12. 最終目標への階段

直ちに、

$$
\forall n,\ \exists k,\ T^k(n)=1
$$

を狙わない。

まず次を狙う。

### 第一山頂

$$
1<n\Longrightarrow\exists k,\ T^k(n)<n
$$

すなわち、任意の奇数核は有限時間で自分より小さい奇数核へ落ちる。

Lean 名の候補：

```lean
exists_iterateT_lt_self
```

### 第二山頂

第一山頂から well-founded induction で、

```lean
iterateT_reaches_one
```

を得る。

### 第三山頂

accelerated odd map から通常 Collatz へ戻す。

```lean
collatz_conjecture_of_accelerated_reaches_one
```

この三段階がよい。

---

# 13. 直近の実装順

今すぐ進める順序は、これで固定するのが最善じゃ。

```text
cp-298
  direct two-spacing

cp-299
  direct half-window density

cp-300
  direct nonpositive injection

cp-301
  UpperWindow definitions

cp-302
  own-width carry = 1 or 2

cp-303
  Mersenne / all-ones boundary examples

cp-304
  bitWidth raw-step theorem

cp-305
  exact Float width balance

cp-306
  telescoping orbit-width balance

cp-307
  carry-two count identity

cp-308
  width growth iff carry 2 and height 1

cp-309
  mod 8 four-color ledger

cp-310
  delayed 3 / continuing 7 split

cp-311+
  Dyadic Net and PressureLedgerBridge
```

## 全体図

```text
LOWER FRONT
v2 / residue
  -> height layers
  -> delayed peeling
  -> pressure
  -> direct local Big
          \
           \
            Float Width Balance
            w + carry = height + w'
           /
          /
UPPER FRONT
finite-start zero boundary
  -> bit width
  -> upper carry 1/2
  -> upper prefix / mantissa
  -> carry-two growth candidates

              |
              v

carry 2 ∧ height 1
  -> mod 8 = 3 or 7
  -> 3 : delayed repayment
  -> 7 : continuing reservoir

              |
              v

Dyadic upper/lower net
  -> middle Gap shrinks
  -> exact state capture
  -> or finite DriftNode cycle

              |
              v

no nonnegative drift cycle
  -> eventual smaller odd state
```

## 総括

この新しい攻め筋の本質は、こうじゃ。

> 下位側は、何 bit 支払ったかを数える。
> 上位側は、何 bit 借りたかを数える。
> Float 幅会計は、その取引が一 bit も失われず一致することを示す。
> upper prefix と lower suffix は、中央の未知 bit を両側から削る。
> 逃げ続ける軌道は、最終的に `carry 2 ∧ 7 mod 8` の有限な悪構造へ押し込められる。

わっちの見立てでは、これまで別々に見えていた、

* bit-width budget
* real drift
* exact-height-one reservoir
* pressure pulse
* all-ones depth
* finite bad-cycle

が、初めて一本の背骨へ並んだ。

この賢狼、ここはかなり手応えを感じておるぞい。
