# Instruction 005 — fresh incidence cost and fixed-seat capacity

既存の lower persistent/fresh split から費用を正確に分解し、**N=20,T=20 の既存 simultaneous full cover の下で、support excess が少なくとも38必要**と Lean で証明した。既存 full-cover candidate/incidence balance に正の `+38` を加える定理も固定した。

元の「fresh >=76」だけでは費用は強制できない。今回の前進は、固定座席の候補奇偶を保って持続周期を **q から2qへ** 絞り、持続容量を **169から97** に縮めたことと、最初の無費用枠を正確に分離したことによる。

## 実装と再利用

- [ParitySafePersistence.lean](../../../DkMath/NumberTheory/Legendre/ParitySafePersistence.lean) に5宣言を追加。座席ごとの cardinality split、既存 `(4*r+1).primeFactors` による持続 support bound、固定座席の有限頻度 bound。既存定義・証明は変更していない。
- [ParitySafePersistenceParity.lean](../../../DkMath/NumberTheory/Legendre/ParitySafePersistenceParity.lean) に10宣言。実際の candidate 奇偶、2q 頻度、座席への転置、改良容量と旧容量との比較。
- [ParitySafeFreshCost.lean](../../../DkMath/NumberTheory/Legendre/ParitySafeFreshCost.lean) に31宣言。singleton、mandatory first slot、incremental excess、実際の fresh pairs、既存 excess/pair/collision-support ledger への包含、有限 full-cover charging。
- [LegendreFreshCost.lean](../../../DkMathTest/NumberTheory/LegendreFreshCost.lean) に15の名前付き校正・正規化定理。

新規二 modules は Legendre facade から公開した。[source inventory](source-inventory-005.md) に必須台帳の定義・型と停止境界を記録した。新しい full-cover ledger を仮定せず、同じ production candidates と supports を使っている。

## 座席ごとの正確な費用

座席 r の後続 active support cardinality を K、持続 support cardinality を P、新規 support cardinality を F とすると、すべて実際の既存 support に対して

```text
K = P+F.
```

現在の excess は K-1、pair-overlap mass は choose(K,2)、canonical star を取り除いた residual pair mass は choose(K-1,2)。自然数 subtraction を用い、空 support も含む。

**ゼロ費用の fresh incidence** は、full active support が singleton で、その唯一の素数が fresh であるもの。F=K=1、P=0 となり、production support excess も fresh charge も0になる。`mem_lowerSingletonFreshSeats_iff_zero_excess` は、このクラスが既存 excess=0 と fresh occupancy の組合せに正確に一致する iff。

多方向 support 全体を無費用とはしない。P=0 のときだけ最初の一枠を無費用として、incremental charge を

```text
C_r = F - (if P=0 then 1 else 0)
```

と定めると、正確に

```text
K-1 = (P-1) + C_r.
```

成立する。P>0 ならすべての F を課金し、P=0 なら最初の一つを除く F-1 を課金する。これは cardinality による費用分解で、特定の素数を恣意的に canonical first prime と同一視していない。

実際の lower candidate sector R_n に総和を取ると

```text
freshCount = singletonFreshSeats.card + multiFreshCount,
multiFreshCount <= 2*paritySafeSupportExcess(n+1),
freshCount = freshWithoutPersistentSeats.card + freshExcessChargeCount,
freshExcessChargeCount <= paritySafeSupportExcess(n+1).
```

singleton は完全なゼロ費用クラス。一方 `freshWithoutPersistentSeats` は P=0,F>0 の各座席につき一つの mandatory first slot を数え、多方向 support の最初の一枠も含む。この二つを混同していない。

後者の first-slot count は係数一で excess に課金でき、前者の singleton count は係数二で課金できる。どちらも全 candidate 数という自明な容量より精密な、実際の support class の容量である。

## fresh pair と既存残余 class

既存 `Internal.upperPairs` を使い、active の unordered pairs から persistent-only pairs を除いた actual finite set を定義した。membership iff で少なくとも一方の endpoint が fresh であることを確認し、

```text
choose(K,2) = choose(P,2) + freshPair.card,
freshPair.card = P*F + choose(F,2)
```

を証明した。この総和は既存 pair overlap 以下で、collision 外へ制限した総和は既存 outside-collision pair overlap 以下。collision 上の fresh excess charge は既存 collision local support cost 以下である。

ただし、fresh pair をすべて residual pair に課金する案は偽。n=12,r=6 では successor shell 13 の active support は `{5,7}`、persistent は `{5}`、fresh は `{7}`。fresh pair は一つ、incremental excess charge は一つだが、local residual pair mass は **0**。否定定理 `fresh_pairs_not_bounded_by_local_residual` を保存した。この例は、最初の star edge と残余 pair を区別する必要を示す。

collision は K>=4、fifth-direction collision は K>=5 を要する。多方向 fresh だけから depth collision、fifth gate、low-cost branch membership を供給することはしていない。

## 固定座席による持続容量の改善

Instruction 004 の制約により、実際の persistent support は

```text
persistentSupport(n,r) subset (4*r+1).primeFactors.
```

したがって cardinality による有限 label budget があり、

```text
activeSupport.card - (4*r+1).primeFactors.card <= freshSupport.card.
```

も得た。fresh labels までこの prime-factor set に制限することはできない。n=8,r=4 には zero-cost singleton fresh q=5 があるが、5 は `(4*r+1)=17` の prime factor ではない。これも回帰定理で固定した。

さらに、実際の lower successor candidate について

```text
Odd((n+1)^2+r) -> n ≡ r (mod 2).
```

同じ固定座席で同じ奇素数 q が持続する二つの殻は mod q で合同、かつ mod2 でも合同である。CRT により **mod(2q) で合同**。この制約による finite frequency は ceil(T/(2q)) となる。coprimality が候補をさらに除く場合もあり、mod(2q) の全番号が候補になるとは主張していない。

固定 r の prime labels は有限でも、同じ label は再使用できる。例えば q=3,r=2 は n=10 と n=16 で再び候補 address となる。永久に持続予算が枯渇するとは言わず、有限区間の使用回数を抑える。

M=N+T とすると、seat-weighted 改良容量は

```text
C2(N,T) = sum_{1<=r<=M} sum_{q prime<=M, q!=2, q|4*r+1} ceil(T/(2q)).
```

旧 C1 の prime-weighted expression を seat-weighted に正確に転置し、全 N,T で C2<=C1 を証明した。使用する r は正確な lower canonical reindex sector の同じ offset であり、異なる候補族の座席を同一視していない。

## N=20,T=20 の kernel 校正と正の費用

| 量 | exact kernel value |
| --- | ---: |
| Lower candidate seats 合計 R | 245 |
| Instruction 004 の持続容量 C1 | 169 |
| Candidate parity を保つ持続容量 C2 | 97 |
| 完全ゼロ費用の singleton fresh seats 合計 S | 94 |
| P=0,F>0 の mandatory first slots 合計 B | 110 |

旧需要 `245-169=76` は S=94 より小さく、それだけでは正の費用を強制できない。これは free capacity を76未満にする無条件の案を否定する exact diagnostic である。

同じ既存 simultaneous full-cover 仮定の下で、新しい持続 bound は

```text
fresh >= 245-97 = 148.
```

を与える。singleton accounting では少なくとも54の multi-support fresh incidences と27以上の excess が必要。より精密な first-slot accounting を使うと

```text
supportExcess summed over successor shells 21..40
  >= 148-110 = 38.
```

`mainBlock_support_excess_lower_bound` はこの **38** を existing production `paritySafeSupportExcess` に直接置く。`mainBlock_fullCover_balance_with_positive_charge` は、既存 exact full-cover balance を用いて

```text
sum fullCandidate.card + 38 <= sum paritySafeIncidenceCount
```

まで証明する。正の追加項を省いた candidate/incidence necessary bound より厳しい有限条件であり、新しい架空の capacity ledger ではない。

これは successor shells 21..40 の full cover を条件とする。full cover 自体は供給せず、Legendre や全殻での contradiction を結論していない。

## どこまで frontier が動いたか

今回厳密に改善したのは、Instruction 004 の actual temporal persistence capacity と、full-cover balance が要求する既存 support-excess の最小費用。C1=169 から C2=97 への strict 改善と、正の既存費用38の回帰定理があるため、Instruction 005 の Outcome A の **support-excess case** を満たす。

十一 collision の readable cancellation inequality 自体を書き換えたわけではない。38を outside-collision mass、collision seats、low-cost residual capacity のいずれかへ移す injection は証明していない。既存 `paritySafeLowCostResidualCapacity` や exact-depth residual capacity の upper bound を38だけ減らすこともしていない。

したがって、full-cover contradiction に必要な residual/collision recipient の局在化は引き続き未解決。有限 minimum-cost の段階は前進し、全殻の prime existence / asymptotic estimate / global contradiction は未証明のままである。

## 指定された八問への回答

| 問 | 回答 |
| --- | --- |
| 1. 現在の zero-cost fresh incidence は何か | 実際の active singleton の唯一の fresh prime。P=0,F=K=1 で existing excess=0。 |
| 2. 座席・有限区間でいくつ無費用に吸収できるか | singleton 座席で一つ。P=0 の多方向座席でも最初の一枠は無費用。main block の exact singleton capacity は94、first-slot capacity は110。 |
| 3. P/F と support excess の local identity は | K=P+F、K-1=(P-1)+[F-(if P=0 then1 else0)]。 |
| 4. P/F と pair overlap の identity は | choose(K,2)=choose(P,2)+P*F+choose(F,2)。実際の fresh-pair set で証明。 |
| 5. q divides 4r+1 は strict seat-local budget になるか | Persistent labels はその prime factors のみに限られ、active support がこの budget を超えれば fresh が必要。さらに candidate parity により fixed-seat frequency は2qになる。Fresh labels を同じ set に制限はできない。 |
| 6. main block の76だけで positive costly mass を強制するか | いいえ。94の zero-cost singleton capacity がある。しかし新たな2q制約で需要が148へ上がり、110 first slots を超えて existing excess38を強制する。 |
| 7. どの既存 frontier term が strict に改善したか | Temporal persistence cap は169から97。既存 supportExcess の minimum は38、summed full-cover candidate/incidence balance に+38。Residual/collision upper capacity の削減は未証明。 |
| 8. Full-cover contradiction frontier は動いたか | 有限 mandatory-cost frontier は動いた。新しい正の費用を residual/collision recipient へ局在化し全殻の cover failure を導く段階には未到達。 |

[Validation](validation-005.md): changed/new focused modules、Legendre facade、DkMath、15回帰宣言の build は成功。新規46 production +15 regression の全公理出力は標準三公理の部分集合。

Outcome A — STRICT RESIDUAL/COLLISION FRONTIER GAIN
