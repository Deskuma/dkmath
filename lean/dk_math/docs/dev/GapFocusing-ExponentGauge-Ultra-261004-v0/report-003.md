# Instruction 003 — Prime reappearance / cyclotomic layer addresses

2026-10-04。Lean / Mathlib `v4.34.1`。
対象: [instruction-003](instruction-003.md)。ユーザーの「読み、実施してください」
という依頼に従い、文書の候補を検証して実装した。候補の住所法則や moire
という語は証明の仮定にしていない。開始時 HEAD は `0d34556bd`、branch は
`research/GapFocusing-ExponentGauge-Ultra-261004-v0`、working tree は clean。

**Outcome A — classified reappearance law。**
素数の斉次円分層住所を、剰余比の乗法位数と素数冪による次数拡大で分類し、
座標が剰余体で消える場合も形式化した。既存 primitive-prime predicate と
最初の正次数層の同値も証明した。これは住所・整除の完全分類である。
valuation の結果は明示した範囲に限られ、全斉次層の multiplicity 完全分類を
主張するものではない。

## 1. 素数の円分層住所を表す正確な対象

既存の一般斉次 evaluator

```lean
DkMath.CFBRC.cyclotomicShiftedEval n (a - b) b
```

を `H_n(a,b)=Phi_n(a,b)` と書く。これは整数円分多項式を実際の natural
degree で homogenize して `(a,b)` で評価したもので、norm の一致による
同一視ではない。値の新しい重複定義は導入していない。

`a,b : ℤ`, `q : ℕ` に対し、再利用できる二つの集合を追加した。

```text
primeLayerAddresses q a b = {n | 1<n and (q:Z) divides H_n(a,b)}
layerPrimeSupport a b n = {q | q.Prime and (q:Z) divides H_n(a,b)}.
```

前者は後者の support-incidence fiber であることを theorem にした。
住所定義自体は primality を仮定しない。分類 theorem は `[Fact q.Prime]`
を要求する。実装: [HomogeneousAddress](../../../DkMath/NumberTheory/GapFocusing/HomogeneousAddress.lean)。

## 2. 乗法位数による最初の出現

`primeRatio q a b=(a mod q)*(b mod q)^(-1)` とし、
`r=primeOrder q a b=orderOf (primeRatio q a b)` と定義した。
`q∤a,b` のとき、この scalar の order が対応する実際の unit-group order
に一致することを証明した。field fraction を新しく導入する必要はない。

素数 `q` と `q∤b` のみで、全自然数 exponent に対し

```text
(q:Z) | a^n-b^n  iff  r | n.
```

が成立する。`q|a` の場合は scalar が 0 で order が 0 となり、正次数の
整除が存在しないこともこの式に含まれる。自然数の減算版には `b≤a` が
必要であり、欠けたときの truncated subtraction 反例も回帰にした。
`q∤a,b` なら `0<r` と `r | q-1`、従って `r` と `q` が互いに素であることを
証明した。座標の gcd 条件はこの residue-order 解析の必要仮定ではない。
実装: [PrimeOrder](../../../DkMath/NumberTheory/GapFocusing/PrimeOrder.lean)。

全ての **正次数** 円分層について、出現しかつ正の低次数層に出現しない
述語 `FirstLayerAppearance q a b n` を定義した。`n>0`, `q∤b` なら

```text
FirstLayerAppearance q a b n  iff  r=n.
```

一方、住所集合は `n>1` に制限しているので、least address は次の二通り。

- `r>1`: 最小住所は `r`。
- `r=1`: 最小の非自明住所は `q`。これは次数 1 からの再出現である。

両方の `IsLeast` theorem を実装した。`(a,b,q)=(4,1,3)` では 3 が最小の
非自明住所だが、既に `3 | 4-1` なので次数 3 の primitive prime ではない。
この境界を回帰で固定した。

## 3. 同じ有理素数が別の層で再出現する条件

まず `q∤b` の下で、係数写像と既存 field evaluator を通じて

```text
q | H_n(a,b)
  iff Phi_n over ZMod(q) has root (a mod q)*(b mod q)^(-1)
```

を証明した。この transport は分母座標だけの非消失を必要とする。
root 分類の core は任意の characteristic-`q` domain について成立する。

```text
n>0  ->  (Phi_n R).IsRoot z iff exists k, n=orderOf(z)*q^k.
```

既存 Mathlib の characteristic-prime cyclotomic root theorem を再利用し、
`n` の `q`-primary part を分けて導いた。scalar `z` の非零性を仮定しない。
正次数が order-zero の branch を自動的に排除する。
実装: [CyclotomicAddress](../../../DkMath/NumberTheory/GapFocusing/CyclotomicAddress.lean)。

## 4. 住所は本当に r*q^k に制限されるか

**はい。素数 `q`、`q∤b`、正次数 `n` で iff として証明した。**

```text
q | H_n(a,b)  iff  exists k:N, n=r*q^k
L_q(a,b) = {n | 1<n and exists k:N, n=r*q^k}.
```

`q∤n` の場合は `r=n` にちょうど一致する。`q|n` の場合は prime-power
inflation の branch となる。任意の住所 `n>1` は `n*q` にも出現し、
その次の住所が `n` より大きいことを証明した。`q=2` に住所法則の追加例外は
ない。非零比の order は `q-1=1` を割るので、非自明住所は 2 の正冪になる。

座標の消失も曖昧な exception とせず、別の checked theorem で分類した。

| residue 座標条件 | 非自明住所集合 |
| --- | --- |
| `q∤a`, `q∤b` | 正の位数 `r` による `r*q^k>1` の列 |
| `q|a`, `q∤b` | 空集合 |
| `q∤a`, `q|b` | 空集合 |
| `q|a`, `q|b` | 全 `n>1` |

後二行は zero-anchor evaluation `H_n(a,0)=a^totient(n)` によって証明した。
正次数では `totient(n)>0` を保持する。
実装: [CyclotomicBoundary](../../../DkMath/NumberTheory/GapFocusing/CyclotomicBoundary.lean)。
原始座標の gcd 条件は最後の全住所 branch を排除するが、order-ray 法則
自体に gcd 仮定は不要である。

## 5. 最初と後続の層の valuation を何が制御するか

checked 範囲は三つに分かれる。

**最初の層、unit anchor。** 整数 `a`、正次数 `r` が `orderOf(a mod q)` に
一致し、`a^r-1≠0` なら

```text
padicValInt q (Phi_r(a)) = padicValInt q (a^r-1).
```

を証明した。既存 full divisor product と住所法則によって proper divisor
層の valuation が全て 0 となり、最初の層が完全な load を保持する。
この load に上界 1 は仮定していない。

**完全なべき差の LTE。** 自然数 `a,b,r`、奇素数 `q`、`b<a`, `r≠0`,
`q∤a`, `q | a^r-b^r` の下で、任意の `k` に対し

```text
v_q(a^(r*q^k)-b^(r*q^k)) = v_q(a^r-b^r)+k.
```

prime two では別の correction が必要であり、`b<a`, `r≠0`, `2∤a`,
`2 | a^r-b^r` の下で

```text
v_2(a^(r*2^(k+1))-b^(r*2^(k+1)))
  = v_2(a^r+b^r)+v_2(a^r-b^r)+k.
```

を証明した。これは完全な power difference の load であり、各層の load
を個別に確定する式ではない。

**個別後続層、unit anchor / order one。** `a>1` とする。
奇素数 `q`、`q∤a`, `q | a-1` の下で、全 `k` に対し
`v_q(Phi_(q^(k+1))(a))=1`。prime two では最初の非自明層が
`v_2(Phi_2(a))=v_2(a+1)` を保持し、`2∤a`, `2 | a-1` の下で以降の
`Phi_(2^(k+2))(a)` は load 1 となる。

これらは有限計算ではなく、任意の `k` に対する theorem。
ただし一般斉次 `Phi_(r*q^k)(a,b)` の個別後続 load 1 はまだ証明していない。
完全な住所分類と、個別 valuation の形式化範囲を区別する。
実装: [LayerValuation](../../../DkMath/NumberTheory/GapFocusing/LayerValuation.lean)。
詳細: [valuation-audit-003](valuation-audit-003.md)。

primitive load の反例も実際の一般斉次 evaluator で固定した。

```text
Phi_3(5,3)=49
PrimitivePrimeDivisor 5 3 3 7
v_7(Phi_3(5,3))=2.
```

`7∤3` であっても初出 load が 1 とは限らない。旧 research の過強な
valuation endpoints は今回の production 依存に用いていない。

## 6. Instruction 002 の successor freshness との違い

Instruction 002 は正の原始座標で、次の GN に直前の GN にない素因子が
あることを証明した。今回の `FirstLayerAppearance` と既存 primitive notion
は、全ての正の低次数への非出現を要求する。

```text
GN_5(1,1)=31, GN_6(1,1)=63
Phi_2(2)=3, Phi_3(2)=7, Phi_6(2)=3.
```

3 と 7 は次数 5 の GN に対して fresh だが、次数 2/3 に既出であり、
次数 6 の globally primitive prime ではない。任意の素数 `q` について
`¬ exists q, PrimitivePrimeDivisor 2 1 6 q` を回帰で確認した。
次数 6 の 3 の負荷は、異なる二つの divisor layer の両方に現れる。
この例は、隣接次数の層集合の完全な置換と、より古い層に対する素数初出性を
同一視しないための calibration である。

## 7. Zsigmondy notion と住所の関係

自然数 `a,b`、`b≤a`, `n>0`, 素数 `q`, `q∤b` の下で

```text
PrimitivePrimeDivisor a b n q
  iff primeOrder q a b=n
  iff FirstLayerAppearance q a b n.
```

を **双方向** で証明した。`n>1` の primitive witness は、それ自体から
`q∤a,b` を導けるため、その方向の first-layer transport は座標の gcd 仮定
なしに適用できる。primitive degree が `q-1` を割ることも証明した。

`n>1` だけの集合の最小元を primitive とする解釈には、次数 1 に出現しない
条件が必要である。order-one の checked counterexample がこれを示す。
また既存 predicate には `n>0` が組み込まれておらず、例えば次数 0 の
`PrimitivePrimeDivisor 2 1 0 3` は vacuously 成立する。そのため新規の order
characterization は正次数を明示している。

既存の checked **存在** theorem は依然として次の十分条件の範囲である。

```text
d.Prime, 3≤d, b<a, 0<b, a.Coprime b, not d|(a-b)
  -> exists q, PrimitivePrimeDivisor a b d q.
```

`exists_primitivePrimeDivisor_prime_exp` と body/kernel 特殊化の型を現在の
[Zsigmondy](../../../DkMath/Zsigmondy.lean) で再確認し、公理も再監査した。
住所の **条件付き分類** は、各次数に primitive witness を供給する新しい
存在 theorem ではない。`d∤a-b` は既存証明の十分条件であって、例外の
必要十分分類ではない。Instruction 002 の `PrimitivePrimeDivisor 4 1 3 7`
という例はこの非必要性を保持する。全 Bang–Zsigmondy 定理を仮定していない。
既存 exception/research API の詳細は
[primitive-prime-audit-002](primitive-prime-audit-002.md) を参照。

## 8. 円分層 aliasing と呼べる theorem-level 対象

対象は関数 `n ↦ layerPrimeSupport a b n` と、その prime-incidence fibers
`primeLayerAddresses q a b` である。評価前の formal index を混同しない。
例 `(a,b)=(2,1)` では次数 2 と 6 の評価がともに 3 であり、二つの prime
support 集合も等しい。従ってこの support 関数は **実際に非単射** である。
単に二つの異なる集合に共通元があるという弱い観察に留めていない。

modulo 3 ではさらに正確な polynomial identity

```text
Phi_6 over ZMod 3 = (Phi_2 over ZMod 3)^2
```

を回帰で検証した。一般の characteristic-prime power identities が
繰り返し根を生むことが再出現の algebraic mechanism である。
characteristic-zero の多項式 layer を同一視する定理ではない。

形式化された最小の意味では、layer aliasing は「異なる index から同じ
有理素数 support への incidence」であり、その fiber を位数列が分類する。
共通座標 prime を除くと各 fiber は `r*q^k>1` の乗法列である。
これを重ねた support pattern を moire と呼ぶのは解釈であり、追加の幾何学、
加法的周期、FLT unit gauge、ramifier normalization の theorem ではない。

## 実装・一次ソース・検証範囲

| 新規 production module | 宣言数 | 内容 |
| --- | ---: | --- |
| `CyclotomicAddress` | 8 | characteristic-prime root と整数評価の分類 |
| `PrimeOrder` | 13 | residue definitions、べき差、primitive order |
| `HomogeneousAddress` | 17 | 既存 evaluator transport、住所・support・初出 |
| `CyclotomicBoundary` | 7 | zero-anchor と座標消失の完全な境界 |
| `LayerValuation` | 8 | first load、LTE、限定した個別 layer loads |
| **合計** | **53** | **48 theorem と 5 definition** |

core の一次ソースは Mathlib
[Cyclotomic/Expand](../../../.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/Cyclotomic/Expand.lean)
の `isRoot_cyclotomic_prime_pow_mul_iff_of_charP` と characteristic-prime
polynomial identities、
[Homogenize](../../../.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Homogenize.lean)
の評価・係数写像、
[Multiplicity](../../../.lake/packages/mathlib/Mathlib/NumberTheory/Multiplicity.lean)
の LTE である。旧 DkMath theorem の名前だけから一般 cyclotomic 値や valuation
を推定せず、実際の evaluator と型を再利用した。

production 5 module は既存 `DkMath.NumberTheory.GapFocusing` facade に接続した。
新規 regression 4 module と全件公理監査 1 module、53 production 宣言と
29 名前付き regression の監査を行った。検証のコマンドと記録は
[validation-003](validation-003.md)、durable checkpoints は
[findings-003](findings-003.md)。

## 解釈・残る形式化の義務

- `r*q^k` は条件を明示した checked address law。moire はその incidence
  を重ねて眺める用語であり、独立した新しい法則を追加していない。
- 一般の斉次後続層 `Phi_(r*q^k)(a,b)` の valuation 完全分類は未実装。
  個別因子の負荷を full divisor product の valuation から抽出する義務が残る。
- 毎次数の globally primitive prime の存在は住所分類からは得られない。
  一般 Zsigmondy の全存在範囲・全例外 theorem は追加していない。
- 加法的周期や漸近密度についての theorem、幾何学的 object map、FLT
  unit gauge / ramifier normalization への写像は今回の成果には含まれない。

**Outcome A — classified reappearance law（valuation は上記の bounded scope）。**
