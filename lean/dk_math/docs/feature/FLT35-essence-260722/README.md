# FLT3 / FLT5 共通本質の抽出・統合

実態調査・Lean 実装設計・standalone 化計画

- Project: `dkmath`
- Branch: `feature/FLT35-essence-260722-v0`
- Date: 2026-07-22
- Status: implementation roadmap

## 0. 結論

FLT3 と FLT5 の完成定理を直接つなぐのではない。

統合対象は、その下にある次の三層である。

```text
差冪と GN
  ↓
boundary escape / local valuation
  ↓
二座標・共役・ノルム・判別式
```

今回の調査で確定した実態は次の通り。

1. FLT3 standalone v3 は `import Mathlib` だけで構築された単一ファイル研究束である。
2. ただし中心定理 `FLT_d3_by_padicValNat` は `hS0_not_sq` を仮定する条件付き定理であり、DkMath-native な無条件 FLT3 完成定理ではない。
3. DkMath には別に、Mathlib の完成済み FLT3 を包む control route `DkMath.FLT.FLT3_core` がある。
4. FLT5 は `DkMath.FLT.Five.fermatFive_no_positive_solution` まで無条件に閉じている。
5. 現在の `DkMath.FLT.Five.Standalone` は Mathlib-only だが、GN5 恒等式だけを収めた seed であり、完成証明全体の standalone 化は未完である。

したがって、この feature の成果物は次の三本とする。

- 中立層 `DkMath.NumberTheory.TraceOneQuadratic`
- FLT3 / FLT5 を中立層へ接続する bridge
- 完成済み FLT5 塔から再生成可能な Mathlib-only full standalone artifact

## 1. 調査対象

主要対象は次である。

```text
lean/dk_math/DkMath/FLT/docs/StandAlone/
  FLT3#StandAlone-NC-v0.lean-v3.lean.txt

lean/dk_math/DkMath/FLT/MathlibBridge/FLT34.lean
lean/dk_math/DkMath/FLT/Main.lean
lean/dk_math/DkMath/FLT/GEisensteinBridge.lean
lean/dk_math/DkMath/Petal/EisensteinBridge.lean

lean/dk_math/DkMath/FLT/Five/*.lean
lean/dk_math/DkMath/FLT/Five/Standalone.lean
lean/dk_math/DkMathTest/FLT/Five/CheckAxioms.lean
```

調査順序は GitHub current source、README / AGENT / SUMMARY、snapshot、standalone source、axiom audit とした。

## 2. FLT3 の実態

### 2.1. 二つの route

#### Control route

`DkMath.FLT.MathlibBridge.FLT34` は Mathlib の FLT3 を包む。

```lean
theorem FLT3_core : FermatLastTheoremFor 3 :=
  fermatLastTheoremThree
```

これは無条件の完成済み FLT3 だが、proof provenance は Mathlib 側にある。

#### DkMath-native valuation route

中心定理は次である。

```lean
theorem FLT_d3_by_padicValNat {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hS0_not_sq :
      ∀ {q : ℕ}, Nat.Prime q →
        q ∣ c ^ 3 - b ^ 3 →
        ¬ q ∣ c - b →
        ¬ q ^ 2 ∣ S0_nat c b) :
    a ^ 3 + b ^ 3 ≠ c ^ 3
```

証明 spine は完成している。

```text
反例方程式
  ↓
c³ - b³ = a³
  ↓
境界 c-b を割らない素数 q を抽出
  ↓
q | a³ なので v_q ≥ 3
  ↓
NoSq / NoLift により v_q ≤ 1
  ↓
3 ≤ 1
```

未完なのは、一般入力に対して `hS0_not_sq` を無条件に構築する arithmetic kernel である。

### 2.2. standalone v3

standalone v3 は次の性質を持つ。

```text
import Mathlib only
single-file build target
DkMath module を import しない
GN / S0 / primitive prime / padicValNat / NoLift scaffold を局所複製
```

snapshot 上の概算規模は次である。

```text
lines         1,824
structures        9
inductives        2
definitions      49
lemmas           66
theorems         26
```

ただし、これを「無条件 FLT3 完成証明」と表現してはならない。

`NoSqOnS0`、`NonLiftableS0`、`DescentClassifyImpossibleOnPrimitive`、`GEisensteinDescentCore` は条件を整理・運搬する API であり、NoLift の算術的発生そのものを自動証明するものではない。

また、ファイル見出しの “no coprimality assumptions” は現行中心 theorem と整合しない。中心 theorem は `Nat.Coprime a b` を入力に持つ。

## 3. FLT5 の実態

### 3.1. 無条件 endpoint

公開終点は次である。

```lean
abbrev FLT5Target : Prop :=
  ∀ x y z : ℕ,
    0 < x → 0 < y → 0 < z →
    ¬ Fermat5Equation x y z

theorem flt5Target : FLT5Target

theorem fermatFive_no_positive_solution
    (x y z : ℕ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    ¬ Fermat5Equation x y z
```

proof route は概ね次である。

```text
positive Fermat5 equation
  ↓
primitive CounterexamplePack
  ↓
signed gap orientation
  ↓
five-adic routing and power split
  ↓
square / golden coordinates
  ↓
ramifier stripping
  ↓
conjugate coprimality
  ↓
fifth power up to a unit
  ↓
five unit sectors
  ├─ sectors 1..4: arithmetic exclusion
  └─ sector 0: inversion / factorization / strict descent
  ↓
unconditional contradiction
```

初期 clean-channel valuation obstruction、

```text
complete fifth power  → local load ≥ 5
clean GN5 channel     → local load ≤ 1
```

は有効な独立補題だが、全候補を閉じる最終機構ではない。最終閉鎖は signed five-adic / golden-order / zero-sector descent が担う。

### 3.2. 現行 standalone

現在の `DkMath.FLT.Five.Standalone` が持つのは次だけである。

- `Fermat5Equation`
- `GN5`
- `(g+y)^5 = y^5 + g*GN5(g,y)`
- subtraction form
- `GN5 1 1 = 31`

よって、これは full proof ではなく Mathlib-only seed である。

## 4. FLT3 / FLT5 比較

| 層 | FLT3 DkMath-native | FLT5 DkMath-native |
|---|---|---|
| 方程式 | $a^3+b^3=c^3$ | $x^5+y^5=z^5$ |
| primitive 化 | coprime を入力 | positive solution から packet 化 |
| gap | $g=c-b$ | signed difference / sum |
| kernel | $GN_3(g,b)=S_0(c,b)$ | explicit `GN5 g y` |
| boundary escape | $q\nmid g$ | clean / signed routing |
| perfect-power load | $v_q\ge3$ | $v_q\ge5$ |
| local NoLift | 仮定または bundle | clean channel では証明済み |
| quadratic norm | shifted Eisenstein | Golden norm |
| quadratic order | bridge / scaffold | direct coordinate ring |
| unit classification | 未完成 | mod fifth powers で完成 |
| exceptional sector | NoLift 側に残る | strict descent で閉鎖 |
| endpoint | 条件付き | 無条件 |
| standalone | research bundle | GN5 seed のみ |

## 5. 共通する valuation spine

奇素数指数 $p$ に対し、gap $g=z-y$ を取る。

$$z^p-y^p=g\,GN_p(g,y)$$

境界 $g$ を割らない素数 $q$ が差冪を割れば、$q$ は kernel 側へ入る。

$$q\mid z^p-y^p\quad\land\quad q\nmid g\quad\Longrightarrow\quad q\mid GN_p(g,y)$$

Fermat 方程式により差冪が完全 $p$ 乗なら、局所 load は $p$ 以上となる。

$$p\le v_q(z^p-y^p)$$

kernel channel が lift しなければ、load は 1 以下となる。

$$q\mid GN_p\quad\land\quad q^2\nmid GN_p\quad\Longrightarrow\quad v_q(GN_p)\le1$$

したがって、FLT3 と FLT5 の初期 obstruction は同じ形に入る。

$$p\le v_q(z^p-y^p)\le1$$

## 6. trace-one quadratic core

整数パラメータ $s$ に対し、基底元 $\tau_s$ を次で定める。

$$\tau_s^2=\tau_s+s$$

二座標元 $a+b\tau_s$ の共役は次である。

$$\overline{\tau_s}=1-\tau_s$$

積は二座標内で閉じる。

$$(a+b\tau_s)(c+d\tau_s)=(ac+sbd)+(ad+bc+bd)\tau_s$$

trace、norm、判別式は次である。

$$\operatorname{Tr}_s(a,b)=2a+b$$

$$N_s(a,b)=a^2+ab-sb^2$$

$$\Delta_s=1+4s$$

$$4N_s(a,b)=(2a+b)^2-\Delta_s b^2$$

$\tau_s^2$ は第三座標を作らず、既存二座標へ還元される。

### 6.1. FLT3 specialization

$s=-1$ とすると、

$$N_{-1}(a,b)=a^2+ab+b^2$$

$$\Delta_{-1}=-3$$

よって、

$$S_0(a,b)=N_{-1}(a,b)$$

となる。

現在の `eisensteinNormNat` は標準基底 $x^2-xy+y^2$ を使うため、

$$S_0(a,b)=\operatorname{EisNorm}(a+b,b)$$

という shifted bridge を持つ。

### 6.2. FLT5 specialization

$s=1$ とすると、

$$N_1(a,b)=a^2+ab-b^2$$

$$\Delta_1=5$$

これは現在の `GoldenInt` / `goldenNorm` の座標式である。

endpoint square coordinates、

$$m=(g+y)^2+y^2$$

$$n=(g+y)y$$

により、

$$GN_5(g,y)=N_1(m,n)$$

となる。

## 7. 共通化しない層

Phase 1 では次を一般化しない。

- FLT3 の `3 ∣ c-b` 特別分岐
- `S0PrimeSupportExceptThree`
- FLT5 の mod 25 routing
- FLT5 の ramifier `tau`
- five unit sectors
- zero-sector inversion / factorization / descent
- 一般奇素数 $p$ に対する quadratic-subfield factorization
- 一般 FLT theorem

共通 core は既存証明を置き換えるものではなく、両 proof tower の共通座標を露出する観測 API とする。

## 8. module 設計

推奨配置は次である。

```text
DkMath/
├── NumberTheory/
│   └── TraceOneQuadratic.lean
│
├── FLT/
│   ├── ThreeTraceOneBridge.lean
│   ├── QuadraticEssence.lean
│   └── Five/
│       └── TraceOneBridge.lean
```

依存方向は次とする。

```text
DkMath.NumberTheory.TraceOneQuadratic
      ↑                         ↑
FLT3 bridge                FLT5 bridge
      \                         /
       DkMath.FLT.QuadraticEssence
```

禁止する依存方向は次である。

```text
NumberTheory -> FLT
FLT3 proof   -> FLT5 proof
FLT5 proof   -> FLT3 proof
```

既存 endpoint は変更しない。

```text
DkMath.FLT.FLT3_core
DkMath.FLT.FLT_d3_by_padicValNat
DkMath.FLT.Five.flt5Target
DkMath.FLT.Five.fermatFive_no_positive_solution
```

## 9. `TraceOneQuadratic` API

### 9.1. skeleton

```lean
namespace DkMath.NumberTheory.TraceOneQuadratic

structure TraceOneInt (s : ℤ) where
  fst : ℤ
  snd : ℤ
  deriving DecidableEq, Repr

def ofInt (s a : ℤ) : TraceOneInt s := ⟨a, 0⟩

def tau (s : ℤ) : TraceOneInt s := ⟨0, 1⟩

def mul (x y : TraceOneInt s) : TraceOneInt s :=
  ⟨x.fst * y.fst + s * x.snd * y.snd,
    x.fst * y.snd + x.snd * y.fst + x.snd * y.snd⟩

def conj (x : TraceOneInt s) : TraceOneInt s :=
  ⟨x.fst + x.snd, -x.snd⟩

def trace (x : TraceOneInt s) : ℤ :=
  2 * x.fst + x.snd

def norm (x : TraceOneInt s) : ℤ :=
  x.fst ^ 2 + x.fst * x.snd - s * x.snd ^ 2

def discr (s : ℤ) : ℤ :=
  1 + 4 * s

end DkMath.NumberTheory.TraceOneQuadratic
```

### 9.2. Phase 1 instance

- `Zero`
- `One`
- `Add`
- `Neg`
- `Sub`
- `Mul`
- `AddCommGroup`
- `CommRing`

一般 $s$ に対する `IsDomain`、PID、UFD、Euclidean domain は要求しない。$T^2-T-s$ が可約な $s$ もあるため、generic core を無条件に整域と宣言してはならない。

### 9.3. theorem surface

```lean
traceOne_ext
traceOne_tau_sq
traceOne_conj_invol
traceOne_conj_mul
traceOne_mul_conj
traceOne_norm_mul
four_mul_traceOneNorm_eq_discriminant
traceOneNorm_neg_one
traceOneNorm_one
```

## 10. FLT3 bridge

対象:

```text
DkMath/FLT/ThreeTraceOneBridge.lean
```

公開候補:

```lean
S0_nat_eq_traceOneNorm_negOne
S0_int_eq_traceOneNorm_negOne
GN_three_sub_eq_traceOneNorm_negOne
eisensteinNorm_shift_eq_traceOneNorm_negOne
```

既存 FLT3 theorem statement は変更しない。

## 11. FLT5 bridge

対象:

```text
DkMath/FLT/Five/TraceOneBridge.lean
```

公開候補:

```lean
goldenToTraceOne
goldenNorm_eq_traceOneNorm_one
GoldenNorm_eq_traceOneNorm_one
GN5_eq_traceOneNorm_squareLink
```

最初は coordinate equality に限定する。

```lean
def goldenToTraceOne (x : GoldenInt) : TraceOneInt 1 :=
  ⟨x.fst, x.snd⟩
```

Phase 1 では `GoldenInt` を type alias に置き換えない。

## 12. common facade

対象:

```text
DkMath/FLT/QuadraticEssence.lean
```

公開範囲は次だけとする。

```text
exponent 3 kernel -> TraceOneInt (-1)
exponent 5 kernel -> TraceOneInt 1
```

一般 $p$ theorem は置かない。

## 13. FLT5 full standalone

### 13.1. 方針

完成済み module tower を手作業で再証明しない。

production source を manifest の topological order で flatten し、Mathlib-only single file を再生成する。

standalone は leaf artifact であり、DkMath production module から import しない。

### 13.2. 成果物

```text
DkMath/FLT/docs/StandAlone/
├── FLT5#StandAlone-v0.lean.txt
├── FLT5#StandAlone-v0.lean.build.log
├── FLT5#StandAlone-v0.lean.txt.sha256
└── FLT5#StandAlone-v0.manifest.txt
```

`NC` の意味が現行資料で一意に定義されていないため、新しい FLT5 名には引き継がない。

### 13.3. generator

推奨 script:

```text
lean/dk_math/scripts/generate-flt5-standalone.py
```

責務:

1. manifest の source file を確認
2. manifest order を import graph に対して検証
3. `import DkMath...` と file marker を除去
4. source commit SHA と module list を header に記録
5. UTF-8 artifact を生成
6. isolated single-file build
7. checksum と build log を生成

script は theorem statement と proof body を変更しない。

### 13.4. source order

初期候補は次である。

```text
Basic
GN5
CleanChannel
Reduction
NormalForm
BranchB
Provider
BranchA
SignedBranchA
SignedFiveAdic
SignedFiveAdicPowerSplit
SquareGoldenBridge
SquareGoldenNormalForm
SignedSquareGoldenExceptional
GoldenOrder
GoldenDivisibility
GoldenEuclidean
SignedGoldenRamifierStripped
SignedGoldenConjugateCoprime
SignedGoldenFifthPower
GoldenFifthPowerCoordinates
GoldenCoprimeFactor
SignedGoldenUnitClasses
SignedGoldenSectorArithmetic
SignedGoldenZeroSector
SignedGoldenZeroSectorInversion
SignedGoldenZeroSectorFactorization
GoldenUnitClassification
SignedGoldenZeroSectorDescent
SignedGoldenClosure
SignedGoldenZeroSectorFinal
Valuation
Main
```

現行 `Standalone.lean` seed は定義が重複するため full manifest に含めない。

### 13.5. endpoint contract

生成 file の末尾で次を検査する。

```lean
#print axioms DkMath.FLT.Five.fermatFive_no_positive_solution

example (x y z : ℕ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    ¬ DkMath.FLT.Five.Fermat5Equation x y z :=
  DkMath.FLT.Five.fermatFive_no_positive_solution x y z hx hy hz
```

禁止依存:

```text
sorryAx
DkMath 独自 axiom
native_decide
未証明 receiver assumption
```

## 14. checkpoint roadmap

### F35-001. 実態調査・設計固定

- 本 README
- conditional / unconditional 境界
- route matrix
- standalone policy

### F35-002. TraceOneQuadratic core

```text
DkMath/NumberTheory/TraceOneQuadratic.lean
```

完了条件:

```text
lake build DkMath.NumberTheory.TraceOneQuadratic
```

### F35-003. FLT3 bridge

```text
DkMath/FLT/ThreeTraceOneBridge.lean
```

- S0 direct norm bridge
- shifted Eisenstein compatibility
- GN3 gap bridge

### F35-004. FLT5 bridge

```text
DkMath/FLT/Five/TraceOneBridge.lean
```

- GoldenInt coordinate map
- norm compatibility
- GN5 square-coordinate bridge

### F35-005. Common facade / audit

```text
DkMath/FLT/QuadraticEssence.lean
DkMathTest/FLT/QuadraticEssence.lean
```

- exponent 3 / 5 facade
- specializations $s=-1,1$
- axiom audit

### F35-006. Standalone manifest / generator

- deterministic generation
- source commit 記録
- regeneration diff が空

### F35-007. FLT5 full standalone

- `import Mathlib` 以外の import なし
- single-file build PASS
- final endpoint PASS

### F35-008. Comparator / trust audit

- Comparator challenge statement
- public theorem と standalone theorem の statement 対応
- `#print axioms` log

### F35-009. Documentation closure

- module map
- provenance
- known non-goals
- completed status へ更新

## 15. verification commands

```bash
cd lean/dk_math

lake build DkMath.NumberTheory.TraceOneQuadratic
lake build DkMath.FLT.ThreeTraceOneBridge
lake build DkMath.FLT.Five.TraceOneBridge
lake build DkMath.FLT.QuadraticEssence
lake build DkMath.FLT.Five
lake build DkMathTest.FLT.Five.CheckAxioms
```

standalone build:

```bash
cp 'DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.txt' /tmp/FLT5Standalone.lean
lake env lean /tmp/FLT5Standalone.lean \
  2>&1 | tee 'DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.build.log'
sha256sum 'DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.txt'
```

## 16. risk register

### Risk A. FLT3 完成状態の誤読

control route と native route を別記し、`hS0_not_sq` を theorem contract に明示する。

### Risk B. generic core の過剰抽象化

Phase 1 は coordinate ring と norm identity に限定する。generic `IsDomain` / PID / UFD は導入しない。

### Risk C. GoldenOrder の大規模 refactor

bridge-only とし、type alias 化は後続 feature へ分離する。

### Risk D. standalone drift

手動 copy を禁止し、manifest generator、source commit、checksum を保存する。

### Risk E. flatten order の誤り

`Main.lean` の import 列挙順をそのまま使わず、source import graph で検査する。

### Risk F. research hypothesis の theorem 化

$p=7$ 以降は experiment に隔離し、common facade に一般 $p$ theorem を置かない。

## 17. Definition of Done

1. `TraceOneInt s` の ring / conjugation / norm / discriminant API が完成
2. FLT3 の $S_0$ と FLT5 の GoldenNorm が同じ neutral norm API へ接続
3. 既存 FLT3 / FLT5 endpoint に変更なし
4. FLT5 full standalone が Mathlib-only single-file build PASS
5. public FLT5 endpoint と standalone endpoint の statement が一致
6. axiom audit で `sorryAx` なし
7. provenance、manifest、checksum が保存

完成時、次が Lean 上の確定 Core となる。

$$GN_3\longrightarrow N_{-1}$$

$$GN_5\longrightarrow N_1$$

## 18. 後続研究

### 18.1. exponent seven smoke test

候補形式:

$$A=z^3+z^2y-y^3$$

$$B=-z^2y-zy^2$$

恒等式:

$$z^6+z^5y+z^4y^2+z^3y^3+z^2y^4+zy^5+y^6=A^2+AB+2B^2$$

右辺は $N_{-2}(A,B)$ である。

これは experiment theorem として `ring` で検証するが、本 feature の完了条件には含めない。

### 18.2. general odd-prime quadratic subfield

一般候補:

$$p^\ast=(-1)^{(p-1)/2}p$$

$$s_p=\frac{p^\ast-1}{4}$$

$$\Phi_p(z,y)=N_{s_p}(A_p(z,y),B_p(z,y))$$

整数係数形式 $A_p,B_p$ の構成と一般 theorem は別 feature とする。

### 18.3. Jacobian dimension-two connection

trace と norm による二座標閉鎖は、DkMath の Core / Gap 読みでは次の候補原理を示す。

```text
二つの Core
  + 一つの共役
  + trace / norm closure
  → 独立な第三 Gap direction を保持しにくい
```

これは Jacobian conjecture $n=2$ の証明ではない。

本 feature では、FLT3 / FLT5 の実装済み二次ノルム閉鎖を、dimension-two obstruction 研究にも再利用できる中立 API として固定するところまでとする。
