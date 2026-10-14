# Primitive-prime / 既存テーマ監査 — Instruction 002

2026-10-04。現在の Lean 4.34.1 / Mathlib v4.34.1 ソースを再確認した。
これは Phase 6–7 の監査であり、古典的 Zsigmondy 定理の一般版を
今回の successor 定理に追加するものではない。

## 結論と形式的反例

**隣接次数の GN 値の互いに素性は、すべての過去の次数に対する原始素因子の
存在を含意しない。** 実際、同じ基底 `(x,u)=(1,1)` で

```text
GN_5(1,1) = 2^5 - 1 = 31
GN_6(1,1) = 2^6 - 1 = 63 = 3^2 * 7
gcd(31,63) = 1
3 | 2^2 - 1
7 | 2^3 - 1
¬ ∃ q, PrimitivePrimeDivisor 2 1 6 q
```

を Lean の既存 GN と既存 `PrimitivePrimeDivisor` 定義に対して証明した。
最後の命題は、有限個の候補を列挙して終わる主張ではなく、任意の素数 `q`
について `q | 63` から次数 2 または 3 への既出性を導く証明である。
31 との直前比較では新しい support でも、全履歴に対しては新しくない。

実装・公理監査: [PrimitivePrimeAudit002.lean](checks/PrimitivePrimeAudit002.lean)。
新規の五つの回帰命題は `sorryAx` に依存しない。

## 現在利用できる原始素因子定理

`DkMath.Zsigmondy.PrimitivePrimeDivisor a b n q` の内容は

```lean
Nat.Prime q ∧ q ∣ a ^ n - b ^ n ∧
  ∀ m : ℕ, 0 < m → m < n → ¬ q ∣ a ^ m - b ^ m
```

である。自然数の減算なので、存在定理は `b<a` を明示的に持つ。

| 既存宣言 | 型・仮定・実際の保証 | 一次ソース |
| --- | --- | --- |
| `DkMath.NumberTheory.GcdDiffPow.exists_prime_divisor_not_dividing_diff_of_prime_exp` | `a,b,p : ℕ`; `p.Prime`, `3≤p`, `b<a`, `0<b`, `a.Coprime b`, `¬p∣a-b`; 差の素因子 `q` を取り、`q∤a-b` を得る | [GcdDiffPow](../../../DkMath/NumberTheory/GcdDiffPow.lean) |
| `DkMath.NumberTheory.GcdNext.exists_primitive_prime_factor_basic` | 上記の薄い wrapper。全ての低次数への非整除まではこの statement に含まれない | [ZsigmondyCyclotomic](../../../DkMath/NumberTheory/ZsigmondyCyclotomic.lean) |
| `DkMath.NumberTheory.GcdNext.prime_exp_not_dvd_diff_imp_primitive` | 素数指数 `d`、素数 `q`、`a.Coprime b`, `b<a`, `0<b`, `q∣a^d-b^d`, `q∤a-b`; `ZMod q` の単数比の位数を使い、全 `0<k<d` の非整除を証明 | 同上 |
| `DkMath.Zsigmondy.exists_primitivePrimeDivisor_prime_exp` | `d.Prime`, `3≤d`, `b<a`, `0<b`, `a.Coprime b`, `¬d∣a-b`; 本当の全低次数条件を持つ `PrimitivePrimeDivisor` の存在 | [Zsigmondy](../../../DkMath/Zsigmondy.lean) |
| `DkMath.Zsigmondy.exists_primitivePrimeDivisor_body_nat` | `x,u,d : ℕ`; `d.Prime`, `3≤d`, `0<x,u`, `(x+u).Coprime u`, `¬d∣x`; 基底 `(a,b)=(x+u,u)` へ特殊化 | 同上 |
| `DkMath.Zsigmondy.exists_primitivePrimeDivisor_kernel_nat` | 同じ仮定で `PrimitivePrimeDivisor (x+u) u d q ∧ q∣KernelN x u d` を得る | 同上 |
| `DkMath.NumberTheory.PrimitiveBeam.PrimitivePrimeFactorOfDiffPow` | 引数順が `q,a,b,d` で低次数 `k` が暗黙引数の同じ原始性条件 | [PrimitiveBeam](../../../DkMath/NumberTheory/PrimitiveBeam.lean) |
| `DkMath.NumberTheory.PrimitiveBeam.exists_primitive_prime_factor_as_prop` | 同じ素数指数・非整除仮定で上述の proposition を得る | 同上 |
| `DkMath.NumberTheory.PrimitiveBeam.primitive_prime_dvd_GN_body` | 原始素因子が与えられ、`0<d`, `1<d` なら `q∣GN d x u`。存在を仮定から生成する定理ではなく、既存 witness の carrier 移送 | 同上 |

これらの存在・移送 endpoints の `#print axioms` を今回再実行し、
`propext`, `Classical.choice`, `Quot.sound` のみであることを確認した。
`PrimitiveBeam` が research モジュールを import している事実と、個々の定理が
`sorryAx` に依存するかどうかは区別する。

局所スタックが保証する範囲は **奇素数指数かつ `d∤a-b`** である。
合成数指数、次数 2、または `d∣a-b` の場合に一般存在が偽だと
言っているわけではない。特に回帰ファイルは

```text
3 | 4 - 1, かつ PrimitivePrimeDivisor 4 1 3 7
```

を証明する。従って `d∤a-b` はこの既存証明の十分条件であり、
古典的定理の必要十分な例外リストではない。

## Mathlib と cyclotomic-value の境界

ローカル `Mathlib/**/*.lean` 全体を `Zsigmondy`, `zsigmondy`,
`PrimitivePrimeDivisor`, `primitive prime`, `primitive divisor`, `Bang`
で検索した。Bang の無関係な parser 名を除き、一般 Bang–Zsigmondy
原始素因子定理に対応する宣言は見つからなかった。
この状態は既存 [Petal-Zsigmondy-Preflight](../../../DkMath/Petal/docs/Petal-Zsigmondy-Preflight.md)
の記録とも一致し、今回は現在の依存ソースに対して検索を再実行している。

| Mathlib の実在 API | 正確な範囲 | 一次ソース |
| --- | --- | --- |
| `Polynomial.cyclotomic.dvd_X_pow_sub_one` | `[Ring R]`; 多項式 `Φ_d` が `X^d-1` を割る | [Cyclotomic/Basic](../../../.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/Cyclotomic/Basic.lean) |
| `Polynomial.prod_cyclotomic_eq_geom_sum` | `[CommRing R]`, `0<d`; `d.divisors.erase 1` の層の積は幾何和 | 同上 |
| `Polynomial.squarefree_cyclotomic` | `[Field K] [NeZero (d : K)]`; 多項式自身の squarefree 性 | 同上 |
| `Polynomial.cyclotomic.irreducible`, `Polynomial.cyclotomic.irreducible_rat` | 正次数、`ℤ[X]` / `ℚ[X]` 上の既約性 | [Cyclotomic/Roots](../../../.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/Cyclotomic/Roots.lean) |
| `Polynomial.cyclotomic.isCoprime_rat` | 相異なる index に対する `ℚ[X]` 上の coprimality | 同上 |
| `Polynomial.isRoot_cyclotomic_iff` | `[CommRing R] [IsDomain R] [NeZero (d : R)]`; root と primitive root の同値。mod 素数への特殊化では index が標数で消えない条件を保持する | 同上 |
| `Polynomial.eval_one_cyclotomic_prime`, `Polynomial.eval_one_cyclotomic_prime_pow`, `Polynomial.eval_one_cyclotomic_not_prime_pow` | `Φ_d(1)` の値を次数の素数冪性に応じて記述 | [Cyclotomic/Eval](../../../.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/Cyclotomic/Eval.lean) |
| `Polynomial.sub_one_lt_natAbs_cyclotomic_eval` | `n,q : ℕ`, `1<n`, `q≠1`; cyclotomic の整数値の大きさの下界 | 同上 |
| `Nat.exists_prime_gt_modEq_one` | `k≠0`; 任意の下界より大きい `p≡1 mod k` の素数が存在。証明内の基底は `k*n!` に選ばれ、指定した固定基底の primitive divisor 存在ではない | [PrimesCongruentOne](../../../.lake/packages/mathlib/Mathlib/NumberTheory/PrimesCongruentOne.lean) |

特に、多項式の既約性や squarefree 性から、その整数評価値の素因子の
初出性や valuation 1 を自動的に結論することはできない。

`DkMath.NumberTheory.GcdNext.cyclotomic_eval_divides` という名前も存在するが、
実際の型は `∃ n : ℤ, n∣(a^d:ℤ)-(b^d:ℤ)` にすぎず、証明は `n=1`。
cyclotomic 評価値を指定しないため、原始素因子の供給源ではない。
docstring にある homogeneous cyclotomic 値の提案と、現在の theorem statement
を区別する必要がある。

## 既存例外説明と未証明一般版

履歴文書 [Zsigmondy-CosmicFormula](../../../DkMath/Zsigmondy/docs/Zsigmondy-CosmicFormula.md)
は、`a>b>0`, `gcd(a,b)=1`, `n>1` の一般版の候補として

```text
(n=2 ∧ ∃k, a+b=2^k) ∨ (a=2 ∧ b=1 ∧ n=6)
```

を例外 predicate に置く案を記している。しかし同文書の
`ExceptionalZsigmondyCase` / `exists_primitivePrimeDivisor` の code block は
**将来の実装案**であり、現在の production 宣言としては存在しない。
今回、その一般定理を形式的説明として使用していない。
二番目の具体例 `(2,1,6)` の原始素因子不在は上記回帰で直接検証した。

`ZsigmondyCyclotomic.lean` の古い導入コメントは一般的な Zsigmondy 理論や
精密 valuation の完成を示唆する箇所があるが、監査は実際の declaration
と依存公理に基づく。一般指数の存在定理、全例外分類、primitive prime の
valuation 1 は今回の checked successor 結果には含まれない。

## Research / no-lift / squarefree の公理境界

| 宣言 | 今回確認した状態 |
| --- | --- |
| `DkMath.NumberTheory.GcdNext.squarefree_implies_padic_val_le_one_research` | [Research](../../../DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean) の既知の過強 statement。`#print axioms` に `sorryAx` がある |
| `DkMath.NumberTheory.GcdNext.padicValNat_primitive_prime_factor_le_one_research` | 上記 placeholder の wrapper |
| `DkMath.NumberTheory.PrimitiveBeam.primitive_prime_obstructs_GN_perfect_power_research` | valuation placeholder を通るため `sorryAx` がある。deprecated な非 research 名もこのルートに委譲する |
| `DkMath.NumberTheory.GcdNext.noLift_GN_of_primitive_prime_factor_is_false` | [NoLift](../../../DkMath/NumberTheory/ZsigmondyCyclotomicNoLift.lean) にある kernel-checked 反例。`(d,a,b,q)=(3,5,3,7)` で `GN_3(2,3)=49` となり、primitive でも `q^2` が割る |
| `DkMath.NumberTheory.GcdNext.padicValNat_primitive_prime_factor_le_one_of_squarefree_G` | [Squarefree](../../../DkMath/NumberTheory/ZsigmondyCyclotomicSquarefree.lean) の追加仮定 `Squarefree (GN d (a-b) b)` を保つ theorem。`sorryAx` がない |
| `PrimitiveBeam.primitive_prime_factor_forbids_perfect_pow_diff_of_noLift_GN`, `PrimitiveBeam.primitive_prime_obstructs_GN_perfect_power_of_noLift_GN` | 選んだ primitive witness について `¬q^2∣GN` を別途要求する honest conditional route |
| 対応する `_of_squarefree_GN` variants | GN の squarefree 性を別途要求する honest conditional route |

ここで必要な追加仮定は support の隣接分離からは得られない。

## PrimitiveSet と finite prime-scale の三つの意味

| API | 「primitive」の意味 | successor 結果との関係 |
| --- | --- | --- |
| `DkMath.NumberTheory.PrimitiveSet.PrimitiveOn` | 有限集合 `S` の divisibility antichain: `a,b∈S` と `a∣b` から `a=b` | 原始素因子の初出性や pairwise gcd 1 ではない。[Basic](../../../DkMath/NumberTheory/PrimitiveSet/Basic.lean) |
| `PrimitiveBeam.PrimitivePrimeFactorOfDiffPow` / `Zsigmondy.PrimitivePrimeDivisor` | 固定基底の全ての正の低次数の差に現れない素因子 | 次数 6 の反例が示すように隣接分離より強い |
| `StructuralArithmetic.FreshPrimeDirection S n q` | `q.Prime ∧ q∣n ∧ q∉S`、指定した有限集合 `S` に相対的な新方向 | `S` が直前の GN support なら隣接分離と接続する。全履歴 support を選ぶ場合は別の義務。[PrimitiveDirection](../../../DkMath/NumberTheory/StructuralArithmetic/PrimitiveDirection.lean) |

`StructuralArithmetic.SupportDisjointFrom S n` は全ての素因子の `S` からの
不在であり、一個の fresh witness より強い。
`exists_freshPrimeDirection_of_supportDisjointFrom` には `1<n` も必要である。
値が 1 の場合に「毎次数新しい素数がある」とは言えない。

`StructuralArithmetic.freshPrimeDirection_GN_of_primitivePrimeFactor` は
primitive witness に加えて **`q∉S` を明示的に受け取る**。
任意の既知 support に対する freshness を primitive witness の名前から
勝手に結論しない設計であり、今回の回帰で同 endpoint に `sorryAx` がない
ことも確認した。[GNBridge](../../../DkMath/NumberTheory/StructuralArithmetic/GNBridge.lean)

`Primitive.primitiveConservationKernel_dichotomy_of_le_fine_squareBody` は
`q≤P`, `0<m`, `m≤squareBody q` において、完全な旧素数世界
`primeScalesUpTo P` による生成か、唯一の大きい fresh 素数と小さい旧生成
cofactor への分解を保証する。fresh branch の毎回の発生を保証せず、
Zsigmondy primitive の定理でもない。同 endpoint の公理監査は `sorryAx`
なし。[PrimitiveConservationKernel](../../../DkMath/NumberTheory/Primitive/PrimitiveConservationKernel.lean)

`Primitive.PHZ30` の mod 30 / 210 support-disjointness と refinement は
有限素数世界の residue 制約であり、GN の全次数に対する primitive prime
供給ではない。[PHZ30](../../../DkMath/NumberTheory/Primitive/PHZ30.lean)

## 既存テーマとの数学的接続

1. **Gap Focusing / Prime Degree Rigidity.**
   `kernelPolynomial_eq_prod_cyclotomic` と
   `kernelPolynomial_irreducible_iff_prime` は形式多項式の層と既約性の定理。
   successor の Bézout 等式は同じ既存 GN の隣接分離を追加する。
   評価後の GN が素数であることや、素因子が全過去次数に現れないこととは
   別の命題である。[Degree](../../../DkMath/NumberTheory/GapFocusing/Degree.lean)

2. **FLT3/5/7 の規格化固定単数類.**
   `sameUnitPowerClass_of_fixed_extraction` は integrally closed domain 上で、
   同じ非零 carrier と非零 ramifier、正指数、二つの実際の
   unit-times-power extraction を与えた場合の root-choice independence。
   `ramifier_rescaling_same_class_iff` は規格化変更に必要な冪条件を別に示す。
   これらは successor の一般単数群 CRT を適用できる代数的入口だが、
   異なる次数で carrier や ramifier が自動一致することを保証しない。
   [UnitGauge](../../../DkMath/NumberTheory/GapFocusing/UnitGauge.lean)
   と既存 [EndpointAudit](../FLT357-CrossInvariant-Ultra-261004-v0/checks/EndpointAudit.lean)
   の p=3/5 規格化等式を現ソースで確認した。

3. **DRC product-degree composition.**
   `DkMath.CosmicFormula.GN_mul_degree` は全 commutative semiring 上で
   `GN_(ab)(x,u)=GN_a(x,u)*GN_b(x*GN_a(x,u),u^a)` を保証する。
   これは乗法的次数の composition であり、`d→d+1` の隣接分離とは別の
   操作。両者は同じ GN 上で併用できるが、product-degree が与える carrier
   置換を unit quotient の同一視に転用しない。
   [GNProductDegree](../../../DkMath/Lib/Cosmic/GNProductDegree.lean)

4. **「自然数 +1 で factor world が変わる」という解釈.**
   数としての `n,n+1` の互いに素性と、次数としての `GN_d,GN_(d+1)`
   の互いに素性は別の statement。後者は一般に GN 値が数として 1 だけ
   違うわけではなく、GN successor の剰余恒等式によって証明される。
   正しい表現は「原始基底では隣接 GN の素数 support が交わらない」。
   正の原始座標と `d>0` の下では、次の GN 値が 1 より大きいことも
   証明したため、直前の GN にない素因子が毎回存在する
   (`nat_exists_prime_dvd_GN_succ_not_dvd_GN`)。
   一方、全履歴に対する support の単調増大や、全履歴に対して新しい
   素数方向が毎回発生するという表現は今回の checked 反例により排除される。

この監査からは **Outcome B** が自然である。GN support 分離と単数冪の
積・交叉・CRT は有用な異なる層である。GN 側の recurrence だけで単数
power quotient が構成されるわけではなく、単数群の抽象 CRT だけで固定
整数基底の primitive divisor が生成されるわけでもない。共通に使われる
互いに素な指数を越える arithmetic bridge は別途必要である。
最終 A/B/C 判定は Phase 4 の群・商定理と合わせて
[report-002](report-002.md) に記録する。

## 実行記録

```text
cwd: lean/dk_math
lake build DkMath.NumberTheory.ZsigmondyCyclotomicNoLift
  DkMath.NumberTheory.Primitive.PrimitiveConservationKernel
  DkMath.NumberTheory.StructuralArithmetic.GNBridge
  DkMath.NumberTheory.PrimitiveSet.Basic
=> exit 0, Build completed successfully (8960 jobs).
=> existing warning: ZsigmondyCyclotomicResearch.lean:147 declaration uses sorry.

lake env lean docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/checks/PrimitivePrimeAudit002.lean
=> exit 0; five new regression theorems and named endpoint axiom audit pass.
=> existing research endpoints report sorryAx; safe existence/transport endpoints do not.
```

旧 research 宣言の監査結果は、新規 successor 定理の依存公理とは別に
記録している。
