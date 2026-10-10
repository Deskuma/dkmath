# Step037 — generic-prime native focused GTail receiver

2026-10-11。**COMPLETE / Outcome B**。Step037 で停止。
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`。
Base HEAD: `e338940c46b6eda8f9fbe1cbd02cb412ec59d582`。

任意の prime q に対し、二次根 t と非自明な seventh root r が供給されれば、
既存 C に実際の evPair:C→+*ZMod q と maximal/prime pairedKernel を構成した。
E/R の各 source contraction を型を保って証明し、q43 の eval43/M43 とも正確に一致した。
自然数 a,b,c,g の Q/T support と q-units から根を選ぶ nativeKernel は hEq を仮定しない。
明示的な条件付き focused_receiver は、既存 hEq-bound API から units・scalar depth・
bounded common-power lower bounds を供給する。任意項目の generic joint-source ideal sum も完成。

これは source variables を入力に取れる local algebra interface の完成である。
conditional adapter は新たな独立 FLT7 obstruction、global balance の逆導出、
exact common valuation、旧 signed carrier の再構成や descent ではない。

Source: DkMath/FLT/Seven/GTailFocusedGenericPrimeReceiver.lean。
Test: DkMathTest/FLT/Seven/GTailFocusedGenericPrimeReceiver.lean。
[Source/API inventory](source-inventory-037.md)、[field/frontier comparison](frontier-037.md)。
review036 は static source review。今回実行した focused builds と区別する。

## 各 gate の検証済み契約

| Gate | Input | Actual output | Boundary |
|---|---|---|---|
| supplied-root receiver | prime q、t²−t+1=0、r≠0、r⁷=1、r≠1 | unital evPair、maximal/prime kernel、両 triangles / contractions | root の存在は入力、q43 固有ではない |
| native Q/T | q∣a²+ab+b²、q∤b,c,g、q∣GTail | t=−a/b、r=(c+g)/c、nativeKernel と α/F0 image membership、両 residue0 | hEq / additive focus 不要 |
| native bounded squares | native inputs＋q≠3、q²∣Tail | iE(α²),iRF0∈J²、iEα·iRF0∈J³、iE(α²)·iRF0∈J⁴ | 一方向の下限、次の冪の除外なし |
| focused adapter | a,b>0、coprime、hEq、hfocus、q≠7、q∣Q/T | units と q≠3 を導出し上記 receiver / powers、既存 scalar depth と parity | hEq を消去した obstruction ではない |
| optional joint generation | 同じ supplied root pair | pairedKernel=map iE P_t⊔map iR K_r | 単一 pair の等式、generic full grid ではない |

Gate1 は Step034 と同じ実際の QA.re_mul/im_mul と ht の linear_combination による。
field 内の t を R 内の値として扱わない。R restriction の既存全射性から C の全射性を得て
ker_isMaximal_of_surjective を適用する。両 contraction は RingHom.comp の零条件の等式。
build01 でこの primary gate が成功した。

Gate2 は existing gtailSevenResidueRoot_polynomial、三つの Tail ratio guards を利用する。
E の α は source residue ideal theorem、R の F0 は unique_slot(0,0) を使い、
sixRootKernel の slot0 を seventhRootKernel に正規化した。
両 image の所属は同じ C の ideal を各 source へ comap してから証明する。
両 residue は0であるが、source images の equality は導かない。build02 成功後に Gate3 を実装。

Gate3 の units は focused_norm_depth_guards の出力から取り出す。
a,b positivity は既存 focused_norm_scalar_depth_readouts のために使う。
v_q(T)=2v_q(Q)、q²∣T、q⁴∣T↔q²∣Q、q³∣T↔q⁴∣T を同じ既存 theorem から回収する。
Even(v_q(T)) の witness は実際の v_q(Q)。この parity は既存 equality の帰結。
source E square は Step017 split-square、source R square は Step025 mem_square_iff による。
map_pow は source extension の平方に入り、包含を pow_le_pow_left' で common square に移す。
Ideal.mul_mem_mul と pow_add で mixed³/⁴。all-k transport API は追加していない。
build04 で全 conditional/bounded contracts が成功した。

任意の generic join は Step036 の座標分解を private coordinate_split(n,x) に限定して適用した。
x∈J のとき y=x.re+(t.val:R)x.im∈K_r、d=τ−(t.val:E)∈P_t。
x=iR(y)+iE(d)iR(x.im) の二項が各 extension に入るので reverse inclusion が得られる。
この exponent-one proof に map_pow は使わない。旧 q43 の grid / injectivity は再構築しない。
最終 production build07 と test08 が成功した。

## 数値・失敗 controls と59 examples

| Calibration | Checked result | What it does not establish |
|---|---|---|
| q43 (1166,1857,1858,1165) | source ratios37/11、nativeKernel=M43、両 images の所属、maximal、mixed support、両 images は不等 | Fermat equation / exact scalar balance は実際に false |
| q43 (5,8,9,4) | additive focus 13=13、coprime、source ratios37/11、同じ M43、両第一冪 endpoints | q²∣Tail と doubled scalar budget は false、F0∉K0² |
| q127 t20,r2 | 20²−20+1=0、2⁷=1、r≠0,1、actual C evaluation / maximal kernel / typed contractions / generator values | native Fermat tuple を構成していない |
| q7 | nonidentity seventh root は存在しない | supplied-root contract の前提を満たせない |
| q3 | 二次根があり得ても nonidentity seventh root は存在しない | repeated E root を R root と混同しない |
| q13 Gap-only (14,29,30,13) | focus、q∣Q、q∣gap、q∤Tail、nonidentity seventh root もない | native Tail branch を入力できない |

q127 の候補は 381=3·127、128=127+1 を独立に算出し、Lean decide で根の契約を確認した。
この例は arbitrary-prime receiver が q43 以外でも実際に instantiate できることを示す。
二つの q43 inputs は同じ kernel を選ぶが、scalar / source-square の追加契約は異なる。
小さい例の F0∉K0² を iRF0∉M43² に読み替える逆 transport は証明していない。
q43 の exact scalar balance failure は自然数式そのものを decide で確認した。
旧 Step035/036 の proper extensions / join と直接 E↔R no-hom も test で維持する。

## 全公開24宣言の正確な elaborated signatures

definition 4件、theorem 20件（private coordinate_split はこの数に含めない）。
以下は最終 test08 の全 #check 出力。section variable の自動 binder も含む実際の署名。
namespace / open は新 source/test の宣言に従う。

```lean
DkMath.FLT.Seven.GTailGenericPrimeReceiver.evPair {q : ℕ} [Fact (Nat.Prime q)] (t r : ZMod q) (ht : t ^ 2 - t + 1 = 0)
  (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) : Carrier →+* ZMod q
```

```lean
DkMath.FLT.Seven.GTailGenericPrimeReceiver.evPair_comp_eisenstein {q : ℕ} [Fact (Nat.Prime q)] (t r : ZMod q)
  (ht : t ^ 2 - t + 1 = 0) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) :
  (evPair t r ht hr0 hr7 hr1).comp fromEisenstein = eisensteinResidueRingHom t ht
```

```lean
DkMath.FLT.Seven.GTailGenericPrimeReceiver.evPair_comp_cyclotomic {q : ℕ} [Fact (Nat.Prime q)] (t r : ZMod q)
  (ht : t ^ 2 - t + 1 = 0) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) :
  (evPair t r ht hr0 hr7 hr1).comp fromCyclotomic = evalCyclotomicFromSeventhRoot r hr0 hr7 hr1
```

```lean
DkMath.FLT.Seven.GTailGenericPrimeReceiver.pairedKernel {q : ℕ} [Fact (Nat.Prime q)] (t r : ZMod q)
  (ht : t ^ 2 - t + 1 = 0) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) : Ideal Carrier
```

```lean
DkMath.FLT.Seven.GTailGenericPrimeReceiver.evPair_surjective {q : ℕ} [Fact (Nat.Prime q)] (t r : ZMod q)
  (ht : t ^ 2 - t + 1 = 0) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) :
  Function.Surjective ⇑(evPair t r ht hr0 hr7 hr1)
```

```lean
DkMath.FLT.Seven.GTailGenericPrimeReceiver.pairedKernel_isMaximal {q : ℕ} [Fact (Nat.Prime q)] (t r : ZMod q)
  (ht : t ^ 2 - t + 1 = 0) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) : (pairedKernel t r ht hr0 hr7 hr1).IsMaximal
```

```lean
DkMath.FLT.Seven.GTailGenericPrimeReceiver.pairedKernel_isPrime {q : ℕ} [Fact (Nat.Prime q)] (t r : ZMod q)
  (ht : t ^ 2 - t + 1 = 0) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) : (pairedKernel t r ht hr0 hr7 hr1).IsPrime
```

```lean
DkMath.FLT.Seven.GTailGenericPrimeReceiver.pairedKernel_comap_eisenstein {q : ℕ} [Fact (Nat.Prime q)] (t r : ZMod q)
  (ht : t ^ 2 - t + 1 = 0) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) :
  Ideal.comap fromEisenstein (pairedKernel t r ht hr0 hr7 hr1) = eisensteinResidueIdeal t ht
```

```lean
DkMath.FLT.Seven.GTailGenericPrimeReceiver.pairedKernel_comap_cyclotomic {q : ℕ} [Fact (Nat.Prime q)] (t r : ZMod q)
  (ht : t ^ 2 - t + 1 = 0) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) :
  Ideal.comap fromCyclotomic (pairedKernel t r ht hr0 hr7 hr1) = seventhRootKernel r hr0 hr7 hr1
```

```lean
DkMath.FLT.Seven.GTailGenericPrimeReceiver.pairedKernel_eq_sup {q : ℕ} [Fact (Nat.Prime q)] (t r : ZMod q)
  (ht : t ^ 2 - t + 1 = 0) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) :
  pairedKernel t r ht hr0 hr7 hr1 =
    Ideal.map fromEisenstein (eisensteinResidueIdeal t ht) ⊔ Ideal.map fromCyclotomic (seventhRootKernel r hr0 hr7 hr1)
```

```lean
DkMath.FLT.Seven.GTailGenericPrimeReceiver.evPair_43 : evPair 37 11 ⋯ ⋯ ⋯ ⋯ = eval43
```

```lean
DkMath.FLT.Seven.GTailGenericPrimeReceiver.pairedKernel_43 : pairedKernel 37 11 ⋯ ⋯ ⋯ ⋯ = M43
```

```lean
DkMath.FLT.Seven.GTailGenericPrimeReceiver.nativeEval {q : ℕ} [Fact (Nat.Prime q)] (a b c g : ℕ)
  (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hb : ¬q ∣ b) (hc : ¬q ∣ c) (hg : ¬q ∣ g) (hT : q ∣ GTail 7 1 g c) :
  Carrier →+* ZMod q
```

```lean
DkMath.FLT.Seven.GTailGenericPrimeReceiver.nativeKernel {q : ℕ} [Fact (Nat.Prime q)] (a b c g : ℕ)
  (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hb : ¬q ∣ b) (hc : ¬q ∣ c) (hg : ¬q ∣ g) (hT : q ∣ GTail 7 1 g c) : Ideal Carrier
```

```lean
DkMath.FLT.Seven.GTailGenericPrimeReceiver.nativeKernel_isMaximal {q : ℕ} [Fact (Nat.Prime q)] (a b c g : ℕ)
  (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hb : ¬q ∣ b) (hc : ¬q ∣ c) (hg : ¬q ∣ g) (hT : q ∣ GTail 7 1 g c) :
  (nativeKernel a b c g hQ hb hc hg hT).IsMaximal
```

```lean
DkMath.FLT.Seven.GTailGenericPrimeReceiver.nativeKernel_comap_eisenstein {q : ℕ} [Fact (Nat.Prime q)] (a b c g : ℕ)
  (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hb : ¬q ∣ b) (hc : ¬q ∣ c) (hg : ¬q ∣ g) (hT : q ∣ GTail 7 1 g c) :
  Ideal.comap fromEisenstein (nativeKernel a b c g hQ hb hc hg hT) =
    eisensteinResidueIdeal (gtailSevenResidueRoot q a b) ⋯
```

```lean
DkMath.FLT.Seven.GTailGenericPrimeReceiver.nativeKernel_comap_cyclotomic {q : ℕ} [Fact (Nat.Prime q)] (a b c g : ℕ)
  (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hb : ¬q ∣ b) (hc : ¬q ∣ c) (hg : ¬q ∣ g) (hT : q ∣ GTail 7 1 g c) :
  Ideal.comap fromCyclotomic (nativeKernel a b c g hQ hb hc hg hT) = seventhRootKernel (gtailSevenTailRatio q c g) ⋯ ⋯ ⋯
```

```lean
DkMath.FLT.Seven.GTailGenericPrimeReceiver.native_eisenstein_source_mem {q : ℕ} [Fact (Nat.Prime q)] (a b : ℕ)
  (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hb : ¬q ∣ b) :
  gtailSevenNormCoord a b ∈ eisensteinResidueIdeal (gtailSevenResidueRoot q a b) ⋯
```

```lean
DkMath.FLT.Seven.GTailGenericPrimeReceiver.native_factor_source_mem {q : ℕ} [Fact (Nat.Prime q)] (c g : ℕ) (hc : ¬q ∣ c)
  (hg : ¬q ∣ g) (hT : q ∣ GTail 7 1 g c) :
  gtailCyclotomicFactor c g 0 ∈ seventhRootKernel (gtailSevenTailRatio q c g) ⋯ ⋯ ⋯
```

```lean
DkMath.FLT.Seven.GTailGenericPrimeReceiver.native_eisenstein_mem {q : ℕ} [Fact (Nat.Prime q)] (a b c g : ℕ)
  (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hb : ¬q ∣ b) (hc : ¬q ∣ c) (hg : ¬q ∣ g) (hT : q ∣ GTail 7 1 g c) :
  fromEisenstein (gtailSevenNormCoord a b) ∈ nativeKernel a b c g hQ hb hc hg hT
```

```lean
DkMath.FLT.Seven.GTailGenericPrimeReceiver.native_factor_mem {q : ℕ} [Fact (Nat.Prime q)] (a b c g : ℕ)
  (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hb : ¬q ∣ b) (hc : ¬q ∣ c) (hg : ¬q ∣ g) (hT : q ∣ GTail 7 1 g c) :
  fromCyclotomic (gtailCyclotomicFactor c g 0) ∈ nativeKernel a b c g hQ hb hc hg hT
```

```lean
DkMath.FLT.Seven.GTailGenericPrimeReceiver.native_residue_zeros {q : ℕ} [Fact (Nat.Prime q)] (a b c g : ℕ)
  (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hb : ¬q ∣ b) (hc : ¬q ∣ c) (hg : ¬q ∣ g) (hT : q ∣ GTail 7 1 g c) :
  (nativeEval a b c g hQ hb hc hg hT) (fromEisenstein (gtailSevenNormCoord a b)) = 0 ∧
    (nativeEval a b c g hQ hb hc hg hT) (fromCyclotomic (gtailCyclotomicFactor c g 0)) = 0
```

```lean
DkMath.FLT.Seven.GTailGenericPrimeReceiver.native_square_support {q : ℕ} [Fact (Nat.Prime q)] (a b c g : ℕ)
  (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hb : ¬q ∣ b) (hc : ¬q ∣ c) (hg : ¬q ∣ g) (hT : q ∣ GTail 7 1 g c) (hq3 : q ≠ 3)
  (hT2 : q ^ 2 ∣ GTail 7 1 g c) :
  have J := nativeKernel a b c g hQ hb hc hg hT;
  fromEisenstein (gtailSevenNormCoord a b ^ 2) ∈ J ^ 2 ∧
    fromCyclotomic (gtailCyclotomicFactor c g 0) ∈ J ^ 2 ∧
      fromEisenstein (gtailSevenNormCoord a b) * fromCyclotomic (gtailCyclotomicFactor c g 0) ∈ J ^ 3 ∧
        fromEisenstein (gtailSevenNormCoord a b ^ 2) * fromCyclotomic (gtailCyclotomicFactor c g 0) ∈ J ^ 4
```

```lean
DkMath.FLT.Seven.GTailGenericPrimeReceiver.focused_receiver {q : ℕ} [Fact (Nat.Prime q)] (a b c g : ℕ) (ha : 0 < a)
  (hbpos : 0 < b) (hcop : a.Coprime b) (hEq : Fermat7Equation a b c) (hfocus : a + b = c + g) (hq7 : q ≠ 7)
  (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hT : q ∣ GTail 7 1 g c) :
  have hu := ⋯;
  have J := nativeKernel a b c g hQ ⋯ ⋯ ⋯ hT;
  J.IsMaximal ∧
    Ideal.comap fromEisenstein J = eisensteinResidueIdeal (gtailSevenResidueRoot q a b) ⋯ ∧
      Ideal.comap fromCyclotomic J = seventhRootKernel (gtailSevenTailRatio q c g) ⋯ ⋯ ⋯ ∧
        fromEisenstein (gtailSevenNormCoord a b) ∈ J ∧
          fromCyclotomic (gtailCyclotomicFactor c g 0) ∈ J ∧
            padicValNat q (GTail 7 1 g c) = 2 * padicValNat q (a ^ 2 + a * b + b ^ 2) ∧
              Even (padicValNat q (GTail 7 1 g c)) ∧
                q ^ 2 ∣ GTail 7 1 g c ∧
                  (q ^ 4 ∣ GTail 7 1 g c ↔ q ^ 2 ∣ a ^ 2 + a * b + b ^ 2) ∧
                    (q ^ 3 ∣ GTail 7 1 g c ↔ q ^ 4 ∣ GTail 7 1 g c) ∧
                      fromEisenstein (gtailSevenNormCoord a b ^ 2) ∈ J ^ 2 ∧
                        fromCyclotomic (gtailCyclotomicFactor c g 0) ∈ J ^ 2 ∧
                          fromEisenstein (gtailSevenNormCoord a b) * fromCyclotomic (gtailCyclotomicFactor c g 0) ∈
                              J ^ 3 ∧
                            fromEisenstein (gtailSevenNormCoord a b ^ 2) *
                                fromCyclotomic (gtailCyclotomicFactor c g 0) ∈
                              J ^ 4
```

## 全公開 #print axioms

最終 test08 の全24出力。全件が標準 foundations のみで非標準公理0。

```text
evPair : [propext, Classical.choice, Quot.sound]
evPair_comp_eisenstein : [propext, Classical.choice, Quot.sound]
evPair_comp_cyclotomic : [propext, Classical.choice, Quot.sound]
pairedKernel : [propext, Classical.choice, Quot.sound]
evPair_surjective : [propext, Classical.choice, Quot.sound]
pairedKernel_isMaximal : [propext, Classical.choice, Quot.sound]
pairedKernel_isPrime : [propext, Classical.choice, Quot.sound]
pairedKernel_comap_eisenstein : [propext, Classical.choice, Quot.sound]
pairedKernel_comap_cyclotomic : [propext, Classical.choice, Quot.sound]
pairedKernel_eq_sup : [propext, Classical.choice, Quot.sound]
evPair_43 : [propext, Classical.choice, Quot.sound]
pairedKernel_43 : [propext, Classical.choice, Quot.sound]
nativeEval : [propext, Classical.choice, Quot.sound]
nativeKernel : [propext, Classical.choice, Quot.sound]
nativeKernel_isMaximal : [propext, Classical.choice, Quot.sound]
nativeKernel_comap_eisenstein : [propext, Classical.choice, Quot.sound]
nativeKernel_comap_cyclotomic : [propext, Classical.choice, Quot.sound]
native_eisenstein_source_mem : [propext, Classical.choice, Quot.sound]
native_factor_source_mem : [propext, Classical.choice, Quot.sound]
native_eisenstein_mem : [propext, Classical.choice, Quot.sound]
native_factor_mem : [propext, Classical.choice, Quot.sound]
native_residue_zeros : [propext, Classical.choice, Quot.sound]
native_square_support : [propext, Classical.choice, Quot.sound]
focused_receiver : [propext, Classical.choice, Quot.sound]
```

## 実行した focused builds と失敗・修正

cwd=/home/deskuma/develop/lean/dkmath/lean/dk_math。
すべて逐次実行、process-local LEAN_NUM_THREADS=2 のみ。
ログの基点は `.lake/build/gtail-step037/`、警告数は warning: 行の数。

| Log | Exact command | Exit | Warnings | Seconds |
|---|---|---|---|---|
| 01-build.log | `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailFocusedGenericPrimeReceiver` | 0 | 0 | 15.18 |
| 02-build.log | `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailFocusedGenericPrimeReceiver` | 0 | 0 | 16.04 |
| 03-build.log | `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailFocusedGenericPrimeReceiver` | 1 | 0 | 17.9 |
| 04-build.log | `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailFocusedGenericPrimeReceiver` | 0 | 0 | 20.86 |
| 05-build.log | `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailFocusedGenericPrimeReceiver` | 1 | 0 | 21.18 |
| 06-build.log | `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailFocusedGenericPrimeReceiver` | 0 | 0 | 27.52 |
| 07-build.log | `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailFocusedGenericPrimeReceiver` | 0 | 0 | 17.96 |
| 08-build.log | `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailFocusedGenericPrimeReceiver` | 0 | 0 | 27.11 |
| 09-build.log | `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailEisensteinCyclotomicPrimeJoin` | 0 | 0 | 9.21 |
| 10-build.log | `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailEisensteinCyclotomicPrimeGrid` | 0 | 0 | 8.19 |

- 01: generic q の actual evPair / contractions / maximality と q43 compatibility が成功。
- 02: native source roots、typed source/image membership、residue zeros が成功。
- 03: conditional adapter の Even witness を underscore のままにしたため omega が
  witness metavariable を決定できず失敗。具体的な padicValNat q Q を witness として指定した。
  hypothesis や theorem の数学的意味は変更していない。
- 04: conditional receiver と bounded source-power/mixed support が成功、警告0。
- 05: test の local notation J43/J127 に `.IsMaximal` 等を続けると名前として解析される問題と、
  q127 generator test の triangle の ht を underscore から推論できない問題で失敗。
  `(J43).IsMaximal` 等と明示的な q127,t20,r2,by decide の certificates に修正。
- 06: q43/q127/除外 characteristics の57 examples が成功、警告0。
- 07: private split と optional generic join を追加した最終 production が成功、警告0。
- 08: 二つの generic/native join examples を追加した59 examples と全24 #check / axioms が成功、警告0。
- 09/10: Step036/035 source/test の選択した直接 regression commands が成功、警告0。
  既存 target は Lake の cached replay を含む。新 production07 / test08 は実際に Built された。

全 clean all-suite の実行結果としては扱わない。

## Lean 結果からの気づき・試した命題・実装提案

1. q43 特殊 API を変更せず、同じ coordinate law のまま symbolic prime q の receiver を構成できた。
   generic root pair と native source root selection を別の層にすると、field/root hypotheses と
   実際の source support を分けて確認できる。
2. q127 の実際の二つの roots と generator residues20/2 を検証できたため、generic declaration が
   q43 に戻っただけの theorem ではないことを実際のインスタンスで確かめられた。
3. 試した optional joint-generation theorem は任意の一つの root pair でも成立した。
   t.val という整数 lift で coordinate split を行い、全 kernel element の二項所属を得る。
   一つの source extension=M とはせず、generic grid や root injectivity も再実装しない。
4. nativeKernel の存在は additive focus すら不要だった。実際の Q/T と denominators の units が
   両 residue0 を供給する。しかしこれらの local data から exact Fermat balance は得られない。
5. 二つの q43 tuples が同じ M43 を選びつつ scalar budget と F0 の source-square support を
   区別することを Lean で確認した。旧 small tuple が additive-focused である修正も保った。
   source の K² nonmembership を C の M² nonmembership に移す逆向きは試していない。
6. conditional adapter に q-unit hypotheses を追加する必要はなかった。
   focused_norm_depth_guards が b,c,g units と q≠3 を既存 hEq から提供し、positivity は
   scalar depth readouts のためにのみ使われる。parity は doubled budget の新しい証拠ではなくその帰結。
7. 今後の補助命題候補として、native inputs の下で両 images の不等式を一般化することは考えられる。
   E image の C.im は cast b、R image の C.im は0で、R residue と q∤b から検出できる。
   今回は q43 の既存不等式を regression した。generic 不等式そのものは新 API として実装していない。
   それを実装しても local compatibility の範囲であり、独立 FLT obstruction とは数えない。
8. 次の研究 review は、now-generic source pairing が original hypothetical primitive solution から
   既存 scalar valuation / root order / mixed support を超える independent global restriction を
   供給するかを問う必要がある。packet の exact field と source-linked global relation を
   照合する表は検討候補だが、local M の冪を増やすだけでは reconstruction の不足は埋まらない。

## 旧 signed packet / descent provider の正確な境界

read-only で実際の RamifiedSignedRootDepthPacket を確認した。
balanced axis split、signedLeftRoot / signedRightRoot と旧 normPacket roots への一致、
IsCoprime、gapRoot / quotientRoot、signedGap=7⁴*gapRoot、signedQuotient=7*quotientRoot、
両 root の7-unit と normalizedEquation を要求する。今回これらの field は供給していない。

実際の AwayDescentClosureProvider x y z p は nextX/Y/Z、新しい CounterexamplePack、
新しい AwayValuationTransferPacket と
`carrier_match : nextRoute.carrier = Int.natAbs p.normal.root.snd` を要求する。
新しい pairedKernel/nativeKernel:Ideal C と source memberships はこれらの field を inhabit しない。
natural F0 と old signed oriented carrier の一致や、より小さな primitive solution も得ていない。
packet/provider の非存在を証明したという意味でもない。

## 最終監査

- 公開宣言24件（definitions4 / theorems20）の実際の `#check` / `#print axioms` を確認した。
  全件の公理は `propext, Classical.choice, Quot.sound` のみ。新 test の example は59件。
- 新 source/test のコメント・文字列を除く forbidden-token scan は
  `sorry / admit / axiom / unsafe / native_decide / set_option / False.elim` 全件0。
  License header、import 後の file print、書式の検査も成功した。
- production closure8952 modules、test closure8953 modules、local union173 vertices の DAG は cycle0。
  neutral GTailSevenRealTraceResidue closure1907 modules（local20）には FLT0。
  到達する neutral Lib owners27件の独立 closure でも FLT reachability0。
- Step036 と比較した production import closure の追加は新 owner
  `DkMath.FLT.Seven.GTailFocusedGenericPrimeReceiver` 一つ、削除0。
  新 source の direct import は Step036 owner 一つのみ。
  DescentClosureAudit / SevenRamifiedSignedRootDepth は既存の推移的依存として残る。
  今回これらへの新しい direct import や packet API の proof-body reference は追加していない。
- Seven facade、SevenRamifiedFusionGlobalOrientedPrimeFactorization、
  Kummer.CyclotomicPrincipalization、CyclotomicQRTraceOneBridge、
  SevenRamifiedFusionCyclotomicDegreeSixDomain、
  SevenRamifiedFusionOrientedCarrierValuationOwnership は今回の closure に含まれない。
- 最終 source07 / test08 と regression09 / 10 はすべて終了コード0、警告0。
  詳細は `.lake/build/gtail-step037/` の runs.json、audit.json、imports.json、
  import-impact.json と個別ログに保存した。
- ROADMAP は既存 bytes を保った追記のみ。既存 tracked Lean / 過去レポートへの変更0。
  新規5ファイルと ROADMAP 追記の空白検査、および `git diff --check` は成功した。
  workspace-audit.json に対象と検査結果を保存した。

Outcome B として Step037 を完了し、ここで停止する。generic prime の実際の receiver、
source-linked membership、conditional doubled budget、bounded mixed support は得られたが、
独立の global obstruction、signed reconstruction、next primitive tuple、FLT7 descent は得ていない。
