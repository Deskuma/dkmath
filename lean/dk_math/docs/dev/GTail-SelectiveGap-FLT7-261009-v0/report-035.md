# Step035 — q43 の二行六列の素イデアル grid

2026-10-11。**COMPLETE / Outcome B**。Step035 で停止。
Base HEAD: `d0773dad48577653ec0604c363b1447a1d4d4463`。

既存 C と二つの単射を変更せず、十二個の互いに異なる極大・素イデアル M(e,j) を証明した。
E への contraction は行の P_t、R への contraction は列の K_j で、別々の型を保つ。
evGrid 0 0=eval43 と M 0 0=M43 も正確に一致した。
任意項目の二つの strict ideal extensions と実際の α/F0 の行・列所属も完成した。
これは有限体での local branching であり、全 spectrum や FLT7 descent は主張しない。

## 実装と証明の構造

新 source は DkMath/FLT/Seven/GTailEisensteinCyclotomicPrimeGrid.lean、
新 test は DkMathTest/FLT/Seven/GTailEisensteinCyclotomicPrimeGrid.lean。
[参照した型と API](source-inventory-035.md)、[残る境界](frontier-035.md) を別記した。

1. 行は ![37,7]。列は既存 sixSlotRoot 11 j を使い、order-seven の単射性を再利用した。
   六値 [11,35,41,21,16,4] の列挙は test のみ。37 と 7 は共役二次根である。
2. evR43(j) は既存の actual R→ZMod43。evGrid(e,j) x は
   evR43(j)(x.re)+t_e·evR43(j)(x.im)。乗法は実際の re_mul/im_mul と二次根の関係で検証。
   両 source の制限を bundled RingHom の等式として証明し、生成元・整数の像も得た。
3. M=ker evGrid。R の既存全射性から C の評価も全射となり、kernel は極大・素。
   E/R contraction の所属条件を両可換三角形で書き換えた。
   行を固定すれば E contraction は列に依存せず、列を固定すれば R contraction は行に依存しない。
4. 単射性は R contraction と sixRootKernel_ne で列を区別する。
   行は実際の C 元 w=ιEτ−t_e.val を使用する。w は元の kernel に入り、kernel が等しければ
   他方でも評価零になるため二次根が一致する。異なる hom だけを根拠に kernel を区別しない。
5. Ideal.map_le_iff_le_comap で source ideal の拡大の包含を得た。
   K0 の拡大は M10 にも入るが ω−37 は M00 に入り M10 に入らない。
   P37 の拡大は M01 にも入るが ιRζ−11 は M00 に入り M01 に入らない。
   よって両方とも M00 より真に小さい。
6. α=gtailSevenNormCoord 1166 1857 の E 所属は二つの根で実際に計算した。
   F0=gtailCyclotomicFactor 1858 1165 0 の R 所属は既存 unique_slot を再利用した。
   任意 e,j について α の像の所属 ↔ e=0、F0 の像の所属 ↔ j=0 を証明した。

| Address | s=11 | s=35 | s=41 | s=21 | s=16 | s=4 |
|---|---|---|---|---|---|---|
| t=37 | α,F0 | α | α | α | α | α |
| t=7 | F0 | neither | neither | neither | neither | neither |

この表は二つの実際の像の所属だけを示す。両像の非等式と
¬ Fermat7Equation 1166 1857 1858 も Lean example で検証した。
source の平方支持は Step034 regression で維持するが C の深さの同一視には使わない。

## 全公開32宣言の正確な署名

Namespace: DkMath.FLT.Seven.GTailPrimeGrid。
open TraceOneQuadratic / Lib.NumberTheory / GTailCommonReceiver。
local Fact (Nat.Prime 43) は by decide で証明。definition 5件、theorem 27件。
以下は実際の source から抽出した署名（定義本体・証明は source を参照）。

```lean
def eisenstein43Root : Fin 2 → ZMod 43
```

```lean
def seven43Root (j : Fin 6) : ZMod 43
```

```lean
theorem eisenstein43Root_relation (e : Fin 2) :
    eisenstein43Root e ^ 2 - eisenstein43Root e + 1 = 0
```

```lean
theorem eisenstein43Root_injective : Function.Injective eisenstein43Root
```

```lean
theorem seven43Root_pow_seven (j : Fin 6) : seven43Root j ^ 7 = 1
```

```lean
theorem seven43Root_ne_zero (j : Fin 6) : seven43Root j ≠ 0
```

```lean
theorem seven43Root_ne_one (j : Fin 6) : seven43Root j ≠ 1
```

```lean
theorem seven43Root_injective : Function.Injective seven43Root
```

```lean
def evR43 (j : Fin 6) : SevenCyclotomicDegreeSixInt.Ring →+* ZMod 43
```

```lean
def evGrid (e : Fin 2) (j : Fin 6) : Carrier →+* ZMod 43
```

```lean
theorem evGrid_comp_cyclotomic (e : Fin 2) (j : Fin 6) :
    (evGrid e j).comp fromCyclotomic = evR43 j
```

```lean
theorem evGrid_comp_eisenstein (e : Fin 2) (j : Fin 6) :
    (evGrid e j).comp fromEisenstein =
      eisensteinResidueRingHom (eisenstein43Root e) (eisenstein43Root_relation e)
```

```lean
theorem evGrid_tau (e : Fin 2) (j : Fin 6) :
    evGrid e j (fromEisenstein (tau (-1))) = eisenstein43Root e
```

```lean
theorem evGrid_zeta (e : Fin 2) (j : Fin 6) :
    evGrid e j (fromCyclotomic SevenCyclotomicDegreeSixInt.zeta) = seven43Root j
```

```lean
theorem evGrid_scalar (e : Fin 2) (j : Fin 6) (n : ℤ) :
    evGrid e j (fromEisenstein (n : TraceOneInt (-1))) = (n : ZMod 43) ∧
    evGrid e j (fromCyclotomic (n : SevenCyclotomicDegreeSixInt.Ring)) = (n : ZMod 43)
```

```lean
def M (e : Fin 2) (j : Fin 6) : Ideal Carrier
```

```lean
theorem evGrid_surjective (e : Fin 2) (j : Fin 6) : Function.Surjective (evGrid e j)
```

```lean
theorem M_isMaximal (e : Fin 2) (j : Fin 6) : (M e j).IsMaximal
```

```lean
theorem M_isPrime (e : Fin 2) (j : Fin 6) : (M e j).IsPrime
```

```lean
theorem M_comap_eisenstein (e : Fin 2) (j : Fin 6) :
    Ideal.comap fromEisenstein (M e j) =
      eisensteinResidueIdeal (eisenstein43Root e) (eisenstein43Root_relation e)
```

```lean
theorem M_comap_cyclotomic (e : Fin 2) (j : Fin 6) :
    Ideal.comap fromCyclotomic (M e j) =
      sixRootKernel (11 : ZMod 43) (by decide) (by decide) (by decide) j
```

```lean
theorem evGrid_zero_zero : evGrid 0 0 = eval43
```

```lean
theorem M_zero_zero : M 0 0 = M43
```

```lean
theorem M_comap_eisenstein_column (e : Fin 2) (j k : Fin 6) :
    Ideal.comap fromEisenstein (M e j) = Ideal.comap fromEisenstein (M e k)
```

```lean
theorem M_comap_cyclotomic_row (e f : Fin 2) (j : Fin 6) :
    Ideal.comap fromCyclotomic (M e j) = Ideal.comap fromCyclotomic (M f j)
```

```lean
theorem M_injective : Function.Injective (fun x : Fin 2 × Fin 6 => M x.1 x.2)
```

```lean
theorem map_eisenstein_le (e : Fin 2) (j : Fin 6) :
    Ideal.map fromEisenstein
      (eisensteinResidueIdeal (eisenstein43Root e) (eisenstein43Root_relation e)) ≤ M e j
```

```lean
theorem map_cyclotomic_le (e : Fin 2) (j : Fin 6) :
    Ideal.map fromCyclotomic
      (sixRootKernel (11 : ZMod 43) (by decide) (by decide) (by decide) j) ≤ M e j
```

```lean
theorem map_cyclotomic_lt_zero_zero :
    Ideal.map fromCyclotomic
      (sixRootKernel (11 : ZMod 43) (by decide) (by decide) (by decide) 0) < M 0 0
```

```lean
theorem map_eisenstein_lt_zero_zero :
    Ideal.map fromEisenstein (eisensteinResidueIdeal (37 : ZMod 43) (by decide)) < M 0 0
```

```lean
theorem normCoord_mem_iff (e : Fin 2) (j : Fin 6) :
    fromEisenstein (gtailSevenNormCoord 1166 1857) ∈ M e j ↔ e = 0
```

```lean
theorem factor_mem_iff (e : Fin 2) (j : Fin 6) :
    fromCyclotomic (gtailCyclotomicFactor 1858 1165 0) ∈ M e j ↔ j = 0
```

## 全公開宣言の #print axioms

最終 test の 09-build.log の実際の出力を照合した。全32件が含まれ、
propext / Classical.choice / Quot.sound 以外の公理はない。

```text
eisenstein43Root : [propext, Classical.choice, Quot.sound]
seven43Root : [propext, Classical.choice, Quot.sound]
eisenstein43Root_relation : [propext, Classical.choice, Quot.sound]
eisenstein43Root_injective : [propext, Classical.choice, Quot.sound]
seven43Root_pow_seven : [propext, Classical.choice, Quot.sound]
seven43Root_ne_zero : [propext, Classical.choice, Quot.sound]
seven43Root_ne_one : [propext, Classical.choice, Quot.sound]
seven43Root_injective : [propext, Classical.choice, Quot.sound]
evR43 : [propext, Classical.choice, Quot.sound]
evGrid : [propext, Classical.choice, Quot.sound]
evGrid_comp_cyclotomic : [propext, Classical.choice, Quot.sound]
evGrid_comp_eisenstein : [propext, Classical.choice, Quot.sound]
evGrid_tau : [propext, Classical.choice, Quot.sound]
evGrid_zeta : [propext, Classical.choice, Quot.sound]
evGrid_scalar : [propext, Classical.choice, Quot.sound]
M : [propext, Classical.choice, Quot.sound]
evGrid_surjective : [propext, Classical.choice, Quot.sound]
M_isMaximal : [propext, Classical.choice, Quot.sound]
M_isPrime : [propext, Classical.choice, Quot.sound]
M_comap_eisenstein : [propext, Classical.choice, Quot.sound]
M_comap_cyclotomic : [propext, Classical.choice, Quot.sound]
evGrid_zero_zero : [propext, Classical.choice, Quot.sound]
M_zero_zero : [propext, Classical.choice, Quot.sound]
M_comap_eisenstein_column : [propext, Classical.choice, Quot.sound]
M_comap_cyclotomic_row : [propext, Classical.choice, Quot.sound]
M_injective : [propext, Classical.choice, Quot.sound]
map_eisenstein_le : [propext, Classical.choice, Quot.sound]
map_cyclotomic_le : [propext, Classical.choice, Quot.sound]
map_cyclotomic_lt_zero_zero : [propext, Classical.choice, Quot.sound]
map_eisenstein_lt_zero_zero : [propext, Classical.choice, Quot.sound]
normCoord_mem_iff : [propext, Classical.choice, Quot.sound]
factor_mem_iff : [propext, Classical.choice, Quot.sound]
```

## 段階的 focused build の記録

すべて cwd=/home/deskuma/develop/lean/dkmath/lean/dk_math、逐次実行。
プロセス局所の LEAN_NUM_THREADS=2 のみ。警告数は各ログの `warning:` 行数。
ログの共通基点は `.lake/build/gtail-step035/`。

| Log | Exact command | Exit | Warnings | Seconds |
|---|---|---|---|---|
| 01-build.log | `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailEisensteinCyclotomicPrimeGrid` | 0 | 2 | 15.0 |
| 02-build.log | `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailEisensteinCyclotomicPrimeGrid` | 0 | 0 | 15.21 |
| 03-build.log | `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailEisensteinCyclotomicPrimeGrid` | 1 | 0 | 17.58 |
| 04-build.log | `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailEisensteinCyclotomicPrimeGrid` | 0 | 0 | 17.45 |
| 05-build.log | `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailEisensteinCyclotomicPrimeGrid` | 1 | 0 | 17.55 |
| 06-build.log | `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailEisensteinCyclotomicPrimeGrid` | 0 | 0 | 17.58 |
| 07-build.log | `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailEisensteinCyclotomicPrimeGrid` | 0 | 0 | 16.13 |
| 08-build.log | `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailEisensteinCyclotomicPrimeGrid` | 0 | 0 | 18.45 |
| 09-build.log | `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailEisensteinCyclotomicPrimeGrid` | 0 | 0 | 15.91 |
| 10-build.log | `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailEisensteinCyclotomicCommonReceiver` | 0 | 0 | 8.69 |
| 11-build.log | `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailEisensteinCyclotomicNoDirectHom` | 0 | 0 | 8.53 |
| 11-build.log | `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailEisensteinCyclotomicNoDirectHom` | 0 | 0 | 8.53 |

- 01: Gate1 の RingHom と両制限が成功。二根の単射証明の first に実行されない
  fallback tactic があり二つの linter warning。不要な枝だけを除去した。
- 02: Gate2 の全射性・極大性・両 contraction・M00/M43 一致が成功、警告0。
- 03: Gate3 の所属の equality transport で `h ▸ hw` が lambda の application を
  正規化できず失敗。`change M x.1 x.2 = M y.1 y.2 at h` と rw に修正。
- 04: 全十二点の injectivity が成功、警告0。この成功後に optional gate へ進んだ。
- 05: optional proof の数値リテラルの map、有限剰余の最終判定、inverse-slot 0 の
  vector evaluation の正規化が不足して失敗。map_ofNat、decide、
  seven43Root 1=35、sixInverseSlot 0=0 の明示的な事実で局所修正。
- 06: 両 strict extensions と任意 e,j の row/column incidence が成功、警告0。
- 07: 全30 examples と全32公理チェックが成功、警告0。
- 08/09: 公開 theorem の docstring と module scope コメントを整えた最終 source/test。
  両方成功、警告0。MIT header と import 後の file print を維持。
- 10: Step034 source/test の既存 regression が成功、警告0。
- 11: Step033 source/test の既存 no-direct-hom regression が成功、警告0。

ビルド・監査の範囲は新 owner と test、指定の既存 regression。
全 clean build や全 suite の結果としては扱わない。

## Lean 結果からの気づき・試した命題・提案

1. 既存 M43 は一つの address の特殊例だった。任意の行・列の可換三角形を
   実装すると、source contraction の独立性と十二点の区別を同じ API で扱えた。
2. 行の単射性には単なる異なる hom の提示では足りない。今回の w=ιEτ−t_e.val は
   実際の member であり、別の評価で nonmember となるため kernel の違いを証明できた。
3. strict extension の二つの命題を試し、どちらも証明できた。
   source prime を一つ指定しても、他方の独立した生成元の根は決まらないことが具体的に見える。
4. α の実座標は ⟨1166,1857⟩。t37 の評価は0、t7 の評価は18である。
   これを利用して全六列にわたる第一行の所属を確認した。
   F0 は既存の inverse-slot theorem によって全二行にわたる第一列を選ぶ。
5. 両方の所属の交点は (0,0) と唯一に定まるが、両像は C で等しくない。
   non-Fermat tuple のまま成立するので、交点の唯一性を Fermat obstruction と呼べない。
6. instruction035 の map/powers の注意は数学的に補正が必要だった。
   Mathlib の Ideal.map_pow は `map f (I^n)=(map f I)^n` を証明している。
   誤った推論は右辺を M00^n に置き換えることであり、今回 n=1 の strictness が
   その同一視を否定した。文書の注意を map_pow 自体の否定として採用していない。
7. 今後の実装候補は、source-linked な両 address を非循環的に入力した場合の
   grid 内の唯一の受け入れ先を契約として整理すること。ただし元の focused Fermat7 data
   がその両入力を供給するかは別問題。今回の数値例はその供給を証明しない。
   新しい field/domain/rank、全 spectrum、signed packet、primitive provider、away descent、
   FLT7 closure は追加しない。Step035 の完了で停止する。

## 最終監査と変更範囲

- 30 examples、全32公開宣言の公理出力を照合。非標準公理0。
- 新 source/test のコメント・文字列を除いた forbidden token scan は
  sorry / admit / axiom / unsafe / native_decide / set_option / False.elim すべて0。
- source/test とも MIT2026 header、import 後の file print、二空白 indentation を維持。
  最終 source08 / test09 と既存 regression10 /11 の warning は0。
- production direct import は旧 Step034 の一つ、test direct import は新 owner の一つ。
  production closure は8950 modules / local170、test は8951 / local171。
  local union171 vertices の DAG cycle0。
- neutral GTailSevenRealTraceResidue closure は1907 / local20、FLT到達0。
  production closure 内の全27 Lib owners の個別到達を調べ、neutral→FLT は0。
- FLT.Seven facade、global oriented factorization、CyclotomicPrincipalization、
  CyclotomicQRTraceOneBridge、degree-six domain certificate、valuation ownership の
  各除外 owner は新 import closure にない。既存の他の carrier modules は既存 closure として維持。
- git diff --check、追加ファイルと ROADMAP 追加部分の whitespace / final newline が成功。
  ROADMAP の旧本文は HEAD bytes を prefix として保ち、歴史的な Markdown hard break も保持。
  旧 source、facade、review/report/inventory/frontier、provider は変更していない。

監査証拠: `.lake/build/gtail-step035/{runs.json,imports.json,audit.json,workspace-audit.json}`。
変更は新 source/test、inventory/report/frontier035、ROADMAP の Step035 追記のみ。
