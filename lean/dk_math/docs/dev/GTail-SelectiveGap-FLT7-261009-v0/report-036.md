# Step036 — paired-source prime join と bounded mixed-power support

2026-10-11。**COMPLETE / Outcome B**。Step036 で停止。
Base HEAD: `6c4659126d9ba8fb3ebe42f1490019ffea6b68a9`。

既存の C と q43 grid をそのまま使い、全 e:Fin 2、j:Fin 6 について
**M(e,j)=A(e)⊔B(j)** を証明した。A は E の source prime の拡大、B は R の source prime の拡大。
個別の拡大の strictness と、共同生成の等式を同時に保つ構造定理である。
任意項目の source powers 0,1,2 の一方向の所属 transport と、実際の二つの混合積の
M00³ / M00⁴ 所属も検証できた。全 spectrum や正確な付値・FLT7 descent の主張は含まない。

新 owner は DkMath/FLT/Seven/GTailEisensteinCyclotomicPrimeJoin.lean、
新 test は DkMathTest/FLT/Seven/GTailEisensteinCyclotomicPrimeJoin.lean。
[型と API inventory](source-inventory-036.md)、[frontier](frontier-036.md) を別記した。
Step035 review は static source review であり、今回の実行した Lean build とは区別する。

## 各 compile gate の実装

Gate1 は n_e=t_e.val:ℕ、d_e=τ−(n_e:E)、y_e(x)=x.re+(n_e:R)x.im と置く。
すべての x:C で x=iR(y_e(x))+iE(d_e)iR(x.im) が成立する。
まず iE(d_e)=ω−(n_e:C) を map_sub / map_natCast と iEτ=ω で書き換え、
QuadraticAlgebra.ext で二座標を比較した。simp only で自然数 cast の座標則を保持する。
E の residue map で d_e∈P_e を示し、x∈M のときだけ evR43(y_e(x))=evGrid(x)=0 から
y_e(x)∈K_j を得た。build03 が成功してから Gate2 を実装した。

Gate2 は A(e)=map iE P_e、B(j)=map iR K_j を定義する。
既存の二つの包含から A⊔B≤M。逆向きは上記の座標分解と
Ideal.mem_map_of_mem、ideal.mul_mem_right、add_mem を使う。
右辺の最初の項は B に、後の積は A に属するため、和は A⊔B に入る。
build05 で M=A⊔B と M43=A0⊔B0 が成功。ここでは Ideal.map_pow を使わない。

Gate3 の build06 は strict extension、joint sum の十二点の単射性と極大性、
元の typed contractions と両 triangles、M00=M43、α/F0 の直交する所属、
両像の非等式と non-Fermat tuple、直接 E↔R map の非存在を回帰した。
A0<M00 と B0<M00 は、M00=A0⊔B0 と矛盾しない。

Gate4 は n:Fin 3、すなわち n.val=0,1,2 に限定した source power API。
Ideal.map_pow の正しい等式で source power から A^n または B^n の所属を得る。
次に pow_le_pow_left' と既存の A≤M / B≤M で M^n に移す。逆向きはない。
新 source の最終 build07 と test の最終 build09 が成功した。

## 実際の source support と mixed C element

α=gtailSevenNormCoord 1166 1857:E、F0=gtailCyclotomicFactor 1858 1165 0:R。
E 側の α∈P37 は既存 GTailSevenResidueIdeal、α²∈P37² は Step017 の
split_square_address を実際の root37 に正規化して使用した。
R 側の F0∈K0² は Step025 の mem_square_iff と root11 / inverse-slot0 による。
source 支持の式は元の E/R 型のまま先に証明してから transport する。

| Checked statement in C | Route | Meaning |
|---|---|---|
| iEα∈M00 | P37 の第一冪を transport | 少なくとも第一冪 |
| iE(α²)∈M00² | P37² を transport | 少なくとも第二冪 |
| iRF0∈M00² | K0² を transport | 少なくとも第二冪 |
| iEα·iRF0∈M00³ | Ideal.mul_mem_mul と 1+2=3 | mixed-product lower bound |
| iE(α²)·iRF0∈M00⁴ | Ideal.mul_mem_mul と 2+2=4 | mixed-product lower bound |

次の冪からの除外や正確な M-adic exponent は証明していない。
M²=A²⊔B² としたり、source 深さの equality を仮定したりしていない。
全34 examples はこれらに加え任意行の coordinate split、第二行の stress test と
全十二点の join / source restrictions の regression を含む。
数値組は ¬ Fermat7Equation 1166 1857 1858 のまま。両像も C で異なる。

## 全公開15宣言の正確な署名

Namespace DkMath.FLT.Seven.GTailPrimeJoin。
open TraceOneQuadratic / Lib.NumberTheory / GTailCommonReceiver / GTailPrimeGrid。
local Fact (Nat.Prime 43) は by decide で証明。definition 4件、theorem 11件。
以下は actual source から抽出。定義本体・証明は新 owner を参照。

```lean
def rowRemainder (e : Fin 2) (x : Carrier) : SevenCyclotomicDegreeSixInt.Ring
```

```lean
def rowDifference (e : Fin 2) : TraceOneInt (-1)
```

```lean
theorem coordinate_decomposition (e : Fin 2) (x : Carrier) :
    x = fromCyclotomic (rowRemainder e x) +
      fromEisenstein (rowDifference e) * fromCyclotomic x.im
```

```lean
theorem rowDifference_mem (e : Fin 2) :
    rowDifference e ∈ eisensteinResidueIdeal (eisenstein43Root e) (eisenstein43Root_relation e)
```

```lean
theorem rowRemainder_mem (e : Fin 2) (j : Fin 6) (x : Carrier) (hx : x ∈ M e j) :
    rowRemainder e x ∈ sixRootKernel (11 : ZMod 43) (by decide) (by decide) (by decide) j
```

```lean
def A (e : Fin 2) : Ideal Carrier
```

```lean
def B (j : Fin 6) : Ideal Carrier
```

```lean
theorem sup_le_M (e : Fin 2) (j : Fin 6) : A e ⊔ B j ≤ M e j
```

```lean
theorem M_le_sup (e : Fin 2) (j : Fin 6) : M e j ≤ A e ⊔ B j
```

```lean
theorem M_eq_map_eisenstein_sup_map_cyclotomic (e : Fin 2) (j : Fin 6) :
    M e j = A e ⊔ B j
```

```lean
theorem M43_eq_sup : M43 = A 0 ⊔ B 0
```

```lean
theorem eisenstein_mem_A_pow (e : Fin 2) (n : Fin 3) (z : TraceOneInt (-1))
    (hz : z ∈ eisensteinResidueIdeal (eisenstein43Root e) (eisenstein43Root_relation e) ^ n.val) :
    fromEisenstein z ∈ A e ^ n.val
```

```lean
theorem eisenstein_mem_M_pow (e : Fin 2) (j : Fin 6) (n : Fin 3) (z : TraceOneInt (-1))
    (hz : z ∈ eisensteinResidueIdeal (eisenstein43Root e) (eisenstein43Root_relation e) ^ n.val) :
    fromEisenstein z ∈ M e j ^ n.val
```

```lean
theorem cyclotomic_mem_B_pow (j : Fin 6) (n : Fin 3) (u : SevenCyclotomicDegreeSixInt.Ring)
    (hu : u ∈ sixRootKernel (11 : ZMod 43) (by decide) (by decide) (by decide) j ^ n.val) :
    fromCyclotomic u ∈ B j ^ n.val
```

```lean
theorem cyclotomic_mem_M_pow (e : Fin 2) (j : Fin 6) (n : Fin 3)
    (u : SevenCyclotomicDegreeSixInt.Ring)
    (hu : u ∈ sixRootKernel (11 : ZMod 43) (by decide) (by decide) (by decide) j ^ n.val) :
    fromCyclotomic u ∈ M e j ^ n.val
```

## 全公開宣言の #print axioms

最終 test09 の実際の全15出力を照合。非標準公理0。

```text
rowRemainder : [propext, Classical.choice, Quot.sound]
rowDifference : [propext, Classical.choice, Quot.sound]
coordinate_decomposition : [propext, Classical.choice, Quot.sound]
rowDifference_mem : [propext, Classical.choice, Quot.sound]
rowRemainder_mem : [propext, Classical.choice, Quot.sound]
A : [propext, Classical.choice, Quot.sound]
B : [propext, Classical.choice, Quot.sound]
sup_le_M : [propext, Classical.choice, Quot.sound]
M_le_sup : [propext, Classical.choice, Quot.sound]
M_eq_map_eisenstein_sup_map_cyclotomic : [propext, Classical.choice, Quot.sound]
M43_eq_sup : [propext, Classical.choice, Quot.sound]
eisenstein_mem_A_pow : [propext, Classical.choice, Quot.sound]
eisenstein_mem_M_pow : [propext, Classical.choice, Quot.sound]
cyclotomic_mem_B_pow : [propext, Classical.choice, Quot.sound]
cyclotomic_mem_M_pow : [propext, Classical.choice, Quot.sound]
```

## 実行した focused build と失敗・修正

cwd は /home/deskuma/develop/lean/dkmath/lean/dk_math。
すべて逐次実行、process-local LEAN_NUM_THREADS=2 のみ。
ログは `.lake/build/gtail-step036/`。警告数は各ログの warning: 行数。

| Log | Exact command | Exit | Warnings | Seconds |
|---|---|---|---|---|
| 01-build.log | `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailEisensteinCyclotomicPrimeJoin` | 1 | 1 | 15.83 |
| 02-build.log | `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailEisensteinCyclotomicPrimeJoin` | 1 | 0 | 16.13 |
| 03-build.log | `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailEisensteinCyclotomicPrimeJoin` | 0 | 0 | 14.53 |
| 04-build.log | `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailEisensteinCyclotomicPrimeJoin` | 1 | 0 | 14.24 |
| 05-build.log | `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailEisensteinCyclotomicPrimeJoin` | 0 | 0 | 14.88 |
| 06-build.log | `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailEisensteinCyclotomicPrimeJoin` | 0 | 0 | 17.43 |
| 07-build.log | `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailEisensteinCyclotomicPrimeJoin` | 0 | 0 | 15.12 |
| 08-build.log | `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailEisensteinCyclotomicPrimeJoin` | 1 | 0 | 16.22 |
| 09-build.log | `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailEisensteinCyclotomicPrimeJoin` | 0 | 0 | 17.79 |
| 10-build.log | `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailEisensteinCyclotomicPrimeGrid` | 0 | 0 | 8.71 |
| 11-build.log | `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailEisensteinCyclotomicCommonReceiver` | 0 | 0 | 8.01 |

- 01: broad simp で n_e.val の natural cast が ZMod.cast 表現に変わり、
  fromEisenstein の map_natCast が適用されない座標 goal が残った。
  unused simp argument warning も1件。型や二次関係の変更はしていない。
- 02: iE(d_e)=ω−(n_e:C) を先に示したが、broad simp が C の cast の projection を
  ZMod.cast の projection に変えたため失敗。残った実際の re goal は
  `x.re = x.re + t.cast*x.im - x.im*t.cast.re`、im goal は
  `x.im = -(t.cast.im*x.im)+x.im`。これらを ring だけでは閉じられない。
- 03: simp only と re_natCast/im_natCast を使って lift の座標を保ち、Gate1 成功、警告0。
- 04: joint-sum proof で le_sup_right / le_sup_left は一般 lattice の inequality のまま
  elaboration され、membership を受け取る関数と認識されず失敗。
  `show B j ≤ A e ⊔ B j from le_sup_right` 等で Ideal C の包含の型を明示した。
- 05: 全 e,j の M=A⊔B と旧 M43 の一致が成功、警告0。
- 06: bounded strictness / source restrictions / orthogonal support の24 examples が成功、警告0。
- 07: Fin 3 に限定した power transport を追加した最終 production が成功、警告0。
- 08: power test の α∈P37 の第一冪への simpa で root0 の定義が十分に展開されず、
  P37 と P_(eisenstein43Root 0) の proof-dependent argument が照合されなかった。
  `simpa [eisenstein43Root] using alpha_mem` に局所修正。
- 09: 最終34 examples、二つの mixed products、全15公理チェックが成功、警告0。
- 10: Step035 source/test の直接 regression 成功、警告0。
- 11: Step034 source/test の直接 regression 成功、警告0。

build の範囲は新 owner/test と指定の直接 regression。全 clean all-suite の結果として扱わない。

## Lean 結果からの気づき・試した命題・実装提案

1. 個別の source extensions が真に小さくても、その和が共通 kernel を正確に生成する。
   共同生成の証明は maximality からの形式的推定ではなく、全 x の明示的な二座標分解だった。
2. d_e の source 所属と y_e(x) の別 source 所属を独立に証明する構成により、
   E の ideal と R の ideal を混同せずに join の逆包含を得られた。
3. root の natural representative を扱う proof では broad simp が ZMod.cast を導入する。
   integer lift の RingHom 保存を先に書き換え、座標法則を限定した simp only にすると、
   deep ext や domain/field 仮定を追加せずに証明できた。
4. 試した別命題として、A0<A0⊔B0、B0<A0⊔B0 と、joint sums の十二点の単射性・極大性も
   examples で検証した。第二行の x の分解も追加し、root37 の特殊ケースに限定されないことを確認。
5. source power と common power の関係は equality と inclusion を分けると正確になる。
   Ideal.map_pow の等式は A/B の冪を対象とし、M^n への所属は包含の単調性を使う。
   理想用の Ideal.pow_mono を推測して使わず、実在する pow_le_pow_left' を確認して使用した。
6. iEα·iRF0 と iE(α²)·iRF0 は source の違いを保持した意味のある C の混合積だった。
   それぞれの M³/M⁴ lower bound を証明できたが、正確な valuation や prime-power 同期にはならない。
   `(A⊔B)^n=A^n⊔B^n` は追加していない。mixed terms の消去を仮定する理由はない。
7. 次の実装を検討するなら、局所の理想 sum より原来の global balance / reconstruction 契約に
   何が供給できるかを先に照合するのがよい。実際の GTailGlobalBalanceFirewall の二つの iff は
   Fermat equation と exact scalar/norm balance の同値であり、今回の join はその balance を作らない。
   non-Fermat witness においても全 local joins と今回の mixed lower bounds が成立している。
8. DescentClosureAudit の実際の AwayDescentClosureProvider は nextX/Y/Z、nextPack、nextRoute、
   `carrier_match : nextRoute.carrier=Int.natAbs p.normal.root.snd` を要求する。
   この出力は Ideal C の等式・所属であり、それらの field や旧 signed carrier の一致は供給しない。
   local theorem と source-linked packet reconstruction の間に必要な情報を明示した契約表が
   次の検討候補である。今回は provider や次の実装を構築せず、Step036 で停止した。

## 最終監査と変更範囲

- 全15公開宣言の #print axioms と34 examples を照合。非標準公理0。
- 新 source/test のコメント・文字列を除いた token scan は
  sorry / admit / axiom / unsafe / native_decide / set_option / False.elim がすべて0。
- MIT2026 header、import 後の file print、二空白 indentation を維持。
  最終 production07 / test09 / regression10,11 は exit0、warning0。
- direct import は production が旧 Step035 一つ、test が新 owner 一つ。
  production closure は8951 modules / local171、test は8952 / local172。
  local union172 vertices で DAG cycle0。
- neutral GTailSevenRealTraceResidue は1907 modules / local20、FLT 到達0。
  production closure 内の全27 Lib owners の個別 closure でも neutral→FLT 到達0。
- FLT.Seven facade、global oriented factorization、CyclotomicPrincipalization、
  CyclotomicQRTraceOneBridge、degree-six domain certification、valuation ownership の
  各除外 owner は新 closure にない。既存の他の carrier modules を消したという意味ではない。
- git diff --check と新ファイル / ROADMAP 追記の whitespace・final newline が成功。
  ROADMAP の HEAD bytes は prefix として保持。歴史的な Markdown hard break も不変。
  old ring/source/provider/facade/ledger/review/report/inventory/frontier の変更なし。

証拠は `.lake/build/gtail-step036/{runs.json,imports.json,audit.json,workspace-audit.json}`。
変更は source/test と inventory/report/frontier036 の新ファイル五つ、および ROADMAP 追記のみ。
STOP036。finite prime join と bounded mixed support の完成は original FLT7 closure の完成ではない。
