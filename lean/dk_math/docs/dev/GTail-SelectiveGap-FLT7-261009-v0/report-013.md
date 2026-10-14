# Report 013 — Eisenstein norm-prime residue slots

Date: 2026-10-10 (JST). **Step 013 COMPLETE / Outcome B.** Initial clean HEAD `728922b30389fc19203f662b86887535390c2683`, branch `feature/GTail-SelectiveGap-FLT7-261009-v0`.

## 実装結果と範囲

既存 TraceOneInt(-1) の α=gtailSevenNormCoord に、元レベルの α*conj α=ofInt(-1) Q、共役の座標、スカラー環元 q の整除と両自然数座標の整除の iff を追加した。有限体では t=-a/b を選び、二次式 t²-t+1 の根、α のゼロ評価、共役側の評価 2a+b と q≠3 での非零性・根の相違を証明した。Fermat 方程式は一切必要としない。

変更ファイル:

- `DkMath/Lib/NumberTheory/GTailSevenEisensteinResidue.lean`: neutral production、２ helper 定義・13 公開定理。
- `DkMathTest/NumberTheory/GTailSevenEisensteinResidue.lean`: direct-import tests と全15公開シンボルの axiom print。
- `source-inventory-013.md`, `report-013.md`, `ROADMAP.md`。

既存の MIT ヘッダ・import 後の file print・namespace/indent スタイルを維持した。optional FLT owner と RingHom package は追加していない。

## Exact public signatures

全シンボルは `DkMath.Lib.NumberTheory`。`open DkMath.NumberTheory.TraceOneQuadratic`。

```lean
theorem gtailSevenNormCoord_mul_conj (a b : ℕ) :
    gtailSevenNormCoord a b * conj (gtailSevenNormCoord a b) =
      ofInt (-1) (((a ^ 2 + a * b + b ^ 2 : ℕ) : ℤ))

theorem conj_gtailSevenNormCoord (a b : ℕ) :
    conj (gtailSevenNormCoord a b) =
      (⟨((a + b : ℕ) : ℤ), -(b : ℤ)⟩ : TraceOneInt (-1))

theorem scalar_dvd_gtailSevenNormCoord_iff (q a b : ℕ) :
    ofInt (-1) (q : ℤ) ∣ gtailSevenNormCoord a b ↔ q ∣ a ∧ q ∣ b

def eisensteinResidueEval {q : ℕ} (t : ZMod q) (z : TraceOneInt (-1)) : ZMod q

def gtailSevenResidueRoot (q a b : ℕ) [Fact (Nat.Prime q)] : ZMod q

theorem eisensteinResidueEval_add {q : ℕ} (t : ZMod q) (x y : TraceOneInt (-1)) :
    eisensteinResidueEval t (x + y) =
      eisensteinResidueEval t x + eisensteinResidueEval t y

theorem eisensteinResidueEval_mul {q : ℕ} (t : ZMod q)
    (ht : t ^ 2 - t + 1 = 0) (x y : TraceOneInt (-1)) :
    eisensteinResidueEval t (x * y) =
      eisensteinResidueEval t x * eisensteinResidueEval t y

theorem gtailSevenResidueRoot_polynomial {q a b : ℕ} [Fact (Nat.Prime q)]
    (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hb : ¬ q ∣ b) :
    gtailSevenResidueRoot q a b ^ 2 - gtailSevenResidueRoot q a b + 1 = 0

theorem eisensteinResidueEval_gtailSevenNormCoord_zero {q a b : ℕ}
    [Fact (Nat.Prime q)] (hb : ¬ q ∣ b) :
    eisensteinResidueEval (gtailSevenResidueRoot q a b) (gtailSevenNormCoord a b) = 0

theorem gtailSevenResidueRoot_conjugate_polynomial {q a b : ℕ}
    [Fact (Nat.Prime q)] (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hb : ¬ q ∣ b) :
    (1 - gtailSevenResidueRoot q a b) ^ 2 -
      (1 - gtailSevenResidueRoot q a b) + 1 = 0

theorem eisensteinResidueEval_gtailSevenNormCoord_conjugate {q a b : ℕ}
    [Fact (Nat.Prime q)] (hb : ¬ q ∣ b) :
    eisensteinResidueEval (1 - gtailSevenResidueRoot q a b) (gtailSevenNormCoord a b) =
      2 * (a : ZMod q) + (b : ZMod q)

theorem eisensteinResidueEval_conj {q : ℕ} (t : ZMod q) (z : TraceOneInt (-1)) :
    eisensteinResidueEval t (conj z) = eisensteinResidueEval (1 - t) z

theorem gtailSevenResidue_trace_ne_zero {q a b : ℕ} [Fact (Nat.Prime q)]
    (hq3 : q ≠ 3) (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hb : ¬ q ∣ b) :
    2 * (a : ZMod q) + (b : ZMod q) ≠ 0

theorem eisensteinResidueEval_gtailSevenNormCoord_conjugate_ne_zero {q a b : ℕ}
    [Fact (Nat.Prime q)] (hq3 : q ≠ 3)
    (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hb : ¬ q ∣ b) :
    eisensteinResidueEval (1 - gtailSevenResidueRoot q a b) (gtailSevenNormCoord a b) ≠ 0

theorem gtailSevenResidueRoot_ne_conjugate {q a b : ℕ} [Fact (Nat.Prime q)]
    (hq3 : q ≠ 3) (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hb : ¬ q ∣ b) :
    gtailSevenResidueRoot q a b ≠ 1 - gtailSevenResidueRoot q a b
```

定義本体は eval=`(z.fst : ZMod q) + (z.snd : ZMod q) * t`、root=`-(a : ZMod q) / (b : ZMod q)`。

## Proof dependencies and carrier audit

α*conj α は既存 `traceOne_mul_conj` と Step 012 `norm_gtailSevenNormCoord` の直接特殊化。スカラー整除は quotient witness の fst/snd を投影し、逆方向は両整数商のペアを構成する。`Int.ofNat_dvd` で natural/Int を接続し、q=0 も含む。旧格子 iff は一般の非零ノルム divisor に対する両共役積座標の条件であり、ノルム値だけの逆推論を許さない。新規一般格子カーネルは作っていない。

prime の `Fact` は division/field instance に先立って署名に入れた。q∣Q を `ZMod.natCast_eq_zero_iff` と `push_cast` で有限体の二次式ゼロにし、明示的な b≠0 のもと `field_simp` で ratio の根を証明した。最初のゼロ評価は ratio と b-unit だけから出て、q∣Q さえ必要ない。共役側の式もゼロ評価から導き、q≠3 を必要としない。

非零性は有限体の恒等式 4Q=(2a+b)²+3b² を `ring` で証明し、Q=0 と trace=0 の仮定から 3*b²=0 を得る。b≠0 と体の zero-product で 3=0、cast iff と `Nat.prime_dvd_prime_iff_eq` により q=3 を導く。根の相違は同じ元の評価が片方0、もう片方非零であることから導いた。a-unit/原始性は仮定していない。

eval は任意の ZMod q 上で加法を保存し、t²-t+1=0 のもと既存 `fst_mul`/`snd_mul` と `linear_combination` で乗法を保存する。共役を評価することと parameter を1-tに替えることの一致も証明した。単なる関数定義から準同型性を宣言していないが、bundled RingHom は実装していない。

直接 imports と既存 TraceOneResidueType / QuadraticResidueType / Mathlib QuadraticAlgebra.lift との違いは [source-inventory-013.md](source-inventory-013.md)。既存 residueMap は２座標の QuadraticAlgebra への reduction、今回は選んだ根における１つの scalar slot である。新 neutral に FLT import はない。

## Sequential incremental Lean checks

全 command の cwd は `lean/dk_math`、process-local `LEAN_NUM_THREADS=2`。以下は実行履歴（途中の修正試行も含む）。

| Command (cwd: `lean/dk_math`) | Exit | Seconds | Log |
|---|---:|---:|---|
| `LEAN_NUM_THREADS=2 lake build DkMath.Lib.NumberTheory.GTailSevenEisensteinResidue` | 1 | 3.89 | `.lake/build/gtail-step013/01-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMath.Lib.NumberTheory.GTailSevenEisensteinResidue` | 0 | 4.08 | `.lake/build/gtail-step013/02-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.NumberTheory.GTailSevenEisensteinResidue` | 1 | 3.93 | `.lake/build/gtail-step013/03-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.NumberTheory.GTailSevenEisensteinResidue` | 1 | 3.77 | `.lake/build/gtail-step013/04-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.NumberTheory.GTailSevenEisensteinResidue` | 0 | 3.82 | `.lake/build/gtail-step013/05-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.NumberTheory.GTailSevenNormReadout` | 0 | 1.37 | `.lake/build/gtail-step013/06-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailNormReadoutAudit` | 0 | 7.97 | `.lake/build/gtail-step013/07-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailNormReadoutAudit` | 0 | 7.97 | `.lake/build/gtail-step013/07-build.log` |

新規２ターゲットと Step 012 の neutral/owner 両回帰ターゲットは最終版ですべて exit 0。全 clean / all-test build は実行していない。

01 は ZMod.Basic だけでは prime Field instance が不足し、field_simp/linear_combination の直接 import も不足した。Mathlib.Algebra.Field.ZMod と２ tactic import を追加した。また hb だけから a を推論できない内部 `have` は `(a := a)` を明示した。02 で production 全体が成功。

03 はスカラー43の整数 literal と natural cast の rewrite 不一致、および ratio division の `decide` reduction が停止した。scalar側はキャスト型を明示し、root43 は b≠0 の `div_eq_iff` と有限な積の `decide` で検証した。04 は q=3 example の `norm_num` が有限体の -1=2 / 3=0 を残したため、それらに `decide` を適用。05 で全テスト成功。命題・仮定を弱めず、production のリング操作や旧定理は変更していない。compiler が失敗途中に生成した sorry 表示は01の未解決 elaboration の診断であり、最終 source/axiom 出力に placeholder はない。

## Public axiom audit

05 の新15シンボルだけを抽出し、折返し行も含め確認した。すべて標準基礎のみ。

| Symbol | Axioms |
|---|---|
| `gtailSevenNormCoord_mul_conj` | `[propext, Classical.choice, Quot.sound]` |
| `conj_gtailSevenNormCoord` | `[propext]` |
| `scalar_dvd_gtailSevenNormCoord_iff` | `[propext]` |
| `eisensteinResidueEval` | `[propext, Quot.sound]` |
| `gtailSevenResidueRoot` | `[propext, Classical.choice, Quot.sound]` |
| `eisensteinResidueEval_add` | `[propext, Quot.sound]` |
| `eisensteinResidueEval_mul` | `[propext, Quot.sound]` |
| `gtailSevenResidueRoot_polynomial` | `[propext, Classical.choice, Quot.sound]` |
| `eisensteinResidueEval_gtailSevenNormCoord_zero` | `[propext, Classical.choice, Quot.sound]` |
| `gtailSevenResidueRoot_conjugate_polynomial` | `[propext, Classical.choice, Quot.sound]` |
| `eisensteinResidueEval_gtailSevenNormCoord_conjugate` | `[propext, Classical.choice, Quot.sound]` |
| `eisensteinResidueEval_conj` | `[propext, Quot.sound]` |
| `gtailSevenResidue_trace_ne_zero` | `[propext, Classical.choice, Quot.sound]` |
| `eisensteinResidueEval_gtailSevenNormCoord_conjugate_ne_zero` | `[propext, Classical.choice, Quot.sound]` |
| `gtailSevenResidueRoot_ne_conjugate` | `[propext, Classical.choice, Quot.sound]` |

## 検査済み example と気づき

- q=43,a=5,b=8: Q=129=3*43、43∣norm α と ¬ofInt(-1)43∣α を同時に検査した。否定対象はスカラー環元43であり、選んだ非スカラー素元の整除についての反例ではない。
- t=37、1-t=7。ratio の数値は `div_eq_iff` を経由して核検査した。generic theorem によるゼロ/18の評価、非零性、根の相違と、独立の 5+8*37 / 5+8*7 の有限計算を確認した。
- conj α の負の第二座標を直接評価して18を得た。α*α の評価も relation-guarded eval_mul から0と証明した。負座標の整数キャストが実際の residue evaluation と両立する。
- q=3,a=b=1: Q=3 の root-polynomial theorem を適用し、t=2=1-t と両評価0を具体的に確認した。q≠3 を除いた非零/異根の一般化はこの例に反する。
- b=0: α(5,0)*conj α(5,0)=ofInt(-1)25 を確認し、q∤0 は成立しないことも確認した。ratio は関数として定義できても denominator-unit theorem を適用してはいけない。
- 任意 prime q の仮定をそのまま持つ example で、２ root equations と distinctness の公開 receiver をまとめて適用した。

ノルム整除から得られる residue address は、スカラー環元整除とは別の情報である。ゼロ評価は α の両座標が0になることを意味せず、選んだ root に沿った線形関係を意味する。共役の向きが t↔1-t と一致することを型付きで回復できた。ただし環元の平方因子分解・素イデアル・単元類・下降は回復していない。

## 実装提案（未実施）と停止点

将来の必要があれば、eval の0/1保存を加えて bundled RingHom にするか、既存 TraceOneResidueType.residueMap と Mathlib QuadraticAlgebra.lift の合成との一致を証明できる。今回は加法・乗法・共役の必要な性質だけを実装した。その先の kernel を素イデアルとして構成するには別の ideal-level 定義・証明が必要であり、このレポートは分解 (q)=P*Pbar を主張しない。

Step 010 の primitive pair と q∣Q から q∤b を導く thin adapter は将来候補。Step 011 owner の既存 b-unit 導出と同じ前提処理になるため今回は追加せず、neutral の実際の必要仮定を公開した。位数21・cyclotomic carrier/unit-class・次の Fermat packet の証明は追加していない。

Outcome B: 成立する中立校正と residue orientation。独立の新 FLT7 算術障害・closure ではない。Step 013 で停止。

## Final source/graph audit

新規２ Lean source に sorry/admit/new axiom/unsafe/False.elim/exfalso/native_decide/FLT impossibility endpoint の禁止構文なし。末尾改行と行末空白検査、`git diff --check` は成功。最終 production/test ログは warning/error なし。16 examples を核検査した。

コメント除去後の import-header closure は production 1198 source names / 11 local modules、test 1199 / 12。ローカル union 12 vertices の DFS で cycle なし、neutral closure に FLT module なし。結果 `.lake/build/gtail-step013/imports.json`。external terminal を含む source 名数であり、Lean job 数や全依存の placeholder 非存在の主張ではない。

HEAD と byte 比較した25の既存ファイル（存在する Lake/toolchain/root driver/facade、TraceOneQuadratic、Eisenstein/TraceOne lattice、coordinate/residue owners、Step 010–012 の prime/norm owners/tests、GTailSeven、GTailBridge、歴史的 ledger）は変更なし。既存 Legendre 対象が指定 glob に存在する場合も比較する監査を実行し、変更は認められなかった。
