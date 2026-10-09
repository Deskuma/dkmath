# Report 012 — typed quadratic norm readout

Date: 2026-10-10 (JST). **Step 012 COMPLETE / Outcome B.** Initial clean HEAD: `5f1266bda9ff8d6e9d686b1037f3ec4ecb7f7abd`, branch `feature/GTail-SelectiveGap-FLT7-261009-v0`.

## 実装と数学的範囲

既存の `TraceOneInt (-1)` と `TraceOneQuadratic.norm` を再利用し、α(a,b)=eisensteinCoord (a:ℤ) (-(b:ℤ))=⟨a,b⟩ のノルムを自然数の Q=a²+ab+b² の整数キャストに接続した。ノルム平方は `traceOne_norm_mul` から導いた。新しい環・Norm は導入していない。

selected Body は任意の自然数 a,b に対して 7ab(a+b)*norm(α²) と等しい。条件付き owner は既存の自然数 focused 積の等式を `congrArg` で整数へキャストする。署名中の GTail は自然数値を整数へキャストしたものであり、整数環で再評価した GTail 行への置換は行っていない。Fermat7Equation と和の関係だけを使い、正値性・原始性・単元条件を追加していない。

変更対象は上記２ production ファイルと対応する２ direct-import test、source-inventory-012、report-012、ROADMAP。全 Lean ファイルは既存の MIT ヘッダ、import 後の `#print "file: ..."`、名前空間・インデントの形式に合わせた。

## 公開署名

以下は production の全公開定義・定理（補助定義１、定理６）。neutral の名前空間は `DkMath.Lib.NumberTheory`、owner は `DkMath.FLT.Seven`。両者の open は TraceOneQuadratic と、それぞれ CosmicFormula / Lib.NumberTheory。

### `DkMath/Lib/NumberTheory/GTailSevenNormReadout.lean`

```lean
def gtailSevenNormCoord (a b : ℕ) : TraceOneInt (-1)

theorem gtailSevenNormCoord_eq (a b : ℕ) :
    gtailSevenNormCoord a b = (⟨(a : ℤ), (b : ℤ)⟩ : TraceOneInt (-1))

theorem norm_gtailSevenNormCoord (a b : ℕ) :
    norm (gtailSevenNormCoord a b) = ((a ^ 2 + a * b + b ^ 2 : ℕ) : ℤ)

theorem norm_gtailSevenNormCoord_sq (a b : ℕ) :
    norm ((gtailSevenNormCoord a b : TraceOneInt (-1)) ^ 2) =
      (((a ^ 2 + a * b + b ^ 2) ^ 2 : ℕ) : ℤ)

theorem dvd_quadratic_iff_dvd_gtailSevenNormCoord (q a b : ℕ) :
    q ∣ a ^ 2 + a * b + b ^ 2 ↔ (q : ℤ) ∣ norm (gtailSevenNormCoord a b)

theorem selectedBody_seven_interior_eq_norm_square (a b : ℕ) :
    selectedBody 7 (Finset.Ico 1 7) (a : ℤ) (b : ℤ) =
      7 * (a : ℤ) * (b : ℤ) * ((a + b : ℕ) : ℤ) *
        norm ((gtailSevenNormCoord a b : TraceOneInt (-1)) ^ 2)
```

### `DkMath/FLT/Seven/GTailNormReadoutAudit.lean`

```lean
theorem focused_gtail_eq_norm_square {a b c g : ℕ}
    (hEq : Fermat7Equation a b c) (hsum : a + b = c + g) :
    (g : ℤ) * ((DkMath.CosmicFormula.GTail 7 1 g c : ℕ) : ℤ) =
      7 * (a : ℤ) * (b : ℤ) * ((a + b : ℕ) : ℤ) *
        norm ((gtailSevenNormCoord a b : TraceOneInt (-1)) ^ 2)
```

補助定義の本体は `eisensteinCoord (a : ℤ) (-(b : ℤ))`。自然数/整数の整除 iff は `Int.ofNat_dvd.symm` により証明し、q=0 を含め任意の q に適用できる。これは整数ノルム値の整除であり、環元 α の整除や素イデアルの選択ではない。

## import・重複・依存監査

neutral の直接 import は `EisensteinCoordinates` と `GTailSeven` の２本。owner は `GTailBridge` と新 neutral の２本。テストは各 owner だけを直接 import。既存 `traceOneNorm_neg_one` / `norm_eisensteinCoord` の自然数入力・正符号への特殊化であり、基礎ノルム API の新規性は主張しない。selected Body / focused 積への新しい型付き接続を追加した。詳しい既存シンボル比較は [source-inventory-012](source-inventory-012.md)。

コメント除去後の import header を追跡するローカル監査で closure は順に 1003/8793/1004/8794 source module names、DkMath/DkMathTest ローカル数は 10/13/11/14。ローカル union 15 vertices に cycle なし、neutral closure に FLT なし。外部 terminal を含む source 名数であり、ビルド job 数や全 closure の無 sorry 保証ではない。結果は `.lake/build/gtail-step012/imports.json`。

TraceOneInt(-2) の `cyclotomicSevenToTraceOne` と実三次環上の degree-six carrier は source の型を比較したのみ。新 α との環写像・単元類移送は実装していない。公開 facade・root test driver・旧 Norm/unit research owner は変更していない。

## Lean 検証

各コマンドは process-local `LEAN_NUM_THREADS=2`、逐次・incremental に実行した。

| Command (cwd: `lean/dk_math`) | Exit | Seconds | Log |
|---|---:|---:|---|
| `LEAN_NUM_THREADS=2 lake build DkMath.Lib.NumberTheory.GTailSevenNormReadout` | 0 | 3.21 | `.lake/build/gtail-step012/01-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailNormReadoutAudit` | 0 | 13.92 | `.lake/build/gtail-step012/02-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.NumberTheory.GTailSevenNormReadout` | 1 | 3.22 | `.lake/build/gtail-step012/03-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.NumberTheory.GTailSevenNormReadout` | 0 | 3.32 | `.lake/build/gtail-step012/04-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailNormReadoutAudit` | 0 | 13.63 | `.lake/build/gtail-step012/05-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.NumberTheory.GTailSevenPrimeOrder` | 0 | 1.9 | `.lake/build/gtail-step012/06-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailPrimeOrderAudit` | 0 | 8.1 | `.lake/build/gtail-step012/07-build.log` |

03 の失敗は、数値 selected Body 目標に `rw` する際の自然数キャストと整数リテラルの構文不一致。定理を型付き `have` に受けてノルム平方を rewrite、`norm_num` でキャストを正規化し、04 で成功した。production の命題・仮定は変更していない。新規４ターゲットと Step 011 の２回帰ターゲットの最終結果はすべて exit 0。全 clean / all-test build は実行していない。

新公開 `#print axioms` の出力（04/05 のログから新シンボルのみ抽出）:

- `gtailSevenNormCoord`: does not depend on any axioms.
- `gtailSevenNormCoord_eq`: `[propext]`。
- `norm_gtailSevenNormCoord`, `norm_gtailSevenNormCoord_sq`, `dvd_quadratic_iff_dvd_gtailSevenNormCoord`, `selectedBody_seven_interior_eq_norm_square`, `focused_gtail_eq_norm_square`: 各 `[propext, Classical.choice, Quot.sound]`。

６定理すべて標準基礎のみ。import 元の既存 EisensteinCoordinates の axiom print もログに現れるため、新規数と混同しない。

## 検査した example と観察

neutral 12 examples、owner ２ examples を kernel 検査した。

- α の座標と境界 (0,0),(1,0),(0,1),(5,8) のノルムは 0,1,1,129。norm(α(5,8)²)=16641。
- α(5,8)²=⟨-39,144⟩。入力座標が自然数でも環元の平方の第一座標は負になり得る。一方ノルムは非負の Q² の整数キャストとして読める。
- `eisensteinCoord 5 8` のノルムは49、新 α のノルムは129。第二引数の符号を逆転し忘れると違う二次式になることを直接検査した。
- 43∣129 を自然数/整数ノルム iff で接続した。
- selected Body(5,8)=60573240=7*5*8*13*16641。定理適用と独立の実値計算を別 example で確認した。
- ⟨1,0⟩ と ⟨0,1⟩ は異なるがノルムはともに１。ノルム値写像が単射でないことを検査した。この対は任意の元の非平方性や「単元倍の平方でないこと」を証明するものではない。
- owner は一般の条件付き署名適用と (a,b,c,g)=(0,3,3,0) の成立する零境界を確認した。正値 Fermat 解を数値構成した例ではない。

## 推論の限界と実装提案

型付き quadratic-ring norm への接続は実装済みになった。しかし scalar norm equality から任意 β の元の平方因子分解、単元倍、選んだ素イデアル、根の向き、cyclotomic unit-power class、次の原始 Fermat packet は得ていない。非単射性の example が示すのは情報の喪失であり、強い非平方命題の反例と取り違えない。

今後の小さな提案（未実装）は、Step 010/011 の q∣Q 仮定を新 iff で整数ノルム整除へ言い換える adapter。入力表示の同値変換として作り、既存 q-budget/order 証明を複製しない。今回は最小 import を保ち optional adapter は追加しなかった。より強い元の因子分解には別の元レベル仮定・定理が必要であり、このノルム読取り自体は独立の新算術障害・下降・FLT7 closure を与えない。

Step 012 で停止する。

## 最終静的監査

４新規 Lean ファイルに `sorry` / `admit` / 新 `axiom` / `unsafe` / `False.elim` / `exfalso` / FLT impossibility endpoint の禁止構文なし。末尾改行・行末空白チェックと `git diff --check` は成功。新規定理６件の axiom 出力を（折返し行を含め）確認し、補助定義に axiom 依存がないことも確認した。最終２新規テストログに warning/error なし。

root / test driver、Lake 設定、Lib/Seven facade、TraceOneQuadratic、EisensteinCoordinates、EisensteinLatticeLanding、GTailSeven、GTailBridge、Step 010/011 owner、歴史的 constraint-ledger は存在する対象を HEAD と byte 比較し変更なし。
