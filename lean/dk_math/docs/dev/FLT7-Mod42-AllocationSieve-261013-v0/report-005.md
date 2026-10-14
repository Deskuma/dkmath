# report-005 — source–allocation–chart compatibility audit

**Outcome B** — 同じ source の既存接続を棚卸しし、divisor-one / perfect-sixth route の missing obligation を限定した。新しい source-coupled restriction は証明していない。付帯する abstract-premise insufficiency は Lean で反例固定した（診断は Outcome C に相当）。

## Q1 — Actual source data

完全な identifier、hypotheses、packet/branch、missing arrow は [source-coupling-map-005.md](source-coupling-map-005.md) の表を参照。

固定 p の norm subpacket K について、`M=|K.innerSndRoot|>0`、`7∤M`、`carrier=7^4*M^7`、inner/outer carrier の exact depth 4/5 が既存。

同じ K の complementary root N は正で seven-unit、`Nat.Coprime M N`、`M*N=V*C`。しかも `|seventhPowerSndCore A B|=N^7` を満たす。この polynomial provenance を捨てると actual packet の情報を失う。

選んだ divisor r の prime ℓ に対し `ℓ∤N`、`ℓ∣V ∨ ℓ∣C` が既存。exact receiver の仮定なしで actual source を使うため、これは本当の既存 source constraint。しかし chosen center / endpoint への新しい帰結ではない。

signedDepth / real-pair 側では norm(core_i)=-Q、pairwise coprimality、routing c21/c22 の gcd address、load projections の全体への associated allocation、stripped residual の associated seventh-power extraction が既存。ここで Q は signed quotientRoot であり M ではない。full real-pair core extraction は c21/c22 の seventh-power witnesses を必要とする。一方 loaded split は unconditional だが荷重を保持し、完全な core の七乗とは違う。

## Q2 — Divisor-one blind spot

prime-support theorem の `Nat.Prime ℓ` と `ℓ∣r` は r=1 では同時に成立しない。Lean の example で prime は1を割らないことも確認。

必要六モジュールと関連 source、centered / perfect-sixth / real-pair / GTail declarations の探索では、exact reconstruction の chosen r=1 を一律に禁止する独立 source theorem は見つからなかった。これは検索範囲内の結果であり、リポジトリ全体の論理的不在証明ではない。r=1 の実現可能性も主張しない。

既存 perfect-sixth obstruction は r=1 でも使えるが `M=t^6` と `9≤t` を別途必要とする。global family exclusion は全 eligible divisors にその条件を与える hfamily を仮定するため、その premise を actual source から得ることが未解決。

## Q3 — Same chart linkage and missing arrow

GN↔center は `c=D+2*u`、RHS↔ordered center は `c=D-u-u` を使う。逆方向も natural interval、parity、coprimality と scalar equality を保持して u を復元する。source reconstruction↔sieved receiver↔centered condition は既存の両方向同値であり、どちら側の存在も新たには与えない。

actual source ledger / real-pair roots → **chosen** r,s,c,u に新たな制約を与える橋は今回確認できていない。norm や ideal が一致しても oriented integer endpoint は固定できない。`no_fullCoordinate_decoder_on_orientedResidualIdeal` は ideal と exact seventh power が同じでも zeta translate の全座標は異なることを既に証明する。ただしこれは任意の invariant chart extractor を否定するものではない。

さらに `internalDepthFourReconstructedRoute_root_ne_innerRoot` は supplied reconstructed route の root が source innerRoot と異なることを保証する。depth 3 の away root と depth 4 の source coordinate を同一視できない。既存 division-free root comparison の multipliers は seven-units であり、integer units とは限らない。

first missing statement は map の Markdown Lean block に記載した `source_divisorOne_center_requires_perfectSixth`。actual p と chosen centered candidate at r=1 から literal `M=t^6` と `9≤t` を導く、既存 gap obstruction への最小局所入力である。**未証明、妥当性未確定**。定理や仮定として追加していない。その証明は既に divisor-one chart exclusion に相当する実質的問題なので、簡単な bookkeeping と扱わない。

## Q4 — New work vs repackaging

今回 production wrapper は追加していない。M*N=V*C の再包装、既存 centered iff、exact equation から再導出した必要条件、未証明 hfamily の条件付き consumer は、新しい independent source constraint と数えない。

GTailBridge は元の自然数端点と supplied Fermat equation に対する正しい identity。GTailFocusedNormCyclotomicDepthBridge は同じ a,b,c,g と prime hypotheses に対する conditional valuation / norm-value synchronization。これらは actual source の A,B を新しい natural endpoint に変換する map を供給しない。Eisenstein norm-square と degree-six carrier の間にも norm/ideal equality だけで integral coordinate map を仮定してはならない。

裸の `M*N=V*C`、`Nat.Coprime M N`、`N>0`、`7∤N` は任意の自然数 M に対して `N=1,V=M,C=1` で成立する。従ってこの subset だけには M を制限する情報がない。この構成は actual quadratic roots の存在を与えず、actual K の polynomial identity / norm / routing 条件を満たしたことにはならない。

## Proven changes — one standalone negative model

新規 production Lean は **0**。新規 DkMathTest の宣言:

```lean
theorem DkMathTest.FLT.Seven.abstractLedger_cheap_not_force_perfectSixth :
    ∃ M N V C : ℕ, 0 < M ∧ ¬ 7 ∣ M ∧ 0 < N ∧ ¬ 7 ∣ N ∧
      M * N = V * C ∧ Nat.Coprime M N ∧
      ModFortyTwoCheapAllocation M 1 ∧ SixthPowerAllocationSieve 1 (M / 1) ∧
      ¬ ∃ t : ℕ, M / 1 = t ^ 6
```

witness は `(631,1,631,1)`。cheap / sixth-power facts は既存 gate-004 family の k=0 を再利用。631 が literal sixth power でないことは `t≤2 → t^6≤64`、`t≥3 → t^6≥729` の exact bounds で証明した。これを使い、上記 abstract premises から literal sixth power が常に従うという universal conjecture の否定も example に固定した。

この model は actual K の polynomial complementary-root identity、real-pair ring elements、routing board、p、exact centered candidate を供給しない。したがって source-packet theorem の反例ではない。bare abstract ledger を source restriction と誤認しないための診断であり、新しい FLT7 の制約とは呼ばない。

## Validation and scope

2026-10-13、cwd `lean/dk_math`。Lean 4.34.1 / Lake 5.0.0-src+5045d00。

| Command | Exit | Result |
| --- | --- | --- |
| `python3 dkmath_theorems.py --db .dkmath-theorems.sqlite3 build --root .` | 0 | 1,806 files / 29,271 declarations |
| index search `internalDepthFourAllocation_prime_support --full` / `inner_complementary --full` / `perfectSixth --limit 20` | 0 | 1 / 1 / 10 relevant declarations; actual source inspected |
| `lake env lean DkMathTest/FLT/Seven/SevenRamifiedFusionSourceAllocationChartAudit.lean` | 0 | negative model, false universal implication, divisor-one prime diagnostic accepted |
| `lake build DkMathTest.FLT.Seven.SevenRamifiedFusionSourceAllocationChartAudit` | 0 | focused diagnostic and import dependencies, 9091 jobs |

Lean proof の失敗試行・追加仮定なし。探索時に brace glob と推測した GTail filename に read/search error があったが、実在する paths を rg で特定し読み直した。source audit を新規 kernel proof と呼ばない。RealPairLoadAllocation 等の全モジュールを今回新たに build したわけではない。

実際の axiom output:

```text
'DkMathTest.FLT.Seven.abstractLedger_cheap_not_force_perfectSixth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

標準三公理のみ、sorryAx / fresh axioms なし。新規5ファイルの whitespace と diagnostic source SHA-256 の最終チェックも成功。禁止構文検索一致なし（rg exit 1）。`git diff --check` exit 0、staging empty、logs ignored。

## Files and next single research question

追加は `DkMathTest/FLT/Seven/SevenRamifiedFusionSourceAllocationChartAudit.lean` と、この指示書ディレクトリの `source-coupling-map-005.md`, `findings-005.md`, `report-005.md`, `evidence/005-verification-summary.md`。既存ソース・README・ROADMAP は変更なし。evidence は今回実際に形式化した diagnostic の compact verification のみ。

**次の一問:** actual packet の ledger / real-pair load を用いたとき、chosen r=1 の centered candidate から literal `M=t^6` と `9≤t` を本当に導けるか。それを判定するには、norm / associated seventh-power residual と natural endpoint を結ぶ orientation-preserving relation が必要で、今ある合同式や norm 値だけをその関係の代わりにしてはならない。まずこの局所 target の妥当性を探索し、成立しない route ならそれ自体を記録する。新 moduli の反復や全 divisor の架空の hfamily へ拡大しない。

gate 005 で停止。Git staging / commit / push / branch / PR / merge は行っていない。
