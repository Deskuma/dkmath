# IRR-006: Galois 位相障害輸送の教科書実装

2026-10-19。対象は [NOTE-004 §5](NOTE-004.md) の実装要求。
§4 の研究提案を未証明の定理として取り込むことはせず、実際の円分体自己同型と
実際のイデアル根の対応を証明する。

## 1. 正規化を通ると何が変わるか

奇素数 p、K=ℚ(ζₚ)、R=𝓞 K とし、λ=1−ζₚ と置く。
A,B∈ℤ と、λq=A+B を満たす q∈R が与えられたとする。
この中心等式の存在を前提とし、整数係数だけから q の存在を推論しない。

既存の商は、割り算を使わず、

\[
Q_i=q-\left(\sum_{k<i}\zeta^k\right)B,
\qquad \lambda Q_i=A+\zeta^iB
\]

と定義される。位相0も含む。
σₐ(ζ)=ζᵃ、a∈(ℤ/pℤ)ˣ に対し整数係数は固定されるが、λは動く。

\[
\sigma_a(\lambda)=1-\zeta^a=c_a\lambda,
\qquad c_a\in R^\times.
\]

単元の存在は原始根の互いに素な冪に関する associated 定理から証明する。
幾何級数によればその値は `∑ k ∈ Finset.range a.val.val, ζ ^ k` に等しい。
したがって、

\[
c_a\lambda\,\sigma_a(Q_i)=\lambda Q_{ai},
\qquad \boxed{\sigma_a(Q_i)=c_a^{-1}Q_{ai}}.
\]

λ≠0 は packet の素元条件から従うため、ここで λ を打ち消せる。
単元を元の等式で省くことはできない。37次の回帰テストは
σ₋₁(λ)≠λ と、a=2 の補正単元の値が 1+ζ であることまで検証する。
単元補正が p乗であるとは結論しない。

## 2. 根そのものの対応から類群の対応へ

既存の packet は各位相について非零イデアル根 𝔞ᵢ を保持し、

\[
(Q_i)=\mathfrak a_i^p,\qquad \omega_i=[\mathfrak a_i]
\]

を記録する。σₐ による `Ideal.map` を適用すると、単元補正は主イデアルから消える。

\[
\sigma_a(\mathfrak a_i)^p=(\sigma_a(Q_i))=(Q_{ai})=\mathfrak a_{ai}^p.
\]

Dedekind 環のイデアルの正の冪写像は単射なので、

\[
\boxed{\sigma_a(\mathfrak a_i)=\mathfrak a_{ai}},
\qquad \boxed{\sigma_a(\omega_i)=\omega_{ai}}
\]

が従う。**ここで使った単射性はイデアル上の性質であり、類群上の p乗写像の
単射性ではない。** `classGroupPTorsionFreeAt` や主イデアル化は不要である。
Mathlib の `ClassGroup.mulEquiv` が本当に写したイデアルの類を与えることも、
分数イデアルへの写像と商群の定義から接続した。

## 3. 読む順序と公開入口

| モジュール | 教科書としての役割 |
| --- | --- |
| `DkMath.Lib.NumberTheory.IdealGaloisTransport` | 非零イデアルの写像、類群同型との整合性、単元倍の因子に対する根の一意性 |
| `DkMath.Lib.NumberTheory.GaloisPhaseObstructionTransport` | 位相置換・作用の合成則、正規化商の単元補正、真の円分体自己同型の供給 |
| `DkMath.FLT.Kummer.IrregularGalois37` | 既存の障害付き State への接続と37次の具体的特殊化 |

`DkMath.Lib` と `DkMath.FLT.Kummer`、および通常の `DkMath` import から到達できる。
新規ソース・テスト・smoke ファイルは、import 直後に要求された
`#print "file: モジュール名"` を持つ。

主な定理は以下。

- `IdealPowerObstruction.root_transport_of_unit`: 選択済みの根の対応。
- `RamifiedPhasePacket.quotient_galois`: 補正を残した元の等式。
- `RamifiedPhasePacket.phase_obstruction_galois`: 係数固定性を仮定した類群の等式。
- `CyclotomicPhaseGalois.obstruction_int`: 整数係数の場合、ガロア作用・単元補正・固定性を円分体内部で供給。
- `IrregularDescent.ObstructedState.galois_transport`: source の既存の因子と根を使う対応。
- `IrregularPrime37.observe_galois`: 整数座標を持つ仮想37次 State の根と類の対応。

## 4. 前提と残る境界

一般の円分整数 x,y はガロア作用で動く。したがって同じ族の i↦ai のみを
結論する一般定理では `e x=x`、`e y=y` を明記する。整数の場合は環準同型の
整数係数保存から供給する。任意の `ObstructedState` に対する無条件な同一族の
再索引則にはしていない。座標が固定されない場合も、`PhaseClassPacket.transport`
で因子族全体と根を運び、`obstruction_transport` で類群作用と比較できる。

既存の source、原始性、非分岐性を取り直したり弱めたりせず、そのまま参照する。
§6の指摘に合わせて `WeightedObstructedState.normalize` の docstring も明確化した。
保存される y,z は重み付き後続状態の座標である。

37次で使う体・整数環・類群作用は本物であるが、入力 State の存在、非自明な
GN 位相障害の存在、37-primary 類群の指標成分、Herbrand–Ribet、FLT37 の閉包は
この輸送則からは得られない。作用の整合性から指標成分を研究するための接続点を用意した。

## 5. 検証

公開宣言30件の公理監査と、主要3経路の実依存監査が通過した。
新規回帰例は mod 37 の位相還元・逆作用・作用の合成、実際に動く λ、
補正単元 1+ζ、既存 `observe` の障害輸送、非自明な類の保存を検査する。

全体トラッカーで見つかった既存テスト
`DkMathTest/NumberTheory/PrimitivBeam/CheckAxioms.lean` のマーカーも、実際の
モジュール名 `DkMathTest.NumberTheory.PrimitivBeam.CheckAxioms` に修正した。

`lake build DkMath DkMath.FLT.Kummer DkMathTest` は 11,487 jobs で成功した。
通常入口の smoke と `DkMathTest.lean` の直接検査も成功した。
`check_tracker_mismatch.py` は 2,283 組の Built/Replayed とマーカーに不一致を検出せず、
新規ソース・テスト5モジュールすべてがログに含まれることも確認した。
新規コードの警告はなく、`git diff --check` も通過した。

コマンド・終了状態・依存監査の結果は
[evidence/validation-irr006.txt](evidence/validation-irr006.txt) に記録する。
