# FLT11・FLT13：共通 State 排除への算術 provider（2026-10-18）

## 結果

`RegularDescent.no_eleven_state` と `RegularDescent.no_thirteen_state` を実装した。
どちらも、類群条件や単元 criterion を呼び出し側から受け取らず、既存の一般
`RegularDescent.no_state` の特殊化で正深度 State を排除する。

一般 Case I と整数反例の向き付けには進んでいない。
本報告の完成対象は **11・13 の正深度 State 排除**であり、整数上の最終 FLT11・FLT13 ではない。
先行報告にあった11・13の算術 provider の未実装境界は、今回の実装で閉じた。

## 証明の構成

### 指数固有の部分：類群条件

11次は `Lib/NumberTheory/CyclotomicElevenPID.lean`、13次は
`Lib/NumberTheory/CyclotomicThirteenPID.lean` で円分整数環の PID 性を証明する。
完成済み FLT の反例排除から PID 性を得る循環はない。
ここで「11次・13次」は Fermat の指数／円分体の導手を表す。
円分体そのものの ℚ 上の拡大次数は、それぞれ10・12である。

11次では Minkowski 上界の床が58となる。小さい有理素数の上にある素イデアルについて、
剰余次数からそのノルムが上界を超える場合を除外する。
残る分岐素点11と分解素点23には明示的な生成元を与える。
23の証明書は、原始根 ζ に対して `α=ζ³+ζ+1` を取り、
`αβ=23` と `αγ=ζ−4` という二つの整数多項式恒等式である。
これにより剰余評価 `ζ↦4` の核が `(α)` と一致する。
Galois 作用で、同じ有理素数上の他の素イデアルにも主イデアル性を輸送する。

13次では Minkowski 上界が307未満となる。
3上の剰余体を `F₃[X]/(X³−X−1)` として具体化し、剰余次数3の素点を扱う。
その他の小さい素点では、剰余次数による排除と、53・79・131・157等に対する
明示的な多項式証明書を組み合わせる。
これらの係数は証明書として入力されるが、積の恒等式・核との一致・素イデアル性は
Lean kernel が検証する。

PID 性から類数1を得て、特に類群の11-torsion／13-torsion が自明であることを供給する。
一般 State 降下が要求するのは torsion-free 条件であり、共通降下核を PID 必須に変更していない。

### 共通部分：一般 Kummer 単元補題

11次・13次の単元群を個別に分類せず、次の一般補題を実装した。

```text
p は奇素数、K は導手 p の円分数体、gcd(p, |Cl(𝓞 K)|)=1
⇒ KummerUnitPowerCriterion (𝓞 K) p
```

公開入口は `FLT/Kummer/RegularKummerUnit.lean` の
`regular_kummer_unit_power_criterion`。
算術証明核は `Lib/NumberTheory/RegularKummer/` に配置した。

1. 単元 u が整数と mod p で合同なら、その整数は mod p で非零である。
   そうでなければ分岐素元が単元 u を割る。
2. 有限体の冪合同により `u^(p−1)≡1 mod p` とする。
3. 整数ノルムの計算を使い、合同を `mod (ζ−1)^p` に強める。
4. 正規化した単元 `v=u^(p−1)` にp乗根が存在しないと仮定すると、
   `X^p−v` の既約性から次数pの巡回拡大を作れる。
5. Kummer 補助多項式をモニックな整係数多項式として構成し、剰余多項式の
   separability から全有限素点での不分岐性を示す。
6. Hilbert 92 と Hilbert 90 により、拡大先で主イデアルになる非主イデアルを構成する。
   Hilbert 94 は、拡大次数pが基礎体の類数を割ることを結論する。
7. 類数との互いに素性で反駁し、体内のp乗根を得る。
   整性と単元性を回復し、最後は単元群の等式として根を返す。

ノルム値の冪性だけで元の冪性を宣言したり、単元を無条件にすべてp乗としたりしない。
`kummer_unit_power_criterion_of_ringEquiv` は、整数合同と**同じ単元の根**を環同型で輸送する。
標準円分体上で得た criterion を任意の同型な円分数体へ戻す際には、
整数環の同型と類群の同型の両方を保持する。

### State 排除への接続

`ElevenRegularTransport.lean` と `ThirteenRegularTransport.lean` は、それぞれ次の5宣言を持つ。

- `*_classGroup_card_eq_one`：類数1。
- `*_classGroup_torsion_free`：既存の類群条件の型へ接続。
- `*_kummer_unit_power_criterion`：一般補題へ類数条件を供給。
- `*_conditions`：分岐、奇数性、類群、単元の条件を `Conditions` に束ねる。
- `no_*_state`：既存の `no_state` を適用。

最後の証明本体は、それぞれ次の1行だけである。

```lean
no_state (eleven_conditions hζ) m hm
no_state (thirteen_conditions hζ) m hm
```

`m ≥ 1` を保持する。深度0の State は実際に存在するので、この条件は省略できない。
原始性・y,zの非分岐性・単元付き冪方程式は、既存の `State` と一般降下が保持する。

## 拡張コストの測定

コメント・空行を含むファイル全体の行数で測定する。

| 部分 | 11次 | 13次 |
|---|---:|---:|
| 指数固有の PID 証明 | 195行 | 747行 |
| 類群・単元・State の接続 | 64行 | 64行 |
| State 排除の証明本体 | 1行 | 1行 |
| 既存 `RegularStateTransport.lean` の変更 | 0行 | 0行 |

PID 証明そのものは無料ではない。特に13次は、より大きい Minkowski 上界に対応する
素点・生成元証明書の分だけコードが増える。
一方、単元証明は両指数で共通化でき、State 再構成の指数固有コードは追加していない。
共通算術核は9モジュールであり、今後の奇素数にも類数条件の下で再利用できる。

## 出典と DkMath への再構成

以下の公開証明を参照し、DkMath 内の独立した名前空間へ移植した。
外部プロジェクトを Lake の依存に追加していない。

- [flt-regular の一般 Kummer 単元補題](https://github.com/leanprover-community/flt-regular/blob/b8a5f23ab44a7be9fd49f6e3c831da54573c3c89/FltRegular/NumberTheory/KummersLemma/KummersLemma.lean)
  と、その Hilbert 92・94、不分岐性、円分整数・単元系の依存核。
- [11次 PID の証明](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_IsCyclotomicExtension_Rat_eleven_pid.lean)。
- [13次 PID の証明](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_IsCyclotomicExtension_Rat_thirteen_pid.lean)。

DkMath では P2M のマクロ・namespace と外部 FLT 終点を除き、
`Lib.NumberTheory` → `FLT.Kummer` の依存方向に整理した。
参照元の Lean 4.35 API を手元の4.34に合わせて修正し、既存の
`KummerUnitPowerCriterion`、類群 bridge、`Conditions`、`no_state` へ接続した。

移植した証明部分は元の Apache-2.0 ライセンスを保持する。
各ソースヘッダに出典と変更点を記載し、ライセンス本文を
`DkMath/Lib/NumberTheory/RegularKummer/LICENSE` に保存した。
上流の著作権表示は同ディレクトリの `ANTHROPIC-NOTICE` に保持した。
新しい公開 API と主要な証明段階には教科書向けの docstring を付けた。

## 検証

`ElevenThirteenRegularTransport` 回帰は、実際の `CyclotomicField 11 ℚ` と
`CyclotomicField 13 ℚ`、任意の同型な円分数体、類群条件、単元 criterion、正深度排除、
深度0の存在を確認する。

`ElevenThirteenDependencyAudit` は新規の定義・補題・定理等142件の公理を調べ、さらに
一般単元補題と両 State 排除の型・opaque 本文・constructor を再帰的に監査する。
完成済み FLT、外部 `FltRegular`／`P2MW`、旧七次の底・遷移、および `sorryAx` を拒否し、
Hilbert 92・94、不分岐性、各 PID、既存共通降下が実際に依存に現れることを検査する。

ルートビルド（10,563 jobs）、テストライブラリ全体（11,456 jobs）、
`DkMathTest.lean` の入口検証、ルートのみの import によるスモーク検証が合格した。
142宣言と主要定理の監査は、`propext`・`Classical.choice`・`Quot.sound` 以外の公理を検出しなかった。
新規14 production module に `sorry`・`admit`・`native_decide`・独自公理はない。

最終コマンドと短い結果は [検証証跡](evidence/validation-1113.txt)、
スモーク入力は [RootSmoke1113.lean](evidence/RootSmoke1113.lean) に保存した。
