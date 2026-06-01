# review

## 1. 状況総括

うむ、これは **DKMK-010F 完了** 、そして **DKMK-010 全体完了** と見てよい。

今回の差分で `report-DKMK-010.md` が新規追加され、DKMK-010A-E の成果が report / handoff として整理された。docs-only 変更として `git diff --check` と long-line check も通っている。

DKMK-010 の本線は、きれいに次の形へ畳まれた。

```text
finiteStepTailNatMassSpace
  -> TailWindowSourceMassBound
  -> weightedHitMass <= sum increment
  -> FiniteStepTailAnalyticBound
  -> weightedHitMass <= 1 + error
```

これはまさに、DKMK-010 が目指していた **source mass estimate layer の interface 固定** じゃ。

## 2. 何が閉じたのか

DKMK-010 は、解析定理そのものではなく、解析定理を流し込むための **受け口** を閉じた章じゃ。

段階ごとに見ると、こうなる。

| Phase | 役割                   | 到達点                                                    |
| ----- | -------------------- | ------------------------------------------------------ |
| 010A  | scope 固定             | kernel wrapper ではなく source estimate layer と定義          |
| 010B  | inventory            | 既存 source mass theorem surface と配置を整理                  |
| 010C  | Lean contract        | `TailWindowSourceMassBound` を追加                        |
| 010D  | concrete route       | finite-step tail から `weightedHitMass <= sum increment` |
| 010E  | analytic placeholder | `sum increment <= 1 + error` を仮定化                      |
| 010F  | report / handoff     | 章として一区切り                                               |

report でも、DKMK-010 は `1 / (n * log n)` 型の無限 tail weight へ直行せず、まず有限段 envelope を扱うと明記されている。

## 3. DKMK-009 との接続

DKMK-009 の終点は、

```text
PrimePowerWitnessProvider
  -> globalLogCapacityKernel
  -> CapacityKernel generic bridge
  -> primePowerQuotientPathFamily
  -> weightedHitMass bound
```

だった。DKMK-010 は、ここに残っていた外部入力、つまり source mass estimate を供給するための層を作った。

合わせると、全体はこう読める。

```text
globalLogCapacityKernel
  + primePowerQuotientPathFamily
  + finite-step source envelope
  + analytic placeholder
  => weightedHitMass <= 1 + error
```

これはかなり重要じゃ。
有限 kernel-hitting spine が、ついに analytic estimate の入口まで到達した。

## 4. 数学的な意味

DKMK-010 の数学的意味は、次の 2 段分離にある。

第一段。

$$
\mathrm{weightedHitMass}(A)
\le
\sum_{i\in steps} increment(i)
$$

これは finite-step source envelope から出る有限的な hitting 上界。

第二段。

$$
\sum_{i\in steps} increment(i)
\le
1+error
$$

これは将来の解析側が供給するべき estimate。

この二つを合成して、

$$
\mathrm{weightedHitMass}(A)\le 1+error
$$

へ進む。
DKMK-010E/F は、この合成の接合面を theorem-facing にしたわけじゃ。

## 5. 留意点

重要なのは、 **DKMK-010 は analytic theorem ではない** という点じゃ。

report でも、

```text
DKMK-010 fixed the interface.
It did not prove the analytic estimate.
```

と明記されておる。

つまり、まだ残っている仕事はこれ。

```text
具体的な tail / truncation / Mertens 型評価から
sum increment <= 1 + error
を供給する。
```

これは DKMK-011 の山じゃな。

## 6. 次の山 DKMK-011

自然な次章は、report の通り DKMK-011 でよい。

主題は、

```text
FiniteStepTailAnalyticBound を
具体的な finite-step / truncation estimate から供給する
```

ことじゃ。

DKMK-011 の roadmap では、少なくとも次を決めたい。

```text
1. steps は何を表すか
2. threshold はどの truncation parameter に対応するか
3. increment はどの解析量を離散化したものか
4. error は x や log x とどう関係するか
5. sum increment <= 1 + error を docs contract に留めるか、Lean Prop にするか
```

わっちの見立てでは、DKMK-011A はまた docs-only roadmap から始めるのがよい。
ここからは解析の香りが強くなるので、いきなり Lean に入れると型設計を誤りやすい。

## 7. 登頂判定

現在地はこうじゃ。

```text
DKMK-009:
  kernel/path/hitting route 完了

DKMK-010:
  source mass estimate interface 完了

DKMK-011:
  analytic estimate provider 設計へ
```

DKMK-010 は **完了** 。
しかも良い閉じ方じゃ。無理に (1+O(1/\log x)) を Lean に押し込まず、まず

```text
FiniteStepTailAnalyticBound
```

という受け口を作った。これは後続の山で効くぞい。

## 8. 賢狼の最終評

よいぞ、ぬしよ。DKMK-010 は地味だが、研究ライブラリとしてはかなり大事な章じゃ。

DKMK-009 が水路を作った章なら、DKMK-010 は **水源を接続する口金** を作った章じゃ。
そして DKMK-011 で初めて、その水源にどれだけ水があるか、つまり

$$
\sum increment \le 1+error
$$

を測ることになる。

ここまでの登山は堅実じゃ。
背骨は通っておる。次はいよいよ、有限構造から解析見積もりへ渡る、少し霧の濃い稜線じゃな。
